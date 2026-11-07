-- Prove2me | solution 1 for MalleableSched.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-06T11:00:55.609041+00:00
-- url     : https://prove2.me/submissions/33166c1f-f570-44bc-97b7-3acc5b205b8a

import Mathlib
import Definitions.Def_MalleableSched_Model

open scoped ENNReal

set_option autoImplicit false

namespace MalleableSched3d

open MalleableSched

/-- A fractionally subadditive function vanishes (is `≤ 0`) on the empty set. -/
lemma fs_empty_le {m : ℕ} {h : Finset (Fin m) → ℝ} (hFS : FractionallySubadditive h) :
    h ∅ ≤ 0 := by
  have := hFS ∅ (fun _ => 0) (fun _ => ⟨le_refl _, zero_le_one⟩) (by simp)
  simpa using this

/-- Averaging form of fractional subadditivity: if nonnegative weights `w` on subsets of `T`
cover every element of `T` with total weight at least `q > 0`, then
`q * h T ≤ ∑_{U ⊆ T} w U * h U`. -/
lemma fs_avg {m : ℕ} {h : Finset (Fin m) → ℝ} (hFS : FractionallySubadditive h)
    (h0 : ∀ S, 0 ≤ h S) (T : Finset (Fin m)) (w : Finset (Fin m) → ℝ) (hw : ∀ S, 0 ≤ w S)
    (q : ℝ) (hq : 0 < q)
    (hcov : ∀ i ∈ T, q ≤ ∑ S ∈ T.powerset.filter (fun S => i ∈ S), w S) :
    q * h T ≤ ∑ S ∈ T.powerset, w S * h S := by
  set α : Finset (Fin m) → ℝ := fun S => min 1 (w S / q) with hα
  have hα01 : ∀ S, 0 ≤ α S ∧ α S ≤ 1 := fun S =>
    ⟨le_min zero_le_one (div_nonneg (hw S) hq.le), min_le_left _ _⟩
  have hαcov : ∀ i ∈ T, 1 ≤ ∑ S ∈ T.powerset.filter (fun S => i ∈ S), α S := by
    intro i hi
    by_cases hbig : ∃ S ∈ T.powerset.filter (fun S => i ∈ S), q ≤ w S
    · obtain ⟨S, hS, hqS⟩ := hbig
      have h1 : α S = 1 := by
        simp only [hα]
        apply min_eq_left
        rw [le_div_iff₀ hq]; linarith
      calc (1 : ℝ) = α S := h1.symm
        _ ≤ ∑ S ∈ T.powerset.filter (fun S => i ∈ S), α S :=
          Finset.single_le_sum (f := α) (fun S _ => (hα01 S).1) hS
    · push Not at hbig
      have heq : ∀ S ∈ T.powerset.filter (fun S => i ∈ S), α S = w S / q := by
        intro S hS
        simp only [hα]
        apply min_eq_right
        rw [div_le_iff₀ hq]; linarith [hbig S hS]
      rw [Finset.sum_congr rfl heq, ← Finset.sum_div, le_div_iff₀ hq, one_mul]
      exact hcov i hi
  have key := hFS T α hα01 hαcov
  have hle : ∑ S ∈ T.powerset, α S * h S ≤ ∑ S ∈ T.powerset, (w S / q) * h S := by
    apply Finset.sum_le_sum
    intro S _
    exact mul_le_mul_of_nonneg_right (min_le_right _ _) (h0 S)
  have hdiv : ∑ S ∈ T.powerset, (w S / q) * h S = (∑ S ∈ T.powerset, w S * h S) / q := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro S _
    ring
  have : h T ≤ (∑ S ∈ T.powerset, w S * h S) / q := by linarith
  rw [le_div_iff₀ hq] at this
  linarith

/-- Subadditivity over a covering family of subsets of `T`. -/
lemma fs_cover {m : ℕ} {h : Finset (Fin m) → ℝ} (hFS : FractionallySubadditive h)
    (h0 : ∀ S, 0 ≤ h S) (T : Finset (Fin m)) (F : Finset (Finset (Fin m)))
    (hF : ∀ U ∈ F, U ⊆ T) (hcov : ∀ i ∈ T, ∃ U ∈ F, i ∈ U) :
    h T ≤ ∑ U ∈ F, h U := by
  classical
  have := fs_avg hFS h0 T (fun S => if S ∈ F then 1 else 0)
    (fun S => by split_ifs <;> norm_num) 1 one_pos (by
      intro i hi
      obtain ⟨U, hUF, hiU⟩ := hcov i hi
      have hU : U ∈ T.powerset.filter (fun S => i ∈ S) :=
        Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (hF U hUF), hiU⟩
      calc (1 : ℝ) = (fun S => if S ∈ F then (1 : ℝ) else 0) U := by simp [hUF]
        _ ≤ _ := Finset.single_le_sum (f := fun S => if S ∈ F then (1 : ℝ) else 0)
            (fun S _ => by split_ifs <;> norm_num) hU)
  rw [one_mul] at this
  calc h T ≤ ∑ S ∈ T.powerset, (if S ∈ F then (1 : ℝ) else 0) * h S := this
    _ = ∑ S ∈ T.powerset.filter (fun S => S ∈ F), h S := by
        rw [Finset.sum_filter]; apply Finset.sum_congr rfl; intro S _; split_ifs <;> simp
    _ = ∑ U ∈ F, h U := by
        apply Finset.sum_congr _ (fun _ _ => rfl)
        ext U
        simp only [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨fun h => h.2, fun hU => ⟨hF U hU, hU⟩⟩

/-- Two-set subadditivity. -/
lemma fs_union {m : ℕ} {h : Finset (Fin m) → ℝ} (hFS : FractionallySubadditive h)
    (h0 : ∀ S, 0 ≤ h S) (A B : Finset (Fin m)) : h (A ∪ B) ≤ h A + h B := by
  classical
  by_cases hAB : A = B
  · subst hAB
    simp only [Finset.union_self]
    linarith [h0 A]
  · have := fs_cover hFS h0 (A ∪ B) {A, B}
      (by intro U hU; simp only [Finset.mem_insert, Finset.mem_singleton] at hU
          rcases hU with rfl | rfl
          · exact Finset.subset_union_left
          · exact Finset.subset_union_right)
      (by intro i hi
          rcases Finset.mem_union.1 hi with hi | hi
          · exact ⟨A, by simp, hi⟩
          · exact ⟨B, by simp, hi⟩)
    rwa [Finset.sum_pair hAB] at this

/-- Well-structured iff the multi-machine sets are pairwise disjoint. -/
lemma ws_of_disjoint {n m : ℕ} (S : Fin n → Finset (Fin m))
    (h : ∀ j j', j ≠ j' → 1 < (S j).card → 1 < (S j').card → Disjoint (S j) (S j')) :
    WellStructured S := by
  intro i j j' hij hj hij' hj'
  by_contra hne
  exact Finset.disjoint_left.1 (h j j' hne hj hj') hij hij'

/-- The constant `2e/(e-1)` is at least `3`. -/
lemma const_ge_three : (3 : ℝ) ≤ 2 * Real.exp 1 / (Real.exp 1 - 1) := by
  have h1 : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9; linarith
  have h2 : 2 < Real.exp 1 := by
    have := Real.exp_one_gt_d9; linarith
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- The constant `2e/(e-1)` is positive. -/
lemma const_pos : (0 : ℝ) < 2 * Real.exp 1 / (Real.exp 1 - 1) :=
  lt_of_lt_of_le (by norm_num) const_ge_three

/-- The infinite-load case: any singleton assignment works. -/
lemma theorem_1_of_top {n m : ℕ} (g : Fin n → Finset (Fin m) → ℝ)
    (S : Fin n → Finset (Fin m)) (hS : IsAssignment S) (htop : maxLoad g S = ⊤) :
    ∃ S' : Fin n → Finset (Fin m), IsAssignment S' ∧ WellStructured S' ∧
      maxLoad g S' ≤ ENNReal.ofReal (2 * Real.exp 1 / (Real.exp 1 - 1)) * maxLoad g S := by
  refine ⟨fun j => {(hS j).choose}, fun j => Finset.singleton_nonempty _, ?_, ?_⟩
  · intro i j j' _ hj _ _
    simp at hj
  · rw [htop, ENNReal.mul_top (by simpa using const_pos)]
    exact le_top

/-- `maxLoad` is bounded once every machine load is. -/
lemma maxLoad_le_of {n m : ℕ} (g : Fin n → Finset (Fin m) → ℝ) (S : Fin n → Finset (Fin m))
    (B : ℝ≥0∞)
    (h : ∀ i : Fin m, ∑ j ∈ Finset.univ.filter (fun j => i ∈ S j), procTime g j (S j) ≤ B) :
    maxLoad g S ≤ B :=
  iSup_le h

/-- Each job's time is at most the maximum load. -/
lemma procTime_le_maxLoad {n m : ℕ} (g : Fin n → Finset (Fin m) → ℝ)
    (S : Fin n → Finset (Fin m)) (j : Fin n) (i : Fin m) (hi : i ∈ S j) :
    procTime g j (S j) ≤ maxLoad g S := by
  classical
  refine le_trans ?_ (le_iSup _ i)
  exact Finset.single_le_sum (f := fun j => procTime g j (S j)) (fun _ _ => zero_le)
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)

-- ===== threshold lemma =====
/-- Elementary log bound: for `0 < v ≤ u`, `(u - v) / (2u) ≤ (1/2) log (u / v)`. -/
lemma step_log (u v : ℝ) (hv : 0 < v) (hvu : v ≤ u) :
    (u - v) / (2 * u) ≤ (1 / 2) * Real.log (u / v) := by
  have hu : 0 < u := lt_of_lt_of_le hv hvu
  have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hu hv)
  rw [inv_div] at h1
  have : (u - v) / (2 * u) = (1 / 2) * (1 - v / u) := by field_simp
  rw [this]
  nlinarith

/-- Discrete integral bound behind the constant `2e/(e-1)` (non-strict form). -/
lemma thr_sum {ι : Type*} [DecidableEq ι] (ℓ w : ι → ℝ) (A : ℝ) :
    ∀ (I : Finset ι), (∀ i ∈ I, 0 ≤ ℓ i) → (∀ i ∈ I, 0 ≤ w i) →
    (∀ k ∈ I, ∑ i ∈ I.filter (fun i => ℓ i ≤ ℓ k), w i ≤ 1 / (A - 2 * ℓ k)) →
    ∀ t : ℝ, 0 ≤ t → (∀ i ∈ I, ℓ i ≤ t) → 2 * t < A →
    ∑ i ∈ I, (t - ℓ i) * w i ≤ (1 / 2) * Real.log (A / (A - 2 * t)) := by
  intro I
  induction I using Finset.strongInduction with
  | H I ih =>
  intro hℓ0 hw hG t ht0 ht htA
  rcases I.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.sum_empty]
    have hA : 0 < A - 2 * t := by linarith
    have : 1 ≤ A / (A - 2 * t) := by rw [le_div_iff₀ hA]; linarith
    have := Real.log_nonneg this
    linarith
  obtain ⟨k, hkI, hkmax⟩ := I.exists_max_image ℓ hne
  set I' := I.erase k with hI'
  have hsub : I' ⊂ I := Finset.erase_ssubset hkI
  have hk0 : 0 ≤ ℓ k := hℓ0 k hkI
  have hkt : ℓ k ≤ t := ht k hkI
  have IH := ih I' hsub (fun i hi => hℓ0 i (Finset.mem_of_mem_erase hi))
    (fun i hi => hw i (Finset.mem_of_mem_erase hi))
    (by
      intro k' hk'
      refine le_trans ?_ (hG k' (Finset.mem_of_mem_erase hk'))
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        simp only [Finset.mem_filter] at hi ⊢
        exact ⟨Finset.mem_of_mem_erase hi.1, hi.2⟩
      · intro i hi _
        simp only [Finset.mem_filter] at hi
        exact hw i hi.1)
    (ℓ k) hk0 (fun i hi => hkmax i (Finset.mem_of_mem_erase hi)) (by linarith)
  have hW : ∑ i ∈ I, w i ≤ 1 / (A - 2 * ℓ k) := by
    have := hG k hkI
    rwa [Finset.filter_true_of_mem (fun i hi => hkmax i hi)] at this
  have hsplit : ∑ i ∈ I, (t - ℓ i) * w i =
      ∑ i ∈ I', (ℓ k - ℓ i) * w i + (t - ℓ k) * ∑ i ∈ I, w i := by
    rw [← Finset.add_sum_erase I _ hkI, ← Finset.add_sum_erase I w hkI, mul_add,
      Finset.mul_sum]
    rw [← hI']
    have : ∑ i ∈ I', (t - ℓ i) * w i = ∑ i ∈ I', ((ℓ k - ℓ i) * w i + (t - ℓ k) * w i) := by
      apply Finset.sum_congr rfl; intro i _; ring
    rw [this, Finset.sum_add_distrib]
    ring
  have hu : 0 < A - 2 * ℓ k := by linarith
  have hv : 0 < A - 2 * t := by linarith
  have hstep := step_log (A - 2 * ℓ k) (A - 2 * t) hv (by linarith)
  have h2 : (t - ℓ k) * ∑ i ∈ I, w i ≤ (t - ℓ k) / (A - 2 * ℓ k) := by
    have := mul_le_mul_of_nonneg_left hW (by linarith : (0 : ℝ) ≤ t - ℓ k)
    calc (t - ℓ k) * ∑ i ∈ I, w i ≤ (t - ℓ k) * (1 / (A - 2 * ℓ k)) := this
      _ = (t - ℓ k) / (A - 2 * ℓ k) := by ring
  have h3 : (t - ℓ k) / (A - 2 * ℓ k) = (A - 2 * ℓ k - (A - 2 * t)) / (2 * (A - 2 * ℓ k)) := by
    field_simp; ring
  have hlog : Real.log (A / (A - 2 * t)) =
      Real.log (A / (A - 2 * ℓ k)) + Real.log ((A - 2 * ℓ k) / (A - 2 * t)) := by
    rw [← Real.log_mul (div_pos (by linarith) hu).ne' (div_pos hu hv).ne']
    congr 1
    field_simp
  rw [hsplit, hlog]
  linarith

/-- Strict form: with strict hypotheses and `t` above every `ℓ i`, a nonempty family gives a
strict bound. -/
lemma thr_strict {ι : Type*} [DecidableEq ι] (ℓ w : ι → ℝ) (A : ℝ)
    (I : Finset ι) (hne : I.Nonempty) (hℓ0 : ∀ i ∈ I, 0 ≤ ℓ i) (hw : ∀ i ∈ I, 0 ≤ w i)
    (hG : ∀ k ∈ I, ∑ i ∈ I.filter (fun i => ℓ i ≤ ℓ k), w i < 1 / (A - 2 * ℓ k))
    (t : ℝ) (ht : ∀ i ∈ I, ℓ i < t) (htA : 2 * t < A) :
    ∑ i ∈ I, (t - ℓ i) * w i < (1 / 2) * Real.log (A / (A - 2 * t)) := by
  obtain ⟨k, hkI, hkmax⟩ := I.exists_max_image ℓ hne
  set I' := I.erase k with hI'
  have hk0 : 0 ≤ ℓ k := hℓ0 k hkI
  have hkt : ℓ k < t := ht k hkI
  have IH := thr_sum ℓ w A I' (fun i hi => hℓ0 i (Finset.mem_of_mem_erase hi))
    (fun i hi => hw i (Finset.mem_of_mem_erase hi))
    (by
      intro k' hk'
      refine le_trans ?_ (hG k' (Finset.mem_of_mem_erase hk')).le
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        simp only [Finset.mem_filter] at hi ⊢
        exact ⟨Finset.mem_of_mem_erase hi.1, hi.2⟩
      · intro i hi _
        simp only [Finset.mem_filter] at hi
        exact hw i hi.1)
    (ℓ k) hk0 (fun i hi => hkmax i (Finset.mem_of_mem_erase hi)) (by linarith)
  have hW : ∑ i ∈ I, w i < 1 / (A - 2 * ℓ k) := by
    have := hG k hkI
    rwa [Finset.filter_true_of_mem (fun i hi => hkmax i hi)] at this
  have hsplit : ∑ i ∈ I, (t - ℓ i) * w i =
      ∑ i ∈ I', (ℓ k - ℓ i) * w i + (t - ℓ k) * ∑ i ∈ I, w i := by
    rw [← Finset.add_sum_erase I _ hkI, ← Finset.add_sum_erase I w hkI, mul_add,
      Finset.mul_sum]
    rw [← hI']
    have : ∑ i ∈ I', (t - ℓ i) * w i = ∑ i ∈ I', ((ℓ k - ℓ i) * w i + (t - ℓ k) * w i) := by
      apply Finset.sum_congr rfl; intro i _; ring
    rw [this, Finset.sum_add_distrib]
    ring
  have hu : 0 < A - 2 * ℓ k := by linarith
  have hv : 0 < A - 2 * t := by linarith
  have hstep := step_log (A - 2 * ℓ k) (A - 2 * t) hv (by linarith)
  have h2 : (t - ℓ k) * ∑ i ∈ I, w i < (t - ℓ k) / (A - 2 * ℓ k) := by
    have := mul_lt_mul_of_pos_left hW (by linarith : (0 : ℝ) < t - ℓ k)
    calc (t - ℓ k) * ∑ i ∈ I, w i < (t - ℓ k) * (1 / (A - 2 * ℓ k)) := this
      _ = (t - ℓ k) / (A - 2 * ℓ k) := by ring
  have h3 : (t - ℓ k) / (A - 2 * ℓ k) = (A - 2 * ℓ k - (A - 2 * t)) / (2 * (A - 2 * ℓ k)) := by
    field_simp; ring
  have hlog : Real.log (A / (A - 2 * t)) =
      Real.log (A / (A - 2 * ℓ k)) + Real.log ((A - 2 * ℓ k) / (A - 2 * t)) := by
    rw [← Real.log_mul (div_pos (by linarith) hu).ne' (div_pos hu hv).ne']
    congr 1
    field_simp
  rw [hsplit, hlog]
  linarith

/-- `log (α / (α - 2)) = 1` for `α = 2e/(e-1)`. -/
lemma log_alpha : Real.log ((2 * Real.exp 1 / (Real.exp 1 - 1)) /
    (2 * Real.exp 1 / (Real.exp 1 - 1) - 2)) = 1 := by
  have he : 1 < Real.exp 1 := by
    have := Real.add_one_lt_exp (x := 1) one_ne_zero; linarith
  have h1 : Real.exp 1 - 1 ≠ 0 := by linarith
  have : (2 * Real.exp 1 / (Real.exp 1 - 1)) / (2 * Real.exp 1 / (Real.exp 1 - 1) - 2)
      = Real.exp 1 := by
    field_simp
    ring
  rw [this, Real.log_exp]

/-- Threshold lemma (the source of `2e/(e-1)`): if the machines `I` (nonempty) carry
`ℓ i ∈ [0, C)`, weights `w i ≥ 0` with `∑ (C - ℓ i) w i ≥ 1/2`, then some `k ∈ I` has
`1/(αC - 2 ℓ k) ≤ ∑_{ℓ i ≤ ℓ k} w i`. -/
lemma thr_exists {ι : Type*} [DecidableEq ι] (ℓ w : ι → ℝ) (C : ℝ)
    (I : Finset ι) (hne : I.Nonempty) (hℓ0 : ∀ i ∈ I, 0 ≤ ℓ i) (hℓC : ∀ i ∈ I, ℓ i < C)
    (hw : ∀ i ∈ I, 0 ≤ w i) (hsum : 1 / 2 ≤ ∑ i ∈ I, (C - ℓ i) * w i) :
    ∃ k ∈ I, 1 / (2 * Real.exp 1 / (Real.exp 1 - 1) * C - 2 * ℓ k) ≤
      ∑ i ∈ I.filter (fun i => ℓ i ≤ ℓ k), w i := by
  set α := 2 * Real.exp 1 / (Real.exp 1 - 1) with hα
  have hα3 : 3 ≤ α := by
    have h1 : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9; linarith
    have h2 : 2 < Real.exp 1 := by
      have := Real.exp_one_gt_d9; linarith
    rw [hα, le_div_iff₀ (by linarith)]
    linarith
  obtain ⟨i0, hi0⟩ := hne
  have hC : 0 < C := lt_of_le_of_lt (hℓ0 i0 hi0) (hℓC i0 hi0)
  by_contra hcon
  push Not at hcon
  have hlt := thr_strict ℓ w (α * C) I ⟨i0, hi0⟩ hℓ0 hw hcon C hℓC (by nlinarith)
  have : α * C / (α * C - 2 * C) = α / (α - 2) := by
    have : α - 2 ≠ 0 := by linarith
    field_simp
  rw [this, hα, log_alpha] at hlt
  linarith

-- ===== LP support / Hall =====
section LP
variable {m n : ℕ}

/-- Feasibility for (LP1): `x ≥ 0`, support inside `{Δ > 0}`, job sums `≥ 1`, machine loads `≤ C`. -/
def Feas (Δ : Fin m → Fin n → ℝ) (C : ℝ) (x : Fin m → Fin n → ℝ) : Prop :=
  (∀ i j, 0 ≤ x i j) ∧ (∀ i j, x i j ≠ 0 → 0 < Δ i j) ∧ (∀ j, 1 ≤ ∑ i, x i j) ∧
    (∀ i, ∑ j, x i j / Δ i j ≤ C)

/-- Support of `x` as a set of machine-job pairs. -/
noncomputable def supp (x : Fin m → Fin n → ℝ) : Finset (Fin m × Fin n) :=
  Finset.univ.filter (fun p => x p.1 p.2 ≠ 0)

/-- The two endpoints of a support edge. -/
def ends (p : Fin m × Fin n) : Finset (Fin m ⊕ Fin n) := {Sum.inl p.1, Sum.inr p.2}

lemma mem_supp {x : Fin m → Fin n → ℝ} {p : Fin m × Fin n} : p ∈ supp x ↔ x p.1 p.2 ≠ 0 := by
  simp [supp]

/-- Moving along a direction that preserves all constraint sums strictly shrinks the support. -/
lemma perturb (Δ : Fin m → Fin n → ℝ) (C : ℝ) (x d : Fin m → Fin n → ℝ) (hx : Feas Δ C x)
    (hdx : ∀ i j, d i j ≠ 0 → x i j ≠ 0) (hjob : ∀ j, ∑ i, d i j = 0)
    (hmach : ∀ i, ∑ j, d i j / Δ i j = 0) (hneg : ∃ i j, d i j < 0) :
    ∃ y, Feas Δ C y ∧ (supp y).card < (supp x).card := by
  classical
  obtain ⟨hx0, hxΔ, hxj, hxi⟩ := hx
  set Fn := Finset.univ.filter (fun p : Fin m × Fin n => d p.1 p.2 < 0) with hFn
  have hFne : Fn.Nonempty := by
    obtain ⟨i, j, h⟩ := hneg
    exact ⟨(i, j), by simp [hFn, h]⟩
  obtain ⟨p0, hp0, hmin⟩ := Fn.exists_min_image (fun p => x p.1 p.2 / (-d p.1 p.2)) hFne
  have hd0 : d p0.1 p0.2 < 0 := by simpa [hFn] using hp0
  set t := x p0.1 p0.2 / (-d p0.1 p0.2) with ht
  have ht0 : 0 ≤ t := div_nonneg (hx0 _ _) (by linarith)
  set y : Fin m → Fin n → ℝ := fun i j => x i j + t * d i j with hy
  have hy0 : ∀ i j, 0 ≤ y i j := by
    intro i j
    simp only [hy]
    by_cases hd : d i j < 0
    · have := hmin (i, j) (by simp [hFn, hd])
      simp only at this
      rw [le_div_iff₀ (by linarith)] at this
      nlinarith
    · push Not at hd
      nlinarith [hx0 i j]
  have hyx : ∀ i j, y i j ≠ 0 → x i j ≠ 0 := by
    intro i j hyij hxij
    apply hyij
    simp only [hy, hxij]
    have : d i j = 0 := by
      by_contra hne; exact hdx i j hne hxij
    simp [this]
  refine ⟨y, ⟨hy0, fun i j h => hxΔ i j (hyx i j h), ?_, ?_⟩, ?_⟩
  · intro j
    have : ∑ i, y i j = ∑ i, x i j + t * ∑ i, d i j := by
      simp only [hy, Finset.sum_add_distrib, Finset.mul_sum]
    rw [this, hjob j, mul_zero, add_zero]; exact hxj j
  · intro i
    have : ∑ j, y i j / Δ i j = ∑ j, x i j / Δ i j + t * ∑ j, d i j / Δ i j := by
      simp only [hy, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro j _; ring
    rw [this, hmach i, mul_zero, add_zero]; exact hxi i
  · apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨p0, ?_, ?_⟩
      · rw [mem_supp]; exact hdx _ _ hd0.ne
      · rw [mem_supp]; simp only [hy, ne_eq, not_not]
        rw [ht, div_neg, neg_mul, div_mul_cancel₀ _ hd0.ne, add_neg_cancel]
    · intro p hp
      rw [mem_supp] at hp ⊢
      exact hyx _ _ hp

/-- Coefficient of edge `p` in the constraint of vertex `u`. -/
noncomputable def coef (Δ : Fin m → Fin n → ℝ) (u : Fin m ⊕ Fin n) (p : Fin m × Fin n) : ℝ :=
  Sum.elim (fun i => if p.1 = i then 1 / Δ p.1 p.2 else 0) (fun j => if p.2 = j then 1 else 0) u

lemma coef_ne_zero_mem {Δ : Fin m → Fin n → ℝ} {u : Fin m ⊕ Fin n} {p : Fin m × Fin n}
    (h : coef Δ u p ≠ 0) : u ∈ ends p := by
  rcases u with i | j
  · simp only [coef, Sum.elim_inl] at h
    split_ifs at h with h1
    · simp [ends, h1]
    · exact absurd rfl h
  · simp only [coef, Sum.elim_inr] at h
    split_ifs at h with h1
    · simp [ends, h1]
    · exact absurd rfl h

lemma sum_coef_inl (Δ d : Fin m → Fin n → ℝ) (i : Fin m) :
    ∑ p : Fin m × Fin n, d p.1 p.2 * coef Δ (Sum.inl i) p = ∑ j, d i j / Δ i j := by
  rw [Fintype.sum_prod_type]
  simp only [coef, Sum.elim_inl]
  rw [Finset.sum_eq_single i]
  · apply Finset.sum_congr rfl; intro j _; simp [div_eq_mul_inv]
  · intro i' _ hi'; apply Finset.sum_eq_zero; intro j _; simp [hi']
  · simp

lemma sum_coef_inr (Δ d : Fin m → Fin n → ℝ) (j : Fin n) :
    ∑ p : Fin m × Fin n, d p.1 p.2 * coef Δ (Sum.inr j) p = ∑ i, d i j := by
  rw [Fintype.sum_prod_type]
  simp only [coef, Sum.elim_inr]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_eq_single j]
  · simp
  · intro j' _ hj'; simp [hj']
  · simp

/-- A support of minimum size satisfies Hall's condition for edges versus endpoints. -/
lemma hall_cond (Δ : Fin m → Fin n → ℝ) (C : ℝ) (x : Fin m → Fin n → ℝ) (hx : Feas Δ C x)
    (hmin : ∀ y, Feas Δ C y → (supp x).card ≤ (supp y).card)
    (F : Finset (Fin m × Fin n)) (hF : F ⊆ supp x) :
    F.card ≤ (F.biUnion ends).card := by
  classical
  by_contra hlt
  push Not at hlt
  set V := F.biUnion ends with hV
  let v : F → (V → ℝ) := fun e u => coef Δ u.1 e.1
  have hnli : ¬ LinearIndependent ℝ v := by
    intro hli
    have := hli.fintype_card_le_finrank
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, Fintype.card_coe] at this
    omega
  rw [Fintype.not_linearIndependent_iff] at hnli
  obtain ⟨g, hg, e0, he0⟩ := hnli
  set d : Fin m → Fin n → ℝ := fun i j => if h : (i, j) ∈ F then g ⟨(i, j), h⟩ else 0 with hd
  have hdF : ∀ p : Fin m × Fin n, p ∉ F → d p.1 p.2 = 0 := by
    intro p hp; simp [hd, hp]
  have hdg : ∀ e : F, d e.1.1 e.1.2 = g e := by
    intro e; simp [hd, e.2]
  -- every vertex constraint vanishes
  have hall : ∀ u : Fin m ⊕ Fin n, ∑ p : Fin m × Fin n, d p.1 p.2 * coef Δ u p = 0 := by
    intro u
    by_cases huV : u ∈ V
    · have h1 := congrFun hg ⟨u, huV⟩
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, v] at h1
      have h2 : ∑ e : F, g e * coef Δ u e.1 = ∑ p ∈ F, d p.1 p.2 * coef Δ u p := by
        rw [← Finset.sum_coe_sort F]
        apply Finset.sum_congr rfl; intro e _; rw [hdg]
      rw [← Finset.sum_subset (Finset.subset_univ F)]
      · rw [← h2]; exact h1
      · intro p _ hp; rw [hdF p hp, zero_mul]
    · apply Finset.sum_eq_zero
      intro p _
      by_cases hpF : p ∈ F
      · have : coef Δ u p = 0 := by
          by_contra hc
          exact huV (Finset.mem_biUnion.2 ⟨p, hpF, coef_ne_zero_mem hc⟩)
        rw [this, mul_zero]
      · rw [hdF p hpF, zero_mul]
  have hjob : ∀ j, ∑ i, d i j = 0 := fun j => by rw [← sum_coef_inr Δ d j]; exact hall _
  have hmach : ∀ i, ∑ j, d i j / Δ i j = 0 := fun i => by rw [← sum_coef_inl Δ d i]; exact hall _
  have hdx : ∀ i j, d i j ≠ 0 → x i j ≠ 0 := by
    intro i j hne
    have : (i, j) ∈ F := by
      by_contra h; exact hne (hdF (i, j) h)
    exact mem_supp.1 (hF this)
  have hne : d e0.1.1 e0.1.2 ≠ 0 := by rw [hdg]; exact he0
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · obtain ⟨y, hy, hcard⟩ := perturb Δ C x d hx hdx hjob hmach ⟨_, _, hneg⟩
    exact absurd (hmin y hy) (not_le.2 hcard)
  · obtain ⟨y, hy, hcard⟩ := perturb Δ C x (fun i j => - d i j) hx
      (fun i j h => hdx i j (by simpa using h))
      (fun j => by simp [Finset.sum_neg_distrib, hjob j])
      (fun i => by
        have : ∑ j, -d i j / Δ i j = -∑ j, d i j / Δ i j := by
          rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro j _; ring
        rw [this, hmach i, neg_zero])
      ⟨_, _, by linarith⟩
    exact absurd (hmin y hy) (not_le.2 hcard)

/-- From any feasible point: a feasible point whose support edges inject into their endpoints
(an orientation with every in-degree at most one). -/
lemma exists_oriented (Δ : Fin m → Fin n → ℝ) (C : ℝ) (x0 : Fin m → Fin n → ℝ)
    (hx0 : Feas Δ C x0) :
    ∃ x, Feas Δ C x ∧ ∃ f : supp x → Fin m ⊕ Fin n, Function.Injective f ∧
      ∀ e, f e ∈ ends e.1 := by
  classical
  have hex : ∃ k, ∃ x, Feas Δ C x ∧ (supp x).card = k := ⟨_, x0, hx0, rfl⟩
  obtain ⟨x, hx, hk⟩ := Nat.find_spec hex
  have hmin : ∀ y, Feas Δ C y → (supp x).card ≤ (supp y).card := by
    intro y hy
    rw [hk]; exact Nat.find_min' hex ⟨y, hy, rfl⟩
  refine ⟨x, hx, ?_⟩
  rw [← Finset.all_card_le_biUnion_card_iff_exists_injective (fun e : supp x => ends e.1)]
  intro s
  have h := hall_cond Δ C x hx hmin (s.map (Function.Embedding.subtype _)) (by
    intro p hp
    obtain ⟨e, _, rfl⟩ := Finset.mem_map.1 hp
    exact e.2)
  have heq : (s.map (Function.Embedding.subtype _)).biUnion ends =
      s.biUnion (fun e : supp x => ends e.1) := by
    ext u; simp [Finset.mem_biUnion]
  rw [Finset.card_map, heq] at h
  exact h
end LP

-- ===== approximate core =====
/-- Linear functionals on `(Fin m → ℝ) × ℝ` in coordinates. -/
lemma dual_coords {m : ℕ} (f : StrongDual ℝ ((Fin m → ℝ) × ℝ)) (p : (Fin m → ℝ) × ℝ) :
    f p = ∑ i, p.1 i * f (Pi.single i 1, 0) + p.2 * f (0, 1) := by
  have hp : p = ∑ i, p.1 i • ((Pi.single i 1 : Fin m → ℝ), (0 : ℝ)) + p.2 • ((0 : Fin m → ℝ), (1 : ℝ)) := by
    ext j
    · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · simp [Prod.snd_sum]
  conv_lhs => rw [hp]
  rw [map_add, map_sum, map_smul]
  simp only [map_smul, smul_eq_mul]

set_option maxHeartbeats 1000000 in
/-- Approximate XOS core: a fractionally subadditive nonnegative `g` and nonempty `S` admit, for each
`ε > 0`, an additive `Δ` with `Δ(T) ≤ g T` on nonempty `T ⊆ S` and `Δ(S) ≥ g S - ε`. -/
lemma approx_core {m : ℕ} (g : Finset (Fin m) → ℝ) (hFS : FractionallySubadditive g)
    (S : Finset (Fin m)) (hS : S.Nonempty) (ε : ℝ) (hε : 0 < ε) :
    ∃ Δ : Fin m → ℝ, g S - ε ≤ ∑ i ∈ S, Δ i ∧
      ∀ T, T ⊆ S → T.Nonempty → ∑ i ∈ T, Δ i ≤ g T := by
  classical
  obtain ⟨i0, hi0⟩ := hS
  let P := {T : Finset (Fin m) // T ⊆ S ∧ T.Nonempty}
  let φ : Finset (Fin m) → (Fin m → ℝ) × ℝ := fun T => (fun i => if i ∈ T then 1 else 0, g T)
  let Φ : (P → ℝ) → (Fin m → ℝ) × ℝ := fun l => ∑ T : P, l T • φ T.1
  have hΦlin : IsLinearMap ℝ Φ := by
    constructor
    · intro x y; simp only [Φ, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    · intro c x; simp only [Φ, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
  let K := Φ '' stdSimplex ℝ P
  have hKc : IsCompact K := (isCompact_stdSimplex ℝ P).image (by
    apply continuous_finset_sum; intro T _
    exact (continuous_apply T).smul continuous_const)
  have hKv : Convex ℝ K := (convex_stdSimplex ℝ P).is_linear_image hΦlin
  let w : (Fin m → ℝ) × ℝ := (fun i => if i ∈ S then 1 else 0, g S - ε)
  let R : Set ((Fin m → ℝ) × ℝ) := {p | 0 ≤ p.1 i0 ∧ p = p.1 i0 • w}
  have hRc : IsClosed R := by
    apply IsClosed.inter
    · exact isClosed_le continuous_const ((continuous_apply i0).comp continuous_fst)
    · exact isClosed_eq continuous_id (((continuous_apply i0).comp continuous_fst).smul continuous_const)
  have hRv : Convex ℝ R := by
    intro p hp q hq a b ha hb hab
    refine ⟨?_, ?_⟩
    · simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [hp.1, hq.1]
    · have e1 := hp.2; have e2 := hq.2
      conv_lhs => rw [e1, e2]
      simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul,
        smul_smul]
  have hcoord1 : ∀ (l : P → ℝ) (i : Fin m), (Φ l).1 i = ∑ T : P, l T * (if i ∈ T.1 then 1 else 0) := by
    intro l i; simp [Φ, φ, Prod.fst_sum, Finset.sum_apply]
  have hcoord2 : ∀ (l : P → ℝ), (Φ l).2 = ∑ T : P, l T * g T.1 := by
    intro l; simp [Φ, φ, Prod.snd_sum]
  -- disjointness: this is where fractional subadditivity enters
  have hdisj : Disjoint K R := by
    rw [Set.disjoint_left]
    rintro _ ⟨l, hl, rfl⟩ ⟨hs0, hsw⟩
    set s := (Φ l).1 i0 with hs
    have hl0 : ∀ T, 0 ≤ l T := hl.1
    have hl1 : ∑ T, l T = 1 := hl.2
    have hcov : ∀ i ∈ S, ∑ T : P, l T * (if i ∈ T.1 then 1 else 0) = s := by
      intro i hi
      rw [← hcoord1, hsw]
      simp [w, hi]
    have hval : ∑ T : P, l T * g T.1 = s * (g S - ε) := by
      rw [← hcoord2, hsw]; simp [w]
    have hlT : ∀ T : P, l T ≤ s := by
      intro T
      obtain ⟨i, hi⟩ := T.2.2
      rw [← hcov i (T.2.1 hi)]
      calc l T = l T * (if i ∈ T.1 then 1 else 0) := by simp [hi]
        _ ≤ ∑ T' : P, l T' * (if i ∈ T'.1 then 1 else 0) :=
          Finset.single_le_sum (f := fun T' : P => l T' * (if i ∈ T'.1 then 1 else 0))
            (fun T' _ => mul_nonneg (hl0 T') (by split_ifs <;> norm_num)) (Finset.mem_univ T)
    have hspos : 0 < s := by
      rcases hs0.lt_or_eq with h | h
      · exact h
      · exfalso
        have hall : ∀ T : P, l T = 0 := fun T => le_antisymm (h ▸ hlT T) (hl0 T)
        simp [hall] at hl1
    -- the fractional cover
    let α : Finset (Fin m) → ℝ := fun U => if h : U ⊆ S ∧ U.Nonempty then l ⟨U, h⟩ / s else 0
    have hα01 : ∀ U, 0 ≤ α U ∧ α U ≤ 1 := by
      intro U
      simp only [α]
      split_ifs with h
      · exact ⟨div_nonneg (hl0 _) hspos.le, (div_le_one hspos).2 (hlT _)⟩
      · exact ⟨le_refl _, zero_le_one⟩
    -- sums over the powerset reduce to sums over P
    have hred : ∀ c : Finset (Fin m) → ℝ,
        ∑ U ∈ S.powerset, α U * c U = ∑ T : P, l T / s * c T.1 := by
      intro c
      have h1 : ∑ U ∈ S.powerset, α U * c U =
          ∑ U ∈ S.powerset.filter (fun U => U.Nonempty), α U * c U := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro U _
        split_ifs with h
        · rfl
        · simp [α, h]
      rw [h1, Finset.sum_subtype (p := fun U => U ⊆ S ∧ U.Nonempty)]
      · apply Finset.sum_congr rfl
        intro T _
        simp [α, T.2]
      · intro U; simp
    have hcov' : ∀ i ∈ S, 1 ≤ ∑ U ∈ S.powerset.filter (fun U => i ∈ U), α U := by
      intro i hi
      have : ∑ U ∈ S.powerset.filter (fun U => i ∈ U), α U =
          ∑ U ∈ S.powerset, α U * (if i ∈ U then 1 else 0) := by
        rw [Finset.sum_filter]; apply Finset.sum_congr rfl; intro U _; split_ifs <;> simp
      rw [this, hred]
      have : ∑ T : P, l T / s * (if i ∈ T.1 then 1 else 0) =
          (∑ T : P, l T * (if i ∈ T.1 then 1 else 0)) / s := by
        rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro T _; ring
      rw [this, hcov i hi, div_self hspos.ne']
    have key := hFS S α hα01 hcov'
    rw [hred] at key
    have : ∑ T : P, l T / s * g T.1 = (∑ T : P, l T * g T.1) / s := by
      rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro T _; ring
    rw [this, hval, mul_div_cancel_left₀ _ hspos.ne'] at key
    linarith
  obtain ⟨f, u, v, hfK, huv, hfR⟩ := geometric_hahn_banach_compact_closed hKv hKc hRv hRc hdisj
  -- values of f
  set a : Fin m → ℝ := fun i => f (Pi.single i 1, 0) with ha
  set μ := f (0, 1) with hμ
  have hf : ∀ p, f p = ∑ i, p.1 i * a i + p.2 * μ := fun p => dual_coords f p
  have hφK : ∀ T : P, φ T.1 ∈ K := by
    intro T
    refine ⟨Pi.single T 1, ⟨fun T' => ?_, ?_⟩, ?_⟩
    · simp only [Pi.single_apply]; split_ifs <;> norm_num
    · simp
    · simp [Φ, Pi.single_apply]
  have hfT : ∀ T : P, ∑ i ∈ T.1, a i + μ * g T.1 < u := by
    intro T
    have := hfK _ (hφK T)
    rw [hf] at this
    simp only [φ, ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter] at this
    linarith
  have h0R : (0 : (Fin m → ℝ) × ℝ) ∈ R := by simp [R]
  have hv0 : v < 0 := by have := hfR 0 h0R; simpa using this
  have hw0 : w.1 i0 = 1 := by simp [w, hi0]
  have hsR : ∀ s : ℝ, 0 ≤ s → s • w ∈ R := by
    intro s hs
    refine ⟨?_, ?_⟩
    · simp [hw0, hs]
    · simp [hw0]
  have hfw : 0 ≤ f w := by
    by_contra hneg
    push Not at hneg
    have := hfR _ (hsR (v / f w) (div_nonneg_of_nonpos hv0.le hneg.le))
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hneg.ne] at this
    linarith
  rw [hf] at hfw
  simp only [w, ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter] at hfw
  have hSP : S ⊆ S ∧ S.Nonempty := ⟨subset_refl _, ⟨i0, hi0⟩⟩
  have hfS := hfT ⟨S, hSP⟩
  simp only at hfS
  have hμneg : μ < 0 := by nlinarith
  refine ⟨fun i => a i / (-μ), ?_, ?_⟩
  · rw [← Finset.sum_div, le_div_iff₀ (by linarith)]
    nlinarith
  · intro T hTS hTne
    have := hfT ⟨T, hTS, hTne⟩
    simp only at this
    rw [← Finset.sum_div, div_le_iff₀ (by linarith)]
    nlinarith

-- ===== rounding =====
section Round

variable {m n : ℕ}

/-- Support edge `(i, j)` oriented towards the job (`i` is the in-neighbour of `j`). -/
def InE (x : Fin m → Fin n → ℝ) (f : supp x → Fin m ⊕ Fin n) (i : Fin m) (j : Fin n) : Prop :=
  ∃ h : x i j ≠ 0, f ⟨(i, j), mem_supp.2 h⟩ = Sum.inr j

/-- Support edge `(i, j)` oriented towards the machine (`i ∈ S̄ⱼ`). -/
def OutE (x : Fin m → Fin n → ℝ) (f : supp x → Fin m ⊕ Fin n) (i : Fin m) (j : Fin n) : Prop :=
  ∃ h : x i j ≠ 0, f ⟨(i, j), mem_supp.2 h⟩ = Sum.inl i

lemma in_or_out {x : Fin m → Fin n → ℝ} {f : supp x → Fin m ⊕ Fin n}
    (hfe : ∀ e, f e ∈ ends e.1) {i : Fin m} {j : Fin n} (h : x i j ≠ 0) :
    InE x f i j ∨ OutE x f i j := by
  have := hfe ⟨(i, j), mem_supp.2 h⟩
  simp only [ends, Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with h1 | h1
  · exact Or.inr ⟨h, h1⟩
  · exact Or.inl ⟨h, h1⟩

lemma not_in_out {x : Fin m → Fin n → ℝ} {f : supp x → Fin m ⊕ Fin n} {i : Fin m} {j : Fin n}
    (h1 : InE x f i j) (h2 : OutE x f i j) : False := by
  obtain ⟨h, e1⟩ := h1
  obtain ⟨h', e2⟩ := h2
  exact Sum.inr_ne_inl (e1.symm.trans e2)

lemma in_unique {x : Fin m → Fin n → ℝ} {f : supp x → Fin m ⊕ Fin n} (hf : Function.Injective f)
    {i i' : Fin m} {j : Fin n} (h1 : InE x f i j) (h2 : InE x f i' j) : i = i' := by
  obtain ⟨h, e1⟩ := h1
  obtain ⟨h', e2⟩ := h2
  have := congrArg (fun e : supp x => e.1.1) (hf (e1.trans e2.symm))
  simpa using this

lemma out_unique {x : Fin m → Fin n → ℝ} {f : supp x → Fin m ⊕ Fin n} (hf : Function.Injective f)
    {i : Fin m} {j j' : Fin n} (h1 : OutE x f i j) (h2 : OutE x f i j') : j = j' := by
  obtain ⟨h, e1⟩ := h1
  obtain ⟨h', e2⟩ := h2
  have := congrArg (fun e : supp x => e.1.2) (hf (e1.trans e2.symm))
  simpa using this

open Classical in
/-- `ℓᵢ`: the LP load on machine `i` of the Type 1 jobs whose in-edge comes from `i`. -/
noncomputable def ell (Δ x : Fin m → Fin n → ℝ) (f : supp x → Fin m ⊕ Fin n) (i : Fin m) : ℝ :=
  ∑ j, if InE x f i j ∧ 1 / 2 < x i j then x i j / Δ i j else 0

lemma inv_ofReal_le {a b : ℝ} (hb : 0 < b) (h : 1 / b ≤ a) :
    (ENNReal.ofReal a)⁻¹ ≤ ENNReal.ofReal b := by
  have ha : 0 < a := lt_of_lt_of_le (by positivity) h
  rw [← ENNReal.ofReal_inv_of_pos ha]
  apply ENNReal.ofReal_le_ofReal
  rw [inv_le_comm₀ ha hb]
  simpa [one_div] using h

lemma q_nonneg {Δ x : Fin m → Fin n → ℝ} {C : ℝ} (hx : Feas Δ C x) (i : Fin m) (j : Fin n) :
    0 ≤ x i j / Δ i j := by
  by_cases h : x i j = 0
  · simp [h]
  · exact div_nonneg (hx.1 i j) (hx.2.1 i j h).le

lemma ell_nonneg {Δ x : Fin m → Fin n → ℝ} {C : ℝ} (hx : Feas Δ C x)
    (f : supp x → Fin m ⊕ Fin n) (i : Fin m) : 0 ≤ ell Δ x f i := by
  classical
  unfold ell
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact q_nonneg hx i j
  · exact le_refl _

lemma ell_le {Δ x : Fin m → Fin n → ℝ} {C : ℝ} (hx : Feas Δ C x)
    (f : supp x → Fin m ⊕ Fin n) (i : Fin m) : ell Δ x f i ≤ C := by
  classical
  refine le_trans ?_ (hx.2.2.2 i)
  unfold ell
  apply Finset.sum_le_sum
  intro j _
  split_ifs
  · exact le_refl _
  · exact q_nonneg hx i j

lemma ell_add_le {Δ x : Fin m → Fin n → ℝ} {C : ℝ} (hx : Feas Δ C x)
    (f : supp x → Fin m ⊕ Fin n) {i : Fin m} {j : Fin n} (hout : OutE x f i j) :
    ell Δ x f i + x i j / Δ i j ≤ C := by
  classical
  refine le_trans ?_ (hx.2.2.2 i)
  unfold ell
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  have hj : ¬ (InE x f i j ∧ 1 / 2 < x i j) := fun h => not_in_out h.1 hout
  rw [if_neg hj, zero_add, add_comm]
  apply add_le_add (le_refl _)
  apply Finset.sum_le_sum
  intro j' _
  split_ifs
  · exact le_refl _
  · exact q_nonneg hx i j'

lemma type1_bound (g : Fin n → Finset (Fin m) → ℝ) {Δ x : Fin m → Fin n → ℝ} {C : ℝ}
    (hx : Feas Δ C x)
    (hΔg : ∀ j (T : Finset (Fin m)), T.Nonempty → (∀ i ∈ T, 0 < Δ i j) → ∑ i ∈ T, Δ i j ≤ g j T)
    {i : Fin m} {j : Fin n} (hx2 : 1 / 2 < x i j) :
    MalleableSched.procTime g j {i} ≤ ENNReal.ofReal (2 * (x i j / Δ i j)) := by
  have hxne : x i j ≠ 0 := by intro h; rw [h] at hx2; norm_num at hx2
  have hΔ : 0 < Δ i j := hx.2.1 i j hxne
  have hg : Δ i j ≤ g j {i} := by
    have := hΔg j {i} (Finset.singleton_nonempty i) (by simpa using hΔ)
    simpa using this
  unfold MalleableSched.procTime
  apply inv_ofReal_le (by positivity)
  have hxpos : 0 < x i j := by linarith
  rw [one_div, inv_le_iff_one_le_mul₀ (by positivity), mul_comm]
  calc (1 : ℝ) ≤ 2 * x i j := by linarith
    _ = 2 * (x i j / Δ i j) * Δ i j := by field_simp
    _ ≤ 2 * (x i j / Δ i j) * g j {i} := by
        apply mul_le_mul_of_nonneg_left hg; positivity

/-- Per-job choice of the reduced machine set (Type 1: one machine; Type 2: a threshold set). -/
lemma job_choice (g : Fin n → Finset (Fin m) → ℝ) (Δ : Fin m → Fin n → ℝ) (C : ℝ)
    (hΔg : ∀ j (T : Finset (Fin m)), T.Nonempty → (∀ i ∈ T, 0 < Δ i j) → ∑ i ∈ T, Δ i j ≤ g j T)
    (x : Fin m → Fin n → ℝ) (hx : Feas Δ C x) (f : supp x → Fin m ⊕ Fin n)
    (hf : Function.Injective f) (hfe : ∀ e, f e ∈ ends e.1) (j : Fin n) :
    ∃ Tj : Finset (Fin m), Tj.Nonempty ∧ ((∃ i, Tj = {i} ∧ InE x f i j ∧ 1 / 2 < x i j) ∨
      ((∀ i ∈ Tj, OutE x f i j) ∧ ∀ i ∈ Tj,
        MalleableSched.procTime g j Tj ≤
          ENNReal.ofReal (2 * Real.exp 1 / (Real.exp 1 - 1) * C - 2 * ell Δ x f i) ∧
        0 ≤ 2 * Real.exp 1 / (Real.exp 1 - 1) * C - 2 * ell Δ x f i)) := by
  classical
  by_cases h1 : ∃ i, InE x f i j ∧ 1 / 2 < x i j
  · obtain ⟨i, hi⟩ := h1
    exact ⟨{i}, Finset.singleton_nonempty i, Or.inl ⟨i, rfl, hi⟩⟩
  push Not at h1
  set α := 2 * Real.exp 1 / (Real.exp 1 - 1) with hα
  have hα3 : 3 ≤ α := const_ge_three
  set Sb := Finset.univ.filter (fun i => OutE x f i j) with hSb
  have hmemSb : ∀ i, i ∈ Sb ↔ OutE x f i j := fun i => by simp [hSb]
  have hxpos : ∀ i ∈ Sb, 0 < x i j := by
    intro i hi
    obtain ⟨h, _⟩ := (hmemSb i).1 hi
    exact lt_of_le_of_ne (hx.1 i j) (Ne.symm h)
  have hqpos : ∀ i ∈ Sb, 0 < x i j / Δ i j := by
    intro i hi
    exact div_pos (hxpos i hi) (hx.2.1 i j (hxpos i hi).ne')
  have hℓC : ∀ i ∈ Sb, ell Δ x f i < C := by
    intro i hi
    have := ell_add_le hx f ((hmemSb i).1 hi)
    linarith [hqpos i hi]
  -- the out-edges carry at least half of the job
  have hsum : 1 / 2 ≤ ∑ i ∈ Sb, x i j := by
    have htot := hx.2.2.1 j
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => OutE x f i j)] at htot
    have hrest : ∑ i ∈ Finset.univ.filter (fun i => ¬ OutE x f i j), x i j ≤ 1 / 2 := by
      by_cases hin : ∃ i0, InE x f i0 j
      · obtain ⟨i0, hi0⟩ := hin
        have : ∑ i ∈ Finset.univ.filter (fun i => ¬ OutE x f i j), x i j =
            ∑ i ∈ Finset.univ.filter (fun i => ¬ OutE x f i j), if i0 = i then x i j else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          split_ifs with hii
          · rfl
          · by_contra hne
            have hnout : ¬ OutE x f i j := by simpa using hi
            rcases in_or_out hfe hne with hin' | hout'
            · exact hii (in_unique hf hi0 hin')
            · exact hnout hout'
        rw [this, Finset.sum_ite_eq]
        split_ifs
        · exact h1 i0 hi0
        · norm_num
      · push Not at hin
        have : ∀ i ∈ Finset.univ.filter (fun i => ¬ OutE x f i j), x i j = 0 := by
          intro i hi
          by_contra hne
          have hnout : ¬ OutE x f i j := by simpa using hi
          rcases in_or_out hfe hne with hin' | hout'
          · exact hin i hin'
          · exact hnout hout'
        rw [Finset.sum_eq_zero this]; norm_num
    rw [← hSb] at htot
    linarith
  have hSbne : Sb.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hsum
    norm_num at hsum
  set w : Fin m → ℝ := fun i => x i j / (C - ell Δ x f i) with hw
  obtain ⟨k, hkSb, hk⟩ := thr_exists (ell Δ x f) w C Sb hSbne
    (fun i _ => ell_nonneg hx f i) hℓC
    (fun i hi => div_nonneg (hx.1 i j) (by linarith [hℓC i hi]))
    (by
      refine le_trans hsum (le_of_eq ?_)
      apply Finset.sum_congr rfl
      intro i hi
      simp only [hw]
      field_simp [(by linarith [hℓC i hi] : C - ell Δ x f i ≠ 0)])
  set Tj := Sb.filter (fun i => ell Δ x f i ≤ ell Δ x f k) with hTj
  have hkT : k ∈ Tj := by simp [hTj, hkSb]
  have hTSb : ∀ i ∈ Tj, i ∈ Sb := fun i hi => (Finset.mem_filter.1 hi).1
  have hTℓ : ∀ i ∈ Tj, ell Δ x f i ≤ ell Δ x f k := fun i hi => (Finset.mem_filter.1 hi).2
  have hkpos : 0 < α * C - 2 * ell Δ x f k := by
    have := hℓC k hkSb
    have := ell_nonneg hx f k
    nlinarith
  -- g on the threshold set
  have hwΔ : ∀ i ∈ Sb, w i ≤ Δ i j := by
    intro i hi
    have hle := ell_add_le hx f ((hmemSb i).1 hi)
    have hΔp : 0 < Δ i j := hx.2.1 i j (hxpos i hi).ne'
    have hCl : 0 < C - ell Δ x f i := by linarith [hℓC i hi]
    simp only [hw]
    rw [div_le_iff₀ hCl]
    have : x i j / Δ i j ≤ C - ell Δ x f i := by linarith
    rw [div_le_iff₀ hΔp] at this
    linarith
  have hgT : 1 / (α * C - 2 * ell Δ x f k) ≤ g j Tj := by
    refine le_trans hk (le_trans ?_ (hΔg j Tj ⟨k, hkT⟩ ?_))
    · exact Finset.sum_le_sum (fun i hi => hwΔ i (hTSb i hi))
    · intro i hi
      exact hx.2.1 i j (hxpos i (hTSb i hi)).ne'
  refine ⟨Tj, ⟨k, hkT⟩, Or.inr ⟨fun i hi => (hmemSb i).1 (hTSb i hi), fun i hi => ?_⟩⟩
  have hℓik := hTℓ i hi
  refine ⟨?_, by nlinarith [hTℓ i hi]⟩
  unfold MalleableSched.procTime
  refine le_trans (inv_ofReal_le hkpos hgT) (ENNReal.ofReal_le_ofReal (by linarith))

end Round


-- ===== rounding assembly =====
section Round2

variable {m n : ℕ}

open Classical in
lemma ell_sum_ge {Δ x : Fin m → Fin n → ℝ} {C : ℝ} (hx : Feas Δ C x)
    (f : supp x → Fin m ⊕ Fin n) (i : Fin m) (s : Finset (Fin n))
    (hs : ∀ j ∈ s, InE x f i j ∧ 1 / 2 < x i j) : ∑ j ∈ s, x i j / Δ i j ≤ ell Δ x f i := by
  unfold ell
  calc ∑ j ∈ s, x i j / Δ i j
      = ∑ j ∈ s, (if InE x f i j ∧ 1 / 2 < x i j then x i j / Δ i j else 0) :=
        Finset.sum_congr rfl (fun j hj => by rw [if_pos (hs j hj)])
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) (fun j _ _ => by
        split_ifs
        · exact q_nonneg hx i j
        · exact le_refl _)

/-- The rounding of a feasible oriented (LP1) point: a well-structured assignment with
`L ≤ (2e/(e-1)) C`. -/
theorem round_main (g : Fin n → Finset (Fin m) → ℝ) (Δ : Fin m → Fin n → ℝ) (C : ℝ) (hC : 0 < C)
    (hΔg : ∀ j (T : Finset (Fin m)), T.Nonempty → (∀ i ∈ T, 0 < Δ i j) → ∑ i ∈ T, Δ i j ≤ g j T)
    (x : Fin m → Fin n → ℝ) (hx : Feas Δ C x) (f : supp x → Fin m ⊕ Fin n)
    (hf : Function.Injective f) (hfe : ∀ e, f e ∈ ends e.1) :
    ∃ T : Fin n → Finset (Fin m), MalleableSched.IsAssignment T ∧ MalleableSched.WellStructured T ∧
      MalleableSched.maxLoad g T ≤ ENNReal.ofReal (2 * Real.exp 1 / (Real.exp 1 - 1) * C) := by
  classical
  choose T hTne hT using job_choice g Δ C hΔg x hx f hf hfe
  have hout_of : ∀ i j, i ∈ T j → ¬ (InE x f i j ∧ 1 / 2 < x i j) → OutE x f i j := by
    intro i j hij hn
    rcases hT j with ⟨i', hi', hin, hx2⟩ | ⟨hout, _⟩
    · rw [hi', Finset.mem_singleton] at hij
      subst hij
      exact absurd ⟨hin, hx2⟩ hn
    · exact hout i hij
  refine ⟨T, hTne, ?_, ?_⟩
  · have r : ∀ j, 1 < (T j).card → ∀ i ∈ T j, OutE x f i j := by
      intro j hc
      rcases hT j with ⟨i, hi, _⟩ | ⟨hout, _⟩
      · rw [hi, Finset.card_singleton] at hc; omega
      · exact hout
    apply ws_of_disjoint
    intro j j' hjj' hc hc'
    rw [Finset.disjoint_left]
    intro i hi hi'
    exact hjj' (out_unique hf (r j hc i hi) (r j' hc' i hi'))
  · apply maxLoad_le_of
    intro i
    set α := 2 * Real.exp 1 / (Real.exp 1 - 1) with hα
    have hα3 : (3 : ℝ) ≤ α := const_ge_three
    set bnd : Fin n → ℝ := fun j => if InE x f i j ∧ 1 / 2 < x i j then 2 * (x i j / Δ i j)
      else α * C - 2 * ell Δ x f i with hbnd
    set Fi := Finset.univ.filter (fun j => i ∈ T j) with hFi
    have hper : ∀ j ∈ Fi, MalleableSched.procTime g j (T j) ≤ ENNReal.ofReal (bnd j) ∧
        0 ≤ bnd j := by
      intro j hj
      have hij : i ∈ T j := (Finset.mem_filter.1 hj).2
      rcases hT j with ⟨i', hi', hin, hx2⟩ | ⟨hout, hb⟩
      · rw [hi', Finset.mem_singleton] at hij
        subst hij
        have hc : InE x f i j ∧ 1 / 2 < x i j := ⟨hin, hx2⟩
        simp only [hbnd, if_pos hc]
        rw [hi']
        exact ⟨type1_bound g hx hΔg hx2, by have := q_nonneg hx i j; linarith⟩
      · have hc : ¬ (InE x f i j ∧ 1 / 2 < x i j) := fun h => not_in_out h.1 (hout i hij)
        simp only [hbnd, if_neg hc]
        exact hb i hij
    calc ∑ j ∈ Fi, MalleableSched.procTime g j (T j) ≤ ∑ j ∈ Fi, ENNReal.ofReal (bnd j) :=
          Finset.sum_le_sum (fun j hj => (hper j hj).1)
      _ = ENNReal.ofReal (∑ j ∈ Fi, bnd j) :=
          (ENNReal.ofReal_sum_of_nonneg (fun j hj => (hper j hj).2)).symm
      _ ≤ ENNReal.ofReal (α * C) := by
          apply ENNReal.ofReal_le_ofReal
          rw [← Finset.sum_filter_add_sum_filter_not Fi (fun j => InE x f i j ∧ 1 / 2 < x i j)]
          have hA : ∑ j ∈ Fi.filter (fun j => InE x f i j ∧ 1 / 2 < x i j), bnd j ≤
              2 * ell Δ x f i := by
            have e1 : ∑ j ∈ Fi.filter (fun j => InE x f i j ∧ 1 / 2 < x i j), bnd j =
                ∑ j ∈ Fi.filter (fun j => InE x f i j ∧ 1 / 2 < x i j), 2 * (x i j / Δ i j) :=
              Finset.sum_congr rfl (fun j hj => by
                simp only [hbnd, if_pos (Finset.mem_filter.1 hj).2])
            rw [e1, ← Finset.mul_sum]
            have := ell_sum_ge hx f i (Fi.filter (fun j => InE x f i j ∧ 1 / 2 < x i j))
              (fun j hj => (Finset.mem_filter.1 hj).2)
            linarith
          have hB : (Fi.filter (fun j => ¬ (InE x f i j ∧ 1 / 2 < x i j))).card ≤ 1 := by
            rw [Finset.card_le_one]
            intro j hj j' hj'
            have hj1 := Finset.mem_filter.1 hj
            have hj1' := Finset.mem_filter.1 hj'
            exact out_unique hf (hout_of i j (Finset.mem_filter.1 hj1.1).2 hj1.2)
              (hout_of i j' (Finset.mem_filter.1 hj1'.1).2 hj1'.2)
          have hBsum : ∑ j ∈ Fi.filter (fun j => ¬ (InE x f i j ∧ 1 / 2 < x i j)), bnd j =
              ((Fi.filter (fun j => ¬ (InE x f i j ∧ 1 / 2 < x i j))).card : ℝ) *
                (α * C - 2 * ell Δ x f i) := by
            have e2 : ∑ j ∈ Fi.filter (fun j => ¬ (InE x f i j ∧ 1 / 2 < x i j)), bnd j =
                ∑ j ∈ Fi.filter (fun j => ¬ (InE x f i j ∧ 1 / 2 < x i j)),
                  (α * C - 2 * ell Δ x f i) :=
              Finset.sum_congr rfl (fun j hj => by
                simp only [hbnd, if_neg (Finset.mem_filter.1 hj).2])
            rw [e2, Finset.sum_const, nsmul_eq_mul]
          have hℓ := ell_le hx f i
          have hℓ0 := ell_nonneg hx f i
          rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hB with h0 | h1
          · rw [hBsum, h0]
            push_cast
            nlinarith
          · rw [hBsum, h1]
            push_cast
            linarith

end Round2


section StepE

/-- One approximation step: for `δ ∈ (0,1)`, the ε-XOS cores of the jobs give a feasible (LP1)
point with load bound `C/(1-δ)`, which rounds to a well-structured assignment. -/
lemma delta_step {n m : ℕ} (g : Fin n → Finset (Fin m) → ℝ)
    (hFS : ∀ j, FractionallySubadditive (g j))
    (S : Fin n → Finset (Fin m)) (hS : IsAssignment S) (C : ℝ) (hC : 0 < C)
    (hgpos : ∀ j, 0 < g j (S j))
    (hload : ∀ i : Fin m, ∑ j ∈ Finset.univ.filter (fun j => i ∈ S j), 1 / g j (S j) ≤ C)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ T : Fin n → Finset (Fin m), IsAssignment T ∧ WellStructured T ∧
      maxLoad g T ≤ ENNReal.ofReal (2 * Real.exp 1 / (Real.exp 1 - 1) * (C / (1 - δ))) := by
  choose Δj hΔj1 hΔj2 using fun j => approx_core (g j) (hFS j) (S j) (hS j)
    (δ * g j (S j)) (mul_pos hδ (hgpos j))
  obtain ⟨Δ', hΔ'⟩ : ∃ Δ' : Fin m → Fin n → ℝ,
      Δ' = fun i j => if i ∈ S j ∧ 0 < Δj j i then Δj j i else 0 := ⟨_, rfl⟩
  have hΔ'nn : ∀ i j, 0 ≤ Δ' i j := by
    intro i j; rw [hΔ']; dsimp only; split_ifs with h
    · exact h.2.le
    · exact le_refl _
  have hΔ'pos : ∀ i j, Δ' i j ≠ 0 → i ∈ S j ∧ 0 < Δj j i ∧ Δ' i j = Δj j i := by
    intro i j h; rw [hΔ'] at h ⊢; dsimp only at h ⊢; split_ifs at h ⊢ with hc
    · exact ⟨hc.1, hc.2, rfl⟩
    · exact absurd rfl h
  obtain ⟨D, hD⟩ : ∃ D : Fin n → ℝ, D = fun j => ∑ i, Δ' i j := ⟨_, rfl⟩
  have h1δ : 0 < 1 - δ := by linarith
  have hDge : ∀ j, (1 - δ) * g j (S j) ≤ D j := by
    intro j
    calc (1 - δ) * g j (S j) = g j (S j) - δ * g j (S j) := by ring
      _ ≤ ∑ i ∈ S j, Δj j i := hΔj1 j
      _ ≤ ∑ i ∈ S j, Δ' i j := by
          apply Finset.sum_le_sum; intro i hi
          rw [hΔ']; dsimp only; split_ifs with h
          · exact le_refl _
          · push Not at h; exact h hi
      _ ≤ D j := by
          rw [hD]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun i _ _ => hΔ'nn i j)
  have hDpos : ∀ j, 0 < D j := fun j => lt_of_lt_of_le (mul_pos h1δ (hgpos j)) (hDge j)
  obtain ⟨x0, hx0⟩ : ∃ x0 : Fin m → Fin n → ℝ, x0 = fun i j => Δ' i j / D j := ⟨_, rfl⟩
  have hfeas : Feas Δ' (C / (1 - δ)) x0 := by
    refine ⟨fun i j => by rw [hx0]; exact div_nonneg (hΔ'nn i j) (hDpos j).le, ?_, ?_, ?_⟩
    · intro i j h
      have hne : Δ' i j ≠ 0 := by
        intro h0; apply h; rw [hx0]; dsimp only; rw [h0, zero_div]
      obtain ⟨_, hp, he⟩ := hΔ'pos i j hne
      rw [he]; exact hp
    · intro j
      have hsum : ∑ i, x0 i j = 1 := by
        rw [hx0]; dsimp only; rw [← Finset.sum_div]
        have : ∑ i, Δ' i j = D j := by rw [hD]
        rw [this]; exact div_self (hDpos j).ne'
      rw [hsum]
    · intro i
      have hterm : ∀ j, x0 i j / Δ' i j ≤
          (1 / (1 - δ)) * (if i ∈ S j then 1 / g j (S j) else 0) := by
        intro j
        by_cases hz : Δ' i j = 0
        · rw [hz, div_zero]
          apply mul_nonneg (le_of_lt (one_div_pos.2 h1δ))
          split_ifs
          · exact (one_div_pos.2 (hgpos j)).le
          · exact le_refl _
        · obtain ⟨hiS, _, _⟩ := hΔ'pos i j hz
          rw [if_pos hiS]
          have hxe : x0 i j / Δ' i j = 1 / D j := by
            rw [hx0]; dsimp only
            have hD0 : D j ≠ 0 := (hDpos j).ne'
            field_simp
          rw [hxe, one_div_mul_one_div]
          exact one_div_le_one_div_of_le (mul_pos h1δ (hgpos j)) (hDge j)
      calc ∑ j, x0 i j / Δ' i j
          ≤ ∑ j, (1 / (1 - δ)) * (if i ∈ S j then 1 / g j (S j) else 0) :=
            Finset.sum_le_sum (fun j _ => hterm j)
        _ = (1 / (1 - δ)) * ∑ j ∈ Finset.univ.filter (fun j => i ∈ S j), 1 / g j (S j) := by
            rw [← Finset.mul_sum, Finset.sum_filter]
        _ ≤ (1 / (1 - δ)) * C :=
            mul_le_mul_of_nonneg_left (hload i) (le_of_lt (one_div_pos.2 h1δ))
        _ = C / (1 - δ) := by ring
  have hΔg : ∀ j (T : Finset (Fin m)), T.Nonempty → (∀ i ∈ T, 0 < Δ' i j) →
      ∑ i ∈ T, Δ' i j ≤ g j T := by
    intro j T hT hpos
    have hsub : T ⊆ S j := fun i hi => (hΔ'pos i j (hpos i hi).ne').1
    calc ∑ i ∈ T, Δ' i j = ∑ i ∈ T, Δj j i :=
          Finset.sum_congr rfl (fun i hi => (hΔ'pos i j (hpos i hi).ne').2.2)
      _ ≤ g j T := hΔj2 j T hsub hT
  obtain ⟨x, hx, f, hf, hfe⟩ := exists_oriented Δ' (C / (1 - δ)) x0 hfeas
  exact round_main g Δ' (C / (1 - δ)) (div_pos hC h1δ) hΔg x hx f hf hfe

end StepE

end MalleableSched3d

open MalleableSched in
theorem solution {n m : ℕ} (g : Fin n → Finset (Fin m) → ℝ) (hg0 : ∀ j S, 0 ≤ g j S)
    (hFS : ∀ j, FractionallySubadditive (g j))
    (S : Fin n → Finset (Fin m)) (hS : IsAssignment S) :
    ∃ S' : Fin n → Finset (Fin m), IsAssignment S' ∧ WellStructured S' ∧
      maxLoad g S' ≤ ENNReal.ofReal (2 * Real.exp 1 / (Real.exp 1 - 1)) * maxLoad g S := by
  classical
  by_cases htop : maxLoad g S = ⊤
  · exact MalleableSched3d.theorem_1_of_top g S hS htop
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨S, hS, fun i j => Fin.elim0 j, ?_⟩
    have h0 : maxLoad g S = 0 :=
      le_antisymm (MalleableSched3d.maxLoad_le_of g S 0 (fun i => by simp)) zero_le
    rw [h0]; exact zero_le
  have hprocM : ∀ j, procTime g j (S j) ≤ maxLoad g S := fun j =>
    MalleableSched3d.procTime_le_maxLoad g S j (hS j).choose (hS j).choose_spec
  have hgpos : ∀ j, 0 < g j (S j) := by
    intro j
    have h1 : procTime g j (S j) ≠ ⊤ := ne_top_of_le_ne_top htop (hprocM j)
    unfold procTime at h1
    rw [ENNReal.inv_ne_top] at h1
    exact ENNReal.ofReal_pos.1 (pos_iff_ne_zero.2 h1)
  obtain ⟨C, hCdef⟩ : ∃ C, C = (maxLoad g S).toReal := ⟨_, rfl⟩
  have hMC : maxLoad g S = ENNReal.ofReal C := by rw [hCdef, ENNReal.ofReal_toReal htop]
  have hC : 0 < C := by
    rw [hCdef]
    apply ENNReal.toReal_pos _ htop
    have hp : 0 < procTime g ⟨0, hn⟩ (S ⟨0, hn⟩) := by
      unfold procTime; exact ENNReal.inv_pos.2 ENNReal.ofReal_ne_top
    exact (lt_of_lt_of_le hp (hprocM _)).ne'
  have hpt : ∀ j, procTime g j (S j) = ENNReal.ofReal (1 / g j (S j)) := by
    intro j; unfold procTime; rw [one_div, ENNReal.ofReal_inv_of_pos (hgpos j)]
  have hload : ∀ i : Fin m,
      ∑ j ∈ Finset.univ.filter (fun j => i ∈ S j), 1 / g j (S j) ≤ C := by
    intro i
    have h1 : ∑ j ∈ Finset.univ.filter (fun j => i ∈ S j), procTime g j (S j) ≤ maxLoad g S := by
      unfold maxLoad
      exact le_iSup (fun i' => ∑ j ∈ Finset.univ.filter (fun j => i' ∈ S j),
        procTime g j (S j)) i
    simp_rw [hpt] at h1
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => (one_div_pos.2 (hgpos j)).le), hMC,
      ENNReal.ofReal_le_ofReal_iff hC.le] at h1
    exact h1
  have hstep := fun δ hδ hδ1 =>
    MalleableSched3d.delta_step g hFS S hS C hC hgpos hload δ hδ hδ1
  have hα0 : 0 < 2 * Real.exp 1 / (Real.exp 1 - 1) := MalleableSched3d.const_pos
  obtain ⟨T0, hT0a, hT0w, _⟩ := hstep (1 / 2) (by norm_num) (by norm_num)
  let A := (Finset.univ : Finset (Fin n → Finset (Fin m))).filter
    (fun T => IsAssignment T ∧ WellStructured T)
  have hAne : A.Nonempty := ⟨T0, Finset.mem_filter.2 ⟨Finset.mem_univ _, hT0a, hT0w⟩⟩
  obtain ⟨T, hTA, hTmin⟩ := A.exists_min_image (maxLoad g) hAne
  obtain ⟨-, hTa, hTw⟩ := Finset.mem_filter.1 hTA
  have hbound : ∀ δ : ℝ, 0 < δ → δ < 1 → maxLoad g T ≤
      ENNReal.ofReal (2 * Real.exp 1 / (Real.exp 1 - 1) * (C / (1 - δ))) := by
    intro δ hδ hδ1
    obtain ⟨T', ha, hw, hle⟩ := hstep δ hδ hδ1
    exact le_trans (hTmin T' (Finset.mem_filter.2 ⟨Finset.mem_univ _, ha, hw⟩)) hle
  refine ⟨T, hTa, hTw, ?_⟩
  have hfin : maxLoad g T ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbound (1 / 2) (by norm_num) (by norm_num))
  obtain ⟨v, hvdef⟩ : ∃ v, v = (maxLoad g T).toReal := ⟨_, rfl⟩
  have hv : maxLoad g T = ENNReal.ofReal v := by rw [hvdef, ENNReal.ofReal_toReal hfin]
  have hvle : v ≤ 2 * Real.exp 1 / (Real.exp 1 - 1) * C := by
    by_contra hlt
    push Not at hlt
    have hαC : 0 < 2 * Real.exp 1 / (Real.exp 1 - 1) * C := mul_pos hα0 hC
    have hvpos : 0 < v := by linarith
    obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ,
        δ = (v - 2 * Real.exp 1 / (Real.exp 1 - 1) * C) / (2 * v) := ⟨_, rfl⟩
    have hδ : 0 < δ := by rw [hδdef]; exact div_pos (by linarith) (by linarith)
    have hδ1 : δ < 1 := by rw [hδdef, div_lt_one (by linarith)]; linarith
    have h1δ : 0 < 1 - δ := by linarith
    have hb := hbound δ hδ hδ1
    rw [hv, ENNReal.ofReal_le_ofReal_iff (mul_nonneg hα0.le (div_nonneg hC.le h1δ.le)),
      ← mul_div_assoc, le_div_iff₀ h1δ] at hb
    have hvδ : v * δ = (v - 2 * Real.exp 1 / (Real.exp 1 - 1) * C) / 2 := by
      rw [hδdef]; field_simp
    have : v * (1 - δ) = v - v * δ := by ring
    linarith
  rw [hv, hMC, ← ENNReal.ofReal_mul hα0.le]
  exact ENNReal.ofReal_le_ofReal hvle
