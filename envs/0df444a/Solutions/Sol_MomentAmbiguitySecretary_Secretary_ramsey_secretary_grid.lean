-- Prove2me | solution 1 for MomentAmbiguitySecretary.Secretary.ramsey_secretary_grid
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:11:19.783202+00:00
-- url     : https://prove2.me/submissions/fa2a608f-0d6a-410d-820e-4de0634db7c8

import Mathlib
import Definitions.Def_MomentAmbiguitySecretary_Secretary_Values
import Theorems.Thm_AppliedComb_Ramsey_hypergraph_ramsey

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Equiv
open scoped BigOperators Topology NNReal ENNReal
namespace MomentAmbiguitySecretary.Secretary.Dev.Grid.PartA
open MomentAmbiguitySecretary.Secretary
/-!
Part (A) of the Blueprint `GridBP.lean`: the classical secretary bound for randomized
rank-based stopping masses over uniformly random injective sequences.

Route: group injective sequences by their image set `A`; on `B m A` (injective sequences with
values in `A`, `|A| = m`) prove by peeling off the last position that
* a candidate at `t` is independent of the relative order of the earlier prefix (prob. `1/(t+1)`),
* a candidate at `t` is the global maximum with probability `(t+1)/m`;
this yields the rank LP `(t+1) x_t + Σ_{s<t} x_s ≤ N`, whose value is bounded by
`classicalValue m` through a backward induction with the cutoff values.
-/
/-! ### The rank LP -/
lemma cutoff_rec (m : ℕ) (t : ℕ) (ht : t < m) :
    cutoffProbability m (t + 1) =
      1 / (m : ℝ) + (t : ℝ) / ((t : ℝ) + 1) * cutoffProbability m (t + 2) := by
  rcases Nat.eq_zero_or_pos t with rfl | htp
  · simp [cutoffProbability]
  have h1 : t + 1 ≠ 1 := by omega
  have h2 : t + 2 ≠ 1 := by omega
  have hsplit : Finset.Icc (t + 1) m = insert (t + 1) (Finset.Icc (t + 2) m) := by
    have := Finset.insert_Icc_succ_left_eq_Icc (a := t + 1) (b := m) (by omega)
    rw [Order.succ_eq_add_one] at this
    exact this.symm
  have hnot : t + 1 ∉ Finset.Icc (t + 2) m := by simp
  simp only [cutoffProbability, if_neg h1, if_neg h2, hsplit, Finset.sum_insert hnot]
  have htr : (0 : ℝ) < t := by exact_mod_cast htp
  have hm : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  push_cast
  have e1 : (t : ℝ) + 1 - 1 = t := by ring
  have e2 : (t : ℝ) + 2 - 1 = t + 1 := by ring
  rw [e1, e2]
  have ht0 : (t : ℝ) ≠ 0 := htr.ne'
  field_simp

lemma cutoff_top (m : ℕ) (hm : 1 ≤ m) : cutoffProbability m (m + 1) = 0 := by
  have h : m + 1 ≠ 1 := by omega
  simp [cutoffProbability]

lemma lp_bound (m : ℕ) (hm : 1 ≤ m) (N : ℝ) (x : ℕ → ℝ) (hx0 : ∀ t < m, 0 ≤ x t)
    (hx : ∀ t < m, ((t : ℝ) + 1) * x t + ∑ s ∈ Finset.range t, x s ≤ N) :
    ∑ t ∈ Finset.range m, ((t : ℝ) + 1) / m * x t ≤ N * classicalValue m := by
  set Y : ℕ → ℝ := cutoffProbability m with hYdef
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hex : ∃ r, ∀ t, r ≤ t → t < m → Y (t + 2) ≤ ((t : ℝ) + 1) / m := by
    refine ⟨m - 1, fun t h1 h2 => ?_⟩
    have : t = m - 1 := by omega
    subst this
    have : m - 1 + 2 = m + 1 := by omega
    rw [this, hYdef, cutoff_top m hm]
    positivity
  classical
  set r := Nat.find hex with hrdef
  have hr : ∀ t, r ≤ t → t < m → Y (t + 2) ≤ ((t : ℝ) + 1) / m := Nat.find_spec hex
  have hrm : r ≤ m - 1 := Nat.find_min' hex (fun t h1 h2 => by
    have : t = m - 1 := by omega
    subst this
    have : m - 1 + 2 = m + 1 := by omega
    rw [this, hYdef, cutoff_top m hm]
    positivity)
  have hmin : 1 ≤ r → (r : ℝ) / m < Y (r + 1) := by
    intro hr1
    have := Nat.find_min hex (show r - 1 < r by omega)
    push Not at this
    obtain ⟨t, ht1, ht2, ht3⟩ := this
    by_cases htr : r ≤ t
    · exact absurd (hr t htr ht2) (not_le.2 ht3)
    · have : t = r - 1 := by omega
      subst this
      have e : r - 1 + 2 = r + 1 := by omega
      have e2 : ((r - 1 : ℕ) : ℝ) + 1 = r := by
        rw [Nat.cast_sub hr1]; push_cast; ring
      rw [e, e2] at ht3
      exact ht3
  let W : ℕ → ℝ := fun t => if t < r then Y (r + 1) else Y (t + 1)
  let R : ℕ → ℝ := fun t => N - ∑ s ∈ Finset.range t, x s
  have claim : ∀ j t, t + j = m →
      ∑ s ∈ Finset.Ico t m, ((s : ℝ) + 1) / m * x s ≤ W t * R t := by
    intro j
    induction j with
    | zero =>
      intro t ht
      simp only [add_zero] at ht
      subst ht
      have hW : W t = 0 := by
        simp only [W, if_neg (show ¬ t < r by omega), hYdef]
        exact cutoff_top t hm
      simp [hW]
    | succ j ih =>
      intro t ht
      have htm : t < m := by omega
      have ih' := ih (t + 1) (by omega)
      rw [Finset.sum_eq_sum_Ico_succ_bot htm]
      have hR : R (t + 1) = R t - x t := by
        simp only [R, Finset.sum_range_succ]; ring
      rw [hR] at ih'
      have hc : ((t : ℝ) + 1) * x t ≤ R t := by
        have := hx t htm; simp only [R]; linarith
      have hxt := hx0 t htm
      by_cases htr : t < r
      · have hW1 : W (t + 1) = Y (r + 1) := by
          by_cases h' : t + 1 < r
          · simp [W, h']
          · simp only [W, if_neg h']
            have : t + 1 = r := by omega
            rw [this]
        have hW0 : W t = Y (r + 1) := by simp [W, htr]
        rw [hW1] at ih'
        rw [hW0]
        have hY := hmin (by omega)
        have htr' : ((t : ℝ) + 1) ≤ r := by exact_mod_cast htr
        have : ((t : ℝ) + 1) / m ≤ r / m := div_le_div_of_nonneg_right htr' hmpos.le
        nlinarith [mul_nonneg hxt (sub_nonneg.2 (this.trans hY.le))]
      · have hW1 : W (t + 1) = Y (t + 2) := by
          simp [W, show ¬ t + 1 < r by omega]
        have hW0 : W t = Y (t + 1) := by simp [W, htr]
        rw [hW1] at ih'
        rw [hW0]
        have hY := hr t (by omega) htm
        have key : Y (t + 1) * R t - (((t : ℝ) + 1) / m * x t + Y (t + 2) * (R t - x t)) =
            (R t - ((t : ℝ) + 1) * x t) * (1 / m - Y (t + 2) / ((t : ℝ) + 1)) := by
          rw [hYdef, cutoff_rec m t htm]
          field_simp
          ring
        have hnn : 0 ≤ (R t - ((t : ℝ) + 1) * x t) * (1 / m - Y (t + 2) / ((t : ℝ) + 1)) := by
          apply mul_nonneg (by linarith)
          rw [sub_nonneg, div_le_div_iff₀ (by positivity) hmpos]
          rw [le_div_iff₀ hmpos] at hY
          linarith
        linarith
  have h0 := claim m 0 (by simp)
  have hW0 : W 0 = Y (r + 1) := by
    by_cases h : 0 < r
    · simp [W, h]
    · have : r = 0 := by omega
      simp [W, this]
  rw [hW0, ← Finset.range_eq_Ico] at h0
  have hN : 0 ≤ N := by
    have := hx 0 (by omega); have := hx0 0 (by omega); simp at *; linarith
  have hYc : Y (r + 1) ≤ classicalValue m := by
    simp only [classicalValue, dif_pos hm, hYdef]
    exact Finset.le_sup' (cutoffProbability m) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  calc _ ≤ Y (r + 1) * R 0 := h0
    _ = Y (r + 1) * N := by simp [R]
    _ ≤ classicalValue m * N := mul_le_mul_of_nonneg_right hYc hN
    _ = N * classicalValue m := mul_comm _ _

end MomentAmbiguitySecretary.Secretary.Dev.Grid.PartA
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Equiv
open scoped BigOperators Topology NNReal ENNReal
namespace MomentAmbiguitySecretary.Secretary.Dev.Grid.PartA
open MomentAmbiguitySecretary.Secretary
variable {k : ℕ}
/-! ### Injective sequences with a given value set -/
/-- Injective sequences of length `n` with all values in `A`. -/
def B (n : ℕ) (A : Finset (Fin k)) : Finset (Fin n → Fin k) :=
  Finset.univ.filter (fun z => Function.Injective z ∧ ∀ i, z i ∈ A)

lemma mem_B {n : ℕ} {A : Finset (Fin k)} {z : Fin n → Fin k} :
    z ∈ B n A ↔ Function.Injective z ∧ ∀ i, z i ∈ A := by
  simp [B]

/-- `f` depends only on the relative order of the positions `< p`. -/
def DepOn {n : ℕ} (p : ℕ) (f : (Fin n → Fin k) → ℝ) : Prop :=
  ∀ z z' : Fin n → Fin k, (∀ i j : Fin n, (i : ℕ) < p → (j : ℕ) < p →
    (z i < z j ↔ z' i < z' j)) → f z = f z'

lemma DepOn.mono {n p q : ℕ} {f : (Fin n → Fin k) → ℝ} (h : DepOn p f) (hpq : p ≤ q) :
    DepOn q f :=
  fun z z' hz => h z z' fun i j hi hj => hz i j (by omega) (by omega)

lemma DepOn.mul {n p : ℕ} {f g : (Fin n → Fin k) → ℝ} (hf : DepOn p f) (hg : DepOn p g) :
    DepOn p (fun z => f z * g z) :=
  fun z z' hz => by show f z * g z = f z' * g z'; rw [hf z z' hz, hg z z' hz]

/-- Position `t` beats all positions `≤ t` (a candidate). -/
def candI {n : ℕ} (t : ℕ) (z : Fin n → Fin k) : ℝ :=
  if ∀ i j : Fin n, (i : ℕ) ≤ t → (j : ℕ) = t → z i ≤ z j then 1 else 0

/-- Position `t` beats all positions (the best). -/
def bestI {n : ℕ} (t : ℕ) (z : Fin n → Fin k) : ℝ :=
  if ∀ i j : Fin n, (j : ℕ) = t → z i ≤ z j then 1 else 0

lemma candI_nonneg {n : ℕ} (t : ℕ) (z : Fin n → Fin k) : 0 ≤ candI t z := by
  unfold candI; split_ifs <;> norm_num

lemma candI_le_one {n : ℕ} (t : ℕ) (z : Fin n → Fin k) : candI t z ≤ 1 := by
  unfold candI; split_ifs <;> norm_num

lemma candI_depOn {n : ℕ} (t : ℕ) : DepOn (k := k) (n := n) (t + 1) (candI t) := by
  intro z z' h
  have key : ∀ i j : Fin n, (i : ℕ) ≤ t → (j : ℕ) ≤ t → (z i ≤ z j ↔ z' i ≤ z' j) :=
    fun i j hi hj => by rw [← not_lt, ← not_lt, h j i (by omega) (by omega)]
  unfold candI
  exact if_congr ⟨fun H i j hi hj => (key i j hi (by omega)).1 (H i j hi hj),
    fun H i j hi hj => (key i j hi (by omega)).2 (H i j hi hj)⟩ rfl rfl

lemma snoc_apply_lt {n : ℕ} (w : Fin n → Fin k) (v : Fin k) (i : Fin (n + 1))
    (hi : (i : ℕ) < n) : (Fin.snoc (α := fun _ => Fin k) w v i : Fin k) = w ⟨i, hi⟩ := by
  obtain ⟨i, hi'⟩ := i
  exact Fin.snoc_castSucc (α := fun _ => Fin k) (i := ⟨i, hi⟩) _ _

lemma DepOn.snoc {n p : ℕ} {f : (Fin (n + 1) → Fin k) → ℝ} (h : DepOn p f) (hp : p ≤ n)
    (v : Fin k) : DepOn p (fun w : Fin n → Fin k => f (Fin.snoc w v)) := by
  intro w w' hw
  apply h
  intro i j hi hj
  rw [snoc_apply_lt _ _ i (by omega), snoc_apply_lt _ _ j (by omega),
    snoc_apply_lt _ _ i (by omega), snoc_apply_lt _ _ j (by omega)]
  exact hw _ _ hi hj

lemma DepOn.snoc_eq {n p : ℕ} {f : (Fin (n + 1) → Fin k) → ℝ} (h : DepOn p f) (hp : p ≤ n)
    (w : Fin n → Fin k) (v v' : Fin k) : f (Fin.snoc w v) = f (Fin.snoc w v') := by
  apply h
  intro i j hi hj
  rw [snoc_apply_lt _ _ i (by omega), snoc_apply_lt _ _ j (by omega),
    snoc_apply_lt _ _ i (by omega), snoc_apply_lt _ _ j (by omega)]

lemma snoc_mem_B {n : ℕ} {A : Finset (Fin k)} {v : Fin k} (hv : v ∈ A) {w : Fin n → Fin k}
    (hw : w ∈ B n (A.erase v)) : (Fin.snoc w v : Fin (n + 1) → Fin k) ∈ B (n + 1) A := by
  rw [mem_B] at hw ⊢
  refine ⟨Fin.snoc_injective_of_injective hw.1 ?_, fun i => ?_⟩
  · rintro ⟨i, hi⟩
    exact (Finset.mem_erase.1 (hw.2 i)).1 hi
  · induction i using Fin.lastCases with
    | last => simpa using hv
    | cast i => simpa using (Finset.mem_erase.1 (hw.2 i)).2

lemma sum_B_succ {n : ℕ} (A : Finset (Fin k)) (F : (Fin (n + 1) → Fin k) → ℝ) :
    ∑ z ∈ B (n + 1) A, F z = ∑ v ∈ A, ∑ w ∈ B n (A.erase v), F (Fin.snoc w v) := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun z => z (Fin.last n)) (t := A)
    (fun z hz => (mem_B.1 hz).2 _)]
  refine Finset.sum_congr rfl fun v hv => ?_
  refine Finset.sum_nbij' Fin.init (fun w => Fin.snoc w v) ?_ ?_ ?_ ?_ ?_
  · intro z hz
    simp only [Finset.mem_filter] at hz
    obtain ⟨hzB, hl⟩ := hz
    obtain ⟨hinj, hA⟩ := mem_B.1 hzB
    refine mem_B.2 ⟨hinj.comp (Fin.castSucc_injective _), fun i => Finset.mem_erase.2 ⟨?_, hA _⟩⟩
    intro he
    rw [← hl] at he
    exact Fin.castSucc_ne_last i (hinj he)
  · intro w hw
    simp only [Finset.mem_filter]
    exact ⟨snoc_mem_B hv hw, Fin.snoc_last (α := fun _ => Fin k) _ _⟩
  · intro z hz
    simp only [Finset.mem_filter] at hz
    rw [← hz.2]
    exact Fin.snoc_init_self z
  · intro w _
    exact Fin.init_snoc (α := fun _ => Fin k) _ _
  · intro z hz
    simp only [Finset.mem_filter] at hz
    rw [← hz.2, Fin.snoc_init_self]

lemma B_surj {n : ℕ} {A : Finset (Fin k)} (hA : A.card = n) {w : Fin n → Fin k}
    (hw : w ∈ B n A) {a : Fin k} (ha : a ∈ A) : ∃ i, w i = a := by
  have hw' := mem_B.1 hw
  have himg : Finset.univ.image w = A := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hx
      exact hw'.2 i
    · rw [Finset.card_image_of_injective _ hw'.1, hA, Finset.card_univ, Fintype.card_fin]
  rw [← himg] at ha
  simpa using ha

/-- Sums of relative-order functions over `B n A` do not depend on `A`. -/
lemma sum_B_congr {n : ℕ} {A A' : Finset (Fin k)} (hA : A.card = n) (hA' : A'.card = n)
    {f : (Fin n → Fin k) → ℝ} (hf : DepOn n f) :
    ∑ z ∈ B n A, f z = ∑ z ∈ B n A', f z := by
  set e := A.orderIsoOfFin hA
  set e' := A'.orderIsoOfFin hA'
  refine Finset.sum_bij' (fun z hz j => (e' (e.symm ⟨z j, (mem_B.1 hz).2 j⟩)).1)
    (fun z hz j => (e (e'.symm ⟨z j, (mem_B.1 hz).2 j⟩)).1) ?_ ?_ ?_ ?_ ?_
  · intro z hz
    refine mem_B.2 ⟨fun a b hab => ?_, fun j => (e' _).2⟩
    have h2 := e.symm.injective (e'.injective (Subtype.ext hab))
    exact (mem_B.1 hz).1 (by simpa using h2)
  · intro z hz
    refine mem_B.2 ⟨fun a b hab => ?_, fun j => (e _).2⟩
    have h2 := e'.symm.injective (e.injective (Subtype.ext hab))
    exact (mem_B.1 hz).1 (by simpa using h2)
  · intro z hz
    funext j
    simp
  · intro z hz
    funext j
    simp
  · intro z hz
    apply hf
    intro a b _ _
    simp

lemma card_erase_B {n : ℕ} {A : Finset (Fin k)} (hA : A.card = n + 1) {v : Fin k} (hv : v ∈ A) :
    (A.erase v).card = n := by
  rw [Finset.card_erase_of_mem hv, hA]; rfl

lemma candI_snoc {n t : ℕ} (ht : t < n) (w : Fin n → Fin k) (v : Fin k) :
    candI t (Fin.snoc w v : Fin (n + 1) → Fin k) = candI t w := by
  unfold candI
  refine if_congr ⟨fun H i j hi hj => ?_, fun H i j hi hj => ?_⟩ rfl rfl
  · have := H (Fin.castSucc i) (Fin.castSucc j) hi hj
    simpa only [Fin.snoc_castSucc] using this
  · rw [snoc_apply_lt _ _ i (by omega), snoc_apply_lt _ _ j (by omega)]
    exact H _ _ hi hj

lemma bestI_snoc {n t : ℕ} (ht : t < n) {A : Finset (Fin k)} (hA : A.card = n + 1)
    (hne : A.Nonempty) {v : Fin k} (hv : v ∈ A) {w : Fin n → Fin k}
    (hw : w ∈ B n (A.erase v)) :
    bestI t (Fin.snoc w v : Fin (n + 1) → Fin k) =
      (if v = A.max' hne then 0 else 1) * bestI t w := by
  set tt : Fin n := ⟨t, ht⟩
  have hcond : (∀ i j : Fin (n + 1), (j : ℕ) = t →
      (Fin.snoc w v : Fin (n + 1) → Fin k) i ≤ (Fin.snoc w v : Fin (n + 1) → Fin k) j) ↔
      (∀ i j : Fin n, (j : ℕ) = t → w i ≤ w j) ∧ v ≤ w tt := by
    constructor
    · intro H
      refine ⟨fun i j hj => ?_, ?_⟩
      · have := H (Fin.castSucc i) (Fin.castSucc j) hj
        simpa only [Fin.snoc_castSucc] using this
      · have := H (Fin.last n) (Fin.castSucc tt) rfl
        simpa only [Fin.snoc_castSucc, Fin.snoc_last] using this
    · rintro ⟨H, hvt⟩ i j hj
      have hj' : j = Fin.castSucc tt := Fin.ext hj
      subst hj'
      rw [Fin.snoc_castSucc]
      induction i using Fin.lastCases with
      | last => rw [Fin.snoc_last]; exact hvt
      | cast i => rw [Fin.snoc_castSucc]; exact H i tt rfl
  have hwB := mem_B.1 hw
  unfold bestI
  rw [if_congr hcond rfl rfl]
  by_cases hb : ∀ i j : Fin n, (j : ℕ) = t → w i ≤ w j
  · rw [if_pos hb, mul_one]
    have hwt := Finset.mem_erase.1 (hwB.2 tt)
    by_cases hvM : v = A.max' hne
    · rw [if_pos hvM, if_neg]
      rintro ⟨_, hvt⟩
      have h1 : w tt ≤ A.max' hne := A.le_max' _ hwt.2
      rw [← hvM] at h1
      exact hwt.1 (le_antisymm h1 hvt)
    · rw [if_neg hvM, if_pos]
      refine ⟨hb, ?_⟩
      have hM : A.max' hne ∈ A.erase v := Finset.mem_erase.2 ⟨Ne.symm hvM, A.max'_mem hne⟩
      obtain ⟨i, hi⟩ := B_surj (card_erase_B hA hv) hw hM
      calc v ≤ A.max' hne := A.le_max' _ hv
        _ = w i := hi.symm
        _ ≤ w tt := hb i tt rfl
  · rw [if_neg hb, mul_zero, if_neg (fun h => hb h.1)]

lemma candI_snoc_last {t : ℕ} {A : Finset (Fin k)} (hA : A.card = t + 1) (hne : A.Nonempty)
    {v : Fin k} (hv : v ∈ A) {w : Fin t → Fin k} (hw : w ∈ B t (A.erase v)) :
    candI t (Fin.snoc w v : Fin (t + 1) → Fin k) = if v = A.max' hne then 1 else 0 := by
  unfold candI
  refine if_congr ⟨fun H => ?_, fun hvM i j _ hj => ?_⟩ rfl rfl
  · by_contra hvM
    have hM : A.max' hne ∈ A.erase v := Finset.mem_erase.2 ⟨Ne.symm hvM, A.max'_mem hne⟩
    obtain ⟨i, hi⟩ := B_surj (card_erase_B hA hv) hw hM
    have h1 := H (Fin.castSucc i) (Fin.last t) (by rw [Fin.val_castSucc]; exact i.isLt.le)
      (Fin.val_last t)
    rw [Fin.snoc_castSucc, Fin.snoc_last, hi] at h1
    exact hvM (le_antisymm (A.le_max' _ hv) h1)
  · have hj' : j = Fin.last t := Fin.ext hj
    subst hj'
    rw [Fin.snoc_last]
    exact (A.le_max' _ ((mem_B.1 (snoc_mem_B hv hw)).2 i)).trans_eq hvM.symm

lemma bestI_eq_candI_top {t : ℕ} (z : Fin (t + 1) → Fin k) : bestI t z = candI t z := by
  unfold bestI candI
  exact if_congr ⟨fun H i j _ hj => H i j hj,
    fun H i j hj => H i j (Nat.lt_succ_iff.1 i.isLt) hj⟩ rfl rfl

/-- A candidate at `t` is independent of the relative order of the earlier positions. -/
lemma F1 (t : ℕ) : ∀ n, t + 1 ≤ n → ∀ A : Finset (Fin k), A.card = n →
    ∀ h : (Fin n → Fin k) → ℝ, DepOn t h →
      ((t : ℝ) + 1) * ∑ z ∈ B n A, h z * candI t z = ∑ z ∈ B n A, h z := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    intro A hA h hh
    have hne : A.Nonempty := Finset.card_pos.1 (by omega)
    set M := A.max' hne with hMdef
    have hM : M ∈ A := A.max'_mem hne
    rw [sum_B_succ, sum_B_succ]
    have e1 : ∀ v ∈ A, ∑ w ∈ B t (A.erase v),
        h (Fin.snoc w v) * candI t (Fin.snoc w v : Fin (t + 1) → Fin k) =
        if v = M then ∑ w ∈ B t (A.erase M), h (Fin.snoc w M) else 0 := by
      intro v hv
      have : ∀ w ∈ B t (A.erase v), h (Fin.snoc w v) *
          candI t (Fin.snoc w v : Fin (t + 1) → Fin k) =
          if v = M then h (Fin.snoc w v) else 0 := fun w hw => by
        rw [candI_snoc_last hA hne hv hw]
        split_ifs <;> simp
      rw [Finset.sum_congr rfl this]
      split_ifs with hvM
      · rw [hvM]
      · simp
    rw [Finset.sum_congr rfl e1, Finset.sum_ite_eq' A M, if_pos hM]
    have e2 : ∀ v ∈ A, ∑ w ∈ B t (A.erase v), h (Fin.snoc w v) =
        ∑ w ∈ B t (A.erase M), h (Fin.snoc w M) := by
      intro v hv
      rw [Finset.sum_congr rfl (fun w _ => hh.snoc_eq le_rfl w v M)]
      exact sum_B_congr (card_erase_B hA hv) (card_erase_B hA hM) (hh.snoc le_rfl M)
    rw [Finset.sum_congr rfl e2, Finset.sum_const, hA, nsmul_eq_mul]
    push_cast
    ring
  | succ n hn ih =>
    intro A hA h hh
    rw [sum_B_succ, sum_B_succ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [← ih (A.erase v) (card_erase_B hA hv) _ (hh.snoc (by omega) v)]
    congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [candI_snoc (by omega)]

/-- A candidate at `t` is the overall best with probability `(t+1)/n`. -/
lemma F2 (t : ℕ) : ∀ n, t + 1 ≤ n → ∀ A : Finset (Fin k), A.card = n →
    ∀ f : (Fin n → Fin k) → ℝ, DepOn (t + 1) f →
      (n : ℝ) * ∑ z ∈ B n A, f z * bestI t z =
        ((t : ℝ) + 1) * ∑ z ∈ B n A, f z * candI t z := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    intro A hA f hf
    push_cast
    congr 1
    exact Finset.sum_congr rfl fun z _ => by rw [bestI_eq_candI_top]
  | succ n hn ih =>
    intro A hA f hf
    have hne : A.Nonempty := Finset.card_pos.1 (by omega)
    set M := A.max' hne with hMdef
    have hM : M ∈ A := A.max'_mem hne
    set C := ∑ w ∈ B n (A.erase M), f (Fin.snoc w M) * candI t w with hCdef
    have hC : ∀ v ∈ A, ∑ w ∈ B n (A.erase v), f (Fin.snoc w v) * candI t w = C := by
      intro v hv
      rw [Finset.sum_congr rfl (fun w _ => by rw [hf.snoc_eq (by omega) w v M])]
      exact sum_B_congr (card_erase_B hA hv) (card_erase_B hA hM)
        (((hf.snoc (by omega) M).mul (candI_depOn t)).mono (by omega))
    have hD : ∀ v ∈ A, (n : ℝ) * ∑ w ∈ B n (A.erase v), f (Fin.snoc w v) * bestI t w =
        ((t : ℝ) + 1) * C := by
      intro v hv
      rw [ih (A.erase v) (card_erase_B hA hv) _ (hf.snoc (by omega) v), hC v hv]
    have hR : ∑ z ∈ B (n + 1) A, f z * candI t z = ((n : ℝ) + 1) * C := by
      rw [sum_B_succ]
      rw [Finset.sum_congr rfl (fun v hv => by
        rw [Finset.sum_congr rfl (fun w _ => by rw [candI_snoc (by omega)]), hC v hv])]
      rw [Finset.sum_const, hA, nsmul_eq_mul]
      push_cast
      ring
    have hL : (n : ℝ) * ∑ z ∈ B (n + 1) A, f z * bestI t z = (n : ℝ) * (((t : ℝ) + 1) * C) := by
      rw [sum_B_succ]
      have e : ∀ v ∈ A, ∑ w ∈ B n (A.erase v),
          f (Fin.snoc w v) * bestI t (Fin.snoc w v : Fin (n + 1) → Fin k) =
          if v = M then 0 else ∑ w ∈ B n (A.erase v), f (Fin.snoc w v) * bestI t w := by
        intro v hv
        rw [Finset.sum_congr rfl (fun w hw => by rw [bestI_snoc (by omega) hA hne hv hw])]
        split_ifs <;> simp
      rw [Finset.sum_congr rfl e, Finset.mul_sum, ← Finset.add_sum_erase A (fun v => (n : ℝ) *
        (if v = M then 0 else ∑ w ∈ B n (A.erase v), f (Fin.snoc w v) * bestI t w)) hM]
      simp only [↓reduceIte, mul_zero, zero_add]
      rw [Finset.sum_congr rfl (fun v hv => by
        rw [if_neg (Finset.ne_of_mem_erase hv), hD v (Finset.mem_of_mem_erase hv)])]
      rw [Finset.sum_const, card_erase_B hA hM, nsmul_eq_mul]
    have hn0 : (n : ℝ) ≠ 0 := by
      have : 0 < n := by omega
      positivity
    have hL' : ∑ z ∈ B (n + 1) A, f z * bestI t z = ((t : ℝ) + 1) * C :=
      mul_left_cancel₀ hn0 hL
    rw [hL', hR]
    push_cast
    ring

end MomentAmbiguitySecretary.Secretary.Dev.Grid.PartA
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Equiv
open scoped BigOperators Topology NNReal ENNReal
namespace MomentAmbiguitySecretary.Secretary.Dev.Grid.PartA
open MomentAmbiguitySecretary.Secretary
/-! ### The bound on one image set, and the assembly -/
lemma main_A {k : ℕ} (m : ℕ) (hm : 1 ≤ m) (A : Finset (Fin k)) (hA : A.card = m)
    (G : Fin m → (Fin m → Fin k) → ℝ)
    (hG0 : ∀ t z, 0 ≤ G t z)
    (hG1 : ∀ z, Function.Injective z → ∑ t, G t z ≤ 1)
    (hGc : ∀ t z z', (∀ i j : Fin m, i ≤ t → j ≤ t → (z i < z j ↔ z' i < z' j)) →
      G t z = G t z') :
    ∑ z ∈ B m A, ∑ t, G t z * (if ∀ i, z i ≤ z t then (1 : ℝ) else 0)
      ≤ ((B m A).card : ℝ) * classicalValue m := by
  set N : ℝ := ((B m A).card : ℝ) with hN
  let gs : ℕ → (Fin m → Fin k) → ℝ := fun s z => if hs : s < m then G ⟨s, hs⟩ z else 0
  have hgs : ∀ (t : Fin m) z, gs t z = G t z := fun t z => by simp [gs, t.isLt]
  have hgs0 : ∀ s z, 0 ≤ gs s z := fun s z => by
    simp only [gs]; split_ifs
    · exact hG0 _ _
    · exact le_rfl
  have hgsDep : ∀ s, DepOn (s + 1) (gs s) := by
    intro s z z' h
    simp only [gs]
    split_ifs with hs
    · exact hGc _ z z' fun i j hi hj =>
        h i j (by have := Fin.le_iff_val_le_val.1 hi; simp at this; omega)
          (by have := Fin.le_iff_val_le_val.1 hj; simp at this; omega)
    · rfl
  let x : ℕ → ℝ := fun s => ∑ z ∈ B m A, gs s z * candI s z
  have hmR : (m : ℝ) ≠ 0 := by
    have : 0 < m := by omega
    positivity
  have step1 : ∑ z ∈ B m A, ∑ t, G t z * (if ∀ i, z i ≤ z t then (1 : ℝ) else 0) =
      ∑ s ∈ Finset.range m, ((s : ℝ) + 1) / m * x s := by
    rw [Finset.sum_comm, ← Fin.sum_univ_eq_sum_range (fun s => ((s : ℝ) + 1) / m * x s) m]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hF2 := F2 t.val m (by omega) A hA (gs t) (hgsDep t)
    have hb : ∀ z : Fin m → Fin k, (if ∀ i, z i ≤ z t then (1 : ℝ) else 0) = bestI t.val z :=
      fun z => by
        unfold bestI
        exact if_congr ⟨fun H i j hj => (Fin.ext hj : j = t) ▸ H i, fun H i => H i t rfl⟩
          rfl rfl
    rw [Finset.sum_congr rfl (fun z _ => by rw [hb z, ← hgs t z])]
    simp only [x]
    rw [div_mul_eq_mul_div, eq_div_iff hmR, mul_comm, hF2]
  rw [step1]
  apply lp_bound m hm N x
  · intro t _
    exact Finset.sum_nonneg fun z _ => mul_nonneg (hgs0 _ _) (candI_nonneg _ _)
  · intro t ht
    let h : (Fin m → Fin k) → ℝ := fun z => 1 - ∑ s ∈ Finset.range t, gs s z
    have hdep : DepOn t h := by
      intro z z' hz
      simp only [h]
      congr 1
      refine Finset.sum_congr rfl fun s hs => hgsDep s z z' fun i j hi hj => hz i j
        (by have := Finset.mem_range.1 hs; omega) (by have := Finset.mem_range.1 hs; omega)
    have hF1 := F1 t m (by omega) A hA h hdep
    have hpath : ∀ z ∈ B m A, gs t z ≤ h z := by
      intro z hz
      have h1 := hG1 z (mem_B.1 hz).1
      have h3 : ∑ s ∈ Finset.range m, gs s z = ∑ t : Fin m, G t z := by
        rw [← Fin.sum_univ_eq_sum_range]
        exact Finset.sum_congr rfl fun t _ => hgs t z
      have h2 : ∑ s ∈ Finset.range (t + 1), gs s z ≤ ∑ s ∈ Finset.range m, gs s z :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
          (fun _ _ _ => hgs0 _ _)
      rw [Finset.sum_range_succ] at h2
      simp only [h]
      linarith
    have hx_le : x t ≤ ∑ z ∈ B m A, h z * candI t z :=
      Finset.sum_le_sum fun z hz => mul_le_mul_of_nonneg_right (hpath z hz) (candI_nonneg _ _)
    have hsumh : ∑ z ∈ B m A, h z = N - ∑ s ∈ Finset.range t, ∑ z ∈ B m A, gs s z := by
      simp only [h, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, hN]
      rw [Finset.sum_comm]
    have hxa : ∑ s ∈ Finset.range t, x s ≤ ∑ s ∈ Finset.range t, ∑ z ∈ B m A, gs s z :=
      Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun z _ => by
        have := candI_le_one s z
        have := hgs0 s z
        nlinarith
    have ht1 : (0 : ℝ) ≤ (t : ℝ) + 1 := by positivity
    have := mul_le_mul_of_nonneg_left hx_le ht1
    rw [hF1, hsumh] at this
    linarith

/-- (A) The classical secretary bound for randomized rank-based stopping masses, over uniformly
random injective sequences in `Fin k`. `G t z` is the probability of stopping at time `t`; it
depends only on the relative order of `z 0, …, z t`, and the stopping masses along any injective
sequence sum to at most one. -/
theorem secretary_mass_bound (m k : ℕ) (hm : 1 ≤ m) (hmk : m ≤ k)
    (G : Fin m → (Fin m → Fin k) → ℝ)
    (hG0 : ∀ t z, 0 ≤ G t z)
    (hG1 : ∀ z, Function.Injective z → ∑ t, G t z ≤ 1)
    (hGc : ∀ t z z', (∀ i j : Fin m, i ≤ t → j ≤ t → (z i < z j ↔ z' i < z' j)) →
      G t z = G t z') :
    ∑ z ∈ Finset.univ.filter (fun z : Fin m → Fin k => Function.Injective z),
        ∑ t, G t z * (if ∀ i, z i ≤ z t then (1 : ℝ) else 0)
      ≤ ((Finset.univ.filter (fun z : Fin m → Fin k => Function.Injective z)).card : ℝ) *
          classicalValue m := by
  set S := Finset.univ.filter (fun z : Fin m → Fin k => Function.Injective z) with hS
  have hmaps : ∀ z ∈ S, Finset.univ.image z ∈
      (Finset.univ : Finset (Fin k)).powersetCard m := by
    intro z hz
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.subset_univ _, ?_⟩
    rw [Finset.card_image_of_injective _ (Finset.mem_filter.1 hz).2]
    simp
  have hfib : ∀ A ∈ (Finset.univ : Finset (Fin k)).powersetCard m,
      S.filter (fun z => Finset.univ.image z = A) = B m A := by
    intro A hA
    rw [Finset.mem_powersetCard] at hA
    ext z
    simp only [Finset.mem_filter, mem_B, S, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hinj, rfl⟩
      exact ⟨hinj, fun i => Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
    · rintro ⟨hinj, hmem⟩
      refine ⟨hinj, Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_⟩
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hx
        exact hmem i
      · rw [hA.2, Finset.card_image_of_injective _ hinj]
        simp
  rw [← Finset.sum_fiberwise_of_maps_to hmaps,
    Finset.card_eq_sum_card_fiberwise (fun z hz => hmaps z hz)]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun A hA => ?_
  rw [hfib A hA]
  exact main_A m hm A (Finset.mem_powersetCard.1 hA).2 G hG0 hG1 hGc

end MomentAmbiguitySecretary.Secretary.Dev.Grid.PartA
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Equiv
open scoped BigOperators Topology NNReal ENNReal
namespace MomentAmbiguitySecretary.Secretary.Dev.Grid
open MomentAmbiguitySecretary.Secretary
/-!
Blueprint for Lemma 6.1 (`ramsey_secretary_grid`): the stubs (A)–(D) below are the interfaces;
the Parts prove them; `Grid.lean` assembles the lemma from them.
-/
alias secretary_mass_bound := MomentAmbiguitySecretary.Secretary.Dev.Grid.PartA.secretary_mass_bound

end MomentAmbiguitySecretary.Secretary.Dev.Grid
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Equiv
open scoped BigOperators Topology NNReal ENNReal
namespace MomentAmbiguitySecretary.Secretary.Dev.Grid.PartB
/-- (B) Finite Ramsey for `s`-subsets, in order-embedding form. -/
theorem ramsey_ordered (C : Type) [Fintype C] [Nonempty C] (s K : ℕ) (hs : 1 ≤ s)
    (hK : s ≤ K) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ χ : (Fin s ↪o Fin N) → C,
      ∃ E : Fin K ↪o Fin N, ∀ U U' : Fin s ↪o Fin K, χ (U.trans E) = χ (U'.trans E) := by
  classical
  set r := Fintype.card C
  let e : C ≃ Fin r := Fintype.equivFin C
  have hR := AppliedComb.Ramsey.hypergraph_ramsey r s Fintype.card_pos hs (fun _ => K)
    (fun _ => hK)
  refine ⟨AppliedComb.Ramsey.hypergraphRamseyNumber s r (fun _ => K), ?_⟩
  intro N hN χ
  obtain ⟨α, H, hH, hhom⟩ := hR.1.2 N hN
    (fun S => e (χ (S.1.orderEmbOfFin S.2)))
  let E : Fin K ↪o Fin N := H.orderEmbOfFin hH
  have key : ∀ U : Fin s ↪o Fin K, e (χ (U.trans E)) = α := by
    intro U
    let S : Finset (Fin N) := Finset.univ.map (U.trans E).toEmbedding
    have hS : S.card = s := by simp [S]
    have hSH : S ⊆ H := by
      intro x hx
      simp only [S, Finset.mem_map, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      exact Finset.orderEmbOfFin_mem H hH (U i)
    have hU : U.trans E = S.orderEmbOfFin hS :=
      Finset.orderEmbOfFin_unique' hS (fun x => by simp [S])
    have := hhom S hS hSH
    simp only at this
    rw [hU]; exact this
  refine ⟨E, fun U U' => ?_⟩
  apply e.injective
  rw [key U, key U']

end MomentAmbiguitySecretary.Secretary.Dev.Grid.PartB
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Equiv
open scoped BigOperators Topology NNReal ENNReal
namespace MomentAmbiguitySecretary.Secretary.Dev.Grid
open MomentAmbiguitySecretary.Secretary
alias ramsey_ordered := MomentAmbiguitySecretary.Secretary.Dev.Grid.PartB.ramsey_ordered

end MomentAmbiguitySecretary.Secretary.Dev.Grid
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Equiv
open scoped BigOperators Topology NNReal ENNReal
namespace MomentAmbiguitySecretary.Secretary.Dev.Grid.PartC
open MomentAmbiguitySecretary.Secretary
theorem grid_measure {k N : ℕ} (hk : 0 < k) (v : Fin N → ℝ≥0) (e : Fin k ↪o Fin N) :
    ((gridDistribution v (Finset.univ.map e.toEmbedding) : Distribution) : Measure ℝ≥0) =
      ∑ h : Fin k, (k : ℝ≥0∞)⁻¹ • Measure.dirac (v (e h)) := by
  have hne : (Finset.univ.map e.toEmbedding).Nonempty := ⟨e ⟨0, hk⟩, by simp⟩
  simp only [gridDistribution, hne, ↓reduceDIte]
  simp [Finset.sum_map]

theorem pi_measure {m k N : ℕ} (hk : 0 < k) (v : Fin N → ℝ≥0) (e : Fin k ↪o Fin N) :
    Measure.pi (fun _ : Fin m => ∑ h : Fin k, (k : ℝ≥0∞)⁻¹ • Measure.dirac (v (e h))) =
      ∑ a : Fin m → Fin k, ((k : ℝ≥0∞)⁻¹) ^ m • Measure.dirac (fun i => v (e (a i))) := by
  have : IsFiniteMeasure (∑ h : Fin k, (k : ℝ≥0∞)⁻¹ • Measure.dirac (v (e h))) := by
    constructor
    rw [Measure.finsetSum_apply]
    refine ENNReal.sum_lt_top.2 fun h _ => ?_
    simp [Measure.smul_apply, hk]
  refine Measure.pi_eq fun s hs => ?_
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (MeasurableSet.univ_pi hs), Measure.dirac_apply' _ (hs _)]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  by_cases h : ∀ i, v (e (a i)) ∈ s i
  · simp [h]
  · obtain ⟨i, hi⟩ := not_forall.1 h
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])]
    simp [h]

theorem perm_measure (m : ℕ) :
    ((uniformPermutation m : ProbabilityMeasure (Perm (Fin m))) : Measure (Perm (Fin m))) =
      ∑ σ : Perm (Fin m), ((m.factorial : ℝ≥0∞))⁻¹ • Measure.dirac σ := by
  refine Measure.ext_of_singleton fun σ => ?_
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (measurableSet_singleton σ)]
  change (PMF.uniformOfFintype (Perm (Fin m))).toMeasure {σ} = _
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton σ),
    PMF.uniformOfFintype_apply, Fintype.card_perm, Fintype.card_fin]
  simp [Set.indicator_apply]

theorem exp_measure {m k N : ℕ} (hk : 0 < k) (v : Fin N → ℝ≥0) (e : Fin k ↪o Fin N) :
    (experiment (fun _ : Fin m => gridDistribution v (Finset.univ.map e.toEmbedding)) :
        Measure (Path m)) =
      ∑ σ : Perm (Fin m), ∑ a : Fin m → Fin k,
        ((m.factorial : ℝ≥0∞) * (k : ℝ≥0∞) ^ m)⁻¹ •
          Measure.dirac ((σ, fun i => v (e (a i))) : Path m) := by
  change ((uniformPermutation m : Measure (Perm (Fin m)))).prod
      (Measure.pi (fun _ : Fin m =>
        ((gridDistribution v (Finset.univ.map e.toEmbedding) : Distribution) :
          Measure ℝ≥0))) = _
  refine Measure.prod_eq fun s t hs ht => ?_
  rw [perm_measure, grid_measure hk, pi_measure hk]
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (hs.prod ht), Measure.dirac_apply' _ hs, Measure.dirac_apply' _ ht]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun a _ => ?_
  rw [ENNReal.mul_inv (Or.inl (by exact_mod_cast (Nat.factorial_pos m).ne'))
    (Or.inl (ENNReal.natCast_ne_top _)), ENNReal.inv_pow]
  by_cases h1 : σ ∈ s <;> by_cases h2 : (fun i => v (e (a i))) ∈ t <;>
    simp [h1, h2, Set.mem_prod]

theorem section_measure {m : ℕ} (π : CardinalPolicy m) (σ : Perm (Fin m)) (x : Fin m → ℝ≥0) :
    fixedKernel π () ((σ, x) : Path m) (Prod.mk ((σ, x) : Path m) ⁻¹' successEvent m) =
      ∑ t : Fin m, π.kernel ((), (σ, x)) {some t} *
        (if ∀ i, x i ≤ x (σ t) then (1 : ℝ≥0∞) else 0) := by
  have hset : Prod.mk ((σ, x) : Path m) ⁻¹' successEvent m =
      ⋃ t ∈ Finset.univ.filter (fun t : Fin m => ∀ i, x i ≤ x (σ t)), {some t} := by
    ext o
    simp [successEvent, and_comm]
  rw [hset, fixedKernel, Kernel.comap_apply, measure_biUnion_finset]
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs <;> simp
  · intro i _ j _ hij
    simpa using hij
  · intro t _
    exact measurableSet_singleton _

theorem success_grid (m k N : ℕ) (hk : 0 < k) (π : CardinalPolicy m) (v : Fin N → ℝ≥0)
    (e : Fin k ↪o Fin N) :
    success π () (fun _ : Fin m => gridDistribution v (Finset.univ.map e.toEmbedding)) =
      ((m.factorial : ℝ) * (k : ℝ) ^ m)⁻¹ *
        ∑ σ : Perm (Fin m), ∑ a : Fin m → Fin k, ∑ t : Fin m,
          (π.kernel ((), (σ, fun i => v (e (a i)))) {some t}).toReal *
            (if ∀ i, v (e (a i)) ≤ v (e (a (σ t))) then (1 : ℝ) else 0) := by
  have hterm : ∀ (p : Path m) (t : Fin m) (c : Prop) [Decidable c],
      π.kernel ((), p) {some t} * (if c then (1 : ℝ≥0∞) else 0) ≠ ⊤ := fun p t c _ =>
    ENNReal.mul_ne_top (measure_ne_top _ _) (by split_ifs <;> simp)
  unfold success outcomeLaw
  change (((experiment (fun _ : Fin m => gridDistribution v (Finset.univ.map e.toEmbedding)) :
      Measure (Path m)) ⊗ₘ fixedKernel π ()) (successEvent m)).toReal = _
  rw [Measure.compProd_apply (successEvent_measurable m), exp_measure hk]
  simp only [lintegral_finsetSum_measure, lintegral_smul_measure, lintegral_dirac, smul_eq_mul,
    section_measure]
  simp_rw [← Finset.mul_sum]
  rw [ENNReal.toReal_mul]
  congr 1
  · simp [ENNReal.toReal_inv]
  · rw [ENNReal.toReal_sum fun σ _ => ?_]
    · refine Finset.sum_congr rfl fun σ _ => ?_
      rw [ENNReal.toReal_sum fun a _ => ?_]
      · refine Finset.sum_congr rfl fun a _ => ?_
        rw [ENNReal.toReal_sum fun t _ => ?_]
        · refine Finset.sum_congr rfl fun t _ => ?_
          rw [ENNReal.toReal_mul]
          split_ifs <;> simp
        · exact hterm _ _ _
      · exact ENNReal.sum_ne_top.2 fun t _ => hterm _ _ _
    · exact ENNReal.sum_ne_top.2 fun a _ => ENNReal.sum_ne_top.2 fun t _ => hterm _ _ _

end MomentAmbiguitySecretary.Secretary.Dev.Grid.PartC
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Equiv
open scoped BigOperators Topology NNReal ENNReal
namespace MomentAmbiguitySecretary.Secretary.Dev.Grid
open MomentAmbiguitySecretary.Secretary
alias success_grid := MomentAmbiguitySecretary.Secretary.Dev.Grid.PartC.success_grid

end MomentAmbiguitySecretary.Secretary.Dev.Grid
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Equiv
open scoped BigOperators Topology NNReal ENNReal
namespace MomentAmbiguitySecretary.Secretary.Dev.Grid.PartD
lemma card_eq_pair (m k : ℕ) (i j : Fin m) (hij : i ≠ j) :
    (Finset.univ.filter fun a : Fin m → Fin k => a i = a j).card * k = k ^ m := by
  have h1 : ((Finset.univ.filter fun a : Fin m → Fin k => a i = a j) ×ˢ
      (Finset.univ : Finset (Fin k))).card = (Finset.univ : Finset (Fin m → Fin k)).card := by
    refine Finset.card_nbij' (fun x => Function.update x.1 j x.2)
      (fun b => (Function.update b j (b i), b j)) ?_ ?_ ?_ ?_
    · intro x _; simp
    · intro b _
      simp [Function.update_of_ne hij]
    · rintro ⟨a, c⟩ hx
      simp only [Finset.coe_product, Finset.coe_filter, Finset.mem_univ, true_and,
        Finset.coe_univ, Set.mem_prod, Set.mem_ofPred_eq, Set.mem_univ, and_true] at hx
      simp only [Function.update_self, Function.update_of_ne hij, Prod.mk.injEq, and_true]
      funext t
      by_cases ht : t = j
      · subst ht; simp [hx]
      · simp [Function.update_of_ne ht]
    · intro b _
      funext t
      by_cases ht : t = j
      · subst ht; simp
      · simp [Function.update_of_ne ht]
  rw [Finset.card_product, Finset.card_univ, Finset.card_univ] at h1
  simpa [Fintype.card_fun, Fintype.card_fin] using h1

theorem card_not_injective (m k : ℕ) :
    ((Finset.univ.filter fun a : Fin m → Fin k => ¬ Function.Injective a).card : ℝ) * k
      ≤ (m.choose 2 : ℝ) * (k : ℝ) ^ m := by
  classical
  let g : Finset (Fin m) → Finset (Fin m → Fin k) := fun S =>
    Finset.univ.filter fun a => ∀ x ∈ S, ∀ y ∈ S, a x = a y
  have hsub : (Finset.univ.filter fun a : Fin m → Fin k => ¬ Function.Injective a) ⊆
      (Finset.univ.powersetCard 2).biUnion g := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.Injective,
      not_forall] at ha
    obtain ⟨x, y, hxy, hne⟩ := ha
    rw [Finset.mem_biUnion]
    refine ⟨{x, y}, ?_, ?_⟩
    · rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, Finset.card_pair hne⟩
    · simp only [g, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      rintro u (rfl | rfl) v (rfl | rfl) <;> simp [hxy]
  have hg : ∀ S ∈ (Finset.univ : Finset (Fin m)).powersetCard 2, (g S).card * k = k ^ m := by
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    obtain ⟨x, y, hne, rfl⟩ := Finset.card_eq_two.mp hS.2
    have : g {x, y} = Finset.univ.filter fun a : Fin m → Fin k => a x = a y := by
      ext a
      simp only [g, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · intro h; exact h x (Or.inl rfl) y (Or.inr rfl)
      · intro h
        rintro u (rfl | rfl) v (rfl | rfl) <;> simp [h]
    rw [this]
    exact card_eq_pair m k x y hne
  have key : (Finset.univ.filter fun a : Fin m → Fin k => ¬ Function.Injective a).card * k
      ≤ m.choose 2 * k ^ m := by
    calc _ ≤ (∑ S ∈ (Finset.univ : Finset (Fin m)).powersetCard 2, (g S).card) * k :=
          Nat.mul_le_mul_right _ ((Finset.card_le_card hsub).trans Finset.card_biUnion_le)
      _ = ∑ S ∈ (Finset.univ : Finset (Fin m)).powersetCard 2, (g S).card * k := by
          rw [Finset.sum_mul]
      _ = ∑ S ∈ (Finset.univ : Finset (Fin m)).powersetCard 2, k ^ m :=
          Finset.sum_congr rfl hg
      _ = m.choose 2 * k ^ m := by
          rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
            smul_eq_mul]
  exact_mod_cast key

end MomentAmbiguitySecretary.Secretary.Dev.Grid.PartD
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Equiv
open scoped BigOperators Topology NNReal ENNReal
namespace MomentAmbiguitySecretary.Secretary.Dev.Grid
open MomentAmbiguitySecretary.Secretary
alias card_not_injective := MomentAmbiguitySecretary.Secretary.Dev.Grid.PartD.card_not_injective

end MomentAmbiguitySecretary.Secretary.Dev.Grid
end

section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped BigOperators Topology NNReal ENNReal
namespace MomentAmbiguitySecretary.Secretary.Dev.Grid.Asm
open MomentAmbiguitySecretary.Secretary
open Equiv
/-!
Assembly of Lemma 6.1 (`ramsey_secretary_grid`) from the Blueprint stubs (A)–(D) of `GridBP.lean`.
-/
/-- The stopping mass at time `t` along the path `(σ, x)`. -/
noncomputable def fm {m : ℕ} (π : CardinalPolicy m) (σ : Perm (Fin m)) (x : Fin m → ℝ≥0)
    (t : Fin m) : ℝ :=
  (π.kernel ((), (σ, x)) {some t}).toReal

lemma fm_nonneg {m : ℕ} (π : CardinalPolicy m) (σ : Perm (Fin m)) (x : Fin m → ℝ≥0)
    (t : Fin m) : 0 ≤ fm π σ x t := ENNReal.toReal_nonneg

lemma sum_fm_le_one {m : ℕ} (π : CardinalPolicy m) (σ : Perm (Fin m)) (x : Fin m → ℝ≥0) :
    ∑ t, fm π σ x t ≤ 1 := by
  have hfin : ∀ t ∈ (Finset.univ : Finset (Fin m)), π.kernel ((), (σ, x)) {some t} ≠ ∞ :=
    fun t _ => measure_ne_top _ _
  unfold fm
  rw [← ENNReal.toReal_sum hfin]
  have h1 : ∑ t, π.kernel ((), (σ, x)) {some t} ≤ 1 := by
    have : ∑ t, π.kernel ((), (σ, x)) {some t} = π.kernel ((), (σ, x))
        ((Finset.univ.map ⟨some, Option.some_injective _⟩ : Finset (Option (Fin m))) : Set _) := by
      rw [← MeasureTheory.sum_measure_singleton, Finset.sum_map]; rfl
    rw [this]; exact prob_le_one
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using h1)

lemma fm_le_one {m : ℕ} (π : CardinalPolicy m) (σ : Perm (Fin m)) (x : Fin m → ℝ≥0)
    (t : Fin m) : fm π σ x t ≤ 1 :=
  (Finset.single_le_sum (fun i _ => fm_nonneg π σ x i) (Finset.mem_univ t)).trans
    (sum_fm_le_one π σ x)

lemma classicalValue_nonneg (m : ℕ) (hm : 1 ≤ m) : 0 ≤ classicalValue m := by
  rw [classicalValue, dif_pos hm]
  refine Finset.le_sup'_of_le _ (b := 1) (Finset.mem_Icc.mpr ⟨le_rfl, hm⟩) ?_
  simp only [cutoffProbability, if_true]
  exact div_nonneg zero_le_one (Nat.cast_nonneg m)

/-- Prefix rank data: for `j ≤ t`, the number of `i ≤ t` with `z i < z j`. -/
def rk {m k : ℕ} (hm : 0 < m) (t : Fin m) (z : Fin m → Fin k) (j : Fin m) : Fin m :=
  if j ≤ t then ⟨((Finset.Iic t).filter (fun i => z i < z j)).card % m, Nat.mod_lt _ hm⟩
  else ⟨0, hm⟩

lemma rk_congr {m k : ℕ} (hm : 0 < m) (t : Fin m) (z z' : Fin m → Fin k)
    (h : ∀ i j : Fin m, i ≤ t → j ≤ t → (z i < z j ↔ z' i < z' j)) :
    rk hm t z = rk hm t z' := by
  funext j
  unfold rk
  split_ifs with hj
  · ext
    simp only
    rw [Finset.filter_congr (fun i hi => h i j (Finset.mem_Iic.mp hi) hj)]
  · rfl

lemma card_filter_lt_orderEmbOfFin {α : Type*} [LinearOrder α] {n : ℕ} (S : Finset α)
    (h : S.card = n) (i : Fin n) :
    (S.filter (· < S.orderEmbOfFin h i)).card = i := by
  have : S.filter (· < S.orderEmbOfFin h i) =
      (Finset.Iio i).map (S.orderEmbOfFin h).toEmbedding := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_Iio, RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨hy, hlt⟩
      have : y ∈ Set.range (S.orderEmbOfFin h) := by
        rw [Finset.range_orderEmbOfFin]; exact hy
      obtain ⟨j, rfl⟩ := this
      exact ⟨j, (S.orderEmbOfFin h).lt_iff_lt.mp hlt, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem S h j, (S.orderEmbOfFin h).lt_iff_lt.mpr hj⟩
  rw [this, Finset.card_map, Fin.card_Iio]

lemma exists_w {m k : ℕ} (hm : 0 < m) (t : Fin m) (z : Fin m → Fin k)
    (hz : Function.Injective z) :
    ∃ w : Fin m ↪o Fin (k + m), ∀ j, j ≤ t →
      w (rk hm t z j) = Fin.castLE (Nat.le_add_right k m) (z j) := by
  have hcinj : Function.Injective (fun i => Fin.castLE (Nat.le_add_right k m) (z i)) :=
    (Fin.castLE_injective _).comp hz
  set P : Finset (Fin (k + m)) :=
    (Finset.Iic t).image (fun i => Fin.castLE (Nat.le_add_right k m) (z i)) with hP
  have hPcard : P.card = t + 1 := by
    rw [hP, Finset.card_image_of_injective _ hcinj, Fin.card_Iic]
  set Top : Finset (Fin (k + m)) := Finset.univ.map (Fin.natAddEmb k) with hTop
  have hTopcard : Top.card = m := by simp [hTop]
  obtain ⟨T, hTsub, hTcard⟩ :=
    Finset.exists_subset_card_eq (s := Top) (n := m - (t + 1)) (by omega)
  have hPlt : ∀ y ∈ P, (y : ℕ) < k := by
    intro y hy
    rw [hP, Finset.mem_image] at hy
    obtain ⟨i, -, rfl⟩ := hy
    simp
  have hTge : ∀ y ∈ T, k ≤ (y : ℕ) := by
    intro y hy
    have := hTsub hy
    rw [hTop, Finset.mem_map] at this
    obtain ⟨r, -, rfl⟩ := this
    show k ≤ (Fin.natAdd k r : ℕ)
    simp
  have hdisj : Disjoint P T := by
    rw [Finset.disjoint_left]
    intro y hy hy'
    have := hPlt y hy
    have := hTge y hy'
    omega
  have hScard : (P ∪ T).card = m := by
    rw [Finset.card_union_of_disjoint hdisj, hPcard, hTcard]
    have := t.isLt
    omega
  refine ⟨(P ∪ T).orderEmbOfFin hScard, ?_⟩
  intro j hj
  have hmem : Fin.castLE (Nat.le_add_right k m) (z j) ∈ P ∪ T :=
    Finset.mem_union_left _ (by
      rw [hP]; exact Finset.mem_image_of_mem _ (Finset.mem_Iic.mpr hj))
  have : Fin.castLE (Nat.le_add_right k m) (z j) ∈ Set.range ((P ∪ T).orderEmbOfFin hScard) := by
    rw [Finset.range_orderEmbOfFin]; exact hmem
  obtain ⟨i, hi⟩ := this
  have hcount : ((P ∪ T).filter (· < Fin.castLE (Nat.le_add_right k m) (z j))).card =
      ((Finset.Iic t).filter (fun i => z i < z j)).card := by
    rw [Finset.filter_union]
    have hT0 : T.filter (· < Fin.castLE (Nat.le_add_right k m) (z j)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro y hy
      have := hTge y hy
      simp only [not_lt, Fin.le_iff_val_le_val, Fin.val_castLE]
      have := (z j).isLt
      omega
    rw [hT0, Finset.union_empty, hP, Finset.filter_image,
      Finset.card_image_of_injective _ hcinj]
    congr 1
  have hi2 := card_filter_lt_orderEmbOfFin (P ∪ T) hScard i
  rw [hi, hcount] at hi2
  have hrk : rk hm t z j = i := by
    unfold rk
    rw [if_pos hj]
    ext
    simp only
    rw [hi2, Nat.mod_eq_of_lt i.isLt]
  rw [hrk, hi]

/-- The Ramsey colouring: floors of the stopping masses at resolution `δ`, capped at `M`. -/
noncomputable def colour {m N : ℕ} (π : CardinalPolicy m) (v : Fin N → ℝ≥0) (δ : ℝ) (M : ℕ)
    (w : Fin m ↪o Fin N) : Fin m → Perm (Fin m) → (Fin m → Fin m) → Fin (M + 1) :=
  fun t σ ρ => ⟨min ⌊fm π σ (fun i => v (w (ρ (σ⁻¹ i)))) t / δ⌋₊ M,
    Nat.lt_succ_of_le (min_le_right _ _)⟩

lemma key {m k N : ℕ} (hm : 0 < m) (π : CardinalPolicy m) (v : Fin N → ℝ≥0) (δ : ℝ)
    (hδ : 0 < δ) (E : Fin (k + m) ↪o Fin N)
    (hE : ∀ U U' : Fin m ↪o Fin (k + m),
      colour π v δ ⌊1 / δ⌋₊ (U.trans E) = colour π v δ ⌊1 / δ⌋₊ (U'.trans E))
    (U₀ : Fin m ↪o Fin (k + m)) (σ : Perm (Fin m)) (z : Fin m → Fin k)
    (hz : Function.Injective z) (t : Fin m) :
    δ * ((colour π v δ ⌊1 / δ⌋₊ (U₀.trans E) t σ (rk hm t z) : ℕ) : ℝ) ≤
        fm π σ (fun i => v (E (Fin.castLE (Nat.le_add_right k m) (z (σ⁻¹ i))))) t ∧
      fm π σ (fun i => v (E (Fin.castLE (Nat.le_add_right k m) (z (σ⁻¹ i))))) t <
        δ * ((colour π v δ ⌊1 / δ⌋₊ (U₀.trans E) t σ (rk hm t z) : ℕ) : ℝ) + δ := by
  set F := fm π σ (fun i => v (E (Fin.castLE (Nat.le_add_right k m) (z (σ⁻¹ i))))) t with hF
  obtain ⟨w, hw⟩ := exists_w hm t z hz
  have hFw : fm π σ (fun i => v ((w.trans E) (rk hm t z (σ⁻¹ i)))) t = F := by
    rw [hF]
    unfold fm
    congr 1
    refine π.causal () _ _ t ?_
    intro i hi
    have hσ : σ⁻¹ (σ i) = i := by simp
    simp only [observation, hσ, RelEmbedding.coe_trans, Function.comp_apply, hw i hi]
  have hc : ((colour π v δ ⌊1 / δ⌋₊ (U₀.trans E) t σ (rk hm t z) : ℕ)) =
      min ⌊F / δ⌋₊ ⌊1 / δ⌋₊ := by
    rw [hE U₀ w]
    simp only [colour, hFw]
  have hFle : F ≤ 1 := fm_le_one _ _ _ _
  have hF0 : 0 ≤ F := fm_nonneg _ _ _ _
  have hmin : min ⌊F / δ⌋₊ ⌊1 / δ⌋₊ = ⌊F / δ⌋₊ :=
    min_eq_left (Nat.floor_le_floor (div_le_div_of_nonneg_right hFle hδ.le))
  rw [hc, hmin]
  constructor
  · have := Nat.floor_le (div_nonneg hF0 hδ.le)
    calc δ * (⌊F / δ⌋₊ : ℝ) ≤ δ * (F / δ) := mul_le_mul_of_nonneg_left this hδ.le
      _ = F := by field_simp
  · have := Nat.lt_floor_add_one (F / δ)
    calc F = δ * (F / δ) := by field_simp
      _ < δ * ((⌊F / δ⌋₊ : ℝ) + 1) := mul_lt_mul_of_pos_left this hδ
      _ = _ := by ring

lemma inj_part {m k N : ℕ} (hm : 1 ≤ m) (hmk : m ≤ k) (π : CardinalPolicy m)
    (v : Fin N → ℝ≥0) (hv : StrictMono v) (δ : ℝ) (hδ : 0 < δ) (E : Fin (k + m) ↪o Fin N)
    (hE : ∀ U U' : Fin m ↪o Fin (k + m),
      colour π v δ ⌊1 / δ⌋₊ (U.trans E) = colour π v δ ⌊1 / δ⌋₊ (U'.trans E))
    (σ : Perm (Fin m)) :
    ∑ a ∈ Finset.univ.filter (fun a : Fin m → Fin k => Function.Injective a), ∑ t : Fin m,
        fm π σ (fun i => v (E (Fin.castLE (Nat.le_add_right k m) (a i)))) t *
          (if ∀ i, v (E (Fin.castLE (Nat.le_add_right k m) (a i))) ≤
              v (E (Fin.castLE (Nat.le_add_right k m) (a (σ t)))) then (1 : ℝ) else 0)
      ≤ ((Finset.univ.filter (fun a : Fin m → Fin k => Function.Injective a)).card : ℝ) *
          (classicalValue m + m * δ) := by
  have hm0 : 0 < m := hm
  set inj := Finset.univ.filter (fun a : Fin m → Fin k => Function.Injective a) with hinj
  set c : Fin k → Fin (k + m) := Fin.castLE (Nat.le_add_right k m) with hc
  have hg : StrictMono (fun x : Fin k => v (E (c x))) :=
    hv.comp (E.strictMono.comp (Fin.strictMono_castLE _))
  let U₀ : Fin m ↪o Fin (k + m) := Fin.castLEOrderEmb (by omega)
  let F : Fin m → (Fin m → Fin k) → ℝ := fun t z => fm π σ (fun i => v (E (c (z (σ⁻¹ i))))) t
  let G : Fin m → (Fin m → Fin k) → ℝ := fun t z =>
    δ * ((colour π v δ ⌊1 / δ⌋₊ (U₀.trans E) t σ (rk hm0 t z) : ℕ) : ℝ)
  have hre : ∑ a ∈ inj, ∑ t : Fin m, fm π σ (fun i => v (E (c (a i)))) t *
        (if ∀ i, v (E (c (a i))) ≤ v (E (c (a (σ t)))) then (1 : ℝ) else 0) =
      ∑ z ∈ inj, ∑ t : Fin m, F t z * (if ∀ i, z i ≤ z t then (1 : ℝ) else 0) := by
    refine Finset.sum_nbij' (fun a => fun j => a (σ j)) (fun z => fun i => z (σ⁻¹ i))
      ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [hinj, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      exact ha.comp σ.injective
    · intro z hz
      simp only [hinj, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact hz.comp (σ⁻¹).injective
    · intro a _
      funext i
      simp
    · intro z _
      funext j
      simp
    · intro a _
      refine Finset.sum_congr rfl fun t _ => ?_
      have h1 : (fun i => v (E (c (a (σ (σ⁻¹ i)))))) = fun i => v (E (c (a i))) := by
        funext i; simp
      have h2 : (∀ i, v (E (c (a i))) ≤ v (E (c (a (σ t))))) ↔ ∀ i, a (σ i) ≤ a (σ t) := by
        constructor
        · intro h i; exact hg.le_iff_le.mp (h (σ i))
        · intro h i
          have := h (σ⁻¹ i)
          have hσ : σ (σ⁻¹ i) = i := by simp
          rw [hσ] at this
          exact hg.le_iff_le.mpr this
      simp only [F, h1]
      rw [if_congr h2 rfl rfl]
  rw [hre]
  have hkey : ∀ z ∈ inj, ∀ t, G t z ≤ F t z ∧ F t z < G t z + δ := by
    intro z hz t
    simp only [hinj, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    exact key hm0 π v δ hδ E hE U₀ σ z hz t
  have hA := secretary_mass_bound m k hm hmk G
    (fun t z => mul_nonneg hδ.le (Nat.cast_nonneg _))
    (fun z hz => by
      refine (Finset.sum_le_sum fun t _ => ?_).trans
        (sum_fm_le_one π σ (fun i => v (E (c (z (σ⁻¹ i))))))
      exact (hkey z (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩) t).1)
    (fun t z z' h => by simp only [G]; rw [rk_congr hm0 t z z' h])
  calc ∑ z ∈ inj, ∑ t : Fin m, F t z * (if ∀ i, z i ≤ z t then (1 : ℝ) else 0)
      ≤ ∑ z ∈ inj, ∑ t : Fin m, (G t z * (if ∀ i, z i ≤ z t then (1 : ℝ) else 0) + δ) := by
        refine Finset.sum_le_sum fun z hz => Finset.sum_le_sum fun t _ => ?_
        have := hkey z hz t
        have := mul_nonneg hδ.le (Nat.cast_nonneg
          ((colour π v δ ⌊1 / δ⌋₊ (U₀.trans E) t σ (rk hm0 t z) : ℕ)))
        split_ifs <;> simp only [G] at * <;> linarith
    _ = ∑ z ∈ inj, ∑ t : Fin m, G t z * (if ∀ i, z i ≤ z t then (1 : ℝ) else 0) +
          inj.card * (m * δ) := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
    _ ≤ inj.card * classicalValue m + inj.card * (m * δ) := by linarith
    _ = _ := by ring

end MomentAmbiguitySecretary.Secretary.Dev.Grid.Asm
end

section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped BigOperators Topology NNReal ENNReal
namespace MomentAmbiguitySecretary.Secretary
open Dev.Grid Dev.Grid.Asm in
theorem chk_ramsey_secretary_grid (m k : ℕ) (hm : 1 ≤ m) (hk : m ≤ k)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, k ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ v : Fin N → ℝ≥0, StrictMono v → ∀ π : CardinalPolicy m,
      ∃ H : Finset (Fin N), H.card = k ∧
        success π () (fun _ : Fin m => gridDistribution v H) ≤
          classicalValue m + ε + (Nat.choose m 2 : ℝ) / (k : ℝ) := by
  have hm0 : 0 < m := hm
  have hk0 : 0 < k := by omega
  set δ : ℝ := ε / (2 * m) with hδdef
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hδ : 0 < δ := by positivity
  have hmδ : (m : ℝ) * δ < ε := by
    rw [hδdef, mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
  obtain ⟨N₁, hN₁⟩ := ramsey_ordered
    (Fin m → Equiv.Perm (Fin m) → (Fin m → Fin m) → Fin (⌊1 / δ⌋₊ + 1)) m (k + m) hm (by omega)
  refine ⟨max N₁ k, le_max_right _ _, ?_⟩
  intro N hN v hv π
  obtain ⟨E, hE⟩ := hN₁ N (le_of_max_le_left hN) (colour π v δ ⌊1 / δ⌋₊)
  let e : Fin k ↪o Fin N := (Fin.castLEOrderEmb (Nat.le_add_right k m)).trans E
  refine ⟨Finset.univ.map e.toEmbedding, by simp, ?_⟩
  rw [success_grid m k N hk0 π v e]
  set inj := Finset.univ.filter (fun a : Fin m → Fin k => Function.Injective a) with hinj
  set ninj := Finset.univ.filter (fun a : Fin m → Fin k => ¬ Function.Injective a) with hninj
  set V := classicalValue m with hV
  have hV0 : 0 ≤ V := classicalValue_nonneg m hm
  have hT : ∀ σ : Equiv.Perm (Fin m), ∑ a : Fin m → Fin k, ∑ t : Fin m,
      (π.kernel ((), (σ, fun i => v (e (a i)))) {some t}).toReal *
        (if ∀ i, v (e (a i)) ≤ v (e (a (σ t))) then (1 : ℝ) else 0)
      ≤ ninj.card + inj.card * (V + m * δ) := by
    intro σ
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun a => Function.Injective a)]
    have h1 : ∑ a ∈ inj, ∑ t : Fin m,
        (π.kernel ((), (σ, fun i => v (e (a i)))) {some t}).toReal *
          (if ∀ i, v (e (a i)) ≤ v (e (a (σ t))) then (1 : ℝ) else 0) ≤ inj.card * (V + m * δ) :=
      inj_part hm hk π v hv δ hδ E hE σ
    have h2 : ∑ a ∈ ninj, ∑ t : Fin m,
        (π.kernel ((), (σ, fun i => v (e (a i)))) {some t}).toReal *
          (if ∀ i, v (e (a i)) ≤ v (e (a (σ t))) then (1 : ℝ) else 0) ≤ ninj.card := by
      calc _ ≤ ∑ a ∈ ninj, (1 : ℝ) := by
            refine Finset.sum_le_sum fun a _ => ?_
            refine (Finset.sum_le_sum fun t _ => ?_).trans (sum_fm_le_one π σ (fun i => v (e (a i))))
            have := fm_nonneg π σ (fun i => v (e (a i))) t
            unfold fm at this ⊢
            split_ifs <;> simp [this]
        _ = ninj.card := by simp
    linarith
  have hKpos : (0 : ℝ) < (k : ℝ) ^ m := by positivity
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hfac : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  refine (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => hT σ) (by positivity)).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  have hD : (ninj.card : ℝ) * k ≤ (m.choose 2 : ℝ) * (k : ℝ) ^ m := card_not_injective m k
  have hi : (inj.card : ℝ) ≤ (k : ℝ) ^ m := by
    have : inj.card ≤ k ^ m := by
      calc inj.card ≤ (Finset.univ : Finset (Fin m → Fin k)).card := Finset.card_filter_le _ _
        _ = k ^ m := by simp
    exact_mod_cast this
  have hn : (ninj.card : ℝ) ≤ (m.choose 2 : ℝ) / k * (k : ℝ) ^ m := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hkR]; linarith
  have hW0 : 0 ≤ V + m * δ := by positivity
  have h1 : (inj.card : ℝ) * (V + m * δ) ≤ (k : ℝ) ^ m * (V + m * δ) :=
    mul_le_mul_of_nonneg_right hi hW0
  have h2 : (k : ℝ) ^ m * (V + m * δ) ≤ (k : ℝ) ^ m * (V + ε) :=
    mul_le_mul_of_nonneg_left (by linarith) hKpos.le
  rw [show ((m.factorial : ℝ) * (k : ℝ) ^ m)⁻¹ *
      ((m.factorial : ℝ) * ((ninj.card : ℝ) + inj.card * (V + m * δ))) =
      ((ninj.card : ℝ) + inj.card * (V + m * δ)) / (k : ℝ) ^ m by field_simp]
  rw [div_le_iff₀ hKpos]
  nlinarith

end MomentAmbiguitySecretary.Secretary
end

theorem solution : type_of% @MomentAmbiguitySecretary.Secretary.chk_ramsey_secretary_grid := @MomentAmbiguitySecretary.Secretary.chk_ramsey_secretary_grid
