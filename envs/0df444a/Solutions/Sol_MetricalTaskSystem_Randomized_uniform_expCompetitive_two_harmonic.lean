-- Prove2me | solution 1 for MetricalTaskSystem.Randomized.uniform_expCompetitive_two_harmonic
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T22:59:30.525582+00:00
-- url     : https://prove2.me/submissions/b82eb1cd-ccb3-4293-bb5d-73ed75b31614

import Definitions.Def_MetricalTaskSystem_Randomized_Model
import Definitions.Def_MetricalTaskSystem_Randomized_RandomizedAlgorithm

open MetricalTaskSystem.Randomized
open scoped ENNReal

private def snocFun {S : Type} {k : ℕ} (v : Fin k → S) (x : S) (i : Fin (k + 1)) : S :=
  if h : i.val < k then v ⟨i.val, h⟩ else x

private def snocEquiv {S : Type} (k : ℕ) : ((Fin k → S) × S) ≃ (Fin (k + 1) → S) where
  toFun p := snocFun p.1 p.2
  invFun w := (fun i => w i.castSucc, w (Fin.last k))
  left_inv := by
    rintro ⟨v, x⟩
    ext i
    · simp [snocFun, i.isLt]
    · simp [snocFun, Fin.last]
  right_inv := by
    intro w
    ext i
    dsimp [snocFun]
    split_ifs with h
    · rfl
    · have hi : i = Fin.last k := Fin.ext (by dsimp [Fin.last]; omega)
      rw [hi]

private lemma harmonic_one_real : (harmonic 1 : ℝ) = 1 := by
  unfold harmonic
  simp

private lemma harmonic_two_real : (harmonic 2 : ℝ) = 3 / 2 := by
  rw [harmonic_succ 1, harmonic_succ 0]
  push_cast
  norm_num

private lemma harmonic_mono_real {a b : ℕ} (hab : a ≤ b) :
    (harmonic a : ℝ) ≤ (harmonic b : ℝ) := by
  induction b, hab using Nat.le_induction with
  | base => exact le_refl _
  | succ k _ ih =>
    rw [harmonic_succ]
    push_cast
    have : (0 : ℝ) ≤ ((k : ℝ) + 1)⁻¹ := by positivity
    linarith

private lemma one_le_harmonic_real {a : ℕ} (ha : 1 ≤ a) :
    (1 : ℝ) ≤ (harmonic a : ℝ) := by
  rw [← harmonic_one_real]
  exact harmonic_mono_real ha

private lemma three_halves_le_harmonic_real {a : ℕ} (ha : 2 ≤ a) :
    (3 / 2 : ℝ) ≤ (harmonic a : ℝ) := by
  rw [← harmonic_two_real]
  exact harmonic_mono_real ha

private lemma sub_div_le_harmonic_sub {a b : ℕ} (hb : 0 < b) (hba : b ≤ a) :
    ((a : ℝ) - (b : ℝ)) / (a : ℝ) ≤ (harmonic a : ℝ) - (harmonic b : ℝ) := by
  induction a, hba using Nat.le_induction with
  | base => simp
  | succ k hbk ih =>
    have hk_pos : 0 < k := lt_of_lt_of_le hb hbk
    have hk_real : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk_pos
    have hk1_real : (0 : ℝ) < (k : ℝ) + 1 := by linarith
    have hbk_real : (b : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hbk
    rw [harmonic_succ k]
    push_cast
    have hstep : ((k : ℝ) + 1 - (b : ℝ)) / ((k : ℝ) + 1) ≤
        ((k : ℝ) - (b : ℝ)) / (k : ℝ) + ((k : ℝ) + 1)⁻¹ := by
      have h1 : ((k : ℝ) + 1 - (b : ℝ)) / ((k : ℝ) + 1) =
          1 - (b : ℝ) / ((k : ℝ) + 1) := by
        rw [sub_div, div_self (ne_of_gt hk1_real)]
      have h2 : ((k : ℝ) - (b : ℝ)) / (k : ℝ) + ((k : ℝ) + 1)⁻¹ =
          1 - (b : ℝ) / (k : ℝ) + 1 / ((k : ℝ) + 1) := by
        rw [sub_div, div_self (ne_of_gt hk_real), one_div]
      rw [h1, h2]
      have hdiff : (b : ℝ) / (k : ℝ) - (b : ℝ) / ((k : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) := by
        rw [div_sub_div _ _ (ne_of_gt hk_real) (ne_of_gt hk1_real)]
        rw [div_le_div_iff₀ (mul_pos hk_real hk1_real) hk1_real]
        nlinarith
      linarith
    linarith

private lemma pmf_pure_toReal {S : Type} [DecidableEq S] (x y : S) :
    (PMF.pure x y).toReal = if y = x then 1 else 0 := by
  rw [PMF.pure_apply]
  split_ifs <;> simp

private lemma pmf_ofFinset_toReal {S : Type} [Fintype S] [DecidableEq S]
    (U : Finset S) (hU : U.Nonempty) (y : S) :
    (PMF.uniformOfFinset U hU y).toReal = if y ∈ U then (U.card : ℝ)⁻¹ else 0 := by
  rw [PMF.uniformOfFinset_apply]
  split_ifs <;> simp

private lemma sum_pmf_pure_mul {S : Type} [Fintype S] [DecidableEq S]
    (x : S) (f : S → ℝ) :
    ∑ y : S, (PMF.pure x y).toReal * f y = f x := by
  simp_rw [pmf_pure_toReal]
  have h1 : ∀ y : S, (if y = x then (1 : ℝ) else 0) * f y = if y = x then f x else 0 := by
    intro y
    split_ifs with h
    · subst h; ring
    · ring
  simp_rw [h1]
  simp

private lemma sum_pmf_ofFinset_mul {S : Type} [Fintype S] [DecidableEq S]
    (U : Finset S) (hU : U.Nonempty) (f : S → ℝ) :
    ∑ y : S, (PMF.uniformOfFinset U hU y).toReal * f y =
      (U.card : ℝ)⁻¹ * ∑ y ∈ U, f y := by
  simp_rw [pmf_ofFinset_toReal]
  have h1 : ∀ y : S, (if y ∈ U then (U.card : ℝ)⁻¹ else 0) * f y =
      (U.card : ℝ)⁻¹ * (if y ∈ U then f y else 0) := by
    intro y
    split_ifs <;> ring
  simp_rw [h1, ← Finset.mul_sum, ← Finset.sum_filter, Finset.filter_univ_mem]

private noncomputable def nextW {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (W : S → ℝ) (t : S → ℝ) (s : S) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun y => W y + max (t y) 0 + uniformD y s)

private noncomputable def minVal {S : Type} [Fintype S] [Nonempty S] (W : S → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty W

private noncomputable def wfStep {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (WM : (S → ℝ) × ℝ) (t : S → ℝ) : (S → ℝ) × ℝ :=
  let W' := nextW WM.1 t
  let μ' := minVal W'
  (W', if μ' < WM.2 + 1 then WM.2 else μ')

private noncomputable def wfAt {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) (L_T : List (S → ℝ)) : ℕ → (S → ℝ) × ℝ
  | 0 => (fun s => uniformD s₀ s, 0)
  | k + 1 => wfStep (wfAt s₀ L_T k) (L_T.getD k (fun _ => 0))

private noncomputable def WAt {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) (L_T : List (S → ℝ)) (k : ℕ) : S → ℝ :=
  (wfAt s₀ L_T k).1

private noncomputable def MAt {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) (L_T : List (S → ℝ)) (k : ℕ) : ℝ :=
  (wfAt s₀ L_T k).2

private noncomputable def μAt {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) (L_T : List (S → ℝ)) (k : ℕ) : ℝ :=
  minVal (WAt s₀ L_T k)

private noncomputable def UAt {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) (L_T : List (S → ℝ)) (k : ℕ) : Finset S :=
  Finset.univ.filter (fun s => WAt s₀ L_T k s < MAt s₀ L_T k + 1)

private lemma uniformD_self {S : Type} [DecidableEq S] (s : S) :
    uniformD s s = 0 := if_pos rfl

private lemma uniformD_nonneg {S : Type} [DecidableEq S] (x y : S) :
    0 ≤ uniformD x y := by
  dsimp [uniformD]
  split_ifs <;> norm_num

private lemma uniformD_le_one {S : Type} [DecidableEq S] (x y : S) :
    uniformD x y ≤ 1 := by
  dsimp [uniformD]
  split_ifs <;> norm_num

private lemma uniformD_triangle {S : Type} [DecidableEq S] (x y z : S) :
    uniformD x z ≤ uniformD x y + uniformD y z := by
  by_cases h1 : x = y <;> by_cases h2 : y = z <;> by_cases h3 : x = z <;> simp_all [uniformD]

private lemma WAt_succ_eq {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) (L_T : List (S → ℝ)) (k : ℕ) :
    WAt s₀ L_T (k + 1) = nextW (WAt s₀ L_T k) (L_T.getD k (fun _ => 0)) := rfl

private lemma MAt_succ_eq {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) (L_T : List (S → ℝ)) (k : ℕ) :
    MAt s₀ L_T (k + 1) =
      if μAt s₀ L_T (k + 1) < MAt s₀ L_T k + 1 then MAt s₀ L_T k else μAt s₀ L_T (k + 1) := rfl

private lemma WAt_metric {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) (L_T : List (S → ℝ)) (k : ℕ) (y s : S) :
    WAt s₀ L_T k s ≤ WAt s₀ L_T k y + uniformD y s := by
  induction k with
  | zero =>
    change uniformD s₀ s ≤ uniformD s₀ y + uniformD y s
    exact uniformD_triangle s₀ y s
  | succ k _ =>
    rw [WAt_succ_eq, ← sub_le_iff_le_add]
    unfold nextW
    rw [Finset.le_inf'_iff]
    intro z _
    have hz : Finset.univ.inf' Finset.univ_nonempty
        (fun w => WAt s₀ L_T k w + max (L_T.getD k (fun _ => 0) w) 0 + uniformD w s) ≤
        WAt s₀ L_T k z + max (L_T.getD k (fun _ => 0) z) 0 + uniformD z s :=
      Finset.inf'_le _ (Finset.mem_univ z)
    have htri := uniformD_triangle z y s
    linarith

private lemma WAt_mono {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) (L_T : List (S → ℝ)) (k : ℕ) (s : S) :
    WAt s₀ L_T k s ≤ WAt s₀ L_T (k + 1) s := by
  rw [WAt_succ_eq]
  unfold nextW
  rw [Finset.le_inf'_iff]
  intro y _
  have h1 := WAt_metric s₀ L_T k y s
  have h2 : 0 ≤ max (L_T.getD k (fun _ => 0) y) 0 := le_max_right _ _
  linarith

private lemma μAt_le_WAt {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) (L_T : List (S → ℝ)) (k : ℕ) (s : S) :
    μAt s₀ L_T k ≤ WAt s₀ L_T k s :=
  Finset.inf'_le _ (Finset.mem_univ s)

private lemma μAt_mono {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) (L_T : List (S → ℝ)) (k : ℕ) :
    μAt s₀ L_T k ≤ μAt s₀ L_T (k + 1) := by
  unfold μAt minVal
  rw [Finset.le_inf'_iff]
  intro s _
  exact le_trans (μAt_le_WAt s₀ L_T k s) (WAt_mono s₀ L_T k s)

private lemma WAt_succ_le_add {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) (L_T : List (S → ℝ)) (k : ℕ) (s : S) :
    WAt s₀ L_T (k + 1) s ≤ WAt s₀ L_T k s + max (L_T.getD k (fun _ => 0) s) 0 := by
  rw [WAt_succ_eq]
  unfold nextW
  have h := Finset.inf'_le
    (f := fun y => WAt s₀ L_T k y + max (L_T.getD k (fun _ => 0) y) 0 + uniformD y s)
    (Finset.mem_univ s)
  rw [uniformD_self, add_zero] at h
  exact h

private lemma WAt_le_μAt_add_one {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) (L_T : List (S → ℝ)) (k : ℕ) (s : S) :
    WAt s₀ L_T k s ≤ μAt s₀ L_T k + 1 := by
  obtain ⟨y, _, hy⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (WAt s₀ L_T k)
  have h1 := WAt_metric s₀ L_T k y s
  have h2 := uniformD_le_one y s
  change μAt s₀ L_T k = WAt s₀ L_T k y at hy
  linarith

private lemma WAt_succ_eq_add_of_lt {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) (L_T : List (S → ℝ)) (k : ℕ) {s : S}
    (h : WAt s₀ L_T (k + 1) s < μAt s₀ L_T (k + 1) + 1) :
    WAt s₀ L_T (k + 1) s = WAt s₀ L_T k s + max (L_T.getD k (fun _ => 0) s) 0 := by
  apply le_antisymm (WAt_succ_le_add s₀ L_T k s)
  rw [WAt_succ_eq] at h ⊢
  obtain ⟨y, _, hy⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (fun y => WAt s₀ L_T k y + max (L_T.getD k (fun _ => 0) y) 0 + uniformD y s)
  change nextW (WAt s₀ L_T k) (L_T.getD k (fun _ => 0)) s =
    WAt s₀ L_T k y + max (L_T.getD k (fun _ => 0) y) 0 + uniformD y s at hy
  by_cases hys : y = s
  · subst hys
    rw [hy, uniformD_self, add_zero]
  · exfalso
    have hd : uniformD y s = 1 := if_neg hys
    have hμ : μAt s₀ L_T (k + 1) ≤ WAt s₀ L_T (k + 1) y := μAt_le_WAt s₀ L_T (k + 1) y
    have hle : WAt s₀ L_T (k + 1) y ≤ WAt s₀ L_T k y + max (L_T.getD k (fun _ => 0) y) 0 :=
      WAt_succ_le_add s₀ L_T k y
    rw [ ← WAt_succ_eq ] at hy h
    linarith

private lemma μAt_zero {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) (L_T : List (S → ℝ)) :
    μAt s₀ L_T 0 = 0 := by
  apply le_antisymm
  · have h := μAt_le_WAt s₀ L_T 0 s₀
    change μAt s₀ L_T 0 ≤ uniformD s₀ s₀ at h
    rwa [uniformD_self] at h
  · unfold μAt minVal
    rw [Finset.le_inf'_iff]
    intro s _
    exact uniformD_nonneg s₀ s

private lemma MAt_bounds {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) (L_T : List (S → ℝ)) (k : ℕ) :
    MAt s₀ L_T k ≤ μAt s₀ L_T k ∧ μAt s₀ L_T k < MAt s₀ L_T k + 1 := by
  induction k with
  | zero =>
    rw [μAt_zero]
    change (0 : ℝ) ≤ 0 ∧ (0 : ℝ) < 0 + 1
    norm_num
  | succ k ih =>
    rw [MAt_succ_eq]
    have hmono := μAt_mono s₀ L_T k
    split_ifs with hlt
    · exact ⟨le_trans ih.1 hmono, hlt⟩
    · exact ⟨le_refl _, by linarith⟩

private lemma MAt_mono {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) (L_T : List (S → ℝ)) (k : ℕ) :
    MAt s₀ L_T k ≤ MAt s₀ L_T (k + 1) := by
  rw [MAt_succ_eq]
  split_ifs with hlt
  · exact le_refl _
  · exact le_trans (MAt_bounds s₀ L_T k).1 (μAt_mono s₀ L_T k)

private lemma UAt_nonempty {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) (L_T : List (S → ℝ)) (k : ℕ) :
    (UAt s₀ L_T k).Nonempty := by
  obtain ⟨s, _, hs⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (WAt s₀ L_T k)
  refine ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ s, ?_⟩⟩
  change μAt s₀ L_T k = WAt s₀ L_T k s at hs
  rw [← hs]
  exact (MAt_bounds s₀ L_T k).2

private lemma UAt_zero {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) (L_T : List (S → ℝ)) :
    UAt s₀ L_T 0 = {s₀} := by
  ext s
  simp only [UAt, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  change uniformD s₀ s < 0 + 1 ↔ s = s₀
  dsimp [uniformD]
  split_ifs with h
  · exact ⟨fun _ => h.symm, fun _ => by norm_num⟩
  · exact ⟨fun hlt => False.elim (by linarith), fun heq => False.elim (h heq.symm)⟩

private lemma UAt_subset_of_branchA {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) (L_T : List (S → ℝ)) (k : ℕ)
    (hA : μAt s₀ L_T (k + 1) < MAt s₀ L_T k + 1) :
    UAt s₀ L_T (k + 1) ⊆ UAt s₀ L_T k := by
  intro s hs
  have hs' : WAt s₀ L_T (k + 1) s < MAt s₀ L_T (k + 1) + 1 := (Finset.mem_filter.mp hs).2
  rw [MAt_succ_eq, if_pos hA] at hs'
  have hmono := WAt_mono s₀ L_T k s
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ s, lt_of_le_of_lt hmono hs'⟩

private lemma WAt_sub_MAt_bounds {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) (L_T : List (S → ℝ)) (k : ℕ) {s : S} (hs : s ∈ UAt s₀ L_T k) :
    0 ≤ WAt s₀ L_T k s - MAt s₀ L_T k ∧ WAt s₀ L_T k s - MAt s₀ L_T k ≤ 1 := by
  have hlt : WAt s₀ L_T k s < MAt s₀ L_T k + 1 := (Finset.mem_filter.mp hs).2
  have hM : MAt s₀ L_T k ≤ WAt s₀ L_T k s :=
    le_trans (MAt_bounds s₀ L_T k).1 (μAt_le_WAt s₀ L_T k s)
  exact ⟨by linarith, by linarith⟩

private lemma wfAt_take {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) (L_T : List (S → ℝ)) (k n : ℕ) (hk : k ≤ n) :
    wfAt s₀ (L_T.take n) k = wfAt s₀ L_T k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold wfAt
    rw [ih (Nat.le_of_succ_le hk)]
    have hget : (L_T.take n).getD k (fun _ => 0) = L_T.getD k (fun _ => 0) := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk]
    rw [hget]

private noncomputable def stepKernel {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) (L_T : List (S → ℝ)) (k : ℕ) (x : S) : PMF S :=
  if μAt s₀ L_T (k + 1) < MAt s₀ L_T k + 1 then
    if x ∈ UAt s₀ L_T (k + 1) then PMF.pure x
    else PMF.uniformOfFinset (UAt s₀ L_T (k + 1)) (UAt_nonempty s₀ L_T (k + 1))
  else
    PMF.uniformOfFinset (UAt s₀ L_T (k + 1)) (UAt_nonempty s₀ L_T (k + 1))

private noncomputable def algR {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] :
    RandomizedOnlineAlgorithm S :=
  fun s₀ L_T L_S =>
    let k := L_T.length - 1
    stepKernel s₀ L_T k (L_S.getD k s₀)

private lemma stepKernel_stationary {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) (L_T : List (S → ℝ)) (k : ℕ) (f : S → ℝ) :
    ((UAt s₀ L_T k).card : ℝ)⁻¹ *
      (∑ x ∈ UAt s₀ L_T k, ∑ y : S, (stepKernel s₀ L_T k x y).toReal * f y) =
      ((UAt s₀ L_T (k + 1)).card : ℝ)⁻¹ * ∑ y ∈ UAt s₀ L_T (k + 1), f y := by
  let U := UAt s₀ L_T k
  let U' := UAt s₀ L_T (k + 1)
  have hU : U.Nonempty := UAt_nonempty s₀ L_T k
  have hU' : U'.Nonempty := UAt_nonempty s₀ L_T (k + 1)
  have hcard_U : (0 : ℝ) < (U.card : ℝ) := Nat.cast_pos.mpr hU.card_pos
  have hcard_U' : (0 : ℝ) < (U'.card : ℝ) := Nat.cast_pos.mpr hU'.card_pos
  unfold stepKernel
  split_ifs with hA
  · have hsub : U' ⊆ U := UAt_subset_of_branchA s₀ L_T k hA
    have hinner : ∀ x ∈ U,
        (∑ y : S, ((if x ∈ U' then PMF.pure x else PMF.uniformOfFinset U' hU') y).toReal * f y) =
          if x ∈ U' then f x else (U'.card : ℝ)⁻¹ * ∑ y ∈ U', f y := by
      intro x _
      split_ifs with hx'
      · exact sum_pmf_pure_mul x f
      · exact sum_pmf_ofFinset_mul U' hU' f
    rw [Finset.sum_congr rfl hinner]
    rw [← Finset.sum_sdiff hsub]
    have hs1 : (∑ x ∈ U \ U', (if x ∈ U' then f x else (U'.card : ℝ)⁻¹ * ∑ y ∈ U', f y)) =
        (((U.card : ℝ) - (U'.card : ℝ)) * ((U'.card : ℝ)⁻¹ * ∑ y ∈ U', f y)) := by
      have hcongr : ∀ x ∈ U \ U',
          (if x ∈ U' then f x else (U'.card : ℝ)⁻¹ * ∑ y ∈ U', f y) =
            (U'.card : ℝ)⁻¹ * ∑ y ∈ U', f y := by
        intro x hx
        rw [if_neg (Finset.mem_sdiff.mp hx).2]
      rw [Finset.sum_congr rfl hcongr, Finset.sum_const, nsmul_eq_mul,
          Finset.card_sdiff, Finset.inter_eq_left.mpr hsub,
          Nat.cast_sub (Finset.card_le_card hsub)]
    have hs2 : (∑ x ∈ U', (if x ∈ U' then f x else (U'.card : ℝ)⁻¹ * ∑ y ∈ U', f y)) =
        ∑ y ∈ U', f y := by
      refine Finset.sum_congr rfl fun x hx => if_pos hx
    rw [hs1, hs2]
    change (U.card : ℝ)⁻¹ *
      (((U.card : ℝ) - (U'.card : ℝ)) * ((U'.card : ℝ)⁻¹ * ∑ y ∈ U', f y) + ∑ y ∈ U', f y) =
      (U'.card : ℝ)⁻¹ * ∑ y ∈ U', f y
    have hne_U : (U.card : ℝ) ≠ 0 := ne_of_gt hcard_U
    have hne_U' : (U'.card : ℝ) ≠ 0 := ne_of_gt hcard_U'
    field_simp
    ring
  · have hinner : ∀ x ∈ U,
        (∑ y : S, (PMF.uniformOfFinset U' hU' y).toReal * f y) =
          (U'.card : ℝ)⁻¹ * ∑ y ∈ U', f y :=
      fun _ _ => sum_pmf_ofFinset_mul U' hU' f
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul,
        ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hcard_U), one_mul]

private noncomputable def probAt {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) (L_T : List (S → ℝ)) (k : ℕ) (σ : Fin (k + 1) → S) : ℝ :=
  if σ 0 = s₀ then
    ∏ i : Fin k, (stepKernel s₀ L_T i.val (σ i.castSucc) (σ i.succ)).toReal
  else 0

private lemma probAt_snocFun {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) (L_T : List (S → ℝ)) (k : ℕ) (τ : Fin (k + 1) → S) (y : S) :
    probAt s₀ L_T (k + 1) (snocFun τ y) =
      probAt s₀ L_T k τ * (stepKernel s₀ L_T k (τ (Fin.last k)) y).toReal := by
  unfold probAt
  have h0 : snocFun τ y 0 = τ 0 := by
    dsimp [snocFun]
  rw [h0]
  split_ifs with hτ0
  · rw [Fin.prod_univ_castSucc]
    congr 1
    · refine Finset.prod_congr rfl fun i _ => ?_
      have hcast : snocFun τ y i.castSucc.castSucc = τ i.castSucc := by
        dsimp [snocFun]
        rw [dif_pos (Nat.lt_succ_of_lt i.isLt)]
        rfl
      have hsucc : snocFun τ y i.castSucc.succ = τ i.succ := by
        dsimp [snocFun]
        rw [dif_pos (Nat.succ_lt_succ i.isLt)]
        rfl
      rw [Fin.val_castSucc, hcast, hsucc]
    · have hlast_cast : snocFun τ y (Fin.last k).castSucc = τ (Fin.last k) := by
        dsimp [snocFun, Fin.last]
        rw [dif_pos (Nat.lt_succ_self k)]
      have hlast_succ : snocFun τ y (Fin.last k).succ = y := by
        dsimp [snocFun, Fin.last]
        rw [dif_neg (Nat.lt_irrefl (k + 1))]
      rw [Fin.val_last, hlast_cast, hlast_succ]
  · ring

private lemma sum_probAt_mul_last {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) (L_T : List (S → ℝ)) (k : ℕ) (f : S → ℝ) :
    ∑ σ : Fin (k + 1) → S, probAt s₀ L_T k σ * f (σ (Fin.last k)) =
      ((UAt s₀ L_T k).card : ℝ)⁻¹ * ∑ x ∈ UAt s₀ L_T k, f x := by
  induction k generalizing f with
  | zero =>
    have hU0 : UAt s₀ L_T 0 = {s₀} := UAt_zero s₀ L_T
    rw [hU0, Finset.card_singleton, Nat.cast_one, inv_one, one_mul, Finset.sum_singleton]
    let e : S ≃ (Fin 1 → S) :=
      { toFun := fun s _ => s
        invFun := fun σ => σ 0
        left_inv := fun _ => rfl
        right_inv := fun σ => by ext i; rw [Fin.eq_zero i] }
    rw [← Equiv.sum_comp e]
    have h1 : ∀ s : S, probAt s₀ L_T 0 (e s) * f (e s (Fin.last 0)) =
        if s = s₀ then f s₀ else 0 := by
      intro s
      unfold probAt
      dsimp [e, Fin.last]
      split_ifs with hs
      · subst hs; simp
      · simp
    simp_rw [h1]
    simp
  | succ k ih =>
    rw [← Equiv.sum_comp (snocEquiv (k + 1)), Fintype.sum_prod_type]
    change ∑ τ : Fin (k + 1) → S, ∑ y : S,
        probAt s₀ L_T (k + 1) (snocFun τ y) * f (snocFun τ y (Fin.last (k + 1))) = _
    have hlast : ∀ (τ : Fin (k + 1) → S) (y : S),
        snocFun τ y (Fin.last (k + 1)) = y := by
      intro τ y
      dsimp [snocFun, Fin.last]
      rw [dif_neg (Nat.lt_irrefl (k + 1))]
    simp_rw [probAt_snocFun, hlast, mul_assoc, ← Finset.mul_sum]
    rw [ih (fun x => ∑ y : S, (stepKernel s₀ L_T k x y).toReal * f y)]
    exact stepKernel_stationary s₀ L_T k f

private lemma sum_probAt_eq_one {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) (L_T : List (S → ℝ)) (k : ℕ) :
    ∑ σ : Fin (k + 1) → S, probAt s₀ L_T k σ = 1 := by
  have h := sum_probAt_mul_last s₀ L_T k (fun _ => 1)
  simp only [mul_one, Finset.sum_const, nsmul_eq_mul] at h
  have hU : (0 : ℝ) < ((UAt s₀ L_T k).card : ℝ) :=
    Nat.cast_pos.mpr (UAt_nonempty s₀ L_T k).card_pos
  rw [h, inv_mul_cancel₀ (ne_of_gt hU)]

private noncomputable def costAt {S : Type} [DecidableEq S] (L_T : List (S → ℝ))
    (k : ℕ) (σ : Fin (k + 1) → S) : ℝ :=
  ∑ i : Fin k,
    (uniformD (σ i.castSucc) (σ i.succ) + max (L_T.getD i.val (fun _ => 0) (σ i.succ)) 0)

private noncomputable def expCostAt {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) (L_T : List (S → ℝ)) (k : ℕ) : ℝ :=
  ∑ σ : Fin (k + 1) → S, probAt s₀ L_T k σ * costAt L_T k σ

private noncomputable def stepExpCost {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) (L_T : List (S → ℝ)) (k : ℕ) : ℝ :=
  ((UAt s₀ L_T k).card : ℝ)⁻¹ *
    ∑ x ∈ UAt s₀ L_T k, ∑ y : S,
      (stepKernel s₀ L_T k x y).toReal *
        (uniformD x y + max (L_T.getD k (fun _ => 0) y) 0)

private lemma expCostAt_succ {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) (L_T : List (S → ℝ)) (k : ℕ) :
    expCostAt s₀ L_T (k + 1) = expCostAt s₀ L_T k + stepExpCost s₀ L_T k := by
  unfold expCostAt
  rw [← Equiv.sum_comp (snocEquiv (k + 1)), Fintype.sum_prod_type]
  change ∑ τ : Fin (k + 1) → S, ∑ y : S,
      probAt s₀ L_T (k + 1) (snocFun τ y) * costAt L_T (k + 1) (snocFun τ y) = _
  have hcost : ∀ (τ : Fin (k + 1) → S) (y : S),
      costAt L_T (k + 1) (snocFun τ y) =
        costAt L_T k τ +
          (uniformD (τ (Fin.last k)) y + max (L_T.getD k (fun _ => 0) y) 0) := by
    intro τ y
    unfold costAt
    rw [Fin.sum_univ_castSucc]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      have hcast : snocFun τ y i.castSucc.castSucc = τ i.castSucc := by
        dsimp [snocFun]
        rw [dif_pos (Nat.lt_succ_of_lt i.isLt)]
        rfl
      have hsucc : snocFun τ y i.castSucc.succ = τ i.succ := by
        dsimp [snocFun]
        rw [dif_pos (Nat.succ_lt_succ i.isLt)]
        rfl
      rw [Fin.val_castSucc, hcast, hsucc]
    · have hlast_cast : snocFun τ y (Fin.last k).castSucc = τ (Fin.last k) := by
        dsimp [snocFun, Fin.last]
        rw [dif_pos (Nat.lt_succ_self k)]
      have hlast_succ : snocFun τ y (Fin.last k).succ = y := by
        dsimp [snocFun, Fin.last]
        rw [dif_neg (Nat.lt_irrefl (k + 1))]
      rw [Fin.val_last, hlast_cast, hlast_succ]
  simp_rw [probAt_snocFun, hcost]
  have hinner : ∀ τ : Fin (k + 1) → S,
      (∑ y : S, (probAt s₀ L_T k τ * (stepKernel s₀ L_T k (τ (Fin.last k)) y).toReal) *
          (costAt L_T k τ +
            (uniformD (τ (Fin.last k)) y + max (L_T.getD k (fun _ => 0) y) 0))) =
        probAt s₀ L_T k τ * costAt L_T k τ +
          probAt s₀ L_T k τ *
            ∑ y : S, (stepKernel s₀ L_T k (τ (Fin.last k)) y).toReal *
              (uniformD (τ (Fin.last k)) y + max (L_T.getD k (fun _ => 0) y) 0) := by
    intro τ
    have hsplit : ∀ y : S,
        (probAt s₀ L_T k τ * (stepKernel s₀ L_T k (τ (Fin.last k)) y).toReal) *
          (costAt L_T k τ +
            (uniformD (τ (Fin.last k)) y + max (L_T.getD k (fun _ => 0) y) 0)) =
        (probAt s₀ L_T k τ * costAt L_T k τ) *
            (stepKernel s₀ L_T k (τ (Fin.last k)) y).toReal +
          probAt s₀ L_T k τ *
            ((stepKernel s₀ L_T k (τ (Fin.last k)) y).toReal *
              (uniformD (τ (Fin.last k)) y + max (L_T.getD k (fun _ => 0) y) 0)) := by
      intro y; ring
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hpmf : ∑ y : S, (stepKernel s₀ L_T k (τ (Fin.last k)) y).toReal = 1 := by
      let P := stepKernel s₀ L_T k (τ (Fin.last k))
      change ∑ y : S, (P y).toReal = 1
      rw [← ENNReal.toReal_sum (fun y _ => P.apply_ne_top y)]
      have htsum : ∑ y : S, P y = ∑' y : S, P y := (tsum_fintype (fun y => P y)).symm
      rw [htsum, P.tsum_coe, ENNReal.toReal_one]
    rw [hpmf, mul_one]
  simp_rw [hinner]
  rw [Finset.sum_add_distrib]
  congr 1
  exact sum_probAt_mul_last s₀ L_T k
    (fun x => ∑ y : S, (stepKernel s₀ L_T k x y).toReal *
      (uniformD x y + max (L_T.getD k (fun _ => 0) y) 0))

private noncomputable def phiAt {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) (L_T : List (S → ℝ)) (k : ℕ) : ℝ :=
  2 * (harmonic (UAt s₀ L_T k).card : ℝ) -
    ((UAt s₀ L_T k).card : ℝ)⁻¹ *
      ∑ x ∈ UAt s₀ L_T k, (WAt s₀ L_T k x - MAt s₀ L_T k)

private lemma avg_sub_le_card_sub_div {S : Type} [DecidableEq S]
    {U U' : Finset S} (hsub : U' ⊆ U) (hU : U.Nonempty) (hU' : U'.Nonempty)
    (g : S → ℝ) (hg0 : ∀ x ∈ U, 0 ≤ g x) (hg1 : ∀ x ∈ U, g x ≤ 1) :
    (U.card : ℝ)⁻¹ * (∑ x ∈ U, g x) - (U'.card : ℝ)⁻¹ * (∑ y ∈ U', g y) ≤
      ((U.card : ℝ) - (U'.card : ℝ)) / (U.card : ℝ) := by
  have hcard_U : (0 : ℝ) < (U.card : ℝ) := Nat.cast_pos.mpr hU.card_pos
  have hcard_U' : (0 : ℝ) < (U'.card : ℝ) := Nat.cast_pos.mpr hU'.card_pos
  have hle_card : (U'.card : ℝ) ≤ (U.card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hsub)
  have hsum_sdiff : ∑ x ∈ U, g x ≤ (∑ y ∈ U', g y) + ((U.card : ℝ) - (U'.card : ℝ)) := by
    rw [← Finset.sum_sdiff hsub]
    have hs : ∑ x ∈ U \ U', g x ≤ (U.card : ℝ) - (U'.card : ℝ) := by
      calc ∑ x ∈ U \ U', g x
          ≤ ∑ _x ∈ U \ U', (1 : ℝ) :=
            Finset.sum_le_sum fun x hx => hg1 x (Finset.mem_sdiff.mp hx).1
        _ = (U.card : ℝ) - (U'.card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one,
                Finset.card_sdiff, Finset.inter_eq_left.mpr hsub,
                Nat.cast_sub (Finset.card_le_card hsub)]
    linarith
  have hdiv : (U.card : ℝ)⁻¹ * ∑ x ∈ U, g x ≤
      (U.card : ℝ)⁻¹ * (∑ y ∈ U', g y) + ((U.card : ℝ) - (U'.card : ℝ)) / (U.card : ℝ) := by
    calc (U.card : ℝ)⁻¹ * ∑ x ∈ U, g x
        ≤ (U.card : ℝ)⁻¹ * ((∑ y ∈ U', g y) + ((U.card : ℝ) - (U'.card : ℝ))) :=
          mul_le_mul_of_nonneg_left hsum_sdiff (inv_nonneg.mpr (le_of_lt hcard_U))
      _ = (U.card : ℝ)⁻¹ * (∑ y ∈ U', g y) + ((U.card : ℝ) - (U'.card : ℝ)) / (U.card : ℝ) := by
          ring
  have hsum_U'_nonneg : 0 ≤ ∑ y ∈ U', g y :=
    Finset.sum_nonneg fun y hy => hg0 y (hsub hy)
  have hinv_le : (U.card : ℝ)⁻¹ ≤ (U'.card : ℝ)⁻¹ :=
    inv_anti₀ hcard_U' hle_card
  have hmul_le : (U.card : ℝ)⁻¹ * ∑ y ∈ U', g y ≤ (U'.card : ℝ)⁻¹ * ∑ y ∈ U', g y :=
    mul_le_mul_of_nonneg_right hinv_le hsum_U'_nonneg
  linarith

private lemma step_potential_bound {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) (L_T : List (S → ℝ)) (k : ℕ) :
    stepExpCost s₀ L_T k + phiAt s₀ L_T (k + 1) - phiAt s₀ L_T k ≤
      2 * (harmonic (Fintype.card S) : ℝ) * (MAt s₀ L_T (k + 1) - MAt s₀ L_T k) := by
  let U := UAt s₀ L_T k
  let U' := UAt s₀ L_T (k + 1)
  have hU : U.Nonempty := UAt_nonempty s₀ L_T k
  have hU' : U'.Nonempty := UAt_nonempty s₀ L_T (k + 1)
  have hcard_U : (0 : ℝ) < (U.card : ℝ) := Nat.cast_pos.mpr hU.card_pos
  have hcard_U' : (0 : ℝ) < (U'.card : ℝ) := Nat.cast_pos.mpr hU'.card_pos
  have hsplit_step : stepExpCost s₀ L_T k =
      ((U.card : ℝ)⁻¹ * ∑ x ∈ U, ∑ y : S, (stepKernel s₀ L_T k x y).toReal * uniformD x y) +
        ((U'.card : ℝ)⁻¹ * ∑ y ∈ U', max (L_T.getD k (fun _ => 0) y) 0) := by
    unfold stepExpCost
    have h1 : ∀ x ∈ U,
        (∑ y : S, (stepKernel s₀ L_T k x y).toReal *
            (uniformD x y + max (L_T.getD k (fun _ => 0) y) 0)) =
          (∑ y : S, (stepKernel s₀ L_T k x y).toReal * uniformD x y) +
            (∑ y : S, (stepKernel s₀ L_T k x y).toReal * max (L_T.getD k (fun _ => 0) y) 0) := by
      intro x _
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun y _ => by ring
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, mul_add]
    congr 1
    exact stepKernel_stationary s₀ L_T k (fun y => max (L_T.getD k (fun _ => 0) y) 0)
  have htask_eq : ∀ y ∈ U',
      max (L_T.getD k (fun _ => 0) y) 0 = WAt s₀ L_T (k + 1) y - WAt s₀ L_T k y := by
    intro y hy
    have hy_lt : WAt s₀ L_T (k + 1) y < MAt s₀ L_T (k + 1) + 1 := (Finset.mem_filter.mp hy).2
    have hM_le : MAt s₀ L_T (k + 1) ≤ μAt s₀ L_T (k + 1) := (MAt_bounds s₀ L_T (k + 1)).1
    have h_eq := WAt_succ_eq_add_of_lt s₀ L_T k (s := y) (by linarith)
    linarith
  have htask_sum : (U'.card : ℝ)⁻¹ * ∑ y ∈ U', max (L_T.getD k (fun _ => 0) y) 0 =
      ((U'.card : ℝ)⁻¹ * ∑ y ∈ U', (WAt s₀ L_T (k + 1) y - MAt s₀ L_T (k + 1))) +
        (MAt s₀ L_T (k + 1) - MAt s₀ L_T k) -
        ((U'.card : ℝ)⁻¹ * ∑ y ∈ U', (WAt s₀ L_T k y - MAt s₀ L_T k)) := by
    rw [Finset.sum_congr rfl htask_eq]
    have h2 : ∀ y ∈ U',
        WAt s₀ L_T (k + 1) y - WAt s₀ L_T k y =
          ((WAt s₀ L_T (k + 1) y - MAt s₀ L_T (k + 1)) + (MAt s₀ L_T (k + 1) - MAt s₀ L_T k)) -
            (WAt s₀ L_T k y - MAt s₀ L_T k) := by
      intro y _; ring
    rw [Finset.sum_congr rfl h2, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        Finset.sum_const, nsmul_eq_mul]
    have hne : (U'.card : ℝ) ≠ 0 := ne_of_gt hcard_U'
    field_simp
  rw [hsplit_step, htask_sum]
  unfold phiAt
  change (((U.card : ℝ)⁻¹ * ∑ x ∈ U, ∑ y : S, (stepKernel s₀ L_T k x y).toReal * uniformD x y) +
      (((U'.card : ℝ)⁻¹ * ∑ y ∈ U', (WAt s₀ L_T (k + 1) y - MAt s₀ L_T (k + 1))) +
        (MAt s₀ L_T (k + 1) - MAt s₀ L_T k) -
        ((U'.card : ℝ)⁻¹ * ∑ y ∈ U', (WAt s₀ L_T k y - MAt s₀ L_T k)))) +
      (2 * (harmonic U'.card : ℝ) -
        (U'.card : ℝ)⁻¹ * ∑ y ∈ U', (WAt s₀ L_T (k + 1) y - MAt s₀ L_T (k + 1))) -
      (2 * (harmonic U.card : ℝ) -
        (U.card : ℝ)⁻¹ * ∑ x ∈ U, (WAt s₀ L_T k x - MAt s₀ L_T k)) ≤
    2 * (harmonic (Fintype.card S) : ℝ) * (MAt s₀ L_T (k + 1) - MAt s₀ L_T k)
  by_cases hA : μAt s₀ L_T (k + 1) < MAt s₀ L_T k + 1
  · have hM_eq : MAt s₀ L_T (k + 1) = MAt s₀ L_T k := by
      rw [MAt_succ_eq, if_pos hA]
    have hsub : U' ⊆ U := UAt_subset_of_branchA s₀ L_T k hA
    have htrans : (U.card : ℝ)⁻¹ *
        (∑ x ∈ U, ∑ y : S, (stepKernel s₀ L_T k x y).toReal * uniformD x y) ≤
        ((U.card : ℝ) - (U'.card : ℝ)) / (U.card : ℝ) := by
      have hinner : ∀ x ∈ U,
          (∑ y : S, (stepKernel s₀ L_T k x y).toReal * uniformD x y) ≤
            if x ∈ U' then 0 else 1 := by
        intro x _
        unfold stepKernel
        rw [if_pos hA]
        split_ifs with hx'
        · rw [sum_pmf_pure_mul, uniformD_self]
        · rw [sum_pmf_ofFinset_mul]
          calc (U'.card : ℝ)⁻¹ * ∑ y ∈ U', uniformD x y
              ≤ (U'.card : ℝ)⁻¹ * ∑ _y ∈ U', (1 : ℝ) :=
                mul_le_mul_of_nonneg_left
                  (Finset.sum_le_sum fun y _ => uniformD_le_one x y)
                  (inv_nonneg.mpr (le_of_lt hcard_U'))
            _ = 1 := by
                rw [Finset.sum_const, nsmul_eq_mul, mul_one,
                    inv_mul_cancel₀ (ne_of_gt hcard_U')]
      calc (U.card : ℝ)⁻¹ * ∑ x ∈ U, ∑ y : S, (stepKernel s₀ L_T k x y).toReal * uniformD x y
          ≤ (U.card : ℝ)⁻¹ * ∑ x ∈ U, (if x ∈ U' then (0 : ℝ) else 1) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum hinner)
              (inv_nonneg.mpr (le_of_lt hcard_U))
        _ = ((U.card : ℝ) - (U'.card : ℝ)) / (U.card : ℝ) := by
            rw [← Finset.sum_sdiff hsub]
            have hs1 : (∑ x ∈ U \ U', (if x ∈ U' then (0 : ℝ) else 1)) =
                (U.card : ℝ) - (U'.card : ℝ) := by
              have hc : ∀ x ∈ U \ U', (if x ∈ U' then (0 : ℝ) else 1) = 1 :=
                fun x hx => if_neg (Finset.mem_sdiff.mp hx).2
              rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul, mul_one,
                  Finset.card_sdiff, Finset.inter_eq_left.mpr hsub,
                  Nat.cast_sub (Finset.card_le_card hsub)]
            have hs2 : (∑ x ∈ U', (if x ∈ U' then (0 : ℝ) else 1)) = 0 := by
              have hc : ∀ x ∈ U', (if x ∈ U' then (0 : ℝ) else 1) = 0 :=
                fun x hx => if_pos hx
              rw [Finset.sum_congr rfl hc, Finset.sum_const_zero]
            rw [hs1, hs2, add_zero, div_eq_inv_mul]
    have havg := avg_sub_le_card_sub_div hsub hU hU'
      (fun x => WAt s₀ L_T k x - MAt s₀ L_T k)
      (fun x hx => (WAt_sub_MAt_bounds s₀ L_T k hx).1)
      (fun x hx => (WAt_sub_MAt_bounds s₀ L_T k hx).2)
    have hharm := sub_div_le_harmonic_sub hU'.card_pos (Finset.card_le_card hsub)
    rw [hM_eq]
    linarith
  · have hM_eq : MAt s₀ L_T (k + 1) = μAt s₀ L_T (k + 1) := by
      rw [MAt_succ_eq, if_neg hA]
    have hM_diff : 1 ≤ MAt s₀ L_T (k + 1) - MAt s₀ L_T k := by
      rw [hM_eq]; linarith
    have htrans_le_one : (U.card : ℝ)⁻¹ *
        (∑ x ∈ U, ∑ y : S, (stepKernel s₀ L_T k x y).toReal * uniformD x y) ≤ 1 := by
      have hinner : ∀ x ∈ U,
          (∑ y : S, (stepKernel s₀ L_T k x y).toReal * uniformD x y) ≤ 1 := by
        intro x _
        unfold stepKernel
        rw [if_neg hA, sum_pmf_ofFinset_mul]
        calc (U'.card : ℝ)⁻¹ * ∑ y ∈ U', uniformD x y
            ≤ (U'.card : ℝ)⁻¹ * ∑ _y ∈ U', (1 : ℝ) :=
              mul_le_mul_of_nonneg_left
                (Finset.sum_le_sum fun y _ => uniformD_le_one x y)
                (inv_nonneg.mpr (le_of_lt hcard_U'))
          _ = 1 := by
              rw [Finset.sum_const, nsmul_eq_mul, mul_one,
                  inv_mul_cancel₀ (ne_of_gt hcard_U')]
      calc (U.card : ℝ)⁻¹ * ∑ x ∈ U, ∑ y : S, (stepKernel s₀ L_T k x y).toReal * uniformD x y
          ≤ (U.card : ℝ)⁻¹ * ∑ _x ∈ U, (1 : ℝ) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum hinner)
              (inv_nonneg.mpr (le_of_lt hcard_U))
        _ = 1 := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one,
                inv_mul_cancel₀ (ne_of_gt hcard_U)]
    have hdelta_harm :
        1 + ((U.card : ℝ)⁻¹ * ∑ x ∈ U, (WAt s₀ L_T k x - MAt s₀ L_T k) -
              (U'.card : ℝ)⁻¹ * ∑ y ∈ U', (WAt s₀ L_T k y - MAt s₀ L_T k)) -
            2 * (harmonic U.card : ℝ) ≤ -1 := by
      by_cases hcard1 : U.card = 1
      · obtain ⟨x₀, hx₀⟩ := Finset.card_eq_one.mp hcard1
        have hx₀_mem : x₀ ∈ U := by rw [hx₀]; exact Finset.mem_singleton_self x₀
        have hx₀_le_one : WAt s₀ L_T k x₀ - MAt s₀ L_T k ≤ 1 :=
          (WAt_sub_MAt_bounds s₀ L_T k hx₀_mem).2
        have hy_ge : ∀ y ∈ U', WAt s₀ L_T k x₀ - MAt s₀ L_T k ≤ WAt s₀ L_T k y - MAt s₀ L_T k := by
          intro y _
          by_cases hyx : y = x₀
          · subst hyx; exact le_refl _
          · have hy_not : y ∉ U := by rw [hx₀, Finset.mem_singleton]; exact hyx
            have hy_ge_one : MAt s₀ L_T k + 1 ≤ WAt s₀ L_T k y := by
              by_contra hlt
              push Not at hlt
              exact hy_not (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hlt⟩)
            linarith
        have havg_U' : WAt s₀ L_T k x₀ - MAt s₀ L_T k ≤
            (U'.card : ℝ)⁻¹ * ∑ y ∈ U', (WAt s₀ L_T k y - MAt s₀ L_T k) := by
          calc WAt s₀ L_T k x₀ - MAt s₀ L_T k
              = (U'.card : ℝ)⁻¹ * ∑ _y ∈ U', (WAt s₀ L_T k x₀ - MAt s₀ L_T k) := by
                rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
                    inv_mul_cancel₀ (ne_of_gt hcard_U'), one_mul]
            _ ≤ (U'.card : ℝ)⁻¹ * ∑ y ∈ U', (WAt s₀ L_T k y - MAt s₀ L_T k) :=
                mul_le_mul_of_nonneg_left (Finset.sum_le_sum hy_ge)
                  (inv_nonneg.mpr (le_of_lt hcard_U'))
        have havg_U : (U.card : ℝ)⁻¹ * ∑ x ∈ U, (WAt s₀ L_T k x - MAt s₀ L_T k) =
            WAt s₀ L_T k x₀ - MAt s₀ L_T k := by
          rw [hx₀, Finset.card_singleton, Nat.cast_one, inv_one, one_mul, Finset.sum_singleton]
        have hH1 : (harmonic U.card : ℝ) = 1 := by rw [hcard1, harmonic_one_real]
        linarith
      · have hcard2 : 2 ≤ U.card := by
          have := hU.card_pos
          omega
        have hH2 : (3 / 2 : ℝ) ≤ (harmonic U.card : ℝ) := three_halves_le_harmonic_real hcard2
        have havg_U_le : (U.card : ℝ)⁻¹ * ∑ x ∈ U, (WAt s₀ L_T k x - MAt s₀ L_T k) ≤ 1 := by
          calc (U.card : ℝ)⁻¹ * ∑ x ∈ U, (WAt s₀ L_T k x - MAt s₀ L_T k)
              ≤ (U.card : ℝ)⁻¹ * ∑ _x ∈ U, (1 : ℝ) :=
                mul_le_mul_of_nonneg_left
                  (Finset.sum_le_sum fun x hx => (WAt_sub_MAt_bounds s₀ L_T k hx).2)
                  (inv_nonneg.mpr (le_of_lt hcard_U))
            _ = 1 := by
                rw [Finset.sum_const, nsmul_eq_mul, mul_one,
                    inv_mul_cancel₀ (ne_of_gt hcard_U)]
        have havg_U'_nonneg : 0 ≤ (U'.card : ℝ)⁻¹ * ∑ y ∈ U', (WAt s₀ L_T k y - MAt s₀ L_T k) := by
          refine mul_nonneg (inv_nonneg.mpr (le_of_lt hcard_U')) (Finset.sum_nonneg fun y _ => ?_)
          have h1 := (MAt_bounds s₀ L_T k).1
          have h2 := μAt_le_WAt s₀ L_T k y
          linarith
        linarith
    have hH_U' : (harmonic U'.card : ℝ) ≤ (harmonic (Fintype.card S) : ℝ) :=
      harmonic_mono_real (Finset.card_le_univ U')
    have hH_S_ge_one : (1 : ℝ) ≤ (harmonic (Fintype.card S) : ℝ) :=
      one_le_harmonic_real (@Fintype.card_pos S _ _)
    have hprod : (2 * (harmonic (Fintype.card S) : ℝ) - 1) *
        (MAt s₀ L_T (k + 1) - MAt s₀ L_T k - 1) ≥ 0 :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith

private lemma expCostAt_le_two_harmonic_mul_MAt {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) (L_T : List (S → ℝ)) (k : ℕ) :
    expCostAt s₀ L_T k + phiAt s₀ L_T k - phiAt s₀ L_T 0 ≤
      2 * (harmonic (Fintype.card S) : ℝ) * MAt s₀ L_T k := by
  induction k with
  | zero =>
    have hexp0 : expCostAt s₀ L_T 0 = 0 := by
      unfold expCostAt costAt
      simp
    have hM0 : MAt s₀ L_T 0 = 0 := rfl
    rw [hexp0, hM0]
    linarith
  | succ k ih =>
    rw [expCostAt_succ]
    have hstep := step_potential_bound s₀ L_T k
    linarith

private lemma phiAt_zero {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) (L_T : List (S → ℝ)) :
    phiAt s₀ L_T 0 = 2 := by
  unfold phiAt
  rw [UAt_zero, Finset.card_singleton, harmonic_one_real, Nat.cast_one, inv_one, one_mul,
      Finset.sum_singleton]
  change 2 * (1 : ℝ) - (uniformD s₀ s₀ - 0) = 2
  rw [uniformD_self]
  ring

private lemma phiAt_ge_one {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) (L_T : List (S → ℝ)) (k : ℕ) :
    1 ≤ phiAt s₀ L_T k := by
  unfold phiAt
  have hU := UAt_nonempty s₀ L_T k
  have hcard_U : (0 : ℝ) < ((UAt s₀ L_T k).card : ℝ) := Nat.cast_pos.mpr hU.card_pos
  have hH : (1 : ℝ) ≤ (harmonic (UAt s₀ L_T k).card : ℝ) :=
    one_le_harmonic_real hU.card_pos
  have havg : ((UAt s₀ L_T k).card : ℝ)⁻¹ *
      ∑ x ∈ UAt s₀ L_T k, (WAt s₀ L_T k x - MAt s₀ L_T k) ≤ 1 := by
    calc ((UAt s₀ L_T k).card : ℝ)⁻¹ *
          ∑ x ∈ UAt s₀ L_T k, (WAt s₀ L_T k x - MAt s₀ L_T k)
        ≤ ((UAt s₀ L_T k).card : ℝ)⁻¹ * ∑ _x ∈ UAt s₀ L_T k, (1 : ℝ) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun x hx => (WAt_sub_MAt_bounds s₀ L_T k hx).2)
            (inv_nonneg.mpr (le_of_lt hcard_U))
      _ = 1 := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one,
              inv_mul_cancel₀ (ne_of_gt hcard_U)]
  linarith

private lemma WAt_le_prefix_schedCost {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) {m : ℕ} (T : Fin m → S → ℝ) (σ : Fin (m + 1) → S) (h0 : σ 0 = s₀)
    (k : ℕ) (hk : k ≤ m) (s : S) :
    WAt s₀ (List.ofFn T) k s ≤
      (∑ i : Fin k,
        (uniformD (σ ⟨i.val, by omega⟩) (σ ⟨i.val + 1, by omega⟩) +
          max (T ⟨i.val, by omega⟩ (σ ⟨i.val + 1, by omega⟩)) 0)) +
        uniformD (σ ⟨k, by omega⟩) s := by
  induction k generalizing s with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_add]
    have hσ0 : σ ⟨0, by omega⟩ = s₀ := h0
    rw [hσ0]
    rfl
  | succ k ih =>
    have hk_lt : k < m := Nat.lt_of_succ_le hk
    have hget : (List.ofFn T).getD k (fun _ => 0) = T ⟨k, hk_lt⟩ := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hk_lt]
      rfl
    have hnext : WAt s₀ (List.ofFn T) (k + 1) s ≤
        WAt s₀ (List.ofFn T) k (σ ⟨k + 1, by omega⟩) +
          max (T ⟨k, hk_lt⟩ (σ ⟨k + 1, by omega⟩)) 0 +
          uniformD (σ ⟨k + 1, by omega⟩) s := by
      rw [WAt_succ_eq, hget]
      unfold nextW
      exact Finset.inf'_le _ (Finset.mem_univ (σ ⟨k + 1, by omega⟩))
    have hih := ih (Nat.le_of_succ_le hk) (σ ⟨k + 1, by omega⟩)
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    linarith

private lemma MAt_le_offlineOpt {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) {m : ℕ} (T : Fin m → S → ℝ) (hT : ∀ i s, 0 ≤ T i s) :
    MAt s₀ (List.ofFn T) m ≤ offlineOpt (uniformD (S := S)) s₀ T := by
  refine le_trans (MAt_bounds s₀ (List.ofFn T) m).1 ?_
  unfold offlineOpt
  refine Finset.le_inf' _ _ fun σ hσ => ?_
  have h0 : σ 0 = s₀ := (Finset.mem_filter.mp hσ).2
  have h1 := μAt_le_WAt s₀ (List.ofFn T) m (σ ⟨m, Nat.lt_succ_self m⟩)
  have h2 := WAt_le_prefix_schedCost s₀ T σ h0 m (le_refl m) (σ ⟨m, Nat.lt_succ_self m⟩)
  rw [uniformD_self, add_zero] at h2
  have hcost_eq : (∑ i : Fin m,
      (uniformD (σ ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) (σ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) +
        max (T ⟨i.val, i.isLt⟩ (σ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)) 0)) =
      schedCost (uniformD (S := S)) T σ := by
    unfold schedCost
    refine Finset.sum_congr rfl fun i _ => ?_
    have hmax : max (T i (σ i.succ)) 0 = T i (σ i.succ) := max_eq_left (hT i (σ i.succ))
    exact congrArg (fun v => uniformD (σ i.castSucc) (σ i.succ) + v) hmax
  linarith

private lemma pmf_ofFinset_congr {S : Type} [Fintype S] [DecidableEq S]
    {U₁ U₂ : Finset S} (h : U₁ = U₂) (h₁ : U₁.Nonempty) (h₂ : U₂.Nonempty) :
    PMF.uniformOfFinset U₁ h₁ = PMF.uniformOfFinset U₂ h₂ := by
  subst h
  rfl

private lemma stepKernel_take_ofFn {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) {m : ℕ} (T : Fin m → S → ℝ) (i : Fin m) (x : S) :
    stepKernel s₀ ((List.ofFn T).take (i.val + 1)) i.val x =
      stepKernel s₀ (List.ofFn T) i.val x := by
  have hμ : μAt s₀ ((List.ofFn T).take (i.val + 1)) (i.val + 1) =
      μAt s₀ (List.ofFn T) (i.val + 1) := by
    unfold μAt WAt
    rw [wfAt_take s₀ (List.ofFn T) (i.val + 1) (i.val + 1) (le_refl _)]
  have hM : MAt s₀ ((List.ofFn T).take (i.val + 1)) i.val =
      MAt s₀ (List.ofFn T) i.val := by
    unfold MAt
    rw [wfAt_take s₀ (List.ofFn T) i.val (i.val + 1) (Nat.le_succ i.val)]
  have hU : UAt s₀ ((List.ofFn T).take (i.val + 1)) (i.val + 1) =
      UAt s₀ (List.ofFn T) (i.val + 1) := by
    unfold UAt WAt MAt
    rw [wfAt_take s₀ (List.ofFn T) (i.val + 1) (i.val + 1) (le_refl _)]
  have hpmf : PMF.uniformOfFinset (UAt s₀ ((List.ofFn T).take (i.val + 1)) (i.val + 1))
      (UAt_nonempty s₀ ((List.ofFn T).take (i.val + 1)) (i.val + 1)) =
      PMF.uniformOfFinset (UAt s₀ (List.ofFn T) (i.val + 1))
      (UAt_nonempty s₀ (List.ofFn T) (i.val + 1)) :=
    pmf_ofFinset_congr hU _ _
  unfold stepKernel
  rw [hpmf, hμ, hM, hU]

private lemma schedProb_eq_probAt {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) {m : ℕ} (T : Fin m → S → ℝ) (σ : Fin (m + 1) → S) :
    schedProb algR s₀ T σ = probAt s₀ (List.ofFn T) m σ := by
  unfold schedProb probAt
  split_ifs with h0
  · refine Finset.prod_congr rfl fun i _ => ?_
    dsimp only [algR]
    have hlen : ((List.ofFn T).take (i.val + 1)).length - 1 = i.val := by
      rw [List.length_take, List.length_ofFn, Nat.min_eq_left i.isLt]
      omega
    have hget_S : ((List.ofFn σ).take (i.val + 1)).getD i.val s₀ = σ i.castSucc := by
      have hi_lt : i.val < i.val + 1 := Nat.lt_succ_self i.val
      have hi_m : i.val < m + 1 := Nat.lt_succ_of_lt i.isLt
      rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi_lt,
          List.getElem?_ofFn, dif_pos hi_m]
      rfl
    rw [hlen, hget_S, stepKernel_take_ofFn]
  · rfl

private lemma expCost_eq_expCostAt {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) {m : ℕ} (T : Fin m → S → ℝ) (hT : ∀ i s, 0 ≤ T i s) :
    expCost (uniformD (S := S)) algR s₀ T = expCostAt s₀ (List.ofFn T) m := by
  unfold expCost expCostAt
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [schedProb_eq_probAt]
  congr 1
  unfold schedCost costAt
  refine Finset.sum_congr rfl fun i _ => ?_
  have hget : (List.ofFn T).getD i.val (fun _ => 0) = T i := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos i.isLt]
    rfl
  rw [hget, max_eq_left (hT i (σ i.succ))]

theorem solution {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] :
    ∃ R : RandomizedOnlineAlgorithm S,
      IsExpCompetitive (uniformD (S := S)) R (2 * (harmonic (Fintype.card S) : ℝ)) := by
  refine ⟨algR, ?_, 1, fun s₀ m T hT => ?_⟩
  · have hH : (1 : ℝ) ≤ (harmonic (Fintype.card S) : ℝ) :=
      one_le_harmonic_real (@Fintype.card_pos S _ _)
    linarith
  · rw [expCost_eq_expCostAt s₀ T hT]
    have hbound := expCostAt_le_two_harmonic_mul_MAt s₀ (List.ofFn T) m
    have hphi0 := phiAt_zero s₀ (List.ofFn T)
    have hphim := phiAt_ge_one s₀ (List.ofFn T) m
    have hM_le := MAt_le_offlineOpt s₀ T hT
    have hH_pos : (0 : ℝ) ≤ 2 * (harmonic (Fintype.card S) : ℝ) := by
      have := one_le_harmonic_real (@Fintype.card_pos S _ _)
      linarith
    have hmul : 2 * (harmonic (Fintype.card S) : ℝ) * MAt s₀ (List.ofFn T) m ≤
        2 * (harmonic (Fintype.card S) : ℝ) * offlineOpt (uniformD (S := S)) s₀ T :=
      mul_le_mul_of_nonneg_left hM_le hH_pos
    linarith
