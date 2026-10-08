-- Prove2me | solution 1 for GilmoreGomoryTSP.MinCost.eq_28_tree_le_costStar
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:48:03.103927+00:00
-- url     : https://prove2.me/submissions/d77e518a-0dff-4d56-b56d-a921fbc26698

import Mathlib
import Definitions.Def_GilmoreGomoryTSP_MinCost_Model
import Definitions.Def_GilmoreGomoryTSP_MinCost_Underestimate



namespace GilmoreGomoryTSP.MinCost

open MeasureTheory

variable {n : ℕ}

lemma cnt_int_ind (f : ℝ → ℝ) (hf : LocallyIntegrable f) (a b : ℝ) :
    Integrable ((Set.Ico a b).indicator f) :=
  (integrable_indicator_iff measurableSet_Ico).mpr
    ((hf.integrableOn_isCompact isCompact_Icc).mono_set Set.Ico_subset_Icc_self)

lemma cnt_ico (f : ℝ → ℝ) (hf : LocallyIntegrable f) (a b : ℝ) (h : a ≤ b) :
    ∫ x, (Set.Ico a b).indicator f x = ∫ x in a..b, f x := by
  rw [integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioo,
    ← integral_Ioc_eq_integral_Ioo, intervalIntegral.integral_of_le h]

/-- the integrand of the cost of one changeover -/
noncomputable def cntT (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (i j : Fin (n + 1)) (x : ℝ) : ℝ :=
  (Set.Ico (B i) (A j)).indicator f x + (Set.Ico (A j) (B i)).indicator g x

lemma cnt_T_int (f g : ℝ → ℝ) (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    (A B : Fin (n + 1) → ℝ) (i j : Fin (n + 1)) : Integrable (cntT f g A B i j) :=
  (cnt_int_ind f hf _ _).add (cnt_int_ind g hg _ _)

lemma cnt_c (f g : ℝ → ℝ) (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    (A B : Fin (n + 1) → ℝ) (i j : Fin (n + 1)) :
    c f g A B i j = ∫ x, cntT f g A B i j x := by
  unfold cntT
  rw [integral_add (cnt_int_ind f hf _ _) (cnt_int_ind g hg _ _)]
  unfold c
  split_ifs with h
  · have : Set.Ico (A j) (B i) = ∅ := Set.Ico_eq_empty (not_lt.mpr h)
    rw [this, cnt_ico f hf _ _ h]
    simp
  · have h' : A j ≤ B i := (not_le.mp h).le
    have : Set.Ico (B i) (A j) = ∅ := Set.Ico_eq_empty (not_lt.mpr h')
    rw [this, cnt_ico g hg _ _ h']
    simp

noncomputable def cntW (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (ψ : Equiv.Perm (Fin (n + 1)))
    (x : ℝ) : ℝ := ∑ i, cntT f g A B i (ψ i) x

lemma cnt_W_int (f g : ℝ → ℝ) (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    (A B : Fin (n + 1) → ℝ) (ψ : Equiv.Perm (Fin (n + 1))) : Integrable (cntW f g A B ψ) := by
  unfold cntW
  exact integrable_finsetSum _ (fun i _ => cnt_T_int f g hf hg A B i (ψ i))

lemma cnt_cost (f g : ℝ → ℝ) (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    (A B : Fin (n + 1) → ℝ) (ψ : Equiv.Perm (Fin (n + 1))) :
    cost f g A B ψ = ∫ x, cntW f g A B ψ x := by
  unfold cost cntW
  rw [integral_finsetSum _ (fun i _ => cnt_T_int f g hf hg A B i (ψ i))]
  exact Finset.sum_congr rfl (fun i _ => cnt_c f g hf hg A B i (ψ i))

/-- counts -/
noncomputable def cntNf (A B : Fin (n + 1) → ℝ) (ψ : Equiv.Perm (Fin (n + 1))) (x : ℝ) : ℝ :=
  ∑ i, if B i ≤ x ∧ x < A (ψ i) then (1:ℝ) else 0

noncomputable def cntNg (A B : Fin (n + 1) → ℝ) (ψ : Equiv.Perm (Fin (n + 1))) (x : ℝ) : ℝ :=
  ∑ i, if A (ψ i) ≤ x ∧ x < B i then (1:ℝ) else 0

noncomputable def cntD (A B : Fin (n + 1) → ℝ) (x : ℝ) : ℝ :=
  (∑ i, if B i ≤ x then (1:ℝ) else 0) - ∑ i, if A i ≤ x then (1:ℝ) else 0

lemma cntNf_nonneg (A B : Fin (n + 1) → ℝ) (ψ : Equiv.Perm (Fin (n + 1))) (x : ℝ) :
    0 ≤ cntNf A B ψ x :=
  Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)

lemma cntNg_nonneg (A B : Fin (n + 1) → ℝ) (ψ : Equiv.Perm (Fin (n + 1))) (x : ℝ) :
    0 ≤ cntNg A B ψ x :=
  Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)

lemma cnt_W_eq (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (ψ : Equiv.Perm (Fin (n + 1))) (x : ℝ) :
    cntW f g A B ψ x = cntNf A B ψ x * f x + cntNg A B ψ x * g x := by
  unfold cntW cntNf cntNg cntT
  rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Set.indicator_apply, Set.mem_Ico]
  split_ifs <;> simp

lemma cnt_diff (A B : Fin (n + 1) → ℝ) (ψ : Equiv.Perm (Fin (n + 1))) (x : ℝ) :
    cntNf A B ψ x - cntNg A B ψ x = cntD A B x := by
  unfold cntNf cntNg cntD
  rw [← Finset.sum_sub_distrib]
  have h2 : ∑ i, (if A (ψ i) ≤ x then (1:ℝ) else 0) = ∑ i, if A i ≤ x then (1:ℝ) else 0 :=
    Equiv.sum_comp ψ (fun j => if A j ≤ x then (1:ℝ) else 0)
  rw [← h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  generalize B i = b
  generalize A (ψ i) = a
  rcases le_or_gt b x with hb | hb <;> rcases le_or_gt a x with ha | ha <;>
    simp [hb, ha, not_lt_of_ge, not_le_of_gt, le_of_lt]

lemma cnt_sorted (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : Monotone (A ∘ φ)) (x : ℝ) :
    cntNf A B φ x = 0 ∨ cntNg A B φ x = 0 := by
  by_contra hcon
  push Not at hcon
  have h1 : ∃ i, B i ≤ x ∧ x < A (φ i) := by
    by_contra hh
    push Not at hh
    apply hcon.1
    exact Finset.sum_eq_zero (fun i _ => by
      rw [if_neg]; intro h; exact absurd h.2 (not_lt.mpr (hh i h.1)))
  have h2 : ∃ j, A (φ j) ≤ x ∧ x < B j := by
    by_contra hh
    push Not at hh
    apply hcon.2
    exact Finset.sum_eq_zero (fun i _ => by
      rw [if_neg]; intro h; exact absurd h.2 (not_lt.mpr (hh i h.1)))
  obtain ⟨i, hi1, hi2⟩ := h1
  obtain ⟨j, hj1, hj2⟩ := h2
  have hij : i < j := by
    by_contra h; push Not at h
    have := hB h; linarith
  have hji : j < i := by
    by_contra h; push Not at h
    have := hφ h; simp only [Function.comp] at this; linarith
  exact lt_asymm hij hji

lemma cnt_Ng_le (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : Monotone (A ∘ φ)) (ψ : Equiv.Perm (Fin (n + 1)))
    (x : ℝ) : cntNg A B φ x ≤ cntNg A B ψ x := by
  have h1 := cnt_diff A B φ x
  have h2 := cnt_diff A B ψ x
  have := cnt_sorted A B hB φ hφ x
  have := cntNf_nonneg A B ψ x
  have := cntNg_nonneg A B ψ x
  have := cntNf_nonneg A B φ x
  have := cntNg_nonneg A B φ x
  rcases cnt_sorted A B hB φ hφ x with h | h <;> linarith

lemma cnt_W_sub (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (ψ φ : Equiv.Perm (Fin (n + 1))) (x : ℝ) :
    cntW f g A B ψ x - cntW f g A B φ x =
      (cntNg A B ψ x - cntNg A B φ x) * (f x + g x) := by
  rw [cnt_W_eq, cnt_W_eq]
  have h1 := cnt_diff A B φ x
  have h2 := cnt_diff A B ψ x
  have e1 : cntNf A B ψ x = cntNg A B ψ x + cntD A B x := by linarith
  have e2 : cntNf A B φ x = cntNg A B φ x + cntD A B x := by linarith
  rw [e1, e2]; ring


lemma st_meas_P (A B : Fin (n + 1) → ℝ) (φ : Equiv.Perm (Fin (n + 1))) :
    MeasurableSet (P A B φ) := by
  unfold P Pq
  exact MeasurableSet.iUnion (fun q => measurableSet_Icc.inter measurableSet_Icc)

lemma st_int_ind (f : ℝ → ℝ) (hf : LocallyIntegrable f) (a b : ℝ) (S : Set ℝ)
    (hS : MeasurableSet S) :
    Integrable ((Set.Icc a b ∩ S).indicator f) :=
  (integrable_indicator_iff (measurableSet_Icc.inter hS)).mpr
    ((hf.integrableOn_isCompact isCompact_Icc).mono_set Set.inter_subset_left)

noncomputable def stT (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (φ : Equiv.Perm (Fin (n + 1)))
    (i j : Fin (n + 1)) (x : ℝ) : ℝ :=
  (Set.Icc (B i) (A j) ∩ P A B φ).indicator f x + (Set.Icc (A j) (B i) ∩ P A B φ).indicator g x

lemma st_T_int (f g : ℝ → ℝ) (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    (A B : Fin (n + 1) → ℝ) (φ : Equiv.Perm (Fin (n + 1))) (i j : Fin (n + 1)) :
    Integrable (stT f g A B φ i j) :=
  (st_int_ind f hf _ _ _ (st_meas_P A B φ)).add (st_int_ind g hg _ _ _ (st_meas_P A B φ))

lemma st_cStar (f g : ℝ → ℝ) (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    (A B : Fin (n + 1) → ℝ) (φ : Equiv.Perm (Fin (n + 1))) (i j : Fin (n + 1)) :
    cStar f g A B φ i j = ∫ x, stT f g A B φ i j x := by
  unfold stT cStar
  rw [integral_add (st_int_ind f hf _ _ _ (st_meas_P A B φ))
    (st_int_ind g hg _ _ _ (st_meas_P A B φ)),
    integral_indicator (measurableSet_Icc.inter (st_meas_P A B φ)),
    integral_indicator (measurableSet_Icc.inter (st_meas_P A B φ))]

noncomputable def stW (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (φ ψ : Equiv.Perm (Fin (n + 1)))
    (x : ℝ) : ℝ := ∑ i, stT f g A B φ i (ψ i) x

lemma st_W_int (f g : ℝ → ℝ) (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    (A B : Fin (n + 1) → ℝ) (φ ψ : Equiv.Perm (Fin (n + 1))) : Integrable (stW f g A B φ ψ) := by
  unfold stW
  exact integrable_finsetSum _ (fun i _ => st_T_int f g hf hg A B φ i (ψ i))

lemma st_costStar (f g : ℝ → ℝ) (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    (A B : Fin (n + 1) → ℝ) (φ ψ : Equiv.Perm (Fin (n + 1))) :
    costStar f g A B φ ψ = ∫ x, stW f g A B φ ψ x := by
  unfold costStar stW
  rw [integral_finsetSum _ (fun i _ => st_T_int f g hf hg A B φ i (ψ i))]
  exact Finset.sum_congr rfl (fun i _ => st_cStar f g hf hg A B φ i (ψ i))

lemma st_out (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (φ ψ : Equiv.Perm (Fin (n + 1))) (x : ℝ)
    (hx : x ∉ P A B φ) : stW f g A B φ ψ x = 0 := by
  unfold stW stT
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [Set.indicator_of_notMem (fun h => hx h.2), Set.indicator_of_notMem (fun h => hx h.2)]
  simp

lemma st_in (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (φ ψ : Equiv.Perm (Fin (n + 1))) (x : ℝ)
    (hx : x ∈ P A B φ) (hxA : ∀ i, x ≠ A i) (hxB : ∀ i, x ≠ B i) :
    stW f g A B φ ψ x = cntW f g A B ψ x := by
  unfold stW cntW stT cntT
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have e1 : x ∈ Set.Icc (B i) (A (ψ i)) ∩ P A B φ ↔ x ∈ Set.Ico (B i) (A (ψ i)) := by
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ico]
    constructor
    · rintro ⟨⟨h1, h2⟩, _⟩; exact ⟨h1, lt_of_le_of_ne h2 (hxA _)⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.le⟩, hx⟩
  have e2 : x ∈ Set.Icc (A (ψ i)) (B i) ∩ P A B φ ↔ x ∈ Set.Ico (A (ψ i)) (B i) := by
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ico]
    constructor
    · rintro ⟨⟨h1, h2⟩, _⟩; exact ⟨h1, lt_of_le_of_ne h2 (hxB _)⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.le⟩, hx⟩
  have key : ∀ (h : ℝ → ℝ) (S T : Set ℝ), (x ∈ S ↔ x ∈ T) → S.indicator h x = T.indicator h x := by
    intro h S T hST
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hST.mp hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h' => hx (hST.mpr h'))]
  rw [key f _ _ e1, key g _ _ e2]

lemma st_phi_zero (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : Monotone (A ∘ φ)) (x : ℝ)
    (hx : x ∈ P A B φ) (hxA : ∀ i, x ≠ A i) (hxB : ∀ i, x ≠ B i) :
    cntW f g A B φ x = 0 := by
  obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hx
  simp only [Pq, Set.mem_inter_iff, Set.mem_Icc] at hq
  obtain ⟨⟨hq1, hq2⟩, hq3, hq4⟩ := hq
  have hNf : cntNf A B φ x = 0 := by
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [if_neg]
    rintro ⟨h1, h2⟩
    have hlt : x < B q.succ := lt_of_le_of_ne hq2 (hxB _)
    have hi : i ≤ q.castSucc := by
      by_contra hc
      push Not at hc
      have : q.succ ≤ i := Fin.castSucc_lt_iff_succ_le.mp hc
      have := hB this
      linarith
    have := hφ hi
    simp only [Function.comp] at this
    linarith
  have hNg : cntNg A B φ x = 0 := by
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [if_neg]
    rintro ⟨h1, h2⟩
    have hi : q.succ ≤ i := by
      by_contra hc
      push Not at hc
      have hc' : i ≤ q.castSucc := Fin.le_castSucc_iff.mpr hc
      have := hB hc'
      linarith
    have := hφ hi
    simp only [Function.comp] at this
    exact hxA _ (le_antisymm hq4 (by linarith))
  rw [cnt_W_eq, hNf, hNg]; simp

lemma e11_ii (f : ℝ → ℝ) (hf : LocallyIntegrable f) (a b : ℝ) :
    IntervalIntegrable f volume a b :=
  (hf.integrableOn_isCompact isCompact_uIcc).intervalIntegrable

noncomputable def e11F (φ γ : ℝ → ℝ) (u v : ℝ) : ℝ := if u ≤ v then φ v - φ u else γ u - γ v

lemma e11_c (f g : ℝ → ℝ) (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    (A B : Fin (n + 1) → ℝ) (i j : Fin (n + 1)) :
    c f g A B i j = e11F (fun t => ∫ x in (0:ℝ)..t, f x) (fun t => ∫ x in (0:ℝ)..t, g x)
      (B i) (A j) := by
  unfold c e11F
  split_ifs with h
  · rw [← intervalIntegral.integral_interval_sub_left (e11_ii f hf _ _) (e11_ii f hf _ _)]
  · rw [← intervalIntegral.integral_interval_sub_left (e11_ii g hg _ _) (e11_ii g hg _ _)]

lemma e11_alg (φ γ : ℝ → ℝ) (a b p q : ℝ) (hab : a ≤ b) (hpq : p ≤ q) :
    e11F φ γ a q + e11F φ γ b p - e11F φ γ a p - e11F φ γ b q =
      if max a p ≤ min b q then (φ (min b q) + γ (min b q)) - (φ (max a p) + γ (max a p))
      else 0 := by
  unfold e11F
  simp only [max_def, min_def]
  split_ifs <;> first
    | linarith
    | (exfalso; linarith)
    | (have e : b = p := (by linarith); subst e; linarith)
    | (have e : a = q := (by linarith); subst e; linarith)
    | (have e : a = p := (by linarith); subst e; linarith)
    | (have e : b = q := (by linarith); subst e; linarith)

lemma e11_cost (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (ψ : Equiv.Perm (Fin (n + 1)))
    (i j : Fin (n + 1)) :
    interchangeCost f g A B ψ i j =
      c f g A B i (ψ j) + c f g A B j (ψ i) - c f g A B i (ψ i) - c f g A B j (ψ j) := by
  unfold interchangeCost cost
  by_cases hij : i = j
  · subst hij; simp [alpha]
  · rw [← Finset.sum_sub_distrib]
    rw [← Finset.sum_subset (Finset.subset_univ ({i, j} : Finset (Fin (n+1))))]
    · rw [Finset.sum_pair hij]
      simp [alpha, Equiv.swap_apply_left, Equiv.swap_apply_right]
      ring
    · intro x _ hx
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      simp [alpha, Equiv.swap_apply_of_ne_of_ne hx.1 hx.2]

theorem eq_11_core {n : ℕ}
    (f g : ℝ → ℝ) (hf : MeasureTheory.LocallyIntegrable f) (hg : MeasureTheory.LocallyIntegrable g)
    (hfg : ∀ x, 0 ≤ f x + g x) (A B : Fin (n + 1) → ℝ)
    (ψ : Equiv.Perm (Fin (n + 1))) (i j : Fin (n + 1))
    (hBij : B i ≤ B j) (hAij : A (ψ i) ≤ A (ψ j)) :
    interchangeCost f g A B ψ i j =
      ∫ x in Set.Icc (B i) (B j) ∩ Set.Icc (A (ψ i)) (A (ψ j)), (f x + g x) := by
  rw [e11_cost, e11_c f g hf hg, e11_c f g hf hg, e11_c f g hf hg, e11_c f g hf hg]
  set φ : ℝ → ℝ := fun t => ∫ x in (0:ℝ)..t, f x
  set γ : ℝ → ℝ := fun t => ∫ x in (0:ℝ)..t, g x
  rw [e11_alg φ γ _ _ _ _ hBij hAij, Set.Icc_inter_Icc]
  split_ifs with h
  · have h1 : φ (min (B j) (A (ψ j))) - φ (max (B i) (A (ψ i))) =
        ∫ x in (max (B i) (A (ψ i)))..(min (B j) (A (ψ j))), f x :=
      intervalIntegral.integral_interval_sub_left (e11_ii f hf _ _) (e11_ii f hf _ _)
    have h2 : γ (min (B j) (A (ψ j))) - γ (max (B i) (A (ψ i))) =
        ∫ x in (max (B i) (A (ψ i)))..(min (B j) (A (ψ j))), g x :=
      intervalIntegral.integral_interval_sub_left (e11_ii g hg _ _) (e11_ii g hg _ _)
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h,
      intervalIntegral.integral_add (e11_ii f hf _ _) (e11_ii g hg _ _)]
    linarith
  · rw [Set.Icc_eq_empty h]; simp

lemma l7_adj (φ ψ : Equiv.Perm (Fin (n + 1))) (q : Fin n) (hq : q ∈ starArcs φ ψ) :
    (graphStar φ ψ).Adj q.castSucc q.succ := by
  have hne : q.castSucc ≠ q.succ := (Fin.castSucc_lt_succ).ne
  refine (SimpleGraph.sup_adj _ _ _ _).mpr (Or.inr ?_)
  simp only [SimpleGraph.fromRel_adj]
  refine ⟨hne, Or.inl ?_⟩
  simp only [adjArcs, Finset.mem_image]
  exact ⟨q, hq, rfl⟩

lemma l7_interval (φ ψ : Equiv.Perm (Fin (n + 1))) :
    ∀ (k : ℕ) (a b : Fin (n + 1)), b.val = a.val + k →
      (∀ q : Fin n, a ≤ q.castSucc → q.castSucc < b → q ∈ starArcs φ ψ) →
      (graphStar φ ψ).Reachable a b := by
  intro k
  induction k with
  | zero =>
    intro a b hab _
    have : a = b := Fin.ext (by omega)
    subst this; exact SimpleGraph.Reachable.refl _
  | succ k ih =>
    intro a b hab hq
    have han : a.val < n := by have := b.isLt; omega
    let c : Fin n := ⟨a.val, han⟩
    have hc1 : c.castSucc = a := Fin.ext rfl
    have hc2 : c.succ.val = a.val + 1 := rfl
    have h1 : (graphStar φ ψ).Reachable a c.succ := by
      have := l7_adj φ ψ c (hq c (by rw [hc1]) (by
        rw [Fin.lt_def]; show a.val < b.val; omega))
      rw [hc1] at this
      exact this.reachable
    refine h1.trans (ih c.succ b (by omega) ?_)
    intro q h1q h2q
    have h3 : c.succ.val ≤ q.castSucc.val := h1q
    have h4 : a.val ≤ q.castSucc.val := by omega
    exact hq q h4 h2q

lemma l7_core (φ ψ : Equiv.Perm (Fin (n + 1))) (hψ : IsTour ψ) :
    (graphStar φ ψ).Connected := by
  classical
  have hstep : ∀ x : Fin (n+1), (graphStar φ ψ).Reachable x (φ.symm (ψ x)) := by
    intro x
    rcases le_total x (φ.symm (ψ x)) with h | h
    · refine l7_interval φ ψ ((φ.symm (ψ x)).val - x.val) x _ (by
        have := Fin.le_def.mp h; omega) ?_
      intro q h1 h2
      simp only [starArcs, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inl ⟨x, h1, h2⟩
    · refine (l7_interval φ ψ (x.val - (φ.symm (ψ x)).val) (φ.symm (ψ x)) x (by
        have := Fin.le_def.mp h; omega) ?_).symm
      intro q h1 h2
      simp only [starArcs, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inr ⟨x, h1, h2⟩
  have hφ : ∀ x : Fin (n+1), (graphStar φ ψ).Reachable x (φ x) := by
    intro x
    by_cases h : φ x = x
    · rw [h]
    · apply SimpleGraph.Adj.reachable
      refine (SimpleGraph.sup_adj _ _ _ _).mpr (Or.inl ?_)
      simp only [graph, SimpleGraph.fromRel_adj]
      exact ⟨fun h' => h h'.symm, by simp⟩
  have hψx : ∀ x : Fin (n+1), (graphStar φ ψ).Reachable x (ψ x) := by
    intro x
    have h1 := hstep x
    have h2 := hφ (φ.symm (ψ x))
    simp only [Equiv.apply_symm_apply] at h2
    exact h1.trans h2
  let x0 : Fin (n+1) := 0
  let s : Finset (Fin (n+1)) := Finset.univ.filter fun y => (graphStar φ ψ).Reachable x0 y
  have hsub : s.map ψ.toEmbedding ⊆ s := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hz
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact hy.trans (hψx y)
  have heq : s.map ψ.toEmbedding = s :=
    Finset.eq_of_subset_of_card_le hsub (by simp)
  have hall : s = Finset.univ := by
    by_contra hne
    exact hψ s ⟨x0, by simp [s]⟩ hne heq
  have hreach : ∀ y, (graphStar φ ψ).Reachable x0 y := by
    intro y
    have : y ∈ s := by rw [hall]; exact Finset.mem_univ _
    simpa [s] using this
  refine ⟨fun u v => ?_⟩
  exact (hreach u).symm.trans (hreach v)


lemma e28_nonneg (f g : ℝ → ℝ) (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    (hfg : ∀ x, 0 ≤ f x + g x) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : RanksA A φ) (q : Fin n) :
    interchangeCost f g A B φ q.castSucc q.succ = ∫ x in Pq A B φ q, (f x + g x) := by
  exact eq_11_core f g hf hg hfg A B φ _ _ (hB (Fin.castSucc_lt_succ).le)
    (hφ (Fin.castSucc_lt_succ).le)

lemma e28_pq_meas (A B : Fin (n + 1) → ℝ) (φ : Equiv.Perm (Fin (n + 1))) (q : Fin n) :
    MeasurableSet (Pq A B φ q) := measurableSet_Icc.inter measurableSet_Icc

lemma e28_tree_sub (φ : Equiv.Perm (Fin (n + 1))) (S : Finset (Fin n))
    (hS : (graphWith φ (adjArcs S)).Connected) : ∃ T' ⊆ S, IsAdjTree φ T' := by
  classical
  have hne : ((S.powerset).filter fun S' => (graphWith φ (adjArcs S')).Connected).Nonempty :=
    ⟨S, by simp [hS]⟩
  obtain ⟨S', hS'mem, hmin⟩ := Finset.exists_min_image _ Finset.card hne
  simp only [Finset.mem_filter, Finset.mem_powerset] at hS'mem
  refine ⟨S', hS'mem.1, hS'mem.2, ?_⟩
  intro E' hE' hconn
  set S'' := S'.filter (fun q => adjArc q ∈ E') with hS''
  have hadj : adjArcs S'' = E' := by
    ext e
    simp only [adjArcs, Finset.mem_image, hS'', Finset.mem_filter]
    constructor
    · rintro ⟨q, ⟨_, hq⟩, rfl⟩; exact hq
    · intro he
      have : e ∈ adjArcs S' := hE'.subset he
      simp only [adjArcs, Finset.mem_image] at this
      obtain ⟨q, hq, rfl⟩ := this
      exact ⟨q, ⟨hq, he⟩, rfl⟩
  have hss : S'' ⊂ S' := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, fun h => ?_⟩
    rw [h] at hadj
    rw [hadj] at hE'
    exact lt_irrefl _ hE'
  have := hmin S'' (by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨(Finset.filter_subset _ _).trans hS'mem.1, by rw [hadj]; exact hconn⟩)
  exact absurd (Finset.card_lt_card hss) (not_lt.mpr this)

theorem eq_28_core {n : ℕ}
    (f g : ℝ → ℝ) (hf : MeasureTheory.LocallyIntegrable f) (hg : MeasureTheory.LocallyIntegrable g)
    (hfg : ∀ x, 0 ≤ f x + g x) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : RanksA A φ)
    (ψ : Equiv.Perm (Fin (n + 1))) (hψ : IsTour ψ)
    (T : Finset (Fin n)) (hT : IsMinCostAdjTree f g A B φ T) :
    adjTreeCost f g A B φ T ≤ costStar f g A B φ ψ := by
  classical
  set S := starArcs φ ψ with hSdef
  -- the tree inside the star arcs
  obtain ⟨T', hT'S, hT'⟩ := e28_tree_sub φ S (l7_core φ ψ hψ)
  have hnn : ∀ q : Fin n, 0 ≤ interchangeCost f g A B φ q.castSucc q.succ := by
    intro q
    rw [e28_nonneg f g hf hg hfg A B hB φ hφ q]
    exact integral_nonneg (fun x => hfg x)
  have h1 : adjTreeCost f g A B φ T ≤ adjTreeCost f g A B φ T' := hT.2 T' hT'
  have h2 : adjTreeCost f g A B φ T' ≤ adjTreeCost f g A B φ S :=
    Finset.sum_le_sum_of_subset_of_nonneg hT'S (fun q _ _ => hnn q)
  refine h1.trans (h2.trans ?_)
  -- integral comparison
  let Φ : ℝ → ℝ := fun x => ∑ q ∈ S, (Pq A B φ q).indicator (fun x => f x + g x) x
  have hIq : ∀ q : Fin n, Integrable ((Pq A B φ q).indicator (fun x => f x + g x)) := by
    intro q
    exact (integrable_indicator_iff (e28_pq_meas A B φ q)).mpr
      (((hf.add hg).integrableOn_isCompact isCompact_Icc).mono_set
        (Set.inter_subset_left))
  have hΦint : Integrable Φ := integrable_finsetSum _ (fun q _ => hIq q)
  have hΦ : ∫ x, Φ x = adjTreeCost f g A B φ S := by
    simp only [Φ]
    rw [integral_finsetSum _ (fun q _ => hIq q)]
    unfold adjTreeCost
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [integral_indicator (e28_pq_meas A B φ q), e28_nonneg f g hf hg hfg A B hB φ hφ q]
  rw [← hΦ, st_costStar f g hf hg]
  have hfin : (Set.range A ∪ Set.range B).Finite :=
    (Set.finite_range A).union (Set.finite_range B)
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ Set.range A ∪ Set.range B :=
    measure_eq_zero_iff_ae_notMem.mp (hfin.measure_zero _)
  refine integral_mono_ae hΦint (st_W_int f g hf hg A B φ ψ) ?_
  filter_upwards [hae] with x hx
  have hxA : ∀ i, x ≠ A i := fun i h => hx (Or.inl ⟨i, h.symm⟩)
  have hxB : ∀ i, x ≠ B i := fun i h => hx (Or.inr ⟨i, h.symm⟩)
  show Φ x ≤ stW f g A B φ ψ x
  by_cases hP : x ∈ P A B φ
  · obtain ⟨q0, hq0⟩ := Set.mem_iUnion.mp hP
    have hq0' := hq0
    simp only [Pq, Set.mem_inter_iff, Set.mem_Icc] at hq0'
    obtain ⟨⟨hb1, hb2⟩, ha1, ha2⟩ := hq0'
    -- index characterizations
    have hBiff : ∀ i, B i ≤ x ↔ i ≤ q0.castSucc := by
      intro i
      constructor
      · intro h
        by_contra hc
        push Not at hc
        have : q0.succ ≤ i := Fin.castSucc_lt_iff_succ_le.mp hc
        have := hB this
        exact hxB _ (le_antisymm hb2 (by linarith))
      · intro h; exact (hB h).trans hb1
    have hAiff : ∀ i, A (φ i) ≤ x ↔ i ≤ q0.castSucc := by
      intro i
      constructor
      · intro h
        by_contra hc
        push Not at hc
        have h' : q0.succ ≤ i := Fin.castSucc_lt_iff_succ_le.mp hc
        have := hφ h'
        simp only [Function.comp] at this
        exact hxA _ (le_antisymm ha2 (by linarith))
      · intro h
        have := hφ h
        simp only [Function.comp] at this
        linarith
    have hD : cntD A B x = 0 := by
      unfold cntD
      have : ∑ i, (if A i ≤ x then (1:ℝ) else 0) = ∑ i, if A (φ i) ≤ x then (1:ℝ) else 0 :=
        (Equiv.sum_comp φ (fun j => if A j ≤ x then (1:ℝ) else 0)).symm
      rw [this, sub_eq_zero]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [hBiff, hAiff]
    have hNeq : cntNf A B ψ x = cntNg A B ψ x := by
      have := cnt_diff A B ψ x; linarith
    have hst : stW f g A B φ ψ x = cntNf A B ψ x * (f x + g x) := by
      rw [st_in f g A B φ ψ x hP hxA hxB, cnt_W_eq, ← hNeq]; ring
    -- uniqueness of the interval
    have huniq : ∀ q : Fin n, x ∈ Pq A B φ q → q = q0 := by
      intro q hq
      have hq' := hq
      simp only [Pq, Set.mem_inter_iff, Set.mem_Icc] at hq'
      obtain ⟨⟨c1, c2⟩, _, _⟩ := hq'
      have e1 : q.castSucc ≤ q0.castSucc := (hBiff _).mp c1
      have e2 : q0.castSucc ≤ q.castSucc := by
        by_contra hc
        push Not at hc
        have h' : q.succ ≤ q0.castSucc := Fin.castSucc_lt_iff_succ_le.mp hc
        have := hB h'
        exact hxB _ (le_antisymm c2 (by linarith [(hBiff q0.castSucc).mpr le_rfl]))
      exact Fin.castSucc_injective _ (le_antisymm e1 e2)
    have hNf1 : q0 ∈ S → 1 ≤ cntNf A B ψ x := by
      intro hq0S
      simp only [hSdef, starArcs, Finset.mem_filter, Finset.mem_univ, true_and] at hq0S
      rcases hq0S with ⟨i, hi1, hi2⟩ | ⟨j, hj1, hj2⟩
      · have hBi : B i ≤ x := (hBiff i).mpr hi1
        have hAi : x < A (ψ i) := by
          have h3 : ¬ A (φ (φ.symm (ψ i))) ≤ x := by
            rw [hAiff]; exact not_le.mpr hi2
          rw [Equiv.apply_symm_apply] at h3
          exact not_le.mp h3
        have hterm : (if B i ≤ x ∧ x < A (ψ i) then (1:ℝ) else 0) = 1 := if_pos ⟨hBi, hAi⟩
        have := Finset.single_le_sum (f := fun i => if B i ≤ x ∧ x < A (ψ i) then (1:ℝ) else 0)
          (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
        unfold cntNf
        simp only [hterm] at this
        exact this
      · have hAj : A (ψ j) ≤ x := by
          have h3 := (hAiff (φ.symm (ψ j))).mpr hj1
          rwa [Equiv.apply_symm_apply] at h3
        have hBj : x < B j := by
          have h3 : ¬ B j ≤ x := by rw [hBiff]; exact not_le.mpr hj2
          exact not_le.mp h3
        have hterm : (if A (ψ j) ≤ x ∧ x < B j then (1:ℝ) else 0) = 1 := if_pos ⟨hAj, hBj⟩
        have := Finset.single_le_sum (f := fun i => if A (ψ i) ≤ x ∧ x < B i then (1:ℝ) else 0)
          (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ j)
        simp only [hterm] at this
        rw [hNeq]
        unfold cntNg
        exact this
    by_cases hq0S : q0 ∈ S
    · have hΦx : Φ x = f x + g x := by
        simp only [Φ]
        rw [Finset.sum_eq_single q0]
        · exact Set.indicator_of_mem hq0 _
        · intro q _ hq
          exact Set.indicator_of_notMem (fun h => hq (huniq q h)) _
        · intro h; exact absurd hq0S h
      rw [hΦx, hst]
      exact le_mul_of_one_le_left (hfg x) (hNf1 hq0S)
    · have hΦx : Φ x = 0 := by
        refine Finset.sum_eq_zero (fun q hq => ?_)
        have hqq : q ≠ q0 := fun h => hq0S (h ▸ hq)
        exact Set.indicator_of_notMem (fun h => hqq (huniq q h)) _
      rw [hΦx, hst]
      exact mul_nonneg (cntNf_nonneg A B ψ x) (hfg x)
  · have : Φ x = 0 := by
      simp only [Φ]
      refine Finset.sum_eq_zero (fun q _ => ?_)
      exact Set.indicator_of_notMem (fun h => hP (Set.mem_iUnion.mpr ⟨q, h⟩)) _
    rw [this, st_out f g A B φ ψ x hP]

end GilmoreGomoryTSP.MinCost

open GilmoreGomoryTSP.MinCost


theorem solution {n : ℕ}
    (f g : ℝ → ℝ) (hf : MeasureTheory.LocallyIntegrable f) (hg : MeasureTheory.LocallyIntegrable g)
    (hfg : ∀ x, 0 ≤ f x + g x) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : RanksA A φ)
    (ψ : Equiv.Perm (Fin (n + 1))) (hψ : IsTour ψ)
    (T : Finset (Fin n)) (hT : IsMinCostAdjTree f g A B φ T) :
    adjTreeCost f g A B φ T ≤ costStar f g A B φ ψ := by
  exact eq_28_core f g hf hg hfg A B hB φ hφ ψ hψ T hT
