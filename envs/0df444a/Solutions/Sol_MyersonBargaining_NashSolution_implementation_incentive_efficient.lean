-- Prove2me | solution 1 for MyersonBargaining.NashSolution.implementation_incentive_efficient
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T23:59:29.109114+00:00
-- url     : https://prove2.me/submissions/9374c802-798e-49fa-8175-40c47969050e

import Mathlib
import Definitions.Def_MyersonBargaining_NashSolution_Bargaining



namespace MyersonBargaining.NashSolution

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {A : ι → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
  [∀ i, Nonempty (A i)] {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]

lemma prod_lt_prod_aux {β : Type} (s : Finset β) (hs : s.Nonempty) (f g : β → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i < g i) : ∏ i ∈ s, f i < ∏ i ∈ s, g i := by
  by_cases h : ∀ i ∈ s, 0 < f i
  · exact Finset.prod_lt_prod_of_nonempty h hfg hs
  · push_neg at h
    obtain ⟨i, hi, hi0⟩ := h
    have : f i = 0 := le_antisymm hi0 (hf i hi)
    rw [Finset.prod_eq_zero hi this]
    exact Finset.prod_pos (fun j hj => lt_of_le_of_lt (hf j hj) (hfg j hj))

theorem implementation_incentive_efficient_core
    (G : Problem ι A C) (cstar : C) (π : C → (∀ i, A i) → ℝ)
    (hπ : IsChoiceMechanism π ∧ IsBIC G π)
    (hx : IsBargainingSolution G cstar (V G π)) :
    IsIncentiveEfficient G π := by
  refine ⟨hπ.1, hπ.2, ?_⟩
  rintro ⟨π', h1, h2, hdom⟩
  obtain ⟨hxF, hmax⟩ := hx
  have hyF : V G π' ∈ FPlus G cstar :=
    ⟨⟨π', h1, h2, rfl⟩, fun k => le_trans (hxF.2 k) (le_of_lt (hdom k))⟩
  have hle := hmax _ hyF
  have hlt : nashProduct G cstar (V G π) < nashProduct G cstar (V G π') := by
    unfold nashProduct
    apply prod_lt_prod_aux _ Finset.univ_nonempty
    · intro i _
      apply Finset.prod_nonneg
      intro a _
      apply Real.rpow_nonneg
      linarith [hxF.2 ⟨i, a⟩]
    · intro i _
      apply prod_lt_prod_aux _ Finset.univ_nonempty
      · intro a _
        apply Real.rpow_nonneg
        linarith [hxF.2 ⟨i, a⟩]
      · intro a _
        apply Real.rpow_lt_rpow
        · linarith [hxF.2 ⟨i, a⟩]
        · linarith [hdom ⟨i, a⟩]
        · exact G.marginal_pos i a
  linarith

end MyersonBargaining.NashSolution

open MyersonBargaining.NashSolution


theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {A : ι → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Nonempty (A i)] {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
    (G : Problem ι A C) (cstar : C) (π : C → (∀ i, A i) → ℝ)
    (hπ : IsChoiceMechanism π ∧ IsBIC G π)
    (hx : IsBargainingSolution G cstar (V G π)) :
    IsIncentiveEfficient G π := by
  exact implementation_incentive_efficient_core G cstar π hπ hx
