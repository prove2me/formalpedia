-- Prove2me | solution 1 for KAdaptability.PolicyCount.card_policies_eq
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:23:08.468815+00:00
-- url     : https://prove2.me/submissions/2e833964-42d3-41f6-a107-d21a090e4831

import Mathlib
import Definitions.Def_KAdaptability_PolicyCount_PO
import Definitions.Def_KAdaptability_PolicyCount_POK

set_option autoImplicit false
open Matrix KAdaptability.PolicyCount

variable {N M L nQ R : ℕ}

theorem cons' (P : Problem N M L nQ R) (K : ℕ) :
    P.optPO ≤ P.optPOK K := by
  unfold Problem.optPOK
  refine le_iInf fun x => le_iInf fun ys => le_iInf fun hf => ?_
  refine le_trans (iInf₂_le x hf.1) ?_
  unfold Problem.objPO Problem.objPOK
  refine iSup₂_mono fun ξ hξ => ?_
  refine add_le_add le_rfl ?_
  refine le_iInf fun k => ?_
  exact (iInf₂_le (ys k) (hf.2 k).1).trans (iInf_le _ (hf.2 k).2)

open Classical in
theorem solution (P : Problem N M L nQ R) :
    P.optPOK P.Y.card = P.optPO := by
  apply le_antisymm
  · unfold Problem.optPO
    refine le_iInf fun x => le_iInf fun hx => ?_
    by_cases hne : (P.Y.filter (fun y => P.T *ᵥ x + P.W *ᵥ y ≤ P.h)).Nonempty
    · obtain ⟨y0, hy0⟩ := hne
      set Yx := P.Y.filter (fun y => P.T *ᵥ x + P.W *ᵥ y ≤ P.h) with hYx
      let ys : Fin P.Y.card → Fin M → ℝ := fun k => Yx.toList.getD k y0
      have hys_mem : ∀ k, ys k ∈ Yx := by
        intro k
        simp only [ys]
        by_cases hk : (k : ℕ) < Yx.toList.length
        · rw [List.getD_eq_getElem _ _ hk]
          exact Finset.mem_toList.1 (List.getElem_mem hk)
        · rw [List.getD_eq_default _ _ (by omega)]
          exact hy0
      have hsurj : ∀ y ∈ Yx, ∃ k, ys k = y := by
        intro y hy
        have hy' : y ∈ Yx.toList := Finset.mem_toList.2 hy
        obtain ⟨i, hi, hiy⟩ := List.mem_iff_getElem.1 hy'
        have hlen : Yx.toList.length ≤ P.Y.card := by
          rw [Finset.length_toList]
          exact Finset.card_le_card (Finset.filter_subset _ _)
        refine ⟨⟨i, by omega⟩, ?_⟩
        simp only [ys]
        rw [List.getD_eq_getElem _ _ hi]
        exact hiy
      have hfeas : P.FeasibleK P.Y.card x ys :=
        ⟨hx, fun k => Finset.mem_filter.1 (hys_mem k)⟩
      refine le_trans ((iInf_le _ x).trans ((iInf_le _ ys).trans (iInf_le _ hfeas))) ?_
      unfold Problem.objPO Problem.objPOK
      refine iSup₂_mono fun ξ hξ => ?_
      refine add_le_add le_rfl ?_
      refine le_iInf fun y => le_iInf fun hy => le_iInf fun hfe => ?_
      obtain ⟨k, hk⟩ := hsurj y (Finset.mem_filter.2 ⟨hy, hfe⟩)
      rw [← hk]
      exact iInf_le (fun k => ((ξ ⬝ᵥ (P.Q *ᵥ ys k) : ℝ) : EReal)) k
    · refine le_trans le_top ?_
      obtain ⟨ξ0, hξ0⟩ := P.Xi_nonempty
      unfold Problem.objPO
      refine le_iSup₂_of_le ξ0 hξ0 ?_
      have : (⨅ y ∈ P.Y, ⨅ (_ : P.T *ᵥ x + P.W *ᵥ y ≤ P.h),
          ((ξ0 ⬝ᵥ (P.Q *ᵥ y) : ℝ) : EReal)) = ⊤ := by
        simp only [iInf_eq_top]
        intro y hy hfe
        exact absurd ⟨y, Finset.mem_filter.2 ⟨hy, hfe⟩⟩ hne
      rw [this, EReal.coe_add_top]
  · exact cons' P _
