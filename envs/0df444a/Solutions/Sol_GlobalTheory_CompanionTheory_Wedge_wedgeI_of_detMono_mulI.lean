-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Wedge.wedgeI_of_detMono_mulI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:39:41.635314+00:00
-- url     : https://prove2.me/submissions/28d75007-bf79-40e7-a466-68520139ace2

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeBoundInfinitePlaces
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_nI_nonneg
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_nI_ne_zero_iff_det
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_gram_det_ne_zero_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_nI_submatrix
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_exists_proj
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_commGroup_mul_mul_eq_mul_inv_mul_mul_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PositivityTheory.Rg.BcB.D1
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Wedge
variable {ι κ κ' : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
namespace GlobalTheory.CompanionTheory.Wedge
theorem _root_.solution : DetMono → MulI → WedgeI := by
  intro hD hM ι _ _
  refine ⟨fun κ _ _ A => nI_nonneg A, fun κ _ _ A => (nI_ne_zero_iff_det A).trans (gram_det_ne_zero_iff A),
    fun κ κ' _ _ _ _ e A => nI_submatrix e A, fun κ _ _ B hB => ?_⟩
  obtain ⟨Y, hYB, hQ⟩ := exists_proj B hB
  exact ⟨Y, fun κ' _ _ C => commGroup_mul_mul_eq_mul_inv_mul_mul_mul hD hM B Y hYB hQ C⟩
end GlobalTheory.CompanionTheory.Wedge
