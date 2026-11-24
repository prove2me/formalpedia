-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.Unitary.lowerUni_of_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:39:23.873929+00:00
-- url     : https://prove2.me/submissions/ceeb904d-28ee-4853-a73f-80dd1104edd5

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AntiInvolutionSwapsUpperLower
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_Unitary_diag_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Iwahori GlobalTheory.CompanionTheory.Iwahori.Unitary
variable {E ι : Type} [Ring E] [Fintype ι]
namespace GlobalTheory.CompanionTheory.Iwahori.Unitary
theorem _root_.solution {wt : ι → ℕ} {P : ι → E} (hP : IsPieces P) (hw : Function.Injective wt)
    {b b' : E} (hb : IsLowerUni wt P b) (hb' : IsLower wt P b') (h : b * b' = 1) :
    IsLowerUni wt P b' := by
  refine ⟨hb', fun i => ?_⟩
  have h1 := diag_mul hP hw hb.1 hb' i
  rw [h, mul_one, hP.idem, hb.2] at h1
  calc P i * b' * P i = P i * (P i * b' * P i) := by simp only [← mul_assoc, hP.idem]
    _ = P i := h1.symm
end GlobalTheory.CompanionTheory.Iwahori.Unitary
