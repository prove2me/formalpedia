-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.UpInv.sum_pieces
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:39:29.346881+00:00
-- url     : https://prove2.me/submissions/27130ba3-b4f6-450b-b6e9-842ddd3bc729

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_UpperTriangularInverseIsUpper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Iwahori GlobalTheory.CompanionTheory.Iwahori.UpInv
variable {L V ι : Type} [Field L] [AddCommGroup V] [Module L V] [Fintype ι]
namespace GlobalTheory.CompanionTheory.Iwahori.UpInv
theorem _root_.solution {P : ι → Module.End L V} (hP : IsPieces P) (x : V) :
    ∑ j, P j x = x := by
  have h := congrArg (fun T : Module.End L V => T x) hP.sum
  simpa [LinearMap.sum_apply] using h
end GlobalTheory.CompanionTheory.Iwahori.UpInv
