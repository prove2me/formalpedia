-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.UpInv.piece_mem_low
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:39:28.532868+00:00
-- url     : https://prove2.me/submissions/585361c9-76ef-43ce-9c5f-03744c38fcc8

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
theorem _root_.solution {wt : ι → ℕ} {P : ι → Module.End L V} (hP : IsPieces P) (j : ι) (x : V) :
    P j x ∈ low wt P (wt j + 1) := by
  intro i hi
  have hij : i ≠ j := by
    rintro rfl
    omega
  have h := congrArg (fun T : Module.End L V => T x) (hP.orth i j hij)
  simpa using h
end GlobalTheory.CompanionTheory.Iwahori.UpInv
