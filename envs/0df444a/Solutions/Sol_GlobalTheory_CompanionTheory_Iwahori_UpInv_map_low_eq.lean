-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.UpInv.map_low_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:14:05.78408+00:00
-- url     : https://prove2.me/submissions/225fe128-259e-4a0b-a28f-f79f97241d05

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_UpperTriangularInverseIsUpper
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_UpInv_map_low_le

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
theorem _root_.solution [FiniteDimensional L V] {wt : ι → ℕ} {P : ι → Module.End L V}
    (hP : IsPieces P) {a a' : Module.End L V} (h1 : a * a' = 1) (h2 : a' * a = 1)
    (ha : IsUpper wt P a) (m : ℕ) : (low wt P m).map a = low wt P m := by
  let e : V ≃ₗ[L] V := LinearEquiv.ofLinear a a' h1 h2
  exact Submodule.eq_of_le_of_finrank_eq (map_low_le hP ha m)
    (LinearEquiv.finrank_map_eq e (low wt P m))
end GlobalTheory.CompanionTheory.Iwahori.UpInv
