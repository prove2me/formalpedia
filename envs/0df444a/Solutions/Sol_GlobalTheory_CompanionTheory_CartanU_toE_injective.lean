-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CartanU.toE_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:22:51.774035+00:00
-- url     : https://prove2.me/submissions/6771d577-64b5-4132-88b4-affd8aa34fbd

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsometricLatticeCongruenceSubgroups

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB CompanionTheory.Rg.Fl
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CartanU
variable {L : Type} [NontriviallyNormedField L] {n : ℕ}
namespace GlobalTheory.CompanionTheory.CartanU
theorem _root_.solution : Function.Injective (toE : GL (Fin n) L → _) := by
  intro a b h
  apply Units.ext
  apply Matrix.mulVec_injective
  funext x
  exact congrArg (fun t : (Fin n → L) ≃ₗ[L] (Fin n → L) => t x) h
end GlobalTheory.CompanionTheory.CartanU
