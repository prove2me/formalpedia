-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CartanU.isTor_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:22:56.200055+00:00
-- url     : https://prove2.me/submissions/d7786770-7648-4a9d-8d2a-4ab263e565b8

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
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
namespace GlobalTheory.CompanionTheory.CartanU
theorem _root_.solution {s : L →+* L} {l : ℕ} {e f : Fin l → V} {W : Submodule L V} {u u' : Fin l → L}
    {t t' : V ≃ₗ[L] V} (h : IsTor s e f W u t) (h' : IsTor s e f W u' t') :
    IsTor s e f W (fun i => u i * u' i) (t * t') := by
  refine ⟨fun i => ?_, fun i => ?_, fun w hw => ?_⟩
  · rw [LinearEquiv.mul_apply, h'.1, map_smul, h.1, smul_smul, mul_comm]
  · rw [LinearEquiv.mul_apply, h'.2.1, map_smul, h.2.1, smul_smul, map_mul, mul_inv, mul_comm]
  · rw [LinearEquiv.mul_apply, h'.2.2 w hw, h.2.2 w hw]
end GlobalTheory.CompanionTheory.CartanU
