-- Prove2me | solution 1 for GlobalTheory.QCoh.IsFlatOver.isSMulRegular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:10:35.010745+00:00
-- url     : https://prove2.me/submissions/cc1f4e74-895a-4349-9f3f-9c615de0c0b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds
import Theorems.Thm_GlobalTheory_QCoh_section_eq_zero_of_germ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct IsLocalRing
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} {F G H : X.Modules} {U V : X.Opens}
variable {R : Type*} [CommRing R] (ρ : R →+* Γ(X, ⊤))
variable {ρ}
namespace GlobalTheory.QCoh
namespace IsFlatOver
theorem _root_.solution (h : IsFlatOver F ρ) {r : R} (hr : r ∈ nonZeroDivisors R)
    (U : X.Opens) : IsSMulRegular Γ(F, U) (baseHom U ρ r) := by
  refine .of_right_eq_zero_of_smul fun s hs ↦ section_eq_zero_of_germ s fun x hx ↦ ?_
  obtain ⟨V, hV, hxV, hVU⟩ := exists_affine_mem_le x hx
  letI := baseModule F V ρ
  haveI : Module.Flat R Γ(F, V) := h V hV
  have h0 : r • F.presheaf.map (homOfLE hVU).op s = 0 := by
    change baseHom V ρ r • F.presheaf.map (homOfLE hVU).op s = 0
    rw [← res_baseHom ρ hVU, ← Scheme.Modules.map_smul, hs, map_zero]
  rw [← F.presheaf.germ_res_apply (homOfLE hVU) x hxV,
    (Module.Flat.isSMulRegular_of_nonZeroDivisors hr).right_eq_zero_of_smul h0, map_zero]
end IsFlatOver
end GlobalTheory.QCoh
