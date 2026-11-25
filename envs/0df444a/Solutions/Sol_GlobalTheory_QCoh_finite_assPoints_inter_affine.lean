-- Prove2me | solution 1 for GlobalTheory.QCoh.finite_assPoints_inter_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:11:11.264826+00:00
-- url     : https://prove2.me/submissions/e7108308-3a85-40f6-9f3e-9ce6527ba363

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds
import Theorems.Thm_GlobalTheory_QCoh_biprodSectionsEquiv_apply
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_pointOfPrime_primeIdealOf
import Theorems.Thm_GlobalTheory_QCoh_primeIdealOf_pointOfPrime
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_stalkLinearEquiv_apply
import Theorems.Thm_GlobalTheory_QCoh_stalkLinear_add
import Theorems.Thm_GlobalTheory_QCoh_stalkLinear_zero
import Theorems.Thm_GlobalTheory_SheafLES_map_id
import Theorems.Thm_GlobalTheory_SheafLES_map_zero_hom
import Theorems.Thm_GlobalTheory_SheafLES_res_id
import Theorems.Thm_GlobalTheory_SheafLES_toAbSheaf_map_hom
import Theorems.Thm_GlobalTheory_SheafLES_toAbSheaf_obj_obj
import Theorems.Thm_P2M_GlobalTheory_SheafLES___map_026ec4bafb10
import Theorems.Thm_P2M_GlobalTheory_SheafLES_map___ee3a67e9aebf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.QCoh.biprodSectionsEquiv_apply
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.pointOfPrime_primeIdealOf
attribute [local simp] GlobalTheory.QCoh.primeIdealOf_pointOfPrime
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply
attribute [local simp] GlobalTheory.QCoh.stalkLinearEquiv_apply
attribute [local simp] GlobalTheory.QCoh.stalkLinear_add
attribute [local simp] GlobalTheory.QCoh.stalkLinear_zero
attribute [local simp] GlobalTheory.SheafLES.map_id
attribute [local simp] GlobalTheory.SheafLES.map_zero_hom
attribute [local simp] GlobalTheory.SheafLES.res_id
attribute [local simp] GlobalTheory.SheafLES.toAbSheaf_map_hom
attribute [local simp] GlobalTheory.SheafLES.toAbSheaf_obj_obj
attribute [local simp] P2M_GlobalTheory_SheafLES___map_026ec4bafb10
attribute [local simp] P2M_GlobalTheory_SheafLES_map___ee3a67e9aebf



set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct IsLocalRing
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} {F G H : X.Modules} {U V : X.Opens}
variable [IsLocallyNoetherian X]
variable (F)
namespace GlobalTheory.QCoh
theorem _root_.solution [IsFiniteQC F] (hU : IsAffineOpen U) :
    (assPoints F ∩ U).Finite := by
  have := finite_sections F hU
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have h : (PrimeSpectrum.asIdeal ⁻¹' associatedPrimes Γ(X, U) Γ(F, U)).Finite :=
    (associatedPrimes.finite Γ(X, U) Γ(F, U)).preimage fun _ _ _ _ ↦ PrimeSpectrum.ext
  refine (h.image fun P ↦ (pointOfPrime hU P : X)).subset fun x hx ↦
    ⟨hU.primeIdealOf ⟨x, hx.2⟩, (mem_assPoints_iff_primeIdealOf hU ⟨x, hx.2⟩).1 hx.1, ?_⟩
  simp only [pointOfPrime_primeIdealOf]
end GlobalTheory.QCoh
