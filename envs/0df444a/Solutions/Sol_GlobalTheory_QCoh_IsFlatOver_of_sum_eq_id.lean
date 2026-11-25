-- Prove2me | solution 1 for GlobalTheory.QCoh.IsFlatOver.of_sum_eq_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:57:41.039442+00:00
-- url     : https://prove2.me/submissions/0572e385-fe6b-420b-9bdd-8a00906d0045

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds
import Theorems.Thm_GlobalTheory_QCoh_sectionsBaseLinear_apply
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


attribute [local simp] GlobalTheory.QCoh.sectionsBaseLinear_apply

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
theorem _root_.solution {ι : Type*} [Fintype ι] {A : ι → X.Modules} (p : ∀ i, F ⟶ A i)
    (q : ∀ i, A i ⟶ F) (h : ∑ i, p i ≫ q i = 𝟙 F) (hA : ∀ i, IsFlatOver (A i) ρ) :
    IsFlatOver F ρ := by
  classical
  intro U hU
  letI := baseModule F U ρ
  letI (i : ι) := baseModule (A i) U ρ
  haveI (i : ι) : Module.Flat R Γ(A i, U) := hA i U hU
  haveI : Module.Flat R (∀ i, Γ(A i, U)) :=
    .of_linearEquiv (DirectSum.linearEquivFunOnFintype R ι fun i ↦ Γ(A i, U)).symm
  refine .of_retract (LinearMap.pi fun i ↦ sectionsBaseLinear ρ (p i) U)
    (LinearMap.lsum R (fun i ↦ Γ(A i, U)) ℕ fun i ↦ sectionsBaseLinear ρ (q i) U) ?_
  ext s
  simpa using sum_app_app p q h s
end IsFlatOver
end GlobalTheory.QCoh
