-- Prove2me | solution 1 for GlobalTheory.QCoh.IsFiniteQC.of_isFiniteType
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:23:21.116559+00:00
-- url     : https://prove2.me/submissions/2cdd590d-f7eb-4034-9ce1-424b966d5310

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds
import Theorems.Thm_GlobalTheory_QCoh_IsFiniteQC_of_restrict
import Theorems.Thm_GlobalTheory_QCoh_IsFiniteQC_of_generatingSections
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
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.QCoh
namespace IsFiniteQC
theorem _root_.solution [F.IsQuasicoherent] [F.IsFiniteType] : IsFiniteQC F := by
  obtain ⟨σ, hσ⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData F
  refine .of_restrict (fun i ↦ Scheme.Opens.ι (σ.X i)) (fun x ↦ ?_) fun i ↦ ?_
  · obtain ⟨i, hi⟩ := ((Opens.coversTop_iff _ _).1 σ.coversTop).exists_mem x
    exact ⟨i, by simpa using hi⟩
  · let e := Scheme.Modules.overEquiv (σ.X i)
    have : PreservesColimitsOfSize.{u, u} e.functor := inferInstance
    have := hσ.isFiniteType i
    let τ := ((σ.generators i).map e.functor
      (Opens.sheafOfModulesEquivOverUnit (σ.X i) X.ringCatSheaf).symm).ofEpi
      ((Scheme.Modules.overFunctorEquiv (σ.X i)).app F).hom
    have : τ.IsFiniteType := ⟨this.finite⟩
    exact .of_generatingSections τ
end IsFiniteQC
end GlobalTheory.QCoh
