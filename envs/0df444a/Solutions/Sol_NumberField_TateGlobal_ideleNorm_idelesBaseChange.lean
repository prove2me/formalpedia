-- Prove2me | solution 1 for NumberField.TateGlobal.ideleNorm_idelesBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/d63d809b-8bb9-5c2e-a0c7-d106c1d05097

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_NumberField_distribHaarChar_idelicNorm_genuineBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_ideleNorm_idelesBaseChange
p2m_attr_erase "instance" "instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.preimage_mulLeft_smul ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false

open NumberField

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (y : (AdeleRing (𝓞 K) K)ˣ) :
    NumberField.TateGlobal.ideleNorm L (AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) =
      NumberField.TateGlobal.ideleNorm K y ^ Module.finrank K L := by
  classical
  haveI : Nontrivial (AdeleRing (𝓞 K) K) :=
    nontrivial_of_ne 0 1 (fun h => zero_ne_one (by exact congrArg Prod.fst h))
  letI alg : Algebra (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) :=
    (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toAlgebra
  haveI hfree : Module.Free (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) :=
    Module.Free.of_equiv (M4aHerbrand.GenuineDescent.genuineBaseChange K L).tensorEquiv.toLinearEquiv
  have hrank : Module.finrank (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) = Module.finrank K L := by
    rw [← (M4aHerbrand.GenuineDescent.genuineBaseChange K L).tensorEquiv.toLinearEquiv.finrank_eq,
      Module.finrank_baseChange]
  have hN : (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm
      (AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) = y ^ Module.finrank K L := by
    apply Units.ext
    simp only [M4aHerbrand.AdeleBaseChange.idelicNorm, AutomorphicForm.TransversalMeasure.idelesBaseChange,
      Units.coe_map, MonoidHom.coe_coe, Units.val_pow_eq_pow_val, RingHom.toMonoidHom_eq_coe]
    show Algebra.norm (AdeleRing (𝓞 K) K) (algebraMap (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) (y : AdeleRing (𝓞 K) K)) =
      (y : AdeleRing (𝓞 K) K) ^ Module.finrank K L
    rw [Algebra.norm_algebraMap, hrank]
  unfold NumberField.TateGlobal.ideleNorm
  rw [← NumberField.distribHaarChar_idelicNorm_genuineBaseChange K L, hN, map_pow]
  push_cast
  rfl

end S_NumberField_TateGlobal_ideleNorm_idelesBaseChange
end P2MW
export P2MW.S_NumberField_TateGlobal_ideleNorm_idelesBaseChange (solution)
