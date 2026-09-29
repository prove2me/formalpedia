-- Prove2me | solution 1 for NumberField.AdeleRing.polishSpace_units
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/f22dfd86-fcd4-5a25-b4dd-d2d0b52a42b9

import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_NumberField_AdelicHaar
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdeleRing_polishSpace_units
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open NumberField

namespace K42Polish

open Topology

theorem polishSpace_of_addCommGroup (A : Type*) [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] : PolishSpace A := by
  letI u : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  haveI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  haveI : CompleteSpace A := IsRightUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace
  haveI : (uniformity A).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  haveI : TopologicalSpace.IsCompletelyMetrizableSpace A := inferInstance
  infer_instance

theorem polishSpace_of_commGroup (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] : PolishSpace G := by
  letI u : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  haveI : IsUniformGroup G := isUniformGroup_of_commGroup
  haveI : CompleteSpace G := IsRightUniformGroup.completeSpace_of_weaklyLocallyCompactSpace
  haveI : (uniformity G).IsCountablyGenerated := IsUniformGroup.uniformity_countably_generated
  haveI : TopologicalSpace.IsCompletelyMetrizableSpace G := inferInstance
  infer_instance

end K42Polish

theorem solution (K : Type) [Field K] [NumberField K] :
    PolishSpace (AdeleRing (𝓞 K) K)ˣ := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K) := NumberField.AdeleRing.secondCountableTopology K
  haveI : LocallyCompactSpace (AdeleRing (𝓞 K) K) := NumberField.AdelicHaar.locallyCompactSpace_adeleRing (𝓞 K) K
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ := Units.isInducing_embedProduct.secondCountableTopology
  haveI : LocallyCompactSpace (AdeleRing (𝓞 K) K)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (AdeleRing (𝓞 K) K)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  exact K42Polish.polishSpace_of_commGroup (AdeleRing (𝓞 K) K)ˣ

end S_NumberField_AdeleRing_polishSpace_units
end P2MW
export P2MW.S_NumberField_AdeleRing_polishSpace_units (solution)
