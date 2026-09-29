-- Prove2me | solution 1 for HopfAlgebra.surjective_of_injective_of_surjective_baseChange_of_pow_eq_one_of_simple
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/011feadb-0902-5485-9bf9-e4be72853cb6

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Definitions.Def_HopfAlgebra_FVectStructure
import Definitions.Def_HopfAlgebra_HasFVectDevissage
import Theorems.Thm_HopfAlgebra_exists_faithfullyFlat_hasFVectDevissage_baseChange_of_pow_eq_one
import Theorems.Thm_HopfAlgebra_bijective_of_faithfullyFlat_baseChange_bijective
import Theorems.Thm_HopfAlgebra_bijective_baseChange_of_hasFVectDevissage
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_surjective_of_injective_of_surjective_baseChange_of_pow_eq_one_of_simple
p2m_attr_erase "instance" "CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra instIsScalarTowerTensorProduct_definitions"
p2m_attr_erase "simp" "HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply mem_flatClosure_iff HopfOrder.doubleCmp_tmul HopfOrder.tensorSqHom_tmul HopfOrder.baseChangeHom_tmul"

set_option autoImplicit false
universe u v
open scoped TensorProduct

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hunif : Irreducible (p : R))
    {H : Type v} [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H]
    [Coalgebra.IsCocomm R H]
    {H' : Type v} [CommRing H'] [HopfAlgebra R H'] [Module.Finite R H'] [Module.Flat R H']
    [Coalgebra.IsCocomm R H']
    (n : ℕ)
    (hH : ∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (H →ₐ[R] T)), f ^ p ^ n = 1)
    (hH' : ∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (H' →ₐ[R] T)), f ^ p ^ n = 1)
    (hsimple : ∀ I : Ideal H',
      (∀ (c : R) (x : H'), c ≠ 0 → c • x ∈ I → x ∈ I) →
      (∀ x ∈ I, Coalgebra.counit (R := R) x = 0) →
      (∀ x ∈ I, HopfAlgebra.antipode R x ∈ I) →
      (∀ x ∈ I, Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)
        (Coalgebra.comul (R := R) x) = 0) →
      I = ⊥ ∨ I = RingHom.ker (Bialgebra.counitAlgHom R H'))
    (j : H →ₐc[R] H') (hj : Function.Injective j)
    (hjK : Function.Surjective ((j : H →ₐ[R] H').toLinearMap.baseChange K)) :
    Function.Surjective j := by

  have hφK : Function.Bijective ((j : H →ₐ[R] H').toLinearMap.baseChange K) := by
    refine ⟨?_, hjK⟩
    haveI : Module.Flat R K := IsLocalization.flat K (nonZeroDivisors R)
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := K) _ hj

  obtain ⟨R₂, _, _, _, _, _, K₂, _, _, _, hunif₂, hdev⟩ :=
    HopfAlgebra.exists_faithfullyFlat_hasFVectDevissage_baseChange_of_pow_eq_one p hp2 hunif n hH'

  exact (HopfAlgebra.bijective_of_faithfullyFlat_baseChange_bijective R₂ j
    (HopfAlgebra.bijective_baseChange_of_hasFVectDevissage K p hp2 j hφK R₂ K₂ hunif₂ hdev)).2

end S_HopfAlgebra_surjective_of_injective_of_surjective_baseChange_of_pow_eq_one_of_simple
end P2MW
export P2MW.S_HopfAlgebra_surjective_of_injective_of_surjective_baseChange_of_pow_eq_one_of_simple (solution)
