-- Prove2me | solution 1 for HopfAlgebra.ker_eq_map_hopfKer_inf_ker_counit_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/f7b8f2b8-f3f8-57e8-8804-d2ba6dd6aaa7

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Theorems.Thm_HopfAlgebra_isHopfGalois_iff_ker_le_span_of_surjective
import Theorems.Thm_HopfAlgebra_isHopfGalois_and_faithfullyFlat_and_finiteType_hopfKer_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_ker_eq_map_hopfKer_inf_ker_counit_of_surjective
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul"

set_option autoImplicit false

open scoped TensorProduct

namespace HopfAlgebra
p2m_export "HopfAlgebra" "coaction coaction_apply hopfKer coaction_eq_of_mem isHopfGalois_iff_ker_le_span_of_surjective isHopfGalois_and_faithfullyFlat_and_finiteType_hopfKer_of_surjective"
namespace KerEqAug
p2m_open "HopfAlgebra"

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Bialgebra R A]
  {B : Type*} [CommRing B] [Bialgebra R B]

noncomputable def epsId (R A B : Type*) [CommRing R] [CommRing A] [Bialgebra R A] [CommRing B] [Bialgebra R B] :
    A ⊗[R] B →ₗ[R] B :=
  (TensorProduct.lid R B).toLinearMap ∘ₗ TensorProduct.map (Coalgebra.counit (R := R) (A := A)) LinearMap.id

@[scoped simp] theorem epsId_tmul (a : A) (b : B) : epsId R A B (a ⊗ₜ[R] b) = Coalgebra.counit (R := R) a • b := by
  simp [epsId]

theorem epsId_coaction (π : A →ₐc[R] B) (a : A) : epsId R A B (coaction π a) = π a := by
  have key : ∀ z : A ⊗[R] A,
      epsId R A B (Algebra.TensorProduct.map (AlgHom.id R A) (π : A →ₐ[R] B) z) =
        π (TensorProduct.lid R A (Coalgebra.counit.rTensor A z)) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [LinearMap.rTensor_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [coaction_apply, key, Coalgebra.rTensor_counit_comul]
  simp

theorem apply_eq_zero_of_mem_hopfKer (π : A →ₐc[R] B) {a : A} (ha : a ∈ hopfKer π)
    (hε : Coalgebra.counit (R := R) a = 0) : π a = 0 := by
  rw [← epsId_coaction π a, coaction_eq_of_mem π ha, epsId_tmul, hε, zero_smul]

end HopfAlgebra.KerEqAug
p2m_reactivate "P2MW.S_HopfAlgebra_ker_eq_map_hopfKer_inf_ker_counit_of_surjective.HopfAlgebra P2MW.S_HopfAlgebra_ker_eq_map_hopfKer_inf_ker_counit_of_surjective.HopfAlgebra.KerEqAug"
p2m_reactivate "P2MW.S_HopfAlgebra_ker_eq_map_hopfKer_inf_ker_counit_of_surjective.HopfAlgebra"

open HopfAlgebra.KerEqAug in
theorem solution
    {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {A : Type} [CommRing A] [HopfAlgebra R A] [Module.Finite R A] [Module.Flat R A] [Coalgebra.IsCocomm R A]
    {B : Type} [CommRing B] [HopfAlgebra R B] [Module.Finite R B] [Module.Flat R B]
    (π : A →ₐc[R] B) (hπ : Function.Surjective π) :
    RingHom.ker (π : A →+* B) =
      Ideal.span ((HopfAlgebra.hopfKer π : Set A) ∩ (RingHom.ker (Bialgebra.counitAlgHom R A) : Set A)) := by
  have hset : ((HopfAlgebra.hopfKer π : Set A) ∩ (RingHom.ker (Bialgebra.counitAlgHom R A) : Set A)) =
      {a : A | a ∈ HopfAlgebra.hopfKer π ∧ Coalgebra.counit (R := R) a = 0} := by
    ext a
    simp only [Set.mem_inter_iff, SetLike.mem_coe, RingHom.mem_ker, Bialgebra.counitAlgHom_apply,
      Set.mem_setOf_eq]
  haveI : Algebra.FiniteType R A := Module.Finite.finiteType A
  have hG := (HopfAlgebra.isHopfGalois_and_faithfullyFlat_and_finiteType_hopfKer_of_surjective R A B π hπ).1
  have hle := (HopfAlgebra.isHopfGalois_iff_ker_le_span_of_surjective π hπ).mp hG
  apply le_antisymm
  · rw [hset]
    intro a ha
    exact hle ha
  · rw [Ideal.span_le]
    rintro a ⟨ha, hε⟩
    rw [SetLike.mem_coe, RingHom.mem_ker] at hε ⊢
    exact apply_eq_zero_of_mem_hopfKer π ha hε

end S_HopfAlgebra_ker_eq_map_hopfKer_inf_ker_counit_of_surjective
end P2MW
export P2MW.S_HopfAlgebra_ker_eq_map_hopfKer_inf_ker_counit_of_surjective (solution)
