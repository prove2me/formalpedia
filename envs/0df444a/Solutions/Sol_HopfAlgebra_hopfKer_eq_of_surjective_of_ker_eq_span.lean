-- Prove2me | solution 1 for HopfAlgebra.hopfKer_eq_of_surjective_of_ker_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/90e54227-4aa6-5521-ab97-74c5726c7697

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Theorems.Thm_HopfAlgebra_faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem
import Theorems.Thm_HopfAlgebra_exists_algEquiv_subalgebraTensor_tensorQuotient_of_comul_mem_span
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_hopfKer_eq_of_surjective_of_ker_eq_span
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul"

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace K6bBody

private theorem exists_algebraMap_eq_of_tmul_one_eq_one_tmul
    {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
    [Module.FaithfullyFlat A S] {b : S} (hb : b ⊗ₜ[A] (1 : S) = (1 : S) ⊗ₜ[A] b) :
    ∃ a : A, algebraMap A S a = b := by
  have key : (Submodule.span A ({b} : Set S)).baseChange S ≤
      (Submodule.span A ({1} : Set S)).baseChange S := by
    rw [Submodule.baseChange_span, Submodule.baseChange_span, Set.image_singleton,
      Set.image_singleton, Submodule.span_le, Set.singleton_subset_iff, TensorProduct.mk_apply,
      TensorProduct.mk_apply, SetLike.mem_coe, ← hb]
    have : b ⊗ₜ[A] (1 : S) = b • ((1 : S) ⊗ₜ[A] (1 : S)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  rw [Submodule.baseChange_le_iff] at key
  have hb' : b ∈ Submodule.span A ({1} : Set S) := key (Submodule.subset_span rfl)
  rw [Submodule.mem_span_singleton] at hb'
  obtain ⟨a, ha⟩ := hb'
  exact ⟨a, by rw [Algebra.algebraMap_eq_smul_one, ha]⟩

end K6bBody

open K6bBody in
theorem solution
    {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
    (K : Subalgebra k H)
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (hS : ∀ x ∈ K, HopfAlgebra.antipode k x ∈ K)
    {B : Type w} [CommRing B] [Bialgebra k B] (q : H →ₐc[k] B) (hq : Function.Surjective q)
    (hker : RingHom.ker (q : H →+* B) =
      Ideal.span {x : H | x ∈ K ∧ Coalgebra.counit (R := k) x = 0}) :
    HopfAlgebra.hopfKer q = K := by

  set J : Ideal H := Ideal.span {x : H | x ∈ K ∧ Coalgebra.counit (R := k) x = 0}

  have hqK : ∀ b ∈ K, q b = algebraMap k B (Coalgebra.counit (R := k) b) := by
    intro b hb
    have hmem : b - algebraMap k H (Coalgebra.counit (R := k) b) ∈ RingHom.ker (q : H →+* B) := by
      rw [hker]
      refine Ideal.subset_span ⟨K.sub_mem hb (K.algebraMap_mem _), ?_⟩
      rw [map_sub, Bialgebra.counit_algebraMap, sub_self]
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hmem
    have h2 : (q : H →+* B) (algebraMap k H (Coalgebra.counit (R := k) b)) =
        algebraMap k B (Coalgebra.counit (R := k) b) := by
      rw [RingHom.coe_coe, AlgHomClass.commutes]
    rw [← h2, ← hmem]; rfl
  apply le_antisymm
  ·
    intro h hh
    haveI : Module.FaithfullyFlat ↥K H :=
      HopfAlgebra.faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem K hΔ hS
    obtain ⟨β, hβ⟩ :=
      HopfAlgebra.exists_algEquiv_subalgebraTensor_tensorQuotient_of_comul_mem_span K hΔ
    suffices htm : h ⊗ₜ[↥K] (1 : H) = (1 : H) ⊗ₜ[↥K] h by
      obtain ⟨a, ha⟩ := exists_algebraMap_eq_of_tmul_one_eq_one_tmul htm
      rw [← ha]
      exact a.2
    apply β.injective
    rw [hβ, hβ, Bialgebra.comul_one, map_one, mul_one, ← Algebra.TensorProduct.one_def, one_mul]

    have hJ : RingHom.ker (q : H →ₐ[k] B) = J := by
      rw [← hker]
      ext x
      simp [RingHom.mem_ker]
    have hq' : Function.Surjective (q : H →ₐ[k] B) := hq
    let e : (H ⧸ J) ≃ₐ[k] B :=
      (Ideal.quotientEquivAlgOfEq k hJ.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hq')
    have he : ∀ x : H, e (Ideal.Quotient.mk J x) = q x := by
      intro x
      simp only [e, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
        Ideal.quotientKerAlgEquivOfSurjective_mk, BialgHom.coe_toAlgHom]
    apply (Algebra.TensorProduct.congr (AlgEquiv.refl : H ≃ₐ[k] H) e).injective
    have hcomp : ∀ t : H ⊗[k] H,
        Algebra.TensorProduct.congr (AlgEquiv.refl : H ≃ₐ[k] H) e
          (Algebra.TensorProduct.map (AlgHom.id k H) (Ideal.Quotient.mkₐ k J) t) =
        Algebra.TensorProduct.map (AlgHom.id k H) (q : H →ₐ[k] B) t := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul x y =>
        rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.congr_apply,
          Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, Ideal.Quotient.mkₐ_eq_mk]
        simp only [AlgHom.coe_id, id_eq, AlgEquiv.coe_algHom, he, BialgHom.coe_toAlgHom]
        rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [hcomp, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
    simp only [AlgEquiv.coe_algHom, map_one]

    exact ((HopfAlgebra.mem_hopfKer_iff q h).1 hh).symm
  ·
    intro x hx
    rw [HopfAlgebra.mem_hopfKer_iff, HopfAlgebra.coaction_apply]

    have hagree : ∀ t ∈ Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b},
        Algebra.TensorProduct.map (AlgHom.id k H) (q : H →ₐ[k] B) t =
          LinearMap.lTensor H (Algebra.linearMap k B ∘ₗ Coalgebra.counit) t := by
      intro t ht
      induction ht using Submodule.span_induction with
      | mem t ht =>
        obtain ⟨a, ha, b, hb, rfl⟩ := ht
        rw [Algebra.TensorProduct.map_tmul, LinearMap.lTensor_tmul, LinearMap.comp_apply,
          Algebra.linearMap_apply, AlgHom.coe_id, id_eq, BialgHom.coe_toAlgHom, hqK b hb]
      | zero => simp only [map_zero]
      | add s t _ _ hs ht => simp only [map_add, hs, ht]
      | smul r t _ ht => simp only [map_smul, ht]
    rw [hagree _ (hΔ x hx), LinearMap.lTensor_comp, LinearMap.comp_apply,
      Coalgebra.lTensor_counit_comul, LinearMap.lTensor_tmul, Algebra.linearMap_apply, map_one]

end S_HopfAlgebra_hopfKer_eq_of_surjective_of_ker_eq_span
end P2MW
export P2MW.S_HopfAlgebra_hopfKer_eq_of_surjective_of_ker_eq_span (solution)
