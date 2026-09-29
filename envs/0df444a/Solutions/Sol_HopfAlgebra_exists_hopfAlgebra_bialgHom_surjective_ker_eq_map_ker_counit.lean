-- Prove2me | solution 1 for HopfAlgebra.exists_hopfAlgebra_bialgHom_surjective_ker_eq_map_ker_counit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/260774aa-93e9-51a1-9f13-5eaaed1090f4

import Mathlib
import Theorems.Thm_HopfAlgebra_exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal_of_commRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_hopfAlgebra_bialgHom_surjective_ker_eq_map_ker_counit

universe u v w

open scoped TensorProduct

namespace Pen5K9a

open Coalgebra in

private theorem map_antipode {R : Type u} [CommRing R] {A : Type v} [CommRing A] [HopfAlgebra R A]
    {B : Type w} [CommRing B] [HopfAlgebra R B] (φ : A →ₐc[R] B) (a : A) :
    φ (HopfAlgebra.antipode R a) = HopfAlgebra.antipode R (φ a) := by
  open WithConv in
  suffices h : toConv ((φ : A →ₗ[R] B) ∘ₗ HopfAlgebra.antipode R) =
      toConv (HopfAlgebra.antipode R ∘ₗ (φ : A →ₗ[R] B)) by
    simpa using LinearMap.congr_fun (congrArg WithConv.ofConv h) a
  refine left_inv_eq_right_inv (a := toConv (φ : A →ₗ[R] B)) ?_ ?_
  ·
    refine WithConv.ext (LinearMap.ext fun x => ?_)
    rw [Coalgebra.Repr.convMul_apply (ℛ R x), LinearMap.convOne_apply]
    change (∑ i ∈ (ℛ R x).index, φ (HopfAlgebra.antipode R ((ℛ R x).left i)) * φ ((ℛ R x).right i)) = _
    simp only [← map_mul]
    rw [← map_sum, HopfAlgebra.sum_antipode_mul_eq_algebraMap_counit, AlgHomClass.commutes]
  ·
    refine WithConv.ext (LinearMap.ext fun x => ?_)
    rw [Coalgebra.Repr.convMul_apply (ℛ R x), LinearMap.convOne_apply]
    change (∑ i ∈ (ℛ R x).index, φ ((ℛ R x).left i) * HopfAlgebra.antipode R (φ ((ℛ R x).right i))) = _
    have key := HopfAlgebra.mul_antipode_lTensor_comul_apply (R := R) (φ x)
    rw [← CoalgHomClass.map_comp_comul_apply, ← (ℛ R x).eq, CoalgHomClass.counit_comp_apply] at key
    simpa [map_sum, TensorProduct.map_tmul, LinearMap.lTensor_tmul, LinearMap.mul'_apply] using key

end Pen5K9a

open Coalgebra in
theorem solution
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] [HopfAlgebra R A]
    {B : Type w} [CommRing B] [HopfAlgebra R B] (φ : A →ₐc[R] B) :
    ∃ (H : Type w) (_ : CommRing H) (_ : HopfAlgebra R H) (q : B →ₐc[R] H),
      Function.Surjective q ∧
      RingHom.ker (q : B →+* H) =
        Ideal.map (φ : A →ₐ[R] B) (RingHom.ker (Bialgebra.counitAlgHom R A)) ∧
      (Coalgebra.IsCocomm R B → Coalgebra.IsCocomm R H) ∧
      (Module.Finite R B → Module.Finite R H) := by
  classical
  set I : Ideal B := Ideal.map (φ : A →ₐ[R] B) (RingHom.ker (Bialgebra.counitAlgHom R A)) with hI

  have hgen : ∀ a : A, Coalgebra.counit (R := R) a = 0 → φ a ∈ I := fun a ha =>
    Ideal.mem_map_of_mem _ (by simpa [RingHom.mem_ker] using ha)

  have hcounit : ∀ b ∈ I, Coalgebra.counit (R := R) b = 0 := by
    have hle : I ≤ RingHom.ker (Bialgebra.counitAlgHom R B) := by
      refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
      simp only [RingHom.mem_ker, Bialgebra.counitAlgHom_apply] at ha
      simp [Ideal.mem_comap, RingHom.mem_ker, ha]
    intro b hb
    simpa [RingHom.mem_ker] using hle hb

  have hanti : ∀ b ∈ I, HopfAlgebraStruct.antipode (R := R) b ∈ I := by
    intro b hb
    refine Submodule.span_induction (p := fun b _ => HopfAlgebraStruct.antipode (R := R) b ∈ I) ?_ ?_ ?_ ?_ hb
    · rintro _ ⟨a, ha, rfl⟩
      have ha' : Coalgebra.counit (R := R) a = 0 := by simpa [RingHom.mem_ker] using ha
      change HopfAlgebra.antipode R (φ a) ∈ I
      rw [← Pen5K9a.map_antipode]
      exact hgen _ (by rw [HopfAlgebra.counit_antipode, ha'])
    · simp
    · intro x y _ _ hx hy
      simpa using I.add_mem hx hy
    · intro c x _ hx
      change HopfAlgebra.antipode R (c * x) ∈ I
      rw [HopfAlgebra.antipode_mul]
      exact I.mul_mem_right _ hx

  have hcomul : ∀ b ∈ I, Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)
      (Coalgebra.comul (R := R) b) = 0 := by

    let D : B →ₐ[R] (B ⧸ I) ⊗[R] (B ⧸ I) :=
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)).comp (Bialgebra.comulAlgHom R B)
    have hD : ∀ b, D b = Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)
        (Coalgebra.comul (R := R) b) := fun b => rfl
    have hle : I ≤ RingHom.ker D := by
      refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
      have ha' : Coalgebra.counit (R := R) a = 0 := by simpa [RingHom.mem_ker] using ha
      have hπ : ∀ a' : A, Coalgebra.counit (R := R) a' = 0 → Ideal.Quotient.mkₐ R I (φ a') = 0 := fun a' h =>
        (Ideal.Quotient.eq_zero_iff_mem).2 (hgen a' h)
      simp only [Ideal.mem_comap, RingHom.mem_ker, hD, BialgHom.coe_toAlgHom]

      rw [← CoalgHomClass.map_comp_comul_apply, ← (ℛ R a).eq]
      simp only [map_sum, TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, LinearMap.coe_coe]

      have hsplit : ∀ i ∈ (ℛ R a).index,
          Ideal.Quotient.mkₐ R I (φ ((ℛ R a).left i)) ⊗ₜ[R] Ideal.Quotient.mkₐ R I (φ ((ℛ R a).right i)) =
          (1 : B ⧸ I) ⊗ₜ[R] (Coalgebra.counit (R := R) ((ℛ R a).left i) • Ideal.Quotient.mkₐ R I (φ ((ℛ R a).right i))) := by
        intro i _
        have h0 : Ideal.Quotient.mkₐ R I (φ ((ℛ R a).left i - algebraMap R A (Coalgebra.counit ((ℛ R a).left i)))) = 0 :=
          hπ _ (by simp)
        rw [map_sub, map_sub, sub_eq_zero, AlgHomClass.commutes, AlgHomClass.commutes] at h0
        rw [h0, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.algebraMap_eq_smul_one]
      rw [Finset.sum_congr rfl hsplit, ← TensorProduct.tmul_sum]
      simp only [← map_smul, ← map_sum, Coalgebra.sum_counit_smul, hπ a ha', TensorProduct.tmul_zero]
    intro b hb
    simpa [RingHom.mem_ker, hD] using hle hb
  obtain ⟨H, _, _, q, hq, hker, hcc, hfin, -⟩ :=
    HopfAlgebra.exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal_of_commRing I hcomul hcounit hanti
  exact ⟨H, inferInstance, inferInstance, q, hq, hker, hcc, hfin⟩

end S_HopfAlgebra_exists_hopfAlgebra_bialgHom_surjective_ker_eq_map_ker_counit
end P2MW
export P2MW.S_HopfAlgebra_exists_hopfAlgebra_bialgHom_surjective_ker_eq_map_ker_counit (solution)
