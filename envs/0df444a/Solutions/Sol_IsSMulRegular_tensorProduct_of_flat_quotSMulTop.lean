-- Prove2me | solution 1 for IsSMulRegular.tensorProduct_of_flat_quotSMulTop
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/99a36000-59d1-5466-a9f0-7d0b40923646

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsSMulRegular_tensorProduct_of_flat_quotSMulTop

set_option autoImplicit false

open scoped TensorProduct Pointwise

universe u v w

namespace E83Aux

open Function TensorProduct

theorem lTensor_injective_of_flat_quotient {A : Type*} [CommRing A] (I : Ideal A)
    {N₁ N₂ N₃ : Type*} [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃]
    [Module A N₁] [Module A N₂] [Module A N₃]
    [Module (A ⧸ I) N₁] [Module (A ⧸ I) N₂] [Module (A ⧸ I) N₃]
    [IsScalarTower A (A ⧸ I) N₁] [IsScalarTower A (A ⧸ I) N₂] [IsScalarTower A (A ⧸ I) N₃]
    [Module.Flat (A ⧸ I) N₃]
    (g : N₁ →ₗ[A] N₂) (f : N₂ →ₗ[A] N₃) (hg : Injective g) (hf : Surjective f)
    (hfg : Exact g f) (M : Type*) [AddCommGroup M] [Module A M] :
    Injective (g.lTensor M) := by
  have h : Surjective (algebraMap A (A ⧸ I)) := Ideal.Quotient.mk_surjective
  let g' : N₁ →ₗ[A ⧸ I] N₂ := g.extendScalarsOfSurjective h
  let f' : N₂ →ₗ[A ⧸ I] N₃ := f.extendScalarsOfSurjective h
  have key : Injective (g'.lTensor ((A ⧸ I) ⊗[A] M)) :=
    LinearMap.lTensor_injective_of_exact_of_flat f' hf g' hg hfg _
  let e₁ : M ⊗[A] N₁ ≃ₗ[A] ((A ⧸ I) ⊗[A] M) ⊗[A ⧸ I] N₁ :=
    TensorProduct.comm A M N₁ ≪≫ₗ
      ((AlgebraTensorModule.cancelBaseChange A (A ⧸ I) (A ⧸ I) N₁ M).symm ≪≫ₗ
        TensorProduct.comm (A ⧸ I) N₁ ((A ⧸ I) ⊗[A] M)).restrictScalars A
  let e₂ : M ⊗[A] N₂ ≃ₗ[A] ((A ⧸ I) ⊗[A] M) ⊗[A ⧸ I] N₂ :=
    TensorProduct.comm A M N₂ ≪≫ₗ
      ((AlgebraTensorModule.cancelBaseChange A (A ⧸ I) (A ⧸ I) N₂ M).symm ≪≫ₗ
        TensorProduct.comm (A ⧸ I) N₂ ((A ⧸ I) ⊗[A] M)).restrictScalars A
  have hcomp : (e₂ : M ⊗[A] N₂ →ₗ[A] ((A ⧸ I) ⊗[A] M) ⊗[A ⧸ I] N₂) ∘ₗ g.lTensor M =
      (g'.lTensor ((A ⧸ I) ⊗[A] M)).restrictScalars A ∘ₗ
        (e₁ : M ⊗[A] N₁ →ₗ[A] ((A ⧸ I) ⊗[A] M) ⊗[A ⧸ I] N₁) := by
    apply TensorProduct.ext'
    intro m n
    rfl
  have hinj : Injective ((e₂ : M ⊗[A] N₂ →ₗ[A] ((A ⧸ I) ⊗[A] M) ⊗[A ⧸ I] N₂) ∘ₗ g.lTensor M) := by
    rw [hcomp, LinearMap.coe_comp]
    exact key.comp e₁.injective
  rw [LinearMap.coe_comp] at hinj
  exact hinj.of_comp

theorem smul_tensor_quotSMulTop_eq_zero {A : Type*} [CommRing A] (t : A)
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (x : M ⊗[A] QuotSMulTop t N) : t • x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero]
  | tmul m n =>
    have hn : t • n = 0 := Module.isTorsionBy_quotient_element_smul N t (x := n)
    rw [smul_tmul', smul_tmul, hn, tmul_zero]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

theorem exists_eq_smul_of_tensor_smul_top {A : Type*} [CommRing A] (t : A)
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (x : M ⊗[A] ↥(t • (⊤ : Submodule A N))) :
    ∃ w : M ⊗[A] N, ((t • (⊤ : Submodule A N)).subtype.lTensor M) x = t • w := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [map_zero, smul_zero]⟩
  | tmul m s =>
    obtain ⟨s, hs⟩ := s
    obtain ⟨n, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hs
    exact ⟨m ⊗ₜ n, by rw [LinearMap.lTensor_tmul, Submodule.subtype_apply, tmul_smul]⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, ha, hb, smul_add]⟩

end E83Aux

namespace E83Aux

open Function TensorProduct

theorem isSMulRegular_tensor_of_presentation
    {A : Type*} [CommRing A] (t : A) {B : Type*} [AddCommGroup B] [Module A B]
    {M : Type*} [AddCommGroup M] [Module A M]
    {S : Type*} [AddCommGroup S] [Module A S] {F : Type*} [AddCommGroup F] [Module A F]
    [Module.Flat A F] (ι : S →ₗ[A] F) (π : F →ₗ[A] B) (hι : Injective ι) (hπ : Surjective π)
    (hιπ : Exact ι π)
    (htB : IsSMulRegular B t) (htM : IsSMulRegular M t)
    [Module.Flat (A ⧸ Ideal.span {t}) (QuotSMulTop t B)] :
    IsSMulRegular (M ⊗[A] B) t := by

  have h0ι : Exact (0 : S →ₗ[A] S) ι := by
    rw [LinearMap.exact_zero_iff_injective]
    exact hι
  have hbar := QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last
    (r := t) h0ι hιπ htB
  rw [map_zero] at hbar
  have hι' : Injective (QuotSMulTop.map t ι) :=
    (LinearMap.exact_zero_iff_injective _ _).mp hbar
  have hιπ' : Exact (QuotSMulTop.map t ι) (QuotSMulTop.map t π) := QuotSMulTop.map_exact t hιπ hπ
  have hπ' : Surjective (QuotSMulTop.map t π) := QuotSMulTop.map_surjective t hπ

  have hkey : Injective ((QuotSMulTop.map t ι).lTensor M) :=
    lTensor_injective_of_flat_quotient (Ideal.span {t}) (QuotSMulTop.map t ι)
      (QuotSMulTop.map t π) hι' hπ' hιπ' M

  have hπM : Surjective (π.lTensor M) := LinearMap.lTensor_surjective M hπ
  have hιπM : Exact (ι.lTensor M) (π.lTensor M) := lTensor_exact M hιπ hπ
  have hregF : IsSMulRegular (M ⊗[A] F) t := htM.rTensor F

  refine IsSMulRegular.of_right_eq_zero_of_smul fun y hy => ?_
  obtain ⟨z, rfl⟩ := hπM y
  have htz : t • z ∈ LinearMap.ker (π.lTensor M) := by
    rw [LinearMap.mem_ker, map_smul, hy]
  rw [hιπM.linearMap_ker_eq] at htz
  obtain ⟨w, hw⟩ := htz
  have h1 : ((t • ⊤ : Submodule A F).mkQ.lTensor M) ∘ₗ ι.lTensor M =
      ((QuotSMulTop.map t ι).lTensor M) ∘ₗ ((t • ⊤ : Submodule A S).mkQ.lTensor M) := by
    rw [← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp, QuotSMulTop.map_comp_mkQ]
  have h3 : ((t • ⊤ : Submodule A S).mkQ.lTensor M) w = 0 := by
    apply hkey
    rw [map_zero, ← LinearMap.comp_apply, ← h1, LinearMap.comp_apply, hw, map_smul,
      smul_tensor_quotSMulTop_eq_zero]
  have h4 : w ∈ LinearMap.range ((t • ⊤ : Submodule A S).subtype.lTensor M) := by
    rw [← lTensor_mkQ]
    exact h3
  obtain ⟨w₀, rfl⟩ := h4
  obtain ⟨w', hw'⟩ := exists_eq_smul_of_tensor_smul_top t w₀
  rw [hw', map_smul] at hw
  have hz : ι.lTensor M w' = z := hregF hw
  rw [← hz]
  exact hιπM.apply_apply_eq_zero w'

end E83Aux

open Function in
theorem solution
    {A : Type u} [CommRing A] (t : A) {B : Type v} [AddCommGroup B] [Module A B]
    {M : Type w} [AddCommGroup M] [Module A M]
    (htA : IsSMulRegular A t) (htB : IsSMulRegular B t) (htM : IsSMulRegular M t)
    [Module.Flat (A ⧸ Ideal.span {t}) (QuotSMulTop t B)] :
    IsSMulRegular (M ⊗[A] B) t := by

  refine E83Aux.isSMulRegular_tensor_of_presentation
    (S := ↥(LinearMap.ker (Finsupp.linearCombination A (id : B → B)))) (F := B →₀ A) t
    (LinearMap.ker (Finsupp.linearCombination A (id : B → B))).subtype
    (Finsupp.linearCombination A (id : B → B)) ?_ ?_ ?_ htB htM
  · exact Submodule.injective_subtype _
  · exact Finsupp.linearCombination_id_surjective A B
  · exact LinearMap.exact_subtype_ker_map _

end S_IsSMulRegular_tensorProduct_of_flat_quotSMulTop
end P2MW
export P2MW.S_IsSMulRegular_tensorProduct_of_flat_quotSMulTop (solution)
