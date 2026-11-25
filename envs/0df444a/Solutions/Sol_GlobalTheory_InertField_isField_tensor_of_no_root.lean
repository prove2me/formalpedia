-- Prove2me | solution 1 for GlobalTheory.InertField.isField_tensor_of_no_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:54:44.062737+00:00
-- url     : https://prove2.me/submissions/71efe6e4-0422-487d-bdc7-fa7a5be95777

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IsFieldAdicCompletionTensorOfInert
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open scoped TensorProduct
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Polynomial
open GlobalTheory GlobalTheory.InertField
namespace GlobalTheory.InertField
theorem _root_.solution {F K E : Type} [Field F] [Field K] [Field E] [Algebra F K] [Algebra F E]
    (h2 : Module.finrank F E = 2) (a : E) (ha : ∀ x : F, algebraMap F E x ≠ a) (b c : F)
    (hq : a ^ 2 + algebraMap F E b * a + algebraMap F E c = 0)
    (hK : ∀ x : K, x ^ 2 + algebraMap F K b * x + algebraMap F K c ≠ 0) : IsField (K ⊗[F] E) := by
  have hli : LinearIndependent F ![(1 : E), a] := by
    rw [LinearIndependent.pair_iff' one_ne_zero]
    intro x hx
    exact ha x (by rw [Algebra.algebraMap_eq_smul_one, hx])
  let B := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])
  have hB : ⇑B = ![(1 : E), a] := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  let B' := Algebra.TensorProduct.basis K B
  set α : K ⊗[F] E := (1 : K) ⊗ₜ[F] a with hα
  let ι := algebraMap K (K ⊗[F] E)
  have hιF : ∀ x : F, ι (algebraMap F K x) = (1 : K) ⊗ₜ[F] algebraMap F E x := fun x => by
    rw [← IsScalarTower.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply']
  have hq' : α ^ 2 + ι (algebraMap F K b) * α + ι (algebraMap F K c) = 0 := by
    have := congrArg (Algebra.TensorProduct.includeRight : E →ₐ[F] K ⊗[F] E) hq
    rw [map_add, map_add, map_mul, map_pow, map_zero] at this
    rw [hιF, hιF]
    exact this
  refine ⟨exists_pair_ne _, mul_comm, fun {z} hz => ?_⟩
  obtain ⟨x, y, rfl⟩ : ∃ x y : K, z = ι x + ι y * α := by
    refine ⟨B'.repr z 0, B'.repr z 1, ?_⟩
    have h := B'.sum_repr z
    rw [Fin.sum_univ_two] at h
    have h0 : B' 0 = 1 := by simp [B', hB, Algebra.TensorProduct.one_def]
    have h1 : B' 1 = α := by simp [B', hB, hα]
    rw [h0, h1, Algebra.smul_def, Algebra.smul_def, mul_one] at h
    exact h.symm
  have hN : x ^ 2 - algebraMap F K b * x * y + algebraMap F K c * y ^ 2 ≠ 0 := by
    intro hN
    by_cases hy : y = 0
    · subst hy
      have : x = 0 := by simpa using hN
      subst this
      simp at hz
    · apply hK (-x / y)
      field_simp
      linear_combination hN
  refine ⟨ι (x ^ 2 - algebraMap F K b * x * y + algebraMap F K c * y ^ 2)⁻¹ *
    (ι x - ι (algebraMap F K b) * ι y - ι y * α), ?_⟩
  have h1 := congrArg ι (mul_inv_cancel₀ hN)
  rw [map_mul, map_one] at h1
  set N := ι (x ^ 2 - algebraMap F K b * x * y + algebraMap F K c * y ^ 2)⁻¹
  simp only [map_add, map_sub, map_mul, map_pow] at h1
  linear_combination h1 - N * ι y ^ 2 * hq'
end GlobalTheory.InertField
