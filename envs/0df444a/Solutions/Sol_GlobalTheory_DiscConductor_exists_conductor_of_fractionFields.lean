-- Prove2me | solution 1 for GlobalTheory.DiscConductor.exists_conductor_of_fractionFields
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:43:35.47836+00:00
-- url     : https://prove2.me/submissions/7d808ddb-33e7-4228-8221-171d59545cd8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsBasisInFiniteDomainTraceMemStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FlatTensorEmbedsTensorFractionFieldsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsUnitMapOfMemNonZeroDivisorsTensorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IntegralOfFiniteBaseChangeImageStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiscrMulMemOfIsIntegral
import Theorems.Thm_GlobalTheory_DiscConductor_isIntegral_trace_of_isIntegral
import Theorems.Thm_GlobalTheory_DiscConductor_det_smul_eq_sum
import Theorems.Thm_GlobalTheory_T_exists_basis_of_integral_with_trace_in_base
import Theorems.Thm_GlobalTheory_T_exists_injective_tensor_into_tensor_fractionFields
import Theorems.Thm_GlobalTheory_T_isIntegral_of_monic_eval_tmul_map_eq_zero
import Theorems.Thm_P2M_GlobalTheory_T_isUnit_map_of_mem_nonZeroDivisors_tensor__ba12e47f1fb4


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Polynomial
open GlobalTheory GlobalTheory.DiscConductor
namespace GlobalTheory.DiscConductor
theorem _root_.solution
    (T U C F K L : Type) [CommRing T] [IsDomain T] [IsIntegrallyClosed T] [CharZero T]
    [CommRing U] [IsDomain U] [IsIntegrallyClosed U]
    [CommRing C] [IsDomain C] [Field F] [Field K] [Field L]
    [Algebra T U] [Algebra T C] [Algebra T F] [IsFractionRing T F]
    [Algebra C K] [IsFractionRing C K] [Algebra U L] [IsFractionRing U L]
    [Algebra T K] [Algebra F K] [IsScalarTower T C K] [IsScalarTower T F K]
    [Algebra T L] [Algebra F L] [IsScalarTower T U L] [IsScalarTower T F L]
    [Module.Flat T U] [Module.Finite T C] :
    ∃ d : T, d ≠ 0 ∧ ∀ c : FractionRing (U ⊗[T] C), IsIntegral (U ⊗[T] C) c →
      ∃ s : (U ⊗[T] C), algebraMap (U ⊗[T] C) (FractionRing (U ⊗[T] C)) s =
        algebraMap (U ⊗[T] C) (FractionRing (U ⊗[T] C)) (algebraMap T (U ⊗[T] C) d) * c := by
  classical
  obtain ⟨n, b, hbC, hbT⟩ := GlobalTheory.T.exists_basis_of_integral_with_trace_in_base T C F K
  obtain ⟨φ, hφi, hφ⟩ := GlobalTheory.T.exists_injective_tensor_into_tensor_fractionFields T U C F K L
  have hφu := GlobalTheory.T.isUnit_map_of_mem_nonZeroDivisors_tensor' T U C F K L φ hφi hφ
  choose t ht using hbT
  choose e he using hbC
  let Gt : Matrix (Fin n) (Fin n) T := Matrix.of t
  have hG : (algebraMap T F).mapMatrix Gt = Algebra.traceMatrix F b := by
    ext i j
    simp [Gt, ht, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  haveI : FiniteDimensional F K := Module.Finite.of_basis b
  haveI : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective T F)
  have hd : algebraMap T F Gt.det = (Algebra.traceMatrix F b).det := by
    rw [RingHom.map_det, hG]
  refine ⟨Gt.det, ?_, ?_⟩
  · intro h0
    apply Algebra.discr_not_zero_of_basis F b
    rw [Algebra.discr_def, ← hd, h0, map_zero]
  intro c hc
  let B : Module.Basis (Fin n) L (L ⊗[F] K) := b.baseChange L
  have hB : ∀ i, B i = 1 ⊗ₜ b i := fun i => Module.Basis.baseChange_apply L b i
  haveI : Module.Finite L (L ⊗[F] K) := Module.Finite.of_basis B
  have htr : ∀ x : K, Algebra.trace L (L ⊗[F] K) (1 ⊗ₜ x) = algebraMap F L (Algebra.trace F K x) := by
    intro x
    rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
      LinearMap.trace_baseChange]
  have htow : ∀ x : T, algebraMap F L (algebraMap T F x) = algebraMap U L (algebraMap T U x) := by
    intro x
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hBB : ∀ i j, algebraMap U L (algebraMap T U (t i j)) =
      Algebra.trace L (L ⊗[F] K) (B i * B j) := by
    intro i j
    rw [hB, hB, Algebra.TensorProduct.tmul_mul_tmul, one_mul, htr, ← ht, htow]
  let ψ : FractionRing (U ⊗[T] C) →+* L ⊗[F] K :=
    IsLocalization.lift (M := nonZeroDivisors (U ⊗[T] C)) (g := φ) (fun s => hφu s.1 s.2)
  have hψ : ∀ s, ψ (algebraMap (U ⊗[T] C) _ s) = φ s := fun s => IsLocalization.lift_eq _ s
  have hψi : Function.Injective ψ := by
    refine (RingHom.injective_iff_ker_eq_bot ψ).2 ((RingHom.ker_eq_bot_iff_eq_zero ψ).2 ?_)
    intro x hx
    obtain ⟨⟨s, r⟩, h⟩ := IsLocalization.surj (nonZeroDivisors (U ⊗[T] C)) x
    have h1 := congrArg ψ h
    rw [map_mul, hx, zero_mul, hψ] at h1
    have h2 : s = 0 := hφi (by rw [map_zero]; exact h1.symm)
    rw [h2, map_zero] at h
    exact (IsLocalization.map_units (FractionRing (U ⊗[T] C)) r).mul_left_eq_zero.1 h
  have hω : IsIntegral U (ψ c) := by
    obtain ⟨p, hp, hpc⟩ := hc
    refine GlobalTheory.T.isIntegral_of_monic_eval_tmul_map_eq_zero T U C F K L φ hφ (ψ c) p hp ?_
    have h1 := congrArg ψ hpc
    rw [hom_eval₂, map_zero] at h1
    have h2 : ψ.comp (algebraMap (U ⊗[T] C) _) = φ := RingHom.ext hψ
    rwa [h2] at h1
  have hBi : ∀ i, IsIntegral U (B i) := by
    intro i
    refine GlobalTheory.T.isIntegral_of_monic_eval_tmul_map_eq_zero T U C F K L φ hφ (B i) (X - Polynomial.C (1 ⊗ₜ e i))
      (monic_X_sub_C _) ?_
    rw [eval₂_sub, eval₂_X, eval₂_C, hφ, map_one, he, hB, sub_self]
  obtain ⟨v, hv⟩ := det_smul_eq_sum U L (L ⊗[F] K) (Fin n) B (ψ c)
    (fun i j => ⟨_, hBB i j⟩) (fun i => IsIntegrallyClosed.isIntegral_iff.1
      (isIntegral_trace_of_isIntegral U L (L ⊗[F] K) _ (hω.mul (hBi i))))
  have hdet : (Algebra.traceMatrix L B).det = algebraMap U L (algebraMap T U Gt.det) := by
    rw [RingHom.map_det, RingHom.map_det]
    congr 1
    ext i j
    simp [Gt, hBB, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  refine ⟨∑ j, v j ⊗ₜ e j, hψi ?_⟩
  rw [map_mul, hψ, hψ, map_sum, Algebra.TensorProduct.algebraMap_apply, hφ, map_one, ← hdet]
  have h1 : ((Algebra.traceMatrix L B).det ⊗ₜ[F] (1 : K)) * ψ c =
      (Algebra.traceMatrix L B).det • ψ c := by
    rw [Algebra.smul_def]; rfl
  rw [h1, hv]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hφ, he, hB, smul_tmul', smul_eq_mul, mul_one]
end GlobalTheory.DiscConductor
