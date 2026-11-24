-- Prove2me | solution 1 for GlobalTheory.HilbFam.hasSum_iterD_gval_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:26:01.333726+00:00
-- url     : https://prove2.me/submissions/e85df66f-3ed7-4336-b69f-a4fd5b390a9b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedDerivZeroEqLaguerreDerivativePolynomialVStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedPartialDerivProdOneVarAtZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedPartialDerivConstMulReindexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumIteratedComplexPartialDerivTermwiseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSummableBoundHilbertEisensteinTermsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumHilbertEisensteinMovedPointStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRadiusMoebiusPerturbationUpperHalfPlaneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumIteratedDerivHilbertEisensteinSplitLattice
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_T_exists_radius_moebius_perturbation_upperHalfPlane
import Theorems.Thm_GlobalTheory_T_exists_summable_bound_hilbert_eisenstein_terms
import Theorems.Thm_GlobalTheory_T_hasSum_hilbertEisenstein_movedPoint
import Theorems.Thm_GlobalTheory_T_hasSum_iteratedComplexPartialDeriv_termwise
import Theorems.Thm_GlobalTheory_T_iteratedDeriv_zero_eq_laguerreDerivativePolynomialValue
import Theorems.Thm_GlobalTheory_T_iteratedPartialDeriv_const_mul_reindex
import Theorems.Thm_GlobalTheory_T_iteratedPartialDeriv_prod_oneVar_at_zero
import Theorems.Thm_GlobalTheory_WeightTwoSum_dz_apply
import Theorems.Thm_GlobalTheory_WeightTwoSum_dzbar_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub
attribute [local simp] GlobalTheory.WeightTwoSum.dz_apply
attribute [local simp] GlobalTheory.WeightTwoSum.dzbar_apply



set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory GlobalTheory.HilbFam
namespace GlobalTheory.HilbFam
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t : ℂ) (u : List (Emb F)), Even k → IsCoef k 𝔞 𝔟 a₀ a → 0 < τ.im → HasSum (fun ξ : F ↦ a ξ * eTr (ξ * x) * Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) * ∏ i : Emb F, lag k (u.count i) c ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t)) (iterD u (fun z ↦ (cK F k : ℂ) * gval k (split 𝔞 𝔟 x) (fun i ↦ τ + z i * (c * τ + t)) (fun i ↦ 1 + z i * c)) 0 / ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * (omegaFactor 𝔞 : ℂ)) ^ k) := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x τ c t u hk ha hτ
  obtain ⟨r, hr, hrad⟩ := GlobalTheory.T.exists_radius_moebius_perturbation_upperHalfPlane τ c t hτ
  obtain ⟨M, hM, hbd⟩ := GlobalTheory.T.exists_summable_bound_hilbert_eisenstein_terms F k 𝔞 𝔟 a₀ a x τ c t ha hτ
  set D : ℂ := ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * (omegaFactor 𝔞 : ℂ)) ^ k with hD
  set G : (Emb F → ℂ) → ℂ := fun z ↦ (cK F k : ℂ) * gval k (split 𝔞 𝔟 x) (fun i ↦ τ + z i * (c * τ + t)) (fun i ↦ 1 + z i * c) with hG
  have hcoord : ∀ z ∈ Metric.ball (0 : Emb F → ℂ) r, ∀ i, ‖z i‖ < r := fun z hz i ↦
    (norm_le_pi_norm z i).trans_lt (mem_ball_zero_iff.1 hz)
  have hne : ∀ w : ℂ, ‖w‖ < r → 1 + w * c ≠ 0 := fun w hw h ↦ by
    have := (hrad w hw).1
    rw [h, norm_zero] at this
    linarith
  have hψ : ∀ y : ℂ, DifferentiableOn ℂ (fun w : ℂ ↦ (1 + w * c)⁻¹ ^ k * Complex.exp (y * w / (1 + w * c))) (Metric.ball 0 r) := by
    intro y w hw
    have h0 := hne w (mem_ball_zero_iff.1 hw)
    have h1 : DifferentiableAt ℂ (fun w : ℂ ↦ 1 + w * c) w := by fun_prop
    have h2 : DifferentiableAt ℂ (fun w : ℂ ↦ y * w) w := by fun_prop
    exact (((h1.inv h0).pow k).mul (h2.div h1 h0).cexp).differentiableWithinAt
  have key := GlobalTheory.T.hasSum_iteratedComplexPartialDeriv_termwise (Emb F) F u r
    (fun ξ z ↦ a ξ * eTr (ξ * x) * Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) * ∏ i : Emb F, ((1 + z i * c)⁻¹ ^ k * Complex.exp ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t * z i / (1 + z i * c))))
    (fun z ↦ D⁻¹ * G z) M hr hM
    (fun ξ z hz ↦ by
      refine (DifferentiableAt.const_mul ?_ _).differentiableWithinAt
      refine (HasFDerivAt.finset_prod (𝕜 := ℂ) (u := (Finset.univ : Finset (Emb F)))
        (g := fun i (z : Emb F → ℂ) ↦ (1 + z i * c)⁻¹ ^ k * Complex.exp ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t * z i / (1 + z i * c)))
        (fun i _ ↦ DifferentiableAt.hasFDerivAt ?_)).differentiableAt
      have h1 := ((hψ ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t)).differentiableAt
        (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 (hcoord z hz i))))
      exact h1.comp z (differentiableAt_apply (𝕜 := ℂ) i z))
    (fun ξ z hz ↦ hbd ξ z (fun i ↦ hrad _ (hcoord z hz i)))
    (fun z hz ↦ by
      have := GlobalTheory.T.hasSum_hilbertEisenstein_movedPoint F k 𝔞 𝔟 a₀ a x τ c t z hk ha (fun i ↦ ⟨hne _ (hcoord z hz i), by
        have := (hrad _ (hcoord z hz i)).2
        linarith⟩)
      rw [div_eq_inv_mul] at this
      exact this)
  have hc := GlobalTheory.T.iteratedPartialDeriv_const_mul_reindex (Emb F) (Emb F) (Equiv.refl _) u G D⁻¹ 0
  simp only [Equiv.refl_symm, Equiv.coe_refl, id_eq, List.map_id, List.map_id_fun] at hc
  have hc' : iterD u (fun z ↦ D⁻¹ * G z) 0 = iterD u G 0 / D := by
    rw [div_eq_inv_mul]; exact hc
  rw [hc'] at key
  convert key using 2 with ξ
  have := GlobalTheory.T.iteratedPartialDeriv_prod_oneVar_at_zero (Emb F) u r
    (fun i w ↦ (1 + w * c)⁻¹ ^ k * Complex.exp ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t * w / (1 + w * c)))
    (a ξ * eTr (ξ * x) * Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ)) hr
    (fun i ↦ hψ _)
  rw [this]
  congr 1
  exact Finset.prod_congr rfl (fun i _ ↦ (GlobalTheory.T.iteratedDeriv_zero_eq_laguerreDerivativePolynomialValue k _ c _).symm)
end GlobalTheory.HilbFam
