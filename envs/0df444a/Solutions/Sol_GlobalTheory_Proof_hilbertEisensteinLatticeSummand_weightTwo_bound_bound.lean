-- Prove2me | solution 1 for GlobalTheory.Proof.hilbertEisensteinLatticeSummand_weightTwo_bound.bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:54:08.02223+00:00
-- url     : https://prove2.me/submissions/a11a7d62-1cba-4649-857e-99a7a21d0f01

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinConstantTermPartDifferentiableOn
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleXSqAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinLatticeSummandWeightTwoBound
import Theorems.Thm_GlobalTheory_Proof_hilbertEisensteinLatticeSummand_weightTwo_bound_normSq_lower
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OmegaFactorization_latPt_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
open GlobalTheory GlobalTheory.Proof GlobalTheory.Proof.hilbertEisensteinLatticeSummand_weightTwo_bound
namespace GlobalTheory.Proof.hilbertEisensteinLatticeSummand_weightTwo_bound
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (σ : ℂ), 0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, ∃ C : ℝ, ∀ p : F × F, p ≠ 0 → ‖GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisTerm 2 σ z p‖ ≤ C * (∏ τ : F →+* ℝ, ((τ p.1) ^ 2 + (τ p.2) ^ 2)) ^ (-(1 + σ.re)) := by
  intro F _ _ σ hσ z hz
  set s := σ.re with hs
  let c : (F →+* ℝ) → ℝ := fun τ => 4 * Real.pi ^ 2 * ((z τ).im ^ 2 / (1 + ‖z τ‖ ^ 2))
  have hc : ∀ τ, 0 < c τ := fun τ => by have := hz τ; positivity
  refine ⟨(∏ τ, c τ) ^ (-(1 + s)), fun p hp => ?_⟩
  set P := ∏ τ : F →+* ℝ, ((τ p.1) ^ 2 + (τ p.2) ^ 2) with hPdef
  have hP : 0 < P := Finset.prod_pos fun τ _ => by
    by_contra h
    push_neg at h
    have h1 : τ p.1 = 0 := by nlinarith [sq_nonneg (τ p.1), sq_nonneg (τ p.2)]
    have h2 : τ p.2 = 0 := by nlinarith [sq_nonneg (τ p.1), sq_nonneg (τ p.2)]
    exact hp (Prod.ext ((map_eq_zero τ).1 h1) ((map_eq_zero τ).1 h2))
  set N := ∏ τ, ‖latPt z p τ‖ with hN
  have hNpos : 0 < N := Finset.prod_pos fun τ _ => norm_pos_iff.2 (latPt_ne_zero hz hp τ)
  have hterm : ‖eisTerm 2 σ z p‖ = (N ^ 2) ^ (-(1 + s)) := by
    unfold eisTerm
    simp only [norm_mul, norm_pow, norm_inv, norm_prod]
    rw [← hN, Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
    rw [show (N ^ 2 : ℝ) = N ^ (2 : ℝ) from (Real.rpow_two N).symm, ← Real.rpow_mul hNpos.le]
    have : (2 : ℝ) * (-(1 + s)) = -(2 : ℝ) + (-2 * σ).re := by simp [hs]; ring
    rw [this, Real.rpow_add hNpos, Real.rpow_neg hNpos.le, Real.rpow_two, inv_pow]
  have hlow : (∏ τ, c τ) * P ≤ N ^ 2 := by
    rw [hPdef, hN, ← Finset.prod_mul_distrib, ← Finset.prod_pow]
    refine Finset.prod_le_prod (fun τ _ => mul_nonneg (hc τ).le (by positivity)) fun τ _ => ?_
    have hl : ‖latPt z p τ‖ ^ 2 = 4 * Real.pi ^ 2 * ‖((τ p.1 : ℝ) : ℂ) + (τ p.2 : ℝ) * z τ‖ ^ 2 := by
      simp only [latPt, norm_mul, Complex.norm_I, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
      ring
    rw [hl, mul_assoc (4 * Real.pi ^ 2)]
    exact mul_le_mul_of_nonneg_left (normSq_lower (z τ) _ _) (by positivity)
  rw [hterm, ← Real.mul_rpow (Finset.prod_nonneg fun τ _ => (hc τ).le) hP.le]
  exact Real.rpow_le_rpow_of_nonpos (mul_pos (Finset.prod_pos fun τ _ => hc τ) hP) hlow (by linarith)
end GlobalTheory.Proof.hilbertEisensteinLatticeSummand_weightTwo_bound
