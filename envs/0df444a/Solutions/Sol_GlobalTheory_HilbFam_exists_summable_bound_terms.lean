-- Prove2me | solution 1 for GlobalTheory.HilbFam.exists_summable_bound_terms
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:49:46.019648+00:00
-- url     : https://prove2.me/submissions/b2f10e02-5f0c-4b7b-b829-c1c52b7336cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumRealEmbeddingsEqTraceTotallyReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSummableBoundHilbertEisensteinTerms
import Theorems.Thm_GlobalTheory_HilbFam_norm_qPow_eq_exp
import Theorems.Thm_GlobalTheory_HilbFam_norm_eTr_eq_one
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_HilbFam_sum_realEmb_eq_trace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory GlobalTheory.HilbFam
namespace GlobalTheory.HilbFam
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t : ℂ), IsCoef k 𝔞 𝔟 a₀ a → 0 < τ.im → ∃ M : F → ℝ, Summable M ∧ ∀ (ξ : F) (z : Emb F → ℂ), (∀ i, 1 / 2 ≤ ‖1 + z i * c‖ ∧ τ.im / 2 ≤ (τ + t * z i / (1 + z i * c)).im) → ‖a ξ * eTr (ξ * x) * Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) * ∏ i : Emb F, ((1 + z i * c)⁻¹ ^ k * Complex.exp ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t * z i / (1 + z i * c)))‖ ≤ M ξ := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x τ c t hc hτ
  obtain ⟨-, -, hpos, hsum⟩ := hc
  set w₀ : Emb F → ℂ := fun _ ↦ ((τ.im / 2 : ℝ) : ℂ) * Complex.I with hw₀
  have him : ∀ i, (w₀ i).im = τ.im / 2 := fun i ↦ by simp [hw₀]
  have hw : w₀ ∈ upperHalf F := fun i ↦ by rw [him i]; positivity
  have hs : Summable fun ξ : F ↦ ‖a ξ * qPow ξ w₀‖ := summable_norm_iff.mpr (hsum w₀ hw).summable
  refine ⟨fun ξ ↦ ((2 : ℝ) ^ k) ^ Fintype.card (Emb F) * ‖a ξ * qPow ξ w₀‖, hs.mul_left _, ?_⟩
  intro ξ z hz
  by_cases ha : a ξ = 0
  · simp [ha]
  have hnn : ∀ i : Emb F, 0 ≤ i ξ := fun i ↦ by
    by_cases h0 : ξ = 0
    · simp [h0]
    · exact ((hpos ξ h0 ha).2 i).le
  set w : Emb F → ℂ := fun i ↦ τ + t * z i / (1 + z i * c) with hwdef
  have key : Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) *
      ∏ i : Emb F, Complex.exp ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t * z i / (1 + z i * c)) = qPow ξ w := by
    rw [← Complex.exp_sum, ← Complex.exp_add, ← GlobalTheory.HilbFam.sum_realEmb_eq_trace F ξ]
    unfold qPow
    congr 1
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [hwdef]
    ring
  have hq : ‖qPow ξ w‖ ≤ ‖qPow ξ w₀‖ := by
    rw [norm_qPow_eq_exp, norm_qPow_eq_exp]
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine Finset.sum_le_sum fun i _ ↦ ?_
    rw [him i]
    exact mul_le_mul_of_nonneg_left (hz i).2 (hnn i)
  have hp : ‖∏ i : Emb F, (1 + z i * c)⁻¹ ^ k‖ ≤ ((2 : ℝ) ^ k) ^ Fintype.card (Emb F) := by
    rw [norm_prod, ← Finset.card_univ]
    have h := Finset.prod_le_prod (s := Finset.univ) (f := fun i : Emb F ↦ ‖(1 + z i * c)⁻¹ ^ k‖)
      (g := fun _ ↦ (2 : ℝ) ^ k) (fun i _ ↦ norm_nonneg _) (fun i _ ↦ by
        rw [norm_pow, norm_inv]
        apply pow_le_pow_left₀ (by positivity)
        have := (hz i).1
        rw [inv_le_comm₀ (by linarith) (by norm_num)]
        linarith)
    rwa [Finset.prod_const] at h
  have e : a ξ * eTr (ξ * x) * Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) * ∏ i : Emb F, ((1 + z i * c)⁻¹ ^ k * Complex.exp ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t * z i / (1 + z i * c))) =
      (∏ i : Emb F, (1 + z i * c)⁻¹ ^ k) * (eTr (ξ * x) * (a ξ * qPow ξ w)) := by
    rw [← key, Finset.prod_mul_distrib]
    ring
  rw [e, norm_mul, norm_mul, norm_eTr_eq_one, one_mul, norm_mul]
  show _ ≤ ((2 : ℝ) ^ k) ^ Fintype.card (Emb F) * ‖a ξ * qPow ξ w₀‖
  rw [norm_mul (a ξ)]
  gcongr
end GlobalTheory.HilbFam
