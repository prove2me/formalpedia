-- Prove2me | solution 1 for GlobalTheory.HeckeMellinOne.mellin_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:15:43.978257+00:00
-- url     : https://prove2.me/submissions/006813d5-8c43-4259-b1a8-686f9349b31a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralHeckeMellinGaussIntegrandEqProdGammaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypeProdNormSqEqAbsNormSpanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeMellinGaussIntegralNonzeroInteger
import Theorems.Thm_GlobalTheory_HeckeMellinOne_ofReal_prod_cpow
import Theorems.Thm_GlobalTheory_HeckeMellinOne_real_factor
import Theorems.Thm_GlobalTheory_HeckeMellinOne_complex_factor
import Theorems.Thm_GlobalTheory_HeckeMellinOne_real_prod_rpow
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_T_cmType_prod_norm_sq_eq_absNorm_span
import Theorems.Thm_GlobalTheory_T_integral_heckeMellinGaussIntegrand_eq_prod_gamma
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField MeasureTheory
open GlobalTheory GlobalTheory.HeckeMellinOne
namespace GlobalTheory.HeckeMellinOne
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ) (s : ℂ), 0 < s.re → ∀ α : 𝓞 K, α ≠ 0 → Integrable (GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (α : K))) ∧ 2 ^ Fintype.card I * ∫ y, GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (α : K)) y = GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.archFactor n s * GlobalTheory.HeckeStrip.wt φ n (α : K) * ((Ideal.absNorm (Ideal.span {α}) : ℕ) : ℂ) ^ (-s) ∧ ∫ y, ‖GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (α : K)) y‖ = (∏ i, (2 * Real.pi) ^ (-(s.re + (|n i| : ℝ) / 2)) * Real.Gamma (s.re + (|n i| : ℝ) / 2)) * ((Ideal.absNorm (Ideal.span {α}) : ℕ) : ℝ) ^ (-s.re) := by
  intro K _ _ _ I _ φ hφ n s hs α hα
  have hαK : (α : K) ≠ 0 := by exact_mod_cast hα
  have hv : ∀ i, GlobalTheory.HeckeTheta.emb φ (α : K) i ≠ 0 := fun i => (map_ne_zero (φ i)).2 hαK
  obtain ⟨hint, hI, hN⟩ := GlobalTheory.T.integral_heckeMellinGaussIntegrand_eq_prod_gamma I n s hs _ hv
  have hnorm := GlobalTheory.T.cmType_prod_norm_sq_eq_absNorm_span K I φ hφ α
  refine ⟨hint, ?_, ?_⟩
  · rw [hI, ← Complex.ofReal_natCast, ← hnorm, ofReal_prod_cpow _ _ (fun i => by positivity),
      ← Finset.card_univ, Finset.pow_card_mul_prod]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.archFactor GlobalTheory.HeckeStrip.wt
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [complex_factor _ (hv i)]
    simp only [GlobalTheory.HeckeTheta.emb]
    ring
  · rw [hN, ← hnorm, real_prod_rpow _ _ (fun i => by positivity), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    exact real_factor _ _ _ _ _ (norm_pos_iff.2 (hv i)) (by rw [Nat.cast_natAbs, Int.cast_abs])
end GlobalTheory.HeckeMellinOne
