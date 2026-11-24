-- Prove2me | solution 1 for GlobalTheory.RealWeil.exists_norm_toLp_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:39:07.528822+00:00
-- url     : https://prove2.me/submissions/dc7904df-de92-4eb6-bd79-5362e160938e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Theorems.Thm_GlobalTheory_RealWeil_norm_weightOp_pow_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap LineDeriv Matrix
open scoped Real RealInnerProductSpace ContDiff FourierTransform
open GlobalTheory GlobalTheory.RealWeil
variable {l : Type} [Fintype l]
variable [DecidableEq l]
namespace GlobalTheory.RealWeil
theorem _root_.solution :
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ f : Sch l, ‖f.toLp 1 volume‖ ≤ C * ‖((weightOp l ^ N) f).toLp 2 volume‖ := by
  set N := Module.finrank ℝ (EuclideanSpace ℝ l) + 1 with hN
  let u : EuclideanSpace ℝ l → ℂ := fun x => ((((1 + ‖x‖ ^ 2) ^ N)⁻¹ : ℝ) : ℂ)
  have hun : ∀ x, ‖u x‖ = ((1 + ‖x‖ ^ 2) ^ N)⁻¹ := fun x => by
    simp only [u]
    rw [norm_real, Real.norm_of_nonneg (by positivity)]
  have hc : Continuous u := by
    refine continuous_ofReal.comp (Continuous.inv₀ (by fun_prop) fun x => by positivity)
  have hu : MemLp u (ENNReal.ofReal 2) volume := by
    rw [show ENNReal.ofReal 2 = 2 by simp, memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable]
    have := integrable_rpow_neg_one_add_norm_sq (E := EuclideanSpace ℝ l) (μ := volume) (r := 4 * N)
      (by rw [hN]; push_cast; have := Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ (EuclideanSpace ℝ l)); linarith)
    refine this.congr (.of_forall fun x => ?_)
    simp only [hun]
    rw [show -(4 * (N : ℝ)) / 2 = -((N * 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_neg (by positivity),
      Real.rpow_natCast, pow_mul, inv_pow]
  refine ⟨N, (∫ x, ‖u x‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ),
    Real.rpow_nonneg (integral_nonneg fun x => by positivity) _, fun f => ?_⟩
  have := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hu (((weightOp l ^ N) f).memLp _ volume)
  rw [norm_toLp_one, norm_toLp' (by simp) (by simp)]
  refine le_trans (le_of_eq ?_) (this.trans (le_of_eq (by simp)))
  refine integral_congr_ae (.of_forall fun x => ?_)
  simp only [hun, norm_weightOp_pow_apply]
  field_simp
end GlobalTheory.RealWeil
