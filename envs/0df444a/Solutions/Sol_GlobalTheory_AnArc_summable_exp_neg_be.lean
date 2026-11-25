-- Prove2me | solution 1 for GlobalTheory.AnArc.summable_exp_neg_be
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:51:42.586741+00:00
-- url     : https://prove2.me/submissions/b44a1bc0-2fa3-4fc0-9b38-8f7a4e23e542

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SummableExpNegSumAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HasSumLocallyUniformlyOnTerm
import Theorems.Thm_GlobalTheory_AnArc_summable_exp_neg_size
import Theorems.Thm_GlobalTheory_AnArc_exists_size_sq_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution {δ : ℝ} (hδ : 0 < δ) (D : ℝ) :
    Summable fun μ => Real.exp (-(δ * A.be μ μ) + D * A.size μ) := by
  obtain ⟨C, hC, h⟩ := A.exists_size_sq_le
  refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun μ => ?_)
    (A.summable_exp_neg_size.mul_left (Real.exp (C * (D + 1) ^ 2 / (4 * δ))))
  rw [← Real.exp_add, Real.exp_le_exp]
  have h1 : (D + 1) * A.size μ - δ * A.be μ μ ≤ C * (D + 1) ^ 2 / (4 * δ) := by
    rw [le_div_iff₀ (by positivity), ← mul_le_mul_iff_right₀ hC]
    nlinarith [sq_nonneg (C * (D + 1) - 2 * δ * A.size μ), mul_le_mul_of_nonneg_left (h μ) (sq_nonneg (2 * δ))]
  linarith
end GlobalTheory.AnArc
