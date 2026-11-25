-- Prove2me | solution 1 for GlobalTheory.AnArc.exists_summable_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:36:52.652155+00:00
-- url     : https://prove2.me/submissions/76d750af-f1cf-4673-8a02-9c99bbe0a8ee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SummableExpNegSumAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HasSumLocallyUniformlyOnTerm
import Theorems.Thm_GlobalTheory_AnArc_summable_exp_neg_be
import Theorems.Thm_GlobalTheory_AnArc_exists_norm_term_le

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
variable {A} {T₀ : ℝ} (hT : A.IsConvLine T₀) {j : ℕ} {α : A.X} {th : (Fin A.gB → ℂ) → ℂ}
include hT
namespace GlobalTheory.AnArc
theorem _root_.solution (hj : j ≠ 0) (h : th ∈ A.Theta j α) {T₁ : ℝ} (h₁ : T₀ < T₁) (T₂ R : ℝ) :
    ∃ u : A.X → ℝ, Summable u ∧ ∀ μ (w : ℂ) (v : A.V), T₁ ≤ w.im → w.im ≤ T₂ → ‖v‖ ≤ R →
      ‖A.term j α th μ v * eTwoPi (w * A.exponent j α μ)‖ ≤ u μ := by
  obtain ⟨K, D, hK⟩ := exists_norm_term_le hT hj h h₁.le (max R (max |T₁| |T₂|))
  refine ⟨_, (A.summable_exp_neg_be (mul_pos Real.pi_pos (sub_pos.2 h₁)) D).mul_left K, fun μ w v a b c =>
    hK μ w v a ((abs_le_max_abs_abs a b).trans (le_max_right _ _)) (c.trans (le_max_left _ _))⟩
end GlobalTheory.AnArc
