-- Prove2me | solution 1 for GlobalTheory.IsSiegel.summable_norm_riemannThetaTerm_smul_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:57:04.636648+00:00
-- url     : https://prove2.me/submissions/46abbdfc-9b98-4be2-ad55-a0079a5cf7dc

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_PeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology MeasureTheory
open scoped Real
noncomputable section
open GlobalTheory
variable {ι κ : Type*}
variable [Fintype ι] [Fintype κ]
namespace GlobalTheory
namespace IsSiegel
theorem _root_.solution {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω)
    (a b : ι → ℝ) (v : ι → ℂ) :
    Summable fun n => ‖riemannThetaTerm a b Ω v n • riemannThetaForm a n‖ := by
  obtain ⟨c, hc, hY⟩ := posDef_exists_mul_dotProduct_le h.posDef
  refine ((summable_pow_mul_riemannThetaBound a hc ‖v‖ 1).mul_left (2 * π)).of_nonneg_of_le
    (fun _ => norm_nonneg _) fun n => ?_
  rw [norm_smul, pow_one, ← mul_assoc, mul_comm]
  exact mul_le_mul (norm_riemannThetaForm_le a n)
    (norm_riemannThetaTerm_le a b hY (abs_im_apply_le_norm v) n) (norm_nonneg _) (by positivity)
end IsSiegel
end GlobalTheory
