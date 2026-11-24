-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.TermSmooth.ne_zero_of_mem_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:26:14.138172+00:00
-- url     : https://prove2.me/submissions/355a2659-cadc-4528-80b9-21805b92299f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffOnHeckeEisensteinFourierTerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermSmooth
namespace GlobalTheory.HeckeTwo.TermSmooth
theorem _root_.solution {y₀ y : ℝ} (hy₀ : y₀ ≠ 0) (hy : y ∈ Metric.ball y₀ (|y₀| / 2)) : y ≠ 0 := by
  rintro rfl
  rw [Metric.mem_ball, Real.dist_eq, zero_sub, abs_neg] at hy
  have : 0 < |y₀| := abs_pos.2 hy₀
  linarith
end GlobalTheory.HeckeTwo.TermSmooth
