-- Prove2me | solution 1 for GlobalTheory.SplitFlip.shellSum_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:31:01.194931+00:00
-- url     : https://prove2.me/submissions/f64a411c-1b81-4d88-8513-a3db5a248529

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitFlip
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A A' D : Type*} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
variable [MeasurableSpace k] [BorelSpace k]
omit [BorelSpace k]
namespace GlobalTheory.SplitFlip
theorem _root_.solution {a : ℕ} (μ : Measure (GL (Fin a) k)) (ϖ : kˣ) (ν : kˣ →* ℂˣ) (z c : ℂ)
    (φ : Matrix (Fin a) (Fin a) k → ℂ) : shellSum μ ϖ ν z (fun g => c * φ g) = c * shellSum μ ϖ ν z φ := by
  simp only [shellSum, shell, mul_finsum, mul_assoc, integral_const_mul]
end GlobalTheory.SplitFlip
