-- Prove2me | solution 1 for GlobalTheory.TorusElliptic.norm_ch
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:34:05.500534+00:00
-- url     : https://prove2.me/submissions/4d99503f-8040-4346-b7c4-4c1f442a6dc6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsRapidFourierSeriesOfIntPeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ContDiffAndFderivTsumFourierOfRapid
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FourierCoeffEqZeroOfTsumEqZeroFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorusEllipticSystemSolvable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
open GlobalTheory
open GlobalTheory.TorusElliptic
namespace GlobalTheory.TorusElliptic
theorem _root_.solution {n : ℕ} (ν : Fin n → ℤ) (x : Fin n → ℝ) : ‖ch ν x‖ = 1 := by
  have : (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ)) = ((2 * π * ∑ k, (ν k : ℝ) * x k : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [ch, this, Complex.norm_exp_ofReal_mul_I]
end GlobalTheory.TorusElliptic
