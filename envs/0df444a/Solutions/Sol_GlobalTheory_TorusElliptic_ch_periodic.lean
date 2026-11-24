-- Prove2me | solution 1 for GlobalTheory.TorusElliptic.ch_periodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:34:04.600802+00:00
-- url     : https://prove2.me/submissions/69e94a6b-dafd-46d8-9dd3-760a4711e73f

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
theorem _root_.solution {n : ℕ} (ν μ : Fin n → ℤ) (x : Fin n → ℝ) :
    ch ν (x + fun k => (μ k : ℝ)) = ch ν x := by
  have : (2 * π * I * ∑ k, (ν k : ℂ) * (((x + fun k => (μ k : ℝ)) k : ℝ) : ℂ))
      = (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ)) + ((∑ k, ν k * μ k : ℤ) : ℂ) * (2 * π * I) := by
    simp only [Pi.add_apply]
    push_cast
    simp only [mul_add, Finset.sum_add_distrib]
    ring
  rw [ch, this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, ch]
end GlobalTheory.TorusElliptic
