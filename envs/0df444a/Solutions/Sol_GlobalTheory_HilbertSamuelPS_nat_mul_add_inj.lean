-- Prove2me | solution 1 for GlobalTheory.HilbertSamuelPS.nat_mul_add_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:30:47.684881+00:00
-- url     : https://prove2.me/submissions/836ce710-c62f-4933-9d5d-348032a3ad25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndependentOfDistinctValuationLikeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankLeCardValuesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankMulPowLeFinrankOfPowerSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
open GlobalTheory.HilbertSamuelPS
open MvPowerSeries
namespace GlobalTheory.HilbertSamuelPS
theorem _root_.solution {m x y x' y' : ℕ} (hy : y < m) (hy' : y' < m)
    (h : m * x + y = m * x' + y') : x = x' ∧ y = y' := by
  have hm : 0 < m := by omega
  have e1 : (m * x + y) / m = x := by rw [Nat.mul_add_div hm, Nat.div_eq_of_lt hy, add_zero]
  have e2 : (m * x' + y') / m = x' := by rw [Nat.mul_add_div hm, Nat.div_eq_of_lt hy', add_zero]
  have hx : x = x' := by rw [← e1, h, e2]
  subst hx
  exact ⟨rfl, by omega⟩
end GlobalTheory.HilbertSamuelPS
