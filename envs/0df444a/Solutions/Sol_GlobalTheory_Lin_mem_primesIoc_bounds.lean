-- Prove2me | solution 1 for GlobalTheory.Lin.mem_primesIoc_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:43:59.061279+00:00
-- url     : https://prove2.me/submissions/2e213832-e17d-4f2d-a0df-d222480bdf99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumPrimesIocEqSumIndicator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.Lin
namespace GlobalTheory.Lin
theorem _root_.solution {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) {p : ℕ} (hp : p ∈ primesIoc x y) :
    x < p ∧ (p : ℝ) ≤ y := by
  simp only [primesIoc, Finset.mem_filter, Finset.mem_Ioc] at hp
  exact ⟨(Nat.floor_lt hx).mp hp.1.1, (Nat.le_floor_iff (hx.trans hxy)).mp hp.1.2⟩
end GlobalTheory.Lin
