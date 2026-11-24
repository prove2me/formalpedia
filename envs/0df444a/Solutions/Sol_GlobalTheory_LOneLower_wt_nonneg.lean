-- Prove2me | solution 1 for GlobalTheory.LOneLower.wt_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:40:04.724185+00:00
-- url     : https://prove2.me/submissions/63b88b60-6e08-4f9f-be7a-99a57f9d0de3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsLeNormLFunctionOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Filter Topology
open scoped ComplexOrder
open GlobalTheory GlobalTheory.LOneLower
namespace GlobalTheory.LOneLower
theorem _root_.solution {x : ℝ} (hx : 0 < x) : 0 ≤ wt x := by
  have := Real.add_one_le_exp x
  exact sub_nonneg.2 (inv_anti₀ hx (by linarith))
end GlobalTheory.LOneLower
