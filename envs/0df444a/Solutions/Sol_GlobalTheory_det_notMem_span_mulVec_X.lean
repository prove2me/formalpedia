-- Prove2me | solution 1 for GlobalTheory.det_notMem_span_mulVec_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:37:42.955973+00:00
-- url     : https://prove2.me/submissions/5f228fa3-cfa3-42a2-b40c-4c713c9ab85a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DetUpdateRowAlternatingMulVecMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MvPowerSeriesVariablesSyzygySocle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DetNotMemSpanMulVecOfSocle
import Theorems.Thm_GlobalTheory_det_notMem_span_mulVec_of_socle
import Theorems.Thm_GlobalTheory_mvPowerSeries_variables_syzygy_socle


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (k : Type) [Field k] (g N : ℕ) (a : Matrix (Fin g) (Fin g) (MvPowerSeries (Fin g) k)), (∀ i, (MvPowerSeries.X i : MvPowerSeries (Fin g) k) ^ N ∈ Ideal.span (Set.range (a.mulVec MvPowerSeries.X))) → a.det ∉ Ideal.span (Set.range (a.mulVec MvPowerSeries.X)) := by
  intro k _ g N a h
  obtain ⟨hsyz, hsoc⟩ := GlobalTheory.mvPowerSeries_variables_syzygy_socle k g MvPowerSeries.X (fun _ => rfl)
  refine det_notMem_span_mulVec_of_socle MvPowerSeries.X hsyz (hsoc N) a fun i => ?_
  rw [pow_succ]
  exact Ideal.mul_mem_right _ _ (h i)
end GlobalTheory
