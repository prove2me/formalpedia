-- Prove2me | solution 1 for GlobalTheory.RealWeil.integral_norm_sq_eq_norm_toLp_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:50:12.660487+00:00
-- url     : https://prove2.me/submissions/36b39aba-97fa-4d7c-b270-08ef02769a74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MetaplecticOneParameterSchwartzIntertwining

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap Matrix
open GlobalTheory GlobalTheory.RealWeil
namespace GlobalTheory.RealWeil
theorem _root_.solution {l : Type} [Fintype l] (g : Sch l) :
    ∫ x, ‖g x‖ ^ 2 = ‖g.toLp 2 volume‖ ^ 2 := by
  rw [SchwartzMap.norm_toLp' (by simp) (by simp)]
  have h2 : (2 : ENNReal).toReal = 2 := by simp
  simp only [h2]
  have hn : 0 ≤ ∫ x, ‖g x‖ ^ (2 : ℝ) := integral_nonneg fun x => by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul hn]
  norm_num
end GlobalTheory.RealWeil
