-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure.heightZeroOnFractions_of_additive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:00:36.570048+00:00
-- url     : https://prove2.me/submissions/771a6cda-67a9-49f5-b952-51ae30c73fcf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_SphereBlockLogMean

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory NumberField MvPolynomial
open scoped ENNReal NNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure
namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure
theorem _root_.solution (h : HeightZeroAdditive) : HeightZeroOnFractions := by
  intro K _ _ B N a b a' b' p q p' q' hp hq hp' hq' ha hb ha' hb' e
  have h1 := h K B N a b' p q' hp hq' ha hb'
  have h2 := h K B N a' b p' q hp' hq ha' hb
  rw [e] at h1
  linarith
end GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure
