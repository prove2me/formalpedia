-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure.gaussAbsValue_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:55:21.329973+00:00
-- url     : https://prove2.me/submissions/73ed6e6f-e8e9-4bef-9ec3-1226ac720dab

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
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure
theorem _root_.solution {ι : Type} (w : FinitePlace K) {ω : MvPolynomial ι K}
    (h : ω ≠ 0) : 0 < gaussAbsValue w ω := by
  obtain ⟨d, hd, e⟩ := exists_gaussAbsValue_eq w h
  rw [e]
  exact FinitePlace.pos_iff.2 (mem_support_iff.1 hd)
end GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure
