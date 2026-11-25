-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure.finitePlace_eq_absNorm_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:55:15.06199+00:00
-- url     : https://prove2.me/submissions/8006d522-e0ed-4ba7-b7aa-f8ec0e66d737

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
theorem _root_.solution (w : FinitePlace K) {c : K} (hc : c ≠ 0) :
    w c = (Ideal.absNorm w.maximalIdeal.asIdeal : ℝ) ^
      (WithZero.log (w.maximalIdeal.valuation K c)) := by
  have h0 : w.maximalIdeal.valuation K c ≠ 0 := (Valuation.ne_zero_iff _).2 hc
  rw [← FinitePlace.norm_embedding_eq, FinitePlace.norm_embedding',
    WithZeroMulInt.toNNReal_neg_apply _ h0]
  obtain ⟨k, hk⟩ := WithZero.ne_zero_iff_exists.1 h0
  simp only [← hk, WithZero.unzero_coe]
  push_cast
  rfl
end GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure
