-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure.eval_hermitianLinearForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:56:11.11036+00:00
-- url     : https://prove2.me/submissions/0e54f39f-d6e8-4f74-9f75-c1c2649f866c

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
theorem _root_.solution {N : ℕ} (u z : EuclideanSpace ℂ (Fin (N + 1))) :
    eval (fun j => z j) (hermitianLinearForm u) = inner ℂ u z := by
  simp [hermitianLinearForm, PiLp.inner_apply]
end GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure
