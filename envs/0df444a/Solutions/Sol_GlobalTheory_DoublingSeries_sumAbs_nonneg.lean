-- Prove2me | solution 1 for GlobalTheory.DoublingSeries.sumAbs_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:17:29.08139+00:00
-- url     : https://prove2.me/submissions/d82bd571-a85b-41fc-9399-ba7780788ba3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BorelParam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RatFunDifferentiableOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
noncomputable section
open GlobalTheory GlobalTheory.DoublingSeries
namespace GlobalTheory.DoublingSeries
theorem _root_.solution {D : Type} [Fintype D] (e : D → ℤ) : 0 ≤ sumAbs e :=
  Finset.sum_nonneg fun i _ => abs_nonneg (e i)
end GlobalTheory.DoublingSeries
