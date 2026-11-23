-- Prove2me | solution 1 for GlobalTheory.GaugeAdjoint.const_pt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:35:18.786935+00:00
-- url     : https://prove2.me/submissions/4a514b21-e054-4f80-a351-574702227ea4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_IntAASubstOfHasSubst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ConstantCoeffEv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.GaugeAdjoint
open GlobalTheory.FormalCalc GlobalTheory.IntSeries
variable {k : Type} [CommRing k] {d m n p : ℕ}
namespace GlobalTheory.GaugeAdjoint
theorem _root_.solution (j : Fin n) (i : Fin d) : constantCoeff (pt k d j i) = 0 := by
  unfold pt
  exact constantCoeff_X _
end GlobalTheory.GaugeAdjoint
