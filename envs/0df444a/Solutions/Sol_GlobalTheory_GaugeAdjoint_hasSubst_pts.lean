-- Prove2me | solution 1 for GlobalTheory.GaugeAdjoint.hasSubst_pts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:35:37.695724+00:00
-- url     : https://prove2.me/submissions/04d4e09a-da70-4dd4-a691-119a502a2564

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
theorem _root_.solution {a : Fin m → Pt k n d} (ha : ∀ j i, constantCoeff (a j i) = 0) :
    HasSubst (fun q : Fin m × Fin d => a q.1 q.2) := hasSubst_of_constantCoeff_zero fun q => ha q.1 q.2
end GlobalTheory.GaugeAdjoint
