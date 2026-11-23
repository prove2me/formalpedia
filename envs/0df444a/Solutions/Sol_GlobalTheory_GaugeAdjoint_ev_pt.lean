-- Prove2me | solution 1 for GlobalTheory.GaugeAdjoint.ev_pt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:24.506721+00:00
-- url     : https://prove2.me/submissions/402376a0-1d13-4028-961c-04820a39b3cb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_IntAASubstOfHasSubst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ConstantCoeffEv
import Theorems.Thm_GlobalTheory_GaugeAdjoint_hasSubst_pts

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
theorem _root_.solution {a : Fin m → Pt k n d} (ha : ∀ j i, constantCoeff (a j i) = 0) (j : Fin m)
    (i : Fin d) : ev a (pt k d j i) = a j i := by
  unfold ev pt
  rw [subst_X (hasSubst_pts ha)]
end GlobalTheory.GaugeAdjoint
