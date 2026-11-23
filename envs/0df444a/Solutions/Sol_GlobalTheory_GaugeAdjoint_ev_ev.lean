-- Prove2me | solution 1 for GlobalTheory.GaugeAdjoint.ev_ev
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:05:28.73401+00:00
-- url     : https://prove2.me/submissions/3ce55881-a1fc-4979-9e90-e6b236f4483c

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
theorem _root_.solution {a : Fin m → Pt k n d} (ha : ∀ j i, constantCoeff (a j i) = 0)
    {b : Fin n → Pt k p d} (hb : ∀ j i, constantCoeff (b j i) = 0) (f : PS k m d) :
    ev b (ev a f) = ev (fun j i => ev b (a j i)) f := by
  unfold ev
  rw [subst_comp_subst_apply (hasSubst_pts ha) (hasSubst_pts hb)]
end GlobalTheory.GaugeAdjoint
