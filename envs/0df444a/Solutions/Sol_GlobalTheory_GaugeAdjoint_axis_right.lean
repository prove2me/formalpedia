-- Prove2me | solution 1 for GlobalTheory.GaugeAdjoint.axis_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:59:46.929565+00:00
-- url     : https://prove2.me/submissions/04e7f5df-810a-437a-9662-193f75bed4e6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_IntAASubstOfHasSubst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ConstantCoeffEv
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_pt
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_comp1
import Theorems.Thm_GlobalTheory_GaugeAdjoint_ev_origin
import Theorems.Thm_GlobalTheory_GaugeAdjoint_ev_ev_one
import Theorems.Thm_GlobalTheory_GaugeAdjoint_ev_ev_two
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_axis
import Theorems.Thm_GlobalTheory_GaugeAdjoint_axis_pt_zero
import Theorems.Thm_GlobalTheory_GaugeAdjoint_axis_pt_one

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
theorem _root_.solution {φ : Pt k 1 d} (hφ : ∀ i, constantCoeff (φ i) = 0) (f : PS k 2 d) :
    ev (n := 1) ![pt k d 0, 0] (ev (n := 2) ![pt k d 0, comp1 φ (pt k d 1)] f) =
      ev (n := 1) ![pt k d 0, 0] f := by
  have hp0 : ∀ i, constantCoeff (pt k d (0 : Fin 2) i) = 0 := fun i => const_pt 0 i
  have hp1 : ∀ i, constantCoeff (pt k d (1 : Fin 2) i) = 0 := fun i => const_pt 1 i
  have hc1 := const_comp1 hφ hp1
  have e1 : (fun i => ev (n := 1) ![pt k d 0, 0] (comp1 φ (pt k d (1 : Fin 2)) i)) = 0 := by
    funext i
    show ev _ (ev ![pt k d 1] (φ i)) = 0
    rw [ev_ev_one hp1 const_axis, axis_pt_one, ev_origin, hφ i, map_zero]
  rw [ev_ev_two hp0 hc1 const_axis, axis_pt_zero, e1]
end GlobalTheory.GaugeAdjoint
