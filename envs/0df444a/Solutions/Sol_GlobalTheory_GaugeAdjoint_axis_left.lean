-- Prove2me | solution 1 for GlobalTheory.GaugeAdjoint.axis_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:59:46.19305+00:00
-- url     : https://prove2.me/submissions/0760b667-366d-4619-8310-35394af3fe0a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_IntAASubstOfHasSubst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ConstantCoeffEv
import Theorems.Thm_GlobalTheory_GaugeAdjoint_ev_pt
import Theorems.Thm_GlobalTheory_GaugeAdjoint_ev_zero
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_pt
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_one
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_zero
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_comp1
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
    ev (n := 1) ![pt k d 0, 0] (ev (n := 2) ![comp1 φ (pt k d 0), pt k d 1] f) =
      ev (n := 1) ![comp1 φ (pt k d 0)] (ev (n := 1) ![pt k d 0, 0] f) := by
  have hp0 : ∀ i, constantCoeff (pt k d (0 : Fin 2) i) = 0 := fun i => const_pt 0 i
  have hp1 : ∀ i, constantCoeff (pt k d (1 : Fin 2) i) = 0 := fun i => const_pt 1 i
  have hq0 : ∀ i, constantCoeff (pt k d (0 : Fin 1) i) = 0 := fun i => const_pt 0 i
  have hc0 := const_comp1 hφ hp0
  have hb0 := const_comp1 hφ hq0
  rw [ev_ev_two hc0 hp1 const_axis, ev_ev_two hq0 (fun i => const_zero i) (const_one hb0)]
  have e0 : (fun i => ev (n := 1) ![pt k d 0, 0] (comp1 φ (pt k d (0 : Fin 2)) i)) =
      fun i => ev (n := 1) ![comp1 φ (pt k d (0 : Fin 1))] (pt k d (0 : Fin 1) i) := by
    funext i
    rw [ev_pt (const_one hb0)]
    show ev _ (ev ![pt k d 0] (φ i)) = ev ![pt k d 0] (φ i)
    rw [ev_ev_one hp0 const_axis, axis_pt_zero]
  have e1 : (fun i => ev (n := 1) ![pt k d 0, 0] (pt k d (1 : Fin 2) i)) =
      fun i => ev (n := 1) ![comp1 φ (pt k d (0 : Fin 1))] ((0 : Pt k 1 d) i) := by
    rw [axis_pt_one]
    funext i
    exact (ev_zero (const_one hb0)).symm
  rw [e0, e1]
end GlobalTheory.GaugeAdjoint
