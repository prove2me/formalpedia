-- Prove2me | solution 1 for GlobalTheory.FormalMulN.add_comm_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:19:46.748915+00:00
-- url     : https://prove2.me/submissions/abe3788c-387d-4d74-a0ed-c946fe81dc3b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
import Theorems.Thm_GlobalTheory_FormalMulN_ev_pt_fun
import Theorems.Thm_GlobalTheory_FormalMulN_ev_add_pts
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_pt
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_two


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.FormalMulN
open GlobalTheory.GaugeAdjoint
variable {R : Type} [CommRing R] {d m n : ℕ} (G : FGLaw R d)
namespace GlobalTheory.FormalMulN
theorem _root_.solution {x y : Pt R n d} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) : G.add x y = G.add y x := by
  have hc : G.add (pt R (n := 2) d 1) (pt R (n := 2) d 0) = G.F := funext fun i => G.comm i
  have h : (fun i => ev ![x, y] (G.add (pt R (n := 2) d 1) (pt R (n := 2) d 0) i)) =
      fun i => ev ![x, y] (G.F i) := by rw [hc]
  rw [ev_add_pts G (const_pt 1) (const_pt 0) (const_two hx hy), ev_pt_fun (const_two hx hy) 1,
    ev_pt_fun (const_two hx hy) 0] at h
  exact h.symm
end GlobalTheory.FormalMulN
