-- Prove2me | solution 1 for GlobalTheory.FormalMulN.zero_add_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:19:48.296132+00:00
-- url     : https://prove2.me/submissions/530577d1-9d8c-4c34-ad85-9c1d20de4d82

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
import Theorems.Thm_GlobalTheory_FormalMulN_ev_pt_fun
import Theorems.Thm_GlobalTheory_FormalMulN_ev_zero_fun
import Theorems.Thm_GlobalTheory_FormalMulN_ev_add_pts
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_one
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_pt
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_zero


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
theorem _root_.solution {y : Pt R n d} (hy : ∀ i, constantCoeff (y i) = 0) : G.add 0 y = y := by
  have hu : G.add 0 (pt R (n := 1) d 0) = pt R (n := 1) d 0 := funext fun i => G.unit i
  have h : (fun i => ev ![y] (G.add 0 (pt R (n := 1) d 0) i)) =
      fun i => ev ![y] (pt R (n := 1) d 0 i) := by rw [hu]
  rw [ev_add_pts G const_zero (const_pt 0) (const_one hy), ev_zero_fun (const_one hy),
    ev_pt_fun (const_one hy) 0] at h
  exact h
end GlobalTheory.FormalMulN
