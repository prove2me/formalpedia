-- Prove2me | solution 1 for GlobalTheory.FormalMulN.formalGroupLaw_comp_mulN_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:19:59.521497+00:00
-- url     : https://prove2.me/submissions/e290ed7f-ebe1-410c-a614-a637a923e76f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
import Theorems.Thm_GlobalTheory_FormalMulN_ev_pt_fun
import Theorems.Thm_GlobalTheory_FormalMulN_ev_add_pts
import Theorems.Thm_GlobalTheory_FormalMulN_const_mulN
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_one
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_pt


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
theorem _root_.solution (k : ℕ) {x : Pt R n d} (hx : ∀ i, constantCoeff (x i) = 0) :
    comp1 (mulN G (k + 1)) x = G.add (comp1 (mulN G k) x) x := by
  show (fun i => ev ![x] (G.add (mulN G k) (pt R d 0) i)) = _
  rw [ev_add_pts G (const_mulN G k) (const_pt 0) (const_one hx), ev_pt_fun (const_one hx) 0]
  rfl
end GlobalTheory.FormalMulN
