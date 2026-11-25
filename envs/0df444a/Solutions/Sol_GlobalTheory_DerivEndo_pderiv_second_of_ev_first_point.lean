-- Prove2me | solution 1 for GlobalTheory.DerivEndo.pderiv_second_of_ev_first_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:26:08.216266+00:00
-- url     : https://prove2.me/submissions/54c5d1b3-1acc-4d90-acd6-b19167b85c53

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_GermPointsNoConstantTermFirstZero
import Theorems.Thm_GlobalTheory_DerivEndo_noConst_one
import Theorems.Thm_GlobalTheory_DerivEndo_cc_pt
import Theorems.Thm_GlobalTheory_DerivEndo_pderiv_ev

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.DerivEndo
variable {R : Type} [CommRing R] {d : ℕ}
namespace GlobalTheory.DerivEndo
theorem _root_.solution (h : PS R 1 d) (i : Fin d) :
    pderiv R ((1 : Fin 2), i) (ev (n := 2) ![pt R d 0] h) = 0 := by
  have hx : NoConst (![pt R (n := 2) d 0] : Fin 1 → Pt R 2 d) := noConst_one (cc_pt 0)
  rw [pderiv_ev hx]
  refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
  rw [Fin.fin_one_eq_zero j]
  show _ * pderiv R ((1 : Fin 2), i) (X ((0 : Fin 2), k)) = 0
  rw [pderiv_X_of_ne (by simp), mul_zero]
end GlobalTheory.DerivEndo
