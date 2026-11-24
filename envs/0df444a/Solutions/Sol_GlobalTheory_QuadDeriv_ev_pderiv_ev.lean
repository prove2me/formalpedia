-- Prove2me | solution 1 for GlobalTheory.QuadDeriv.ev_pderiv_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:07:16.673558+00:00
-- url     : https://prove2.me/submissions/2f02dd17-51be-40ef-8374-a07268125db1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
import Theorems.Thm_GlobalTheory_QuadDeriv_ev_sum
import Theorems.Thm_GlobalTheory_QuadDeriv_pderiv_ev
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_ev__a7884319006c
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_mul


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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory GlobalTheory.QuadDeriv
variable {k : Type} [CommRing k] {d : ℕ}
namespace GlobalTheory.QuadDeriv
theorem _root_.solution {l m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) (a : Fin l → Pt k m d)
    (ha : ∀ j, GP (a j)) (f : PS k l d) (s : Fin m × Fin d) :
    ev V (pderiv k s (ev a f)) =
      ∑ j, ∑ i, ev (fun j => evP V (a j)) (pderiv k (j, i) f) * ev V (pderiv k s (a j i)) := by
  rw [pderiv_ev a ha, ev_sum V hV]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ev_sum V hV]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gt_ev_mul V hV, gt_ev_ev' V a hV ha]
end GlobalTheory.QuadDeriv
