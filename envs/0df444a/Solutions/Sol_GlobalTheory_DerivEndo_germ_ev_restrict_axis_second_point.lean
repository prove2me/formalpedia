-- Prove2me | solution 1 for GlobalTheory.DerivEndo.germ_ev_restrict_axis_second_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:31:09.466851+00:00
-- url     : https://prove2.me/submissions/0970fa53-1b66-4c7d-ba82-429cda234336

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_GermPointsNoConstantTermFirstZero
import Theorems.Thm_GlobalTheory_DerivEndo_noConst_one
import Theorems.Thm_GlobalTheory_DerivEndo_cc_pt
import Theorems.Thm_GlobalTheory_DerivEndo_ev_pt
import Theorems.Thm_GlobalTheory_DerivEndo_ev_ev
import Theorems.Thm_GlobalTheory_DerivEndo_ev_const
import Theorems.Thm_GlobalTheory_DerivEndo_germPointsNoConstantTerm_first_zero

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
theorem _root_.solution (h : PS R 1 d) :
    ev (n := 1) ![pt R d 0, 0] (ev (n := 2) ![pt R d 1] h) = C (constantCoeff h) := by
  have hy : NoConst (![pt R (n := 2) d 1] : Fin 1 → Pt R 2 d) := noConst_one (cc_pt 1)
  have hfam : (fun j i => ev (n := 1) ![pt R d 0, 0]
      ((![pt R (n := 2) d 1] : Fin 1 → Pt R 2 d) j i)) = fun _ _ => (0 : PS R 1 d) := by
    funext j i
    rw [Fin.fin_one_eq_zero j]
    show ev (n := 1) ![pt R d 0, 0] (pt R d 1 i) = 0
    rw [ev_pt germPointsNoConstantTerm_first_zero]
    rfl
  rw [ev_ev germPointsNoConstantTerm_first_zero hy, hfam, ev_const]
end GlobalTheory.DerivEndo
