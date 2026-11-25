-- Prove2me | solution 1 for GlobalTheory.DerivEndo.germ_ev_restrict_axis_groupLaw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:36:23.129735+00:00
-- url     : https://prove2.me/submissions/297eb20a-ef4f-4b5e-b2bc-15bf0b366d64

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_GermPointsNoConstantTermFirstZero
import Theorems.Thm_GlobalTheory_DerivEndo_noConst_one
import Theorems.Thm_GlobalTheory_DerivEndo_ev_ev
import Theorems.Thm_GlobalTheory_DerivEndo_ev_id
import Theorems.Thm_GlobalTheory_DerivEndo_germPointsNoConstantTerm_first_zero
import Theorems.Thm_GlobalTheory_DerivEndo_formalGroupLaw_ev_second_zero

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
theorem _root_.solution (G : FGLaw R d) (h : PS R 1 d) :
    ev (n := 1) ![pt R d 0, 0] (ev (n := 2) ![G.F] h) = h := by
  have hfam : (fun j i => ev (n := 1) ![pt R d 0, 0]
      ((![G.F] : Fin 1 → Pt R 2 d) j i)) = (![pt R d 0] : Fin 1 → Pt R 1 d) := by
    funext j i
    rw [Fin.fin_one_eq_zero j]
    exact formalGroupLaw_ev_second_zero G i
  rw [ev_ev germPointsNoConstantTerm_first_zero (noConst_one G.const), hfam, ev_id]
end GlobalTheory.DerivEndo
