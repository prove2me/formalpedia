-- Prove2me | solution 1 for GlobalTheory.FormalConnection.coeff_F_y
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:11:50.717996+00:00
-- url     : https://prove2.me/submissions/bc59bf3f-b88d-4438-9c62-95159de606ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_InvariantDerivationsCommuteFormalConnection
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_ev_zero_left


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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.FormalLog
open GlobalTheory GlobalTheory.FormalConnection
variable {k : Type} [CommRing k] {d : ℕ} (G : FGLaw k d)
namespace GlobalTheory.FormalConnection
theorem _root_.solution (c i : Fin d) : coeff (Finsupp.single ((1 : Fin 2), i) 1) (G.F c) = if c = i then 1 else 0 := by
  classical
  have h := congrArg (coeff (Finsupp.single ((0 : Fin 1), i) 1)) (G.unit c)
  rw [coeff_ev_zero_left, Finsupp.embDomain_single] at h
  rw [show (eZ d) ((0 : Fin 1), i) = ((1 : Fin 2), i) from rfl] at h
  rw [h, coeff_X]
  by_cases hci : c = i
  · subst hci; simp
  · rw [if_neg, if_neg hci]
    intro he
    exact hci (congrArg Prod.snd (Finsupp.single_left_injective one_ne_zero he)).symm
end GlobalTheory.FormalConnection
