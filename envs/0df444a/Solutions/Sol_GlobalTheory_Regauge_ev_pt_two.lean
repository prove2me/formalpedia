-- Prove2me | solution 1 for GlobalTheory.Regauge.ev_pt_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:38:38.288611+00:00
-- url     : https://prove2.me/submissions/03c5e7f5-4369-4aaa-a94f-63ef7b30c38e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_GermEvRegaugedSecondLawFamily

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
open GlobalTheory GlobalTheory.Regauge
variable {k : Type} [CommRing k] {d : ℕ}
namespace GlobalTheory.Regauge
theorem _root_.solution (f : PS k 2 d) : ev ![pt k (n := 2) d 0, pt k (n := 2) d 1] f = f := by
  change MvPowerSeries.subst (fun p : Fin 2 × Fin d => (![pt k (n := 2) d 0, pt k (n := 2) d 1] p.1) p.2) f = f
  have e : (fun p : Fin 2 × Fin d => (![pt k (n := 2) d 0, pt k (n := 2) d 1] p.1) p.2) = X := by
    funext p
    obtain ⟨j, i⟩ := p
    fin_cases j <;> rfl
  rw [e, MvPowerSeries.subst_self]
  rfl
end GlobalTheory.Regauge
