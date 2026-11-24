-- Prove2me | solution 1 for GlobalTheory.ChartInv.formalComp_apply_eq_mvPowerSeries_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:10:52.908333+00:00
-- url     : https://prove2.me/submissions/93ef239c-d902-476a-aea6-8111987198cc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalCompApplyEqMvPowerSeriesSubst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.ChartInv
variable {k : Type} [CommRing k] {d : ℕ}
namespace GlobalTheory.ChartInv
theorem _root_.solution (φ ψ : Pt k 1 d) (i : Fin d) :
    comp1 φ ψ i = (φ i).subst (fun p : Fin 1 × Fin d => ψ p.2) := by
  unfold comp1 ev
  congr 1
  funext p
  obtain ⟨a, j⟩ := p
  fin_cases a
  rfl
end GlobalTheory.ChartInv
