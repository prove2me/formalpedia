-- Prove2me | solution 1 for GlobalTheory.FormalCocycle.formalSeriesSubstPoints_standard_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:09:54.587569+00:00
-- url     : https://prove2.me/submissions/259fd583-6cd3-42d9-aadc-eb28bfc463e0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalLogEqSumOfMultiplicativeParam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSeriesSubstPointsStandardThree

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB Sum
open GlobalTheory GlobalTheory.FormalCocycle
variable {k : Type} [CommRing k] {d : ℕ} {μ ν : Type}
namespace GlobalTheory.FormalCocycle
theorem _root_.solution (c : PS k 3 d) : evAt ![pt k (n := 3) d 0, pt k d 1, pt k d 2] c = c := by
  have e : (fun p : Fin 3 × Fin d => (![pt k (n := 3) d 0, pt k d 1, pt k d 2] p.1) p.2) = X := by
    funext p
    obtain ⟨j, i⟩ := p
    fin_cases j <;> rfl
  rw [evAt, e, subst_self]
  rfl
end GlobalTheory.FormalCocycle
