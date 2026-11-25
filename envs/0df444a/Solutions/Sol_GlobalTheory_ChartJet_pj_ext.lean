-- Prove2me | solution 1 for GlobalTheory.ChartJet.pj_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:54:23.625822+00:00
-- url     : https://prove2.me/submissions/c17375bb-2611-4427-b4d8-9fd8b45d9d73

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_IntChartCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsIsUnivChartOfIsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsPtJ
import Theorems.Thm_GlobalTheory_ChartJet_pj_eq_mk
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ChartJet
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FormalLog
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R] {σ τ : Type} [Finite σ] [Finite τ]
namespace GlobalTheory.ChartJet
theorem _root_.solution {f g : MvPowerSeries σ R} (h : ∀ m, pj m f = pj m g) : f = g := by
  ext e
  have h1 := h e.degree
  have h2 : pj e.degree g = Ideal.Quotient.mk _ (truncTotal (e.degree + 1) g) := rfl
  rw [h2, pj_eq_mk] at h1
  rw [h1 e (Nat.lt_succ_self _), MvPowerSeries.coeff_truncTotal _ (Nat.lt_succ_self _)]
end GlobalTheory.ChartJet
