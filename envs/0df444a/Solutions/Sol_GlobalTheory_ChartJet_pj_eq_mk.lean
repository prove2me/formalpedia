-- Prove2me | solution 1 for GlobalTheory.ChartJet.pj_eq_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:39:27.701682+00:00
-- url     : https://prove2.me/submissions/b4e1c6f1-de88-40ab-98de-15d46c066667

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_IntChartCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsIsUnivChartOfIsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsPtJ

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
theorem _root_.solution {m : ℕ} {f : MvPowerSeries σ R} {q : MvPolynomial σ R} :
    pj m f = Ideal.Quotient.mk _ q ↔ ∀ e : σ →₀ ℕ, e.degree < m + 1 → coeff e f = q.coeff e := by
  unfold pj
  rw [Ideal.Quotient.eq]
  change _ ∈ MvPolynomial.idealOfVars σ R ^ (m + 1) ↔ _
  rw [MvPolynomial.mem_pow_idealOfVars_iff']
  refine forall_congr' fun e => imp_congr_right fun he => ?_
  rw [MvPolynomial.coeff_sub, MvPowerSeries.coeff_truncTotal _ he, sub_eq_zero]
end GlobalTheory.ChartJet
