-- Prove2me | solution 1 for GlobalTheory.ChartJet.jP_zR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:25:29.515084+00:00
-- url     : https://prove2.me/submissions/85566658-c1ce-4d1b-8dc9-8ba78fe1366d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_IntChartCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsIsUnivChartOfIsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsPtJ
import Theorems.Thm_GlobalTheory_ChartJet_jS_zR

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
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ} (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G) {n l : ℕ}
namespace GlobalTheory.ChartJet
theorem _root_.solution (m : ℕ) (p : Q R d n) (j : Fin d) : jP m p (zR m j) = pj m (p.1 j) := jS_zR m p.1 p.2 j
end GlobalTheory.ChartJet
