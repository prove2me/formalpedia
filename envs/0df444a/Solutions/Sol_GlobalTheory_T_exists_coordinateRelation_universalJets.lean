-- Prove2me | solution 1 for GlobalTheory.T.exists_coordinateRelation_universalJets
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:16:02.518926+00:00
-- url     : https://prove2.me/submissions/c21ffad2-17ed-459d-abf8-2aa49d89ec46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsCoordinateRelationUniversalJets
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsCoordinateRelationUniversalJetsStatement
import Theorems.Thm_GlobalTheory_ChartCmp_exists_coordRel_of_isUnivJ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V : Type) [CommRing V] (G : Over (Sp V)) [GrpObj G] (d : ℕ) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G), GlobalTheory.PowGerm.IsUnivJ G (Fin 1 × Fin d) x → GlobalTheory.PowGerm.IsUnivJ G (Fin 1 × Fin d) x' → ∃ φ φi : Pt V 1 d, IsInvPair φ φi ∧ CoordRel x x' φ ∧ CoordRel x' x φi := by
  first | exact @GlobalTheory.ChartCmp.exists_coordRel_of_isUnivJ | exact GlobalTheory.ChartCmp.exists_coordRel_of_isUnivJ | (intros; apply GlobalTheory.ChartCmp.exists_coordRel_of_isUnivJ <;> assumption)
end _root_.GlobalTheory.T
