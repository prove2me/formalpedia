-- Prove2me | solution 1 for GlobalTheory.T.universalJetCoordinates_dim_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:25:38.774677+00:00
-- url     : https://prove2.me/submissions/8df59901-fec5-43b0-a110-f2fafcd25272

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_UniversalJetCoordinatesDimUnique
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_UniversalJetCoordinatesDimUniqueStatement
import Theorems.Thm_GlobalTheory_ChartCmp_univJ_dim_unique


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
theorem _root_.solution : ∀ (V : Type) [CommRing V] [Nontrivial V] (G : Over (Sp V)) [GrpObj G] (d d' : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G) (x' : ∀ m, jOG (𝟙 (Sp V)) d' m 1 ⟶ G), GlobalTheory.PowGerm.IsUnivJ G (Fin 1 × Fin d) x → GlobalTheory.PowGerm.IsUnivJ G (Fin 1 × Fin d') x' → d = d' := by
  first | exact @GlobalTheory.ChartCmp.univJ_dim_unique | exact GlobalTheory.ChartCmp.univJ_dim_unique | (intros; apply GlobalTheory.ChartCmp.univJ_dim_unique <;> assumption)
end _root_.GlobalTheory.T
