-- Prove2me | solution 1 for GlobalTheory.T.isSeriesOfMorphismInCharts_pow_mulFormalGroupLaw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:22:23.530365+00:00
-- url     : https://prove2.me/submissions/1270600a-ab0f-4620-ad40-d98455f0065c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsSeriesOfMorphismInChartsPowMulFormalGroupLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsSeriesOfMorphismInChartsPowMulFormalGroupLawStatement
import Theorems.Thm_GlobalTheory_JetSer_isMapOf_pow_mulF


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (d : ℕ) (x : GlobalTheory.JetSer.Fam G (Fin d)), Chart.IsUnivChart G d x → ∀ F : Fin d → PS R 2 d, GlobalTheory.JetSer.IsLawOf x F → ∀ N : ℕ, GlobalTheory.JetSer.IsMapOf x x ((𝟙 G) ^ N : G ⟶ G) (mulF F N) := by
  first | exact @GlobalTheory.JetSer.isMapOf_pow_mulF | exact GlobalTheory.JetSer.isMapOf_pow_mulF | (intros; apply GlobalTheory.JetSer.isMapOf_pow_mulF <;> assumption)
end _root_.GlobalTheory.T
