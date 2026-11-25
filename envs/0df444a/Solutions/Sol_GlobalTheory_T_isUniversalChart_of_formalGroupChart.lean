-- Prove2me | solution 1 for GlobalTheory.T.isUniversalChart_of_formalGroupChart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:22:46.813051+00:00
-- url     : https://prove2.me/submissions/58e0d809-604f-4247-9dc9-5da200950bb3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsUniversalChartOfFormalGroupChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsUniversalChartOfFormalGroupChartStatement
import Theorems.Thm_GlobalTheory_ChartUniv_isUnivChart_of_isChartJ


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
theorem _root_.solution : ∀ (T : Type) [CommRing T] [IsLocalRing T] (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (d : ℕ) (F : FGLaw T d) (x : ∀ m : ℕ, algOver T (JetR T (Fin 1 × Fin d) m) ⟶ G), IsChartJ G F x → ∃ x0 : GlobalTheory.JetSer.Fam G (Fin d), Chart.IsUnivChart G d x0 ∧ ∃ ρ : ∀ m, JetR T (Fin 1 × Fin d) m →ₐ[T] Chart.JetR T (Fin d) m, (∀ m j, ρ m (zR m ((0 : Fin 1), j)) = Chart.zR m j) ∧ ∀ m, (x0 m).left = spMap (ρ m : JetR T (Fin 1 × Fin d) m →+* Chart.JetR T (Fin d) m) ≫ (x m).left := by
  first | exact @GlobalTheory.ChartUniv.isUnivChart_of_isChartJ | exact GlobalTheory.ChartUniv.isUnivChart_of_isChartJ | (intros; apply GlobalTheory.ChartUniv.isUnivChart_of_isChartJ <;> assumption)
end _root_.GlobalTheory.T
