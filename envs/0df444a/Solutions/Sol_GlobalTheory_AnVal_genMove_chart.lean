-- Prove2me | solution 1 for GlobalTheory.AnVal.genMove_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:38:39.3725+00:00
-- url     : https://prove2.me/submissions/1277926a-650c-4e0d-9bcb-40c504750351

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_GeneratorReadingPullbackPeriodRigid

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
open GlobalTheory GlobalTheory.AnVal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)
namespace GlobalTheory.AnVal
theorem _root_.solution {X Z : Scheme.{0}} (M : LB X) {K : Type} [Fintype K] (φ : K → (Z ⟶ X)) (q : Sp ℂ ⟶ Z)
    (j : K → M.ι) (h : ⊤ ≤ q ⁻¹ᵁ LB.wchart M φ j) (k : K) : ⊤ ≤ (q ≫ φ k) ⁻¹ᵁ M.U (j k) :=
  fun _ hy => LB.wchart_le M φ j k (h hy)
end GlobalTheory.AnVal
