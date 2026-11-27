-- Prove2me | solution 1 for GlobalTheory.JetVal.isHolFam_lftJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:05:25.590823+00:00
-- url     : https://prove2.me/submissions/976462c4-10a4-4094-a694-4f2f8571faad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsHolFamPullbackLiftOfCommonBase
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsValueAtJetPointCmFrameSection
import Theorems.Thm_GlobalTheory_AnVal_isHolFam_pullback_lift


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
open GlobalTheory GlobalTheory.JetVal
open AlgebraicGeometry CategoryTheory Opposite Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
variable {X : Scheme.{0}} {G : Over X} [GrpObj G] (L : LB G.left) {x0 : Sp ℂ ⟶ X} {g : ℕ}
variable (e : (Fin g → ℂ) → (Sp ℂ ⟶ G.left)) (hol : IsHolFam e) (he : ∀ z, e z ≫ G.hom = x0)
namespace GlobalTheory.JetVal
theorem _root_.solution (hol : IsHolFam e) : IsHolFam (lftJ e he) := by
  have hl : lftJ e he = fun z => Limits.pullback.lift (f := x0) (g := G.hom) (𝟙 (Sp ℂ)) (e z)
      ((Category.id_comp x0).trans (he z).symm) := by
    funext z
    rw [lftJ, ptSecT, Over.lift_left]
    rfl
  rw [hl]
  exact GlobalTheory.AnVal.isHolFam_pullback_lift X (Sp ℂ) G.left x0 G.hom g (fun _ => 𝟙 (Sp ℂ)) e x0 (fun _ => Category.id_comp x0) he
    (isHolFam_const _) hol
end GlobalTheory.JetVal
