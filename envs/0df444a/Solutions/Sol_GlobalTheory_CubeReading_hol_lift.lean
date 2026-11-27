-- Prove2me | solution 1 for GlobalTheory.CubeReading.hol_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:14:37.477908+00:00
-- url     : https://prove2.me/submissions/98060119-6a59-4287-b66a-d24baa70cd49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TripleProductTorusPeriodicBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsHolFamPullbackLiftOfCommonBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AbelianHolomorphicFrameReadingConstOfFormsCancel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CubicalReadingOneAnalyticFrame
import Theorems.Thm_GlobalTheory_AnVal_isHolFam_pullback_lift


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.CubeReading
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ}
  (Φ : AnFr A L x0 g)
namespace GlobalTheory.CubeReading
theorem _root_.solution {N : ℕ} {B C : Over S} (p : (Fin N → ℂ) → (Over.mk x0 ⟶ B)) (q : (Fin N → ℂ) → (Over.mk x0 ⟶ C))
    (hp : IsHolFam fun v => (p v).left) (hq : IsHolFam fun v => (q v).left) :
    IsHolFam fun v => (lift (p v) (q v)).left := by
  have key := isHolFam_pullback_lift S B.left C.left B.hom C.hom N (fun v => (p v).left) (fun v => (q v).left) x0
    (fun z => by simp) (fun z => by simp) hp hq
  exact key
end GlobalTheory.CubeReading
