-- Prove2me | solution 1 for GlobalTheory.CubeReading.hol_tri
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:40:46.988802+00:00
-- url     : https://prove2.me/submissions/bcfc95b1-ef21-487a-855a-bd8657afadb1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TripleProductTorusPeriodicBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsHolFamPullbackLiftOfCommonBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AbelianHolomorphicFrameReadingConstOfFormsCancel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CubicalReadingOneAnalyticFrame
import Theorems.Thm_GlobalTheory_CubeReading_hol_lin
import Theorems.Thm_GlobalTheory_CubeReading_hol_lift

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
theorem _root_.solution : IsHolFam fun z => (tri Φ (colsEquiv 3 g z)).left := by
  have hc : ∀ k : Fin 3, IsHolFam fun z => (Φ.e (colsEquiv 3 g z k)).left := by
    intro k
    have h := hol_lin Φ (LinearMap.proj k ∘ₗ (colsEquiv 3 g).toLinearMap)
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.proj_apply] using h
  have h12 := hol_lift (B := A) (C := A) (fun z => Φ.e (colsEquiv 3 g z 1)) (fun z => Φ.e (colsEquiv 3 g z 2))
    (hc 1) (hc 2)
  exact hol_lift (B := A) (C := A ⊗ A) (fun z => Φ.e (colsEquiv 3 g z 0))
    (fun z => lift (Φ.e (colsEquiv 3 g z 1)) (Φ.e (colsEquiv 3 g z 2))) (hc 0) h12
end GlobalTheory.CubeReading
