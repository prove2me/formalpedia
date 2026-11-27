-- Prove2me | solution 1 for GlobalTheory.AnVal.mulN_eSec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:46:26.849239+00:00
-- url     : https://prove2.me/submissions/1b30f0e9-b144-454b-968c-035dcafae8c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AbelianHolomorphicFrameReadingConstOfFormsCancelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_GeneratorReadingCorrMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_GeneratorReadingPullbackPeriodRigid
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ReadingTwistedPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NormalisedPullbackMulNReadsTheta
import Theorems.Thm_GlobalTheory_AnVal_mulN_comp

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
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ}
  (Φ : AnFr A L x0 g)
omit [IsCommMonObj A]
namespace GlobalTheory.AnVal
theorem _root_.solution (N : ℕ) : eSec A ≫ (mulA A N).left = eSec A := by
  have h1 : (η : 𝟙_ (Over S) ⟶ A) = 1 := by
    have h0 : (1 : 𝟙_ (Over S) ⟶ A) = toUnit _ ≫ η := rfl
    simpa using h0.symm
  have h := mulN_comp (η : 𝟙_ (Over S) ⟶ A) N
  rw [h1, one_pow] at h
  unfold eSec
  rw [← Over.comp_left, h1, h]
end GlobalTheory.AnVal
