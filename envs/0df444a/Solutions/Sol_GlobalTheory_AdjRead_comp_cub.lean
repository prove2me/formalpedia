-- Prove2me | solution 1 for GlobalTheory.AdjRead.comp_cub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:32:29.148638+00:00
-- url     : https://prove2.me/submissions/f18f6f6e-8ca5-42f6-85b8-c7ad4ae0d5bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGenRosati
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsHolFamPullbackLiftOfCommonBaseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AbelianHolomorphicFrameReadingConstOfFormsCancelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_GeneratorReadingCorrMulInvStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_GeneratorReadingPullbackPeriodRigidStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsAdjReadingOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.AdjRead
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]
private theorem padd_lemma {T : Over S} (a b : T ⟶ A) : padd A a b = a * b := rfl
private theorem pzero_eq_one_cusp_form_evaluations {T : Over S} : pzero A T = 1 := rfl
variable {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)
end GlobalTheory.AdjRead
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AdjRead
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]
namespace GlobalTheory.AdjRead
theorem _root_.solution {T T' : Over S} {n : ℕ} (h : T' ⟶ T) (xs : Fin n → (T ⟶ A)) (I : ULift.{0} (Finset (Fin n))) :
    h.left ≫ cub xs I = cub (fun k => h ≫ xs k) I := by
  simp only [cub]
  rw [← Over.comp_left]
  congr 1
  unfold psum
  generalize List.filter (fun x => decide (x ∈ I.down)) (List.finRange n) = l
  induction l with
  | nil => simp [pzero_eq_one_cusp_form_evaluations]
  | cons a l ih => simp_all [padd_lemma, pzero_eq_one_cusp_form_evaluations, MonObj.comp_mul]
end GlobalTheory.AdjRead
