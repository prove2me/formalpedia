-- Prove2me | solution 1 for GlobalTheory.CubeReading.tri_psum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:35:01.68855+00:00
-- url     : https://prove2.me/submissions/32fc5452-aae3-48be-b4e5-30e61fabd62a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TripleProductTorusPeriodicBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsHolFamPullbackLiftOfCommonBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AbelianHolomorphicFrameReadingConstOfFormsCancel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CubicalReadingOneAnalyticFrame
import Theorems.Thm_GlobalTheory_CubeReading_e_zero
import Theorems.Thm_GlobalTheory_CubeReading_tripleProductPoint_comp_projection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.CubeReading
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ}
  (Φ : AnFr A L x0 g)
private theorem tri_comp_foldr_lift_mul_eq_e_sum (x : Fin 3 → Fin g → ℂ) (l : List (Fin 3)) :
    tri Φ x ≫ l.foldr (fun k acc => lift (x3 A k) acc ≫ μ) (toUnit (G3 A) ≫ η) = Φ.e (l.map x).sum := by
  induction l with
  | nil =>
    simp only [List.foldr_nil, List.map_nil, List.sum_nil, e_zero]
    rw [comp_toUnit_assoc]
    rfl
  | cons k l ih =>
    simp only [List.foldr_cons, List.map_cons, List.sum_cons, Φ.e_add, ← ih, ← tripleProductPoint_comp_projection]
    rw [← Category.assoc, comp_lift]
    rfl
end GlobalTheory.CubeReading
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.CubeReading
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ}
  (Φ : AnFr A L x0 g)
namespace GlobalTheory.CubeReading
theorem _root_.solution (x : Fin 3 → Fin g → ℂ) (I : Finset (Fin 3)) :
    tri Φ x ≫ psum A (x3 A) I = Φ.e (∑ a ∈ I, x a) := by
  unfold psum padd pzero
  rw [tri_comp_foldr_lift_mul_eq_e_sum]
  congr 1
  have hs : ∑ a ∈ I, x a = ∑ a : Fin 3, if a ∈ I then x a else 0 := by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hl : List.finRange 3 = [0, 1, 2] := by decide
  rw [hs, Fin.sum_univ_three, hl]
  by_cases h0 : (0 : Fin 3) ∈ I <;> by_cases h1 : (1 : Fin 3) ∈ I <;> by_cases h2 : (2 : Fin 3) ∈ I <;>
    simp [h0, h1, h2, add_assoc]
end GlobalTheory.CubeReading
