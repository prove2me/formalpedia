-- Prove2me | solution 1 for OAI.Kadison.ProjectionJoin.dimension_sup_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:09:43.908912+00:00
-- url     : https://prove2.me/submissions/e46b227f-3ae9-4897-be0b-bbd577fe84cb

import Mathlib
import Definitions.Def_OAIQ039C068
import Theorems.Thm_OAI_Kadison_PartialIsometryOrder_DyadicPartition_dimension_tendsto_of_strong_increasing
import Theorems.Thm_OAI_Kadison_ProjectionJoin_dimension_finiteJoin_le

section
-- module Solutions.OAIQ039_CM.Commutator_CountableProjectionJoin
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Kadison.ProjectionJoin

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma sup_mem (M : VonNeumannAlgebra H) (P : ℕ → H →L[ℂ] H)
    (hP : ∀ n,IsStarProjection (P n)) (hPM : ∀ n,P n∈M) : sup M P hP hPM∈M :=
  (exists_countable_sup M P hP hPM).choose_spec.1

lemma sup_projection (M : VonNeumannAlgebra H) (P : ℕ → H →L[ℂ] H)
    (hP : ∀ n,IsStarProjection (P n)) (hPM : ∀ n,P n∈M) : IsStarProjection (sup M P hP hPM) :=
  (exists_countable_sup M P hP hPM).choose_spec.2.1

lemma le_sup (M : VonNeumannAlgebra H) (P : ℕ → H →L[ℂ] H)
    (hP : ∀ n,IsStarProjection (P n)) (hPM : ∀ n,P n∈M) (n : ℕ) : P n≤ sup M P hP hPM :=
  (exists_countable_sup M P hP hPM).choose_spec.2.2.1 n

lemma sup_strong (M : VonNeumannAlgebra H) (P : ℕ → H →L[ℂ] H)
    (hP : ∀ n,IsStarProjection (P n)) (hPM : ∀ n,P n∈M) (x : H) :
    Tendsto (fun n => finiteJoin P n x) atTop (𝓝 (sup M P hP hPM x)) :=
  (exists_countable_sup M P hP hPM).choose_spec.2.2.2.1 x

open PartialIsometryOrder PartialIsometryOrder.DyadicPartition

variable [Nontrivial H] [TopologicalSpace.SeparableSpace H]

variable (M : VonNeumannAlgebra H) (hfac : FactorCorner.IsFactor M)
  (hd : DiffuseProjection.HasNoMinimalProjections M) (hfin : IsFiniteAlgebra M)

include hfin

theorem dimension_sup_le_oai (P : ℕ → H →L[ℂ] H) (hP : ∀ n,IsStarProjection (P n))
    (hPM : ∀ n,P n∈M) (b : ℕ → ℝ) (hb : Summable b)
    (hPb : ∀ n,dimension M hfac hd (P n)≤b n) :
    dimension M hfac hd (sup M P hP hPM)≤∑' n,b n := by
  have hlim := dimension_tendsto_of_strong_increasing M hfac hd hfin (sup_mem M P hP hPM)
    (sup_projection M P hP hPM) (finiteJoin P) (finiteJoin_mem M P hPM) (finiteJoin_projection P)
    (finiteJoin_mono P) (finiteJoin_le P hP (sup_projection M P hP hPM) (le_sup M P hP hPM))
    (sup_strong M P hP hPM)
  apply le_of_tendsto_of_tendsto hlim hb.hasSum.tendsto_sum_nat
  exact Filter.Eventually.of_forall fun n => (dimension_finiteJoin_le M hfac hd hfin P hP hPM n).trans
    (Finset.sum_le_sum fun k _ => hPb k)

end Kadison.ProjectionJoin

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.ProjectionJoin.dimension_sup_le_oai.{u_1} := @OAI.Kadison.ProjectionJoin.dimension_sup_le_oai.{u_1}
