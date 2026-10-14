-- Prove2me | solution 1 for NegativeDP.Stationary.lemma31
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T22:31:06.28009+00:00
-- url     : https://prove2.me/submissions/73736788-33ff-43de-a936-effd443353ff

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_NegativeDP_Stationary_Model
open MeasureTheory ProbabilityTheory Filter Topology
open DiscountedDP.Stationary (Hist Plan MarkovPlan MarkovPlan.toPlan stationary)


namespace NegativeDP.Stationary

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

theorem lemma31_core (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) :
    Antitone (fun n => In P π n 0 s) ∧
      Tendsto (fun n => In P π n 0 s) atTop (𝓝 (I P π s)) := by
  have hIn : ∀ n, In P π n 0 s =
      -(((∑ j ∈ Finset.range n, stageLoss P π s j : ENNReal)) : EReal) := by
    intro n
    simp [In]
  simp only [hIn]
  refine ⟨?_, ?_⟩
  · intro m n hmn
    apply EReal.neg_le_neg_iff.mpr
    exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr
      (Finset.sum_le_sum_of_subset (Finset.range_mono hmn))
  · unfold I
    have h1 := ENNReal.tendsto_nat_tsum (fun n => stageLoss P π s n)
    have h2 := (continuous_coe_ennreal_ereal.tendsto _).comp h1
    exact (continuous_neg.tendsto _).comp h2

end NegativeDP.Stationary

open NegativeDP.Stationary


theorem solution {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A] (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) :
    Antitone (fun n => In P π n 0 s) ∧
      Tendsto (fun n => In P π n 0 s) atTop (𝓝 (I P π s)) := by
  exact lemma31_core P π s
