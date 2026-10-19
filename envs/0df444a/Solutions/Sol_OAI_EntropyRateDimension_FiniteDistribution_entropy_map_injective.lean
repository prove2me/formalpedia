-- Prove2me | solution 1 for OAI.EntropyRateDimension.FiniteDistribution.entropy_map_injective
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:22:58.83899+00:00
-- url     : https://prove2.me/submissions/de4a9801-3eaf-476a-b493-4c8e98beb18c

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteDistribution
universe uα uβ uγ
open scoped BigOperators ENNReal
open MeasureTheory
attribute [local instance] Classical.propDecidable
theorem h44_mapw {α : Type*} {β : Type*} (p : FiniteDistribution α) (f : α → β) (b : β) :
    (p.map f).weight b = ∑ a ∈ p.support, if f a = b then p.weight a else 0 := by
  unfold FiniteDistribution.map FiniteEntropy.mass
  dsimp only
  rw [Finset.sum_filter]

theorem solution {α : Type uα} {β : Type uβ} (p : FiniteDistribution α)
    (f : α → β) (hf : Function.Injective f) : (p.map f).entropy=p.entropy := by
  unfold entropy
  rw [← hf.tsum_eq]
  · congr 1
    ext a
    rw [h44_mapw]
    congr 1
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      rw [if_neg (fun h => hb (hf h))]
    · intro ha
      rw [if_pos rfl]
      exact p.vanish a ha
  · intro b hb
    by_contra hr
    apply hb
    show Real.negMulLog ((p.map f).weight b) = 0
    rw [h44_mapw, Finset.sum_eq_zero (fun a _ => if_neg (fun h => hr ⟨a, h⟩))]
    exact Real.negMulLog_zero

