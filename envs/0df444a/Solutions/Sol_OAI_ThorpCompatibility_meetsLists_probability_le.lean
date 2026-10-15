-- Prove2me | solution 1 for OAI.ThorpCompatibility.meetsLists_probability_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T00:47:59.63916+00:00
-- url     : https://prove2.me/submissions/7f0cf6e9-801b-42b0-add9-0a14fc4bee9b

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/ListIncidence.lean:L53-L85
-- (upload_full_project.md Phase 4): solution for node OAI.ThorpCompatibility.meetsLists_probability_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_ConditionalEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_LightRescaling
import Definitions.Def_OAI_Probability_ThorpCompatibility_Prediction
import Definitions.Def_OAI_Probability_ThorpCompatibility_RankLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Model
import Definitions.Def_OAI_Probability_ThorpCompatibility_EntropyChain
import Definitions.Def_OAI_Probability_ThorpCompatibility_GridEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_GridExposure
import Definitions.Def_OAI_Probability_ThorpCompatibility_ClumpCost
import Definitions.Def_OAI_Probability_ThorpCompatibility_PermutationProbability
import Definitions.Def_OAI_Probability_ThorpCompatibility_ListIncidence
import Theorems.Thm_OAI_ThorpCompatibility_prescribed_function_probability_le

-- ---- from OAI.Probability.ThorpCompatibility.PermutationProbability ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset
open Finset
lemma uniformProbability_def {α : Type*} [Fintype α] (P : α → Prop)
    [DecidablePred P] :
    uniformProbability P = ((Finset.univ.filter P).card : ℝ) / Fintype.card α := by
  unfold uniformProbability
  congr

lemma uniformProbability_nonneg {α : Type*} [Fintype α] (P : α → Prop) :
    0 ≤ uniformProbability P := by
  unfold uniformProbability
  positivity

lemma uniformProbability_eq_zero {α : Type*} [Fintype α] (P : α → Prop)
    (h : ¬ ∃ x, P x) : uniformProbability P = 0 := by
  classical
  have hP : ∀ x, ¬ P x := fun x hx => h ⟨x, hx⟩
  simp [uniformProbability, hP]

lemma uniformProbability_all {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι]
    (P : ι → α → Prop) :
    uniformProbability (fun f : ι → α => ∀ i, P i (f i)) =
      ∏ i, uniformProbability (P i) := by
  classical
  rw [uniformProbability_def]
  have hset : Finset.univ.filter (fun f : ι → α => ∀ i, P i (f i)) =
      Fintype.piFinset (fun i => Finset.univ.filter (P i)) := by
    ext f
    simp
  rw [show (Finset.univ.filter (fun f : ι → α => ∀ i, P i (f i))).card =
      ∏ i, (Finset.univ.filter (P i)).card by
    rw [hset, Fintype.card_piFinset]]
  simp only [uniformProbability, Fintype.card_pi, Nat.cast_prod, Finset.prod_div_distrib]

end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.ListIncidence ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
private abbrev Finset.prod_le_prod₀ := @Finset.prod_le_prod

namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset
open Finset
lemma lists_incidence_count {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

    (S : β × β → Finset α) (r : α → Equiv.Perm β) (hr : MeetsLists S r) :
    ∑ i, (Finset.univ.filter (fun j => i ∈ S (j, r i j))).card =
      ∑ b, (S b).card := by
  have hk (i : α) (j k : β) : i ∈ S (j, k) ↔ k = r i j ∧ i ∈ S (j, r i j) := by
    constructor
    · intro h
      exact ⟨(hr j k i h).symm, by simpa [hr j k i h] using h⟩
    · rintro ⟨rfl, h⟩
      exact h
  have hc (s : Finset α) : s.card = ∑ i, if i ∈ s then 1 else 0 := by simp
  calc
    _ = ∑ i, ∑ j, ∑ k, if i ∈ S (j, k) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.card_filter]
      apply Finset.sum_congr rfl
      intro j _
      symm
      calc
        _ = ∑ k, if k = r i j then (if i ∈ S (j, r i j) then 1 else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro k _
          by_cases he : k = r i j
          · subst k
            simp
          · have hmem : i ∉ S (j, k) := fun h => he (hr j k i h).symm
            simp [he, hmem]
        _ = _ := by simp
    _ = ∑ j, ∑ k, ∑ i, if i ∈ S (j, k) then 1 else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = _ := by simp only [Fintype.sum_prod_type, hc]

lemma meetsLists_probability_le {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (hn : 0 < Fintype.card β)
    (S : β × β → Finset α) :
    uniformProbability (MeetsLists S) ≤
      (Real.exp 1 / Fintype.card β) ^ (∑ b, (S b).card) := by
  classical
  by_cases h : ∃ r, MeetsLists S r
  · obtain ⟨r, hr⟩ := h
    let s : α → Finset β := fun i => Finset.univ.filter (fun j => i ∈ S (j, r i j))
    have hP : MeetsLists S = (fun r' => ∀ i, ∀ j ∈ s i, r' i j = r i j) := by
      funext r'
      apply propext
      constructor
      · intro hr' i j hj
        exact hr' j (r i j) i ((Finset.mem_filter.mp hj).2)
      · intro hr' j k i hi
        have he := hr j k i hi
        have hm : j ∈ s i := by simpa [s, he] using hi
        exact (hr' i j hm).trans he
    rw [hP, uniformProbability_all (fun i (σ : Equiv.Perm β) => ∀ j ∈ s i, σ j = r i j)]
    calc
      _ ≤ ∏ i, (Real.exp 1 / Fintype.card β) ^ (s i).card := by
        apply Finset.prod_le_prod₀
        · intro i _
          exact uniformProbability_nonneg _
        · intro i _
          rw [uniformProbability_def]
          exact prescribed_function_probability_le hn (s i) (r i)
      _ = (Real.exp 1 / Fintype.card β) ^ (∑ i, (s i).card) :=
        Finset.prod_pow_eq_pow_sum Finset.univ _ _
      _ = _ := by rw [lists_incidence_count S r hr]
  · rw [uniformProbability_eq_zero _ h]
    positivity

end ThorpCompatibility

end OAI

-- ---- platform node ----
open OAI OAI.ThorpCompatibility
open scoped Classical
open Finset
open Finset

theorem solution {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (hn : 0 < Fintype.card β)
    (S : β × β → Finset α) :
    uniformProbability (MeetsLists S) ≤
      (Real.exp 1 / Fintype.card β) ^ (∑ b, (S b).card) := by
  first
    | exact OAI.ThorpCompatibility.meetsLists_probability_le hn S
    | exact OAI.ThorpCompatibility.meetsLists_probability_le
    | (apply OAI.ThorpCompatibility.meetsLists_probability_le <;> assumption)
    | (intros; apply OAI.ThorpCompatibility.meetsLists_probability_le <;> assumption)
