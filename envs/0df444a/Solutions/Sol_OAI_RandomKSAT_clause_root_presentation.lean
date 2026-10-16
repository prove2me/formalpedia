-- Prove2me | solution 1 for OAI.RandomKSAT.clause_root_presentation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T19:36:37.271147+00:00
-- url     : https://prove2.me/submissions/88cfc4de-cda2-47ba-8e3c-63132d20a699

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/OmissionCompression.lean:L163-L191
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.clause_root_presentation. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiniteVariance
import Definitions.Def_OAI_Probability_SATVariance_LifetimePotential
import Definitions.Def_OAI_Probability_SATVariance_RootDisintegration__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiberRefresh
import Definitions.Def_OAI_Probability_SATVariance_PairEvolution
import Definitions.Def_OAI_Probability_SATVariance_HiddenTests
import Definitions.Def_OAI_Probability_SATVariance_WeightedRewards
import Definitions.Def_OAI_Probability_SATVariance_CountMoments
import Definitions.Def_OAI_Probability_SATVariance_SupportProbabilities__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_OmissionCompression

-- ---- from OAI.Probability.SATVariance.OmissionCompression ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma joinedAssignment_inl {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n)
    (x : Assignment k × Assignment u) (j : Fin k) :
    joinedAssignment e x (e (Sum.inl j)) = x.1 j := by simp [joinedAssignment]

lemma clause_root_presentation {n k : ℕ} (c : Clause n k) :
    ∃ (e : Fin k ⊕ Fin (n-k) ≃ Fin n) (a : Assignment k),
      ∀ x, ¬Satisfies c (joinedAssignment e x) ↔ x.1 = a := by
  unfold Clause at c
  let R : Set (Fin n) := ↑c.1.1
  have hR : Fintype.card R = k := by
    exact (Fintype.card_of_subtype c.1.1 (fun _ => Iff.rfl)).trans c.1.property
  have hRc : Fintype.card (↥Rᶜ) = n-k := by
    rw [Fintype.card_compl_set, Fintype.card_fin, hR]
  let er : Fin k ≃ R := (Fintype.equivFinOfCardEq hR).symm
  let eu : Fin (n-k) ≃ ↥Rᶜ := (Fintype.equivFinOfCardEq hRc).symm
  let e : Fin k ⊕ Fin (n-k) ≃ Fin n :=
    (Equiv.sumCongr er eu).trans (Equiv.Set.sumCompl R)
  let a : Assignment k := fun j => !(c.2 (er j))
  refine ⟨e,a,fun x => ?_⟩
  have hinl (j : Fin k) : e (Sum.inl j) = (er j).val := rfl
  have hs : Satisfies c (joinedAssignment e x) ↔ ∃ j, x.1 j = c.2 (er j) := by
    constructor
    · rintro ⟨v,hv⟩
      obtain ⟨j,rfl⟩ := er.surjective v
      exact ⟨j, by simpa only [← hinl, joinedAssignment_inl] using hv⟩
    · rintro ⟨j,hj⟩
      exact ⟨er j, by simpa only [← hinl, joinedAssignment_inl] using hj⟩
  rw [hs, not_exists]
  constructor
  · intro h
    exact funext fun j => Bool.eq_not_iff.mpr (h j)
  · intro h j
    exact Bool.eq_not_iff.mp (congrFun h j)

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.clause_root_presentation := @_root_.OAI.RandomKSAT.clause_root_presentation
