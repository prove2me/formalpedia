-- Prove2me | solution 1 for OAI.ThreeState.TreeClauses.Experiment.productPMF_cons
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:22:36.706386+00:00
-- url     : https://prove2.me/submissions/71616190-e82e-49d9-ac45-26fe9b964ee6

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeStateClauses/Products.lean:L73-L97
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeState.TreeClauses.Experiment.productPMF_cons. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ThreeStateTreeClauses
import Definitions.Def_OAI_Probability_ThreeStateClauses_RadialAlgebra
import Definitions.Def_OAI_Probability_ThreeStateClauses_PosteriorLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_DiscreteLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_Products

-- ---- from OAI.Probability.ThreeStateClauses.Products ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Products. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeState.TreeClauses.Experiment

variable {α β : Type*}

lemma productPMF_cons {n : ℕ} (p : Fin (n+1) → PMF α) :
    productPMF p = (p 0).bind (fun a ↦ (productPMF (fun j ↦ p j.succ)).map (Fin.cons a)) := by
  classical
  apply PMF.ext
  intro v
  rw [PMF.bind_apply, tsum_eq_single (v 0)]
  · rw [PMF.map_apply, tsum_eq_single (Fin.tail v)]
    · simp [productPMF_apply, Fin.prod_univ_succ, Fin.tail]
    · intro w hw
      have hn : v ≠ Fin.cons (v 0) w := by
        intro he
        have := congrArg Fin.tail he
        simp only [Fin.tail_cons] at this
        exact hw this.symm
      simp [hn]
  · intro a ha
    have he : (productPMF (fun j ↦ p j.succ)).map (Fin.cons a) v = 0 := by
      rw [PMF.map_apply]
      apply ENNReal.tsum_eq_zero.mpr
      intro w
      have hn : v ≠ Fin.cons a w := by
        intro h
        exact ha (congrFun h 0).symm
      simp [hn]
    rw [he, mul_zero]

end ThreeState.TreeClauses.Experiment

end

end OAI

-- ---- platform node ----
open OAI OAI.ThreeState OAI.ThreeState.TreeClauses OAI.ThreeState.TreeClauses.Experiment
open scoped BigOperators ENNReal NNReal Topology
open Filter
open Set MeasureTheory
open scoped BigOperators ENNReal


theorem solution : type_of% @_root_.OAI.ThreeState.TreeClauses.Experiment.productPMF_cons := @_root_.OAI.ThreeState.TreeClauses.Experiment.productPMF_cons
