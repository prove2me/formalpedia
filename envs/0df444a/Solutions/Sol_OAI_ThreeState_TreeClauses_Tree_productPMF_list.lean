-- Prove2me | solution 1 for OAI.ThreeState.TreeClauses.Tree.productPMF_list
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:26:41.293895+00:00
-- url     : https://prove2.me/submissions/831a1a5b-fff4-4c26-a994-f8c39662bc75

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeStateClauses/RegularLaw.lean:L54-L72
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeState.TreeClauses.Tree.productPMF_list. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ThreeStateTreeClauses
import Definitions.Def_OAI_Probability_ThreeStateClauses_RadialAlgebra
import Definitions.Def_OAI_Probability_ThreeStateClauses_PosteriorLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_DiscreteLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_Products
import Definitions.Def_OAI_Probability_ThreeStateClauses_Degradation
import Definitions.Def_OAI_Probability_ThreeStateClauses_RegularLaw
import Theorems.Thm_OAI_ThreeState_TreeClauses_Experiment_productPMF_cons

-- ---- from OAI.Probability.ThreeStateClauses.RegularLaw ----
namespace OAI

/-! Regular Law. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeState.TreeClauses.Tree
open ThreeState.TreeClauses.Experiment

lemma productPMF_list {α : Type} (p : PMF α) (n : ℕ) :
    (productPMF (fun _ : Fin n ↦ p)).map List.ofFn = iidList p n := by
  induction n with
  | zero =>
    have h : productPMF (fun _ : Fin 0 ↦ p) = PMF.pure (fun i : Fin 0 ↦ i.elim0) := by
      apply PMF.ext
      intro v
      simp [PMF.pure_apply, Subsingleton.elim v (fun i : Fin 0 ↦ i.elim0)]
    rw [h, PMF.pure_map]
    rfl
  | succ n ih =>
    rw [productPMF_cons, PMF.map_bind]
    change (p.bind (fun a ↦ _)) = p.bind (fun a ↦ _)
    congr 1
    funext a
    rw [PMF.map_comp]
    have he : (List.ofFn ∘ Fin.cons (n := n) (α := fun _ ↦ α) a : (Fin n → α) → List α) = List.cons a ∘ List.ofFn := by
      funext v; exact List.ofFn_cons a v
    rw [he, ← PMF.map_comp, ih]

end ThreeState.TreeClauses.Tree

end

end OAI

-- ---- platform node ----
open OAI OAI.ThreeState OAI.ThreeState.TreeClauses OAI.ThreeState.TreeClauses.Tree
open scoped BigOperators ENNReal NNReal Topology
open Filter
open Set MeasureTheory
open scoped BigOperators ENNReal
open ThreeState.TreeClauses.Experiment


theorem solution : type_of% @_root_.OAI.ThreeState.TreeClauses.Tree.productPMF_list := @_root_.OAI.ThreeState.TreeClauses.Tree.productPMF_list
