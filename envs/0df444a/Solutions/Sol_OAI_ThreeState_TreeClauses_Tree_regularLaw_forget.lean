-- Prove2me | solution 1 for OAI.ThreeState.TreeClauses.Tree.regularLaw_forget
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:28:36.068574+00:00
-- url     : https://prove2.me/submissions/dc0f694b-7b64-4fa5-baf6-a98ddfb1b5ad

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeStateClauses/RegularLaw.lean:L74-L87
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeState.TreeClauses.Tree.regularLaw_forget. The node keeps its source
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
import Theorems.Thm_OAI_ThreeState_TreeClauses_Tree_productPMF_list

-- ---- from OAI.Probability.ThreeStateClauses.Products ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-! Products. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeState.TreeClauses.Experiment

variable {α β : Type*}

lemma productPMF_pure {n : ℕ} (v : Fin n → α) :
    productPMF (fun j ↦ PMF.pure (v j)) = PMF.pure v := by
  classical
  apply PMF.ext
  intro w
  by_cases h : w = v
  · subst w; simp
  · have hn : ∃ j, w j ≠ v j := by simpa only [funext_iff, not_forall] using h
    obtain ⟨j,hj⟩ := hn
    simp only [productPMF_apply, PMF.pure_apply, ite_eq_right h]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

lemma productPMF_bind {n : ℕ} (p : Fin n → PMF α) (K : Fin n → α → PMF β) :
    (productPMF p).bind (fun v ↦ productPMF (fun j ↦ K j (v j))) =
      productPMF (fun j ↦ (p j).bind (K j)) := by
  apply PMF.ext
  intro w
  simp only [PMF.bind_apply, productPMF_apply, ← Finset.prod_mul_distrib]
  exact ennreal_tsum_fin_product n (fun j a ↦ p j a*K j a (w j))

lemma productPMF_map {n : ℕ} (p : Fin n → PMF α) (T : Fin n → α → β) :
    (productPMF p).map (fun v j ↦ T j (v j)) = productPMF (fun j ↦ (p j).map (T j)) := by
  change (productPMF p).bind (fun v ↦ PMF.pure (fun j ↦ T j (v j))) = _
  simp_rw [← productPMF_pure]
  exact productPMF_bind p (fun j a ↦ PMF.pure (T j a))

end ThreeState.TreeClauses.Experiment

end

end OAI

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

lemma regularLaw_forget (b : ℕ) (lam : ℝ) (hlam : Admissible lam) (ℓ : ℕ) (i : Spin) :
    (regularLaw b lam hlam ℓ i).map (forgetRegular b ℓ) =
      observationLaw lam hlam (PMF.pure b) ℓ i := by
  induction ℓ generalizing i with
  | zero => exact PMF.map_id _
  | succ ℓ ih =>
    simp only [observationLaw, PMF.pure_bind]
    change (productPMF (fun _ : Fin b ↦ (channel lam hlam i).bind (regularLaw b lam hlam ℓ))).map
      ((fun xs : List (Observation ℓ) ↦ (xs : Multiset (Observation ℓ))) ∘
        List.ofFn ∘ (fun v j ↦ forgetRegular b ℓ (v j))) = _
    rw [← PMF.map_comp, ← PMF.map_comp, productPMF_map]
    simp_rw [PMF.map_bind, ih]
    rw [productPMF_list]
    exact (PMF.map_id _).symm

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


theorem solution : type_of% @_root_.OAI.ThreeState.TreeClauses.Tree.regularLaw_forget := @_root_.OAI.ThreeState.TreeClauses.Tree.regularLaw_forget
