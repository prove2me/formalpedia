-- Prove2me | solution 1 for OAI.ThreeState.TreeClauses.Tree.orderedLaw_forget
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:39:51.899691+00:00
-- url     : https://prove2.me/submissions/ffcd38fa-5a1e-42ed-bb49-347770d01b2d

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeStateClauses/OffspringLaws.lean:L46-L62
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeState.TreeClauses.Tree.orderedLaw_forget. The node keeps its source
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
import Definitions.Def_OAI_Probability_ThreeStateClauses_BranchMoments
import Definitions.Def_OAI_Probability_ThreeStateClauses_CompactLimits
import Definitions.Def_OAI_Probability_ThreeStateClauses_RegularStatistics
import Definitions.Def_OAI_Probability_ThreeStateClauses_InformationLoss
import Definitions.Def_OAI_Probability_ThreeStateClauses_RegularReconstruction
import Definitions.Def_OAI_Probability_ThreeStateClauses_ObservedMixtures
import Definitions.Def_OAI_Probability_ThreeStateClauses_OffspringLaws
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

-- ---- from OAI.Probability.ThreeStateClauses.ObservedMixtures ----
namespace OAI

/-! Observed Mixtures. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace ThreeState.TreeClauses.Experiment
-- [generator] trimmed: open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial

variable {X : Type*} [MeasurableSpace X]

variable [TopologicalSpace X] [CompactSpace X] [BorelSpace X]

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeState.TreeClauses.Experiment
-- [generator] trimmed: open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial

variable {α : ℕ → Type*}

lemma sigmaPMF_eq_bind (ρ : PMF ℕ) (p : ∀ n, PMF (α n)) :
    sigmaPMF ρ p = ρ.bind (fun n ↦ (p n).map (Sigma.mk n)) := by
  classical
  apply PMF.ext
  rintro ⟨n,a⟩
  rw [PMF.bind_apply, tsum_eq_single n]
  · simp [PMF.map_apply]
  · intro m hm
    have hn : n ≠ m := Ne.symm hm
    simp [PMF.map_apply, hn]

lemma sigmaPMF_bind {β : Type*} (ρ : PMF ℕ) (p : ∀ n, PMF (α n))
    (K : Sigma α → PMF β) :
    (sigmaPMF ρ p).bind K = ρ.bind (fun n ↦ (p n).bind (fun a ↦ K ⟨n,a⟩)) := by
  rw [sigmaPMF_eq_bind, PMF.bind_bind]
  simp only [PMF.bind_map, Function.comp_def]

lemma sigmaPMF_map {β : Type*} (ρ : PMF ℕ) (p : ∀ n, PMF (α n))
    (T : Sigma α → β) :
    (sigmaPMF ρ p).map T = ρ.bind (fun n ↦ (p n).map (fun a ↦ T ⟨n,a⟩)) :=
  sigmaPMF_bind ρ p (fun z ↦ PMF.pure (T z))

section Measures
variable [∀ n, Countable (α n)] [∀ n, MeasurableSpace (α n)]
  [∀ n, MeasurableSingletonClass (α n)]

end Measures
end ThreeState.TreeClauses.Experiment

end

end OAI

-- ---- from OAI.Probability.ThreeStateClauses.OffspringLaws ----
namespace OAI

/-! Offspring Laws. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeState.TreeClauses.Tree
-- [generator] trimmed: open ThreeState.TreeClauses.Experiment ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Experiment ThreeState.TreeClauses.Radial

lemma orderedLaw_forget (ρ : PMF ℕ) (lam : ℝ) (hlam : Admissible lam) (ℓ : ℕ) (i : Spin) :
    (orderedLaw ρ lam hlam ℓ i).map (forgetOrdered ℓ) = observationLaw lam hlam ρ ℓ i := by
  induction ℓ generalizing i with
  | zero => exact PMF.map_id _
  | succ ℓ ih =>
    rw [orderedLaw, sigmaPMF_map]
    change ρ.bind _ = ρ.bind _
    congr 1
    funext n
    change (productPMF (fun _ : Fin n ↦ (channel lam hlam i).bind (orderedLaw ρ lam hlam ℓ))).map
      ((fun xs : List (Observation ℓ) ↦ (xs : Multiset (Observation ℓ))) ∘
        List.ofFn ∘ (fun v j ↦ forgetOrdered ℓ (v j))) = _
    rw [← PMF.map_comp, ← PMF.map_comp, productPMF_map]
    simp_rw [PMF.map_bind, ih]
    rw [productPMF_list]
    exact (PMF.map_id ((iidList ((channel lam hlam i).bind
      (observationLaw lam hlam ρ ℓ)) n).map (fun xs : List (Observation ℓ) ↦ (xs : Multiset (Observation ℓ))))).symm

end ThreeState.TreeClauses.Tree

end 

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeState.TreeClauses.Tree
open ThreeState.TreeClauses.Experiment

end ThreeState.TreeClauses.Tree

end 

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace ThreeState.TreeClauses.Experiment
-- [generator] trimmed: open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial

end ThreeState.TreeClauses.Experiment

end

end OAI

-- ---- platform node ----
open OAI OAI.ThreeState OAI.ThreeState.TreeClauses OAI.ThreeState.TreeClauses.Tree
open scoped BigOperators ENNReal NNReal Topology
open Filter
open Set MeasureTheory
open scoped BigOperators ENNReal
open ThreeState.TreeClauses.Experiment ThreeState.TreeClauses.Radial


theorem solution : type_of% @_root_.OAI.ThreeState.TreeClauses.Tree.orderedLaw_forget := @_root_.OAI.ThreeState.TreeClauses.Tree.orderedLaw_forget
