-- Prove2me | solution 2 for OAI.DiamondDistortion.headline_all_pairs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:31:33.967639+00:00
-- url     : https://prove2.me/submissions/90a6c3be-0133-48e3-a1b1-75180ee7a383

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/Descent.lean:L104-L115
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.DiamondDistortion.headline_all_pairs.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_DiamondDistortion_headline_all_pairs) verbatim and is proved by it.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry
import Definitions.Def_OAI_Analysis_DiamondDistortion_Orthogonality
import Definitions.Def_OAI_Analysis_DiamondDistortion_ForestModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_DiamondGraph
import Definitions.Def_OAI_Analysis_DiamondDistortion_CoordinateSpace
import Definitions.Def_OAI_Analysis_DiamondDistortion_RecursiveModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_InfimalCost
import Definitions.Def_OAI_Analysis_DiamondDistortion_PathModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_StartModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_CoordinateDual
import Definitions.Def_OAI_Analysis_DiamondDistortion_Incomparable
import Definitions.Def_OAI_Analysis_DiamondDistortion_ModelMaps
import Definitions.Def_OAI_Analysis_DiamondDistortion_EquivalentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_UpperFunction
import Definitions.Def_OAI_Analysis_DiamondDistortion_RecursiveBounds
import Definitions.Def_OAI_Analysis_DiamondDistortion_SignCube
import Definitions.Def_OAI_Analysis_DiamondDistortion_HeadProjections
import Theorems.Thm_OAI_DiamondDistortion_Ancestry_coordinate_predual_approximation
import Theorems.Thm_OAI_DiamondDistortion_Ancestry_finite_heads_of_predecessors
import Theorems.Thm_OAI_DiamondDistortion_Ancestry_separated_lens
import Theorems.Thm_OAI_DiamondDistortion_Diamond_hasDistortion_iff_all_pairs
import Theorems.Thm_OAI_DiamondDistortion_Diamond_squared_stretch_loss
import Theorems.Thm_OAI_DiamondDistortion_Forest_full_dual_approximation

-- ---- from OAI.Analysis.DiamondDistortion.ForestModels ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

lemma infinite_finite_heads : ∀ S : Finset (List ℕ), ∃ K : Finset (List ℕ),
    S ⊆ K ∧ Ancestry.Ancestral (A := infiniteAncestry) (K : Set (List ℕ)) := by
  apply Ancestry.finite_heads_of_predecessors (A := infiniteAncestry)
  intro b
  exact b.inits.toFinset.finite_toSet.subset (by
    intro a ha
    exact List.mem_toFinset.mpr ((List.mem_inits a b).mpr ha))

lemma forest_finite_heads : ∀ S : Finset ForestNode, ∃ K : Finset ForestNode,
    S ⊆ K ∧ Ancestry.Ancestral (A := forestAncestry) (K : Set ForestNode) := by
  apply Ancestry.finite_heads_of_predecessors (A := forestAncestry)
  intro b
  have hfin : (({b.val.1} : Set ℕ) ×ˢ (b.val.2.inits.toFinset : Set (List ℕ))).Finite :=
    (Set.finite_singleton _).prod b.val.2.inits.toFinset.finite_toSet
  have hpre := hfin.preimage (f := (Subtype.val : ForestNode → ℕ × List ℕ)) Subtype.val_injective.injOn
  apply hpre.subset
  intro a ha
  exact ⟨ha.1, List.mem_toFinset.mpr ((List.mem_inits _ _).mpr ha.2)⟩

namespace Forest

end Forest

end DiamondDistortion

end

end OAI

-- ---- from OAI.Analysis.DiamondDistortion.DiamondGraph ----
namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace Diamond

lemma endpoint_ne (n : ℕ) (e : Edge n) : endpoint n e false ≠ endpoint n e true := by
  cases n with
  | zero => simp [endpoint]
  | succ n =>
    rcases e with ⟨e,i,b⟩
    cases b <;> simp [endpoint]

lemma adj_iff {n : ℕ} {u v : Vertex n} : (graph n).Adj u v ↔
    ∃ e : Edge n, (u=endpoint n e false ∧ v=endpoint n e true) ∨
      (u=endpoint n e true ∧ v=endpoint n e false) := by
  rw [graph,SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_,⟨e,hu,hv⟩ | ⟨e,hv,hu⟩⟩
    · exact ⟨e,Or.inl ⟨hu,hv⟩⟩
    · exact ⟨e,Or.inr ⟨hu,hv⟩⟩
  · rintro ⟨e,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩
    · exact ⟨endpoint_ne n e,Or.inl ⟨e,rfl,rfl⟩⟩
    · exact ⟨(endpoint_ne n e).symm,Or.inr ⟨e,rfl,rfl⟩⟩

lemma adj_endpoint (n : ℕ) (e : Edge n) :
    (graph n).Adj (endpoint n e false) (endpoint n e true) :=
  adj_iff.mpr ⟨e,Or.inl ⟨rfl,rfl⟩⟩

lemma distance_edge (n : ℕ) (e : Edge n) :
    distance n (endpoint n e false) (endpoint n e true)=1/(2:ℝ)^n := by
  rw [distance,SimpleGraph.dist_eq_one_iff_adj.mpr (adj_endpoint n e),Nat.cast_one,Nat.cast_ofNat]

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma distortion_bound (hX : QuadraticLens X) (k : ℕ) (f : Vertex k → X)
    (D s : ℝ) (h : HasDistortion k f D s) : 1+(k:ℝ)/4 ≤ D^2 := by
  obtain ⟨hD,hs,h⟩ := h
  have hbound : ∀ e,‖slope f e‖^2 ≤ (D*s)^2 := by
    intro e
    have he := (h (endpoint k e false) (endpoint k e true)).2
    rw [distance_edge] at he
    have hh : ‖slope f e‖ ≤ D*s := by
      rw [slope,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0<(2:ℝ)^k),norm_sub_rev]
      calc
        _ ≤ (2:ℝ)^k*(D*s*(1/(2:ℝ)^k)) := mul_le_mul_of_nonneg_left he (by positivity)
        _ = _ := by field_simp
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by linarith) hs.le)).mpr hh
  have hb := squared_stretch_loss hX k f hs (fun u v => (h u v).1) hbound
  have hp : 0 < s^2 := sq_pos_of_pos hs
  have hmul : s^2*(1+(k:ℝ)/4) ≤ s^2*D^2 := by nlinarith only [hb]
  exact (mul_le_mul_iff_right₀ hp).mp hmul

end Diamond

/-- The finite forest lens property follows from the proved pooled estimate and
    the proved approximation of its full dual. -/
theorem forest_quadratic_lens : Diamond.QuadraticLens ForestDual := by
  intro x z R ε hR hε hp hm hs
  exact Ancestry.separated_lens (A := forestAncestry) forest_finite_heads
    (fun η hη => Forest.full_dual_approximation x hη) z hR hε hp hm hs

/-- The infinite-height assertion is only for its closed coordinate span,
    not for the full infinite-height dual. -/
theorem infinite_quadratic_lens : Diamond.QuadraticLens InfinitePredual := by
  intro x z R ε hR hε hp hm hs
  exact Ancestry.separated_lens (A := infiniteAncestry) infinite_finite_heads
    (fun η hη => Ancestry.coordinate_predual_approximation (A := infiniteAncestry)
      infinite_finite_heads x.property hη) (fun i => (z i).val) hR hε hp hm hs

theorem headline : Headline := by
  constructor
  · exact fun k f D s h => Diamond.distortion_bound forest_quadratic_lens k f D s h
  · exact fun k f D s h => Diamond.distortion_bound infinite_quadratic_lens k f D s h

end DiamondDistortion

end

end OAI

-- ---- from OAI.Analysis.DiamondDistortion.Descent ----
namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

open scoped ENNReal

namespace PathModel
-- [generator] trimmed: open RecursiveModel DirectLayers SignCube
open RecursiveModel SignCube
end PathModel

namespace DirectSegmentApplications

end DirectSegmentApplications

namespace Diamond
variable {X : Type*} [NormedAddCommGroup X]
end Diamond

theorem headline_all_pairs :
    (∀ (k : ℕ) (f : Diamond.Vertex k → ForestDual) (D s : ℝ),
      0 < s → (∀ u v,s*Diamond.distance k u v ≤ ‖f u-f v‖ ∧
        ‖f u-f v‖ ≤ D*s*Diamond.distance k u v) → 1+(k:ℝ)/4 ≤ D^2) ∧
    (∀ (k : ℕ) (f : Diamond.Vertex k → InfinitePredual) (D s : ℝ),
      0 < s → (∀ u v,s*Diamond.distance k u v ≤ ‖f u-f v‖ ∧
        ‖f u-f v‖ ≤ D*s*Diamond.distance k u v) → 1+(k:ℝ)/4 ≤ D^2) := by
  constructor
  · intro k f D s hs h
    exact headline.1 k f D s ((Diamond.hasDistortion_iff_all_pairs f D s).mpr ⟨hs,h⟩)
  · intro k f D s hs h
    exact headline.2 k f D s ((Diamond.hasDistortion_iff_all_pairs f D s).mpr ⟨hs,h⟩)

end DiamondDistortion

end

end OAI

-- ---- mission target ----
open OAI OAI.DiamondDistortion
universe u v
open scoped BigOperators Classical Topology
open Set
open scoped ENNReal

namespace OAI
namespace DiamondDistortion
theorem _root_.solution :
    (∀ (k : ℕ) (f : Diamond.Vertex k → ForestDual) (D s : ℝ),
      0 < s → (∀ u v,s*Diamond.distance k u v ≤ ‖f u-f v‖ ∧
        ‖f u-f v‖ ≤ D*s*Diamond.distance k u v) → 1+(k:ℝ)/4 ≤ D^2) ∧
    (∀ (k : ℕ) (f : Diamond.Vertex k → InfinitePredual) (D s : ℝ),
      0 < s → (∀ u v,s*Diamond.distance k u v ≤ ‖f u-f v‖ ∧
        ‖f u-f v‖ ≤ D*s*Diamond.distance k u v) → 1+(k:ℝ)/4 ≤ D^2) := by
  first
    | exact OAI.DiamondDistortion.headline_all_pairs
    | (apply OAI.DiamondDistortion.headline_all_pairs <;> assumption)
    | (intros; apply OAI.DiamondDistortion.headline_all_pairs <;> assumption)
end DiamondDistortion
end OAI
