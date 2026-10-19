-- Prove2me | solution 1 for OAI.ReflexiveFixedPoints.exists_separable_invariant_subset
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T16:59:04.244527+00:00
-- url     : https://prove2.me/submissions/6367bb82-aab6-4729-8834-1761e7c62a55

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Nonexpansive/SeparableInvariant.lean:L33-L110
-- (upload_full_project.md Phase 4): solution for node OAI.ReflexiveFixedPoints.exists_separable_invariant_subset. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ReflexiveFixedPoints
import Definitions.Def_OAI_Analysis_Nonexpansive_Model
import Definitions.Def_OAI_Analysis_Nonexpansive_Basic

-- ---- from OAI.Analysis.Nonexpansive.SeparableInvariant ----
namespace OAI

/-!
# A separable closed convex invariant subset

Starting at one point, repeatedly adjoin its current set's image and take
the closed convex hull. The closure of the increasing union is invariant.
The map always has domain `C`; no ambient extension is used.
-/

noncomputable section

open Set TopologicalSpace

namespace ReflexiveFixedPoints

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The successive closed convex hulls used in the separable reduction. -/
private def separableInvariantStage (C : Set X) (F : C → C) (a : X) : ℕ → Set X
  | 0 => {a}
  | n + 1 => closure (convexHull ℝ
      (separableInvariantStage C F a n ∪
        (fun x : C => (F x : X)) ''
          ((Subtype.val : C → X) ⁻¹' separableInvariantStage C F a n)))

/-- Every nonempty closed bounded convex set with a nonexpansive self-map
contains a nonempty closed bounded convex separable invariant subset. -/
theorem exists_separable_invariant_subset {C : Set X}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hbounded : Bornology.IsBounded C)
    (hconvex : Convex ℝ C) (F : C → C) (hF : LipschitzWith 1 F) :
    ∃ S : Set X, S ⊆ C ∧ S.Nonempty ∧ IsClosed S ∧ Bornology.IsBounded S ∧
      Convex ℝ S ∧ IsSeparable S ∧ InvariantSubset C F S := by
  obtain ⟨a, ha⟩ := hne
  let A : ℕ → Set X := separableInvariantStage C F a
  let g : C → X := fun x => (F x : X)
  have hg : Continuous g := continuous_subtype_val.comp hF.continuous
  have hsucc (n : ℕ) :
      A (n + 1) = closure (convexHull ℝ
        (A n ∪ g '' ((Subtype.val : C → X) ⁻¹' A n))) := rfl
  have hAsub : ∀ n, A n ⊆ C := by
    intro n
    induction n with
    | zero =>
        simpa only [A, separableInvariantStage, singleton_subset_iff] using ha
    | succ n ih =>
        rw [hsucc]
        apply closure_minimal _ hclosed
        apply convexHull_min _ hconvex
        rintro x (hx | ⟨y, hy, rfl⟩)
        · exact ih hx
        · exact (F y).property
  have hAmono : Monotone A := by
    apply monotone_nat_of_le_succ
    intro n x hx
    rw [hsucc]
    exact subset_closure (subset_convexHull ℝ _ (Or.inl hx))
  have hAconv : ∀ n, Convex ℝ (A n) := by
    intro n
    cases n with
    | zero => exact convex_singleton a
    | succ n =>
        rw [hsucc]
        exact (convex_convexHull ℝ _).closure
  have hAsep : ∀ n, IsSeparable (A n) := by
    intro n
    induction n with
    | zero => exact (countable_singleton a).isSeparable
    | succ n ih =>
        rw [hsucc]
        have hp : IsSeparable ((Subtype.val : C → X) ⁻¹' A n) :=
          Topology.IsEmbedding.subtypeVal.isSeparable_preimage ih
        have hu : IsSeparable (A n ∪ g '' ((Subtype.val : C → X) ⁻¹' A n)) :=
          ih.union (hp.image hg)
        apply IsSeparable.closure
        exact (hu.span (R := ℝ)).mono
          (convexHull_min Submodule.subset_span (Submodule.span ℝ _).convex)
  let U : Set X := ⋃ n, A n
  have hUsub : U ⊆ C := iUnion_subset hAsub
  have hSsub : closure U ⊆ C := closure_minimal hUsub hclosed
  have hUconv : Convex ℝ U :=
    hAmono.directed_le.convex_iUnion (fun {n} => hAconv n)
  have hUimage : (Subtype.val : C → X) '' ((Subtype.val : C → X) ⁻¹' U) = U := by
    apply Subset.antisymm
    · exact image_preimage_subset _ _
    · intro x hx
      exact ⟨⟨x, hUsub hx⟩, hx, rfl⟩
  have hmap : MapsTo g ((Subtype.val : C → X) ⁻¹' U) U := by
    intro x hx
    change (x : X) ∈ ⋃ n, A n at hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    apply mem_iUnion.mpr
    refine ⟨n + 1, ?_⟩
    rw [hsucc]
    exact subset_closure (subset_convexHull ℝ _ (Or.inr ⟨x, hn, rfl⟩))
  refine ⟨closure U, hSsub, ?_, isClosed_closure, hbounded.subset hSsub,
    hUconv.closure, (IsSeparable.iUnion hAsep).closure, ?_⟩
  · refine ⟨a, subset_closure ?_⟩
    exact mem_iUnion.mpr ⟨0, by simp only [A, separableInvariantStage, mem_singleton_iff]⟩
  · intro x hx
    have hxc : x ∈ closure ((Subtype.val : C → X) ⁻¹' U) := by
      rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, hUimage]
      exact hx
    exact hmap.closure hg hxc

end ReflexiveFixedPoints

end

end OAI

-- ---- platform node ----
open OAI OAI.ReflexiveFixedPoints
open Set TopologicalSpace


theorem solution.{u} : type_of% @_root_.OAI.ReflexiveFixedPoints.exists_separable_invariant_subset.{u} := @_root_.OAI.ReflexiveFixedPoints.exists_separable_invariant_subset.{u}
