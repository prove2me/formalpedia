-- Prove2me | solution 1 for Grunbaum2003.global_facet_from_compatible_local_facets_and_ridge_gluing
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T22:02:59.689112+00:00
-- url     : https://prove2.me/submissions/4249178a-6dc9-4eb1-96d7-bf95800108f6

import Theorems.Thm_Grunbaum2003_improving_edge_and_global_facet_from_ridge_pairs
import Theorems.Thm_Grunbaum2003_two_maximal_ridges_above_facet_edge_and_maximal_skeleton_dim
import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SkeletonFace
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

set_option autoImplicit false

open Grunbaum2003

theorem solution (d : ℕ) (hd : 3 ≤ d)
    (P Q : Set (Fin (d + 1) → ℝ)) (hP : IsDPolytope P) (hQ : IsDPolytope Q)
    (φ : SkeletonFace P (d + 1 - 2) ≃o SkeletonFace Q (d + 1 - 2))
    (F : PolytopeFace P)
    (hF : F.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F.val).direction = d)
    (hLocal : ∀ (v : Fin (d + 1) → ℝ), IsExposed ℝ P {v} → v ∈ F.val →
      ∃ G : PolytopeFace Q,
        G.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ G.val).direction = d ∧
        (∀ S : SkeletonFace P (d + 1 - 2), v ∈ S.val.val → ((φ S).val ≤ G ↔ S.val ≤ F)))
    (hGlue : ∀ (u w : Fin (d + 1) → ℝ) (G_u G_w : PolytopeFace Q),
      (G_u.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ G_u.val).direction = d) →
      (G_w.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ G_w.val).direction = d) →
      (∀ S : SkeletonFace P (d + 1 - 2), u ∈ S.val.val → ((φ S).val ≤ G_u ↔ S.val ≤ F)) →
      (∀ S : SkeletonFace P (d + 1 - 2), w ∈ S.val.val → ((φ S).val ≤ G_w ↔ S.val ≤ F)) →
      ∀ R₁ R₂ : SkeletonFace P (d + 1 - 2),
        R₁.val ≤ F → R₂.val ≤ F →
        u ∈ R₁.val.val → w ∈ R₁.val.val →
        u ∈ R₂.val.val → w ∈ R₂.val.val →
        ((φ R₁).val.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ (φ R₁).val.val).direction = d - 1) →
        ((φ R₂).val.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ (φ R₂).val.val).direction = d - 1) →
        R₁ ≠ R₂ →
        G_u = G_w) :
    ∃ G : PolytopeFace Q,
      ∀ T : SkeletonFace Q (d + 1 - 2), T.val ≤ G ↔ (φ.symm T).val ≤ F := by
  obtain ⟨hRidges, hMaxDimQ⟩ :=
    Grunbaum2003.two_maximal_ridges_above_facet_edge_and_maximal_skeleton_dim d hd P Q hP hQ F hF
  obtain ⟨G, _, _, hG⟩ :=
    Grunbaum2003.improving_edge_and_global_facet_from_ridge_pairs.2 d hd P Q hP hQ φ F hF
      hLocal hGlue hRidges hMaxDimQ
  refine ⟨G, fun T => ?_⟩
  simpa using hG (φ.symm T)
