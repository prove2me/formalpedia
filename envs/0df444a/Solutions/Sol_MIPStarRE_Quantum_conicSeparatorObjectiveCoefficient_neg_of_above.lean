-- Prove2me | solution 1 for MIPStarRE.Quantum.conicSeparatorObjectiveCoefficient_neg_of_above
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:35:23.723858+00:00
-- url     : https://prove2.me/submissions/32a3b60b-2e3a-4b16-847f-16f96dc2bf23

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/Quantum/FiniteConicDuality.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/Quantum/FiniteConicDuality.lean (solution of MIPStarRE.Quantum.conicSeparatorObjectiveCoefficient_neg_of_above);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteConicDuality

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPStarRE.Quantum
section
set_option backward.isDefEq.respectTransparency false
/-- A separator on `E × ℝ` is the sum of its constraint-coordinate part and
objective-coordinate part. -/
theorem conicSeparator_decompose
    {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    (φ : StrongDual ℝ (E × ℝ)) (y : E) (t : ℝ) :
    φ (y, t) =
      conicSeparatorConstraintFunctional φ y +
        t * conicSeparatorObjectiveCoefficient φ := by
  rw [← ContinuousLinearMap.comp_inl_add_comp_inr φ (y, t)]
  simp only [conicSeparatorConstraintFunctional, conicSeparatorObjectiveCoefficient]
  congr 1
  simpa using
    ((φ.comp (ContinuousLinearMap.inr ℝ E ℝ)).map_smul t (1 : ℝ))
end
end MIPStarRE.Quantum

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPStarRE.Quantum
set_option backward.isDefEq.respectTransparency false
theorem _root_.solution
    {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    {C : Set (E × ℝ)}
    (φ : StrongDual ℝ (E × ℝ))
    {y : E} {s t : ℝ}
    (hφ : ∀ z ∈ C, 0 ≤ φ z)
    (hys : (y, s) ∈ C)
    (hyt : φ (y, t) < 0)
    (hst : s < t) :
    conicSeparatorObjectiveCoefficient φ < 0 := by
  have hs_nonneg :
      0 ≤
        conicSeparatorConstraintFunctional φ y +
          s * conicSeparatorObjectiveCoefficient φ := by
    have hnonneg := hφ (y, s) hys
    rwa [conicSeparator_decompose] at hnonneg
  have ht_neg :
      conicSeparatorConstraintFunctional φ y +
          t * conicSeparatorObjectiveCoefficient φ < 0 := by
    rwa [conicSeparator_decompose] at hyt
  by_contra hnot
  have hcoeff_nonneg : 0 ≤ conicSeparatorObjectiveCoefficient φ :=
    le_of_not_gt hnot
  have hmul :
      s * conicSeparatorObjectiveCoefficient φ ≤
        t * conicSeparatorObjectiveCoefficient φ :=
    mul_le_mul_of_nonneg_right (le_of_lt hst) hcoeff_nonneg
  nlinarith
end MIPStarRE.Quantum
