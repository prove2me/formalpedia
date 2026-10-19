-- Prove2me | solution 1 for MIPStarRE.Quantum.conicNormalizedSeparatorFunctional_lt_of_sep
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:36:06.192223+00:00
-- url     : https://prove2.me/submissions/d783c77e-d59c-4aff-8fbb-5d4738370496

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/Quantum/FiniteConicDuality.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/Quantum/FiniteConicDuality.lean (solution of MIPStarRE.Quantum.conicNormalizedSeparatorFunctional_lt_of_sep);
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
    (φ : StrongDual ℝ (E × ℝ))
    {y : E} {t : ℝ}
    (hsep : φ (y, t) < 0)
    (hcoeff : conicSeparatorObjectiveCoefficient φ < 0) :
    conicNormalizedSeparatorFunctional φ y < t := by
  have hpositiveCoeff : 0 < -conicSeparatorObjectiveCoefficient φ :=
    neg_pos.mpr hcoeff
  have hsepDecomposed :
      conicSeparatorConstraintFunctional φ y +
          t * conicSeparatorObjectiveCoefficient φ < 0 := by
    rwa [conicSeparator_decompose] at hsep
  have hlt :
      conicSeparatorConstraintFunctional φ y <
        t * (-conicSeparatorObjectiveCoefficient φ) := by
    nlinarith
  rw [conicNormalizedSeparatorFunctional_apply]
  exact (inv_mul_lt_iff₀ hpositiveCoeff).mpr (by simpa [mul_comm] using hlt)
end MIPStarRE.Quantum
