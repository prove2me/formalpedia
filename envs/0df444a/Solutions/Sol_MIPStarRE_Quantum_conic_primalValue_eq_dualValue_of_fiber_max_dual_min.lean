-- Prove2me | solution 1 for MIPStarRE.Quantum.conic_primalValue_eq_dualValue_of_fiber_max_dual_min
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:36:58.383708+00:00
-- url     : https://prove2.me/submissions/31d1af10-2d03-45e7-a15a-0582306ffe34

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/Quantum/FiniteConicDuality.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/Quantum/FiniteConicDuality.lean (solution of MIPStarRE.Quantum.conic_primalValue_eq_dualValue_of_fiber_max_dual_min);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteConicDuality
import Theorems.Thm_MIPStarRE_Quantum_conicFunctionalDualFeasible_normalizedSeparator
import Theorems.Thm_MIPStarRE_Quantum_conicNormalizedSeparatorFunctional_lt_of_sep
import Theorems.Thm_MIPStarRE_Quantum_conicSeparatorObjectiveCoefficient_neg_of_above

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPStarRE.Quantum
set_option backward.isDefEq.respectTransparency false
theorem _root_.solution
    {F : Type*}
    [TopologicalSpace F] [AddCommGroup F] [IsTopologicalAddGroup F]
    [Module ℝ F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
    (C : ProperCone ℝ (F × ℝ))
    {y : F} {p d : ℝ}
    (hprimalMem : (y, p) ∈ C)
    (hprimalMax : ∀ {t : ℝ}, (y, t) ∈ C → t ≤ p)
    (hdualMin : ∀ ψ : StrongDual ℝ F,
      (∀ z ∈ C, z.2 ≤ ψ z.1) → d ≤ ψ y)
    (hweak : p ≤ d) :
    p = d := by
  have hd_le_p : d ≤ p := by
    by_contra hnot
    have hp_lt_d : p < d := lt_of_not_ge hnot
    let t : ℝ := (p + d) / 2
    have hp_lt_t : p < t := by
      dsimp [t]
      nlinarith
    have ht_lt_d : t < d := by
      dsimp [t]
      nlinarith
    have hnotMem : (y, t) ∉ C := by
      intro hyt
      exact (not_lt_of_ge (hprimalMax hyt)) hp_lt_t
    obtain ⟨φ, hφ_nonneg, hsep⟩ := C.hyperplane_separation_point hnotMem
    have hcoeff : conicSeparatorObjectiveCoefficient φ < 0 :=
      conicSeparatorObjectiveCoefficient_neg_of_above
        (C := (C : Set (F × ℝ))) φ hφ_nonneg hprimalMem hsep hp_lt_t
    let ψ : StrongDual ℝ F := conicNormalizedSeparatorFunctional φ
    have hψfeasible : ∀ z ∈ C, z.2 ≤ ψ z.1 := by
      simpa [ψ] using
        conicFunctionalDualFeasible_normalizedSeparator
          (C := (C : Set (F × ℝ))) φ hφ_nonneg hcoeff
    have hd_le_ψ : d ≤ ψ y := hdualMin ψ hψfeasible
    have hψ_lt_t : ψ y < t :=
      conicNormalizedSeparatorFunctional_lt_of_sep φ hsep hcoeff
    nlinarith
  exact le_antisymm hweak hd_le_p
end MIPStarRE.Quantum
