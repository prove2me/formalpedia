-- Prove2me | solution 1 for GlobalTheory.norm_fwdDiff_iter_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:27:12.206998+00:00
-- url     : https://prove2.me/submissions/b5b239ed-746e-4f94-8bd4-ad2629696ebe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LatticeFourierOfContDiffFiniteDimensional

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Set
open scoped RealInnerProductSpace Real Pointwise ContDiff
noncomputable section
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
local notation "e[" t "]" => Complex.exp (2 * (π : ℂ) * Complex.I * ((t : ℝ) : ℂ))
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
local notation "L*" => LinearMap.BilinForm.dualSubmodule (innerₗ E) L
variable {L}
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
namespace GlobalTheory
theorem _root_.solution (c : E) (k : ℕ) {A : E → V} (hA : ContDiff ℝ k A) {M : ℝ}
    (hM : ∀ x, ‖iteratedFDeriv ℝ k A x‖ ≤ M) (x : E) :
    ‖(fwdDiff c)^[k] A x‖ ≤ ‖c‖ ^ k * M := by
  induction k generalizing A M with
  | zero => simpa using hM x
  | succ k ih =>
    have hA' : ContDiff ℝ k A := hA.of_le (by exact_mod_cast k.le_succ)
    have hAc : ContDiff ℝ k fun y ↦ A (y + c) := hA'.comp (by fun_prop)
    rw [Function.iterate_succ_apply, pow_succ, mul_assoc]
    refine ih (hAc.sub hA') fun y ↦ ?_
    have hd : Differentiable ℝ (iteratedFDeriv ℝ k A) :=
      hA.differentiable_iteratedFDeriv (by exact_mod_cast k.lt_succ_self)
    have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (s := univ) (C := M)
      (f := iteratedFDeriv ℝ k A) (x := y) (y := y + c) (fun z _ ↦ hd z)
      (fun z _ ↦ by rw [norm_fderiv_iteratedFDeriv]; exact hM z) convex_univ trivial trivial
    rw [fun_iteratedFDeriv_sub_apply hAc.contDiffAt hA'.contDiffAt, iteratedFDeriv_comp_add_right]
    simpa [mul_comm] using this
end GlobalTheory
