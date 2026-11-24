-- Prove2me | solution 1 for GlobalTheory.latticeFourierCoeff_fwdDiff_iter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:29:12.880912+00:00
-- url     : https://prove2.me/submissions/06965326-93fb-49ca-8dc0-ff8097bc99af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LatticeFourierOfContDiffFiniteDimensional
import Theorems.Thm_GlobalTheory_latticeFourierCoeff_comp_add
import Theorems.Thm_GlobalTheory_latticeFourierCoeff_sub

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
namespace GlobalTheory
theorem _root_.solution {A : E → V} (hA : ∀ x ∈ L, Function.Periodic A x)
    (hc : Continuous A) {ν : E} (hν : ν ∈ L*) (c : E) (k : ℕ) :
    latticeFourierCoeff L ((fwdDiff c)^[k] A) ν =
      (e[⟪ν, c⟫] - 1) ^ k • latticeFourierCoeff L A ν := by
  induction k generalizing A with
  | zero => simp
  | succ k ih =>
    have h1 : ∀ x ∈ L, Function.Periodic (fwdDiff c A) x := fun x hx b ↦ by
      simp only [fwdDiff, add_right_comm b x c, hA x hx b, hA x hx (b + c)]
    have h2 : Continuous (fwdDiff c A) := by unfold fwdDiff; fun_prop
    rw [Function.iterate_succ_apply, ih h1 h2, pow_succ, mul_smul]
    congr 1
    unfold fwdDiff
    rw [latticeFourierCoeff_sub (by fun_prop) hc, latticeFourierCoeff_comp_add hA hν, sub_smul,
      one_smul]
end GlobalTheory
