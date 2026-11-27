-- Prove2me | solution 1 for GlobalTheory.latticeFourier_of_contDiff_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:39:08.142106+00:00
-- url     : https://prove2.me/submissions/ec3b2572-d24c-4c34-b429-5bb0f7aa3f13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LatticeFourierOfContDiffFiniteDimensional
import Theorems.Thm_GlobalTheory_latticeFourier_of_contDiff

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
theorem _root_.solution [FiniteDimensional ℂ V] {A : E → V}
    (hsm : ContDiff ℝ ∞ A) (hA : ∀ x ∈ L, Function.Periodic A x) :
    (BddAbove (range fun b ↦ ‖A b‖) ∧ ∀ ν : L*, ‖latticeFourierCoeff L A ν‖ ≤ ⨆ b, ‖A b‖) ∧
    (Summable fun ν : L* ↦ ‖latticeFourierCoeff L A ν‖) ∧
    (∀ b, HasSum (fun ν : L* ↦ e[⟪(ν : E), b⟫] • latticeFourierCoeff L A ν) (A b)) ∧
    ∀ (c : E) (ν : L*), latticeFourierCoeff L (fun b ↦ A (b + c)) ν =
      e[⟪(ν : E), c⟫] • latticeFourierCoeff L A ν :=
  have : CompleteSpace V := FiniteDimensional.complete ℂ V
  latticeFourier_of_contDiff hsm hA
end GlobalTheory
