-- Prove2me | solution 1 for GlobalTheory.cexp_two_pi_I_intCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:26:10.388136+00:00
-- url     : https://prove2.me/submissions/39856c8d-6183-4600-9a6f-fcb1c5555cab

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
namespace GlobalTheory
theorem _root_.solution (n : ℤ) : e[(n : ℝ)] = 1 := by
  rw [← Complex.exp_int_mul_two_pi_mul_I n]
  congr 1; push_cast; ring
end GlobalTheory
