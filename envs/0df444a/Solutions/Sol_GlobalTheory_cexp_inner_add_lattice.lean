-- Prove2me | solution 1 for GlobalTheory.cexp_inner_add_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:36:07.500409+00:00
-- url     : https://prove2.me/submissions/a3992241-bad8-4687-8518-0a0536923d0a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LatticeFourierOfContDiffFiniteDimensional
import Theorems.Thm_GlobalTheory_mem_innerDual_iff
import Theorems.Thm_GlobalTheory_cexp_two_pi_I_add
import Theorems.Thm_GlobalTheory_cexp_two_pi_I_intCast

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
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [DiscreteTopology L]
  [IsZLattice ℝ L]
namespace GlobalTheory
theorem _root_.solution {ν : E} (hν : ν ∈ L*) {x : E} (hx : x ∈ L) (b : E) :
    e[⟪ν, b + x⟫] = e[⟪ν, b⟫] := by
  obtain ⟨n, hn⟩ := (mem_innerDual_iff L).1 hν x hx
  rw [inner_add_right, cexp_two_pi_I_add, ← hn, cexp_two_pi_I_intCast, mul_one]
end GlobalTheory
