-- Prove2me | solution 1 for GlobalTheory.summable_norm_latticeFourierCoeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:44:31.188857+00:00
-- url     : https://prove2.me/submissions/59b96ebd-f6ce-4e79-a9ca-5470f427261c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LatticeFourierOfContDiffFiniteDimensional
import Theorems.Thm_GlobalTheory_exists_bound_of_lattice_periodic
import Theorems.Thm_GlobalTheory_pow_mul_norm_latticeFourierCoeff_le
import Theorems.Thm_GlobalTheory_summable_norm_inv_pow_innerDual

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
    {k : ℕ} (hk : finrank ℝ E < k) (hAk : ContDiff ℝ k A) :
    Summable fun ν : L* ↦ ‖latticeFourierCoeff L A ν‖ := by
  obtain ⟨M, hM⟩ := exists_bound_of_lattice_periodic (L := L) (f := iteratedFDeriv ℝ k A)
    (fun x hx b ↦ by
      rw [← iteratedFDeriv_comp_add_right, show (fun z ↦ A (z + x)) = A from funext (hA x hx)])
    (hAk.continuous_iteratedFDeriv le_rfl)
  refine .of_norm_bounded_eventually
    ((summable_norm_inv_pow_innerDual (L := L) hk).mul_left ((4 ^ k)⁻¹ * M)) ?_
  filter_upwards [Filter.eventually_cofinite_ne 0] with ν h0
  have hn : 0 < ‖(ν : E)‖ := norm_pos_iff.2 (by simpa using h0)
  have := pow_mul_norm_latticeFourierCoeff_le hA hAk hM ν.2
  rw [← le_inv_mul_iff₀ (by positivity), mul_pow, mul_inv] at this
  rw [norm_norm, inv_pow, mul_right_comm]
  exact this
end GlobalTheory
