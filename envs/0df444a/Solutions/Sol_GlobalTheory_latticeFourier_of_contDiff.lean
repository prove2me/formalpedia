-- Prove2me | solution 1 for GlobalTheory.latticeFourier_of_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:50:50.824348+00:00
-- url     : https://prove2.me/submissions/956a5d31-8e8c-42f8-a94b-e5cb09867850

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LatticeFourierOfContDiffFiniteDimensional
import Theorems.Thm_GlobalTheory_norm_latticeFourierCoeff_le
import Theorems.Thm_GlobalTheory_latticeFourierCoeff_comp_add
import Theorems.Thm_GlobalTheory_exists_bound_of_lattice_periodic
import Theorems.Thm_GlobalTheory_summable_norm_latticeFourierCoeff
import Theorems.Thm_GlobalTheory_hasSum_latticeFourier_of_summable_norm

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
theorem _root_.solution [CompleteSpace V] {A : E → V} (hsm : ContDiff ℝ ∞ A)
    (hA : ∀ x ∈ L, Function.Periodic A x) :
    (BddAbove (range fun b ↦ ‖A b‖) ∧ ∀ ν : L*, ‖latticeFourierCoeff L A ν‖ ≤ ⨆ b, ‖A b‖) ∧
    (Summable fun ν : L* ↦ ‖latticeFourierCoeff L A ν‖) ∧
    (∀ b, HasSum (fun ν : L* ↦ e[⟪(ν : E), b⟫] • latticeFourierCoeff L A ν) (A b)) ∧
    ∀ (c : E) (ν : L*), latticeFourierCoeff L (fun b ↦ A (b + c)) ν =
      e[⟪(ν : E), c⟫] • latticeFourierCoeff L A ν := by
  have hs := summable_norm_latticeFourierCoeff hA (Nat.lt_succ_self _)
    (hsm.of_le (by exact_mod_cast le_top))
  obtain ⟨M, hM⟩ := exists_bound_of_lattice_periodic hA hsm.continuous
  have hb : BddAbove (range fun b ↦ ‖A b‖) := ⟨M, by rintro _ ⟨b, rfl⟩; exact hM b⟩
  exact ⟨⟨hb, fun ν ↦ norm_latticeFourierCoeff_le (le_ciSup hb) ν⟩, hs,
    hasSum_latticeFourier_of_summable_norm hA hsm.continuous hs,
    fun c ν ↦ latticeFourierCoeff_comp_add hA ν.2 c⟩
end GlobalTheory
