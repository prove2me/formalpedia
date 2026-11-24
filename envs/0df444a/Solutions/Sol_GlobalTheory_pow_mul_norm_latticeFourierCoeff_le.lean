-- Prove2me | solution 1 for GlobalTheory.pow_mul_norm_latticeFourierCoeff_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:36:11.599821+00:00
-- url     : https://prove2.me/submissions/c9e92acc-ec9e-4f5f-8630-feb3f2b20905

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LatticeFourierOfContDiffFiniteDimensional
import Theorems.Thm_GlobalTheory_cexp_two_pi_I_half
import Theorems.Thm_GlobalTheory_norm_latticeFourierCoeff_le
import Theorems.Thm_GlobalTheory_latticeFourierCoeff_fwdDiff_iter
import Theorems.Thm_GlobalTheory_norm_fwdDiff_iter_le

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
    {k : ℕ} (hk : ContDiff ℝ k A) {M : ℝ} (hM : ∀ x, ‖iteratedFDeriv ℝ k A x‖ ≤ M)
    {ν : E} (hν : ν ∈ L*) :
    (4 * ‖ν‖) ^ k * ‖latticeFourierCoeff L A ν‖ ≤ M := by
  rcases eq_or_ne ν 0 with rfl | h0
  · rcases k with _ | k
    · simpa using norm_latticeFourierCoeff_le (fun b ↦ by simpa using hM b) 0
    · simpa using (norm_nonneg _).trans (hM 0)
  have hn : 0 < ‖ν‖ := norm_pos_iff.2 h0
  set c : E := (2 * ‖ν‖ ^ 2)⁻¹ • ν with hc
  have h1 : ⟪ν, c⟫ = 1 / 2 := by
    rw [hc, inner_smul_right, real_inner_self_eq_norm_sq]; field_simp
  have h2 : ‖c‖ = (2 * ‖ν‖)⁻¹ := by
    rw [hc, norm_smul, Real.norm_of_nonneg (by positivity)]; field_simp
  have h3 := norm_latticeFourierCoeff_le (L := L) (norm_fwdDiff_iter_le c k hk hM) ν
  rw [latticeFourierCoeff_fwdDiff_iter hA hk.continuous hν, h1, cexp_two_pi_I_half, norm_smul,
    norm_pow, h2, inv_pow, le_inv_mul_iff₀ (by positivity), ← mul_assoc, ← mul_pow] at h3
  have h4 : ‖(-1 - 1 : ℂ)‖ = 2 := by norm_num
  rwa [h4, show 2 * ‖ν‖ * 2 = 4 * ‖ν‖ by ring] at h3
end GlobalTheory
