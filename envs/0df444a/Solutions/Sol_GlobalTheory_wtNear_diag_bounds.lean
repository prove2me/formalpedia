-- Prove2me | solution 1 for GlobalTheory.wtNear_diag_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:20:16.375598+00:00
-- url     : https://prove2.me/submissions/93a1aae3-a795-4cdc-b558-9c5cc6eab2f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_WtNearOrthDecompStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_WeightNearDiagonalOperatorsBounds
import Theorems.Thm_GlobalTheory_wtdiag_pyth
import Theorems.Thm_GlobalTheory_T_exists_orthogonal_weight_decomp_of_mem_wtNear


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (Λ : Fin n → ℝ) (t : ℝ) (w : M), IsUnitary ε E → w ∈ WtNear E Λ t → (∀ m : ℝ, (∀ ω : Fin n → ℝ, ∑ a, |ω a - Λ a| ≤ t → m ≤ ∑ a, ω a ^ 2) → m * ‖w‖ ^ 2 ≤ ∑ a, ‖E a a w‖ ^ 2) ∧ (∀ (a : Fin n) (ζ : ℂ) (d : ℝ), 0 ≤ d → (∀ ω : Fin n → ℝ, ∑ a, |ω a - Λ a| ≤ t → d ≤ ‖ζ + (ω a : ℂ)‖) → d ^ 2 * ‖w‖ ^ 2 ≤ ‖ζ • w + E a a w‖ ^ 2) ∧ ∀ (a : Fin n) (D : ℝ), (∀ ω : Fin n → ℝ, ∑ a, |ω a - Λ a| ≤ t → |ω a| ≤ D) → ‖E a a w‖ ^ 2 ≤ D ^ 2 * ‖w‖ ^ 2 := by
  intro M _ _ n ε E Λ t w hU hw
  obtain ⟨T, x, hx, hsum, horth⟩ := GlobalTheory.T.exists_orthogonal_weight_decomp_of_mem_wtNear M n ε E Λ t w hU hw
  have P := wtdiag_pyth T x horth
  have hw2 : ‖w‖ ^ 2 = ∑ ω ∈ T, ‖x ω‖ ^ 2 := by
    have := P (fun _ => 1)
    simpa [← hsum] using this
  have hE : ∀ a, E a a w = ∑ ω ∈ T, (ω a : ℂ) • x ω := by
    intro a
    rw [hsum, map_sum]
    exact Finset.sum_congr rfl fun ω hω => (hx ω hω).2 a
  have hE2 : ∀ a, ‖E a a w‖ ^ 2 = ∑ ω ∈ T, ω a ^ 2 * ‖x ω‖ ^ 2 := by
    intro a
    rw [hE a, P]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  refine ⟨?_, ?_, ?_⟩
  · intro m hm
    simp_rw [hE2]
    rw [Finset.sum_comm, hw2, Finset.mul_sum]
    refine Finset.sum_le_sum fun ω hω => ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hm ω (hx ω hω).1) (sq_nonneg _)
  · intro a ζ d hd h
    have e : ζ • w + E a a w = ∑ ω ∈ T, (ζ + (ω a : ℂ)) • x ω := by
      rw [hE a]
      conv_lhs => rw [hsum, Finset.smul_sum]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun ω _ => (add_smul _ _ _).symm
    rw [e, P, hw2, Finset.mul_sum]
    refine Finset.sum_le_sum fun ω hω => ?_
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hd (h ω (hx ω hω).1) 2) (sq_nonneg _)
  · intro a D h
    rw [hE2, hw2, Finset.mul_sum]
    refine Finset.sum_le_sum fun ω hω => ?_
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (h ω (hx ω hω).1) 2
end GlobalTheory
