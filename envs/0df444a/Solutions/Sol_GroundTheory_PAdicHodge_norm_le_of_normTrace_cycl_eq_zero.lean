-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_le_of_normTrace_cycl_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:49:37.00227+00:00
-- url     : https://prove2.me/submissions/92df98ed-ceee-419a-8793-dc13a4094df3

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Theorems.Thm_GroundTheory_PAdicHodge_norm_normTrace_cycl_le
import Theorems.Thm_GroundTheory_PAdicHodge_norm_pow_apply_sub_le
import Theorems.Thm_GroundTheory_PAdicHodge_norm_le_of_normTrace_cycl_succ_eq_zero
import Theorems.Thm_GroundTheory_PAdicHodge_pow_prime_pow_fix_and_move
import Theorems.Thm_GroundTheory_PAdicHodge_cycl_map
import Theorems.Thm_GroundTheory_PAdicHodge_cycl_mono
import Theorems.Thm_GroundTheory_PAdicHodge_exists_isPrimitiveRoot
import Theorems.Thm_GroundTheory_PAdicHodge_map_mem_cycl
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_map_of_map_eq
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_mem
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_normTrace_of_le
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_of_mem
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_sub
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_zero
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.normTrace_zero
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial Module
noncomputable section
variable {p : ℕ} [Fact p.Prime]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {n m : ℕ} (hn : 2 ≤ n)
    (γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (hγn : ∀ x ∈ cycl p n, γ x = x)
    {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ (p ^ (n + 1))) (hγζ : γ ζ ≠ ζ)
    {x : PadicAlgCl p} (hx : x ∈ cycl p m) (h0 : normTrace (cycl p n) x = 0) :
    ‖x‖ ≤ (p : ℝ) ^ 3 * ‖γ x - x‖ := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rcases le_or_gt m n with hmn | hnm
  · rw [normTrace_of_mem _ (cycl_mono hmn hx)] at h0
    rw [h0, norm_zero]; positivity
  set w := γ x - x with hw
  have hwm : w ∈ cycl p m := sub_mem (map_mem_cycl γ hx) hx
  have hcomm : ∀ j y, γ (normTrace (cycl p j) y) = normTrace (cycl p j) (γ y) := fun j y =>
    (normTrace_map_of_map_eq (cycl p j) γ (cycl_map γ j) y).symm

  set f : ℕ → PadicAlgCl p := fun k => normTrace (cycl p k) x with hf
  have hlayer : ∀ k ∈ Finset.Ico n m, ‖f (k + 1) - f k‖ ≤ (p : ℝ) ^ 3 * ‖w‖ := by
    intro k hk
    obtain ⟨hnk, hkm⟩ := Finset.mem_Ico.1 hk
    have hk1 : 1 ≤ k := by omega
    set y := f (k + 1) - f k
    have hy : y ∈ cycl p (k + 1) :=
      sub_mem (normTrace_mem _ _) (cycl_mono (Nat.le_succ k) (normTrace_mem _ _))
    have hy0 : normTrace (cycl p k) y = 0 := by
      simp only [y, hf]
      rw [normTrace_sub, normTrace_normTrace_of_le (cycl_mono (p := p) (Nat.le_succ k)),
        normTrace_of_mem _ (normTrace_mem _ _), sub_self]
    have hγy : γ y - y = normTrace (cycl p (k + 1)) w - normTrace (cycl p k) w := by
      simp only [y, hf, hw, map_sub, hcomm, normTrace_sub]; ring
    have hγy' : ‖γ y - y‖ ≤ p * ‖w‖ := by
      rw [hγy, sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · exact norm_normTrace_cycl_le (by omega) hkm hwm
      · rw [norm_neg]; exact norm_normTrace_cycl_le hk1 hkm.le hwm
    obtain ⟨hfix, hmove⟩ := pow_prime_pow_fix_and_move hn γ hγn hζ hγζ (k - n)
    rw [Nat.add_sub_cancel' hnk] at hfix hmove
    obtain ⟨η, hη⟩ := exists_isPrimitiveRoot (p := p) (k + 1)
    have h1 := norm_le_of_normTrace_cycl_succ_eq_zero hk1 _ hfix hη (hmove η hη) hy hy0
    have h2 := norm_pow_apply_sub_le γ y (p ^ (k - n))
    calc ‖y‖ ≤ (p : ℝ) ^ 2 * ‖(γ ^ (p ^ (k - n))) y - y‖ := h1
      _ ≤ (p : ℝ) ^ 2 * (p * ‖w‖) :=
          mul_le_mul_of_nonneg_left (h2.trans hγy') (by positivity)
      _ = _ := by ring
  have htel : ∀ m' : ℕ, n ≤ m' → ∑ k ∈ Finset.Ico n m', (f (k + 1) - f k) = f m' - f n := by
    intro m' hm'
    induction m', hm' using Nat.le_induction with
    | base => simp
    | succ m' hm' ih => rw [Finset.sum_Ico_succ_top hm', ih]; ring
  have hxsum : x = ∑ k ∈ Finset.Ico n m, (f (k + 1) - f k) := by
    rw [htel m hnm.le]
    simp only [hf]
    rw [h0, sub_zero, normTrace_of_mem _ hx]
  rw [hxsum]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) hlayer
end GroundTheory.PAdicHodge
