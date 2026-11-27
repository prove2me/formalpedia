-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.norm_coeff_add_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:48:35.157838+00:00
-- url     : https://prove2.me/submissions/c825bb86-afd8-41be-9007-d9f93a6410d8

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_eq_teich_add___mul_tail_16271f5c650a
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_tail_eq
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_succ
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_ofCoeff
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_succ_f7b410ef729e
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_zero_c24e500c7aa0
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_zero_elem
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_prefixLe_add
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_prefixLe_neg
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_le_rpow_mix
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_rpow_mix_le
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_inv_pow_pos_le_one
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_prefixLe_teich_add_sub_of_le
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeffHolderExp_pos_le_one
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeffHolderExp_succ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.TeichLift.coeff_ofCoeff
attribute [local simp] GroundTheory.PAdicHodge.TeichLift.coeff_π_mul_zero
attribute [local simp] GroundTheory.PAdicHodge.TeichLift.coeff_zero_elem

set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open GroundTheory GroundTheory.PAdicHodge
open Ideal
open GroundTheory.PAdicHodge.TeichLift
variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CharP L p]
  [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)
namespace GroundTheory.PAdicHodge.TeichLift
theorem _root_.solution (n : ℕ) : ∀ {x y : Γ} {B δ : ℝ}, 0 ≤ δ → δ ≤ B →
    T.PrefixLe x n B → T.PrefixLe y n δ → ∀ m ≤ n,
      ‖T.coeff (x + y) m - T.coeff x m‖ ≤ B ^ (1 - coeffHolderExp p n) * δ ^ coeffHolderExp p n := by
  induction n with
  | zero =>
    intro x y B δ hδ hδB hx hy m hm
    obtain rfl : m = 0 := by omega
    rw [coeff_zero, coeff_zero, map_add, add_sub_cancel_left]
    exact (hy 0 le_rfl).trans (le_rpow_mix hδ hδB (coeffHolderExp_pos_le_one 0).2)
  | succ n ih =>
    intro x y B δ hδ hδB hx hy m hm
    rcases m with _ | m
    · rw [coeff_zero, coeff_zero, map_add, add_sub_cancel_left]
      exact (hy 0 (Nat.zero_le _)).trans (le_rpow_mix hδ hδB (coeffHolderExp_pos_le_one _).2)
    obtain ⟨hs0, hs1⟩ := inv_pow_pos_le_one (p := p) (n + 1)
    set s := ((p ^ (n + 1) : ℕ) : ℝ)⁻¹ with hsdef
    have hB0 : 0 ≤ B := hδ.trans hδB
    set H := T.teich (T.red x) + T.teich (T.red y) - T.teich (T.red x + T.red y) with hHdef
    have hH : T.red H = 0 := by rw [hHdef]; simp [red_teich]
    obtain ⟨h', hh'⟩ := T.red_eq_zero_iff.1 hH
    have htail : T.tail (x + y) = T.tail x + (T.tail y + h') := by
      refine T.tail_eq (a := T.red x + T.red y) ?_
      have ex := T.eq_teich_add_π_mul_tail x
      have ey := T.eq_teich_add_π_mul_tail y
      calc x + y = T.teich (T.red x) + T.π * T.tail x + (T.teich (T.red y) + T.π * T.tail y) := by
            rw [← ex, ← ey]
        _ = T.teich (T.red x + T.red y) + H + T.π * T.tail x + T.π * T.tail y := by
            rw [hHdef]; ring
        _ = _ := by rw [hh']; ring
    have hδ' : 0 ≤ B ^ (1 - s) * δ ^ s :=
      mul_nonneg (Real.rpow_nonneg hB0 _) (Real.rpow_nonneg hδ _)
    have hδδ' : δ ≤ B ^ (1 - s) * δ ^ s := le_rpow_mix hδ hδB hs1
    have hδ'B : B ^ (1 - s) * δ ^ s ≤ B := rpow_mix_le hδ hδB hs0.le hs1
    have hxt : T.PrefixLe (T.tail x) n B := fun i hi => by
      rw [← coeff_succ]; exact hx (i + 1) (by omega)
    have hyt : T.PrefixLe (T.tail y) n (B ^ (1 - s) * δ ^ s) := fun i hi => by
      rw [← coeff_succ]; exact (hy (i + 1) (by omega)).trans hδδ'
    have hHb : T.PrefixLe H (n + 1) (B ^ (1 - s) * δ ^ s) := by
      have := T.prefixLe_teich_add_sub_of_le (hx 0 (Nat.zero_le _)) (hy 0 (Nat.zero_le _)) hδ hδB
        (n + 1)
      have e : H = -(T.teich (T.red x + T.red y) - T.teich (T.red x) - T.teich (T.red y)) := by
        rw [hHdef]; ring
      rw [e]; exact T.prefixLe_neg this
    have hh'b : T.PrefixLe h' n (B ^ (1 - s) * δ ^ s) := fun i hi => by
      rw [← T.coeff_π_mul_succ, ← hh']; exact hHb (i + 1) (by omega)
    have := ih hδ' hδ'B hxt (T.prefixLe_add hyt hh'b) m (by omega)
    rw [coeff_succ, coeff_succ, htail]
    refine this.trans (le_of_eq ?_)
    obtain ⟨ht0, ht1⟩ := coeffHolderExp_pos_le_one (p := p) n
    have hne : 1 - coeffHolderExp p n + (1 - s) * coeffHolderExp p n ≠ 0 := by
      have : s * coeffHolderExp p n ≤ s := mul_le_of_le_one_right hs0.le ht1
      have hs2 : s < 1 := by
        rw [hsdef]
        have h2 : (1 : ℝ) < ((p ^ (n + 1) : ℕ) : ℝ) := by
          exact_mod_cast Nat.one_lt_pow (by omega) hp.out.one_lt
        exact inv_lt_one_of_one_lt₀ h2
      nlinarith
    rw [Real.mul_rpow (Real.rpow_nonneg hB0 _) (Real.rpow_nonneg hδ _), ← Real.rpow_mul hB0,
      ← Real.rpow_mul hδ, ← mul_assoc, ← Real.rpow_add' hB0 hne, coeffHolderExp_succ]
    congr 2 <;> ring
end GroundTheory.PAdicHodge.TeichLift
