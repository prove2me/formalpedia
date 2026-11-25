-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.exists_one_add_teich_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:21:41.211849+00:00
-- url     : https://prove2.me/submissions/9d03e809-f527-44a2-acc6-e5a9c4709458

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_teich_pow
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_ofCoeff
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_zero_c24e500c7aa0
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_zero_elem
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_teich_mem_int
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_exists_natCast_p_eq
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
theorem _root_.solution {b : L} (hb : ‖b‖ ≤ 1) (k : ℕ) :
    ∃ U ∈ T.int, (1 + T.teich b) ^ p ^ k = 1 + T.teich (b ^ p ^ k) + T.π * T.teich b * U := by
  obtain ⟨wp, hwp, hpw⟩ := T.exists_natCast_p_eq
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨0, zero_mem _, by simp⟩
  obtain ⟨N, hN⟩ : ∃ N, p ^ k = N + 1 :=
    ⟨p ^ k - 1, by have := Nat.one_le_pow k p hp.out.pos; omega⟩
  have hlt : N + 1 ≠ 1 := by
    rw [← hN]; exact (Nat.one_lt_pow hk.ne' hp.out.one_lt).ne'
  have hdvd : ∀ m < N, p ∣ (N + 1).choose (m + 1) := fun m hm =>
    hN ▸ hp.out.dvd_choose_pow (by omega) (by omega)
  refine ⟨wp * ∑ m ∈ Finset.range N, T.teich b ^ m * (((N + 1).choose (m + 1) / p : ℕ) : Γ), ?_, ?_⟩
  · exact mul_mem hwp (Subring.sum_mem _ fun m _ =>
      mul_mem (pow_mem (T.teich_mem_int hb) _) (natCast_mem _ _))
  · have hsum : ∑ m ∈ Finset.range N, T.teich b ^ (m + 1) * 1 ^ (N + 1 - (m + 1)) *
        ((N + 1).choose (m + 1) : Γ) = T.π * T.teich b *
          (wp * ∑ m ∈ Finset.range N, T.teich b ^ m * (((N + 1).choose (m + 1) / p : ℕ) : Γ)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hc : ((N + 1).choose (m + 1) : Γ) = (p : Γ) * (((N + 1).choose (m + 1) / p : ℕ) : Γ) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' (hdvd m (Finset.mem_range.1 hm))]
      rw [hc, hpw, one_pow, mul_one, pow_succ]; ring
    rw [add_comm (1 : Γ), add_pow, T.teich_pow, hN, Finset.sum_range_succ, Finset.sum_range_succ',
      hsum]
    simp only [pow_zero, one_pow, mul_one, one_mul, Nat.choose_zero_right, Nat.choose_self,
      Nat.cast_one, Nat.sub_self, Nat.sub_zero]
    ring
end GroundTheory.PAdicHodge.TeichLift
