-- Prove2me | solution 1 for GroundTheory.PAdicHodge.not_sq_dvd_choose_pow_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:19:07.879418+00:00
-- url     : https://prove2.me/submissions/937c524f-9a85-47b2-b1d5-55ef4e4c1963

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial
noncomputable section
namespace GroundTheory.PAdicHodge
theorem _root_.solution {p : ℕ} [hp : Fact p.Prime] {k : ℕ} (hk : 1 ≤ k) :
    ¬ p ^ 2 ∣ Nat.choose (p ^ k) (p ^ (k - 1)) := by
  have hp1 := hp.out.one_lt
  have hle : p ^ (k - 1) ≤ p ^ k := Nat.pow_le_pow_right hp.out.pos (by omega)
  have hlog : Nat.log p (p ^ k) = k := Nat.log_pow hp1 k
  have hsub : p ^ k - p ^ (k - 1) = p ^ (k - 1) * (p - 1) := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ, Nat.mul_sub, mul_one]
  have hv : padicValNat p (Nat.choose (p ^ k) (p ^ (k - 1))) ≤ 1 := by
    rw [padicValNat_choose hle (b := k + 1) (by omega)]
    calc _ ≤ ({k} : Finset ℕ).card := by
          refine Finset.card_le_card fun i hi => ?_
          rw [Finset.mem_filter, Finset.mem_Ico] at hi
          rw [Finset.mem_singleton]
          by_contra hik
          obtain ⟨⟨hi1, hi2⟩, hi3⟩ := hi
          have hik' : i ≤ k - 1 := by omega
          have h1 : p ^ (k - 1) % p ^ i = 0 := Nat.mod_eq_zero_of_dvd (pow_dvd_pow p hik')
          have h2 : (p ^ k - p ^ (k - 1)) % p ^ i = 0 := by
            rw [hsub]; exact Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_right (pow_dvd_pow p hik') _)
          rw [h1, h2] at hi3
          have : 0 < p ^ i := pow_pos hp.out.pos i
          omega
      _ = 1 := Finset.card_singleton k
  intro hdvd
  have hne : Nat.choose (p ^ k) (p ^ (k - 1)) ≠ 0 := (Nat.choose_pos hle).ne'
  have := (padicValNat_dvd_iff_le hne).1 hdvd
  omega
end GroundTheory.PAdicHodge
