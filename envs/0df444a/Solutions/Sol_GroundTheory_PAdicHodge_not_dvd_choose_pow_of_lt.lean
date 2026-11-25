-- Prove2me | solution 1 for GroundTheory.PAdicHodge.not_dvd_choose_pow_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:19:06.609645+00:00
-- url     : https://prove2.me/submissions/5c5f4aeb-901a-4286-9140-af8ff1df07ff

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
theorem _root_.solution {p : ℕ} [hp : Fact p.Prime] {d k : ℕ} (h1 : p ^ k ≤ d)
    (h2 : d < p ^ (k + 1)) : ¬ p ∣ Nat.choose d (p ^ k) := by
  have hlog : Nat.log p d = k := Nat.log_eq_of_pow_le_of_lt_pow h1 h2
  have hv : padicValNat p (Nat.choose d (p ^ k)) = 0 := by
    rw [padicValNat_choose h1 (b := k + 1) (by omega), Finset.card_eq_zero,
      Finset.filter_eq_empty_iff]
    intro i hi
    rw [Finset.mem_Ico] at hi
    have hdvd : p ^ i ∣ p ^ k := pow_dvd_pow p (by omega)
    rw [Nat.mod_eq_zero_of_dvd hdvd, zero_add, not_le]
    exact Nat.mod_lt _ (pow_pos hp.out.pos i)
  have hne : Nat.choose d (p ^ k) ≠ 0 := (Nat.choose_pos h1).ne'
  rcases (padicValNat.eq_zero_iff.1 hv) with h | h | h
  · exact absurd h hp.out.one_lt.ne'
  · exact absurd h hne
  · exact h
end GroundTheory.PAdicHodge
