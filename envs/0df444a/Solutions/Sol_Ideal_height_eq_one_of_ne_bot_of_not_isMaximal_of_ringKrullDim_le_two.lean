-- Prove2me | solution 1 for Ideal.height_eq_one_of_ne_bot_of_not_isMaximal_of_ringKrullDim_le_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/bb9c0bce-6963-53b2-821f-f7103b87747a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_height_eq_one_of_ne_bot_of_not_isMaximal_of_ringKrullDim_le_two

set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (hdim : ringKrullDim R ≤ 2) (P : Ideal R) [P.IsPrime] (hP0 : P ≠ ⊥) (hPm : ¬ P.IsMaximal) :
    P.height = 1 := by
  haveI := Ideal.finiteHeight_of_isNoetherianRing P
  have hPtop : P ≠ ⊤ := Ideal.IsPrime.ne_top ‹_›
  obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P hPtop
  have hPM' : P < M := lt_of_le_of_ne hPM (fun h => hPm (h ▸ hM))
  haveI := hM.isPrime
  have hM2 : M.height ≤ ((2 : ℕ) : ℕ∞) := by
    have h := Ideal.height_le_ringKrullDim_of_ne_top hM.ne_top
    have h2 : ((M.height : ℕ∞) : WithBot ℕ∞) ≤ (((2 : ℕ) : ℕ∞) : WithBot ℕ∞) := h.trans (by exact_mod_cast hdim)
    exact WithBot.coe_le_coe.mp h2
  have hlt : P.height < ((2 : ℕ) : ℕ∞) := (Ideal.height_le_iff.mp hM2) P inferInstance hPM'
  have hne0 : P.height ≠ 0 := by
    rw [Ne, Ideal.height_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff]
    exact hP0
  have hfin : P.height ≠ ⊤ := Ideal.height_ne_top hPtop
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hfin
  rw [← hk] at hlt hne0 ⊢
  norm_cast at hlt hne0 ⊢
  omega

end S_Ideal_height_eq_one_of_ne_bot_of_not_isMaximal_of_ringKrullDim_le_two
end P2MW
export P2MW.S_Ideal_height_eq_one_of_ne_bot_of_not_isMaximal_of_ringKrullDim_le_two (solution)
