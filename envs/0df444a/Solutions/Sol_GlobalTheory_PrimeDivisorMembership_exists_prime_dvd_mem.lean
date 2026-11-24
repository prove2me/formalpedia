-- Prove2me | solution 1 for GlobalTheory.PrimeDivisorMembership.exists_prime_dvd_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:29:30.337806+00:00
-- url     : https://prove2.me/submissions/bfae41bc-87df-4c6a-a292-c78dce50b697

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsPrimeDvdMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open GlobalTheory GlobalTheory.PrimeDivisorMembership
namespace GlobalTheory.PrimeDivisorMembership
theorem _root_.solution : ∀ {R : Type u_1} [inst : CommRing R] (P : Ideal R), Ideal.IsPrime P → ∀ (n : ℕ), n ≠ (0 : ℕ) → (↑n : R) ∈ P → ∃ (q : ℕ), Nat.Prime q ∧ q ∣ n ∧ (↑q : R) ∈ P := by
  intro R _ P hP n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hmem
    by_cases h1 : n = 1
    · subst h1
      rw [Nat.cast_one] at hmem
      exact absurd ((Ideal.eq_top_iff_one P).2 hmem) hP.ne_top
    · have hmin := Nat.minFac_prime h1
      obtain ⟨m, hm⟩ := Nat.minFac_dvd n
      have hmem' : (n.minFac : R) * (m : R) ∈ P := by
        rw [← Nat.cast_mul, ← hm]
        exact hmem
      rcases hP.mem_or_mem hmem' with hq | hq
      · exact ⟨n.minFac, hmin, Nat.minFac_dvd n, hq⟩
      · have hm0 : m ≠ 0 := by
          rintro rfl
          rw [mul_zero] at hm
          exact hn hm
        have hlt : m < n := by
          calc m < 2 * m := by omega
            _ ≤ n.minFac * m := Nat.mul_le_mul_right _ hmin.two_le
            _ = n := hm.symm
        obtain ⟨q, hq1, hq2, hq3⟩ := ih m hlt hm0 hq
        exact ⟨q, hq1, hq2.trans (Dvd.intro_left _ hm.symm), hq3⟩
end GlobalTheory.PrimeDivisorMembership
