-- Prove2me | solution 1 for GlobalTheory.ExistsPrimeMem.exists_prime_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:41:32.259864+00:00
-- url     : https://prove2.me/submissions/4d317293-522d-4d05-b742-18d8cbd9a8c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ExistsPrimeMem
namespace GlobalTheory.ExistsPrimeMem
theorem _root_.solution {A : Type} [inst : CommRing A] (P : Ideal A) (hP : Ideal.IsPrime P) :
    ∀ (n : ℕ), n ≠ (0 : ℕ) → (↑n : A) ∈ P → ∃ (ℓ : ℕ), Nat.Prime ℓ ∧ (↑ℓ : A) ∈ P := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hnP
    by_cases h1 : n = 1
    · subst h1
      exact absurd ((Ideal.eq_top_iff_one P).2 (by simpa using hnP)) hP.ne_top
    · have hp := Nat.minFac_prime h1
      have hpos : 0 < n := Nat.pos_of_ne_zero hn
      have hsplit : ((n : ℕ) : A) = (n.minFac : A) * ((n / n.minFac : ℕ) : A) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' (Nat.minFac_dvd n)]
      rw [hsplit] at hnP
      rcases hP.mem_or_mem hnP with h | h
      · exact ⟨n.minFac, hp, h⟩
      · exact ih (n / n.minFac) (Nat.div_lt_self hpos hp.one_lt)
          (Nat.div_pos (Nat.minFac_le hpos) (Nat.minFac_pos n)).ne' h
end GlobalTheory.ExistsPrimeMem
