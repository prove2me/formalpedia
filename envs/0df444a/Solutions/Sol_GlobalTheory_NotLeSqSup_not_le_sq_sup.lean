-- Prove2me | solution 1 for GlobalTheory.NotLeSqSup.not_le_sq_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:16:15.294904+00:00
-- url     : https://prove2.me/submissions/86f8876e-ff5a-49e2-9c3b-1928412e2b34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NotLeSqSup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NotLeSqSup
namespace GlobalTheory.NotLeSqSup
theorem _root_.solution {A : Type} [CommRing A] {m I : Ideal A} {n : ℕ}
    (hn : m ^ (n + 1) = ⊥) (hI : ¬ m ≤ I) : ¬ m ≤ m ^ 2 ⊔ I := by
  intro h
  have key : ∀ j : ℕ, m ≤ m ^ (j + 1) ⊔ I := by
    intro j
    induction j with
    | zero => simpa using (le_sup_left : m ≤ m ⊔ I)
    | succ j ih =>
      calc m ≤ m ^ 2 ⊔ I := h
        _ ≤ m ^ (j + 1 + 1) ⊔ I := by
          refine sup_le ?_ le_sup_right
          calc m ^ 2 = m * m := pow_two m
            _ ≤ m * (m ^ (j + 1) ⊔ I) := Ideal.mul_mono_right ih
            _ = m * m ^ (j + 1) ⊔ m * I := Ideal.mul_sup _ _ _
            _ ≤ m ^ (j + 1 + 1) ⊔ I :=
              sup_le_sup (le_of_eq (pow_succ' m (j + 1)).symm)
                (Ideal.mul_le.mpr fun r _ s hs => I.mul_mem_left r hs)
  apply hI
  simpa [hn] using key n
end GlobalTheory.NotLeSqSup
