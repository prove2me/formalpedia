-- Prove2me | solution 1 for GlobalTheory.eq_zero_of_forall_pow_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:37:03.090281+00:00
-- url     : https://prove2.me/submissions/e7a4337e-18cd-45c2-9cbd-f2cce7a3709d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TendstoTsumZeroOfEventuallyNotMemRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X : Type} [AddCommGroup X] [Module.Free ℤ X] {n : ℕ}
    (hn : 2 ≤ n) {x : X} (hx : ∀ j : ℕ, ∃ μ : X, x = n ^ j • μ) : x = 0 := by
  let b := Module.Free.chooseBasis ℤ X
  apply b.repr.injective
  ext i
  rw [map_zero, Finsupp.zero_apply]
  obtain ⟨μ, hμ⟩ := hx (b.repr x i).natAbs
  have hd : ((n : ℤ) ^ (b.repr x i).natAbs) ∣ b.repr x i := by
    refine ⟨b.repr μ i, ?_⟩
    conv_lhs => rw [hμ]
    simp [map_nsmul]
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd
  rw [Int.natAbs_pow, Int.natAbs_natCast]
  exact Nat.lt_pow_self (by omega)
end GlobalTheory
