-- Prove2me | solution 1 for GlobalTheory.PeriodDvd.sum_vadd_modEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:22:55.779011+00:00
-- url     : https://prove2.me/submissions/59a9c917-3eba-4a16-9f8b-fb20f3ef00bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardDvdSumOfInvariantOfCardStabilizerDvd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DvdOfPeriodOfDvdSumPowersetCard
import Theorems.Thm_GlobalTheory_PeriodDvd_pow_mod_modEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Pointwise
open GlobalTheory
open GlobalTheory.PeriodDvd
namespace GlobalTheory.PeriodDvd
theorem _root_.solution {d : ℕ} [NeZero d] (q : ℕ) (hq : 1 ≤ q) (g : ZMod d) (I : Finset (ZMod d)) :
    (∑ x ∈ I, q ^ x.val) * q ^ g.val ≡ ∑ x ∈ g +ᵥ I, q ^ x.val [MOD q ^ d - 1] := by
  rw [Finset.vadd_finset_def, Finset.sum_image (fun x _ y _ hxy => by simpa using hxy),
    Finset.sum_mul]
  refine Nat.ModEq.sum fun x _ => ?_
  rw [vadd_eq_add, ZMod.val_add, ← pow_add, add_comm]
  exact (pow_mod_modEq q d _ hq).symm
end GlobalTheory.PeriodDvd
