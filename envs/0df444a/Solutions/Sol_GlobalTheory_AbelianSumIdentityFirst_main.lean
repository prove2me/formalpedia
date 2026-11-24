-- Prove2me | solution 1 for GlobalTheory.AbelianSumIdentityFirst.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:52:59.851801+00:00
-- url     : https://prove2.me/submissions/773efcc8-67ab-4040-8311-069cec3c27bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsTerTail

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AbelianSumIdentityFirst
namespace GlobalTheory.AbelianSumIdentityFirst
theorem _root_.solution : ∀ {ι : Type} {z : ℂ}, z ≠ (0 : ℂ) → ∀ (s : Finset ι) (a : ι → ℤ),
    z ^ ∑ i ∈ s, a i = ∏ i ∈ s, z ^ a i := by
  intro ι z hz s a
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj, zpow_add₀ hz, ih]
end GlobalTheory.AbelianSumIdentityFirst
