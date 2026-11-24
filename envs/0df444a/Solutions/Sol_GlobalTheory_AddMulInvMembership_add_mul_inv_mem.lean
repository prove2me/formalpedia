-- Prove2me | solution 1 for GlobalTheory.AddMulInvMembership.add_mul_inv_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:55:20.125932+00:00
-- url     : https://prove2.me/submissions/73f12403-9ead-4b8e-a748-4e811305c314

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AddMulInvMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open GlobalTheory GlobalTheory.AddMulInvMembership
namespace GlobalTheory.AddMulInvMembership
theorem _root_.solution :
    (let d1 : {K : Type u_1} → [inst : Field K] → Subring K → K → K → Prop :=
      @(fun {K : Type u_1} [Field K] (S : Subring K) (π a : K) ↦ a * π⁻¹ ∈ S);
    ∀ {K : Type u_1} [inst : Field K] [StarRing K] {S : Subring K} {π a b : K},
      d1 S π a → d1 S π b → d1 S π (a + b)) := by
  intro d1 K _ _ S π a b ha hb
  show (a + b) * π⁻¹ ∈ S
  rw [add_mul]
  exact S.add_mem ha hb
end GlobalTheory.AddMulInvMembership
