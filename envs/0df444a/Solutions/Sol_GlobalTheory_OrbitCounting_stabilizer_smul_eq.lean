-- Prove2me | solution 1 for GlobalTheory.OrbitCounting.stabilizer_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:19:50.910928+00:00
-- url     : https://prove2.me/submissions/ed759835-ab3e-4e91-9149-d8865b19b677

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinsumOrbitsCountingPrincipleFiniteFibres

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.OrbitCounting
namespace GlobalTheory.OrbitCounting
theorem _root_.solution {G X : Type} [CommGroup G] [MulAction G X] (g : G) (x : X) :
    MulAction.stabilizer G (g • x) = MulAction.stabilizer G x := by
  ext h
  simp only [MulAction.mem_stabilizer_iff]
  rw [← mul_smul, mul_comm, mul_smul, smul_left_cancel_iff]
end GlobalTheory.OrbitCounting
