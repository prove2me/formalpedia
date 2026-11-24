-- Prove2me | solution 1 for GlobalTheory.clm_eq_of_cexp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:29:12.597678+00:00
-- url     : https://prove2.me/submissions/2c17c9a5-6abc-4925-bbf6-9d946c6b2f27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AutomorphyFactorExpLinearOfCube

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (B C : V →L[ℂ] ℂ) (h : ∀ z, cexp (B z) = cexp (C z)) : B = C := by
  have h1 : HasFDerivAt (fun u => cexp (B u)) (cexp (B 0) • B) 0 := B.hasFDerivAt.cexp
  have h2 : HasFDerivAt (fun u => cexp (C u)) (cexp (C 0) • C) 0 := C.hasFDerivAt.cexp
  have e : (fun u => cexp (B u)) = fun u => cexp (C u) := funext h
  rw [e] at h1
  simpa using h1.unique h2
end GlobalTheory
