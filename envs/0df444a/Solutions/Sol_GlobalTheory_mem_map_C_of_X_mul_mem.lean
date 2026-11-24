-- Prove2me | solution 1 for GlobalTheory.mem_map_C_of_X_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:21:23.82421+00:00
-- url     : https://prove2.me/submissions/df4cbe18-0f0b-49b6-b802-6211f3dd6970

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial RingTheory.Sequence
noncomputable section
open GlobalTheory
variable {R : Type*} [CommRing R] {σ : Type*}
namespace GlobalTheory
theorem _root_.solution (x : σ) (I : Ideal R) {p : MvPolynomial σ R}
    (hp : X x * p ∈ I.map (C : R →+* MvPolynomial σ R)) :
    p ∈ I.map (C : R →+* MvPolynomial σ R) := by
  rw [MvPolynomial.mem_map_C_iff] at hp ⊢
  intro m
  have := hp (Finsupp.single x 1 + m)
  rwa [coeff_X_mul] at this
end GlobalTheory
