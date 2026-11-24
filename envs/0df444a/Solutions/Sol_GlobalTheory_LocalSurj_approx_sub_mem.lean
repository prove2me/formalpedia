-- Prove2me | solution 1 for GlobalTheory.LocalSurj.approx_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:08:30.559931+00:00
-- url     : https://prove2.me/submissions/1da799a1-f5eb-4387-b606-a24ffbc51817

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SurjectiveOfResidueOfCotangent
import Theorems.Thm_GlobalTheory_LocalSurj_approx_succ_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Matrix TensorProduct
open GlobalTheory GlobalTheory.LocalSurj
namespace GlobalTheory.LocalSurj
theorem _root_.solution {R A : Type} [CommRing R] [CommRing A] (f : R →+* A)
    (m : Ideal R) (hm : ∀ z : A, ∃ r, z - f r ∈ m.map f) (a : A) {k n : ℕ} (h : k ≤ n) :
    (approx f m hm a n).1 - (approx f m hm a k).1 ∈ m ^ k := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n hkn ih =>
    have e : (approx f m hm a (n + 1)).1 - (approx f m hm a k).1 =
        ((approx f m hm a (n + 1)).1 - (approx f m hm a n).1) +
        ((approx f m hm a n).1 - (approx f m hm a k).1) := by ring
    rw [e]
    exact add_mem (Ideal.pow_le_pow_right hkn (approx_succ_sub f m hm a n)) ih
end GlobalTheory.LocalSurj
