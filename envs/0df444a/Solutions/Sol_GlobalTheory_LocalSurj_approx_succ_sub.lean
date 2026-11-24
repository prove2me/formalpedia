-- Prove2me | solution 1 for GlobalTheory.LocalSurj.approx_succ_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:49:00.558592+00:00
-- url     : https://prove2.me/submissions/bf599dd1-cb0b-4801-92db-698f2834deae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SurjectiveOfResidueOfCotangent

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
    (m : Ideal R) (hm : ∀ z : A, ∃ r, z - f r ∈ m.map f) (a : A) (n : ℕ) :
    (approx f m hm a (n + 1)).1 - (approx f m hm a n).1 ∈ m ^ n := by
  simp only [approx, add_sub_cancel_left]
  exact (exists_sub_mem_map_pow_succ f m hm n _ (approx f m hm a n).2).choose_spec.1
end GlobalTheory.LocalSurj
