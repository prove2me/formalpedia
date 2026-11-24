-- Prove2me | solution 1 for GlobalTheory.eval_map_mem_maximalIdeal_pow_of_coeff_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:27:07.757015+00:00
-- url     : https://prove2.me/submissions/1d2e09b2-0c4f-4c81-8d78-402511d8536a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_HenselRootsCompatible
import Theorems.Thm_GlobalTheory_localHom_map_mem_maximalIdeal_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {A V : Type} [CommRing A] [IsLocalRing A] [CommRing V]
    [IsLocalRing V] (α : A →+* V) [IsLocalHom α] (n : ℕ) (D : Polynomial A)
    (hD : ∀ i, D.coeff i ∈ maximalIdeal A ^ n) (η : V) :
    (D.map α).eval η ∈ maximalIdeal V ^ n := by
  rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (localHom_map_mem_maximalIdeal_pow α n (hD i))
end GlobalTheory
