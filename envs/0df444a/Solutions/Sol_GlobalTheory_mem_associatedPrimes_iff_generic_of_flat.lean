-- Prove2me | solution 1 for GlobalTheory.mem_associatedPrimes_iff_generic_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:09:50.287858+00:00
-- url     : https://prove2.me/submissions/64b48818-383b-4eb9-b5d9-32726758be90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasicOpenEqZeroOfMemIInfPowSmul
import Theorems.Thm_GlobalTheory_ker_includeRight_fiber
import Theorems.Thm_GlobalTheory_mem_associatedPrimes_iff_eq_map_of_flat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {M : Type*} [AddCommGroup M] [Module A M]
variable [Module B M] [IsScalarTower A B M] [Module.Flat A M]
variable [Module.Flat A B]
namespace GlobalTheory
theorem _root_.solution [IsNoetherianRing A] (q : Ideal B)
    [hq : q.IsPrime] [NoZeroDivisors ((q.under A).Fiber B)] :
    q ∈ associatedPrimes B B ↔ q.under A ∈ associatedPrimes A A ∧
      ∀ q' : Ideal B, q'.IsPrime → q'.under A = q.under A → q ≤ q' := by
  rw [mem_associatedPrimes_iff_eq_map_of_flat (A := A), and_congr_right_iff]
  intro _
  constructor
  · intro h q' _ h'
    rw [h, Ideal.map_le_iff_le_comap, ← h']
  · intro h
    have hle : (q.under A).map (algebraMap A B) ≤ q := Ideal.map_comap_le
    have : Nontrivial ((q.under A).Fiber B) := by
      refine ⟨1, 0, fun h1 ↦ hq.ne_top ?_⟩
      rw [Ideal.eq_top_iff_one]
      refine hle ?_
      rw [← ker_includeRight_fiber, RingHom.mem_ker, map_one, h1]
    have := NoZeroDivisors.to_isDomain ((q.under A).Fiber B)
    refine le_antisymm (h _ ?_ ?_) hle
    · rw [← ker_includeRight_fiber]
      exact RingHom.ker_isPrime _
    · exact le_antisymm (Ideal.comap_mono hle) Ideal.le_comap_map
end GlobalTheory
