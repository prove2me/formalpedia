-- Prove2me | solution 1 for GlobalTheory.map_maximalIdeal_le_jacobson_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:39:47.230143+00:00
-- url     : https://prove2.me/submissions/33ad2571-b094-48f6-90f3-47b82e1d483c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Theorems.Thm_GlobalTheory_comap_eq_maximalIdeal_of_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open IsLocalRing Polynomial TensorProduct
namespace GlobalTheory
theorem _root_.solution (R S : Type*) [CommRing R] [IsLocalRing R]
    [CommRing S] [Algebra R S] [Module.Finite R S] :
    (maximalIdeal R).map (algebraMap R S) ≤ (⊥ : Ideal S).jacobson := by
  rw [Ideal.jacobson, le_sInf_iff]
  rintro n ⟨-, hn⟩
  rw [Ideal.map_le_iff_le_comap, comap_eq_maximalIdeal_of_finite]
end GlobalTheory
