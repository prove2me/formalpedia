-- Prove2me | solution 1 for GlobalTheory.exists_isDiscreteValuationRing_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:51:27.305607+00:00
-- url     : https://prove2.me/submissions/c334dd10-c332-4e45-af58-3eaaf7314dd3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Theorems.Thm_GlobalTheory_exists_isDiscreteValuationRing_of_maximalIdeal_eq_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial IsLocalRing
open scoped TensorProduct
variable (V : Type*) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
namespace GlobalTheory
theorem _root_.solution (B : Type*) [CommRing B] [IsLocalRing B]
    [Algebra V B] [Module.Flat V B]
    (hm : (maximalIdeal V).map (algebraMap V B) = maximalIdeal B)
    (hs : ⨅ n : ℕ, maximalIdeal B ^ n = ⊥) : ∃ _ : IsDomain B, IsDiscreteValuationRing B := by
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible V
  refine exists_isDiscreteValuationRing_of_maximalIdeal_eq_span (t := algebraMap V B t) ?_ ?_ hs
  · rw [mem_nonZeroDivisors_iff_left]
    intro x hx
    have := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B)
      (mem_nonZeroDivisors_of_ne_zero ht.ne_zero)
    exact this (show t • x = t • (0 : B) by rw [smul_zero, Algebra.smul_def, hx])
  · rw [← hm, ht.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
end GlobalTheory
