-- Prove2me | solution 1 for GlobalTheory.NormIntegers.ringKrullDim_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:14:38.858979+00:00
-- url     : https://prove2.me/submissions/6feebe9e-8dd5-4a91-a25f-f40098162884

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowLeComapMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
universe u
open GlobalTheory.NormIntegers
namespace GlobalTheory.NormIntegers
theorem _root_.solution {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
    {O : Type*} [CommRing O] [Algebra O C] (hO : (NormedField.valuation (K := C)).Integers O) :
    ringKrullDim O = 1 := by
  haveI := isDomain hO
  haveI := isLocalRing hO
  rw [ringKrullDim_eq_one_iff_of_isLocalRing_isDomain]
  constructor
  · obtain ⟨x, hx0, hx1⟩ := NormedField.exists_norm_lt_one C
    obtain ⟨y, rfl⟩ := exists_of_norm_le_one hO hx1.le
    rw [IsLocalRing.isField_iff_maximalIdeal_eq]
    intro h
    have : y ∈ IsLocalRing.maximalIdeal O := (mem_maximalIdeal_iff hO).2 hx1
    rw [h, Ideal.mem_bot] at this
    exact (norm_pos_iff hO).1 hx0 this
  · intro x hx y hy
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one ((norm_pos_iff hO).2 hx)
      ((mem_maximalIdeal_iff hO).1 hy)
    refine ⟨n, ?_⟩
    rw [Ideal.mem_span_singleton, dvd_iff_norm_le hO, map_pow, norm_pow]
    exact hn.le
end GlobalTheory.NormIntegers
