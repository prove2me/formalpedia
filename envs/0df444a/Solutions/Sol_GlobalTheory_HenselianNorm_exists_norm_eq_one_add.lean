-- Prove2me | solution 1 for GlobalTheory.HenselianNorm.exists_norm_eq_one_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:45:40.543922+00:00
-- url     : https://prove2.me/submissions/c66dc2c4-e1be-4536-9a93-42ec43d100e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_FiniteInvolutionFixedUnitEqMulConjStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsNormEqFixedUnitHenselian
import Theorems.Thm_GlobalTheory_HenselianNorm_exists_mem_add_mul_sq_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.HenselianNorm
namespace GlobalTheory.HenselianNorm
theorem _root_.solution {R : Type*} [CommRing R] (I : Ideal R) [HenselianRing R I]
    (c : R →+* R) (hc : ∀ x, c (c x) = x) (hI : ∀ x ∈ I, c x ∈ I) {w : R} (hw : w + c w = 1)
    {e : R} (he : e ∈ I) (hce : c e = e) : ∃ x, x * c x = 1 + e := by
  obtain ⟨t, htI, ht⟩ := exists_mem_add_mul_sq_eq I (w * c w) he
  have hct : c t = t := by
    have h1 : c t + w * c w * c t ^ 2 = e := by
      have h := congrArg c ht
      simp only [map_add, map_mul, map_pow, hc, hce] at h
      linear_combination h
    have hm : w * c w * (t + c t) ∈ I := I.mul_mem_left _ (I.add_mem htI (hI t htI))
    obtain ⟨U, hU⟩ := (Ideal.mem_jacobson_bot.mp (HenselianRing.jac hm)) 1
    have hz : (t - c t) * (U : R) = 0 := by
      rw [hU]
      linear_combination ht - h1
    have h2 := (U.isUnit.mul_left_eq_zero).mp hz
    linear_combination -h2
  refine ⟨1 + w * t, ?_⟩
  rw [map_add, map_one, map_mul, hct]
  linear_combination ht + t * hw
end GlobalTheory.HenselianNorm
