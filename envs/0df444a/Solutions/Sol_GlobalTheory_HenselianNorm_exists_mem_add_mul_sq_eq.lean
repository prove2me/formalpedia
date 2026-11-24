-- Prove2me | solution 1 for GlobalTheory.HenselianNorm.exists_mem_add_mul_sq_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:26:21.366107+00:00
-- url     : https://prove2.me/submissions/38fd6187-48c5-4a3c-9dfb-c13f354e77a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_FiniteInvolutionFixedUnitEqMulConjStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsNormEqFixedUnitHenselian

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
    (n : R) {e : R} (he : e ∈ I) : ∃ t ∈ I, t + n * t ^ 2 = e := by
  obtain ⟨s, hs, hsI⟩ := HenselianRing.is_henselian (I := I) (X ^ 2 + X - C (n * e))
    (by monicity!) 0
    (by
      simp only [eval_sub, eval_add, eval_pow, eval_X, eval_C]
      simpa using I.mul_mem_left n he)
    (by simp)
  have h0 : eval s (X ^ 2 + X - C (n * e)) = 0 := hs
  simp only [eval_sub, eval_add, eval_pow, eval_X, eval_C] at h0
  rw [sub_zero] at hsI
  obtain ⟨U, hU⟩ := (Ideal.mem_jacobson_bot.mp (HenselianRing.jac hsI)) 1
  have hinv : (s + 1) * (↑U⁻¹ : R) = 1 := by
    rw [show s + 1 = (U : R) by rw [hU]; ring]
    exact U.mul_inv
  have hnt : n * (e * ↑U⁻¹) = s := by
    linear_combination (-(↑U⁻¹ : R)) * h0 + s * hinv
  refine ⟨e * ↑U⁻¹, I.mul_mem_right _ he, ?_⟩
  linear_combination (e * ↑U⁻¹) * hnt + e * hinv
end GlobalTheory.HenselianNorm
