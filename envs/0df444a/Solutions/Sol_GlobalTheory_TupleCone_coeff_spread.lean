-- Prove2me | solution 1 for GlobalTheory.TupleCone.coeff_spread
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:03:25.394053+00:00
-- url     : https://prove2.me/submissions/067491c5-6ee0-4ae3-8a2a-7b5ba96ea45c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIntegralRatioRingIffMemAdjoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TupleCone
open Polynomial
variable (o : Type*) [CommRing o] {L : Type*} [Field L] [Algebra o L] {σ : Type*} (t : σ → L)
variable {o t}
namespace GlobalTheory.TupleCone
theorem _root_.solution {L : Type*} [CommRing L] (p : L[X]) (n : ℕ) :
    (spread L p).coeff n = C (p.coeff n) * X ^ n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, coeff_add, hp, hq, add_mul]
  | monomial m a =>
    rw [spread, coe_eval₂RingHom, eval₂_monomial, mul_pow, ← C_pow, RingHom.comp_apply,
      ← mul_assoc, ← C_mul, coeff_C_mul_X_pow, coeff_monomial]
    by_cases h : n = m
    · simp [h]
    · simp [h, Ne.symm h]
end GlobalTheory.TupleCone
