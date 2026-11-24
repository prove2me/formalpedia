-- Prove2me | solution 1 for GlobalTheory.jacobiInOut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:13:21.880984+00:00
-- url     : https://prove2.me/submissions/d90d6e3f-7dd9-4e84-8dc5-4ad9e59d6dda

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_InPartMulOutPartMulSq
import Theorems.Thm_GlobalTheory_inPart_mul_outPart_mul_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory
open Formalism.HermitianLattices.GL2PrimeSums Formalism.HermitianLattices.GL2a2
namespace GlobalTheory
theorem _root_.solution : Formalism.HermitianLattices.GL2a2.JacobiInOut := by
  intro m₀ m q hm hq
  have h := inPart_mul_outPart_mul_sq m₀ m hm
  set t := ∏ p ∈ m.primeFactors, p ^ (m.factorization p / 2) with ht
  have htm : t ∣ m := by
    refine Dvd.intro_left (inPart m₀ m * outPart m₀ m * t) ?_
    refine Eq.trans ?_ h
    ring
  have htq : Nat.Coprime t q := Nat.Coprime.coprime_dvd_left htm hq
  have hsq : jacobiSym ((t : ℤ) ^ 2) q = 1 := jacobiSym.sq_one' (by simpa using htq)
  have hz : (m : ℤ) = (inPart m₀ m : ℤ) * (outPart m₀ m : ℤ) * (t : ℤ) ^ 2 := by exact_mod_cast h.symm
  calc jacobiSym (m : ℤ) q
      = jacobiSym ((inPart m₀ m : ℤ) * (outPart m₀ m : ℤ) * (t : ℤ) ^ 2) q := by rw [← hz]
    _ = _ := by rw [jacobiSym.mul_left, jacobiSym.mul_left, hsq, mul_one]
end GlobalTheory
