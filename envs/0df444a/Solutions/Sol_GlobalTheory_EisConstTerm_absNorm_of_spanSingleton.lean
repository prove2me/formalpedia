-- Prove2me | solution 1 for GlobalTheory.EisConstTerm.absNorm_of_spanSingleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:27:46.939941+00:00
-- url     : https://prove2.me/submissions/8c08a0eb-acee-4374-a6d4-0fff0db88efe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumHilbertEisensteinConstantTermPartialZeta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
open GlobalTheory GlobalTheory.EisConstTerm
namespace GlobalTheory.EisConstTerm
theorem _root_.solution (F : Type) [Field F] [NumberField F] (𝔞 : Frac F) (a : F) (J : Ideal (𝓞 F))
    (hJ : (J : FractionalIdeal (𝓞 F)⁰ F) = FractionalIdeal.spanSingleton (𝓞 F)⁰ a *
      ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)) :
    (Ideal.absNorm J : ℝ) = |((Algebra.norm ℚ a : ℚ) : ℝ)| * (dF F * nrm 𝔞) := by
  have h := congrArg FractionalIdeal.absNorm hJ
  have e1 : FractionalIdeal.absNorm (J : FractionalIdeal (𝓞 F)⁰ F) = Ideal.absNorm J := FractionalIdeal.coeIdeal_absNorm J
  have e2 : FractionalIdeal.absNorm ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = Ideal.absNorm (differentIdeal ℤ (𝓞 F)) :=
    FractionalIdeal.coeIdeal_absNorm _
  rw [e1, map_mul, map_mul, FractionalIdeal.absNorm_span_singleton (𝓞 F), e2, absNorm_differentIdeal F (𝓞 F)] at h
  have h' := congrArg (fun q : ℚ => (q : ℝ)) h
  simp only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_abs] at h'
  rw [h', dF, nrm, mul_assoc]
  congr 2
  rw [Nat.cast_natAbs, Int.cast_abs]
end GlobalTheory.EisConstTerm
