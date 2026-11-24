-- Prove2me | solution 1 for GlobalTheory.SimAlg.form_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:48:10.126171+00:00
-- url     : https://prove2.me/submissions/073d1965-467a-4022-a576-9bdc403b72ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SimilitudeDefiniteFormIsAlgebraicOnVector
import Theorems.Thm_GlobalTheory_SimAlg_form_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
open GlobalTheory GlobalTheory.SimAlg
namespace GlobalTheory.SimAlg
theorem _root_.solution (g : ℕ → ℕ → ℤ) (q : ℤ) (hg : ∀ i j, g (i + 1) (j + 1) = q * g i j)
    (f h : ℂ[X]) : form g (X * f) (X * h) = q * form g f h := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp [mul_add, hp, hq]
  | monomial i a =>
    induction h using Polynomial.induction_on' with
    | add p q hp hq => simp only [mul_add, map_add, hp, hq]
    | monomial j c =>
      simp only [← smul_X_eq_monomial, mul_smul_comm, ← pow_succ', map_smul, LinearMap.smul_apply,
        form_pow, hg, smul_eq_mul]
      push_cast; ring
end GlobalTheory.SimAlg
