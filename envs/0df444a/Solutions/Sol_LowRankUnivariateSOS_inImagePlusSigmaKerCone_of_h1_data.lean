-- Prove2me | solution 1 for LowRankUnivariateSOS.inImagePlusSigmaKerCone_of_h1_data
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:00:39.471437+00:00
-- url     : https://prove2.me/submissions/ffba5142-1c0b-492e-a1d5-beca23145a97

import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_Certificate
import Definitions.Def_LowRankUnivariateSOS_H1Case
import Theorems.Thm_LowRankUnivariateSOS_inSigmaKerCone_sos_mul_sigma2
import Theorems.Thm_LowRankUnivariateSOS_inImageA_mul_of_isCoprime

set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
namespace LowRankUnivariateSOS
theorem _root_.solution
    (g p q s : Poly) (u : UPair)
    (hu : IsCoprime u.fst u.snd)
    (hs : IsSOS s)
    (hp : p = g * q + s * sigma2 u) :
    InImagePlusSigmaKerCone (scalePair g u) p := by
  rcases inImageA_mul_of_isCoprime g q u hu with ⟨v, hv⟩
  rcases inSigmaKerCone_sos_mul_sigma2 g s u hs with ⟨ws, hwsker, hsum⟩
  refine ⟨v, ws, hwsker, ?_⟩
  rw [hp, hv, hsum]
end LowRankUnivariateSOS
