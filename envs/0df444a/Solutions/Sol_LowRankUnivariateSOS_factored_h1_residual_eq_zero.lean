-- Prove2me | solution 1 for LowRankUnivariateSOS.factored_h1_residual_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:02:52.713284+00:00
-- url     : https://prove2.me/submissions/72954851-7403-4dcc-acf7-181d62b7b747

import Mathlib.Tactic.Linarith
import Definitions.Def_LowRankUnivariateSOS_Socp
import Definitions.Def_LowRankUnivariateSOS_H1Case
import Definitions.Def_LowRankUnivariateSOS_FactoredCase
import Theorems.Thm_LowRankUnivariateSOS_factored_h1_decomposition_to_original
import Theorems.Thm_LowRankUnivariateSOS_transformed_image_plus_cone_implies_objective_eq_zero
import Theorems.Thm_LowRankUnivariateSOS_objective_eq_zero_iff_residual_eq_zero


set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
variable {B : DotForm} [Fact B.toQuadraticMap.PosDef]
namespace LowRankUnivariateSOS
theorem _root_.solution
    (a g p q s : Poly) (u0 : UPair)
    (hg : g ≠ 0)
    (hcop : IsCoprime u0.fst u0.snd)
    (hs : IsSOS s)
    (hp : p = g * q + s * sigma2 u0)
    (himg : ImageOrthogonalResidual B p (scalePair a u0) (scalePair g u0))
    (hsocp : IsSOCP B p (scalePair a u0)) :
    residual p (scalePair a u0) = 0 := by
  exact (objective_eq_zero_iff_residual_eq_zero (B := B)).mp
    (transformed_image_plus_cone_implies_objective_eq_zero (B := B) hsocp himg
      (factored_h1_decomposition_to_original a g p q s u0 hg hcop hs hp))
end LowRankUnivariateSOS
