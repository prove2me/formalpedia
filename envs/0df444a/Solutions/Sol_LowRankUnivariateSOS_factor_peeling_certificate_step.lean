-- Prove2me | solution 1 for LowRankUnivariateSOS.factor_peeling_certificate_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:09:39.147357+00:00
-- url     : https://prove2.me/submissions/85269c20-1223-41bf-968b-494a36f55a08

import Definitions.Def_LowRankUnivariateSOS_UnivariateAlgebra
import Definitions.Def_LowRankUnivariateSOS_UnivariateSOS
import Definitions.Def_LowRankUnivariateSOS_RankTwoMain
import Theorems.Thm_LowRankUnivariateSOS_factor_peeling_image_orthogonal


set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
variable {B : DotForm}
namespace LowRankUnivariateSOS
theorem _root_.solution
    (p : Poly) (u : UPair) :
    IsSOS p → IsSOCP B p u →
      (data : ReducedFactorization u) → data.a ≠ 0 →
      ∃ a g : Poly, ∃ u0 : UPair,
        u = scalePair a u0 ∧ g ≠ 0 ∧ IsCoprime u0.fst u0.snd ∧
          IsCoprime g (sigma2 u0) ∧
            ImageOrthogonalResidual B p (scalePair a u0) (scalePair g u0) := by
  intro hp hsocp data ha
  rcases factor_peeling_image_orthogonal (B := B) p u hsocp data ha with
    ⟨g, hg, hcopg, himg⟩
  refine ⟨data.a, g, data.u0, data.eq_scale, hg, data.reduced_coprime, hcopg, himg⟩
end LowRankUnivariateSOS
