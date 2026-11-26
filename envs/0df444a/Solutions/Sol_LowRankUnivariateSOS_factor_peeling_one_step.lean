-- Prove2me | solution 1 for LowRankUnivariateSOS.factor_peeling_one_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:02:58.515743+00:00
-- url     : https://prove2.me/submissions/7d292c83-df45-4f24-b448-00edb442e0cc

import Definitions.Def_LowRankUnivariateSOS_UnivariateAlgebraCore
import Definitions.Def_LowRankUnivariateSOS_PeelingStep
import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Data.List.Prime
import Mathlib.Data.Multiset.Filter
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Definitions.Def_LowRankUnivariateSOS_UnivariateAlgebra
import Theorems.Thm_LowRankUnivariateSOS_hasPeelingWitness_of_factor_step


set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
namespace LowRankUnivariateSOS
theorem _root_.solution
    (u : UPair) (data : ReducedFactorization u) :
      {gStart gNext : Poly} →
        QuadraticFactorStep data.u0 gStart gNext →
          HasPeelingWitness u (scalePair gStart data.u0) (scalePair gNext data.u0) := by
  intro gStart gNext hfg
  exact hasPeelingWitness_of_factor_step data.eq_scale data.reduced_coprime hfg
end LowRankUnivariateSOS
