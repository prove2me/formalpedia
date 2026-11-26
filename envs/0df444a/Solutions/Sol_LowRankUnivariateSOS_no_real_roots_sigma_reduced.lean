-- Prove2me | solution 1 for LowRankUnivariateSOS.no_real_roots_sigma_reduced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:01:21.682676+00:00
-- url     : https://prove2.me/submissions/4cb45a8a-dbed-4138-9a4f-b057c935a1d3

import Definitions.Def_LowRankUnivariateSOS_H1Case
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.EuclideanDomain
import Definitions.Def_LowRankUnivariateSOS_UnivariateAlgebraCore
import Theorems.Thm_LowRankUnivariateSOS_sigma2_not_isRoot_of_coprime

set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
namespace LowRankUnivariateSOS
theorem _root_.solution
    (u : UPair) (data : ReducedFactorization u) :
    SigmaReducedNoRealRoots data.u0 := by
  intro x
  exact sigma2_not_isRoot_of_coprime data.u0 data.reduced_coprime x
end LowRankUnivariateSOS
