-- Prove2me | solution 1 for LowRankUnivariateSOS.factor_peeling_schedule
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:06:26.649877+00:00
-- url     : https://prove2.me/submissions/2d4cba81-9d15-4f80-8cc9-c78dced8ac81

import Definitions.Def_LowRankUnivariateSOS_UnivariateAlgebraCore
import Definitions.Def_LowRankUnivariateSOS_PeelingStep
import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Data.List.Prime
import Mathlib.Data.Multiset.Filter
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Definitions.Def_LowRankUnivariateSOS_UnivariateAlgebra
import Theorems.Thm_LowRankUnivariateSOS_factor_peeling_decomposition
import Theorems.Thm_LowRankUnivariateSOS_factor_peeling_one_step
import Theorems.Thm_LowRankUnivariateSOS_peelTerminalScale_ne_zero
import Theorems.Thm_LowRankUnivariateSOS_peelingSchedule_of_factors


set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
namespace LowRankUnivariateSOS
theorem _root_.solution
    (u : UPair) (data : ReducedFactorization u) (ha : data.a ≠ 0) :
    ∃ g : Poly, g ≠ 0 ∧ IsCoprime g (sigma2 data.u0) ∧
      PeelingSchedule u data.u0 data.a g := by
  rcases factor_peeling_decomposition u data ha with
    ⟨gBase, g, rs, hgBase, hscale, hgdef, hcopg, hrs⟩
  refine ⟨g, ?_, hcopg, ?_⟩
  · rw [hgdef]
    exact peelTerminalScale_ne_zero hgBase
  rw [hscale, hgdef]
  exact peelingSchedule_of_factors hrs (fun hfg => factor_peeling_one_step u data hfg)
end LowRankUnivariateSOS
