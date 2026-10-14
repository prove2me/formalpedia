-- Prove2me | solution 2 for OAI.PiExponent.pi_eventual_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-11T13:42:12.996919+00:00
-- url     : https://prove2.me/submissions/c57d8b09-857b-4c52-bafa-36dd13f28219
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_piEventualLowerBound_of_interpolation_and_analytic_aggregate
import Theorems.Thm_OAI_PiExponent_AdmissibleMatrixInterpolation_globalInterpolation
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_analyticAggregate

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution : PiEventualLowerBound :=
  DeterminantContradiction.piEventualLowerBound_of_interpolation_and_analytic_aggregate
    AdmissibleMatrixInterpolation.globalInterpolation LiteralAnalytic.analyticAggregate
