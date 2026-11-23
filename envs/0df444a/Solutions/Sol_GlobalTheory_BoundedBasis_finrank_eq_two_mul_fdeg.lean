-- Prove2me | solution 1 for GlobalTheory.BoundedBasis.finrank_eq_two_mul_fdeg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:47.643027+00:00
-- url     : https://prove2.me/submissions/44cdb054-c4c8-4c56-8e09-aec99739d2e0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegerApproximationCountHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFinsetTypesOfBoundedBases

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory
open GlobalTheory.BoundedBasis
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.BoundedBasis
theorem _root_.solution [IsCMField E] : finrank ℚ E = 2 * fdeg E := by
  have h := IsTotallyComplex.finrank E
  unfold fdeg
  omega
end GlobalTheory.BoundedBasis
