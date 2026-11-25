-- Prove2me | solution 1 for GlobalTheory.ProjCut.finrank_homogeneousSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:52:31.389811+00:00
-- url     : https://prove2.me/submissions/580420df-de54-4c46-bb42-42a6a837ef7a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MonomialCountAndBinomialEstimates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IntegralStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Theorems.Thm_GlobalTheory_natCard_degree_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module
open GlobalTheory
open GlobalTheory.ProjCut
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {ι k : Type*} [Field k]
namespace GlobalTheory.ProjCut
theorem _root_.solution [Fintype ι] (n : ℕ) :
    finrank k (homogeneousSubmodule ι k n) = (n + Fintype.card ι - 1).choose n := by
  rw [← natCard_degree_eq, homogeneousSubmodule_eq_finsupp_supported]
  exact finrank_eq_nat_card_basis (basisRestrictSupport k _)
end GlobalTheory.ProjCut
