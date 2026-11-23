-- Prove2me | solution 1 for GlobalTheory.ProjCut.mk_mul_mem_quotPiece
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:55:04.88368+00:00
-- url     : https://prove2.me/submissions/0b928d26-272f-49dc-b593-0fa150d8311c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MonomialCountAndBinomialEstimates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IntegralStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormDegreeLeHilbertDegreeEvalNeZero

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
theorem _root_.solution (I : Ideal (MvPolynomial ι k)) {z : MvPolynomial ι k}
    (hz : z.IsHomogeneous 1) (n : ℤ) {m : MvPolynomial ι k ⧸ I} (hm : m ∈ quotPiece I n) :
    Ideal.Quotient.mk I z * m ∈ quotPiece I (n + 1) := by
  obtain ⟨a, ha, rfl⟩ := hm
  have hz' : z ∈ weightedHomogeneousSubmodule k (fun _ : ι => (1 : ℤ)) ((1 : ℕ) : ℤ) := by
    rwa [weightedHomogeneousSubmodule_one_natCast]
  refine ⟨z * a, ?_, by simp⟩
  rw [add_comm]
  exact IsWeightedHomogeneous.mul hz' ha
end GlobalTheory.ProjCut
