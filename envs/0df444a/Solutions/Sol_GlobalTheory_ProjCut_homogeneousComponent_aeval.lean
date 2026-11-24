-- Prove2me | solution 1 for GlobalTheory.ProjCut.homogeneousComponent_aeval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:41:29.706851+00:00
-- url     : https://prove2.me/submissions/ebbde2b4-cd49-440f-8f14-32690e2bf480

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
open ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf
variable {ι k : Type*} [Field k]
namespace GlobalTheory.ProjCut
theorem _root_.solution {σ : Type*} (w : σ → MvPolynomial ι k)
    (hw : ∀ j, (w j).IsHomogeneous 1) (n : ℕ) (g : MvPolynomial σ k) :
    homogeneousComponent n (aeval w g) = aeval w (homogeneousComponent n g) := by
  classical
  induction g using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial d x =>
    have h1 : (monomial d x : MvPolynomial σ k).IsHomogeneous d.degree :=
      isHomogeneous_monomial x rfl
    have h2 := h1.aeval w hw
    rw [one_mul] at h2
    rw [homogeneousComponent_of_mem h1, homogeneousComponent_of_mem h2]
    split_ifs <;> simp
end GlobalTheory.ProjCut
