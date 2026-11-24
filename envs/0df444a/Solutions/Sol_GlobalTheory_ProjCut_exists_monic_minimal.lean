-- Prove2me | solution 1 for GlobalTheory.ProjCut.exists_monic_minimal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:41:29.002009+00:00
-- url     : https://prove2.me/submissions/b785fc3c-68ee-4742-9af9-9fbb9159ea42

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
theorem _root_.solution {R A : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing A] [IsDomain A] (φ : R →+* A) (hinj : Function.Injective φ) (hint : φ.IsIntegral)
    (t : A) : ∃ p : Polynomial R, p.Monic ∧ 0 < p.natDegree ∧ p.eval₂ φ t = 0 ∧
      ∀ a : Fin p.natDegree → R, ∑ j, φ (a j) * t ^ (j : ℕ) = 0 → a = 0 := by
  letI := φ.toAlgebra
  haveI : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).2 hinj
  have ht : IsIntegral R t := hint t
  refine ⟨minpoly R t, minpoly.monic ht, minpoly.natDegree_pos ht, minpoly.aeval R t, ?_⟩
  intro a ha
  let q : Polynomial.degreeLT R (minpoly R t).natDegree := (Polynomial.degreeLTEquiv R _).symm a
  have hq : (q : Polynomial R) = ∑ j : Fin (minpoly R t).natDegree, Polynomial.monomial (j : ℕ) (a j) := rfl
  have hq0 : (q : Polynomial R) = 0 := by
    by_contra h0
    have h1 := minpoly.IsIntegrallyClosed.degree_le_of_ne_zero (s := t) h0 (by
      rw [hq, map_sum, ← ha]
      simp only [Polynomial.aeval_monomial]
      rfl)
    have h2 := Polynomial.mem_degreeLT.1 q.2
    rw [← Polynomial.degree_eq_natDegree (minpoly.ne_zero ht)] at h2
    exact h2.not_ge h1
  exact (LinearEquiv.map_eq_zero_iff _).1 (Subtype.ext hq0 : q = 0)
end GlobalTheory.ProjCut
