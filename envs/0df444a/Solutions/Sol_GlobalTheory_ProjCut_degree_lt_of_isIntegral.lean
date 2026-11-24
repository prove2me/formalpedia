-- Prove2me | solution 1 for GlobalTheory.ProjCut.degree_lt_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:41:56.936885+00:00
-- url     : https://prove2.me/submissions/181e3954-b43a-4db2-bbdf-50ade07c1619

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MonomialCountAndBinomialEstimates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IntegralStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Theorems.Thm_GlobalTheory_IsHilbertPoly_unique


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
theorem _root_.solution {A : Type*} [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (ℳ : ℤ → Submodule k A) [DirectSum.Decomposition ℳ] {H : Polynomial ℚ}
    (hH : IsHilbertPoly ℳ H) {s : ℕ} (z : Fin s → A)
    (hz : ∀ j n, ∀ m ∈ ℳ n, z j * m ∈ ℳ (n + 1))
    (hint : (aeval z : MvPolynomial (Fin s) k →ₐ[k] A).toRingHom.IsIntegral) :
    H.degree < (s : ℕ) := by
  let φ : MvPolynomial (Fin s) k →ₐ[k] A := aeval z
  letI := φ.toRingHom.toAlgebra
  haveI : IsScalarTower k (MvPolynomial (Fin s) k) A :=
    IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := ⟨hint⟩
  haveI : Algebra.FiniteType (MvPolynomial (Fin s) k) A :=
    Algebra.FiniteType.of_restrictScalars_finiteType k _ _
  haveI : Module.Finite (MvPolynomial (Fin s) k) A := Algebra.IsIntegral.finite
  obtain ⟨H', hH', hd⟩ := exists_isHilbertPoly (ι := Fin s) ℳ (fun j n m hm => by
    have : algebraMap (MvPolynomial (Fin s) k) A (X j) = z j := aeval_X _ _
    rw [Algebra.smul_def, this]
    exact hz j n m hm)
  rwa [hH'.unique hH, Fintype.card_fin] at hd
end GlobalTheory.ProjCut
