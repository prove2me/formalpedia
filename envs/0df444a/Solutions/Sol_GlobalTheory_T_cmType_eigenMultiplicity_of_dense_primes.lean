-- Prove2me | solution 1 for GlobalTheory.T.cmType_eigenMultiplicity_of_dense_primes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:17:05.783905+00:00
-- url     : https://prove2.me/submissions/16b7186e-df1e-4eb1-9704-2b1a98f79a2c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CmTypeEigenMultiplicityOfDensePrimes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CmTypeEigenMultiplicityOfDensePrimesStatement
import Theorems.Thm_GlobalTheory_eigenMult_of_dense


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q n : ℕ) (R : Type) [CommRing R] [IsReduced R] (M : 𝓞 E →+* Module.End R (Fin n → R)) (r : R), r ^ 2 = -(H.d : R) → Dense {P : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : CharZero K) (f : R →+* K) (M' : 𝓞 E →+* Module.End K (Fin n → K)), RingHom.ker f = P.asIdeal ∧ (∀ a c, f ∘ M a c = M' a (f ∘ c)) ∧ ∀ τ : 𝓞 E →+* K, (τ H.rt = f r → Module.finrank K (GlobalTheory.EigenSplit.eigenSub M' τ) = p) ∧ (τ H.rt ≠ f r → Module.finrank K (GlobalTheory.EigenSplit.eigenSub M' τ) = q)} → ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (f : R →+* K) (M' : 𝓞 E →+* Module.End K (Fin n → K)), (∀ a c, f ∘ M a c = M' a (f ∘ c)) → ∀ τ : 𝓞 E →+* K, (τ H.rt = f r → Module.finrank K (GlobalTheory.EigenSplit.eigenSub M' τ) = p) ∧ (τ H.rt ≠ f r → Module.finrank K (GlobalTheory.EigenSplit.eigenSub M' τ) = q) := by
  first | exact @GlobalTheory.eigenMult_of_dense | exact GlobalTheory.eigenMult_of_dense | (intros; apply GlobalTheory.eigenMult_of_dense <;> assumption)
end _root_.GlobalTheory.T
