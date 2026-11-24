-- Prove2me | solution 1 for GlobalTheory.TraceSpread.map_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:39:03.767246+00:00
-- url     : https://prove2.me/submissions/dcd0510b-27cc-4dd8-b87d-b4117447d688

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CmTypeEigenMultiplicityOfDensePrimes
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.TraceSpread
variable {E : Type} [Field E] [NumberField E]
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.TraceSpread
namespace _root_.GlobalTheory.TraceSpread
theorem _root_.solution {R K : Type} [CommRing R] [CommRing K]
    {n : ℕ} (f : R →+* K) (A : Module.End R (Fin n → R))
    (A' : Module.End K (Fin n → K)) (h : ∀ c, f ∘ A c = A' (f ∘ c)) :
    f (LinearMap.trace R _ A) = LinearMap.trace K _ A' := by
  classical
  rw [LinearMap.trace_eq_matrix_trace R (Pi.basisFun R (Fin n)),
    LinearMap.trace_eq_matrix_trace K (Pi.basisFun K (Fin n)), Matrix.trace, Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basisFun_repr, Pi.basisFun_apply]
  have hc : (f ∘ (Pi.single i 1 : Fin n → R)) = Pi.single i 1 := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  rw [← hc, ← h]
  rfl
end _root_.GlobalTheory.TraceSpread
end GlobalTheory.TraceSpread
