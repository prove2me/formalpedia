-- Prove2me | solution 1 for GlobalTheory.TraceSpread.isSplitting_embeddings
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:39:01.84805+00:00
-- url     : https://prove2.me/submissions/9eeea70c-e461-416c-acc1-8a02580adde3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CmTypeEigenMultiplicityOfDensePrimes
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
import Theorems.Thm_GlobalTheory_EigenSplit_isSplitting_of_isDomain
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
theorem _root_.solution (K : Type) [Field K] [IsAlgClosed K]
    [CharZero K] :
    _root_.GlobalTheory.EigenSplit.IsSplitting fun φ : E →+* K => φ.comp (algebraMap (𝓞 E) E) := by
  have hinj : Function.Injective fun φ : E →+* K => φ.comp (algebraMap (𝓞 E) E) :=
    fun φ ψ h => IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) h
  have hdisc : IsUnit ((NumberField.discr E : ℤ) : K) :=
    (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero E)).isUnit
  simpa using _root_.GlobalTheory.EigenSplit.isSplitting_of_isDomain (R := K) hinj (Embeddings.card E K)
    (RingHom.id K) hdisc
end _root_.GlobalTheory.TraceSpread
end GlobalTheory.TraceSpread
