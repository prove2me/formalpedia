-- Prove2me | solution 1 for GlobalTheory.FormalIsogeny.finite_of_finite_quotient_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:09:46.795928+00:00
-- url     : https://prove2.me/submissions/5d78d041-7776-4194-b314-05d3dbeff3ce

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasSubstEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Theorems.Thm_GlobalTheory_FormalIsogeny_finite_of_finite_quotient_smul_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing MvPowerSeries
open GlobalTheory GlobalTheory.FormalIsogeny
namespace GlobalTheory.FormalIsogeny
theorem _root_.solution {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) [IsPrecomplete I A] [IsHausdorff (I.map (algebraMap A B)) B]
    [Module.Finite A (B ⧸ I.map (algebraMap A B))] : Module.Finite A B := by
  have : IsHausdorff I B := IsHausdorff.map_algebraMap_iff.1 ‹_›
  have : Module.Finite A (B ⧸ (I • ⊤ : Submodule A B)) := by
    rw [Ideal.smul_top_eq_map]
    exact .equiv (Submodule.Quotient.restrictScalarsEquiv A (I.map (algebraMap A B))).symm
  exact finite_of_finite_quotient_smul_top I
end GlobalTheory.FormalIsogeny
