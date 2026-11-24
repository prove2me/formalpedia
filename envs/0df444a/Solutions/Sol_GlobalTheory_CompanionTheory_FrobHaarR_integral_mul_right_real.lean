-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FrobHaarR.integral_mul_right_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:33:20.123814+00:00
-- url     : https://prove2.me/submissions/e5987933-e0ff-4aea-9b36-42b48d8d453e

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InvariantFunctionalEqHaarMultiple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FrobHaarR
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
variable [LocallyCompactSpace G]
namespace GlobalTheory.CompanionTheory.FrobHaarR
theorem _root_.solution (hU : IsUnimod G) (μ : Measure G) [μ.IsHaarMeasure] (g : G)
    {u : G → ℝ} (hu : Continuous u) (hcu : HasCompactSupport u) :
    ∫ x, u (x * g) ∂μ = ∫ x, u x ∂μ := by
  have h := integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport (map (· * g) μ) μ hu hcu
  have h1 : modularCharacterFun g = 1 := hU g
  rw [integral_smul_nnreal_measure, ← modularCharacterFun_eq_haarScalarFactor μ g, h1, one_smul,
    integral_map (AEMeasurable.mul_const aemeasurable_id' _) hu.aestronglyMeasurable] at h
  exact h
end GlobalTheory.CompanionTheory.FrobHaarR
