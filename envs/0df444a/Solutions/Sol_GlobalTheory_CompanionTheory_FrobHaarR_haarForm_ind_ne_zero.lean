-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FrobHaarR.haarForm_ind_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:33:18.3558+00:00
-- url     : https://prove2.me/submissions/3b715a95-a112-4947-96f0-b60e0a15b387

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
theorem _root_.solution (μ : Measure G) [μ.IsHaarMeasure] (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) : haarForm μ (ind K hK) ≠ 0 := by
  have e : haarForm μ (ind K hK) = ∫ x, Set.indicator (K : Set G) (fun _ => (1 : ℂ)) x ∂μ := rfl
  rw [e, integral_indicator_const (1 : ℂ) K.isOpen.measurableSet]
  have h0 : μ (K : Set G) ≠ 0 := (K.isOpen.measure_pos μ ⟨1, K.one_mem⟩).ne'
  have h1 : μ.real (K : Set G) ≠ 0 := by
    rw [Measure.real, ENNReal.toReal_ne_zero]
    exact ⟨h0, hK.measure_lt_top.ne⟩
  simpa using h1
end GlobalTheory.CompanionTheory.FrobHaarR
