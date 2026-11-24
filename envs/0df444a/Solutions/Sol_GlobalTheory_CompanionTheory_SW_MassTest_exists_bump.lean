-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.MassTest.exists_bump
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:24:36.232669+00:00
-- url     : https://prove2.me/submissions/cce98173-5350-48b2-b60d-56f21b0ba60f

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_BinaryMassMeans_MeanVal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasure
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_TensTop
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TestFunctionExists
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Mass
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.MassTest
namespace GlobalTheory.CompanionTheory.SW.MassTest
theorem _root_.solution {W : Type} [TopologicalSpace W] [T2Space W] [LocallyCompactSpace W] [MeasurableSpace W]
    [BorelSpace W] (ν : Measure W) [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν] {U : Set W}
    (hU : IsOpen U) {x : W} (hx : x ∈ U) :
    ∃ φ : W → ℝ, Continuous φ ∧ HasCompactSupport φ ∧ (∀ X, 0 ≤ φ X) ∧ tsupport φ ⊆ U ∧
      ∫⁻ X, ENNReal.ofReal (φ X) ∂ν ≠ 0 ∧ ∫⁻ X, ENNReal.ofReal (φ X) ∂ν ≠ ⊤ := by
  obtain ⟨K, hK, hxK, hKU⟩ := exists_compact_subset hU hx
  obtain ⟨f, hf1, hf0, hfc, hfr⟩ := exists_continuous_one_zero_of_isCompact (isCompact_singleton (x := x))
    (isOpen_interior (s := K)).isClosed_compl (by simpa using hxK)
  have hsupp : Function.support f ⊆ K := by
    intro y hy
    by_contra hyK
    exact hy (hf0 (fun h => hyK (interior_subset h)))
  have hg : Continuous fun X => ENNReal.ofReal (f X) := ENNReal.continuous_ofReal.comp f.continuous
  refine ⟨f, f.continuous, hfc, fun X => (hfr X).1, ?_, ?_, ?_⟩
  · exact (closure_minimal hsupp hK.isClosed).trans hKU
  · intro h0
    have hpos : 0 < ν {X | ENNReal.ofReal (f X) ≠ 0} := by
      refine IsOpen.measure_pos ν (isOpen_ne_fun hg continuous_const) ⟨x, ?_⟩
      have : f x = 1 := hf1 (Set.mem_singleton x)
      simp [this]
    exact hpos.ne' (ae_iff.1 ((lintegral_eq_zero_iff hg.measurable).1 h0))
  · exact (f.continuous.integrable_of_hasCompactSupport hfc).lintegral_lt_top.ne
end GlobalTheory.CompanionTheory.SW.MassTest
