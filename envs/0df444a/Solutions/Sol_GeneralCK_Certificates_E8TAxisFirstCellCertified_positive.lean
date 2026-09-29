-- Prove2me | solution 1 for GeneralCK.Certificates.E8TAxisFirstCellCertified.positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T00:55:41.242293+00:00
-- url     : https://prove2.me/submissions/b051eb79-87b2-4d39-b204-e9264abdc504

import Definitions.Def_GeneralCK_E8_canonical_inverse_jet
import Definitions.Def_GeneralCK_E8_first_cell_Taylor_interface
import Definitions.Def_GeneralCK_E8_first_cell_inputs
import Definitions.Def_GeneralCK_E8_first_cell_jet_graphs
import Definitions.Def_GeneralCK_E8_interval_checkers
import Definitions.Def_GeneralCK_E8_mixed_polynomial_interface
import Definitions.Def_GeneralCK_E8_semantic_core
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.DivMod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneContinuity
import Theorems.Thm_GeneralCK_Certificates_E8TAxisFirstCellEndpointWitnesses_centerA_covers
import Theorems.Thm_GeneralCK_Certificates_E8TAxisFirstCellEndpointWitnesses_centerB_covers
import Theorems.Thm_GeneralCK_Certificates_E8TAxisFirstCellEndpointWitnesses_centerC_covers
import Theorems.Thm_GeneralCK_Certificates_E8TAxisFirstCellEndpointWitnesses_centerD_covers
import Theorems.Thm_GeneralCK_Certificates_E8TAxisFirstCellEndpointWitnesses_wholeA_covers_slope
import Theorems.Thm_GeneralCK_Certificates_E8TAxisFirstCellEndpointWitnesses_wholeB_covers_slope
import Theorems.Thm_GeneralCK_Certificates_E8TAxisFirstCellEndpointWitnesses_wholeC_covers_slope
import Theorems.Thm_GeneralCK_Certificates_E8TAxisFirstCellEndpointWitnesses_wholeD_covers_slope
import Theorems.Thm_GeneralCK_Certificates_E8TAxisFirstCellGraphCenterA_qJetBox_contains
import Theorems.Thm_GeneralCK_Certificates_E8TAxisFirstCellGraphCenterB_qJetBox_contains
import Theorems.Thm_GeneralCK_Certificates_E8TAxisFirstCellGraphCenterC_qJetBox_contains
import Theorems.Thm_GeneralCK_Certificates_E8TAxisFirstCellGraphCenterD_qJetBox_contains
import Theorems.Thm_GeneralCK_Certificates_E8TAxisFirstCellGraphWholeA_qJetBox_contains
import Theorems.Thm_GeneralCK_Certificates_E8TAxisFirstCellGraphWholeB_qJetBox_contains
import Theorems.Thm_GeneralCK_Certificates_E8TAxisFirstCellGraphWholeC_qJetBox_contains
import Theorems.Thm_GeneralCK_Certificates_E8TAxisFirstCellGraphWholeD_qJetBox_contains
import Theorems.Thm_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor_Data_firstCell_positive
import Theorems.Thm_GeneralCK_Certificates_E8TAxisMixedCoefficients_mixedBox_sound

section
namespace GeneralCK.Certificates.E8TAxisFirstCellBridge

open GeneralCK E8TAxisOneCellGeometry E8TAxisMixedCoefficients
open E8TAxisDeltaDirectionalJet E8TAxisCenteredReplaySoundness
open E8TAxisOneCellArithmetic DyadicInterval













theorem InverseBoxes.coeff_sound {p : ℕ} {b : InverseBoxes p} {s t : ℝ}
    (h : b.ContainsAt s t) (i j : ℕ) :
    (b.coeff i j).Contains (mixed qJet s t i j) :=
  mixedBox_sound h.1 h.2.1 h.2.2.1 h.2.2.2 i j

















end GeneralCK.Certificates.E8TAxisFirstCellBridge
end

section
namespace GeneralCK.Certificates.E8TAxisFirstCellCertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000











theorem center_0_1_checked :
    centerBoxes.coeff 0 1 = data.coeff 0 1 := by decide

theorem center_0_2_checked :
    centerBoxes.coeff 0 2 = data.coeff 0 2 := by decide

theorem center_1_1_checked :
    centerBoxes.coeff 1 1 = data.coeff 1 1 := by decide

theorem center_0_3_checked :
    centerBoxes.coeff 0 3 = data.coeff 0 3 := by decide

theorem center_1_2_checked :
    centerBoxes.coeff 1 2 = data.coeff 1 2 := by decide

theorem center_2_1_checked :
    centerBoxes.coeff 2 1 = data.coeff 2 1 := by decide

theorem center_0_4_checked :
    centerBoxes.coeff 0 4 = data.coeff 0 4 := by decide

theorem center_1_3_checked :
    centerBoxes.coeff 1 3 = data.coeff 1 3 := by decide

theorem center_2_2_checked :
    centerBoxes.coeff 2 2 = data.coeff 2 2 := by decide

theorem center_3_1_checked :
    centerBoxes.coeff 3 1 = data.coeff 3 1 := by decide

theorem whole_0_5_checked :
    wholeBoxes.coeff 0 5 = data.coeff 0 5 := by decide

theorem whole_1_4_checked :
    wholeBoxes.coeff 1 4 = data.coeff 1 4 := by decide

theorem whole_2_3_checked :
    wholeBoxes.coeff 2 3 = data.coeff 2 3 := by decide

theorem whole_3_2_checked :
    wholeBoxes.coeff 3 2 = data.coeff 3 2 := by decide

theorem whole_4_1_checked :
    wholeBoxes.coeff 4 1 = data.coeff 4 1 := by decide

theorem replay_positive : data.replay.positiveCheck = true := by decide



theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsAt s t) :
    data.CenterEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsAt s t) :
    data.RemainderEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_sound h 4 1





end GeneralCK.Certificates.E8TAxisFirstCellCertifiedArithmetic
end

section
namespace GeneralCK.Certificates.E8TAxisFirstCellCertified
open GeneralCK Set E8TAxisOneCellGeometry E8TAxisFirstCellCertifiedArithmetic
open E8TAxisDeltaDirectionalJet E8TAxisMixedCoefficients
open E8TAxisGeneralCenteredTaylor

theorem centerBoxes_contains : centerBoxes.ContainsAt centerS centerT := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisFirstCellEndpointWitnesses.centerA_covers
    have hh := E8TAxisFirstCellGraphCenterA.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisFirstCellEndpointWitnesses.centerB_covers
    have hh := E8TAxisFirstCellGraphCenterB.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisFirstCellEndpointWitnesses.centerC_covers
    have hh := E8TAxisFirstCellGraphCenterC.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisFirstCellEndpointWitnesses.centerD_covers
    have hh := E8TAxisFirstCellGraphCenterD.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh

theorem wholeBoxes_contains {s t : ℝ} (h : InFirstCell s t) :
    wholeBoxes.ContainsAt s t := by
  rcases h with ⟨hsl, hsu, htl, htu⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ :=
      E8TAxisFirstCellEndpointWitnesses.wholeA_covers_slope (s := t)
        ⟨by linarith, by linarith⟩
    have hh := E8TAxisFirstCellGraphWholeA.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ :=
      E8TAxisFirstCellEndpointWitnesses.wholeB_covers_slope (s := 2*s+t)
        ⟨by linarith, by linarith⟩
    have hh := E8TAxisFirstCellGraphWholeB.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ :=
      E8TAxisFirstCellEndpointWitnesses.wholeC_covers_slope (s := s+t)
        ⟨by linarith, by linarith⟩
    have hh := E8TAxisFirstCellGraphWholeC.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ :=
      E8TAxisFirstCellEndpointWitnesses.wholeD_covers_slope (s := s)
        ⟨by linarith, by linarith⟩
    have hh := E8TAxisFirstCellGraphWholeD.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh



theorem mixedBounds : MixedBounds :=
  ⟨centerEnclosed_of_contains centerBoxes_contains,
    fun _ _ h => wholeEnclosed_of_contains (wholeBoxes_contains h)⟩















end GeneralCK.Certificates.E8TAxisFirstCellCertified
end

open GeneralCK GeneralCK.Certificates GeneralCK.Certificates.E8TAxisFirstCellCertified
open GeneralCK Set E8TAxisOneCellGeometry E8TAxisFirstCellCertifiedArithmetic
open E8TAxisDeltaDirectionalJet E8TAxisMixedCoefficients
open E8TAxisGeneralCenteredTaylor
theorem solution {s t : ℝ} (h : InFirstCell s t) :
    0 < e8RegularDeltaT s t :=
  Data.firstCell_positive rfl rfl mixedBounds.1 mixedBounds.2 replay_positive h
