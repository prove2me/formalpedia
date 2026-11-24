-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Mass.MeanV.exists_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:54:56.335209+00:00
-- url     : https://prove2.me/submissions/f1227878-6c3d-4bc8-90ec-ccaca777dde7

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_BinaryMassMeans_MeanVal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TsumNeZeroEqSum
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsIntegralMultipleBoundedPlacesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteProductDifferenceBoundStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TailSumOverPlacesSmallStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultipliableLocalFactorsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalFactorSandwichApproxStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EulerProductConvergenceBoundStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TruncatedSumLimitStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalHaarMeasureSingletonStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MeanValueFormula
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
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Mass GlobalTheory.CompanionTheory.Mass.MeanV
namespace GlobalTheory.CompanionTheory.Mass.MeanV
theorem _root_.solution (a : ℝ) (n : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ e : ℝ, 0 < e ∧ e ≤ 1 ∧ a * (1 + e) ^ n ≤ a + η ∧ a - η ≤ a * (1 - e) ^ n := by
  have c1 : Tendsto (fun t : ℝ => a * (1 + t) ^ n) (𝓝 0) (𝓝 a) := by
    have : Continuous fun t : ℝ => a * (1 + t) ^ n := by fun_prop
    simpa using this.tendsto 0
  have c2 : Tendsto (fun t : ℝ => a * (1 - t) ^ n) (𝓝 0) (𝓝 a) := by
    have : Continuous fun t : ℝ => a * (1 - t) ^ n := by fun_prop
    simpa using this.tendsto 0
  have e1 := c1.eventually_lt_const (show a < a + η by linarith)
  have e2 := c2.eventually_const_lt (show a - η < a by linarith)
  obtain ⟨r, hr, hh⟩ := Metric.eventually_nhds_iff.1 (e1.and e2)
  refine ⟨min (r / 2) 1, lt_min (by linarith) one_pos, min_le_right _ _, ?_⟩
  have hd : dist (min (r / 2) 1) (0 : ℝ) < r := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (lt_min (by linarith) one_pos)]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  exact ⟨(hh hd).1.le, (hh hd).2.le⟩
end GlobalTheory.CompanionTheory.Mass.MeanV
