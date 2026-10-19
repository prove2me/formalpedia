-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTerminalNegativeProjectorVanishing.allRankCartanCharacteristicProjector_last_false_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.872997+00:00
-- url     : https://prove2.me/submissions/bdbd542e-c399-4af8-a1fe-33f827b34b4c

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankCartanCharacteristicProjector_allRankCartanCharacteristicProjector_raise_channel
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankCartanCharacteristicProjector_allRankCartanCharacteristicProjector_lower_channel
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankOrthogonalTensorPieriActualChannels_paddedOrthogonalTensorPieriChannel_rotation_intertwine
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankOrthogonalTensorPieriActualChannels_paddedOrthogonalTensorPieri_iSup_range_eq_top

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option maxHeartbeats 1800000
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTerminalNegativeProjectorVanishing
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTerminalNegativeProjectorVanishing
theorem _root_.solution
    {r n : ℕ} (hn : 2 * r + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (hzero : lam (Fin.last r) = 0)
    (mu : Fin r → ℕ) (hfinite : FiniteInterlacing n lam mu) :
    allRankCartanCharacteristicProjector (n := n)
        lam (Fin.last r, false) = 0 := by
  let P := allRankCartanCharacteristicProjector (n := n)
    lam (Fin.last r, false)
  let A := paddedOrthogonalTensorPieriChannel hn lam hdom
  have hle : (⨆ i : PaddedPieriChannel lam,
      LinearMap.range (A i).toLinearMap) ≤ LinearMap.ker P := by
    apply iSup_le
    intro i
    rintro _ ⟨q, rfl⟩
    change P (A i q) = 0
    cases i with
    | inl row =>
        change allRankCartanCharacteristicProjector lam
          (Fin.last r, false)
            ((paddedOrthogonalTensorPieriChannel hn lam hdom
              (Sum.inl row)).toLinearMap q) = 0
        have hraise := allRankCartanCharacteristicProjector_raise_channel
          lam mu hfinite (Fin.last r, false) row.val
          (paddedOrthogonalTensorPieriChannel hn lam hdom
            (Sum.inl row)).toLinearMap
          (paddedOrthogonalTensorPieriChannel_rotation_intertwine
            hn lam hdom (Sum.inl row)) q
        rw [if_neg (by simp)] at hraise
        exact hraise
    | inr row =>
        have hsource : lam =
            raiseWeight (paddedPieriSource lam (Sum.inr row)) row.val :=
          (raiseWeight_loweredInternalYoungWeight
            lam row.val row.property.1).symm
        change allRankCartanCharacteristicProjector lam
          (Fin.last r, false)
            ((paddedOrthogonalTensorPieriChannel hn lam hdom
              (Sum.inr row)).toLinearMap q) = 0
        rw [allRankCartanCharacteristicProjector_lower_channel
          lam mu hfinite (Fin.last r, false) row.val
          (paddedPieriSource lam (Sum.inr row)) hsource
          (paddedOrthogonalTensorPieriChannel hn lam hdom
            (Sum.inr row)).toLinearMap
          (paddedOrthogonalTensorPieriChannel_rotation_intertwine
            hn lam hdom (Sum.inr row))]
        have hne : (Fin.last r, false) ≠ (row.val, false) := by
          intro heq
          have hrow := congrArg Prod.fst heq
          change Fin.last r = row.val at hrow
          have hpos := row.property.1
          rw [← hrow, hzero] at hpos
          omega
        simp [hne]
  rw [paddedOrthogonalTensorPieri_iSup_range_eq_top hn lam hdom hzero] at hle
  apply LinearMap.ext
  intro x
  have hx := hle (show x ∈ (⊤ : Submodule ℝ
    (SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) lam)) from trivial)
  exact hx
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTerminalNegativeProjectorVanishing
