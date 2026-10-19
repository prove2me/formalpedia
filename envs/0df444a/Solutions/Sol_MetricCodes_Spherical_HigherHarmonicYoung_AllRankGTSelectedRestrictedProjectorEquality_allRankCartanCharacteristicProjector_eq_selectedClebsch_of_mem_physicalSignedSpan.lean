-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedRestrictedProjectorEquality.allRankCartanCharacteristicProjector_eq_selectedClebsch_of_mem_physicalSignedSpan
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.872997+00:00
-- url     : https://prove2.me/submissions/93094216-d4a0-49d9-8b28-924499619e2a

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankCartanCharacteristicProjector_allRankCartanCharacteristicProjector_apply_eigenvector
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankCartanCharacteristicProjector_allRankCartanCharacteristicProjector_youngClebschLower
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTCartanHodgeSelector_gtSelectedRowClebschRangeProjector_youngClebschLower
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTSelectedRestrictedProjectorEquality_gtSelectedRowClebschRangeProjector_signedEigen_eq_zero

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
set_option maxHeartbeats 3000000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedRestrictedProjectorEquality
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicInterpolation
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanHodgeSelector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolventSpectral
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherRepresentationGraph
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedRestrictedProjectorEquality
theorem _root_.solution
    {r n : ℕ} (low : Fin (r + 1) → ℕ)
    (mu : Fin r → ℕ) (hfinite : FiniteInterlacing n low mu)
    (hdom : Antitone low) (row : Fin (r + 1))
    (hhigh : Antitone (raiseWeight low row))
    (v : SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) low)
    (hv : v ∈ gtSelectedPhysicalSignedSpan (n := n) low row) :
    allRankCartanCharacteristicProjector low (row, true) v =
      gtSelectedRowClebschRangeProjector low row v := by
  let P := allRankCartanCharacteristicProjector (n := n) low (row, true)
  let Q := gtSelectedRowClebschRangeProjector (n := n) low row
  have hle : gtSelectedPhysicalSignedSpan (n := n) low row ≤
      LinearMap.ker (P - Q) := by
    unfold gtSelectedPhysicalSignedSpan
    apply sup_le
    · rintro _ ⟨p, rfl⟩
      change
        (P - Q)
            (youngClebschLower low (raiseWeight low row)
              (sum_raiseWeight low row) row p) = 0
      change
        allRankCartanCharacteristicProjector low (row, true)
            (youngClebschLower low (raiseWeight low row)
              (sum_raiseWeight low row) row p) -
          gtSelectedRowClebschRangeProjector low row
            (youngClebschLower low (raiseWeight low row)
              (sum_raiseWeight low row) row p) = 0
      rw [allRankCartanCharacteristicProjector_youngClebschLower
        low mu hfinite (row, true) row,
        gtSelectedRowClebschRangeProjector_youngClebschLower
          low hdom row hhigh]
      simp
    · apply iSup_le
      intro channel v hv
      have heigen := (Module.End.mem_eigenspace_iff).mp hv
      change (P - Q) v = 0
      change
        allRankCartanCharacteristicProjector low (row, true) v -
          gtSelectedRowClebschRangeProjector low row v = 0
      rw [allRankCartanCharacteristicProjector_apply_eigenvector
        low mu hfinite (row, true) channel.val v heigen,
        gtSelectedRowClebschRangeProjector_signedEigen_eq_zero
          low mu hfinite row channel.val channel.property v heigen]
      simp [Ne.symm channel.property]
  have hzero := hle hv
  change (P - Q) v = 0 at hzero
  exact sub_eq_zero.mp hzero
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedRestrictedProjectorEquality
