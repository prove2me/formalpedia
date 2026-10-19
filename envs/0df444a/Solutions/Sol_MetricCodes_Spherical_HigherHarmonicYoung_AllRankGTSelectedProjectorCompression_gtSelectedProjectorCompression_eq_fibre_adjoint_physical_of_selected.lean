-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedProjectorCompression.gtSelectedProjectorCompression_eq_fibre_adjoint_physical_of_selected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:45.453197+00:00
-- url     : https://prove2.me/submissions/c89703f4-7c59-489a-98e1-e30c0aba8276

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

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
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedProjectorCompression
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanHodgeSelector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankRawProjectedRaiseMickelsson
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankGelfandTsetlinHarmonicIsometry
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowAxialAdjointGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedProjectorCompression
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (row : Fin (r + 2))
    (hselected : ∀ p : HarmonicYoungSpace (n := n) mu,
      allRankCartanCharacteristicProjector lam (row, true)
          (canonicalGelfandTsetlinAxisTensor lam mu h hgram p) =
        gtSelectedRowClebschRangeProjector lam row
          (canonicalGelfandTsetlinAxisTensor lam mu h hgram p)) :
    gtSelectedProjectorCompression lam mu h hgram row =
      (canonicalGelfandTsetlinFibre lam mu h hgram).toLinearMap.adjoint.comp
        ((gtSelectedPhysicalAxisCompression lam row).comp
          (canonicalGelfandTsetlinFibre lam mu h hgram).toLinearMap) := by
  let axis := EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n)
  let F := canonicalGelfandTsetlinFibre lam mu h hgram
  let A := gtYoungAxisTensor lam axis
  have haxis : canonicalGelfandTsetlinAxisTensor lam mu h hgram =
      A.comp F.toLinearMap := rfl
  apply LinearMap.ext
  intro p
  unfold gtSelectedProjectorCompression gtSelectedPhysicalAxisCompression
  rw [haxis, LinearMap.adjoint_comp]
  simp only [LinearMap.comp_apply]
  change
    F.adjoint (A.adjoint
      (allRankCartanCharacteristicProjector lam (row, true)
        (canonicalGelfandTsetlinAxisTensor lam mu h hgram p))) =
      F.adjoint (A.adjoint
        (gtSelectedRowClebschRangeProjector lam row
          (canonicalGelfandTsetlinAxisTensor lam mu h hgram p)))
  rw [hselected p]
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedProjectorCompression
