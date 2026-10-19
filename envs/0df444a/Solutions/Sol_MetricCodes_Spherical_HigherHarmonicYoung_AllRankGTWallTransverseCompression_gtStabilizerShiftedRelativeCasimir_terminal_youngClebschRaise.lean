-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression.gtStabilizerShiftedRelativeCasimir_terminal_youngClebschRaise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:48.515695+00:00
-- url     : https://prove2.me/submissions/2d0eb18a-71e9-47fb-aaeb-9bf470de6781

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTStabilizerCasimirShift_gtStabilizerShiftedRelativeCasimir_raiseTarget_channel
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallTransverseCompression_stabilizerShift_appendZeroWeight_last_add_half_eq_wall

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
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 600000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirPureAxis
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTStabilizerCasimirShift
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTangentialCompression
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTensorRelativeCompression
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.ThreeRowYoungBranching
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression
theorem _root_.solution
    {r n : ℕ} (mu : Fin (r + 1) → ℕ)
    (p : HarmonicYoungSpace (n := n) (appendZeroWeight mu)) :
    gtStabilizerShiftedRelativeCasimir
      (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
      (youngClebschRaise
        (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
        (appendZeroWeight mu)
        (sum_raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
        (Fin.last (r + 1)) p) =
      (-wallShift (n + 1) (r + 1)) •
        youngClebschRaise
          (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
          (appendZeroWeight mu)
          (sum_raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
          (Fin.last (r + 1)) p := by
  rw [gtStabilizerShiftedRelativeCasimir_raiseTarget_channel
    (appendZeroWeight mu) (Fin.last (r + 1))
    (youngClebschRaise
      (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
      (appendZeroWeight mu)
      (sum_raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
      (Fin.last (r + 1)))
    (fun a b => youngClebschRaise_rotation_intertwine
      (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
      (appendZeroWeight mu)
      (sum_raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
      (Fin.last (r + 1)) a b) p]
  simp only [MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement.gtStabilizerArrowheadNode_neg]
  congr 1
  linarith [stabilizerShift_appendZeroWeight_last_add_half_eq_wall
    (n := n) mu]
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression
