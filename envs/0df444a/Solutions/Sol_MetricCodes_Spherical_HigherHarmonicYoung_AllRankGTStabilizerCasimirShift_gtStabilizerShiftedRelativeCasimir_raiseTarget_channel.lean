-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTStabilizerCasimirShift.gtStabilizerShiftedRelativeCasimir_raiseTarget_channel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:47.506255+00:00
-- url     : https://prove2.me/submissions/3023d770-fa23-42a8-835f-29e2ee5cf775

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTRelativeCasimirProjector_gtRelativeCasimir_channel
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTStabilizerCasimirShift_gtStabilizerRelativeCasimir_raiseTarget_eigenvalue

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
set_option maxHeartbeats 2500000
open scoped BigOperators TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTStabilizerCasimirShift
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTStabilizerCasimirShift
theorem _root_.solution
    {r n : ℕ} (mu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (A : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) (raiseWeight mu row)))
    (hA : ∀ a b : Fin n,
      A.comp (youngAmbientRotation mu a b) =
        (ClebschRotation.tensorAmbientRotation
          (raiseWeight mu row) a b).comp A)
    (p : HarmonicYoungSpace (n := n) mu) :
    gtStabilizerShiftedRelativeCasimir (raiseWeight mu row) (A p) =
      gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
        (stabilizerShift (n + 1) mu) (.inr (row, false)) • A p := by
  simp only [gtStabilizerShiftedRelativeCasimir, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.id_apply,
    gtStabilizerArrowheadNode_neg]
  rw [gtRelativeCasimir_channel mu (raiseWeight mu row) A hA,
    gtStabilizerRelativeCasimir_raiseTarget_eigenvalue]
  rw [← add_smul]
  congr 1
  ring
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTStabilizerCasimirShift
