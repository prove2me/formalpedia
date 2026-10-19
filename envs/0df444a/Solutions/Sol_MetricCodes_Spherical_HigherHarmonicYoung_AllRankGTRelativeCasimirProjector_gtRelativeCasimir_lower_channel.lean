-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector.gtRelativeCasimir_lower_channel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.831113+00:00
-- url     : https://prove2.me/submissions/b2ceec74-83bf-423d-8891-3a7812c87c7b

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTRelativeCasimirProjector_gtRelativeCasimir_channel
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTRelativeCasimirProjector_gtRelativeCasimir_lower_eigenvalue

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
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 600000
open scoped BigOperators TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
theorem _root_.solution {r n : ℕ}
    (target source : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hsource : target = raiseWeight source row)
    (A : HarmonicYoungSpace (n := n) source →ₗ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) target))
    (hA : ∀ a b : Fin n,
      A.comp (youngAmbientRotation source a b) =
        (ClebschRotation.tensorAmbientRotation target a b).comp A)
    (p : HarmonicYoungSpace (n := n) source) :
    gtRelativeCasimir target (A p) =
      signedNode (ambientShift n target) (row, false) • A p := by
  rw [gtRelativeCasimir_channel source target A hA,
    gtRelativeCasimir_lower_eigenvalue target source row hsource]
  rfl
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
