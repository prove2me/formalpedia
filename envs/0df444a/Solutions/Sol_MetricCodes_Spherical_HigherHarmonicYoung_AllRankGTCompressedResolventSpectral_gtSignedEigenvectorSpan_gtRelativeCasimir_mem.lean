-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolventSpectral.gtSignedEigenvectorSpan_gtRelativeCasimir_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.222992+00:00
-- url     : https://prove2.me/submissions/10c61520-3fd5-4abb-bff4-0ae5641ce4e1

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
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 600000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolventSpectral
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAppendedRowExclusion
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankTensorClebschCompleteness
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue
open MetricCodes.Spherical.ThreeRowYoungBranching
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolventSpectral
theorem _root_.solution {r n : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (v : SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) lam)
    (hv : v ∈ gtSignedEigenvectorSpan (n := n) lam) :
    gtRelativeCasimir (n := n) lam v ∈
      gtSignedEigenvectorSpan (n := n) lam := by
  change v ∈ ⨆ z : Fin (r + 1) × Bool,
    Module.End.eigenspace (gtRelativeCasimir (n := n) lam)
      (signedNode (HigherChannel.ambientShift n lam) z) at hv
  change gtRelativeCasimir (n := n) lam v ∈
    ⨆ z : Fin (r + 1) × Bool,
      Module.End.eigenspace (gtRelativeCasimir (n := n) lam)
        (signedNode (HigherChannel.ambientShift n lam) z)
  refine Submodule.iSup_induction
    (motive := fun w => gtRelativeCasimir (n := n) lam w ∈
      gtSignedEigenvectorSpan (n := n) lam) _ hv ?_ ?_ ?_
  · intro z w hw
    apply Submodule.mem_iSup_of_mem z
    rw [(Module.End.mem_eigenspace_iff).mp hw]
    exact (Module.End.eigenspace _ _).smul_mem _ hw
  · simp
  · intro v w hv hw
    rw [map_add]
    exact (gtSignedEigenvectorSpan (n := n) lam).add_mem hv hw
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolventSpectral
