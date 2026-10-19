-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankGTAxisTensorRotationIntertwining.canonicalGelfandTsetlinAxisTensor_rotation_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.872997+00:00
-- url     : https://prove2.me/submissions/03b5d20f-03bf-415f-a2c7-3e4dec740177

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGelfandTsetlinCanonicalFibre_canonicalGelfandTsetlinFibre_rotation_intertwine
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankGTProjectedLowerRange_euclideanAmbientRotation_castSucc_last
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankGTAxisTensorRotationIntertwining_euclideanAmbientRotation_castSucc_last

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
noncomputable section
set_option autoImplicit false
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherYoungAllRankGTAxisTensorRotationIntertwining
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankZeroRowRotationEquivariance
open MetricCodes.Spherical.ThreeRowYoungBranching
namespace MetricCodes.Spherical.HigherYoungAllRankGTAxisTensorRotationIntertwining
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (a b : Fin n) :
    (canonicalGelfandTsetlinAxisTensor lam mu h hgram).comp
        (youngAmbientRotation mu a b) =
      (tensorAmbientRotation lam a.castSucc b.castSucc).comp
        (canonicalGelfandTsetlinAxisTensor lam mu h hgram) := by
  apply LinearMap.ext
  intro p
  simp only [LinearMap.comp_apply,
    canonicalGelfandTsetlinAxisTensor_apply,
    tensorAmbientRotation_tmul,
    euclideanAmbientRotation_castSucc_last,
    TensorProduct.zero_tmul, zero_add]
  congr 1
  exact LinearMap.congr_fun
    (canonicalGelfandTsetlinFibre_rotation_intertwine
      lam mu h hgram a b) p
end MetricCodes.Spherical.HigherYoungAllRankGTAxisTensorRotationIntertwining
