-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseRotationIntertwining.gtTransverseTensorEmbedding_rotation_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:48.515695+00:00
-- url     : https://prove2.me/submissions/1afb2e01-7ba4-4757-9783-b585e5bd9841

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGelfandTsetlinCanonicalFibre_canonicalGelfandTsetlinFibre_rotation_intertwine
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseTangentialCompression_gtTransverseEuclideanIsometry_rotation_intertwine

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
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseRotationIntertwining
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTangentialCompression
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWignerEckartPhase
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseRotationIntertwining
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (nu : Fin (r + 1) → ℕ) (h : Interlaces lam nu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam nu h)
    (a b : Fin n) :
    (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap.comp
        (tensorAmbientRotation nu a b) =
      (tensorAmbientRotation lam a.castSucc b.castSucc).comp
        (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul v p =>
      have hE := LinearMap.congr_fun
        (gtTransverseEuclideanIsometry_rotation_intertwine n a b) v
      have hF := LinearMap.congr_fun
        (canonicalGelfandTsetlinFibre_rotation_intertwine
          lam nu h hgram a b) p
      change
        gtTransverseEuclideanIsometry n (euclideanAmbientRotation a b v) =
          euclideanAmbientRotation a.castSucc b.castSucc
            (gtTransverseEuclideanIsometry n v) at hE
      change
        canonicalGelfandTsetlinFibre lam nu h hgram
            (youngAmbientRotation nu a b p) =
          youngAmbientRotation lam a.castSucc b.castSucc
            (canonicalGelfandTsetlinFibre lam nu h hgram p) at hF
      change
        gtTransverseEuclideanIsometry n
            (euclideanAmbientRotation a b v) ⊗ₜ[ℝ]
          canonicalGelfandTsetlinFibre lam nu h hgram p +
        gtTransverseEuclideanIsometry n v ⊗ₜ[ℝ]
          canonicalGelfandTsetlinFibre lam nu h hgram
            (youngAmbientRotation nu a b p) =
        euclideanAmbientRotation a.castSucc b.castSucc
            (gtTransverseEuclideanIsometry n v) ⊗ₜ[ℝ]
          canonicalGelfandTsetlinFibre lam nu h hgram p +
        gtTransverseEuclideanIsometry n v ⊗ₜ[ℝ]
          youngAmbientRotation lam a.castSucc b.castSucc
            (canonicalGelfandTsetlinFibre lam nu h hgram p)
      rw [hE, hF]
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseRotationIntertwining
