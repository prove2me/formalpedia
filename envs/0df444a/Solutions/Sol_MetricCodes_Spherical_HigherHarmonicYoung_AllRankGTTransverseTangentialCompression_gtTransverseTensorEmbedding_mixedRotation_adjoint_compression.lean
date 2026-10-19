-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTangentialCompression.gtTransverseTensorEmbedding_mixedRotation_adjoint_compression
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:47.506255+00:00
-- url     : https://prove2.me/submissions/6f796192-6415-4cf8-9c61-5bd3a26f520b

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseTangentialCompression_gtTransverseTensorEmbedding_tangentialTerm_adjoint_compression
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseTangentialCompression_gtTransverseTensorEmbedding_crossTerm_adjoint_compression
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseTangentialCompression_gtTransverseTensorEmbedding_crossTerm_adjoint_compression_swap
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseTangentialCompression_gtTransverseTensorEmbedding_lastTerm_adjoint_compression

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
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 500000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTangentialCompression
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirPureAxis
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTangentialCompression
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (nu : Fin (r + 1) → ℕ) (h : Interlaces lam nu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam nu h) :
    (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap.adjoint.comp
        ((gtMixedRotationOperator (n := n + 1) lam).comp
          (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap) =
      gtMixedRotationOperator (n := n) nu := by
  unfold gtMixedRotationOperator
  apply TensorProduct.ext'
  intro v p
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  rw [Fin.sum_univ_castSucc]
  simp_rw [Fin.sum_univ_castSucc]
  have htangential (a b : Fin n) := LinearMap.congr_fun
    (gtTransverseTensorEmbedding_tangentialTerm_adjoint_compression
      lam nu h hgram a b) (v ⊗ₜ[ℝ] p)
  have hcross (a : Fin n) := LinearMap.congr_fun
    (gtTransverseTensorEmbedding_crossTerm_adjoint_compression
      lam nu h hgram a) (v ⊗ₜ[ℝ] p)
  have hcrossSwap (a : Fin n) := LinearMap.congr_fun
    (gtTransverseTensorEmbedding_crossTerm_adjoint_compression_swap
      lam nu h hgram a) (v ⊗ₜ[ℝ] p)
  have hlast := LinearMap.congr_fun
    (gtTransverseTensorEmbedding_lastTerm_adjoint_compression
      lam nu h hgram) (v ⊗ₜ[ℝ] p)
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at htangential hcross hcrossSwap hlast
  simp only [htangential, hcross, hcrossSwap, hlast,
    Finset.sum_const_zero, add_zero]
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTangentialCompression
