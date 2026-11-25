-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Mass.MeanV.meanVal_of_equi_countBd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:46:55.908931+00:00
-- url     : https://prove2.me/submissions/df7816c5-de02-494e-83f3-ceb4862cc6ac

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_BinaryMassMeans_MeanVal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TsumNeZeroEqSum
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsIntegralMultipleBoundedPlacesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteProductDifferenceBoundStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TailSumOverPlacesSmallStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultipliableLocalFactorsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalFactorSandwichApproxStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EulerProductConvergenceBoundStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TruncatedSumLimitStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalHaarMeasureSingletonStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MeanValueFormula
import Theorems.Thm_GlobalTheory_CompanionTheory_Mass_MeanV_truncSum_tendsto
import Theorems.Thm_GlobalTheory_CompanionTheory_Mass_MeanV_err_bound
import Theorems.Thm_GlobalTheory_CompanionTheory_Mass_MeanV_ofReal_fullSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Mass GlobalTheory.CompanionTheory.Mass.MeanV
namespace GlobalTheory.CompanionTheory.Mass.MeanV
theorem _root_.solution : Equi → CountBd → MeanVal := by
  intro hE hC F _ _ hF θ hθ li lam hli hlam S G g C hG hGc hG0 hg0 hgS hgo
  have hq : ∀ v : HeightOneSpectrum (𝓞 F), (0 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := fun v => Nat.cast_nonneg _
  have hb1 : ∀ v, v ∉ S → ∀ s ∈ v.adicCompletionIntegers F, s ≠ 0 →
      |g v s - 1| ≤ |C| / (Ideal.absNorm v.asIdeal : ℝ) := fun v hv s hs h0 =>
    ((hgo v hv).2.2.1 s hs h0).trans (div_le_div_of_nonneg_right (le_abs_self C) (hq v))
  have hb2 : ∀ v, v ∉ S → ∀ s : Fv F v, Valued.v s = 1 →
      |g v s - 1| ≤ |C| / (Ideal.absNorm v.asIdeal : ℝ) ^ 2 := fun v hv s hs =>
    ((hgo v hv).2.2.2.1 s hs).trans (div_le_div_of_nonneg_right (le_abs_self C) (pow_nonneg (hq v) 2))
  have hz : ∀ v, v ∉ S → ∀ s, s ∉ v.adicCompletionIntegers F → g v s = 0 := fun v hv => (hgo v hv).2.1
  have hgood : ∀ v, v ∉ S → GoodFac v (lam v) C (g v) := fun v hv => hgo v hv
  have hR : Tendsto (fullSum θ G g) (𝓝[>] 0) (𝓝 ((∫ y, G y ∂li) * ∏ v ∈ S, ∫ s, g v s ∂(lam v))) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨T, hST, hT⟩ := err_bound hC F hF θ hθ S G g |C| (abs_nonneg C) hG hGc hG0 hg0 hgS hz hb1 hb2
      (half_pos hε)
    have htr := truncSum_tendsto hE hC F hF θ hθ li lam hli hlam S G g C hG hGc hG0 hg0 hgS hgood T hST
    filter_upwards [Metric.tendsto_nhds.1 htr (ε / 2) (half_pos hε), self_mem_nhdsWithin] with δ h1 h2
    have h3 := hT T subset_rfl δ h2
    rw [Real.dist_eq] at h1 ⊢
    have h4 := abs_sub_le (fullSum θ G g δ) (truncSum θ G T g δ)
      ((∫ y, G y ∂li) * ∏ v ∈ S, ∫ s, g v s ∂(lam v))
    linarith
  have hL := (ENNReal.continuous_ofReal.tendsto _).comp hR
  refine hL.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (ofReal_fullSum hC F hF θ hθ S G g |C| hGc hG0 hg0 hgS hz hb2 δ hδ).symm
end GlobalTheory.CompanionTheory.Mass.MeanV
