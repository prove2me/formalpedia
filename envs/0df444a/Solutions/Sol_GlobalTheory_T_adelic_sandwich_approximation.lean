-- Prove2me | solution 1 for GlobalTheory.T.adelic_sandwich_approximation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:27:26.206969+00:00
-- url     : https://prove2.me/submissions/1f0d0ac8-603a-4053-b7ba-42d3f308bbe4

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TruncatedSumLimit
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TsumNeZeroEqSum
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TruncatedSumLimitStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Mass_MeanV_tendsto_truncSum


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : Equi → CountBd → ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ (li : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf li → (∀ v, IsStdV v (lam v)) → ∀ (T : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ) (ψ : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ), Continuous G → HasCompactSupport G → (∀ v ∈ T, Continuous (ψ v) ∧ HasCompactSupport (ψ v)) → Tendsto (truncSum θ G T ψ) (𝓝[>] 0) (𝓝 ((∫ y, G y ∂li) * ∏ v ∈ T, ∫ s, ψ v s ∂(lam v))) := by
  first | exact @GlobalTheory.CompanionTheory.Mass.MeanV.tendsto_truncSum | exact GlobalTheory.CompanionTheory.Mass.MeanV.tendsto_truncSum | (intros; apply GlobalTheory.CompanionTheory.Mass.MeanV.tendsto_truncSum <;> assumption)
end _root_.GlobalTheory.T
