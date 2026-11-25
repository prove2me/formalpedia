-- Prove2me | solution 1 for GlobalTheory.T.multipliable_local_factors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:08:24.41796+00:00
-- url     : https://prove2.me/submissions/108c0dc0-c82f-4819-b9c6-9cf112cdf1b1

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultipliableLocalFactors
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TruncSum
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultipliableLocalFactorsStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Mass_MeanV_multipliable_localFactors


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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (C : ℝ) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ), (∀ v, v ∉ S → ∀ s : Fv F v, Valued.v s = 1 → |g v s - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) → ∀ β : F, β ≠ 0 → Multipliable fun v => g v (algebraMap F (Fv F v) β) := by
  first | exact @GlobalTheory.CompanionTheory.Mass.MeanV.multipliable_localFactors | exact GlobalTheory.CompanionTheory.Mass.MeanV.multipliable_localFactors | (intros; apply GlobalTheory.CompanionTheory.Mass.MeanV.multipliable_localFactors <;> assumption)
end _root_.GlobalTheory.T
