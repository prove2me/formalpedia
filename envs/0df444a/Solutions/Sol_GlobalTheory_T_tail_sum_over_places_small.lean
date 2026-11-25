-- Prove2me | solution 1 for GlobalTheory.T.tail_sum_over_places_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:10:34.181409+00:00
-- url     : https://prove2.me/submissions/84d4cd83-ff2d-4cbf-9329-37a4034fa3a8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TailSumOverPlacesSmall
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TruncSum
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TailSumOverPlacesSmallStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Mass_MeanV_tail_sum_finset_prod_two_mul_div_sq


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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (C : ℝ), 0 ≤ C → ∀ η : ℝ, 0 < η → ∃ T₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ T, T₀ ⊆ T → ∀ U : Finset (HeightOneSpectrum (𝓞 F)), ∑ D ∈ U.powerset with ¬ D ⊆ T, ∏ v ∈ D, (2 * C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) ≤ η := by
  first | exact @GlobalTheory.CompanionTheory.Mass.MeanV.tail_sum_finset_prod_two_mul_div_sq | exact GlobalTheory.CompanionTheory.Mass.MeanV.tail_sum_finset_prod_two_mul_div_sq | (intros; apply GlobalTheory.CompanionTheory.Mass.MeanV.tail_sum_finset_prod_two_mul_div_sq <;> assumption)
end _root_.GlobalTheory.T
