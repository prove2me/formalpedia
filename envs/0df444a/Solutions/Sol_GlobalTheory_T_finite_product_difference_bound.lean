-- Prove2me | solution 1 for GlobalTheory.T.finite_product_difference_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:09:39.152805+00:00
-- url     : https://prove2.me/submissions/23db4e22-9770-43ee-ade1-5b3f3ee98be4

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteProductDifferenceBound
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TruncSum
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteProductDifferenceBoundStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Mass_MeanV_abs_prod_sub_prod_le_sum_powerset


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
theorem _root_.solution : ∀ (V : Type) (a : V → ℝ) (A U : Finset V), A ⊆ U → |∏ v ∈ U, a v - ∏ v ∈ A, a v| ≤ ∑ D ∈ U.powerset with ¬ D ⊆ A, ∏ v ∈ D, |a v - 1| := by
  first | exact @GlobalTheory.CompanionTheory.Mass.MeanV.abs_prod_sub_prod_le_sum_powerset | exact GlobalTheory.CompanionTheory.Mass.MeanV.abs_prod_sub_prod_le_sum_powerset | (intros; apply GlobalTheory.CompanionTheory.Mass.MeanV.abs_prod_sub_prod_le_sum_powerset <;> assumption)
end _root_.GlobalTheory.T
