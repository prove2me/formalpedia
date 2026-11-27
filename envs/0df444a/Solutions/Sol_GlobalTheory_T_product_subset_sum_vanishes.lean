-- Prove2me | solution 1 for GlobalTheory.T.product_subset_sum_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:33:29.63861+00:00
-- url     : https://prove2.me/submissions/0662c220-46c4-46b4-9381-b61ab3d8c1d3

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSubsetSumVanishes
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSubsetSumVanishesStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SubsetSum_prod_sub_subset_sum_eq_zero_complex


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] [Algebra ℂ R] (r : ℕ) (m : Multiset ℂ) (A B : R[X]), 0 < r → A.Monic → B.Monic → A.natDegree = r →
  A * B = (m.map fun x => X + C (algebraMap ℂ R x)).prod →
  ((m.powersetCard r).map fun S => A.coeff (r - 1) - algebraMap ℂ R S.sum).prod = 0 := by
  first | exact @GlobalTheory.CompanionTheory.SubsetSum.prod_sub_subset_sum_eq_zero_complex | exact GlobalTheory.CompanionTheory.SubsetSum.prod_sub_subset_sum_eq_zero_complex | (intros; apply GlobalTheory.CompanionTheory.SubsetSum.prod_sub_subset_sum_eq_zero_complex <;> assumption)
end _root_.GlobalTheory.T
