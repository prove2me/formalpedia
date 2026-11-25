-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SubsetSum.prod_sub_subset_sum_eq_zero_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:09:52.976821+00:00
-- url     : https://prove2.me/submissions/a23da04d-aad8-4968-b366-6609026e9b7a

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSubsetSumVanishes
import Theorems.Thm_GlobalTheory_CompanionTheory_SubsetSum_prod_sub_subset_sum_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SubsetSum
namespace GlobalTheory.CompanionTheory.SubsetSum
theorem _root_.solution (R : Type) [CommRing R] [Algebra ℂ R] (r : ℕ)
    (m : Multiset ℂ) (A B : R[X]) (hr : 0 < r) (hA : A.Monic) (hB : B.Monic)
    (hd : A.natDegree = r)
    (h : A * B = (m.map fun x => X + C (algebraMap ℂ R x)).prod) :
    ((m.powersetCard r).map fun S => A.coeff (r - 1) - algebraMap ℂ R S.sum).prod = 0 := by
  have key := prod_sub_subset_sum_eq_zero R r (m.map (algebraMap ℂ R)) A B hr hA hB hd
    (by rw [Multiset.map_map]; exact h)
  rw [Multiset.powersetCard_map, Multiset.map_map] at key
  rw [← key]
  congr 1
  apply Multiset.map_congr rfl
  intro S _
  simp [map_multiset_sum]
end GlobalTheory.CompanionTheory.SubsetSum
