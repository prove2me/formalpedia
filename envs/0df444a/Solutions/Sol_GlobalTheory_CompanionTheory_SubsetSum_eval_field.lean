-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SubsetSum.eval_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:01:29.175866+00:00
-- url     : https://prove2.me/submissions/2b0dafdf-761c-4d27-8153-eac16835a1cd

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSubsetSumVanishes
import Theorems.Thm_GlobalTheory_CompanionTheory_SubsetSum_eval_subsetPoly
import Theorems.Thm_GlobalTheory_CompanionTheory_SubsetSum_natDegree_prod_X_add_C
import Theorems.Thm_GlobalTheory_CompanionTheory_SubsetSum_exists_roots_of_monic
import Theorems.Thm_GlobalTheory_CompanionTheory_SubsetSum_esymm_one_eq_sum

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
theorem _root_.solution {K : Type*} [Field K] [IsAlgClosed K] (r : ℕ) (hr : 0 < r) (P Q : K[X])
    (hP : P.Monic) (hQ : Q.Monic) (hd : P.natDegree = r) :
    ∃ M : Multiset K, Multiset.card M = r + Q.natDegree ∧
      P * Q = (M.map fun x => X + C x).prod ∧ (subsetPoly r M).eval (P.coeff (r - 1)) = 0 := by
  obtain ⟨α, hα⟩ := exists_roots_of_monic P hP
  obtain ⟨β, hβ⟩ := exists_roots_of_monic Q hQ
  have hαc : Multiset.card α = r := by rw [← hd, hα, natDegree_prod_X_add_C]
  have hβc : Multiset.card β = Q.natDegree := by rw [hβ, natDegree_prod_X_add_C]
  refine ⟨α + β, by rw [Multiset.card_add, hαc, hβc], ?_, ?_⟩
  · rw [Multiset.map_add, Multiset.prod_add, ← hα, ← hβ]
  · have hc : P.coeff (r - 1) = α.sum := by
      rw [hα, Multiset.prod_X_add_C_coeff _ (by omega), hαc, show r - (r - 1) = 1 by omega,
        esymm_one_eq_sum]
    rw [eval_subsetPoly, hc]
    apply Multiset.prod_eq_zero
    rw [Multiset.mem_map]
    exact ⟨α, Multiset.mem_powersetCard.2 ⟨Multiset.le_add_right _ _, hαc⟩, sub_self _⟩
end GlobalTheory.CompanionTheory.SubsetSum
