-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SubsetSum.gen_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:49:21.775741+00:00
-- url     : https://prove2.me/submissions/32c585ed-9900-4cdb-b8bb-ef4f4631a48d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSubsetSumVanishes

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
theorem _root_.solution {S : Type*} [CommRing S] [Nontrivial S] (d : ℕ) (c : Fin d → S) :
    (gen d c).natDegree = d := by
  rw [gen, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]
  exact degree_sum_fin_lt c
end GlobalTheory.CompanionTheory.SubsetSum
