-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SubsetSum.exists_roots_of_monic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:40:21.140561+00:00
-- url     : https://prove2.me/submissions/762e653d-26a7-4e04-b398-7a16abde743f

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
theorem _root_.solution {K : Type*} [Field K] [IsAlgClosed K] (P : K[X]) (hP : P.Monic) :
    ∃ α : Multiset K, P = (α.map fun x => X + C x).prod := by
  refine ⟨P.roots.map Neg.neg, ?_⟩
  conv_lhs => rw [(IsAlgClosed.splits P).eq_prod_roots_of_monic hP]
  rw [Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro x _
  simp [sub_eq_add_neg]
end GlobalTheory.CompanionTheory.SubsetSum
