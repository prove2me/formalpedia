-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SubsetSum.natDegree_prod_X_add_C
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:29:19.038577+00:00
-- url     : https://prove2.me/submissions/09037b0c-a0d0-417f-9799-fd6a419658b4

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
theorem _root_.solution {R : Type*} [CommRing R] [Nontrivial R] (M : Multiset R) :
    ((M.map fun x => X + C x).prod).natDegree = Multiset.card M := by
  have h : (M.map fun x => X + C x).prod = ((M.map Neg.neg).map fun x => X - C x).prod := by
    rw [Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro x _
    simp
  rw [h, natDegree_multiset_prod_X_sub_C_eq_card, Multiset.card_map]
end GlobalTheory.CompanionTheory.SubsetSum
