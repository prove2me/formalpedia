-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SubsetSum.eval_subsetPoly
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:26:04.236367+00:00
-- url     : https://prove2.me/submissions/bb3bdc90-ac22-4dfd-bcca-55e80cf49c75

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
theorem _root_.solution {R : Type*} [CommRing R] (r : ℕ) (M : Multiset R) (a : R) :
    (subsetPoly r M).eval a = ((M.powersetCard r).map fun S => a - S.sum).prod := by
  unfold subsetPoly
  rw [Polynomial.eval_multiset_prod, Multiset.map_map]
  simp
end GlobalTheory.CompanionTheory.SubsetSum
