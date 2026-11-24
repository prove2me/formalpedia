-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SubsetSum.esymm_one_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:40:18.939194+00:00
-- url     : https://prove2.me/submissions/7c3c29b1-fda9-47dd-a67f-e2de48da7a7d

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
theorem _root_.solution {R : Type*} [CommRing R] (M : Multiset R) : M.esymm 1 = M.sum := by
  simp [Multiset.esymm, Multiset.powersetCard_one, Multiset.map_map]
end GlobalTheory.CompanionTheory.SubsetSum
