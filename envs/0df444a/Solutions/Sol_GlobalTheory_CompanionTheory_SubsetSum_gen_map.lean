-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SubsetSum.gen_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:40:22.090737+00:00
-- url     : https://prove2.me/submissions/05787b94-0598-48a1-a01a-acb794ac01fd

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
theorem _root_.solution {S T : Type*} [CommRing S] [CommRing T] (f : S →+* T) (d : ℕ) (c : Fin d → S) :
    (gen d c).map f = gen d (fun i => f (c i)) := by
  simp [gen, Polynomial.map_sum]
end GlobalTheory.CompanionTheory.SubsetSum
