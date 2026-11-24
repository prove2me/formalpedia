-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SubsetSum.gen_monic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:40:22.878324+00:00
-- url     : https://prove2.me/submissions/94a56e52-6c53-43ce-bc74-fbe758088e70

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
theorem _root_.solution {S : Type*} [CommRing S] (d : ℕ) (c : Fin d → S) : (gen d c).Monic :=
  monic_X_pow_add (degree_sum_fin_lt c)
end GlobalTheory.CompanionTheory.SubsetSum
