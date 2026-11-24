-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SubsetSum.eq_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:40:18.301963+00:00
-- url     : https://prove2.me/submissions/8ce43e5f-e9b8-4689-8d2a-f483c30a9632

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
theorem _root_.solution {T : Type*} [CommRing T] (P : T[X]) (hP : P.Monic) (d : ℕ) (hd : P.natDegree = d) :
    P = gen d (fun i => P.coeff i) := by
  subst hd
  conv_lhs => rw [hP.as_sum]
  rw [gen, Fin.sum_univ_eq_sum_range (fun i => C (P.coeff i) * X ^ i)]
end GlobalTheory.CompanionTheory.SubsetSum
