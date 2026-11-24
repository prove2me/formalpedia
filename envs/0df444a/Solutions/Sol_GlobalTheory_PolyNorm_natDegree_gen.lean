-- Prove2me | solution 1 for GlobalTheory.PolyNorm.natDegree_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:27:12.774566+00:00
-- url     : https://prove2.me/submissions/1c28c2dc-ddab-432b-9a82-2c47168702ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfNormResultantEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqProdOfMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.PolyNorm
namespace GlobalTheory.PolyNorm
theorem _root_.solution {r : ℕ} {K : Type} [CommRing K] (f : Fin (r + 1) → K) :
    (gen f).natDegree ≤ r := by
  unfold gen
  refine natDegree_sum_le_of_forall_le _ _ fun i _ => (natDegree_monomial_le _).trans ?_
  exact Nat.lt_succ_iff.mp i.2
end GlobalTheory.PolyNorm
