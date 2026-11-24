-- Prove2me | solution 1 for GlobalTheory.TriangularityLowCoeff.expOf_apply_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:39:03.528931+00:00
-- url     : https://prove2.me/submissions/ba518b17-0ba0-405c-aa5c-b072b87b179f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoeffAnnihilatedOfAevalMemKerPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.TriangularityLowCoeff
open MvPolynomial
namespace GlobalTheory.TriangularityLowCoeff
theorem _root_.solution {d : ℕ} (L : List (Fin d)) (i : Fin d) : expOf L i ≤ L.length := by
  rw [expOf, Multiset.toFinsupp_apply, Multiset.coe_count]
  exact List.count_le_length
end GlobalTheory.TriangularityLowCoeff
