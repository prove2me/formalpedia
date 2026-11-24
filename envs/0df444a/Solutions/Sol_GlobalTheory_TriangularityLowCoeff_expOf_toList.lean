-- Prove2me | solution 1 for GlobalTheory.TriangularityLowCoeff.expOf_toList
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:39:04.692701+00:00
-- url     : https://prove2.me/submissions/d7a2434b-5942-4270-94af-b871faa011a6

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
theorem _root_.solution {d : ℕ} (α : Fin d →₀ ℕ) : expOf (Finsupp.toMultiset α).toList = α := by
  rw [expOf, Multiset.coe_toList, Finsupp.toMultiset_toFinsupp]
end GlobalTheory.TriangularityLowCoeff
