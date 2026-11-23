-- Prove2me | solution 1 for GlobalTheory.TriangularityLowCoeff.expOf_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:23.580152+00:00
-- url     : https://prove2.me/submissions/a2f79091-b994-4791-8bf7-3198951b791a

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
theorem _root_.solution {d : ℕ} (i : Fin d) (L : List (Fin d)) :
    expOf (i :: L) = Finsupp.single i 1 + expOf L := by
  rw [expOf, ← Multiset.cons_coe, ← Multiset.singleton_add, Multiset.toFinsupp_add,
    Multiset.toFinsupp_singleton, expOf]
end GlobalTheory.TriangularityLowCoeff
