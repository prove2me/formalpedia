-- Prove2me | solution 1 for GlobalTheory.TriangularityLowCoeff.degree_expOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:38:58.817044+00:00
-- url     : https://prove2.me/submissions/0b10a84f-431b-471d-b782-d1318fd48770

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoeffAnnihilatedOfAevalMemKerPow
import Theorems.Thm_GlobalTheory_TriangularityLowCoeff_expOf_cons

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
theorem _root_.solution {d : ℕ} (L : List (Fin d)) : (expOf L).degree = L.length := by
  induction L with
  | nil => simp [expOf]
  | cons i L ih => rw [expOf_cons, map_add, ih, Finsupp.degree_single]; simp; omega
end GlobalTheory.TriangularityLowCoeff
