-- Prove2me | solution 1 for GlobalTheory.NonzeroIsotropic.quadForm_totalDegree_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:14:48.896798+00:00
-- url     : https://prove2.me/submissions/ddcf8539-90af-49b0-93b5-33e043851e48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsNonzeroIsotropic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open GlobalTheory GlobalTheory.NonzeroIsotropic
open MvPolynomial
namespace GlobalTheory.NonzeroIsotropic
theorem _root_.solution {k : Type u_1} [Field k] (a : Fin 3 → Fin 3 → k) :
    (∑ i : Fin 3, ∑ j : Fin 3, C (a i j) * X i * X j : MvPolynomial (Fin 3) k).totalDegree ≤ 2 := by
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => ?_)
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
  calc (C (a i j) * X i * X j : MvPolynomial (Fin 3) k).totalDegree
      ≤ (C (a i j) * X i : MvPolynomial (Fin 3) k).totalDegree + (X j : MvPolynomial (Fin 3) k).totalDegree :=
        totalDegree_mul _ _
    _ ≤ ((C (a i j) : MvPolynomial (Fin 3) k).totalDegree + (X i : MvPolynomial (Fin 3) k).totalDegree)
          + (X j : MvPolynomial (Fin 3) k).totalDegree := by gcongr; exact totalDegree_mul _ _
    _ = 2 := by simp [totalDegree_C, totalDegree_X]
end GlobalTheory.NonzeroIsotropic
