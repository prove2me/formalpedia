-- Prove2me | solution 1 for GlobalTheory.CofactorOrder.exists_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:27.706796+00:00
-- url     : https://prove2.me/submissions/1c7ae789-64a5-42a5-a584-f37ce4e1710d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsNotXPowDvdAdjugateOfFirstOrderKernel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
open GlobalTheory
open GlobalTheory.CofactorOrder
variable {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.CofactorOrder
theorem _root_.solution (M : Matrix n n K) :
    ∃ (P Q : Matrix n n K) (D : n → K), P.det = 1 ∧ Q.det = 1 ∧ P * M * Q = diagonal D := by
  obtain ⟨L, L', D, hL⟩ := Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal M
  have hdet : ∀ T : List (TransvectionStruct n K),
      (T.map TransvectionStruct.toMatrix).prod.det = 1 := by
    intro T
    induction T with
    | nil => simp
    | cons t T ih => rw [List.map_cons, List.prod_cons, det_mul, ih, TransvectionStruct.det, one_mul]
  exact ⟨_, _, D, hdet L, hdet L', hL⟩
end GlobalTheory.CofactorOrder
