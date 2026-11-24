-- Prove2me | solution 1 for GlobalTheory.eigDim_rank_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:36:04.684447+00:00
-- url     : https://prove2.me/submissions/682af236-4dbb-41f8-92b4-730b11d91b26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankKerAevalEqNatDegreeMulFinrankEigenspaceAl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Polynomial
namespace GlobalTheory
private lemma rank_submatrix_fromBlocks_one_zero_eq {F : Type} [Field F] {m : Type} [Fintype m] [DecidableEq m]
    (a b : ℕ) (e : m ≃ Fin a ⊕ Fin b) :
    ((Matrix.fromBlocks (1 : Matrix (Fin a) (Fin a) F) 0 0 (0 : Matrix (Fin b) (Fin b) F)).submatrix
      e e).rank = a := by
  classical
  have hd : (Matrix.fromBlocks (1 : Matrix (Fin a) (Fin a) F) 0 0 (0 : Matrix (Fin b) (Fin b) F)) =
      Matrix.diagonal (Sum.elim (fun _ => (1 : F)) (fun _ => 0)) := by
    rw [← Matrix.fromBlocks_diagonal]
    simp
  rw [Matrix.rank_submatrix, hd, Matrix.rank_diagonal]
  simp [Fintype.card_subtype, Finset.card_filter, Fintype.sum_sum_type]
end GlobalTheory
end

set_option autoImplicit false
open Polynomial
open GlobalTheory
open Matrix
namespace GlobalTheory
theorem _root_.solution {K L : Type} [Field K] [Field L] (φ : K →+* L) {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n K) : (M.map φ).rank = M.rank := by
  classical
  obtain ⟨V, U, e, hV, hU, h⟩ := Matrix.exists_rank_normal_form M
  have hVd : IsUnit (V.map φ).det := by
    rw [show (V.map φ).det = φ V.det from (RingHom.map_det φ V).symm]
    exact ((Matrix.isUnit_iff_isUnit_det V).mp hV).map φ
  have hUd : IsUnit (U.map φ).det := by
    rw [show (U.map φ).det = φ U.det from (RingHom.map_det φ U).symm]
    exact ((Matrix.isUnit_iff_isUnit_det U).mp hU).map φ
  have h' : V.map φ * M.map φ * U.map φ =
      (Matrix.fromBlocks (1 : Matrix (Fin M.rank) (Fin M.rank) L) 0 0
        (0 : Matrix (Fin (Fintype.card n - M.rank)) (Fin (Fintype.card n - M.rank)) L)).submatrix
          e e := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, h]
    simp [← Matrix.submatrix_map, Matrix.fromBlocks_map]
  calc (M.map φ).rank = (V.map φ * M.map φ * U.map φ).rank := by
        rw [rank_mul_eq_left_of_isUnit_det _ _ hUd, rank_mul_eq_right_of_isUnit_det _ _ hVd]
    _ = M.rank := by rw [h']; exact rank_submatrix_fromBlocks_one_zero_eq _ _ e
end GlobalTheory
