-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.le_rank_iff_exists_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:43:51.082144+00:00
-- url     : https://prove2.me/submissions/2aecab94-4478-4661-a285-10cc084df876

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {m : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix m m F) (k : ℕ) :
    k ≤ M.rank ↔ ∃ (A : Matrix (Fin k) m F) (B : Matrix m (Fin k) F), (A * M * B).det ≠ 0 := by
  constructor
  · intro hk
    obtain ⟨V, U, e, -, -, hVU⟩ := exists_rank_normal_form M
    let f : Fin k → m := fun a => e.symm (Sum.inl (Fin.castLE hk a))
    refine ⟨V.submatrix f id, U.submatrix id f, ?_⟩
    have h1 : V.submatrix f id * M * U.submatrix id f = (V * M * U).submatrix f f := by
      rw [submatrix_mul _ _ f id f Function.bijective_id,
        submatrix_mul _ _ f id id Function.bijective_id, submatrix_id_id]
    have h2 : (V * M * U).submatrix f f = 1 := by
      rw [hVU, submatrix_submatrix]
      ext a b
      simp [f, Matrix.one_apply, Fin.castLE_inj]
    rw [h1, h2, det_one]
    exact one_ne_zero
  · rintro ⟨A, B, hAB⟩
    have h := rank_of_det_ne_zero hAB
    rw [Fintype.card_fin] at h
    calc k = (A * M * B).rank := h.symm
      _ ≤ (A * M).rank := rank_mul_le_left _ _
      _ ≤ M.rank := rank_mul_le_right _ _
end GroundTheory.Automorphic.Whittaker
