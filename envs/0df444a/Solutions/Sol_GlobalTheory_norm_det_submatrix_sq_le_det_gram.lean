-- Prove2me | solution 1 for GlobalTheory.norm_det_submatrix_sq_le_det_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:26:57.934449+00:00
-- url     : https://prove2.me/submissions/7ec60cfe-ec01-4ee4-870b-f53daf54f95b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsDetAddEqDetMulDetOneAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_NormDetSubmatrixSqLeDetGram
import Theorems.Thm_GlobalTheory_det_re_mono_of_posSemidef


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (m : Type) [Fintype m] (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix m ι ℂ)
      (e : ι → m), Function.Injective e →
        ‖(M.submatrix e id).det‖ ^ 2 ≤ (Mᴴ * M).det.re := by
  classical
  intro m _ ι _ _ M e he
  set N : Matrix ι ι ℂ := M.submatrix e id with hN
  set s : Finset m := Finset.univ.map ⟨e, he⟩ with hs
  let B : Matrix (sᶜ : Finset m) ι ℂ := fun i j => M i j
  have hsplit : Mᴴ * M = Nᴴ * N + Bᴴ * B := by
    ext j k
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.add_apply]
    rw [← Finset.sum_add_sum_compl s]
    congr 1
    · rw [hs, Finset.sum_map]
      rfl
    · rw [← Finset.sum_coe_sort sᶜ]
  have hN1 : (Nᴴ * N).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self N
  have hB1 : (Bᴴ * B).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self B
  have key := (det_re_mono_of_posSemidef ι (Nᴴ * N) (Bᴴ * B) hN1 hB1).2.1
  rw [hsplit]
  refine le_trans (le_of_eq ?_) key
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def, Complex.conj_mul']
  norm_cast
end GlobalTheory
