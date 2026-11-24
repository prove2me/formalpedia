-- Prove2me | solution 1 for GlobalTheory.det_updateRow_alternating_mulVec_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:44:48.040054+00:00
-- url     : https://prove2.me/submissions/9a292a02-7400-4982-94c5-cd08cede4ad1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DetUpdateRowAlternatingMulVecMem
import Theorems.Thm_GlobalTheory_det_updateRow_single_mul_sub_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {T : Type} [CommRing T] {g : ℕ} (x : Fin g → T)
    (I : Ideal T) (m : Matrix (Fin g) (Fin g) T) (p : Fin g)
    (hm : ∀ q, q ≠ p → m.mulVec x q ∈ I) (s : Matrix (Fin g) (Fin g) T)
    (hs : s.transpose = -s) (hd : ∀ i, s i i = 0) :
    (m.updateRow p (s.mulVec x)).det ∈ I := by
  have h1 : (m.updateRow p (s.mulVec x)).det
      = ∑ ij : Fin g × Fin g,
          s ij.1 ij.2 * (x ij.2 * (m.updateRow p (Pi.single ij.1 1)).det) := by
    have e : ∀ v : Fin g → T, (m.updateRow p v).det
        = ∑ i, v i * (m.updateRow p (Pi.single i 1)).det := by
      intro v
      have := Matrix.cramer_transpose_apply m v p
      rw [← this, Matrix.cramer_eq_adjugate_mulVec]
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Matrix.adjugate_transpose, Matrix.transpose_apply, Matrix.adjugate_apply, mul_comm]
    rw [e, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]
  rw [h1, ← Ideal.Quotient.eq_zero_iff_mem, map_sum]
  refine Finset.sum_ninvolution Prod.swap ?_ ?_ (fun _ => Finset.mem_univ _) Prod.swap_swap
  · rintro ⟨i, j⟩
    rw [← map_add, Ideal.Quotient.eq_zero_iff_mem]
    have hji : s j i = - s i j := by
      have := congrFun (congrFun hs i) j
      simpa using this
    have := I.mul_mem_left (s i j) (det_updateRow_single_mul_sub_mem x I m p hm i j)
    convert this using 1
    simp only [Prod.fst_swap, Prod.snd_swap, hji]
    ring
  · rintro ⟨i, j⟩ h e
    apply h
    have : j = i := congrArg Prod.fst e
    subst this
    simp [hd]
end GlobalTheory
