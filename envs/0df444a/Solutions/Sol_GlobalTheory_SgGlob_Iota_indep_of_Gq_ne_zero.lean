-- Prove2me | solution 1 for GlobalTheory.SgGlob.Iota.indep_of_Gq_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:21:12.81144+00:00
-- url     : https://prove2.me/submissions/a48f3867-bcbd-4de4-a822-fc32cf5b4d5f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_DiagMemCongruencePairs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndepOfGqNeZero
import Theorems.Thm_GlobalTheory_SgGlob_Iota_det_mul_last

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.SgGlob GlobalTheory.SgGlob.Iota
variable {E : Type} [Field E] [NumberField E]
variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}
omit [NumberField E]
namespace GlobalTheory.SgGlob.Iota
theorem _root_.solution (hσ : ∀ x, σ (σ x) = x) (hJ : cT σ J = J) {T T' : E}
    {Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E} {P P' : Matrix (Fin n) (Fin (r + 1)) E}
    (h : (P, P') ∈ XZ σ J T T' Z) (hG : Gq σ T T' Z ≠ 0) (a a' : Fin (r + 1) → E)
    (e : P *ᵥ a + P' *ᵥ a' = 0) : a = 0 ∧ a' = 0 := by
  obtain ⟨⟨⟨L, hL⟩, h1⟩, ⟨-, h2⟩, h3⟩ := h
  dsimp only at hL h1 h2 h3
  have h4 : pairM σ J P P' = cT σ Z := by
    rw [← h3, pairM, pairM]
    conv_rhs => rw [cT, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul]
    have : ((cT σ P).map σ)ᵀ = P := by
      ext i j
      simp [cT, hσ]
    rw [this, Matrix.mul_assoc]
    exact congrArg (fun M => cT σ P' * (M * P)) hJ.symm
  have e1 : TF r T *ᵥ a + Z *ᵥ a' = 0 := by
    rw [← h1, ← h3, pairM, pairM, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec a',
      ← Matrix.mulVec_add, e, Matrix.mulVec_zero]
  have e2 : TF r T' *ᵥ a' + cT σ Z *ᵥ a = 0 := by
    rw [← h2, ← h4, pairM, pairM, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec a,
      ← Matrix.mulVec_add, add_comm (P' *ᵥ a'), e, Matrix.mulVec_zero]
  have d1 := det_mul_last e1
  have d2 := det_mul_last e2
  have c1 : (cT σ Z).det = σ Z.det := by rw [cT, Matrix.det_transpose, RingHom.map_det]; rfl
  have c2 : lead (cT σ Z) r (Nat.le_succ r) = σ (lead Z r (Nat.le_succ r)) := by
    rw [lead, lead, RingHom.map_det, ← Matrix.det_transpose]
    rfl
  rw [c1, c2] at d2
  have l1 : a (Fin.last r) = 0 := (mul_eq_zero.1 (by
    rw [Gq]
    linear_combination Z.det * d2 + T' * σ (lead Z r (Nat.le_succ r)) * d1)).resolve_left hG
  have l2 : a' (Fin.last r) = 0 := (mul_eq_zero.1 (by
    rw [Gq]
    linear_combination σ Z.det * d1 + T * lead Z r (Nat.le_succ r) * d2)).resolve_left hG
  have z : Z *ᵥ a' = 0 := by
    rw [← e1, right_eq_add]
    ext i
    by_cases hi : i = Fin.last r <;> simp [TF, Matrix.mulVec_diagonal, hi, l1]
  have ha' : a' = 0 := by
    by_cases hd : Z.det = 0
    · have hl : lead Z r (Nat.le_succ r) ≠ 0 := fun h0 => hG (by simp [Gq, hd, h0])
      have := Matrix.eq_zero_of_mulVec_eq_zero hl (v := fun i => a' i.castSucc) (by
        ext i
        have := congrFun z i.castSucc
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, l2, mul_zero, add_zero] at this
        exact this)
      ext i
      induction i using Fin.lastCases with
      | last => exact l2
      | cast i => exact congrFun this i
    · exact Matrix.eq_zero_of_mulVec_eq_zero hd z
  refine ⟨?_, ha'⟩
  rw [ha', Matrix.mulVec_zero, add_zero] at e
  rw [← Matrix.one_mulVec a, ← hL, ← Matrix.mulVec_mulVec, e, Matrix.mulVec_zero]
end GlobalTheory.SgGlob.Iota
