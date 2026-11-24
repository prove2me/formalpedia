-- Prove2me | solution 1 for GlobalTheory.UpqChar.char_Upq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:53:05.20497+00:00
-- url     : https://prove2.me/submissions/d2da9aa2-4d6b-4c58-8fd3-8d243ebde078

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupContinuousCharEqDetZpowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryPQContinuousCharacterEqDetPowProd
import Theorems.Thm_GlobalTheory_UpqChar_det_conj_rect
import Theorems.Thm_GlobalTheory_UpqChar_char_unitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix
open scoped ComplexOrder
namespace GlobalTheory.UpqChar
private theorem matrix_eq_zero_of_eq_neg {ι κ : Type} (X : Matrix ι κ ℂ) (h : X = -X) : X = 0 := by
  ext i j
  have h' := congrFun (congrFun h i) j
  simp only [Matrix.neg_apply] at h'
  simp only [Matrix.zero_apply]
  linear_combination h' / 2
end GlobalTheory.UpqChar
end

set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory GlobalTheory.UpqChar
namespace GlobalTheory.UpqChar
theorem _root_.solution : ∀ (n p q : ℕ) (G s : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin p ⊕ Fin q) ℂ) (B' : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ), B * B' = 1 → B' * B = 1 → Bᴴ * G * B = Matrix.fromBlocks 1 0 0 (-1) → s * B = B * Matrix.fromBlocks 1 0 0 (-1) → ∀ c : Matrix (Fin n) (Fin n) ℂ → ℂ, (∀ k k' : Matrix (Fin n) (Fin n) ℂ, kᴴ * G * k = G → s * k = k * s → k'ᴴ * G * k' = G → s * k' = k' * s → c (k * k') = c k * c k') → (∀ k : Matrix (Fin n) (Fin n) ℂ, kᴴ * G * k = G → s * k = k * s → ‖c k‖ = 1) → ContinuousOn c {k | kᴴ * G * k = G ∧ s * k = k * s} → ∃ x y : ℤ, ∀ k : Matrix (Fin n) (Fin n) ℂ, kᴴ * G * k = G → s * k = k * s → c k = ((1 / 2 : ℂ) • (1 + s) * k + (1 / 2 : ℂ) • (1 - s)).det ^ x * ((1 / 2 : ℂ) • (1 - s) * k + (1 / 2 : ℂ) • (1 + s)).det ^ y := by
  intro n p q G s B B' hBB' hB'B hG hs c hmul hnorm hcont
  classical
  obtain ⟨J, hJdef⟩ : ∃ J : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ, J = Matrix.fromBlocks 1 0 0 (-1) :=
    ⟨_, rfl⟩
  rw [← hJdef] at hG hs
  replace hs : s * B = B * J := hs
  replace hG : Bᴴ * G * B = J := hG
  replace hBB' : B * B' = 1 := hBB'
  replace hB'B : B' * B = 1 := hB'B
  have hconj : ∀ X Y : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ,
      (B * X * B') * (B * Y * B') = B * (X * Y) * B' := by
    intro X Y
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc B' B, hB'B, Matrix.one_mul]
  have hsJ : s = B * J * B' := by
    rw [← hs, Matrix.mul_assoc, hBB', Matrix.mul_one]
  have hGJ : G = B'ᴴ * J * B' := by
    rw [← hG]
    have h0 : (B * B')ᴴ = 1 := by rw [hBB', Matrix.conjTranspose_one]
    rw [Matrix.conjTranspose_mul] at h0
    calc G = (B'ᴴ * Bᴴ) * G * (B * B') := by rw [h0, hBB', Matrix.one_mul, Matrix.mul_one]
      _ = B'ᴴ * (Bᴴ * G * B) * B' := by simp only [Matrix.mul_assoc]
  have hK : ∀ (a : Matrix (Fin p) (Fin p) ℂ) (d : Matrix (Fin q) (Fin q) ℂ), aᴴ * a = 1 → dᴴ * d = 1 →
      (B * Matrix.fromBlocks a 0 0 d * B')ᴴ * G * (B * Matrix.fromBlocks a 0 0 d * B') = G ∧
      s * (B * Matrix.fromBlocks a 0 0 d * B') = (B * Matrix.fromBlocks a 0 0 d * B') * s := by
    intro a d ha hd
    constructor
    · have hm : (Matrix.fromBlocks a 0 0 d)ᴴ * J * Matrix.fromBlocks a 0 0 d = J := by
        rw [hJdef, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
        simp [ha, hd]
      calc (B * Matrix.fromBlocks a 0 0 d * B')ᴴ * G * (B * Matrix.fromBlocks a 0 0 d * B')
          = B'ᴴ * ((Matrix.fromBlocks a 0 0 d)ᴴ * (Bᴴ * G * B) * Matrix.fromBlocks a 0 0 d) * B' := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = G := by rw [hG, hm, ← hGJ]
    · rw [hsJ, hconj, hconj, hJdef, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
      simp
  let kA : Matrix.unitaryGroup (Fin p) ℂ → Matrix (Fin n) (Fin n) ℂ :=
    fun a => B * (Matrix.fromBlocks (a : Matrix (Fin p) (Fin p) ℂ) 0 0 1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B'
  let kD : Matrix.unitaryGroup (Fin q) ℂ → Matrix (Fin n) (Fin n) ℂ :=
    fun d => B * (Matrix.fromBlocks 1 0 0 (d : Matrix (Fin q) (Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B'
  have hKA : ∀ a : Matrix.unitaryGroup (Fin p) ℂ, (kA a)ᴴ * G * kA a = G ∧ s * kA a = kA a * s := by
    intro a
    refine hK _ _ ?_ (by simp)
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.1 a.2
  have hKD : ∀ d : Matrix.unitaryGroup (Fin q) ℂ, (kD d)ᴴ * G * kD d = G ∧ s * kD d = kD d * s := by
    intro d
    refine hK _ _ (by simp) ?_
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.1 d.2
  have hkAmul : ∀ a b : Matrix.unitaryGroup (Fin p) ℂ, kA (a * b) = kA a * kA b := by
    intro a b
    show B * (Matrix.fromBlocks ((a * b : Matrix.unitaryGroup (Fin p) ℂ) : Matrix (Fin p) (Fin p) ℂ) 0 0 1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B' =
      (B * (Matrix.fromBlocks (a : Matrix (Fin p) (Fin p) ℂ) 0 0 1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B') *
        (B * (Matrix.fromBlocks (b : Matrix (Fin p) (Fin p) ℂ) 0 0 1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B')
    rw [hconj, Matrix.fromBlocks_multiply]
    simp
  have hkDmul : ∀ a b : Matrix.unitaryGroup (Fin q) ℂ, kD (a * b) = kD a * kD b := by
    intro a b
    show B * (Matrix.fromBlocks 1 0 0 ((a * b : Matrix.unitaryGroup (Fin q) ℂ) : Matrix (Fin q) (Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B' =
      (B * (Matrix.fromBlocks 1 0 0 (a : Matrix (Fin q) (Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B') *
        (B * (Matrix.fromBlocks 1 0 0 (b : Matrix (Fin q) (Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B')
    rw [hconj, Matrix.fromBlocks_multiply]
    simp
  have hkAc : Continuous kA := by
    show Continuous (fun a : Matrix.unitaryGroup (Fin p) ℂ =>
      B * (Matrix.fromBlocks (a : Matrix (Fin p) (Fin p) ℂ) 0 0 1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B')
    fun_prop
  have hkDc : Continuous kD := by
    show Continuous (fun d : Matrix.unitaryGroup (Fin q) ℂ =>
      B * (Matrix.fromBlocks 1 0 0 (d : Matrix (Fin q) (Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B')
    fun_prop
  obtain ⟨x, hx⟩ := char_unitary (fun a => c (kA a))
    (fun a b => by
      show c (kA (a * b)) = c (kA a) * c (kA b)
      rw [hkAmul]
      exact hmul _ _ (hKA a).1 (hKA a).2 (hKA b).1 (hKA b).2)
    (fun a => hnorm _ (hKA a).1 (hKA a).2) (hcont.comp_continuous hkAc hKA)
  obtain ⟨y, hy⟩ := char_unitary (fun d => c (kD d))
    (fun a b => by
      show c (kD (a * b)) = c (kD a) * c (kD b)
      rw [hkDmul]
      exact hmul _ _ (hKD a).1 (hKD a).2 (hKD b).1 (hKD b).2)
    (fun d => hnorm _ (hKD d).1 (hKD d).2) (hcont.comp_continuous hkDc hKD)
  have hx' : ∀ a : Matrix.unitaryGroup (Fin p) ℂ, c (kA a) = (a : Matrix (Fin p) (Fin p) ℂ).det ^ x := hx
  have hy' : ∀ d : Matrix.unitaryGroup (Fin q) ℂ, c (kD d) = (d : Matrix (Fin q) (Fin q) ℂ).det ^ y := hy
  refine ⟨x, y, fun k hk1 hk2 => ?_⟩
  obtain ⟨m, hmdef⟩ : ∃ m, m = B' * k * B := ⟨_, rfl⟩
  have hk_eq : k = B * m * B' := by
    calc k = (B * B') * k * (B * B') := by rw [hBB', Matrix.one_mul, Matrix.mul_one]
      _ = B * m * B' := by simp only [hmdef, Matrix.mul_assoc]
  have hJm : J * m = m * J := by
    have hJ : J = B' * s * B := by
      rw [Matrix.mul_assoc, hs, ← Matrix.mul_assoc, hB'B, Matrix.one_mul]
    rw [hJ, hmdef]
    calc B' * s * B * (B' * k * B) = B' * (s * k) * B := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc B B', hBB', Matrix.one_mul]
      _ = B' * (k * s) * B := by rw [hk2]
      _ = B' * k * B * (B' * s * B) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc B B', hBB', Matrix.one_mul]
  have hoff : m.toBlocks₁₂ = 0 ∧ m.toBlocks₂₁ = 0 := by
    have h := hJm
    rw [hJdef, ← Matrix.fromBlocks_toBlocks m, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_inj] at h
    obtain ⟨-, hb, hc, -⟩ := h
    simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add,
      Matrix.neg_mul, Matrix.mul_neg] at hb hc
    exact ⟨matrix_eq_zero_of_eq_neg _ hb, matrix_eq_zero_of_eq_neg _ hc.symm⟩
  obtain ⟨a, d, hmad⟩ : ∃ a d, m = Matrix.fromBlocks a 0 0 d :=
    ⟨m.toBlocks₁₁, m.toBlocks₂₂, by rw [← hoff.1, ← hoff.2, Matrix.fromBlocks_toBlocks]⟩
  have hmU : mᴴ * J * m = J := by
    rw [← hG, hmdef]
    calc (B' * k * B)ᴴ * (Bᴴ * G * B) * (B' * k * B)
        = Bᴴ * (kᴴ * ((B * B')ᴴ * G * (B * B')) * k) * B := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Bᴴ * G * B := by rw [hBB', Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hk1]
  rw [hmad, hJdef, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_inj] at hmU
  obtain ⟨ha, -, -, hd⟩ := hmU
  simp only [Matrix.conjTranspose_zero, Matrix.mul_one, Matrix.mul_zero,
    add_zero, zero_add, Matrix.neg_mul, Matrix.mul_neg, neg_inj] at ha hd
  have ha' : a ∈ Matrix.unitaryGroup (Fin p) ℂ :=
    Matrix.mem_unitaryGroup_iff'.2 (by rw [Matrix.star_eq_conjTranspose]; exact ha)
  have hd' : d ∈ Matrix.unitaryGroup (Fin q) ℂ :=
    Matrix.mem_unitaryGroup_iff'.2 (by rw [Matrix.star_eq_conjTranspose]; exact hd)
  have hkAD : k = kA ⟨a, ha'⟩ * kD ⟨d, hd'⟩ := by
    rw [hk_eq, hmad]
    show B * Matrix.fromBlocks a 0 0 d * B' =
      (B * (Matrix.fromBlocks a 0 0 1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B') * (B * (Matrix.fromBlocks 1 0 0 d : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B')
    rw [hconj, Matrix.fromBlocks_multiply]
    simp
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) = B * (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B' := by rw [Matrix.mul_one, hBB']
  have hJ1 : (1 / 2 : ℂ) • (1 + J) = (Matrix.fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 0 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) := by
    rw [hJdef]
    ext (i | i) (j | j) <;> simp [Matrix.one_apply] <;> (try split_ifs) <;> norm_num
  have hJ2 : (1 / 2 : ℂ) • (1 - J) = (Matrix.fromBlocks 0 0 0 (1 : Matrix (Fin q) (Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) := by
    rw [hJdef]
    ext (i | i) (j | j) <;> simp [Matrix.one_apply] <;> (try split_ifs) <;> norm_num
  have hP1 : (1 / 2 : ℂ) • (1 + s) = B * (Matrix.fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 0 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B' := by
    rw [← hJ1, hsJ, h1, ← Matrix.add_mul, ← Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul]
  have hP2 : (1 / 2 : ℂ) • (1 - s) = B * (Matrix.fromBlocks 0 0 0 (1 : Matrix (Fin q) (Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B' := by
    rw [← hJ2, hsJ, h1, ← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.mul_smul, Matrix.smul_mul]
  have hE1 : (1 / 2 : ℂ) • (1 + s) * k + (1 / 2 : ℂ) • (1 - s) = B * (Matrix.fromBlocks a 0 0 1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B' := by
    rw [hP1, hP2, hk_eq, hmad, hconj, ← Matrix.add_mul, ← Matrix.mul_add, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_add]
    simp
  have hE2 : (1 / 2 : ℂ) • (1 - s) * k + (1 / 2 : ℂ) • (1 + s) = B * (Matrix.fromBlocks 1 0 0 d : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B' := by
    rw [hP1, hP2, hk_eq, hmad, hconj, ← Matrix.add_mul, ← Matrix.mul_add, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_add]
    simp
  rw [hE1, hE2, det_conj_rect B B' hBB' hB'B, det_conj_rect B B' hBB' hB'B,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_one, mul_one,
    one_mul, hkAD, hmul _ _ (hKA _).1 (hKA _).2 (hKD _).1 (hKD _).2, hx', hy']
end GlobalTheory.UpqChar
