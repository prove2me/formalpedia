-- Prove2me | solution 1 for GlobalTheory.MonomialDiag.exists_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:37.80929+00:00
-- url     : https://prove2.me/submissions/ed3e6939-484a-413a-8f9a-174d50d1f122

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureConjugationInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsSignatureDecompositionDiagonal
import Theorems.Thm_Formalism_UG_P_sig_data
import Theorems.Thm_Formalism_UG_P_sig_dim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix
namespace GlobalTheory.MonomialDiag
private theorem star_inv_sqrt_abs_mul_mul_inv_sqrt_abs_eq_sign (x : ℝ) (hx : x ≠ 0) :
    star ((Real.sqrt |x| : ℝ) : ℂ)⁻¹ * (x : ℂ) * ((Real.sqrt |x| : ℝ) : ℂ)⁻¹ =
      if 0 < x then (1 : ℂ) else -1 := by
  have hst : star ((Real.sqrt |x| : ℝ) : ℂ) = ((Real.sqrt |x| : ℝ) : ℂ) := Complex.conj_ofReal _
  have hs : Real.sqrt |x| * Real.sqrt |x| = |x| := Real.mul_self_sqrt (abs_nonneg x)
  rw [star_inv₀, hst,
    show ((Real.sqrt |x| : ℝ) : ℂ)⁻¹ * (x : ℂ) * ((Real.sqrt |x| : ℝ) : ℂ)⁻¹ =
      ((x / (Real.sqrt |x| * Real.sqrt |x|) : ℝ) : ℂ) by push_cast; ring, hs]
  split_ifs with h
  · rw [abs_of_pos h, div_self hx, Complex.ofReal_one]
  · rw [abs_of_neg (lt_of_le_of_ne (not_lt.mp h) hx), div_neg_self hx]
    push_cast
    ring
private theorem star_sqrt_abs_mul_sign_mul_sqrt_abs_eq (x : ℝ) (hx : x ≠ 0) :
    star ((Real.sqrt |x| : ℝ) : ℂ) * (if 0 < x then (1 : ℂ) else -1) * ((Real.sqrt |x| : ℝ) : ℂ) =
      (x : ℂ) := by
  have hst : star ((Real.sqrt |x| : ℝ) : ℂ) = ((Real.sqrt |x| : ℝ) : ℂ) := Complex.conj_ofReal _
  have hs : Real.sqrt |x| * Real.sqrt |x| = |x| := Real.mul_self_sqrt (abs_nonneg x)
  rw [hst]
  split_ifs with h
  · rw [mul_one, ← Complex.ofReal_mul, hs, abs_of_pos h]
  · rw [mul_neg_one, neg_mul, ← Complex.ofReal_mul, hs, abs_of_neg (lt_of_le_of_ne (not_lt.mp h) hx)]
    push_cast
    ring
private theorem Jpq_equiv_apply_eq_ite_sign {n p q : ℕ} (d : Fin n → ℝ) (e : Fin n ≃ Fin p ⊕ Fin q)
    (he : ∀ i, 0 < d i ↔ (e i).isLeft = true) (i j : Fin n) :
    Formalism.UG.Jpq p q (e i) (e j) = if i = j then (if 0 < d i then (1 : ℂ) else -1) else 0 := by
  unfold Formalism.UG.Jpq
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    have hi := he i
    revert hi
    generalize e i = x
    rcases x with a | a <;> intro hi <;> simp_all
  · have hne : e i ≠ e j := fun h => hij (e.injective h)
    rw [if_neg hij]
    revert hne
    generalize e i = x
    generalize e j = y
    rcases x with a | a <;> rcases y with b | b <;> intro hne <;> simp_all
private theorem conjTranspose_mul_diagonal_mul_inv_sqrt_eq_Jpq {n p q : ℕ} (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0)
    (e : Fin n ≃ Fin p ⊕ Fin q) (he : ∀ i, 0 < d i ↔ (e i).isLeft = true)
    (C : Matrix (Fin n) (Fin p ⊕ Fin q) ℂ)
    (hC : ∀ i a, C i a = if i = e.symm a then ((Real.sqrt |d i| : ℝ) : ℂ)⁻¹ else 0) :
    Cᴴ * Matrix.diagonal (fun i => (d i : ℂ)) * C = Formalism.UG.Jpq p q := by
  ext a b
  have key := Jpq_equiv_apply_eq_ite_sign d e he (e.symm a) (e.symm b)
  rw [e.apply_symm_apply, e.apply_symm_apply] at key
  rw [key, Matrix.mul_apply, Finset.sum_eq_single (e.symm b)]
  · rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply, hC, hC]
    simp only [↓reduceIte]
    by_cases hab : e.symm a = e.symm b
    · rw [if_pos hab.symm, if_pos hab, hab]
      exact star_inv_sqrt_abs_mul_mul_inv_sqrt_abs_eq_sign _ (hd _)
    · rw [if_neg (Ne.symm hab), if_neg hab, star_zero, zero_mul, zero_mul]
  · intro i _ hi
    rw [hC i b, if_neg hi, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h
private theorem conjTranspose_mul_Jpq_mul_sqrt_eq_diagonal {n p q : ℕ} (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0)
    (e : Fin n ≃ Fin p ⊕ Fin q) (he : ∀ i, 0 < d i ↔ (e i).isLeft = true)
    (B : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ)
    (hB : ∀ a i, B a i = if a = e i then ((Real.sqrt |d i| : ℝ) : ℂ) else 0) :
    Bᴴ * Formalism.UG.Jpq p q * B = Matrix.diagonal (fun i => (d i : ℂ)) := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (e j)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (e i)]
    · rw [Matrix.conjTranspose_apply, hB, hB]
      simp only [↓reduceIte]
      rw [Jpq_equiv_apply_eq_ite_sign d e he, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij
        simp only [↓reduceIte]
        exact star_sqrt_abs_mul_sign_mul_sqrt_abs_eq _ (hd _)
      · rw [if_neg hij, if_neg hij, mul_zero, zero_mul]
    · intro b _ hb
      rw [Matrix.conjTranspose_apply, hB, if_neg hb, star_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro a _ ha
    rw [hB a j, if_neg ha, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h
end GlobalTheory.MonomialDiag
end

set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.MonomialDiag
namespace GlobalTheory.MonomialDiag
theorem _root_.solution : ∀ (n p q : ℕ) (G Q : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ), Formalism.UG.HasSignature G p q → Q.det ≠ 0 → (∀ i, d i ≠ 0) → Qᴴ * G * Q = Matrix.diagonal (fun i => (d i : ℂ)) → ∃ A : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ, Aᴴ * Formalism.UG.Jpq p q * A = G ∧ ∀ a i j, (A * Q) a i ≠ 0 → (A * Q) a j ≠ 0 → i = j := by
  intro n p q G Q d hG hQ hd hQG
  classical
  obtain ⟨hcard, Q₁, hQ₁⟩ := Formalism.UG.P.sig_data G p q hG
  rw [Fintype.card_fin] at hcard

  let e₀ : Fin n ≃ Fin (Fintype.card {i // 0 < d i}) ⊕ Fin (Fintype.card {i // ¬ 0 < d i}) :=
    (Equiv.sumCompl (fun i => 0 < d i)).symm.trans
      (Equiv.sumCongr (Fintype.equivFin _) (Fintype.equivFin _))
  have he₀ : ∀ i, 0 < d i ↔ (e₀ i).isLeft = true := by
    intro i
    by_cases h : 0 < d i
    · simp [e₀, h]
    · simp [e₀, h]
  have hn₀ : n = Fintype.card {i // 0 < d i} + Fintype.card {i // ¬ 0 < d i} := by
    simpa using Fintype.card_congr e₀

  have h₂ : (Q * Matrix.of (fun i a => if i = e₀.symm a then ((Real.sqrt |d i| : ℝ) : ℂ)⁻¹ else 0))ᴴ *
      G * (Q * Matrix.of (fun i a => if i = e₀.symm a then ((Real.sqrt |d i| : ℝ) : ℂ)⁻¹ else 0)) =
      Formalism.UG.Jpq _ _ := by
    rw [Matrix.conjTranspose_mul]
    calc _ = (Matrix.of (fun i a => if i = e₀.symm a then ((Real.sqrt |d i| : ℝ) : ℂ)⁻¹ else 0))ᴴ *
          (Qᴴ * G * Q) * Matrix.of (fun i a => if i = e₀.symm a then ((Real.sqrt |d i| : ℝ) : ℂ)⁻¹ else 0) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hQG]
          exact conjTranspose_mul_diagonal_mul_inv_sqrt_eq_Jpq d hd e₀ he₀ _ (fun i a => rfl)
  have i1 := Formalism.UG.P.sig_dim G Q₁ hQ₁ _ h₂
  have i2 := Formalism.UG.P.sig_dim G _ h₂ Q₁ hQ₁
  rw [Fintype.card_fin] at i1 i2
  have hp : Fintype.card {i // 0 < d i} = p := by omega
  have hq : Fintype.card {i // ¬ 0 < d i} = q := by omega
  let e : Fin n ≃ Fin p ⊕ Fin q := e₀.trans (Equiv.sumCongr (finCongr hp) (finCongr hq))
  have he : ∀ i, 0 < d i ↔ (e i).isLeft = true := by
    intro i
    rw [he₀ i]
    simp only [e, Equiv.trans_apply]
    cases e₀ i <;> rfl
  let B : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ :=
    Matrix.of (fun a i => if a = e i then ((Real.sqrt |d i| : ℝ) : ℂ) else 0)
  have hB : Bᴴ * Formalism.UG.Jpq p q * B = Matrix.diagonal (fun i => (d i : ℂ)) :=
    conjTranspose_mul_Jpq_mul_sqrt_eq_diagonal d hd e he B (fun a i => rfl)
  have hQu : IsUnit Q.det := isUnit_iff_ne_zero.mpr hQ
  have hQQ : Q * Q⁻¹ = 1 := Q.mul_nonsing_inv hQu
  have hQQ' : (Q⁻¹)ᴴ * Qᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hQQ, Matrix.conjTranspose_one]
  refine ⟨B * Q⁻¹, ?_, ?_⟩
  · calc (B * Q⁻¹)ᴴ * Formalism.UG.Jpq p q * (B * Q⁻¹) = (Q⁻¹)ᴴ * (Bᴴ * Formalism.UG.Jpq p q * B) * Q⁻¹ := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = (Q⁻¹)ᴴ * (Qᴴ * G * Q) * Q⁻¹ := by rw [hB, hQG]
      _ = ((Q⁻¹)ᴴ * Qᴴ) * G * (Q * Q⁻¹) := by simp only [Matrix.mul_assoc]
      _ = G := by rw [hQQ', hQQ, Matrix.one_mul, Matrix.mul_one]
  · intro a i j hi hj
    have hBQ : B * Q⁻¹ * Q = B := by
      rw [Matrix.mul_assoc, Q.nonsing_inv_mul hQu, Matrix.mul_one]
    rw [hBQ] at hi hj
    have hai : a = e i := by
      by_contra h
      exact hi (by simp [B, h])
    have haj : a = e j := by
      by_contra h
      exact hj (by simp [B, h])
    exact e.injective (hai.symm.trans haj)
end GlobalTheory.MonomialDiag
