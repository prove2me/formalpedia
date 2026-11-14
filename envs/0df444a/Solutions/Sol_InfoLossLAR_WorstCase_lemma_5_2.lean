-- Prove2me | solution 1 for InfoLossLAR.WorstCase.lemma_5_2
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-13T16:55:58.506538+00:00
-- url     : https://prove2.me/submissions/f7ce3085-390b-4a42-873d-d6dd33a53c4c

import Mathlib
import Definitions.Def_InfoLossLAR_WorstCase_QPT
import Definitions.Def_InfoLossLAR_WorstCase_Rounding
import Definitions.Def_InfoLossLAR_WorstCase_Laws

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open InfoLossLAR.WorstCase
open scoped Classical

private theorem avg_scalar {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    avg (fun a => c * f a) = c * avg f := by
  simp only [avg, ← Finset.mul_sum]
  ring

private theorem avg_constant {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    avg (fun _ : α => c) = c := by
  simp [avg, Fintype.card_ne_zero]

private theorem avg_fiber_weight {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (E : α ≃ α) (target : α) (weight : β → ℝ) (P : β → Prop) [DecidablePred P] :
    (avg fun a : α => ∑ b : β, if E a = target ∧ P b then weight b else 0) =
      (Fintype.card α : ℝ)⁻¹ * ∑ b : β, if P b then weight b else 0 := by
  classical
  unfold avg
  rw [Finset.sum_comm]
  simp only [← E.eq_symm_apply, ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

private theorem avg_two_equiv {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (E : α ≃ α) (F : β ≃ β) (first : α) (second : β) :
    (avg fun a : α => avg fun b : β =>
      if E a = first ∧ F b = second then (1 : ℝ) else 0) =
      (Fintype.card α : ℝ)⁻¹ * (Fintype.card β : ℝ)⁻¹ := by
  classical
  have hb (a : α) :
      (avg fun b : β => if E a = first ∧ F b = second then (1 : ℝ) else 0) =
        if E a = first then (Fintype.card β : ℝ)⁻¹ else 0 := by
    by_cases ha : E a = first
    · simp [ha, avg, ← F.eq_symm_apply]
    · simp [ha, avg]
  simp_rw [hb]
  simp only [avg, ← E.eq_symm_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

private noncomputable def leftMatrixEquiv {q d N : ℕ}
    (Q : Matrix (Fin d) (Fin d) (ZMod q)) (hQ : IsUnit Q.det) :
    Matrix (Fin d) (Fin N) (ZMod q) ≃ Matrix (Fin d) (Fin N) (ZMod q) where
  toFun A := Q * A
  invFun A := Q⁻¹ * A
  left_inv A := by
    change Q⁻¹ * (Q * A) = A
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul Q hQ, Matrix.one_mul]
  right_inv A := by
    change Q * (Q⁻¹ * A) = A
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv Q hQ, Matrix.one_mul]

private noncomputable def affineVectorEquiv {q d : ℕ}
    (Q : Matrix (Fin d) (Fin d) ℤ) (beta : Fin d → ℤ)
    (hQ : IsUnit (matModq q Q).det) :
    (Fin d → ZMod q) ≃ (Fin d → ZMod q) where
  toFun x := evalAffine Q beta x
  invFun x := (matModq q Q)⁻¹.mulVec (x - modq q beta)
  left_inv x := by
    simp only [evalAffine, add_sub_cancel_right, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hQ, Matrix.one_mulVec]
  right_inv x := by
    simp only [evalAffine, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hQ,
      Matrix.one_mulVec, sub_add_cancel]

theorem solution (q r d N : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (T : Matrix (Fin d) (Fin d) ℤ)
    (S : SmithData q r d T) (hℓ : r < d)
    (χ : (Fin d → ZMod q) → ℝ) (hχ0 : ∀ e, 0 ≤ χ e) (hχ1 : ∑ e, χ e = 1)
    (Ω : Type) [Fintype Ω] [Nonempty Ω]
    (samp : Ω → Matrix (Fin d) (Fin d) ℤ × (Fin d → ℤ))
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hinv : ∀ ρ, IsUnit (matModq q (samp ρ).1).det)
    (hfib : sdist (transportLaw samp χ) (unifZeroFiber S.fT) ≤ δ) :
    (∀ (A' : Matrix (Fin d) (Fin N) (ZMod q)) (x' : Fin d → ZMod q),
      (avg fun ρ : Ω => avg fun A : Matrix (Fin d) (Fin N) (ZMod q) =>
        ∑ e : Fin d → ZMod q,
          if matModq q (samp ρ).1 * A = A' ∧ evalAffine (samp ρ).1 (samp ρ).2 e = x'
          then χ e else 0) =
        (Fintype.card (Matrix (Fin d) (Fin N) (ZMod q)) : ℝ)⁻¹ * transportLaw samp χ x') ∧
    sdist (transportLaw samp χ) (unifZeroFiber S.fT) ≤ δ ∧
    (∀ (A' : Matrix (Fin d) (Fin N) (ZMod q)) (x' : Fin d → ZMod q),
      (avg fun ρ : Ω => avg fun A : Matrix (Fin d) (Fin N) (ZMod q) =>
        avg fun u : Fin d → ZMod q =>
          if matModq q (samp ρ).1 * A = A' ∧ evalAffine (samp ρ).1 (samp ρ).2 u = x'
          then (1 : ℝ) else 0) =
        ((Fintype.card (Matrix (Fin d) (Fin N) (ZMod q)) : ℝ) * (q : ℝ) ^ d)⁻¹)  := by
  classical
  let matrixEquiv (ρ : Ω) : Matrix (Fin d) (Fin N) (ZMod q) ≃
      Matrix (Fin d) (Fin N) (ZMod q) :=
    leftMatrixEquiv (matModq q (samp ρ).1) (hinv ρ)
  let vectorEquiv (ρ : Ω) : (Fin d → ZMod q) ≃ (Fin d → ZMod q) :=
    affineVectorEquiv (samp ρ).1 (samp ρ).2 (hinv ρ)
  refine ⟨?_, hfib, ?_⟩
  · intro A' x'
    have hfixed (ρ : Ω) :
        (avg fun A : Matrix (Fin d) (Fin N) (ZMod q) =>
          ∑ e : Fin d → ZMod q,
            if matModq q (samp ρ).1 * A = A' ∧ evalAffine (samp ρ).1 (samp ρ).2 e = x'
            then χ e else 0) =
          (Fintype.card (Matrix (Fin d) (Fin N) (ZMod q)) : ℝ)⁻¹ *
            ∑ e : Fin d → ZMod q,
              if evalAffine (samp ρ).1 (samp ρ).2 e = x' then χ e else 0 :=
      avg_fiber_weight (matrixEquiv ρ) A' χ
        (fun e => evalAffine (samp ρ).1 (samp ρ).2 e = x')
    unfold transportLaw
    simp_rw [hfixed]
    exact avg_scalar _ _
  · intro A' x'
    have hfixed (ρ : Ω) :
        (avg fun A : Matrix (Fin d) (Fin N) (ZMod q) =>
          avg fun u : Fin d → ZMod q =>
            if matModq q (samp ρ).1 * A = A' ∧ evalAffine (samp ρ).1 (samp ρ).2 u = x'
            then (1 : ℝ) else 0) =
          (Fintype.card (Matrix (Fin d) (Fin N) (ZMod q)) : ℝ)⁻¹ *
            (Fintype.card (Fin d → ZMod q) : ℝ)⁻¹ :=
      avg_two_equiv (matrixEquiv ρ) (vectorEquiv ρ) A' x'
    simp_rw [hfixed]
    rw [avg_constant]
    have hcard : (Fintype.card (Fin d → ZMod q) : ℝ) = (q : ℝ) ^ d := by
      simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow]
    rw [hcard, mul_inv_rev]
    exact mul_comm _ _

