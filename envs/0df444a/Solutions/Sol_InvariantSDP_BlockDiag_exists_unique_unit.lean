-- Prove2me | solution 1 for InvariantSDP.BlockDiag.exists_unique_unit
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T21:36:01.391872+00:00
-- url     : https://prove2.me/submissions/677580bf-a8ac-445b-9fac-32e49c492cc9

import Mathlib
import Definitions.Def_InvariantSDP_BlockDiag_Basic

open InvariantSDP.BlockDiag Matrix Polynomial
open scoped ComplexOrder

lemma herm_pow_kill {n : ℕ} (H Q : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) :
    ∀ a : ℕ, H ^ (a + 1) * Q = 0 → H * Q = 0 := by
  intro a
  induction a with
  | zero => intro h; simpa using h
  | succ a ih =>
    intro h
    apply ih
    set W := H ^ a * Q with hW
    have e1 : H ^ (a + 1 + 1) * Q = H * (H * W) := by
      rw [pow_succ', pow_succ', hW]; simp only [Matrix.mul_assoc]
    have e2 : H ^ (a + 1) * Q = H * W := by
      rw [pow_succ', hW]; simp only [Matrix.mul_assoc]
    rw [e2]
    rw [e1] at h
    have h2 : (H * W)ᴴ * (H * W) = 0 := by
      rw [conjTranspose_mul, hH]
      simp only [Matrix.mul_assoc]
      rw [h, Matrix.mul_zero]
    exact Matrix.conjTranspose_mul_self_eq_zero.mp h2

lemma mul_aeval_mem {n : ℕ} (A : NonUnitalStarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ))
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H ∈ A) (r : ℂ[X]) : H * aeval H r ∈ A := by
  induction r using Polynomial.induction_on with
  | C c =>
    rw [aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.mul_one]
    exact SMulMemClass.smul_mem c hH
  | add p q hp hq => rw [map_add, Matrix.mul_add]; exact add_mem hp hq
  | monomial k c ih =>
    have : H * aeval H (C c * X ^ (k + 1)) = (H * aeval H (C c * X ^ k)) * H := by
      simp only [map_mul, aeval_C, map_pow, aeval_X, pow_succ, Algebra.algebraMap_eq_smul_one,
        Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_assoc]
    rw [this]; exact mul_mem ih hH

theorem solution {n : ℕ} (A : NonUnitalStarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ)) :
    ∃! E : Matrix (Fin n) (Fin n) ℂ, IsUnitOf A E := by
  classical
  -- finite spanning set
  let A' : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ) := A.toNonUnitalSubalgebra.toSubmodule
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian A'
  have hsA : ∀ x ∈ s, x ∈ A := by
    intro x hx
    have : x ∈ A' := hs ▸ Submodule.subset_span hx
    exact this
  set H : Matrix (Fin n) (Fin n) ℂ := ∑ x ∈ s, x * xᴴ with hHdef
  have hHA : H ∈ A := sum_mem fun x hx => mul_mem (hsA x hx) (by
    rw [← Matrix.star_eq_conjTranspose]; exact star_mem (hsA x hx))
  have hHh : Hᴴ = H := by
    rw [hHdef, conjTranspose_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
  have hint : IsIntegral ℂ H := Algebra.IsIntegral.isIntegral H
  have hm0 : minpoly ℂ H ≠ 0 := minpoly.ne_zero hint
  obtain ⟨q, hq, hqd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd (minpoly ℂ H) hm0 0
  simp only [map_zero, sub_zero] at hq hqd
  have hc : q.eval 0 ≠ 0 := by
    intro h; apply hqd; rw [X_dvd_iff, coeff_zero_eq_eval_zero]; exact h
  set c := q.eval 0
  set a := (minpoly ℂ H).rootMultiplicity 0
  have hHq : H * aeval H q = 0 := by
    have h0 : aeval H (minpoly ℂ H) = 0 := minpoly.aeval ℂ H
    rw [hq, map_mul, map_pow, aeval_X] at h0
    rcases Nat.eq_zero_or_pos a with ha | ha
    · rw [ha, pow_zero, Matrix.one_mul] at h0; rw [h0, Matrix.mul_zero]
    · obtain ⟨b, hb⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      rw [hb] at h0
      exact herm_pow_kill H _ hHh b h0
  -- q - C c = X * r
  obtain ⟨r, hr⟩ : X ∣ q - C c := by
    rw [X_dvd_iff, coeff_sub, coeff_C_zero, coeff_zero_eq_eval_zero, sub_self]
  have hqexp : aeval H q = c • (1 : Matrix (Fin n) (Fin n) ℂ) + H * aeval H r := by
    have : q = C c + X * r := by rw [← hr]; ring
    rw [this, map_add, aeval_C, map_mul, aeval_X, Algebra.algebraMap_eq_smul_one]
  set K : Matrix (Fin n) (Fin n) ℂ := c⁻¹ • aeval H q with hK
  have hHK : H * K = 0 := by rw [hK, Matrix.mul_smul, hHq, smul_zero]
  have h1K : 1 - K ∈ A := by
    have : 1 - K = (-c⁻¹) • (H * aeval H r) := by
      rw [hK, hqexp, smul_add, smul_smul, inv_mul_cancel₀ hc, one_smul, neg_smul]; abel
    rw [this]; exact SMulMemClass.smul_mem _ (mul_aeval_mem A H hHA r)
  -- Kᴴ x = 0 for generators
  have hKH : Kᴴ * H = 0 := by
    have := congrArg conjTranspose hHK
    rwa [conjTranspose_mul, hHh, conjTranspose_zero] at this
  have hgen : ∀ x ∈ s, Kᴴ * x = 0 := by
    have hsum : ∑ x ∈ s, (Kᴴ * x) * (Kᴴ * x)ᴴ = 0 := by
      have : ∑ x ∈ s, (Kᴴ * x) * (Kᴴ * x)ᴴ = Kᴴ * H * K := by
        rw [hHdef, Matrix.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [conjTranspose_mul, conjTranspose_conjTranspose]
        simp only [Matrix.mul_assoc]
      rw [this, hKH, Matrix.zero_mul]
    have htr := congrArg Matrix.trace hsum
    rw [trace_sum, trace_zero] at htr
    have hnn : ∀ x ∈ s, 0 ≤ ((Kᴴ * x) * (Kᴴ * x)ᴴ).trace := fun x _ =>
      (posSemidef_self_mul_conjTranspose _).trace_nonneg
    intro x hx
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp htr x hx
    exact trace_mul_conjTranspose_self_eq_zero_iff.mp this
  have hKA : ∀ X ∈ A, Kᴴ * X = 0 := by
    intro X hX
    have hX' : X ∈ A' := hX
    rw [← hs] at hX'
    clear hX
    induction hX' using Submodule.span_induction with
    | mem x hx => exact hgen x hx
    | zero => exact Matrix.mul_zero _
    | add x y _ _ hx hy => simp [Matrix.mul_add, hx, hy]
    | smul t x _ hx => simp [Matrix.mul_smul, hx]
  set P : Matrix (Fin n) (Fin n) ℂ := (1 - K)ᴴ with hP
  have hPA : P ∈ A := by rw [hP, ← Matrix.star_eq_conjTranspose]; exact star_mem h1K
  have hleft : ∀ X ∈ A, P * X = X := by
    intro X hX
    rw [hP, conjTranspose_sub, conjTranspose_one, Matrix.sub_mul, Matrix.one_mul, hKA X hX, sub_zero]
  have hPsA : Pᴴ ∈ A := by rw [← Matrix.star_eq_conjTranspose]; exact star_mem hPA
  have hright : ∀ X ∈ A, X * Pᴴ = X := by
    intro X hX
    have hXs : Xᴴ ∈ A := by rw [← Matrix.star_eq_conjTranspose]; exact star_mem hX
    have := congrArg conjTranspose (hleft _ hXs)
    rwa [conjTranspose_mul, conjTranspose_conjTranspose] at this
  have hPP : P = Pᴴ := by
    have e1 := hright P hPA
    have e2 := hleft Pᴴ hPsA
    exact e1.symm.trans e2
  refine ⟨P, ⟨hPA, fun X hX => ⟨hleft X hX, by rw [hPP]; exact hright X hX⟩⟩, ?_⟩
  rintro E ⟨hEA, hE⟩
  -- E * P = E and E * P = P
  have h2 := (hE P hPA).1
  have h3 : E * P = E := by rw [hPP]; exact hright E hEA
  exact h3.symm.trans h2
