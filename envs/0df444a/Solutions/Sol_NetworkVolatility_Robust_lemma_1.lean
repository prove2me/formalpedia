-- Prove2me | solution 1 for NetworkVolatility.Robust.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T21:32:30.782849+00:00
-- url     : https://prove2.me/submissions/42fc7776-24a4-4f77-95a3-026ce67cea1b

import Mathlib
import Definitions.Def_NetworkVolatility_Robust_Model

open Matrix

namespace Aux_NetworkVolatility_Robust_lemma_1

lemma quad_expand {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : Aᵀ = A) (x h : Fin n → ℝ) (t : ℝ) :
    (x + t • h) ⬝ᵥ (A *ᵥ (x + t • h)) =
      x ⬝ᵥ (A *ᵥ x) + t * (2 * ((A *ᵥ x) ⬝ᵥ h)) + t ^ 2 * (h ⬝ᵥ (A *ᵥ h)) := by
  have hs : x ⬝ᵥ (A *ᵥ h) = (A *ᵥ x) ⬝ᵥ h := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hA]
  have hs2 : h ⬝ᵥ (A *ᵥ x) = (A *ᵥ x) ⬝ᵥ h := dotProduct_comm _ _
  rw [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, dotProduct_add, smul_dotProduct,
    smul_dotProduct, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
    hs, hs2]
  ring

lemma quad_contDiff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ContDiff ℝ 1 (fun g : Fin n → ℝ => g ⬝ᵥ (A *ᵥ g)) := by
  show ContDiff ℝ 1 (fun g : Fin n → ℝ => ∑ i, g i * ∑ j, A i j * g j)
  fun_prop

lemma quad_fderiv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : Aᵀ = A) (x h : Fin n → ℝ) :
    fderiv ℝ (fun g : Fin n → ℝ => g ⬝ᵥ (A *ᵥ g)) x h = 2 * ((A *ᵥ x) ⬝ᵥ h) := by
  have hd : DifferentiableAt ℝ (fun g : Fin n → ℝ => g ⬝ᵥ (A *ᵥ g)) x :=
    ((quad_contDiff A).differentiable (by norm_num)) x
  have hline : HasDerivAt (fun t : ℝ => x + t • h) h 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add x
  have h1 := hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have h2 : HasDerivAt (fun t : ℝ => x ⬝ᵥ (A *ᵥ x) + t * (2 * ((A *ᵥ x) ⬝ᵥ h)) +
      t ^ 2 * (h ⬝ᵥ (A *ᵥ h))) (2 * ((A *ᵥ x) ⬝ᵥ h)) 0 := by
    have e1 := ((hasDerivAt_id (0 : ℝ)).mul_const (2 * ((A *ᵥ x) ⬝ᵥ h))).const_add
      (x ⬝ᵥ (A *ᵥ x))
    have e2 := ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (h ⬝ᵥ (A *ᵥ h)))
    refine (e1.fun_add e2).congr_deriv ?_
    simp
  have hfun : ((fun g : Fin n → ℝ => g ⬝ᵥ (A *ᵥ g)) ∘ fun t : ℝ => x + t • h) =
      fun t : ℝ => x ⬝ᵥ (A *ᵥ x) + t * (2 * ((A *ᵥ x) ⬝ᵥ h)) + t ^ 2 * (h ⬝ᵥ (A *ᵥ h)) := by
    funext t
    exact quad_expand A hA x h t
  rw [hfun] at h1
  exact h1.unique h2

end Aux_NetworkVolatility_Robust_lemma_1

open Aux_NetworkVolatility_Robust_lemma_1 in
open NetworkVolatility.Robust in
theorem solution {n : ℕ} (W Wt : Matrix (Fin n) (Fin n) ℝ) (α : ℝ)
    (hW : W.IsSymm) (hWt : Wt.IsSymm) (hL : IsUnit (1 - α • W)) (hLt : IsUnit (1 - α • Wt))
    (f : Fin n → ℝ) :
    let L := 1 - α • W
    let M := 1 - L * (1 - α • Wt)⁻¹
    f ⬝ᵥ (L⁻¹ *ᵥ f) = 1 →
      (IsMaxOn (fun g => g ⬝ᵥ ((L⁻¹ * M) *ᵥ g)) {g | g ⬝ᵥ (L⁻¹ *ᵥ g) = 1} f →
          ∃ μ : ℝ, M *ᵥ f = μ • f) ∧
      (IsMinOn (fun g => g ⬝ᵥ ((L⁻¹ * M) *ᵥ g)) {g | g ⬝ᵥ (L⁻¹ *ᵥ g) = 1} f →
          ∃ μ : ℝ, M *ᵥ f = μ • f) := by
  intro L M hf
  have hLdet : IsUnit L.det := (Matrix.isUnit_iff_isUnit_det _).1 hL
  have hLtdet : IsUnit (1 - α • Wt).det := (Matrix.isUnit_iff_isUnit_det _).1 hLt
  have hLsymm : Lᵀ = L := by
    show (1 - α • W)ᵀ = 1 - α • W
    rw [transpose_sub, transpose_one, transpose_smul, hW.eq]
  have hLtsymm : (1 - α • Wt)ᵀ = 1 - α • Wt := by
    rw [transpose_sub, transpose_one, transpose_smul, hWt.eq]
  have hA : (L⁻¹)ᵀ = L⁻¹ := by rw [transpose_nonsing_inv, hLsymm]
  have hAt : ((1 - α • Wt)⁻¹)ᵀ = (1 - α • Wt)⁻¹ := by rw [transpose_nonsing_inv, hLtsymm]
  have hBeq : L⁻¹ * M = L⁻¹ - (1 - α • Wt)⁻¹ := by
    show L⁻¹ * (1 - L * (1 - α • Wt)⁻¹) = _
    rw [mul_sub, mul_one, ← mul_assoc, nonsing_inv_mul _ hLdet, one_mul]
  have hB : (L⁻¹ * M)ᵀ = L⁻¹ * M := by
    rw [hBeq, transpose_sub, hA, hAt]
  -- core argument from an extremum
  have core : IsLocalExtrOn (fun g => g ⬝ᵥ ((L⁻¹ * M) *ᵥ g))
      {g | g ⬝ᵥ (L⁻¹ *ᵥ g) = f ⬝ᵥ (L⁻¹ *ᵥ f)} f → ∃ μ : ℝ, M *ᵥ f = μ • f := by
    intro hext
    have hc := (quad_contDiff L⁻¹).hasStrictFDerivAt (x := f) (by norm_num)
    have ho := (quad_contDiff (L⁻¹ * M)).hasStrictFDerivAt (x := f) (by norm_num)
    obtain ⟨a, b, hab, heq⟩ := hext.exists_multipliers_of_hasStrictFDerivAt_1d hc ho
    have hvec : ∀ h : Fin n → ℝ,
        (a • (L⁻¹ *ᵥ f) + b • ((L⁻¹ * M) *ᵥ f)) ⬝ᵥ h = 0 := by
      intro h
      have := congrArg (fun T => T h) heq
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
        ContinuousLinearMap.zero_apply] at this
      rw [quad_fderiv _ hA, quad_fderiv _ hB] at this
      rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
      linarith
    have hv0 : a • (L⁻¹ *ᵥ f) + b • ((L⁻¹ * M) *ᵥ f) = 0 :=
      dotProduct_self_eq_zero.1 (hvec _)
    have hb : b ≠ 0 := by
      intro hb0
      have ha0 : a ≠ 0 := by
        intro ha0; exact hab (by rw [ha0, hb0]; rfl)
      rw [hb0, zero_smul, add_zero] at hv0
      have : L⁻¹ *ᵥ f = 0 := by
        rcases smul_eq_zero.1 hv0 with h | h
        · exact absurd h ha0
        · exact h
      rw [this, dotProduct_zero] at hf
      exact zero_ne_one hf
    refine ⟨-a / b, ?_⟩
    have hBf : (L⁻¹ * M) *ᵥ f = (-a / b) • (L⁻¹ *ᵥ f) := by
      have : b • ((L⁻¹ * M) *ᵥ f) = -(a • (L⁻¹ *ᵥ f)) := eq_neg_of_add_eq_zero_right hv0
      have h2 : (L⁻¹ * M) *ᵥ f = b⁻¹ • (b • ((L⁻¹ * M) *ᵥ f)) := by
        rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
      rw [h2, this, smul_neg, smul_smul, ← neg_smul]
      congr 1
      field_simp
    calc M *ᵥ f = (L * (L⁻¹ * M)) *ᵥ f := by
          rw [← mul_assoc, mul_nonsing_inv _ hLdet, one_mul]
      _ = L *ᵥ ((L⁻¹ * M) *ᵥ f) := (mulVec_mulVec _ _ _).symm
      _ = (-a / b) • ((L * L⁻¹) *ᵥ f) := by
          rw [hBf, mulVec_smul, mulVec_mulVec]
      _ = (-a / b) • f := by rw [mul_nonsing_inv _ hLdet, one_mulVec]
  have hset : {g : Fin n → ℝ | g ⬝ᵥ (L⁻¹ *ᵥ g) = 1} =
      {g | g ⬝ᵥ (L⁻¹ *ᵥ g) = f ⬝ᵥ (L⁻¹ *ᵥ f)} := by rw [hf]
  constructor
  · intro hmax
    rw [hset] at hmax
    exact core (Or.inr hmax.localize)
  · intro hmin
    rw [hset] at hmin
    exact core (Or.inl hmin.localize)
