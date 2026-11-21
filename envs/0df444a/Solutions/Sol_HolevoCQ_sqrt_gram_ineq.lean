-- Prove2me | solution 1 for HolevoCQ.sqrt_gram_ineq
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-20T14:38:28.041301+00:00
-- url     : https://prove2.me/submissions/66eb6e1b-2394-46f2-aa98-1d7d6acb257e

import Mathlib
open scoped ComplexOrder MatrixOrder

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι]
    (Γ : Matrix ι ι ℂ) (hΓ : Γ.PosSemidef) :
    (1 - cfc Real.sqrt Γ) ^ 2 = (1 - Γ) ^ 2 * ((1 + cfc Real.sqrt Γ)⁻¹) ^ 2 ∧
      ((1 - Γ) ^ 2 - (1 - cfc Real.sqrt Γ) ^ 2).PosSemidef := by
  classical
  have hsa : IsSelfAdjoint Γ := hΓ.isHermitian.isSelfAdjoint
  have hspec : ∀ x ∈ spectrum ℝ Γ, 0 ≤ x := by
    intro x hx
    rw [hΓ.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hΓ.eigenvalues_nonneg i
  have key1 : ∀ x ∈ spectrum ℝ Γ,
      (1 - Real.sqrt x) ^ 2 = (1 - x) ^ 2 * ((1 + Real.sqrt x)⁻¹) ^ 2 := by
    intro x hx
    have hx0 := hspec x hx
    have h1 : (1 : ℝ) + Real.sqrt x ≠ 0 := by positivity
    have hs : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0
    have hgen : ∀ y : ℝ, (1 - y) ^ 2 * (1 + y) ^ 2 = (1 - y ^ 2) ^ 2 := by
      intro y; ring
    calc (1 - Real.sqrt x) ^ 2
        = (1 - Real.sqrt x) ^ 2 * (((1 + Real.sqrt x) * (1 + Real.sqrt x)⁻¹) ^ 2) := by
            simp [h1]
      _ = (1 - Real.sqrt x) ^ 2 *
            ((1 + Real.sqrt x) ^ 2 * ((1 + Real.sqrt x)⁻¹) ^ 2) := by
            rw [mul_pow]
      _ = ((1 - Real.sqrt x) ^ 2 * (1 + Real.sqrt x) ^ 2) *
            ((1 + Real.sqrt x)⁻¹) ^ 2 := by
            ring
      _ = (1 - Real.sqrt x ^ 2) ^ 2 * ((1 + Real.sqrt x)⁻¹) ^ 2 := by
            rw [hgen]
      _ = (1 - x) ^ 2 * ((1 + Real.sqrt x)⁻¹) ^ 2 := by
            rw [hs]
  have key2 : ∀ x ∈ spectrum ℝ Γ, 0 ≤ (1 - x) ^ 2 - (1 - Real.sqrt x) ^ 2 := by
    intro x hx
    have hx0 := hspec x hx
    have hs : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0
    have hgen : ∀ y : ℝ, (1 - y ^ 2) ^ 2 - (1 - y) ^ 2 = y * (y - 1) ^ 2 * (y + 2) := by
      intro y; ring
    have hfac : (1 - x) ^ 2 - (1 - Real.sqrt x) ^ 2
        = Real.sqrt x * (Real.sqrt x - 1) ^ 2 * (Real.sqrt x + 2) := by
      have := hgen (Real.sqrt x)
      rw [hs] at this
      exact this
    rw [hfac]
    positivity
  have hsqrt_cont : ContinuousOn Real.sqrt (spectrum ℝ Γ) :=
    Real.continuous_sqrt.continuousOn
  have hcont_inv : ContinuousOn (fun x : ℝ => (1 + Real.sqrt x)⁻¹) (spectrum ℝ Γ) :=
    ((continuous_const.add Real.continuous_sqrt).continuousOn).inv₀ (fun x hx => by
      have h := Real.sqrt_nonneg x
      show (1 : ℝ) + Real.sqrt x ≠ 0
      intro h0
      linarith)
  set s : Matrix ι ι ℂ := cfc Real.sqrt Γ with hs
  have hA : (1 - s) ^ 2 = cfc (fun x : ℝ => (1 - Real.sqrt x) ^ 2) Γ := by
    have h1 : (1 : Matrix ι ι ℂ) - s = cfc (fun x : ℝ => 1 - Real.sqrt x) Γ := by
      rw [hs]
      rw [cfc_sub (fun _ : ℝ => 1) Real.sqrt Γ continuousOn_const hsqrt_cont]
      rw [cfc_const_one ℝ Γ]
    rw [h1]
    exact (cfc_pow (fun x : ℝ => 1 - Real.sqrt x) 2 Γ
      ((continuous_const.sub Real.continuous_sqrt).continuousOn) hsa).symm
  have hB : (1 - Γ) ^ 2 = cfc (fun x : ℝ => (1 - x) ^ 2) Γ := by
    have h1 : (1 : Matrix ι ι ℂ) - Γ = cfc (fun x : ℝ => 1 - x) Γ := by
      rw [cfc_sub (fun _ : ℝ => 1) (fun x : ℝ => x) Γ
        continuousOn_const continuous_id.continuousOn]
      rw [cfc_const_one ℝ Γ]
      rw [cfc_id' ℝ Γ hsa]
    rw [h1]
    exact (cfc_pow (fun x : ℝ => 1 - x) 2 Γ
      ((continuous_const.sub continuous_id).continuousOn) hsa).symm
  have hC : ((1 + s)⁻¹) ^ 2 = cfc (fun x : ℝ => ((1 + Real.sqrt x)⁻¹) ^ 2) Γ := by
    have h2 : (1 : Matrix ι ι ℂ) + s = cfc (fun x : ℝ => 1 + Real.sqrt x) Γ := by
      rw [hs]
      rw [cfc_add Γ (fun _ : ℝ => 1) Real.sqrt continuousOn_const hsqrt_cont]
      rw [cfc_const_one ℝ Γ]
    have h3 : ((1 : Matrix ι ι ℂ) + s)⁻¹
        = cfc (fun x : ℝ => (1 + Real.sqrt x)⁻¹) Γ := by
      rw [Matrix.nonsing_inv_eq_ringInverse, h2]
      exact (cfc_inv (fun x : ℝ => 1 + Real.sqrt x) Γ
        (fun x hx => by
          have := hspec x hx
          positivity)
        ((continuous_const.add Real.continuous_sqrt).continuousOn) hsa).symm
    rw [h3]
    exact (cfc_pow (fun x : ℝ => (1 + Real.sqrt x)⁻¹) 2 Γ hcont_inv hsa).symm
  have hD : (1 - Γ) ^ 2 * ((1 + s)⁻¹) ^ 2
      = cfc (fun x : ℝ => (1 - x) ^ 2 * ((1 + Real.sqrt x)⁻¹) ^ 2) Γ := by
    rw [hB, hC]
    exact (cfc_mul (fun x : ℝ => (1 - x) ^ 2) (fun x : ℝ => ((1 + Real.sqrt x)⁻¹) ^ 2) Γ
      (((continuous_const.sub continuous_id).pow 2).continuousOn)
      (hcont_inv.pow 2)).symm
  constructor
  · calc (1 - s) ^ 2
        = cfc (fun x : ℝ => (1 - Real.sqrt x) ^ 2) Γ := hA
      _ = cfc (fun x : ℝ => (1 - x) ^ 2 * ((1 + Real.sqrt x)⁻¹) ^ 2) Γ :=
            cfc_congr key1
      _ = (1 - Γ) ^ 2 * ((1 + s)⁻¹) ^ 2 := hD.symm
  · have hsub : (1 - Γ) ^ 2 - (1 - s) ^ 2
        = cfc (fun x : ℝ => (1 - x) ^ 2 - (1 - Real.sqrt x) ^ 2) Γ := by
      rw [hB, hA]
      exact (cfc_sub (fun x : ℝ => (1 - x) ^ 2) (fun x : ℝ => (1 - Real.sqrt x) ^ 2) Γ
        (((continuous_const.sub continuous_id).pow 2).continuousOn)
        (((continuous_const.sub Real.continuous_sqrt).pow 2).continuousOn)).symm
    rw [hsub, ← Matrix.nonneg_iff_posSemidef]
    exact cfc_nonneg key2
