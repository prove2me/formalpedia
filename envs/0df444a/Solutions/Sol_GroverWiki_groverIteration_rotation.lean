-- Prove2me | solution 1 for GroverWiki.groverIteration_rotation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T19:46:38.971982+00:00
-- url     : https://prove2.me/submissions/1da34588-103e-4af6-b690-c7ee5b3b732b

import Mathlib
import Definitions.Def_GroverWiki_Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Matrix

open GroverWiki

private theorem span_action {N : ℕ} (f : Fin N → Fin 2) (ω : Fin N)
    (hω : ∀ x, f x = 1 ↔ x = ω) (a b : ℂ) :
    diffusion N *ᵥ (a • ket ω + b • uniformState N) =
        (-a) • ket ω + (2 * a / (Real.sqrt N : ℂ) + b) • uniformState N ∧
      phaseOracle f *ᵥ (a • ket ω + b • uniformState N) =
        (-a - 2 * b / (Real.sqrt N : ℂ)) • ket ω + b • uniformState N := by
  classical
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le ω.val) ω.isLt
  have hs : Real.sqrt (N : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hN))
  have hc : (Real.sqrt N : ℂ) ≠ 0 := by exact_mod_cast hs
  have hsq : (Real.sqrt N : ℂ) ^ 2 = (N : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hnorm : (N : ℂ) * (Real.sqrt N : ℂ)⁻¹ * (Real.sqrt N : ℂ)⁻¹ = 1 := by
    rw [← hsq]
    field_simp
  have hinner : dotProduct (star (uniformState N))
      (a • ket ω + b • uniformState N) =
      (Real.sqrt N : ℂ)⁻¹ * a + b := by
    have hstar : star (uniformState N) = uniformState N := by
      ext j
      simp [uniformState]
    rw [hstar]
    simp [dotProduct, uniformState, ket, Pi.single_apply, mul_add, mul_ite,
      Finset.sum_add_distrib, Complex.ofReal_inv, ← mul_assoc]
    linear_combination b * hnorm
  constructor
  · rw [diffusion, sub_mulVec, smul_mulVec, one_mulVec, vecMulVec_mulVec, hinner]
    ext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, uniformState,
      Complex.ofReal_inv, div_eq_mul_inv, op_smul_eq_mul]
    ring
  · ext i
    by_cases hi : i = ω
    · subst i
      have hf : f ω = 1 := (hω ω).2 rfl
      simp [phaseOracle, mulVec_diagonal, hf, ket, uniformState, div_eq_mul_inv]
      ring
    · have hf : f i = 0 := by
        have hn : f i ≠ 1 := fun he => hi ((hω i).1 he)
        apply Fin.ext
        have hv := (f i).isLt
        have hnval : (f i).val ≠ 1 := by
          intro he
          apply hn
          apply Fin.ext
          exact he
        change (f i).val = 0
        omega
      simp [phaseOracle, mulVec_diagonal, hf, ket, uniformState, hi, Ne.symm hi]

theorem solution {N : ℕ} (hN : 2 ≤ N) (f : Fin N → Fin 2) (ω : Fin N)
    (hω : ∀ x, f x = 1 ↔ x = ω) (φ : ℝ) :
    groverIteration f *ᵥ
        ((Real.cos φ : ℂ) • perpState ω + (Real.sin φ : ℂ) • ket ω) =
      (Real.cos (φ + 2 * Real.arcsin (1 / Real.sqrt N)) : ℂ) • perpState ω +
        (Real.sin (φ + 2 * Real.arcsin (1 / Real.sqrt N)) : ℂ) • ket ω := by
  classical
  let s : ℝ := Real.sqrt N
  let t : ℝ := Real.sqrt ((N : ℝ) - 1)
  let α : ℝ := Real.arcsin (1 / s)
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : 0 < s := Real.sqrt_pos.2 (by linarith)
  have ht : 0 < t := Real.sqrt_pos.2 (by linarith)
  have hs2 : s ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
  have ht2 : t ^ 2 = s ^ 2 - 1 := by
    dsimp [t]
    rw [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ N - 1), hs2]
  have hs1 : 1 ≤ s := by nlinarith [sq_nonneg (s - 1)]
  have ha1 : -1 ≤ 1 / s := by linarith [one_div_pos.mpr hs]
  have ha2 : 1 / s ≤ 1 := (div_le_one hs).2 hs1
  have hsin : Real.sin α = 1 / s := Real.sin_arcsin ha1 ha2
  have hcos0 : 0 ≤ Real.cos α := Real.cos_arcsin_nonneg _
  have hsm : Real.sin α * s = 1 := by rw [hsin]; field_simp
  have hcs : (Real.cos α * s) ^ 2 = t ^ 2 := by
    have hh := congrArg (fun x : ℝ => x * s ^ 2) (Real.sin_sq_add_cos_sq α)
    nlinarith [sq_nonneg (Real.sin α * s - 1)]
  have hcos : Real.cos α = t / s := by
    apply (eq_div_iff (ne_of_gt hs)).2
    nlinarith [mul_nonneg hcos0 (le_of_lt hs)]
  have hc : Real.cos (φ + 2 * α) =
      Real.cos φ * (1 - 2 / s ^ 2) - Real.sin φ * (2 * t / s ^ 2) := by
    rw [Real.cos_add, Real.cos_two_mul, Real.sin_two_mul, hsin, hcos]
    field_simp
    linear_combination 2 * Real.cos φ * ht2
  have hq : Real.sin (φ + 2 * α) =
      Real.sin φ * (1 - 2 / s ^ 2) + Real.cos φ * (2 * t / s ^ 2) := by
    rw [Real.sin_add, Real.cos_two_mul, Real.sin_two_mul, hsin, hcos]
    field_simp
    linear_combination 2 * Real.sin φ * ht2
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hs
  have hscast : (Real.sqrt (N : ℝ) : ℂ) = (s : ℂ) := rfl
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  have htcast : (Real.sqrt ((N : ℝ) - 1) : ℂ) = (t : ℂ) := rfl
  have ht2c : (t : ℂ) ^ 2 = (s : ℂ) ^ 2 - 1 := by exact_mod_cast ht2
  have hp : perpState ω = (s / t : ℂ) • uniformState N - (1 / t : ℂ) • ket ω := by
    ext i
    by_cases hi : i = ω
    · subst i
      simp [perpState, uniformState, ket, Complex.ofReal_inv]
      simp only [hscast]
      field_simp [hsc, htc]
      ring
    · simp [perpState, uniformState, ket, hi, Ne.symm hi, Complex.ofReal_inv,
        div_eq_mul_inv]
      simp only [hscast, htcast]
      field_simp [hsc, htc]
  let a : ℂ := (Real.sin φ : ℂ) - (Real.cos φ : ℂ) / t
  let b : ℂ := (Real.cos φ : ℂ) * s / t
  have hv : (Real.cos φ : ℂ) • perpState ω + (Real.sin φ : ℂ) • ket ω =
      a • ket ω + b • uniformState N := by
    rw [hp]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    dsimp [a, b]
    ring
  rw [groverIteration, ← Matrix.mulVec_mulVec, hv, (span_action f ω hω a b).2,
    (span_action f ω hω (-a - 2 * b / (Real.sqrt N : ℂ)) b).1]
  change _ = (Real.cos (φ + 2 * α) : ℂ) • perpState ω +
    (Real.sin (φ + 2 * α) : ℂ) • ket ω
  rw [hc, hq, hp]
  ext i
  dsimp [a, b]
  by_cases hi : i = ω
  · subst i
    simp [uniformState, ket, Complex.ofReal_inv, div_eq_mul_inv]
    simp only [hscast]
    field_simp [hsc, htc]
    linear_combination -2 * Complex.cos (φ : ℂ) * ht2c
  · simp [uniformState, ket, hi, Ne.symm hi, Complex.ofReal_inv, div_eq_mul_inv]
    simp only [hscast]
    field_simp [hsc, htc]
    ring
