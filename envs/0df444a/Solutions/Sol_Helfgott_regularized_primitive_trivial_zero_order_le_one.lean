-- Prove2me | solution 1 for Helfgott.regularized_primitive_trivial_zero_order_le_one
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-06T03:04:49.564648+00:00
-- url     : https://prove2.me/submissions/12ff6928-8a40-4758-bd77-b67f9a5a4efb

import Mathlib.Analysis.Fourier.ZMod
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Finset Complex
open scoped BigOperators

namespace Helfgott

theorem primitive_gauss_norm_sq (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖^2 = (q : ℝ) := by
  classical
  have hid := congr_fun (ZMod.dft_dft (χ : ZMod q → ℂ)) (-1)
  have hτconj : star (gaussSum χ ZMod.stdAddChar) =
      ∑ j : ZMod q, ZMod.stdAddChar (-j)*χ⁻¹ j := by
    rw [star_gaussSum_eq]
    simp [gaussSum, AddChar.inv_apply, mul_comm]
  have hprod : gaussSum χ ZMod.stdAddChar * star (gaussSum χ ZMod.stdAddChar) = (q : ℂ) := by
    rw [ZMod.dft_apply] at hid
    simp only [smul_eq_mul, mul_neg_one, neg_neg] at hid
    simp_rw [hχ.fourierTransform_eq_inv_mul_gaussSum] at hid
    simp only [map_one, mul_one] at hid
    calc
      _ = ∑ j : ZMod q, ZMod.stdAddChar (-j)*
          (χ⁻¹ j*gaussSum χ ZMod.stdAddChar) := by
        rw [hτconj, mul_sum]
        apply sum_congr rfl
        intro j _
        ring
      _ = ∑ k : ZMod q, ZMod.stdAddChar k*
          (χ⁻¹ (-k)*gaussSum χ ZMod.stdAddChar) := by
        exact Fintype.sum_equiv (Equiv.neg _) _ _ (fun j => by simp)
      _ = _ := hid
  change gaussSum χ ZMod.stdAddChar *
    (starRingEnd ℂ) (gaussSum χ ZMod.stdAddChar) = (q : ℂ) at hprod
  rw [Complex.mul_conj] at hprod
  have hre := congrArg Complex.re hprod
  have hs : Complex.normSq (gaussSum χ ZMod.stdAddChar) = (q : ℝ) := by
    simpa only [Complex.ofReal_re, Complex.natCast_re] using hre
  simpa only [Complex.normSq_eq_norm_sq] using hs

theorem primitive_gauss_norm (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt q := by
  have hs := primitive_gauss_norm_sq q χ hχ
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hr := Real.sq_sqrt hq
  have hn := norm_nonneg (gaussSum χ ZMod.stdAddChar)
  have hp := Real.sqrt_nonneg (q : ℝ)
  nlinarith

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex Filter
open scoped Topology Classical

namespace Helfgott

lemma primitive_rootNumber_ne_zero (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive) : χ.rootNumber≠0 := by
  have hg : gaussSum χ ZMod.stdAddChar≠0 := by
    intro hz
    have h := primitive_gauss_norm_sq q χ hp
    rw [hz,norm_zero,zero_pow (by norm_num)] at h
    exact (Nat.cast_ne_zero.mpr (NeZero.ne q) : (q : ℝ)≠0) h.symm
  unfold DirichletCharacter.rootNumber
  apply div_ne_zero (div_ne_zero hg (pow_ne_zero _ I_ne_zero))
  exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne q)))

lemma primitive_nonprincipal_completedLFunction_zero_ne_zero (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive) (hχ : χ≠1) :
    χ.completedLFunction 0≠0 := by
  have hi : χ⁻¹≠1 := by simpa using hχ
  have hL := DirichletCharacter.LFunction_apply_one_ne_zero hi
  have he := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ 1 (Or.inl (by norm_num))
  have hC : χ⁻¹.completedLFunction 1≠0 := by
    intro hz
    rw [he,hz,zero_div] at hL
    exact hL rfl
  have hfe := hp.completedLFunction_one_sub 1
  norm_num only [sub_self] at hfe
  rw [hfe]
  exact mul_ne_zero (mul_ne_zero
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne q))))
    (primitive_rootNumber_ne_zero q χ hp)) hC

lemma gammaR_inverse_factorization (s : ℂ) :
    (Gammaℝ s)⁻¹=s*(Gammaℝ (s+2))⁻¹/(2*(Real.pi : ℂ)) := by
  by_cases hs : s=0
  · subst s
    have hg : Gammaℝ (0 : ℂ)=0 := Gammaℝ_eq_zero_iff.mpr ⟨0,by norm_num⟩
    simp [hg]
  · rw [Gammaℝ_add_two hs]
    by_cases hg : Gammaℝ s=0
    · simp [hg]
    · field_simp
      <;> ring

theorem primitive_nonprincipal_trivial_zero_order_le_one (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive) (hχ : χ≠1) :
    analyticOrderNatAt χ.LFunction (0 : ℂ)≤1 := by
  have hq : q≠1 := by
    intro hq
    subst q
    exact hχ (Subsingleton.elim _ _)
  have hC := primitive_nonprincipal_completedLFunction_zero_ne_zero q χ hp hχ
  rcases χ.even_or_odd with hev | hod
  · let g : ℂ → ℂ := fun s => χ.completedLFunction s*(Gammaℝ (s+2))⁻¹/(2*(Real.pi : ℂ))
    have hg : Differentiable ℂ g :=
      ((DirichletCharacter.differentiable_completedLFunction hχ).mul
        (Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 2))).div_const _
    have hgn : g 0≠0 := by
      dsimp [g]
      exact div_ne_zero (mul_ne_zero hC (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos (by norm_num))))
        (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    have hf : χ.LFunction=fun s => s*g s := by
      funext s
      rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inr hq),
        hev.gammaFactor_def,div_eq_mul_inv,gammaR_inverse_factorization]
      dsimp [g]
      ring
    have h0 : χ.LFunction 0=0 := by rw [hf]; simp
    have hd : deriv χ.LFunction 0=g 0 := by
      rw [hf]
      have h := (hasDerivAt_id (0 : ℂ)).mul (hg 0).hasDerivAt
      have hd' : HasDerivAt (fun s => s*g s) (g 0) 0 := by
        convert! h using 1 <;> simp
      exact hd'.deriv
    have ho := ((DirichletCharacter.differentiable_LFunction hχ).analyticAt (0 : ℂ)).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
      h0 (by rwa [hd])
    simp [analyticOrderNatAt,ho]
  · have h0 : χ.LFunction 0≠0 := by
      rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ 0 (Or.inr hq),
        hod.gammaFactor_def,zero_add,Gammaℝ_one,div_one]
      exact hC
    have ho : analyticOrderNatAt χ.LFunction (0 : ℂ)=0 := by
      by_contra hn
      exact h0 (apply_eq_zero_of_analyticOrderNatAt_ne_zero hn)
    omega

theorem regularized_primitive_trivial_zero_order_le_one (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive) :
    analyticOrderNatAt (if χ=1 then DirichletCharacter.LFunctionTrivChar₁ 1 else χ.LFunction)
      (0 : ℂ)≤1 := by
  by_cases hχ : χ=1
  · rw [if_pos hχ]
    have h0 : DirichletCharacter.LFunctionTrivChar₁ 1 (0 : ℂ)≠0 := by
      rw [DirichletCharacter.LFunctionTrivChar₁,Function.update_of_ne (by norm_num)]
      rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (by norm_num)]
      simp [riemannZeta_zero]
    have ho : analyticOrderNatAt (DirichletCharacter.LFunctionTrivChar₁ 1) (0 : ℂ)=0 := by
      by_contra hn
      exact h0 (apply_eq_zero_of_analyticOrderNatAt_ne_zero hn)
    omega
  · rw [if_neg hχ]
    exact primitive_nonprincipal_trivial_zero_order_le_one q χ hp hχ

end Helfgott
end

open scoped Classical
theorem solution (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive) :
    analyticOrderNatAt (if χ=1 then DirichletCharacter.LFunctionTrivChar₁ 1 else χ.LFunction) (0 : ℂ)≤1 := by
  exact Helfgott.regularized_primitive_trivial_zero_order_le_one q χ hp
#print axioms solution
