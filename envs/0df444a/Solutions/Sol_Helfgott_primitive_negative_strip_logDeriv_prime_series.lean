-- Prove2me | solution 1 for Helfgott.primitive_negative_strip_logDeriv_prime_series
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-05T12:33:25.976526+00:00
-- url     : https://prove2.me/submissions/9ecac54c-51dc-4b1a-aa43-16165cc72ae6

import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.CauchyIntegral

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex

namespace Helfgott

lemma gammaFactor_ne_zero_negative_strip (q : ℕ) (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : -1 < s.re) (hs0 : s.re < 0) : χ.gammaFactor s ≠ 0 := by
  rcases χ.even_or_odd with he | ho
  · rw [he.gammaFactor_def]
    intro hz
    obtain ⟨n,hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp hz
    have hr := congrArg Complex.re hn
    norm_num at hr
    by_cases h : n=0
    · simp [h] at hr
      linarith
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr h)
      linarith
  · rw [ho.gammaFactor_def]
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    simp only [add_re,one_re]
    linarith

lemma primitive_LFunction_ne_zero_negative_strip (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive)
    (s : ℂ) (hs : -1 < s.re) (hs0 : s.re < 0) : χ.LFunction s ≠ 0 := by
  have hright : 1 < (1-s).re := by simp only [sub_re,one_re]; linarith
  have hL : (χ⁻¹).LFunction (1-s) ≠ 0 := by
    rw [DirichletCharacter.LFunction_eq_LSeries _ hright]
    exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re _ hright
  have hsne : s ≠ 0 := by intro h; simp [h] at hs0
  have hrne : 1-s ≠ 0 := by intro h; rw [h] at hright; norm_num at hright
  have hC : (χ⁻¹).completedLFunction (1-s) ≠ 0 := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor _ _ (.inl hrne)] at hL
    exact (div_ne_zero_iff.mp hL).1
  have hpi : (χ⁻¹).IsPrimitive := by
    change (χ⁻¹).conductor=q
    rw [DirichletCharacter.conductor_inv]
    exact hp
  have he := hpi.completedLFunction_one_sub s
  rw [inv_inv] at he
  rw [he] at hC
  have hc : χ.completedLFunction s ≠ 0 := right_ne_zero_of_mul hC
  rw [χ.LFunction_eq_completed_div_gammaFactor s (.inl hsne)]
  exact div_ne_zero hc (gammaFactor_ne_zero_negative_strip q χ s hs hs0)

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set Complex
open scoped Topology

namespace Helfgott

lemma gammaFactor_logDeriv_from_LFunction (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ)
    (hs : s ≠ 0) (hL : χ.LFunction s ≠ 0) :
    logDeriv χ.gammaFactor s=logDeriv χ.completedLFunction s-logDeriv χ.LFunction s := by
  have hdL := DirichletCharacter.differentiable_LFunction hχ
  have hdC := DirichletCharacter.differentiable_completedLFunction hχ
  have hCs : χ.completedLFunction s ≠ 0 := by
    rw [χ.LFunction_eq_completed_div_gammaFactor s (.inl hs)] at hL
    exact (div_ne_zero_iff.mp hL).1
  have he : χ.gammaFactor =ᶠ[𝓝 s] (fun w => χ.completedLFunction w/χ.LFunction w) := by
    filter_upwards [hdL.continuous.continuousAt.eventually_ne hL,
      (continuousAt_id : ContinuousAt (fun w : ℂ => w) s).eventually_ne hs] with w hLw hw
    have hrel := χ.LFunction_eq_completed_div_gammaFactor w (.inl hw)
    have hg : χ.gammaFactor w ≠ 0 := by rw [hrel] at hLw; exact (div_ne_zero_iff.mp hLw).2
    apply (eq_div_iff hLw).mpr
    rw [mul_comm]
    exact ((div_eq_iff hg).mp hrel.symm).symm
  rw [(logDeriv_congr_nhds he).eq_of_nhds,
    logDeriv_div s hCs hL (hdC s) (hdL s)]

lemma primitive_completed_logDeriv_reflection (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive) (hχ : χ ≠ 1)
    (s : ℂ) (hs : -1 < s.re) (hs0 : s.re < 0) :
    logDeriv χ.completedLFunction s+
      logDeriv (χ⁻¹).completedLFunction (1-s)= -log (q : ℂ) := by
  have hχi : χ⁻¹ ≠ 1 := by
    intro h
    apply hχ
    simpa using congrArg (fun χ : DirichletCharacter ℂ q => χ⁻¹) h
  have hpi : (χ⁻¹).IsPrimitive := by
    change (χ⁻¹).conductor=q
    rw [DirichletCharacter.conductor_inv]
    exact hp
  have hright : 1 < (1-s).re := by simp only [sub_re,one_re]; linarith
  have hLs := primitive_LFunction_ne_zero_negative_strip q χ hp s hs hs0
  have hLr := DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ⁻¹) (.inl hχi) hright.le
  have hsne : s ≠ 0 := by intro he; simp [he] at hs0
  have hrne : 1-s ≠ 0 := by intro he; rw [he] at hright; norm_num at hright
  have hCs : χ.completedLFunction s ≠ 0 := by
    rw [χ.LFunction_eq_completed_div_gammaFactor s (.inl hsne)] at hLs
    exact (div_ne_zero_iff.mp hLs).1
  have hCr : (χ⁻¹).completedLFunction (1-s) ≠ 0 := by
    rw [(χ⁻¹).LFunction_eq_completed_div_gammaFactor (1-s) (.inl hrne)] at hLr
    exact (div_ne_zero_iff.mp hLr).1
  let P : ℂ → ℂ := fun w => (q : ℂ)^(w-1/2)
  let ε : ℂ := (χ⁻¹).rootNumber
  have hE : (fun w : ℂ => (χ⁻¹).completedLFunction (1-w))=
      (fun w : ℂ => P w*ε*χ.completedLFunction w) := by
    funext w
    simpa only [inv_inv,P,ε] using hpi.completedLFunction_one_sub w
  have hε : ε ≠ 0 := by
    have he := congrFun hE s
    rw [he] at hCr
    exact right_ne_zero_of_mul (left_ne_zero_of_mul hCr)
  have hP : P s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (.inl (by exact_mod_cast NeZero.ne q))
  have hdP : DifferentiableAt ℂ P s :=
    (differentiableAt_id.sub_const (1/2 : ℂ)).const_cpow (.inl (by exact_mod_cast NeZero.ne q))
  have hdC := DirichletCharacter.differentiable_completedLFunction hχ
  have hdCi := DirichletCharacter.differentiable_completedLFunction hχi
  have hlog := congrArg (fun F : ℂ → ℂ => logDeriv F s) hE
  have hcomp : logDeriv (fun w : ℂ => (χ⁻¹).completedLFunction (1-w)) s=
      -logDeriv (χ⁻¹).completedLFunction (1-s) := by
    change logDeriv ((χ⁻¹).completedLFunction ∘ (fun w : ℂ => 1-w)) s = _
    rw [logDeriv_comp (hdCi (1-s)) ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id)]
    simp
  have hpLog : logDeriv P s=log (q : ℂ) := by
    rw [logDeriv_apply]
    have hd := Complex.deriv_const_cpow (x := s) (differentiableAt_id.sub_const (1/2 : ℂ)) (q : ℂ)
    have hd' : deriv P s=log (q : ℂ)*P s := by simpa [P] using hd
    rw [hd']
    exact mul_div_cancel_right₀ _ hP
  rw [hcomp,logDeriv_mul (f := fun w : ℂ => P w*ε) (g := χ.completedLFunction)
    s (mul_ne_zero hP hε) hCs
    (hdP.mul_const ε) (hdC s),logDeriv_mul_const (f := P) s ε hε,hpLog] at hlog
  linear_combination -hlog

theorem primitive_negative_strip_logDeriv_prime_series
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive)
    (hχ : χ ≠ 1) (s : ℂ) (hs : -1 < s.re) (hs0 : s.re < 0) :
    LSeriesSummable (fun n : ℕ => χ⁻¹ n*(ArithmeticFunction.vonMangoldt n : ℂ)) (1-s) ∧
      -deriv χ.LFunction s/χ.LFunction s = log (q : ℂ)+
        deriv χ.gammaFactor s/χ.gammaFactor s+
        deriv (χ⁻¹).gammaFactor (1-s)/(χ⁻¹).gammaFactor (1-s)-
        LSeries (fun n : ℕ => χ⁻¹ n*(ArithmeticFunction.vonMangoldt n : ℂ)) (1-s) := by
  have hχi : χ⁻¹ ≠ 1 := by
    intro h
    apply hχ
    simpa using congrArg (fun χ : DirichletCharacter ℂ q => χ⁻¹) h
  have hr : 1 < (1-s).re := by simp only [sub_re,one_re]; linarith
  have hec : ((fun n : ℕ => χ⁻¹ n)*(fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)))=
      (fun n : ℕ => χ⁻¹ n*(ArithmeticFunction.vonMangoldt n : ℂ)) := by ext n; rfl
  refine ⟨?_,?_⟩
  · simpa only [hec] using (χ⁻¹).LSeriesSummable_twist_vonMangoldt hr
  · have hLs := primitive_LFunction_ne_zero_negative_strip q χ hp s hs hs0
    have hLr := DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ⁻¹) (.inl hχi) hr.le
    have hsne : s ≠ 0 := by intro he; simp [he] at hs0
    have hrne : 1-s ≠ 0 := by intro he; rw [he] at hr; norm_num at hr
    have hg := gammaFactor_logDeriv_from_LFunction q χ hχ s hsne hLs
    have hgi := gammaFactor_logDeriv_from_LFunction q (χ⁻¹) hχi (1-s) hrne hLr
    have href := primitive_completed_logDeriv_reflection q χ hp hχ s hs hs0
    have hseries := (χ⁻¹).LSeries_twist_vonMangoldt_eq hr
    rw [← (χ⁻¹).deriv_LFunction_eq_deriv_LSeries hr,← (χ⁻¹).LFunction_eq_LSeries hr] at hseries
    simp only [hec] at hseries
    simp only [logDeriv_apply] at hg hgi href
    linear_combination -hg-hgi-href+hseries

end Helfgott
end

open MeasureTheory Filter Set Complex
open scoped Topology

theorem solution (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive)
    (hχ : χ ≠ 1) (s : ℂ) (hs : -1 < s.re) (hs0 : s.re < 0) :
    LSeriesSummable (fun n : ℕ => χ⁻¹ n*(ArithmeticFunction.vonMangoldt n : ℂ)) (1-s) ∧
      -deriv χ.LFunction s/χ.LFunction s = log (q : ℂ)+
        deriv χ.gammaFactor s/χ.gammaFactor s+
        deriv (χ⁻¹).gammaFactor (1-s)/(χ⁻¹).gammaFactor (1-s)-
        LSeries (fun n : ℕ => χ⁻¹ n*(ArithmeticFunction.vonMangoldt n : ℂ)) (1-s) := Helfgott.primitive_negative_strip_logDeriv_prime_series q χ hp hχ s hs hs0

#print axioms solution
