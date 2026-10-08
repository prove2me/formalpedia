-- Prove2me | solution 1 for Helfgott.primitive_low_zero_locations_of_finite_grh_profile
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-06T03:59:58.35919+00:00
-- url     : https://prove2.me/submissions/7412b07d-f29e-4259-a23d-420986c72d75

import Definitions.Def_Helfgott_PrimitiveLowZeroLocations
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Tactic
open scoped Classical

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex
open scoped Classical
namespace Helfgott
lemma primitive_gammaFactor_ne_zero_in_low_strip (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (ρ : ℂ) (hr : -(1/2 : ℝ)≤ρ.re) (hn : ρ≠0) :
    χ.gammaFactor ρ≠0 := by
  rcases χ.even_or_odd with hev | hod
  · rw [hev.gammaFactor_def]
    intro hz
    obtain ⟨n,he⟩ := Gammaℝ_eq_zero_iff.mp hz
    by_cases hn0 : n=0
    · simp [hn0] at he
      exact hn he
    · have hn1 : (1 : ℝ)≤n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
      have hre := congrArg Complex.re he
      norm_num at hre
      linarith
  · rw [hod.gammaFactor_def]
    exact Gammaℝ_ne_zero_of_re_pos (by simp only [add_re,one_re]; linarith)

lemma regularized_primitive_zero_ne_one (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (ρ : ℂ)
    (hz : (if χ=1 then DirichletCharacter.LFunctionTrivChar₁ 1 else χ.LFunction) ρ=0) : ρ≠1 := by
  intro hρ
  subst ρ
  by_cases hχ : χ=1
  · rw [if_pos hχ] at hz
    exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero 1 hz
  · rw [if_neg hχ] at hz
    exact DirichletCharacter.LFunction_apply_one_ne_zero hχ hz

theorem regularized_primitive_zero_reflection (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive) (ρ : ℂ)
    (hr : -(1/2 : ℝ)≤ρ.re) (hn : ρ≠0)
    (hz : (if χ=1 then DirichletCharacter.LFunctionTrivChar₁ 1 else χ.LFunction) ρ=0) :
    (if χ⁻¹=1 then DirichletCharacter.LFunctionTrivChar₁ 1 else χ⁻¹.LFunction) (1-ρ)=0 := by
  have hρ1 := regularized_primitive_zero_ne_one q χ ρ hz
  have hL : χ.LFunction ρ=0 := by
    by_cases hχ : χ=1
    · have hq : q=1 := by
        change χ.conductor=q at hp
        rw [hχ,DirichletCharacter.conductor_one] at hp
        exact hp.symm
      subst q
      rw [if_pos hχ] at hz
      rw [DirichletCharacter.LFunctionTrivChar₁,Function.update_of_ne hρ1] at hz
      have hh : DirichletCharacter.LFunctionTrivChar 1 ρ=χ.LFunction ρ := by
        subst χ
        rfl
      rw [hh] at hz
      exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hρ1)
    · simpa only [if_neg hχ] using hz
  have hC : χ.completedLFunction ρ=0 := by
    have he := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ ρ (Or.inl hn)
    rw [he] at hL
    exact (div_eq_zero_iff).mp hL |>.resolve_right
      (primitive_gammaFactor_ne_zero_in_low_strip q χ ρ hr hn)
  have hpI : χ⁻¹.IsPrimitive := by
    change (χ⁻¹).conductor=q
    rw [DirichletCharacter.conductor_inv]
    exact hp
  have hCr : χ⁻¹.completedLFunction (1-ρ)=0 := by
    rw [hpI.completedLFunction_one_sub ρ,inv_inv,hC,mul_zero]
  have hsr0 : 1-ρ≠0 := sub_ne_zero.mpr (Ne.symm hρ1)
  have hLr : χ⁻¹.LFunction (1-ρ)=0 := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ (1-ρ) (Or.inl hsr0),hCr,zero_div]
  by_cases hi : χ⁻¹=1
  · have hχ : χ=1 := by simpa using hi
    have hq : q=1 := by
      change χ.conductor=q at hp
      rw [hχ,DirichletCharacter.conductor_one] at hp
      exact hp.symm
    subst q
    rw [if_pos hi]
    have hsr1 : 1-ρ≠1 := by intro he; apply hn; linear_combination -he
    rw [DirichletCharacter.LFunctionTrivChar₁,Function.update_of_ne hsr1]
    have hh : DirichletCharacter.LFunctionTrivChar 1 (1-ρ)=χ⁻¹.LFunction (1-ρ) := by
      rw [hi]
    rw [hh,hLr,mul_zero]
  · simpa only [if_neg hi] using hLr

lemma regularized_primitive_zero_on_critical_line_of_right_exclusion
    (q : ℕ) [NeZero q] (T : ℝ)
    (hb : ∀ (χ : DirichletCharacter ℂ q),χ.IsPrimitive →
      ∀ ρ : ℂ,-(1/2 : ℝ)≤ρ.re → ρ.re≤2 →
      (if χ=1 then DirichletCharacter.LFunctionTrivChar₁ 1 else χ.LFunction) ρ=0 →
      |ρ.im|<T → ρ.re≤1/2)
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive) (ρ : ℂ)
    (hr : -(1/2 : ℝ)≤ρ.re) (hu : ρ.re≤2)
    (hz : (if χ=1 then DirichletCharacter.LFunctionTrivChar₁ 1 else χ.LFunction) ρ=0)
    (ht : |ρ.im|<T) : ρ=0 ∨ ρ.re=1/2 := by
  by_cases hn : ρ=0
  · exact Or.inl hn
  right
  have hupper := hb χ hp ρ hr hu hz ht
  have hpI : χ⁻¹.IsPrimitive := by
    change (χ⁻¹).conductor=q
    rw [DirichletCharacter.conductor_inv]
    exact hp
  have href := regularized_primitive_zero_reflection q χ hp ρ hr hn hz
  have hsr : (1-ρ).re=1-ρ.re := by simp
  have hsi : |(1-ρ).im|=|ρ.im| := by simp
  have hlower := hb χ⁻¹ hpI (1-ρ) (by rw [hsr]; linarith)
    (by rw [hsr]; linarith) href (by rwa [hsi])
  rw [hsr] at hlower
  linarith


end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex
open scoped Classical
namespace Helfgott
lemma regularized_primitive_zero_re_lt_one (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (ρ : ℂ)
    (hz : (if χ=1 then DirichletCharacter.LFunctionTrivChar₁ 1 else χ.LFunction) ρ=0) : ρ.re<1 := by
  by_contra hr
  have hr1 : 1≤ρ.re := le_of_not_gt hr
  by_cases hχ : χ=1
  · simp only [if_pos hχ] at hz
    by_cases hρ : ρ=1
    · subst ρ
      exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero 1 hz
    · have he : DirichletCharacter.LFunctionTrivChar₁ 1 ρ=(ρ-1)*riemannZeta ρ := by
        rw [DirichletCharacter.LFunctionTrivChar₁,Function.update_of_ne hρ,
          DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hρ]
        simp
      rw [he] at hz
      exact (mul_ne_zero (sub_ne_zero.mpr hρ) (riemannZeta_ne_zero_of_one_le_re hr1)) hz
  · simp only [if_neg hχ] at hz
    exact (χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) hr1) hz
lemma regularized_primitive_zero_unregularize (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive) (ρ : ℂ) (hn : ρ≠1)
    (hz : (if χ=1 then DirichletCharacter.LFunctionTrivChar₁ 1 else χ.LFunction) ρ=0) :
    χ.LFunction ρ=0 := by
  by_cases hχ : χ=1
  · have hq : q=1 := by
      change χ.conductor=q at hp
      rw [hχ,DirichletCharacter.conductor_one] at hp
      exact hp.symm
    subst q
    rw [if_pos hχ,DirichletCharacter.LFunctionTrivChar₁,Function.update_of_ne hn] at hz
    have hh : DirichletCharacter.LFunctionTrivChar 1 ρ=χ.LFunction ρ := by subst χ; rfl
    rw [hh] at hz
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hn)
  · simpa only [if_neg hχ] using hz

theorem regularized_primitive_low_zero_locations_of_finite_grh
    (q : ℕ) [NeZero q] (T : ℝ)
    (hgrh : ∀ (ψ : DirichletCharacter ℂ q),ψ.IsPrimitive → ∀ ρ : ℂ,
      0<ρ.re → ρ.re<1 → ψ.LFunction ρ=0 → |ρ.im|<T → ρ.re=1/2)
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive) (ρ : ℂ)
    (hr : -(1/2 : ℝ)≤ρ.re) (hu : ρ.re≤2)
    (hz : (if χ=1 then DirichletCharacter.LFunctionTrivChar₁ 1 else χ.LFunction) ρ=0)
    (ht : |ρ.im|<T) : ρ=0 ∨ ρ.re=1/2 := by
  apply regularized_primitive_zero_on_critical_line_of_right_exclusion q T _ χ hp ρ hr hu hz ht
  intro ψ hψ σ _ _ hσ hheight
  by_cases hl : σ.re≤1/2
  · exact hl
  · have hpos : 0<σ.re := by linarith [lt_of_not_ge hl]
    have hu1 := regularized_primitive_zero_re_lt_one q ψ σ hσ
    have hn1 : σ≠1 := by intro he; simp [he] at hu1
    have hL := regularized_primitive_zero_unregularize q ψ hψ σ hn1 hσ
    exact (hgrh ψ hψ σ hpos hu1 hL hheight).le

lemma primitive_low_zero_locations_of_finite_grh_profile
    (hgrh : ∀ (q : ℕ) [NeZero q] (ψ : DirichletCharacter ℂ q),ψ.IsPrimitive →
      (if Odd q then 2*q else q : ℕ)≤300000 → ∀ ρ : ℂ,
      0<ρ.re → ρ.re<1 → ψ.LFunction ρ=0 →
      |ρ.im|<max (200+75000000/((if Odd q then 2*q else q : ℕ) : ℝ))
        ((10 : ℝ)^8/(q : ℝ)) → ρ.re=1/2) : PrimitiveLowZeroLocations := by
  intro q _ χ hp
  dsimp only
  intro hQ
  have hh := regularized_primitive_low_zero_locations_of_finite_grh q
    (max (200+75000000/((if Odd q then 2*q else q : ℕ) : ℝ)) ((10 : ℝ)^8/(q : ℝ)))
    (fun ψ hψ => hgrh q ψ hψ hQ) χ hp
  constructor
  · intro ρ hr hu hz ht
    exact hh ρ hr hu hz (ht.trans_le (le_max_left _ _))
  · intro ρ hr hu hz ht
    exact hh ρ hr hu hz (ht.trans_le (le_max_right _ _))
end Helfgott

end
open Helfgott
theorem solution
    (hgrh : ∀ (q : ℕ) [NeZero q] (ψ : DirichletCharacter ℂ q),ψ.IsPrimitive →
      (if Odd q then 2*q else q : ℕ)≤300000 → ∀ ρ : ℂ,
      0<ρ.re → ρ.re<1 → ψ.LFunction ρ=0 →
      |ρ.im|<max (200+75000000/((if Odd q then 2*q else q : ℕ) : ℝ))
        ((10 : ℝ)^8/(q : ℝ)) → ρ.re=1/2) : PrimitiveLowZeroLocations := primitive_low_zero_locations_of_finite_grh_profile hgrh
#print axioms solution
