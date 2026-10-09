-- Prove2me | solution 1 for HryniewiczCriterion.gaussLinkingIntegral_comp_mul_nat
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-08T18:37:56.327967+00:00
-- url     : https://prove2.me/submissions/f468ebbe-c905-408b-8d53-41795c2de427

import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Calculus.Deriv.Shift

open HryniewiczCriterion

/-- For a `1`-periodic `g : ℝ → E`, `∫₀ᵏ g = k • ∫₀¹ g` for every `k : ℕ`, with no
integrability hypothesis: if `g` is not integrable on one period, both sides are `0`. -/
theorem Function.Periodic.intervalIntegral_zero_natCast_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} (hg : Function.Periodic g 1) (k : ℕ) :
    ∫ x in (0 : ℝ)..(k : ℝ), g x = (k : ℝ) • ∫ x in (0 : ℝ)..1, g x := by
  by_cases hint : IntervalIntegrable g MeasureTheory.volume 0 1
  · have hall : ∀ t₁ t₂, IntervalIntegrable g MeasureTheory.volume t₁ t₂ :=
      hg.intervalIntegrable₀ one_ne_zero hint
    have h := hg.intervalIntegral_add_zsmul_eq (k : ℤ) 0 hall
    simpa [zero_add, Int.cast_natCast, ← Nat.cast_smul_eq_nsmul ℝ] using h
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    have hnk : ¬ IntervalIntegrable g MeasureTheory.volume 0 (k : ℝ) := by
      intro h
      apply hint
      refine h.mono_set ?_
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      rw [Set.uIcc_of_le zero_le_one, Set.uIcc_of_le (by linarith)]
      exact Set.Icc_subset_Icc_right hk1
    rw [intervalIntegral.integral_undef hint, intervalIntegral.integral_undef hnk, smul_zero]

/-- `volumeIn` is linear in its second vector argument. -/
theorem HryniewiczCriterion.volumeIn_smul_middle (N a b c : R4) (r : ℝ) :
    volumeIn N a (r • b) c = r * volumeIn N a b c := by
  unfold volumeIn
  have h1 : Matrix.of ![-N, a, r • b, c] = (Matrix.of ![-N, a, b, c]).updateRow 2 (r • b) := by
    ext i j; fin_cases i <;> rfl
  have h2 : (Matrix.of ![-N, a, b, c]).updateRow 2 b = Matrix.of ![-N, a, b, c] := by
    ext i j; fin_cases i <;> rfl
  rw [h1, Matrix.det_updateRow_smul, h2]

theorem gl_scale_abstract (N : R4) (A B : ℝ → R4) (hBper : Function.Periodic B 1) (k : ℕ) :
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1,
      volumeIn N (deriv A s) (deriv (fun t => B (k * t)) t) (A s - B (k * t)) /
        euclidNorm (A s - B (k * t)) ^ 3) =
    (k : ℝ) * ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1,
      volumeIn N (deriv A s) (deriv B t) (A s - B t) / euclidNorm (A s - B t) ^ 3 := by
  have hB'per : Function.Periodic (deriv B) 1 := fun t => by
    rw [← deriv_comp_add_const]
    exact congrArg (fun f => deriv f t) (funext hBper)
  have hinner : ∀ s, (∫ t in (0 : ℝ)..1,
      volumeIn N (deriv A s) (deriv (fun t => B (k * t)) t) (A s - B (k * t)) /
        euclidNorm (A s - B (k * t)) ^ 3) =
      (k : ℝ) * ∫ t in (0 : ℝ)..1, volumeIn N (deriv A s) (deriv B t) (A s - B t) /
        euclidNorm (A s - B t) ^ 3 := by
    intro s
    set g : ℝ → ℝ := fun t => volumeIn N (deriv A s) (deriv B t) (A s - B t) /
      euclidNorm (A s - B t) ^ 3 with hg
    have hgper : Function.Periodic g 1 := fun t => by simp only [g, hBper t, hB'per t]
    have hpt : ∀ t, volumeIn N (deriv A s) (deriv (fun t => B (k * t)) t) (A s - B (k * t)) /
        euclidNorm (A s - B (k * t)) ^ 3 = (k : ℝ) * g (k * t) := by
      intro t
      have hd : deriv (fun t => B (k * t)) t = (k : ℝ) • deriv B (k * t) :=
        deriv_comp_mul_left (f := B) (c := (k : ℝ)) (x := t)
      rw [hd, HryniewiczCriterion.volumeIn_smul_middle, hg]
      ring
    simp_rw [hpt]
    rw [intervalIntegral.integral_const_mul]
    have h := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1) g (k : ℝ)
    simp only [smul_eq_mul, mul_zero, mul_one] at h
    rw [h, hgper.intervalIntegral_zero_natCast_eq k, smul_eq_mul]
  simp only [hinner]
  rw [intervalIntegral.integral_const_mul]

theorem gl_scale_main (N : R4) (γ₁ γ₂ : ℝ → R4)
    (hper₂ : ∀ s, γ₂ (s + 1) = γ₂ s) (k : ℕ) :
    gaussLinkingIntegral N γ₁ (fun t => γ₂ (k * t)) = k * gaussLinkingIntegral N γ₁ γ₂ := by
  unfold gaussLinkingIntegral
  have hBper : Function.Periodic (fun t => stereographicFrom N (γ₂ t)) 1 := fun t => by
    simp only [hper₂]
  have h := gl_scale_abstract N (fun s => stereographicFrom N (γ₁ s))
    (fun t => stereographicFrom N (γ₂ t)) hBper k
  rw [h]
  ring

open HryniewiczCriterion

theorem solution (N : R4) (γ₁ γ₂ : ℝ → R4)
    (h₁ : ContDiff ℝ 2 γ₁) (h₂ : ContDiff ℝ 2 γ₂)
    (hper₁ : ∀ s, γ₁ (s + 1) = γ₁ s) (hper₂ : ∀ s, γ₂ (s + 1) = γ₂ s)
    (hunit₁ : ∀ s, euclidNorm (γ₁ s) = 1) (hunit₂ : ∀ s, euclidNorm (γ₂ s) = 1)
    (hdisj : ∀ s t, γ₁ s ≠ γ₂ t) (hN : euclidNorm N = 1) (hNγ : ∀ s, γ₁ s ≠ N ∧ γ₂ s ≠ N)
    (k : ℕ) :
    gaussLinkingIntegral N γ₁ (fun t => γ₂ (k * t)) = k * gaussLinkingIntegral N γ₁ γ₂ :=
  gl_scale_main N γ₁ γ₂ hper₂ k
