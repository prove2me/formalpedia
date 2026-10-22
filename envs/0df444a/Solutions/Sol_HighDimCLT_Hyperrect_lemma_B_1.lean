-- Prove2me | solution 1 for HighDimCLT.Hyperrect.lemma_B_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T09:28:45.022117+00:00
-- url     : https://prove2.me/submissions/827da7dc-fa7c-4514-8a92-fdd11eff8371

import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (φ₁ φ₂ : ℝ → ℝ) (hφ₁ : Monotone φ₁) (hφ₂ : Monotone φ₂)
    (hφ₁0 : ∀ x, 0 ≤ φ₁ x) (hφ₂0 : ∀ x, 0 ≤ φ₂ x)
    (ξ₁ ξ₂ : Ω → ℝ) (hξ₁ : Measurable ξ₁) (hξ₂ : Measurable ξ₂) (hind : IndepFun ξ₁ ξ₂ P)
    (hi₁ : Integrable (fun ω => φ₁ (ξ₁ ω)) P)
    (hi₂ : Integrable (fun ω => φ₂ (ξ₁ ω)) P)
    (hi₃ : Integrable (fun ω => φ₂ (ξ₂ ω)) P)
    (hi₁₁ : Integrable (fun ω => φ₁ (ξ₁ ω) * φ₂ (ξ₁ ω)) P)
    (hi₂₂ : Integrable (fun ω => φ₁ (ξ₂ ω) * φ₂ (ξ₂ ω)) P)
    (hi₁₂ : Integrable (fun ω => φ₁ (ξ₁ ω) * φ₂ (ξ₂ ω)) P) :
    (∫ ω, φ₁ (ξ₁ ω) ∂P) * (∫ ω, φ₂ (ξ₁ ω) ∂P) ≤ ∫ ω, φ₁ (ξ₁ ω) * φ₂ (ξ₁ ω) ∂P ∧
    (∫ ω, φ₁ (ξ₁ ω) ∂P) * (∫ ω, φ₂ (ξ₂ ω) ∂P) ≤
      (∫ ω, φ₁ (ξ₁ ω) * φ₂ (ξ₁ ω) ∂P) + ∫ ω, φ₁ (ξ₂ ω) * φ₂ (ξ₂ ω) ∂P ∧
    ∫ ω, φ₁ (ξ₁ ω) * φ₂ (ξ₂ ω) ∂P ≤
      (∫ ω, φ₁ (ξ₁ ω) * φ₂ (ξ₁ ω) ∂P) + ∫ ω, φ₁ (ξ₂ ω) * φ₂ (ξ₂ ω) ∂P := by
  -- third conjunct: pointwise comparison
  have h3 : ∫ ω, φ₁ (ξ₁ ω) * φ₂ (ξ₂ ω) ∂P ≤
      (∫ ω, φ₁ (ξ₁ ω) * φ₂ (ξ₁ ω) ∂P) + ∫ ω, φ₁ (ξ₂ ω) * φ₂ (ξ₂ ω) ∂P := by
    rw [← integral_add hi₁₁ hi₂₂]
    refine integral_mono hi₁₂ (hi₁₁.add hi₂₂) (fun ω => ?_)
    show φ₁ (ξ₁ ω) * φ₂ (ξ₂ ω) ≤ φ₁ (ξ₁ ω) * φ₂ (ξ₁ ω) + φ₁ (ξ₂ ω) * φ₂ (ξ₂ ω)
    set a := ξ₁ ω
    set b := ξ₂ ω
    have h1 := mul_nonneg (hφ₁0 a) (hφ₂0 a)
    have h2 := mul_nonneg (hφ₁0 b) (hφ₂0 b)
    rcases le_total a b with hab | hab
    · have : φ₁ a * φ₂ b ≤ φ₁ b * φ₂ b :=
        mul_le_mul_of_nonneg_right (hφ₁ hab) (hφ₂0 b)
      linarith
    · have : φ₁ a * φ₂ b ≤ φ₁ a * φ₂ a :=
        mul_le_mul_of_nonneg_left (hφ₂ hab) (hφ₁0 a)
      linarith
  -- second conjunct: independence
  have h2 : (∫ ω, φ₁ (ξ₁ ω) ∂P) * (∫ ω, φ₂ (ξ₂ ω) ∂P) = ∫ ω, φ₁ (ξ₁ ω) * φ₂ (ξ₂ ω) ∂P :=
    (hind.integral_fun_comp_mul_comp hξ₁.aemeasurable hξ₂.aemeasurable
      hφ₁.measurable.aestronglyMeasurable hφ₂.measurable.aestronglyMeasurable).symm
  -- first conjunct: Chebyshev's association inequality
  have h1 : (∫ ω, φ₁ (ξ₁ ω) ∂P) * (∫ ω, φ₂ (ξ₁ ω) ∂P) ≤ ∫ ω, φ₁ (ξ₁ ω) * φ₂ (ξ₁ ω) ∂P := by
    set a : Ω → ℝ := fun ω => φ₁ (ξ₁ ω) with ha
    set b : Ω → ℝ := fun ω => φ₂ (ξ₁ ω) with hb
    have hab : Integrable (fun ω => a ω * b ω) P := hi₁₁
    have hone : Integrable (fun _ : Ω => (1 : ℝ)) P := integrable_const 1
    -- the four terms on the product space
    have t1 : Integrable (fun z : Ω × Ω => (a z.1 * b z.1) * (1 : ℝ)) (P.prod P) :=
      Integrable.mul_prod hab hone
    have t2 : Integrable (fun z : Ω × Ω => a z.1 * b z.2) (P.prod P) :=
      Integrable.mul_prod hi₁ hi₂
    have t3 : Integrable (fun z : Ω × Ω => b z.1 * a z.2) (P.prod P) :=
      Integrable.mul_prod hi₂ hi₁
    have t4 : Integrable (fun z : Ω × Ω => (1 : ℝ) * (a z.2 * b z.2)) (P.prod P) :=
      Integrable.mul_prod hone hab
    have hF : Integrable (fun z : Ω × Ω => (a z.1 - a z.2) * (b z.1 - b z.2)) (P.prod P) := by
      have := ((t1.sub t2).sub t3).add t4
      refine this.congr (Filter.Eventually.of_forall (fun z => ?_))
      simp only [mul_one, one_mul, Pi.add_apply, Pi.sub_apply]
      ring
    have hnn : 0 ≤ ∫ z : Ω × Ω, (a z.1 - a z.2) * (b z.1 - b z.2) ∂(P.prod P) := by
      refine integral_nonneg (fun z => ?_)
      show (0:ℝ) ≤ (a z.1 - a z.2) * (b z.1 - b z.2)
      rcases le_total (ξ₁ z.1) (ξ₁ z.2) with h | h
      · have e1 : a z.1 ≤ a z.2 := hφ₁ h
        have e2 : b z.1 ≤ b z.2 := hφ₂ h
        exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
      · have e1 : a z.2 ≤ a z.1 := hφ₁ h
        have e2 : b z.2 ≤ b z.1 := hφ₂ h
        exact mul_nonneg (by linarith) (by linarith)
    have hexp : ∫ z : Ω × Ω, (a z.1 - a z.2) * (b z.1 - b z.2) ∂(P.prod P)
        = (∫ ω, a ω * b ω ∂P) - (∫ ω, a ω ∂P) * (∫ ω, b ω ∂P)
          - (∫ ω, b ω ∂P) * (∫ ω, a ω ∂P) + (∫ ω, a ω * b ω ∂P) := by
      have e : (fun z : Ω × Ω => (a z.1 - a z.2) * (b z.1 - b z.2))
          = fun z => (((a z.1 * b z.1) * (1 : ℝ) - a z.1 * b z.2) - b z.1 * a z.2)
              + (1 : ℝ) * (a z.2 * b z.2) := by
        funext z; ring
      have u1 : Integrable (fun z : Ω × Ω => (a z.1 * b z.1) * (1 : ℝ) - a z.1 * b z.2) (P.prod P) :=
        t1.sub t2
      have u2 : Integrable (fun z : Ω × Ω =>
          ((a z.1 * b z.1) * (1 : ℝ) - a z.1 * b z.2) - b z.1 * a z.2) (P.prod P) :=
        u1.sub t3
      rw [e, integral_add u2 t4, integral_sub u1 t3, integral_sub t1 t2]
      rw [integral_prod_mul (μ := P) (ν := P) (fun ω => a ω * b ω) (fun _ => (1 : ℝ)),
        integral_prod_mul (μ := P) (ν := P) a b, integral_prod_mul (μ := P) (ν := P) b a,
        integral_prod_mul (μ := P) (ν := P) (fun _ => (1 : ℝ)) (fun ω => a ω * b ω)]
      simp
    rw [hexp] at hnn
    show (∫ ω, a ω ∂P) * (∫ ω, b ω ∂P) ≤ ∫ ω, a ω * b ω ∂P
    nlinarith
  exact ⟨h1, by linarith [h2, h3], h3⟩
