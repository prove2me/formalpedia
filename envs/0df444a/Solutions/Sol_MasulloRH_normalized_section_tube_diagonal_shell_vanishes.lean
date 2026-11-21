-- Prove2me | solution 1 for MasulloRH.normalized_section_tube_diagonal_shell_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T04:00:03.75146+00:00
-- url     : https://prove2.me/submissions/ea8bea6a-37d8-4bcc-ad91-98b6856d6ff6

import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory

theorem solution
    {D K : Type*} [Group D] [Group K] [MeasurableSpace K] (μ : Measure K)
    (U : Subgroup K) (hm : MeasurableSet (U : Set K)) (hv : μ.real (U : Set K) ≠ 0)
    [DecidableEq D] [DecidablePred (fun g : K => g ∈ U)] :
    let w := (μ.real (U : Set K))⁻¹
    let tube := fun (r : D) (h : K) => if r = 1 ∧ h ∈ U then w else 0
    let overlap := fun (ξ : D) (g : K) =>
      ∑' r : D, ∫ h : K, tube r h * tube (r * ξ) (h * g) ∂μ
    (∀ ξ g, overlap ξ g = if ξ = 1 ∧ g ∈ U then w else 0) ∧
    (∀ ξ (f : K → ℝ), ∫ g : K, overlap ξ g * f g ∂μ =
      if ξ = 1 then w * ∫ g in (U : Set K), f g ∂μ else 0) ∧
    ∀ (shell : D → ℝ), shell 1 = 0 → ∀ ξ g, shell ξ * overlap ξ g = 0 := by
  classical
  dsimp only
  let w := (μ.real (U : Set K))⁻¹
  let tube := fun (r : D) (h : K) => if r = 1 ∧ h ∈ U then w else 0
  let overlap := fun (ξ : D) (g : K) =>
    ∑' r : D, ∫ h : K, tube r h * tube (r * ξ) (h * g) ∂μ
  have eval (ξ : D) (g : K) : overlap ξ g = if ξ = 1 ∧ g ∈ U then w else 0 := by
    unfold overlap
    rw [tsum_eq_single (1 : D)]
    · by_cases hξ : ξ = 1
      · subst ξ
        by_cases hg : g ∈ U
        · have hh (h : K) : tube 1 h * tube ((1 : D) * 1) (h * g) =
              (U : Set K).indicator (fun _ => w*w) h := by
            by_cases hh' : h ∈ U
            · simp [tube, hh', U.mul_mem hh' hg]
            · simp [tube, hh']
          simp_rw [hh]
          rw [integral_indicator_const _ hm]
          simp [hg, w, smul_eq_mul, hv]
        · have hh (h : K) : tube 1 h * tube ((1 : D) * 1) (h * g) = 0 := by
            by_cases hh' : h ∈ U
            · have hbad : h * g ∉ U := fun hm' => hg (by simpa using U.mul_mem (U.inv_mem hh') hm')
              simp [tube, hh', hbad]
            · simp [tube, hh']
          simp_rw [hh]
          simp [hg]
      · simp [tube, hξ]
    · intro r hr
      simp [tube, hr]
  change (∀ ξ g, overlap ξ g = _) ∧ (∀ (ξ : D) (f : K → ℝ), (∫ g : K, overlap ξ g * f g ∂μ) = _) ∧ _
  refine ⟨eval, ?_, ?_⟩
  · intro ξ f
    by_cases hξ : ξ = 1
    · subst ξ
      simp_rw [eval]
      simp only [true_and, if_true]
      have he (g : K) : (if g ∈ U then w else 0) * f g =
            w * (U : Set K).indicator f g := by
        by_cases hg : g ∈ U <;> simp [hg]
      simp_rw [he]
      rw [integral_const_mul, integral_indicator hm]
    · simp [eval, hξ]
  · intro shell h ξ g
    change shell ξ * overlap ξ g = 0
    rw [eval]
    by_cases hξ : ξ = 1 <;> simp [hξ, h]
