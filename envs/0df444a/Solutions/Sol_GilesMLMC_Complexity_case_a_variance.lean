-- Prove2me | solution 1 for GilesMLMC.Complexity.case_a_variance
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:36:12.693748+00:00
-- url     : https://prove2.me/submissions/fdd6414d-1225-4e9a-803e-b5f27090e589

import Mathlib
import Definitions.Def_GilesMLMC_Complexity_Setup
import Definitions.Def_GilesMLMC_Complexity_Choices

set_option autoImplicit false
open GilesMLMC.Complexity

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (M : ℕ) (hM : 2 ≤ M) (T : ℝ) (hT : 0 < T)
    (β c₂ : ℝ) (hβ : β = 1) (hc₂ : 0 < c₂)
    (Y : ℕ → ℕ → Ω → ℝ)
    (hY : ∀ l N, 1 ≤ N → MeasureTheory.MemLp (Y l N) 2 μ)
    (h_iii : ∀ l N, 1 ≤ N →
      ProbabilityTheory.variance (Y l N) μ ≤ c₂ * (N : ℝ)⁻¹ * h M T l ^ β)
    (h_indep : ∀ N : ℕ → ℕ, (∀ l, 1 ≤ N l) →
      ProbabilityTheory.iIndepFun (fun l => Y l (N l)) μ)
    (ε : ℝ) (hε : 0 < ε) (L : ℕ) :
    ProbabilityTheory.variance (estimator Y (NA M T c₂ ε L) L) μ ≤ ε ^ 2 / 2 := by
  subst hβ
  have hMr : (0 : ℝ) < M := by
    have : (2 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  have hh : ∀ l, 0 < h M T l := by
    intro l; unfold h; positivity
  have hε2 : ε ^ (-2 : ℝ) = (ε ^ 2)⁻¹ := by
    rw [Real.rpow_neg hε.le, Real.rpow_two]
  have harg : ∀ l, 0 < 2 * ε ^ (-2 : ℝ) * ((L : ℝ) + 1) * c₂ * h M T l := by
    intro l
    have := hh l
    rw [hε2]
    positivity
  have hN1 : ∀ l, 1 ≤ NA M T c₂ ε L l := fun l => Nat.one_le_ceil_iff.mpr (harg l)
  have hNge : ∀ l, 2 * ε ^ (-2 : ℝ) * ((L : ℝ) + 1) * c₂ * h M T l ≤ (NA M T c₂ ε L l : ℝ) :=
    fun l => Nat.le_ceil _
  have hvar : ProbabilityTheory.variance (estimator Y (NA M T c₂ ε L) L) μ =
      ∑ l ∈ Finset.range (L + 1), ProbabilityTheory.variance (Y l (NA M T c₂ ε L l)) μ := by
    have : estimator Y (NA M T c₂ ε L) L =
        ∑ l ∈ Finset.range (L + 1), (fun l => Y l (NA M T c₂ ε L l)) l := by
      funext ω
      simp [estimator, Finset.sum_apply]
    rw [this]
    apply ProbabilityTheory.IndepFun.variance_sum
    · intro l _
      exact hY l _ (hN1 l)
    · intro i _ j _ hij
      exact (h_indep (NA M T c₂ ε L) hN1).indepFun hij
  rw [hvar]
  calc ∑ l ∈ Finset.range (L + 1), ProbabilityTheory.variance (Y l (NA M T c₂ ε L l)) μ
      ≤ ∑ l ∈ Finset.range (L + 1), ε ^ 2 / (2 * ((L : ℝ) + 1)) := by
        apply Finset.sum_le_sum
        intro l _
        have h1 := h_iii l (NA M T c₂ ε L l) (hN1 l)
        rw [Real.rpow_one] at h1
        refine h1.trans ?_
        have hpos := harg l
        have hh' := hh l
        have h2 : c₂ * ((NA M T c₂ ε L l : ℕ) : ℝ)⁻¹ * h M T l =
            c₂ * h M T l / (NA M T c₂ ε L l : ℝ) := by
          rw [div_eq_mul_inv]; ring
        rw [h2]
        calc c₂ * h M T l / (NA M T c₂ ε L l : ℝ)
            ≤ c₂ * h M T l / (2 * ε ^ (-2 : ℝ) * ((L : ℝ) + 1) * c₂ * h M T l) :=
              div_le_div_of_nonneg_left (by positivity) hpos (hNge l)
          _ = ε ^ 2 / (2 * ((L : ℝ) + 1)) := by
              rw [hε2]
              field_simp
    _ = ε ^ 2 / 2 := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        field_simp
