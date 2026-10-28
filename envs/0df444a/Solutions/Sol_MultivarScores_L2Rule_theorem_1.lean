-- Prove2me | solution 1 for MultivarScores.L2Rule.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T09:57:24.284695+00:00
-- url     : https://prove2.me/submissions/6f2411ed-51d7-4adb-b5cd-0da274ad07f5

import Mathlib
import Definitions.Def_MultivarScores_L2Rule_Setting
import Theorems.Thm_MultivarScores_L2Rule_divergence_eq
import Theorems.Thm_MultivarScores_L2Rule_S_eq_S_prime_add
import Theorems.Thm_MultivarScores_L2Rule_smooth_ae_eq_of_L2div_eq_zero

open MeasureTheory MultivarScores.L2Rule

theorem solution {d : ℕ} (w h : E d → ℝ) (𝒱 : Set (Measure (E d)))
    (hA : Assumption1 w h 𝒱) :
    (∀ PX ∈ 𝒱, ∀ PY ∈ 𝒱,
      (∫ y, S PX w h y ∂PY) - (∫ y, S PY w h y ∂PY) = L2div PX PY w h ∧
      (∫ y, S' PX w h y ∂PY) - (∫ y, S' PY w h y ∂PY) = L2div PX PY w h) ∧
    (∀ PX ∈ 𝒱, ∀ PY ∈ 𝒱,
      (∫ y, S PY w h y ∂PY) ≤ (∫ y, S PX w h y ∂PY) ∧
      (∫ y, S' PY w h y ∂PY) ≤ (∫ y, S' PX w h y ∂PY)) ∧
    ((∀ᵐ z, h z ≠ 0) → Characterizes w 𝒱 → ∀ PX ∈ 𝒱, ∀ PY ∈ 𝒱, PX ≠ PY →
      (∫ y, S PY w h y ∂PY) < (∫ y, S PX w h y ∂PY) ∧
      (∫ y, S' PY w h y ∂PY) < (∫ y, S' PX w h y ∂PY)) := by
  -- The S' divergence equals the S divergence.
  have hS'S : ∀ PX ∈ 𝒱, ∀ PY ∈ 𝒱,
      (∫ y, S' PX w h y ∂PY) - (∫ y, S' PY w h y ∂PY) =
        (∫ y, S PX w h y ∂PY) - (∫ y, S PY w h y ∂PY) := by
    intro PX hPX PY hPY
    haveI := hA.isProb PY hPY
    have iW : Integrable (fun y => ∫ z, w (z - y) ^ 2 * h z) PY :=
      (hA.sq_w_prod PY hPY).integral_prod_left
    have iS' : ∀ P ∈ 𝒱, Integrable (fun y => S' P w h y) PY := by
      intro P hP
      have iC : Integrable (fun y => ∫ z, smooth P w z * w (z - y) * h z) PY :=
        (hA.cross_prod P hP PY hPY).integral_prod_left
      exact (integrable_const _).sub (iC.const_mul 2)
    have key : ∀ P ∈ 𝒱, ∫ y, S P w h y ∂PY =
        (∫ y, S' P w h y ∂PY) + ∫ y, (∫ z, w (z - y) ^ 2 * h z) ∂PY := by
      intro P hP
      have e : (fun y => S P w h y) = fun y => S' P w h y + ∫ z, w (z - y) ^ 2 * h z :=
        funext fun y => S_eq_S_prime_add P w h y (hA.sq_smooth P hP) (hA.sq_w y)
          (hA.cross P hP y)
      rw [e, integral_add (iS' P hP) iW]
    rw [key PX hPX, key PY hPY]
    ring
  have hdiv : ∀ PX ∈ 𝒱, ∀ PY ∈ 𝒱,
      (∫ y, S PX w h y ∂PY) - (∫ y, S PY w h y ∂PY) = L2div PX PY w h ∧
        0 ≤ L2div PX PY w h :=
    fun PX hPX PY hPY => divergence_eq w h 𝒱 hA PX PY hPX hPY
  refine ⟨?_, ?_, ?_⟩
  · intro PX hPX PY hPY
    exact ⟨(hdiv PX hPX PY hPY).1, (hS'S PX hPX PY hPY).trans (hdiv PX hPX PY hPY).1⟩
  · intro PX hPX PY hPY
    obtain ⟨h1, h2⟩ := hdiv PX hPX PY hPY
    have h3 := hS'S PX hPX PY hPY
    constructor <;> linarith
  · intro hne hchar PX hPX PY hPY hXY
    obtain ⟨h1, h2⟩ := hdiv PX hPX PY hPY
    have h3 := hS'S PX hPX PY hPY
    have hpos : 0 < L2div PX PY w h := by
      rcases h2.lt_or_eq with hlt | heq
      · exact hlt
      · exfalso
        haveI := hA.isProb PY hPY
        haveI := hA.isProb PX hPX
        have hsm : ∀ (P : Measure (E d)) [IsProbabilityMeasure P], Measurable (smooth P w) := by
          intro P _
          have : Measurable (fun p : E d × E d => w (p.1 - p.2)) :=
            hA.measurable_w.comp (measurable_fst.sub measurable_snd)
          exact (this.stronglyMeasurable.integral_prod_right').measurable
        have hint : Integrable (fun z => (smooth PX w z - smooth PY w z) ^ 2 * h z) := by
          have hb : Integrable
              (fun z => 2 * (smooth PX w z ^ 2 * h z) + 2 * (smooth PY w z ^ 2 * h z)) :=
            ((hA.sq_smooth PX hPX).const_mul 2).add ((hA.sq_smooth PY hPY).const_mul 2)
          refine hb.mono' ?_ ?_
          · exact ((((hsm PX).sub (hsm PY)).pow_const 2).mul
              hA.measurable_h).aestronglyMeasurable
          · refine Filter.Eventually.of_forall fun z => ?_
            have hh := hA.h_nonneg z
            rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hh)]
            have : (smooth PX w z - smooth PY w z) ^ 2 ≤
                2 * smooth PX w z ^ 2 + 2 * smooth PY w z ^ 2 := by
              nlinarith [sq_nonneg (smooth PX w z + smooth PY w z)]
            nlinarith [mul_le_mul_of_nonneg_right this hh]
        have hae := smooth_ae_eq_of_L2div_eq_zero PX PY w h hA.h_nonneg hne hint heq.symm
        exact hXY (hchar PX hPX PY hPY hae)
    constructor <;> linarith
