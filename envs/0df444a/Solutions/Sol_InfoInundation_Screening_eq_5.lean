-- Prove2me | solution 1 for InfoInundation.Screening.eq_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T17:40:53.229669+00:00
-- url     : https://prove2.me/submissions/f34b07a3-7bc0-4137-bf90-f7bfb8f1dce1

import Mathlib
import Definitions.Def_InfoInundation_Screening_Model

set_option autoImplicit false
open MeasureTheory ProbabilityTheory InfoInundation.Screening

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ s : ℝ) (hs : 0 < s) (θ ε : Ω → ℝ) (hθ : Measurable θ) (hε : Measurable ε)
    (hθlaw : P.map θ = gaussianReal μ (s ^ 2).toNNReal)
    (hεlaw : P.map ε = gaussianReal 0 1) (hind : IndepFun θ ε P) (σ : ℝ) :
    P.map (fun ω => θ ω + σ * ε ω) = gaussianReal μ (σ ^ 2 + s ^ 2).toNNReal ∧
      ∀ z : ℝ, likelihood μ s σ z = gaussianPDFReal μ (σ ^ 2 + s ^ 2).toNNReal z := by
  constructor
  · have hE : HasLaw ε (gaussianReal 0 1) P := ⟨hε.aemeasurable, hεlaw⟩
    have h1 := gaussianReal_const_mul hE σ
    have hi : IndepFun θ (fun ω => σ * ε ω) P :=
      hind.comp (φ := id) (ψ := fun x => σ * x) measurable_id (measurable_const_mul σ)
    have h2 := gaussianReal_add_gaussianReal_of_indepFun hi hθlaw h1.map_eq
    have e : (fun ω => θ ω + σ * ε ω) = θ + fun ω => σ * ε ω := rfl
    rw [e, h2]
    congr 1
    · simp
    · apply NNReal.eq
      simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_one, mul_one, Real.coe_toNNReal',
        NNReal.coe_mk]
      rw [max_eq_left (by positivity), max_eq_left (by positivity)]
      ring
  · intro z
    have hw : 0 < σ ^ 2 + s ^ 2 := by positivity
    unfold likelihood psi gaussianPDFReal
    rw [Real.sq_sqrt (by positivity), Real.coe_toNNReal _ hw.le]
    have : Real.sqrt Real.pi * Real.sqrt (2 * (σ ^ 2 + s ^ 2)) = Real.sqrt (2 * Real.pi * (σ ^ 2 + s ^ 2)) := by
      rw [← Real.sqrt_mul Real.pi_pos.le]
      congr 1
      ring
    rw [this, one_div, neg_div]
