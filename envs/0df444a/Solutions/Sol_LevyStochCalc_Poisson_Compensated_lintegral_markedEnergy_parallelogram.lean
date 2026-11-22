-- Prove2me | solution 1 for LevyStochCalc.Poisson.Compensated.lintegral_markedEnergy_parallelogram
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-22T04:53:31.874483+00:00
-- url     : https://prove2.me/submissions/9bf07352-011b-4906-acac-0189f739a152

import Definitions.Def_LevyStochCalc_Poisson_CompensatedLinear_F000

open MeasureTheory LevyStochCalc.Poisson.Compensated
open scoped NNReal ENNReal
theorem solution {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
    {P : Measure Ω} {ν : Measure E} [SigmaFinite ν] {φ₁ φ₂ : Ω → ℝ → E → ℝ}
    (hm₁ : Measurable fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2)
    (hm₂ : Measurable fun p : Ω × ℝ × E => φ₂ p.1 p.2.1 p.2.2) (T : ℝ) :
    markedEnergy P ν T (fun ω s e => φ₁ ω s e + φ₂ ω s e)
        + markedEnergy P ν T (fun ω s e => φ₁ ω s e - φ₂ ω s e)
      = 2 * markedEnergy P ν T φ₁ + 2 * markedEnergy P ν T φ₂ := by
  let M := P.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν)
  let q (g : Ω → ℝ → E → ℝ) (p : Ω × ℝ × E) : ℝ≥0∞ := (‖g p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞)^2
  have qm {g : Ω → ℝ → E → ℝ} (hm : Measurable fun p : Ω × ℝ × E => g p.1 p.2.1 p.2.2) :
      Measurable (q g) := ((measurable_nnnorm.comp hm).coe_nnreal_ennreal).pow_const 2
  have repr {g : Ω → ℝ → E → ℝ} (hm : Measurable fun p : Ω × ℝ × E => g p.1 p.2.1 p.2.2) :
      markedEnergy P ν T g = ∫⁻ p, q g p ∂M := by
    unfold markedEnergy M
    rw [lintegral_prod _ (qm hm).aemeasurable]
    apply lintegral_congr
    intro ω
    exact (lintegral_prod (μ := volume.restrict (Set.Icc 0 T)) (ν := ν)
      (fun y : ℝ × E => q g (ω, y))
      ((qm hm).comp (measurable_prodMk_left (x := ω))).aemeasurable).symm
  let gp : Ω → ℝ → E → ℝ := fun ω s e => φ₁ ω s e + φ₂ ω s e
  let gm : Ω → ℝ → E → ℝ := fun ω s e => φ₁ ω s e - φ₂ ω s e
  have hp : Measurable (fun p : Ω × ℝ × E => gp p.1 p.2.1 p.2.2) := hm₁.add hm₂
  have hm : Measurable (fun p : Ω × ℝ × E => gm p.1 p.2.1 p.2.2) := hm₁.sub hm₂
  change markedEnergy P ν T gp + markedEnergy P ν T gm = _
  rw [repr hp, repr hm, repr hm₁, repr hm₂, ← lintegral_add_left (qm hp),
    ← lintegral_const_mul 2 (qm hm₁), ← lintegral_const_mul 2 (qm hm₂),
    ← lintegral_add_left (f := fun p => 2 * q φ₁ p) (measurable_const.mul (qm hm₁))]
  apply lintegral_congr
  intro p
  dsimp only [q, gp, gm]
  norm_cast
  apply NNReal.eq
  simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_ofNat,
    coe_nnnorm, Real.norm_eq_abs, sq_abs]
  ring

#print axioms solution
