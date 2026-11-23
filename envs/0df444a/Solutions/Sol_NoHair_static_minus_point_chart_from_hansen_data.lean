-- Prove2me | solution 1 for NoHair.static_minus_point_chart_from_hansen_data
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T12:35:28.550358+00:00
-- url     : https://prove2.me/submissions/b2ddb437-79d5-4304-841a-a15e62a42851

import Definitions.Def_NoHair_staticReflectionAndCap
import Definitions.Def_NoHair_staticInvertedEndMetric

open NoHair Set Filter Metric
open scoped Topology ContDiff

noncomputable section

private abbrev X := ADMPoint
private abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ

private lemma qscale (t : X → ℝ) (g : X → Mat) (x v : X) :
    staticChartQuadratic (fun y => t y • g y) x v = t x * staticChartQuadratic g x v := by
  simp only [staticChartQuadratic,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem solution (Ω : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (hg : ∃ (a : StaticMinusPointChart Ω N (fun x : ADMPoint => (((1+N x)^4)/(N x)^2) • h x)) (b : ADMPoint → ℝ),
      b 0 = 0 ∧ ContDiffOn ℝ ∞ b (ball 0 a.radius) ∧ (∀ y ∈ ball 0 a.radius, b y < 1) ∧
      ∀ y ∈ a.change.source, 0 < N (a.change y) ∧
        b y = ((1-N (a.change y))/(1+N (a.change y)))^2) :
    Nonempty (StaticMinusPointChart Ω N h) := by
  obtain ⟨a,b,_,smooth,less,data⟩ := hg
  let t := fun y : X => (1-b y)^2 / 16
  have ts : ContDiffOn ℝ ∞ t (ball 0 a.radius) :=
    ((contDiffOn_const.sub smooth).pow 2).div_const _
  refine ⟨{ radius := a.radius, positive := a.positive, change := a.change, source := a.source,
            inside := a.inside, smoothChange := a.smoothChange, smoothInverse := a.smoothInverse,
            tendsOut := a.tendsOut, tendsIn := a.tendsIn, coversInfinity := a.coversInfinity,
            coeff := fun y => t y • a.coeff y, smooth := fun i j => ts.mul (a.smooth i j),
            definite := ?_, pullsBack := ?_ }⟩
  · intro y hy
    exact (a.definite y hy).smul (div_pos (sq_pos_of_pos (sub_pos.mpr (less y hy))) (by norm_num : (0:ℝ)<16))
  · intro y hy v
    rw [qscale,a.pullsBack y hy v]
    obtain ⟨npos,beq⟩ := data y hy
    have cancel : t y * ((1+N (a.change y))^4 / N (a.change y)^2) = 1 := by
      dsimp [t]
      rw [beq]
      field_simp [npos.ne',show (1+N (a.change y))≠0 by linarith] <;> ring
    have hquad (w:X) : t y *
        staticChartQuadratic (staticPositiveMetric (fun z => -N z)
          (fun z => ((1+N z)^4/N z^2) • h z)) (a.change y) w =
          staticChartQuadratic (staticPositiveMetric (fun z => -N z) h) (a.change y) w := by
      simp only [staticChartQuadratic,staticPositiveMetric,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      linear_combination (((1 + -N (a.change y))/2)^4 * h (a.change y) i j * w i * w j) * cancel
    exact hquad _
