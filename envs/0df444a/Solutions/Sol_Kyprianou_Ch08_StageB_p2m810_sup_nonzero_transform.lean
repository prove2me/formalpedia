-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_sup_nonzero_transform
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:22:50.682282+00:00
-- url     : https://prove2.me/submissions/59f64bf3-832c-4203-bc1a-451b2e087b9c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_source_tilt_derivative
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_sup_joint_scale_balance
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_sup_discounted_record_integral
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Reflected exit reduction. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsFullMomentLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q θ x a : ℝ), 0 ≤ q → 0 < a → 0 ≤ x → x ≤ a →
      Integrable (fun ω => Real.exp (θ * D.X 1 ω)) P →
      let p := q - ψ θ
      let V := tiltedScale θ (W q)
      let Zv := Zscale p V
      let d := derivWithin V (Ici a) a
      d + θ * V a ≠ 0 →
      (∫ ω, reflectedSupJointPayoff D.X q θ x a ω ∂P) =
        Real.exp (-θ*x) * (Zv (a-x) -
          V (a-x) * (p * V a + θ * Zv a) / (d + θ * V a)) := by
  intro Ω mΩ P hP D ψ W hψ hW q θ x a hq ha hx hxa hm
  dsimp only
  intro hne
  have hrel := (p2m810_source_tilt_derivative Ω P D ψ W hψ.1 hW q a θ hq ha).2
  have hd : derivWithin (W q) (Ici a) a ≠ 0 := by
    intro hz
    exact hne (by rw [hrel, hz, mul_zero])
  have hb := p2m810_sup_joint_scale_balance Ω P D ψ W hψ hW
    q θ x a hq ha hx hxa hm hd
  dsimp only at hb
  rw [p2m810_sup_discounted_record_integral Ω P D ψ W hψ.1 hW
    q x a hq ha hx hxa hd] at hb
  rw [hb, hrel]
  have he : Real.exp (-θ*x) * tiltedScale θ (W q) (a-x) =
      Real.exp (-θ*a) * W q (a-x) := by
    unfold tiltedScale
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [mul_sub]
  congr 1
  rw [← mul_div_assoc]
  have hcancel (c : ℝ) :
      c * W q (a-x) / derivWithin (W q) (Ici a) a =
      Real.exp (-θ*x) * (tiltedScale θ (W q) (a-x) * c) /
        (Real.exp (-θ*a) * derivWithin (W q) (Ici a) a) := by
    rw [← mul_assoc, he]
    field_simp [Real.exp_ne_zero (-θ*a), hd] <;> ring
  rw [← mul_div_assoc]
  exact hcancel _
