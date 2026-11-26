-- Prove2me | solution 1 for Kyprianou.Ch04.cor412_perpetual_transform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:31:36.540894+00:00
-- url     : https://prove2.me/submissions/1d35a946-53bc-4dfc-91f1-8a2ca260cc32

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_runningInfimumExpRewardProperties
import Theorems.Thm_Kyprianou_Ch04_pathRunningInfimumLimit
import Theorems.Thm_Kyprianou_Ch04_nonSingularInfimumTransform
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (hbounded : ∀ᵐ w ∂P, BddBelow (range (fun t : NNReal => L.X t w)))
    (hNotAnti : ¬ (∀ᵐ w ∂P, Antitone (fun t : NNReal => L.X t w)))
    (β : ℝ) (hβ : 0 < β) (hψ : L.ψ β ≠ 0) :
    (∫ w, Real.exp (β * sInf (range (fun t => L.X t w))) ∂P) =
      max 0 (sInf ((fun b : ℝ => L.ψ b / b) '' Ioi 0)) * β / L.ψ β := by
  letI : IsProbabilityMeasure P := L.isProbability
  let g : NNReal × Ω → ℝ := fun z =>
    Real.exp (β * sInf ((fun t => L.X t z.2) '' Iic z.1))
  obtain ⟨hg, hg0, hg1, _⟩ :=
    Kyprianou.Ch04.runningInfimumExpRewardProperties P F L β hβ
  have hpoint : ∀ᵐ w ∂P, Tendsto (fun t : NNReal => g (t,w)) atTop
      (𝓝 (Real.exp (β * sInf (range (fun t => L.X t w))))) := by
    filter_upwards [hbounded] with w hw
    have h := Kyprianou.Ch04.pathRunningInfimumLimit (fun t => L.X t w) hw
    exact (Real.continuous_exp.tendsto _).comp (tendsto_const_nhds.mul h)
  have hdom := tendsto_integral_filter_of_dominated_convergence
    (fun _ : Ω => (1 : ℝ))
    (Eventually.of_forall fun t =>
      (hg.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    (Eventually.of_forall fun t => Eventually.of_forall fun w => by
      change ‖g (t,w)‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (hg0 (t,w))]
      exact hg1 (t,w))
    (integrable_const 1) hpoint
  exact tendsto_nhds_unique hdom
    (Kyprianou.Ch04.nonSingularInfimumTransform P F L hNotAnti β hβ hψ)
