-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_scale_from_tilted_potential
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T11:56:20.951239+00:00
-- url     : https://prove2.me/submissions/563a20c4-2dcf-47fb-bd79-9cb79fe09023

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_tilted_cumulative_continuous
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_tilted_cumulative_laplace

open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (ψ : ℝ → ℝ) (q : ℝ) (hroot : IsScaleTransformDomainBridge ψ q)
    (ν : Measure ℝ) (hsupp : ν (Iio (0 : ℝ)) = 0)
    (hfin : ∀ x : ℝ, 0 ≤ x → ν (Iic x) < ⊤)
    (hatom : ∀ x : ℝ, 0 < x → ν {x} = 0)
    (hlap : ∀ s : ℝ, 0 < s →
      (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂ν) =
        ENNReal.ofReal (s / (ψ (Phi ψ q + s) - q))) :
    ∃ w : ℝ → ℝ, IsQScale ψ q w := by
  classical
  have hf (x : ℝ) : ν (Iic x) < ⊤ :=
    (measure_mono (Iic_subset_Iic.mpr (le_max_left x 0))).trans_lt
      (hfin (max x 0) (le_max_right x 0))
  let v (x : ℝ) := (ν (Iic x)).toReal
  have hmono : Monotone v := fun x y hxy =>
    ENNReal.toReal_mono (hf y).ne (measure_mono (Iic_subset_Iic.mpr hxy))
  let W (x : ℝ) := Real.exp (Phi ψ q * x) * v x
  have hΦ : 0 ≤ Phi ψ q := hroot.1.2.1.1
  have hExp : Monotone (fun x : ℝ => Real.exp (Phi ψ q * x)) :=
    Real.exp_monotone.comp (fun _ _ h => mul_le_mul_of_nonneg_left h hΦ)
  have hExpC : Continuous (fun x : ℝ => Real.exp (Phi ψ q * x)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  refine ⟨W, hroot.1, ?_, fun x => mul_nonneg (Real.exp_nonneg _) ENNReal.toReal_nonneg,
    hExpC.continuousOn.mul
      (Kyprianou.Ch08.StageB.source_result81_tilted_cumulative_continuous ν hsupp hf hatom), ?_, ?_⟩
  · intro x hx
    have h : ν (Iic x) = 0 := measure_mono_null
      (fun y hy => (show y ≤ x from hy).trans_lt hx) hsupp
    simp [W, v, h]
  · intro x _ y _ hxy
    exact mul_le_mul (hExp hxy) (hmono hxy) ENNReal.toReal_nonneg (Real.exp_nonneg _)
  · intro β hβ hlt
    exact Kyprianou.Ch08.StageB.source_result81_tilted_cumulative_laplace
      ψ q hroot ν hsupp hf hlap β hβ hlt
