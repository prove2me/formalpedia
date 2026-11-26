-- Prove2me | solution 1 for Kyprianou.Ch04.negativeExponentIntegerTailBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:25:10.724345+00:00
-- url     : https://prove2.me/submissions/505ec37c-29a2-4d48-a986-eec8a27799e5

import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P F)
    (theta : Real) (htheta : 0 ≤ theta) (n : Nat) :
    P {omega | (n : Real) * (L.ψ theta / 2) ≤ theta * L.X (n : NNReal) omega}
      ≤ (ENNReal.ofReal (Real.exp (L.ψ theta / 2))) ^ n := by
  let u : NNReal := n
  let a : Real := L.ψ theta / 2
  let g : Omega → ENNReal := fun w =>
    ENNReal.ofReal (Real.exp (theta * L.X u w - (n : Real) * a))
  have hm := (chat04_levy_joint_time_state_measurable L).comp
    (measurable_const.prodMk measurable_id : Measurable (fun w : Omega => (u, w)))
  have hg : Measurable g :=
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
      ((measurable_const.mul hm).sub measurable_const))
  have hmark := mul_meas_ge_le_lintegral (μ := P) hg (1 : ENNReal)
  have hsub : {w | (n : Real) * a ≤ theta * L.X u w} ⊆ {w | 1 ≤ g w} := by
    intro w hw
    have hh := ENNReal.ofReal_le_ofReal (Real.one_le_exp (sub_nonneg.mpr hw))
    simpa [g] using hh
  have hi := L.laplace u theta htheta
  have hMoment : (∫⁻ w, ENNReal.ofReal (Real.exp (theta * L.X u w)) ∂P) =
      ENNReal.ofReal (Real.exp ((u : Real) * L.ψ theta)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi.1
      (Eventually.of_forall (fun w => (Real.exp_pos _).le))]
    exact congrArg ENNReal.ofReal hi.2
  have hgInt : (∫⁻ w, g w ∂P) = (ENNReal.ofReal (Real.exp a)) ^ n := by
    calc
      _ = ∫⁻ w, ENNReal.ofReal (Real.exp (-(n : Real) * a)) *
          ENNReal.ofReal (Real.exp (theta * L.X u w)) ∂P := by
        apply lintegral_congr
        intro w
        dsimp [g]
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
        congr 2
        ring
      _ = ENNReal.ofReal (Real.exp (-(n : Real) * a)) *
          ENNReal.ofReal (Real.exp ((u : Real) * L.ψ theta)) := by
        rw [lintegral_const_mul, hMoment]
        exact ENNReal.measurable_ofReal.comp
          (Real.continuous_exp.measurable.comp (measurable_const.mul hm))
      _ = (ENNReal.ofReal (Real.exp a)) ^ n := by
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add,
          ← ENNReal.ofReal_pow (Real.exp_nonneg _) n, ← Real.exp_nat_mul]
        congr 2
        dsimp [u, a]
        push_cast
        ring
  exact (measure_mono hsub).trans (by simpa [hgInt] using hmark)
