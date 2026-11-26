-- Prove2me | solution 1 for Kyprianou.Ch04.subcriticalWeakLimitLaplaceTransform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:47:43.20066+00:00
-- url     : https://prove2.me/submissions/8f44fe8e-8a06-4103-8824-cd9b68b28d8d

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_totalIdleTrafficMaximalRootV1
import Theorems.Thm_Kyprianou_Ch04_bvSubcriticalSecantSlope
import Theorems.Thm_Kyprianou_Ch04_limitingDrawdown_LaplaceTransform
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc
open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The weak limit identifies the Laplace ratio. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift) :
    let M := ∫⁻ y : ℝ, ENNReal.ofReal (-y) ∂L.ν
    let rho := M / ENNReal.ofReal L.drift
    0 < rho → rho < 1 →
    ∀ nu : Measure ℝ, nu (Iio 0) = 0 →
      (∀ f : BoundedContinuousFunction ℝ ℝ,
        Tendsto (fun t : NNReal => ∫ z, f (sSup ((fun s : NNReal => L.X s z) '' Iic t) - L.X t z) ∂P)
          atTop (nhds (∫ x, f x ∂nu))) →
      ∀ a : ℝ, 0 < a → (∫ x, Real.exp (-a*x) ∂nu) = (L.drift-M.toReal)*a/L.ψ a := by
  intro M rho hr0 hr1 nu hnu0 hweak a ha
  let D (t : NNReal) (z : Ω) := sSup ((fun s : NNReal => L.X s z) '' Iic t) - L.X t z
  let f : BoundedContinuousFunction ℝ ℝ :=
    ⟨⟨fun x => Real.exp (-a*max 0 x), by fun_prop⟩, ⟨1, by
      intro x y
      rw [Real.dist_eq]
      have hx := (Real.exp_pos (-a*max 0 x)).le
      have hy := (Real.exp_pos (-a*max 0 y)).le
      have hx' := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha.le) (le_max_left 0 x))
      have hy' := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha.le) (le_max_left 0 y))
      exact abs_le.mpr ⟨by linarith,by linarith⟩⟩⟩
  have hf (x : ℝ) (hx : 0 ≤ x) : f x = Real.exp (-a*x) := by
    change Real.exp (-a*max 0 x) = _
    rw [max_eq_right hx]
  have hD0 (t : NNReal) (z : Ω) : 0 ≤ D t z := by
    apply sub_nonneg.mpr
    have h := levyPath_bddAbove_Icc L z t
    have hs : Icc (0 : NNReal) t = Iic t := by ext x; simp
    rw [hs] at h
    exact le_csSup h ⟨t,by simp,rfl⟩
  have htest := (hweak f).congr' (Eventually.of_forall fun t =>
    integral_congr_ae (Eventually.of_forall fun z => hf (D t z) (hD0 t z)))
  have hnuAE : ∀ᵐ x ∂nu, 0 ≤ x := by
    rw [ae_iff]
    change nu {x | ¬ 0 ≤ x} = 0
    rw [show {x : ℝ | ¬ 0 ≤ x} = Iio 0 from by ext x; simp]
    exact hnu0
  have hEq : (∫ x, f x ∂nu) = ∫ x, Real.exp (-a*x) ∂nu :=
    integral_congr_ae (hnuAE.mono fun x hx => hf x hx)
  rw [hEq] at htest
  have hn := (Kyprianou.Ch04.totalIdleTrafficMaximalRootV1 P F L hBV hd).1
  have hs := (Kyprianou.Ch04.bvSubcriticalSecantSlope P F L hBV hd hr0 hr1).1
  have hLap := Kyprianou.Ch04.limitingDrawdown_LaplaceTransform P F L hn a ha
  rw [hs] at hLap
  exact tendsto_nhds_unique htest hLap
