-- Prove2me | solution 1 for LanglandsTunnell.ArchPlace.forall_continuous_exists_eq_realCharFun_and_forall_continuous_exists_eq_complexCharFun
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/a06280c9-d2e7-52de-8044-7d94bf0bfac6

import Definitions.Def_LanglandsTunnell_ArchPlace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Algebra.Constructions
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_ArchPlace_forall_continuous_exists_eq_realCharFun_and_forall_continuous_exists_eq_complexCharFun

set_option autoImplicit false

section ExponentialCharacter

set_option autoImplicit false

open Complex intervalIntegral

namespace ExponentialCharacter

private theorem exists_forall_eq_exp_mul_of_continuous (φ : ℝ → ℂ) (hc : Continuous φ) (h0 : φ 0 = 1)
    (hadd : ∀ x y, φ (x + y) = φ x * φ y) : ∃ l : ℂ, ∀ x, φ x = Complex.exp (l * x) := by

  obtain ⟨δ, hδ, hδ'⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ Set.uIcc 0 δ, ‖φ y - 1‖ ≤ 1 / 2 := by
    obtain ⟨ε, hε, hεφ⟩ := Metric.continuousAt_iff.1 (hc.continuousAt (x := 0)) (1 / 2) (by norm_num)
    refine ⟨ε / 2, by positivity, fun y hy => ?_⟩
    rw [Set.uIcc_of_le (by positivity)] at hy
    have : dist y 0 < ε := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hy.1]; linarith [hy.2]
    have h1 := hεφ this
    rw [h0, dist_eq_norm] at h1
    exact h1.le
  set c : ℂ := ∫ y in (0 : ℝ)..δ, φ y with hc_def
  have hint : ∀ a b : ℝ, IntervalIntegrable φ MeasureTheory.volume a b := fun a b =>
    hc.intervalIntegrable a b
  have hc0 : c ≠ 0 := by
    intro hc0
    have hsub : (∫ y in (0 : ℝ)..δ, (φ y - 1)) = c - δ := by
      rw [integral_sub (hint 0 δ) intervalIntegrable_const, integral_const, hc_def]
      congr 1
      rw [sub_zero]
      exact Complex.real_smul.trans (mul_one _)
    have hbound : ‖∫ y in (0 : ℝ)..δ, (φ y - 1)‖ ≤ 1 / 2 * |δ - 0| :=
      norm_integral_le_of_norm_le_const fun y hy => hδ' y (Set.uIoc_subset_uIcc hy)
    rw [hsub, hc0, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs, sub_zero] at hbound
    rw [abs_of_pos hδ] at hbound
    linarith

  set G : ℝ → ℂ := fun u => ∫ y in (0 : ℝ)..u, φ y with hG_def
  have hGd : ∀ u, HasDerivAt G (φ u) u := fun u => hc.integral_hasStrictDerivAt 0 u |>.hasDerivAt
  have hkey : ∀ x, c * φ x = G (x + δ) - G x := by
    intro x
    have h1 : c * φ x = ∫ y in (0 : ℝ)..δ, φ (y + x) :=
      calc c * φ x = ∫ y in (0 : ℝ)..δ, φ y * φ x := (integral_mul_const (φ x) φ).symm
        _ = ∫ y in (0 : ℝ)..δ, φ (y + x) := integral_congr fun y _ => (hadd y x).symm
    rw [h1, integral_comp_add_right (fun y => φ y) x, zero_add, add_comm δ x]
    exact (integral_interval_sub_left (hint 0 (x + δ)) (hint 0 x)).symm
  have hφ_eq : ∀ x, φ x = c⁻¹ * (G (x + δ) - G x) := fun x => by
    rw [← hkey x, inv_mul_cancel_left₀ hc0]
  have hφd : ∀ x, HasDerivAt φ (c⁻¹ * (φ (x + δ) - φ x)) x := by
    intro x
    have h := (((hGd (x + δ)).comp_add_const x δ).sub (hGd x)).const_mul c⁻¹
    refine (h.congr_of_eventuallyEq ?_)
    exact Filter.Eventually.of_forall fun y => hφ_eq y

  set l : ℂ := c⁻¹ * (φ δ - 1) with hl_def
  have hφd' : ∀ x, HasDerivAt φ (l * φ x) x := by
    intro x
    convert hφd x using 1
    rw [hl_def, add_comm, hadd, mul_assoc]
    congr 1
    ring

  have hconst : ∀ x, φ x * Complex.exp (-(l * x)) = 1 := by
    have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => φ x * Complex.exp (-(l * x))) 0 x := by
      intro x
      have he : HasDerivAt (fun x : ℝ => Complex.exp (-(l * x))) (Complex.exp (-(l * x)) * (-l)) x := by
        have h1 : HasDerivAt (fun x : ℝ => -(l * (x : ℂ))) (-l) x := by
          have h__af := ((hasDerivAt_id x).ofReal_comp.const_mul l).neg
          simp at h__af
          exact h__af
        exact h1.cexp
      have := (hφd' x).mul he
      convert this using 1
      · rfl
      · rfl
      ring
    have hdiff : Differentiable ℝ (fun x : ℝ => φ x * Complex.exp (-(l * x))) := fun x =>
      (hd x).differentiableAt
    intro x
    have := is_const_of_deriv_eq_zero hdiff (fun x => (hd x).deriv) x 0
    simpa [h0] using this
  refine ⟨l, fun x => ?_⟩
  have hx := hconst x
  rwa [Complex.exp_neg, mul_inv_eq_one₀ (Complex.exp_ne_zero _)] at hx

end ExponentialCharacter

end ExponentialCharacter

section RealQuasiCharacter

set_option autoImplicit false

open Complex

namespace RealQuasiCharacter

private noncomputable def expUnit (y : ℝ) : ℝˣ := Units.mk0 (Real.exp y) (Real.exp_pos y).ne'

private theorem continuous_expUnit : Continuous expUnit := by
  rw [Units.continuous_iff]
  refine ⟨Real.continuous_exp, ?_⟩
  show Continuous fun y : ℝ => (Real.exp y)⁻¹
  exact Real.continuous_exp.inv₀ fun y => (Real.exp_pos y).ne'

private theorem expUnit_add (x y : ℝ) : expUnit (x + y) = expUnit x * expUnit y := by
  ext; simp [expUnit, Real.exp_add]

private theorem expUnit_zero : expUnit 0 = 1 := by
  ext; simp [expUnit]

private theorem real_value (χ : ℝˣ →* ℂˣ) (l : ℂ) (hl : ∀ y, ((χ (expUnit y) : ℂˣ) : ℂ) = Complex.exp (l * y))
    (a : ZMod 2) (ha : ((χ (-1) : ℂˣ) : ℂ) = (-1) ^ (a.val : ℕ)) (x : ℝˣ) :
    ((χ x : ℂˣ) : ℂ) = (‖(x : ℝ)‖ : ℂ) ^ l * ((x : ℝ) / ‖(x : ℝ)‖ : ℝ) ^ (a.val : ℕ) := by
  have hx0 : (x : ℝ) ≠ 0 := x.ne_zero
  have hpos : 0 < |(x : ℝ)| := abs_pos.2 hx0

  have hexp : Real.exp (Real.log |(x : ℝ)|) = |(x : ℝ)| := Real.exp_log hpos
  have hray : ((χ (expUnit (Real.log |(x : ℝ)|)) : ℂˣ) : ℂ) = (‖(x : ℝ)‖ : ℂ) ^ l := by
    rw [hl, Real.norm_eq_abs, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hpos.ne'),
      ← Complex.ofReal_log (abs_nonneg _), mul_comm]
  rcases lt_or_gt_of_ne hx0 with hneg | hposx
  ·
    have hxeq : x = -1 * expUnit (Real.log |(x : ℝ)|) := by
      ext
      rw [Units.val_mul, Units.val_neg, Units.val_one]
      show (x : ℝ) = -1 * Real.exp (Real.log |(x : ℝ)|)
      rw [hexp, abs_of_neg hneg]
      ring
    have hsign : ((x : ℝ) / ‖(x : ℝ)‖ : ℝ) = -1 := by
      rw [Real.norm_eq_abs, abs_of_neg hneg, div_neg, div_self hx0]
    rw [hsign]
    conv_lhs => rw [hxeq, map_mul, Units.val_mul, ha, hray]
    push_cast
    ring
  · have hxeq : x = expUnit (Real.log |(x : ℝ)|) := by
      ext
      show (x : ℝ) = Real.exp (Real.log |(x : ℝ)|)
      rw [hexp, abs_of_pos hposx]
    have hsign : ((x : ℝ) / ‖(x : ℝ)‖ : ℝ) = 1 := by
      rw [Real.norm_eq_abs, abs_of_pos hposx, div_self hx0]
    rw [hsign]
    conv_lhs => rw [hxeq, hray]
    simp

private theorem exists_eq_realCharFun_of_continuous (χ : ℝˣ →* ℂˣ) (hχ : Continuous χ) :
    ∃ (u : ℂ) (a : ZMod 2), χ = LanglandsTunnell.ArchPlace.realCharFun u a := by

  obtain ⟨l, hl⟩ := ExponentialCharacter.exists_forall_eq_exp_mul_of_continuous (fun y => ((χ (expUnit y) : ℂˣ) : ℂ))
    (Units.continuous_val.comp (hχ.comp continuous_expUnit)) (by simp [expUnit_zero])
    (fun x y => by simp only [expUnit_add, map_mul, Units.val_mul])

  have hsq : ((χ (-1) : ℂˣ) : ℂ) * ((χ (-1) : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, ← map_mul, neg_one_mul, neg_neg, map_one, Units.val_one]
  have hclose : ∀ a : ZMod 2, ((χ (-1) : ℂˣ) : ℂ) = (-1) ^ (a.val : ℕ) →
      χ = LanglandsTunnell.ArchPlace.realCharFun l a := by
    intro a ha
    ext x
    rw [real_value χ l hl a ha x]
    simp [LanglandsTunnell.ArchPlace.realCharFun, LanglandsTunnell.ArchPlace.realSign]
  rcases mul_self_eq_one_iff.1 hsq with h1 | h1
  · exact ⟨l, 0, hclose 0 (by rw [show (0 : ZMod 2).val = 0 from rfl, pow_zero]; exact h1)⟩
  · exact ⟨l, 1, hclose 1 (by rw [show (1 : ZMod 2).val = 1 from rfl, pow_one]; exact h1)⟩

end RealQuasiCharacter

end RealQuasiCharacter

section ComplexQuasiCharacter

set_option autoImplicit false

open Complex

namespace ComplexQuasiCharacter

private noncomputable def posUnit (y : ℝ) : ℂˣ :=
  Units.mk0 ((Real.exp y : ℝ) : ℂ) (Complex.ofReal_ne_zero.mpr (Real.exp_pos y).ne')

private noncomputable def circleUnit (θ : ℝ) : ℂˣ := Units.mk0 (Complex.exp (θ * I)) (Complex.exp_ne_zero _)

private theorem continuous_posUnit : Continuous posUnit := by
  rw [Units.continuous_iff]
  refine ⟨Complex.continuous_ofReal.comp Real.continuous_exp, ?_⟩
  show Continuous fun y : ℝ => (((Real.exp y : ℝ) : ℂ))⁻¹
  exact (Complex.continuous_ofReal.comp Real.continuous_exp).inv₀ fun y =>
    Complex.ofReal_ne_zero.mpr (Real.exp_pos y).ne'

private theorem continuous_circleUnit : Continuous circleUnit := by
  rw [Units.continuous_iff]
  have hc : Continuous fun θ : ℝ => Complex.exp (θ * I) :=
    Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
  refine ⟨hc, ?_⟩
  show Continuous fun θ : ℝ => (Complex.exp (θ * I))⁻¹
  exact hc.inv₀ fun θ => Complex.exp_ne_zero _

private theorem posUnit_add (x y : ℝ) : posUnit (x + y) = posUnit x * posUnit y := by
  ext; simp [posUnit, Real.exp_add]

private theorem posUnit_zero : posUnit 0 = 1 := by
  ext; simp [posUnit]

private theorem circleUnit_add (x y : ℝ) : circleUnit (x + y) = circleUnit x * circleUnit y := by
  ext; simp [circleUnit, add_mul, Complex.exp_add]

private theorem circleUnit_zero : circleUnit 0 = 1 := by
  ext; simp [circleUnit]

private theorem circleUnit_two_pi : circleUnit (2 * Real.pi) = 1 := by
  ext
  simp only [circleUnit, Units.val_mk0, Units.val_one]
  push_cast
  exact Complex.exp_two_pi_mul_I

private theorem eq_posUnit_mul_circleUnit (z : ℂˣ) :
    z = posUnit (Real.log ‖(z : ℂ)‖) * circleUnit (Complex.arg (z : ℂ)) := by
  ext
  simp only [Units.val_mul, posUnit, circleUnit, Units.val_mk0]
  rw [Real.exp_log (norm_pos_iff.mpr z.ne_zero), Complex.norm_mul_exp_arg_mul_I]

private theorem anglePhase_eq_exp (z : ℂˣ) :
    LanglandsTunnell.ArchPlace.anglePhase z = Complex.exp (Complex.arg (z : ℂ) * I) := by
  unfold LanglandsTunnell.ArchPlace.anglePhase
  rw [div_eq_iff (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr z.ne_zero)), mul_comm,
    Complex.norm_mul_exp_arg_mul_I]

private theorem exists_int_of_periodic (l' : ℂ) (h : Complex.exp (l' * ((2 * Real.pi : ℝ) : ℂ)) = 1) :
    ∃ n : ℤ, l' = n * I := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  refine ⟨n, ?_⟩
  have hpi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  push_cast at hn hpi ⊢
  have h2 : l' * (2 * (Real.pi : ℂ)) = (n * I) * (2 * (Real.pi : ℂ)) := by rw [hn]; ring
  exact mul_right_cancel₀ hpi h2

private theorem complex_value (χ : ℂˣ →* ℂˣ) (l : ℂ) (hl : ∀ y, ((χ (posUnit y) : ℂˣ) : ℂ) = Complex.exp (l * y))
    (n : ℤ) (hn : ∀ θ, ((χ (circleUnit θ) : ℂˣ) : ℂ) = Complex.exp ((n * I) * θ)) (z : ℂˣ) :
    ((χ z : ℂˣ) : ℂ) = ((LanglandsTunnell.ArchPlace.complexCharFun (l / 2) n z : ℂˣ) : ℂ) := by
  have hz0 : (0 : ℝ) < ‖(z : ℂ)‖ := norm_pos_iff.mpr z.ne_zero
  conv_lhs => rw [eq_posUnit_mul_circleUnit z, map_mul, Units.val_mul, hl, hn]
  rw [LanglandsTunnell.ArchPlace.complexCharFun_apply]
  rw [anglePhase_eq_exp, ← Complex.exp_int_mul, show (2 : ℂ) * (l / 2) = l by ring,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hz0.ne') l, ← Complex.ofReal_log hz0.le]
  congr 2
  all_goals ring

private theorem exists_eq_complexCharFun_of_continuous (χ : ℂˣ →* ℂˣ) (hχ : Continuous χ) :
    ∃ (u : ℂ) (k : ℤ), χ = LanglandsTunnell.ArchPlace.complexCharFun u k := by
  obtain ⟨l, hl⟩ := ExponentialCharacter.exists_forall_eq_exp_mul_of_continuous (fun y => ((χ (posUnit y) : ℂˣ) : ℂ))
    (Units.continuous_val.comp (hχ.comp continuous_posUnit)) (by simp [posUnit_zero])
    (fun x y => by simp only [posUnit_add, map_mul, Units.val_mul])
  obtain ⟨l', hl'⟩ := ExponentialCharacter.exists_forall_eq_exp_mul_of_continuous
    (fun θ => ((χ (circleUnit θ) : ℂˣ) : ℂ))
    (Units.continuous_val.comp (hχ.comp continuous_circleUnit)) (by simp [circleUnit_zero])
    (fun x y => by simp only [circleUnit_add, map_mul, Units.val_mul])
  have hper : Complex.exp (l' * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
    rw [← hl' (2 * Real.pi)]
    simp [circleUnit_two_pi]
  obtain ⟨n, rfl⟩ := exists_int_of_periodic l' hper
  exact ⟨l / 2, n, MonoidHom.ext fun z => Units.ext (complex_value χ l hl n hl' z)⟩

end ComplexQuasiCharacter

end ComplexQuasiCharacter

open LanglandsTunnell LanglandsTunnell.ArchPlace in
theorem solution
 :
    (∀ χ : ℝˣ →* ℂˣ, Continuous χ → ∃ (u : ℂ) (a : ZMod 2), χ = realCharFun u a) ∧
      (∀ χ : ℂˣ →* ℂˣ, Continuous χ → ∃ (u : ℂ) (k : ℤ), χ = complexCharFun u k) := by
  exact ⟨fun χ hχ => RealQuasiCharacter.exists_eq_realCharFun_of_continuous χ hχ,
      fun χ hχ => ComplexQuasiCharacter.exists_eq_complexCharFun_of_continuous χ hχ⟩

#print axioms solution

end S_LanglandsTunnell_ArchPlace_forall_continuous_exists_eq_realCharFun_and_forall_continuous_exists_eq_complexCharFun
end P2MW
export P2MW.S_LanglandsTunnell_ArchPlace_forall_continuous_exists_eq_realCharFun_and_forall_continuous_exists_eq_complexCharFun (solution)
