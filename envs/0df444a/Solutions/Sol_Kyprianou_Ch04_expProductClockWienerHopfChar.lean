-- Prove2me | solution 1 for Kyprianou.Ch04.expProductClockWienerHopfChar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T09:50:39.966545+00:00
-- url     : https://prove2.me/submissions/1e1d5b39-bf8e-49b5-b11f-179357d028ad

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_Kyprianou_Ch04_expMeasureComplexTransform
import Theorems.Thm_Kyprianou_Ch04_expProductClockTerminalChar
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_P_exp_clock_sup_drawdown_indepFun
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
import Theorems.Thm_AvramDividend_Classical_levy_positive_root_true_exp_clock_supremum_full_law_ws01d
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (Psi : ℝ → ℂ)
    (hPsi : ∀ (t : NNReal) (theta : ℝ),
      (∫ ω, Complex.exp (Complex.I * (theta : ℂ) * (L.X t ω : ℂ)) ∂P) =
        Complex.exp (-((t : ℝ) : ℂ) * Psi theta))
    (q : ℝ) (hq : 0 < q)
    (phi : ℝ) (hphi : 0 < phi) (hroot : L.ψ phi = q)
    (a b : ℝ) :
    let S : Ω × ℝ → ℝ := fun z => runningSup L z.2.toNNReal z.1
    let D : Ω × ℝ → ℝ := fun z => L.X z.2.toNNReal z.1 - S z
    (∫ z, Complex.exp (Complex.I * (a : ℂ) * (D z : ℂ) +
      Complex.I * (b : ℂ) * (S z : ℂ)) ∂(P.prod (expMeasure q))) =
      ((q : ℂ) * ((phi : ℂ) - Complex.I * (a : ℂ))) /
        ((Psi a + (q : ℂ)) * ((phi : ℂ) - Complex.I * (b : ℂ))) := by
  intro S D
  letI : IsProbabilityMeasure P := L.isProbability
  letI : IsProbabilityMeasure (expMeasure q) := isProbabilityMeasure_expMeasure hq
  let Q := P.prod (expMeasure q)
  let f (c : ℝ) (x : ℝ) : ℂ := Complex.exp (Complex.I * (c : ℂ) * (x : ℂ))
  have hf (c : ℝ) : Measurable (f c) := by dsimp [f]; fun_prop
  have hm := levy_exponential_real_clock_extrema_drawdown_measurable L
  have hs : Measurable S := hm.fst.fst
  have hD : (fun z : Ω × ℝ => -(runningSup L z.2.toNNReal z.1 -
      L.X z.2.toNNReal z.1)) = D := by
    funext z
    exact neg_sub _ _
  have hd : Measurable D := hD ▸ hm.snd.neg
  have hi : IndepFun D S Q := hD ▸
    (avram_ws01e_bt_new_original_P_exp_clock_sup_drawdown_indepFun L q hq).symm.comp
      measurable_neg measurable_id
  have hslaw := levy_positive_root_true_exp_clock_supremum_full_law_ws01d L q hq phi hphi hroot
  have hS (c : ℝ) : (∫ z, f c (S z) ∂Q) =
      (phi : ℂ) / ((phi : ℂ) - Complex.I * (c : ℂ)) := by
    rw [← integral_map hs.aemeasurable (hf c).aestronglyMeasurable]
    change (∫ x, f c x ∂Measure.map S Q) = _
    rw [show Measure.map S Q = expMeasure phi from hslaw]
    exact Kyprianou.Ch04.expMeasureComplexTransform phi hphi (Complex.I * (c : ℂ))
      (by simpa [Complex.mul_re] using hphi)
  have hfactor (c : ℝ) :
      (∫ z, Complex.exp (Complex.I * (a : ℂ) * (D z : ℂ) +
        Complex.I * (c : ℂ) * (S z : ℂ)) ∂Q) =
        (∫ z, f a (D z) ∂Q) * (∫ z, f c (S z) ∂Q) := by
    simp_rw [Complex.exp_add]
    exact hi.integral_fun_comp_mul_comp hd.aemeasurable hs.aemeasurable
      (hf a).aestronglyMeasurable (hf c).aestronglyMeasurable
  have ht := Kyprianou.Ch04.expProductClockTerminalChar P F L Psi hPsi q hq a
  have heq : (∫ z, Complex.exp (Complex.I * (a : ℂ) * (D z : ℂ) +
      Complex.I * (a : ℂ) * (S z : ℂ)) ∂Q) = (q : ℂ) / (Psi a + (q : ℂ)) := by
    rw [← ht]
    apply integral_congr_ae
    filter_upwards [] with z
    congr 1
    dsimp [D]
    push_cast
    ring
  rw [hfactor, hS] at heq
  have hne : (phi : ℂ) - Complex.I * (a : ℂ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp [Complex.sub_re, Complex.mul_re] at hr
    linarith
  have hp : (phi : ℂ) ≠ 0 := by exact_mod_cast hphi.ne'
  have hdval := (eq_div_iff (div_ne_zero hp hne)).2 heq
  rw [hfactor, hS, hdval]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  calc
    _ = ((phi : ℂ)⁻¹ * (phi : ℂ)) *
      ((q : ℂ) * ((phi : ℂ) - Complex.I * (a : ℂ)) *
        (((phi : ℂ) - Complex.I * (b : ℂ))⁻¹ * (Psi a + (q : ℂ))⁻¹)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hp, one_mul]
