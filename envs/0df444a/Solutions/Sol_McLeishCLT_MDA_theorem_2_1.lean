-- Prove2me | solution 1 for McLeishCLT.MDA.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T20:24:52.002331+00:00
-- url     : https://prove2.me/submissions/2a55e108-f0cc-4726-88e6-5393b4218338

import Mathlib
import Definitions.Def_McLeishCLT_MDA_Setting
import Theorems.Thm_McLeishCLT_MDA_eq_2_2

set_option autoImplicit false

namespace McLeishCLT.MDA.Thm21Proof

open MeasureTheory Filter Topology Finset Complex

theorem one_add_I_mul_ne_zero (t : ℝ) : (1 + I * (t : ℂ)) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

/-- `e^{ix} = (1 + ix) exp(-x²/2 + r(x))`. -/
theorem exp_I_eq (x : ℝ) :
    Complex.exp (I * (x : ℂ)) = (1 + I * (x : ℂ)) * Complex.exp (-(x : ℂ) ^ 2 / 2 + remR x) := by
  have hne := one_add_I_mul_ne_zero x
  have h : -(x : ℂ) ^ 2 / 2 + remR x = I * (x : ℂ) - Complex.log (1 + I * (x : ℂ)) := by
    unfold remR
    ring
  rw [h, Complex.exp_sub, Complex.exp_log hne]
  field_simp

variable {Ω : Type*}

/-- `T_n U_n = e^{i t S_n}`. -/
theorem prodT_mul_prodU (k : ℕ → ℕ) (X : ℕ → ℕ → Ω → ℝ) (t : ℝ) (n : ℕ) (ω : Ω) :
    prodT k X t n ω * prodU k X t n ω = Complex.exp ((t : ℂ) * (S k X n ω : ℂ) * I) := by
  unfold prodT prodU
  have hsum : -(t : ℂ) ^ 2 / 2 * ∑ j ∈ range (k n), (X n j ω : ℂ) ^ 2
      + ∑ j ∈ range (k n), remR (X n j ω * t)
      = ∑ j ∈ range (k n), (-((X n j ω * t : ℝ) : ℂ) ^ 2 / 2 + remR (X n j ω * t)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  rw [hsum, Complex.exp_sum, ← Finset.prod_mul_distrib]
  have hS : (t : ℂ) * (S k X n ω : ℂ) * I = ∑ j ∈ range (k n), I * ((X n j ω * t : ℝ) : ℂ) := by
    unfold S
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hS, Complex.exp_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [exp_I_eq]
  congr 1
  push_cast
  ring

end McLeishCLT.MDA.Thm21Proof

open MeasureTheory ProbabilityTheory Filter Topology Finset Complex
  McLeishCLT.MDA McLeishCLT.MDA.Thm21Proof
open scoped ENNReal NNReal

theorem solution {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ → ℕ) (X : ℕ → ℕ → Ω → ℝ)
    (hXm : ∀ n, ∀ j < k n, Measurable (X n j))
    (ha : ∀ t : ℝ, Tendsto (fun n => ∫ ω, prodT k X t n ω ∂P) atTop (𝓝 1))
    (hb : ∀ t : ℝ, UniformIntegrable (fun n => prodT k X t n) 1 P)
    (hc : TendstoInMeasure P (fun n => sumSq k X n) atTop (fun _ => 1))
    (hd : TendstoInMeasure P (fun n => maxAbs k X n) atTop (fun _ => 0)) :
    TendstoInDistribution (fun n => S k X n) atTop (id : ℝ → ℝ) (fun _ => P) (gaussianReal 0 1) := by
  have hSm : ∀ n, Measurable (S k X n) := fun n => by
    unfold S
    exact Finset.measurable_sum _ fun j hj => hXm n j (Finset.mem_range.mp hj)
  refine ⟨fun n => (hSm n).aemeasurable, measurable_id.aemeasurable, ?_⟩
  refine ProbabilityMeasure.tendsto_of_tendsto_charFun fun t => ?_
  show Tendsto (fun n => charFun (P.map (S k X n)) t) atTop
    (𝓝 (charFun ((gaussianReal 0 1).map id) t))
  rw [Measure.map_id, charFun_gaussianReal]
  -- The characteristic function of `S_n` is `E[T_n U_n]`.
  have hchar : ∀ n, charFun (P.map (S k X n)) t = ∫ ω, prodT k X t n ω * prodU k X t n ω ∂P := by
    intro n
    rw [charFun_apply_real, integral_map (hSm n).aemeasurable (by fun_prop)]
    simp_rw [prodT_mul_prodU]
  simp_rw [hchar]
  set c : ℂ := Complex.exp (-(t : ℂ) ^ 2 / 2) with hcdef
  -- Split `E[T U] = E[T (U - c)] + c E[T]`.
  have hTint : ∀ n, Integrable (prodT k X t n) P := fun n => ((hb t).memLp n).integrable le_rfl
  have hTUint : ∀ n, Integrable (fun ω => prodT k X t n ω * prodU k X t n ω) P := by
    intro n
    simp_rw [prodT_mul_prodU]
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (Eventually.of_forall fun ω => ?_)
    rw [Complex.norm_exp]
    simp
  have hsplit : ∀ n, ∫ ω, prodT k X t n ω * prodU k X t n ω ∂P
      = ∫ ω, prodT k X t n ω * (prodU k X t n ω - c) ∂P + c * ∫ ω, prodT k X t n ω ∂P := by
    intro n
    rw [← integral_const_mul, ← integral_add]
    · congr 1
      funext ω
      ring
    · have : (fun ω => prodT k X t n ω * (prodU k X t n ω - c))
          = fun ω => prodT k X t n ω * prodU k X t n ω - c * prodT k X t n ω := by
        funext ω
        ring
      rw [this]
      exact (hTUint n).sub ((hTint n).const_mul c)
    · exact (hTint n).const_mul c
  simp_rw [hsplit]
  -- `E[T (U - c)] → 0` by (2.2), and `c E[T] → c`.
  have h22 := eq_2_2 P k X hXm t (hb t) hc hd
  have hW : Tendsto (fun n => ∫ ω, prodT k X t n ω * (prodU k X t n ω - c) ∂P) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h22)
    refine (norm_integral_le_lintegral_norm _).trans ?_
    simp only [Function.comp_apply]
    rw [eLpNorm_one_eq_lintegral_enorm]
    simp_rw [ofReal_norm]
    rfl
  have hgauss : Complex.exp ((t : ℂ) * ((0 : ℝ) : ℂ) * I - (((1 : ℝ≥0) : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2)
      = c := by
    rw [hcdef]
    congr 1
    push_cast
    ring
  have hfin := hW.add ((ha t).const_mul c)
  rw [zero_add, mul_one] at hfin
  rw [hgauss]
  exact hfin
