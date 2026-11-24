-- Prove2me | solution 1 for Kyprianou.Ch02.levyLaplaceCharDefectV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:26:58.298475+00:00
-- url     : https://prove2.me/submissions/c958a5ac-bfeb-4350-9fda-11489918e23d

import Mathlib
import Theorems.Thm_ProbabilityTheory_leanlevy_chat24_re_one_sub_charFun_eq_integral
import Theorems.Thm_Kyprianou_Ch02_levyPointwiseCosExpAbsBoundV1
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (f : Ω → ℝ) (hf : AEMeasurable f P) (ξ : ℝ) :
    (1 - charFun (P.map f) ξ).re ≤
      4 * (1 + |ξ|) * (1 - ∫ ω, Real.exp (-|f ω|) ∂P) := by
  let Q := P.map f
  letI : IsProbabilityMeasure Q := Measure.isProbabilityMeasure_map hf
  have hi : Integrable (fun x : ℝ => Real.exp (-|x|)) Q :=
    Integrable.of_bound (by fun_prop) 1 (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg _)))
  have hcos : Integrable (fun x : ℝ => Real.cos (ξ*x)) Q :=
    Integrable.of_bound (by fun_prop) 1 (Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (ξ*x))
  have hh := integral_mono ((integrable_const 1).sub hcos)
    (((integrable_const 1).sub hi).const_mul (4*(1+|ξ|)))
    (Kyprianou.Ch02.levyPointwiseCosExpAbsBoundV1 ξ)
  rw [integral_const_mul] at hh
  change (∫ x, 1 - Real.cos (ξ*x) ∂Q) ≤
    4*(1+|ξ|)*(∫ x, 1 - Real.exp (-|x|) ∂Q) at hh
  rw [integral_sub (integrable_const 1) hi] at hh
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hh
  rw [ProbabilityTheory.leanlevy_chat24_re_one_sub_charFun_eq_integral (μ := Q) ξ]
  have hmap : (∫ x, Real.exp (-|x|) ∂Q) = ∫ ω, Real.exp (-|f ω|) ∂P :=
    integral_map hf (by fun_prop)
  rw [hmap] at hh
  exact hh
