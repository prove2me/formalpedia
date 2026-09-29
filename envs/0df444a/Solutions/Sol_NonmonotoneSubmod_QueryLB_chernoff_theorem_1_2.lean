-- Prove2me | solution 1 for NonmonotoneSubmod.QueryLB.chernoff_theorem_1_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:46:07.726114+00:00
-- url     : https://prove2.me/submissions/7a7890f4-094e-4208-ac12-9cfbcf8ca142

import Mathlib

open MeasureTheory ProbabilityTheory

namespace NonmonotoneSubmod.QueryLB

theorem aux_chern12_subG {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (hm : Measurable X)
    (hb : ∀ ω, X ω ∈ Set.Icc (-1 : ℝ) 1) (hc : ∫ ω, X ω ∂μ = 0) :
    HasSubgaussianMGF X 1 μ := by
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (μ := μ) (X := X)
    (a := -1) (b := 1) hm.aemeasurable (ae_of_all _ hb) hc
  have h1 : ((‖(1 : ℝ) - (-1)‖₊ / 2) ^ 2 : NNReal) = 1 := by
    apply NNReal.eq
    simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, NNReal.coe_ofNat, NNReal.coe_one]
    norm_num
  rwa [h1] at h

end NonmonotoneSubmod.QueryLB

open MeasureTheory ProbabilityTheory
open NonmonotoneSubmod.QueryLB

theorem solution {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (t : ℕ) (Y : Fin t → Ω → ℝ) (hmeas : ∀ i, Measurable (Y i))
    (hind : iIndepFun Y μ) (hbd : ∀ i ω, Y i ω ∈ Set.Icc (-1 : ℝ) 1)
    (hmean : ∀ i, ∫ ω, Y i ω ∂μ = 0) (lam : ℝ) (hlam : 0 < lam) :
    μ.real {ω | lam < ∑ i, Y i ω} ≤ Real.exp (-(lam ^ 2 / (2 * t))) := by
  have hH := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun (μ := μ) hind (c := fun _ => (1 : NNReal))
    (s := Finset.univ)
    (fun i _ => aux_chern12_subG μ (Y i) (hmeas i) (hbd i) (hmean i)) hlam.le
  have hsub : {ω | lam < ∑ i, Y i ω} ⊆ {ω | lam ≤ ∑ i ∈ Finset.univ, Y i ω} := by
    intro ω (hω : lam < ∑ i, Y i ω)
    exact hω.le
  calc μ.real {ω | lam < ∑ i, Y i ω}
      ≤ μ.real {ω | lam ≤ ∑ i ∈ Finset.univ, Y i ω} := measureReal_mono hsub
    _ ≤ _ := hH
    _ = Real.exp (-(lam ^ 2 / (2 * t))) := by
      congr 1
      simp [neg_div]
