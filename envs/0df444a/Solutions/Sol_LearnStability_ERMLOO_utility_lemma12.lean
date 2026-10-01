-- Prove2me | solution 1 for LearnStability.ERMLOO.utility_lemma12
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T17:35:28.803629+00:00
-- url     : https://prove2.me/submissions/7a516a90-8d33-4ebc-b13e-c51dfe6f5edd

import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic
open MeasureTheory ProbabilityTheory Finset
namespace CLearnERM
theorem abs_mean_le_sqrt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : MemLp Y 2 P) :
    (∫ ω,|Y ω| ∂P) ≤ Real.sqrt (∫ ω,(Y ω)^2 ∂P) := by
  have hAbs : MemLp (fun ω=>|Y ω|) 2 P := by simpa only [Real.norm_eq_abs] using hY.norm
  have hv:=variance_nonneg (fun ω=>|Y ω|) P
  rw [variance_eq_sub hAbs] at hv
  change 0 ≤ (∫ ω,|Y ω|^2 ∂P)-(∫ ω,|Y ω| ∂P)^2 at hv
  simp_rw [sq_abs] at hv
  have hn : 0 ≤ ∫ ω,(Y ω)^2 ∂P := integral_nonneg (fun ω=>sq_nonneg _)
  have hs:=Real.sq_sqrt hn
  have hs0:=Real.sqrt_nonneg (∫ ω,(Y ω)^2 ∂P)
  nlinarith

end CLearnERM

theorem solution {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : ℕ} (hm : 1 ≤ m) (X : Fin m → Ω → ℝ) (B : ℝ)
    (hmeas : ∀ i, Measurable (X i))
    (hindep : iIndepFun X μ)
    (hident : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hB : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ B) :
    ∫ ω, |(∑ i, X i ω) / m - ∫ ω', (∑ i, X i ω') / m ∂μ| ∂μ ≤ B / Real.sqrt m := by
  classical
  have hB0 : 0 ≤ B := by
    obtain ⟨ω,hω⟩:=(hB ⟨0,by omega⟩).exists
    exact (abs_nonneg _).trans hω
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hmn : (m : ℝ) ≠ 0 := ne_of_gt hm0
  have hi2 (i : Fin m) : MemLp (X i) 2 μ :=
    MemLp.of_bound (hmeas i).aestronglyMeasurable B ((hB i).mono (fun ω hω=>by simpa only [Real.norm_eq_abs] using hω))
  let Y (ω : Ω) := (∑ i,X i ω)/(m : ℝ)
  have hY2 : MemLp Y 2 μ := by
    simpa only [Y,div_eq_mul_inv] using (memLp_finsetSum univ (fun i _=>hi2 i)).mul_const ((m : ℝ)⁻¹)
  have hsum : variance (fun ω=>∑ i,X i ω) μ ≤ (m : ℝ)*B^2 := by
    have hv:=IndepFun.variance_sum (s:=univ) (X:=X) (fun i _=>hi2 i)
      (fun i _ j _ hij=>hindep.indepFun hij)
    have he : (∑ i,X i)=(fun ω=>∑ i,X i ω) := by ext ω;simp
    rw [he] at hv
    rw [hv]
    calc
      (∑ i,variance (X i) μ) ≤ ∑ _ : Fin m,B^2 := by
        apply Finset.sum_le_sum
        intro i hi
        apply (variance_le_expectation_sq (hi2 i).aestronglyMeasurable).trans
        calc
          (∫ ω,(X i ω)^2 ∂μ) ≤ ∫ _ : Ω,B^2 ∂μ := by
            apply integral_mono_ae (hi2 i).integrable_sq (integrable_const _)
            filter_upwards [hB i] with ω hω
            nlinarith [sq_abs (X i ω),abs_nonneg (X i ω)]
          _=B^2 := by simp
      _=(m : ℝ)*B^2 := by simp
  have hvY : variance Y μ ≤ B^2/(m : ℝ) := by
    have he : Y=(fun ω=>(∑ i,X i ω)*(m : ℝ)⁻¹) := by funext ω;rfl
    rw [he,variance_mul_const]
    calc
      variance (fun ω=>∑ i,X i ω) μ*((m : ℝ)⁻¹)^2 ≤ (m : ℝ)*B^2*((m : ℝ)⁻¹)^2 := by gcongr
      _=B^2/(m : ℝ) := by field_simp
  have hZ2:=hY2.sub (memLp_const (∫ ω,Y ω ∂μ))
  have hsq : (∫ ω,(Y ω-∫ ω',Y ω' ∂μ)^2 ∂μ)=variance Y μ :=
    (variance_eq_integral hY2.aemeasurable).symm
  calc
    _ ≤ Real.sqrt (∫ ω,(Y ω-∫ ω',Y ω' ∂μ)^2 ∂μ) := CLearnERM.abs_mean_le_sqrt _ _ hZ2
    _ ≤ Real.sqrt (B^2/(m : ℝ)) := by rw [hsq];exact Real.sqrt_le_sqrt hvY
    _=B/Real.sqrt m := by rw [Real.sqrt_div (sq_nonneg B),Real.sqrt_sq_eq_abs,abs_of_nonneg hB0]
