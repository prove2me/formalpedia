-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_no_positive_jumps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T20:37:52.313773+00:00
-- url     : https://prove2.me/submissions/03e102ad-8ce8-4688-aa31-39407cfe69b3

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_law_positive_mgf
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_exponent_quadratic_upper
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_adjacent_grid_increments_near_jump
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_grid_increment_tail
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_finite_grid_rare_events
import Mathlib.Analysis.SpecialFunctions.Exp
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P) :
    ∀ᵐ ω ∂P, ∀ (t : ℝ≥0) (l : ℝ), 0 < t →
      Tendsto (fun s => D.X s ω) (nhdsWithin t (Iio t)) (nhds l) → D.X t ω ≤ l := by
  let ψ := tripletLaplace (-D.triplet.drift) D.gaussianCoefficient D.triplet.levyMeasure
  have hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ := by
    intro β t hβ ht
    obtain ⟨hi, he⟩ := source_result81_law_positive_mgf Ω P D t β hβ
    refine ⟨hi, ?_⟩
    change ψ β = Real.log (∫ ω, Real.exp (β * D.X t ω) ∂P) / (t : ℝ)
    rw [he, Real.log_exp, mul_div_cancel_left₀ _ (NNReal.coe_pos.mpr ht).ne']
  obtain ⟨K, _, hK⟩ := source_result81_exponent_quadratic_upper Ω P D ψ hψ
  let r (n : ℕ) : ℝ := (n : ℝ) + 1
  let d (n : ℕ) : ℝ≥0 := (((n : ℝ≥0) + 1) ^ 4)⁻¹
  have hr (n : ℕ) : 1 ≤ r n := le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hd (n : ℕ) : 0 < d n := by dsimp [d]; positivity
  have hrt : Tendsto r atTop atTop :=
    tendsto_atTop_mono (fun n => le_add_of_nonneg_right zero_le_one) tendsto_natCast_atTop_atTop
  have hdt : Tendsto d atTop (𝓝 0) := (NNReal.tendsto_coe (m := d) (x := 0)).1 (by
    simpa [d, r, Function.comp_def] using (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (show (4 : ℕ) ≠ 0 by decide))).comp hrt)
  let cnt (n : ℕ) := (n + 1) ^ 4
  let E (n k : ℕ) : Set Ω := {ω | (r n)⁻¹ ≤
    D.X ((k : ℝ≥0) * d n + d n) ω - D.X ((k : ℝ≥0) * d n) ω}
  have hb : Tendsto (fun n => (cnt n : ℝ) * Real.exp (K - r n)) atTop (𝓝 0) := by
    have he := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4).comp hrt).const_mul (Real.exp K)
    simpa only [cnt, Nat.cast_pow, Nat.cast_add, Nat.cast_one, r, mul_zero, zero_mul, sub_eq_add_neg,
      Real.exp_add, Function.comp_apply, mul_assoc, mul_left_comm, mul_comm] using he
  have hE (n k : ℕ) : P (E n k) ≤ ENNReal.ofReal (Real.exp (K - r n)) :=
    source_result81_grid_increment_tail D K hK ((k : ℝ≥0) * d n) (r n) (hr n) (d n) (by simp [d, r])
  have hae := source_result81_finite_grid_rare_events P E cnt (fun n => Real.exp (K - r n)) hb hE
  filter_upwards [hae, D.levy.cadlag_ae] with ω hω hc
  intro t l ht hl
  by_contra! hj
  obtain ⟨M, hM⟩ := exists_nat_gt t
  apply hω M
  filter_upwards [source_result81_adjacent_grid_increments_near_jump (fun s => D.X s ω) d hd hdt
    (fun n => (r n)⁻¹) (tendsto_inv_atTop_zero.comp hrt) M t l ht hM.le (hc t).1 hl hj] with n hn
  have hceil : ⌈(M : ℝ≥0) / d n⌉₊ = M * (n + 1) ^ 4 := by
    have heq : (M : ℝ≥0) / d n = ((M * (n + 1) ^ 4 : ℕ) : ℝ≥0) := by
      simp only [d, div_inv_eq_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    rw [heq, Nat.ceil_natCast]
  obtain ⟨k, hk, hinc⟩ := hn
  exact ⟨k, hceil ▸ hk, hinc⟩
