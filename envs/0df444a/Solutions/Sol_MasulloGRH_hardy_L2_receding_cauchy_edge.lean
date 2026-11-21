-- Prove2me | solution 1 for MasulloGRH.hardy_L2_receding_cauchy_edge
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T04:42:50.381529+00:00
-- url     : https://prove2.me/submissions/dd0ab8ca-b5f0-4ee8-b6c4-d0830c7e4b72

import Definitions.Def_MasulloGRH_MellinRpos
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Set MeasureTheory Filter Topology

namespace MasulloGRH
private theorem nf_cauchy_kernelL2 (u : ℝ) (z : ℂ) (hu : u < z.re) :
    let K := fun y : ℝ => ‖((u:ℂ)+(y:ℂ)*Complex.I-z)⁻¹‖
    MemLp K 2 volume ∧ (∫ y : ℝ, (K y)^2) = Real.pi/(z.re-u) := by
  intro K
  let d := z.re-u
  have hd : 0 < d := sub_pos.mpr hu
  let J (v : ℝ) := (1+v^2)⁻¹
  have hJ : Integrable J := integrable_inv_one_add_sq
  have hraw (y : ℝ) : (K y)^2 = d⁻¹^2 * J (d⁻¹*(y-z.im)) := by
    simp only [K,norm_inv,inv_pow,Complex.sq_norm]
    rw [Complex.normSq_apply]
    simp [J,Complex.mul_re,Complex.mul_im]
    rw [← mul_inv]
    congr 1
    field_simp [hd.ne']
    dsimp [d]
    ring
  have heq : (fun y : ℝ => (K y)^2) = (fun y : ℝ => d⁻¹^2 * J (d⁻¹*(y-z.im))) := funext hraw
  have hcontinuous : Continuous K := by
    have hn (y:ℝ) : (u:ℂ)+(y:ℂ)*Complex.I-z ≠ 0 := by
      intro he
      have hh := congrArg Complex.re he
      simp at hh
      linarith
    dsimp [K]
    fun_prop (disch := exact hn _)
  constructor
  · apply (memLp_two_iff_integrable_sq hcontinuous.aestronglyMeasurable).mpr
    rw [heq]
    exact ((hJ.comp_mul_left' (inv_ne_zero hd.ne')).comp_sub_right z.im).const_mul _
  · rw [heq, integral_const_mul, integral_sub_right_eq_self (fun t => J (d⁻¹*t)) z.im,
      Measure.integral_comp_inv_mul_left, abs_of_pos hd, smul_eq_mul]
    have hval : ∫ y, J y = Real.pi := integral_univ_inv_one_add_sq
    rw [hval]
    dsimp [d]
    field_simp

private theorem nf_cauchy_HardyL2_bound (Φ : ℂ → ℂ) (u : ℝ) (z : ℂ)
    (hu : u < z.re) (hL : MemLp (fun y : ℝ => Φ (u+y*Complex.I)) 2 volume) :
    ‖verticalLineIntegral (fun s => Φ s/(s-z)) u‖ ≤
      Real.sqrt (∫ y : ℝ, ‖Φ (u+y*Complex.I)‖^2) * Real.sqrt (Real.pi/(z.re-u)) := by
  let K := fun y : ℝ => ‖((u:ℂ)+(y:ℂ)*Complex.I-z)⁻¹‖
  obtain ⟨hk,hkint⟩ := nf_cauchy_kernelL2 u z hu
  have hΦ : MemLp (fun y : ℝ => ‖Φ (u+y*Complex.I)‖) (ENNReal.ofReal (2:ℝ)) volume := by
    simpa using hL.norm
  have hK : MemLp K (ENNReal.ofReal (2:ℝ)) volume := by simpa [K] using hk
  have holder := integral_mul_le_Lp_mul_Lq_of_nonneg (p:=2) (q:=2)
    (Real.holderConjugate_iff.mpr (by norm_num)) (.of_forall (fun y => norm_nonneg _))
    (.of_forall (fun y => norm_nonneg _)) hΦ hK
  calc
    _ ≤ ∫ y : ℝ, ‖Φ (u+y*Complex.I)‖ * K y := by
      simpa [verticalLineIntegral, K, div_eq_mul_inv, norm_mul] using
        (norm_integral_le_integral_norm (fun y : ℝ => Φ (u+y*Complex.I)/((u:ℂ)+y*Complex.I-z)))
    _ ≤ _ := by
      rw [← hkint]
      simpa [K,Real.sqrt_eq_rpow,one_div] using holder

private theorem nf_cauchy_Hardy_all (Φ : ℂ → ℂ) (u : ℝ) (z : ℂ) (N : ℕ)
    (hu : u < z.re) (hL : MemLp (fun y : ℝ => Φ (u+y*Complex.I)) 2 volume) :
    VerticalLineIntegrable (fun s => Φ s/(s-z)^(N+1)) u ∧
    ‖verticalLineIntegral (fun s => Φ s/(s-z)^(N+1)) u‖ ≤
      Real.sqrt (∫ y : ℝ, ‖Φ (u+y*Complex.I)‖^2) *
      Real.sqrt (Real.pi/(z.re-u)) / (z.re-u)^N := by
  let W (y : ℝ) := (u:ℂ) + (y:ℂ)*Complex.I-z
  let K (y : ℝ) := ‖(W y)⁻¹‖
  have hd : 0 < z.re-u := sub_pos.mpr hu
  have hw (y : ℝ) : z.re-u ≤ ‖W y‖ := by
    have hh := Complex.abs_re_le_norm (W y)
    simpa [W,abs_of_neg (sub_neg.mpr hu)] using hh
  have hw0 (y : ℝ) : W y ≠ 0 := norm_pos_iff.mp (hd.trans_le (hw y))
  obtain ⟨hk,hkint⟩ := nf_cauchy_kernelL2 u z hu
  have hΦ : MemLp (fun y : ℝ => ‖Φ (u+y*Complex.I)‖) (ENNReal.ofReal (2:ℝ)) volume := by
    simpa using hL.norm
  have hK : MemLp K (ENNReal.ofReal (2:ℝ)) volume := by simpa [K,W] using hk
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg (p:=2) (q:=2)
    (Real.holderConjugate_iff.mpr (by norm_num)) (.of_forall (fun y => norm_nonneg _))
    (.of_forall (fun y => norm_nonneg _)) hΦ hK
  have hholder : (∫ y : ℝ, ‖Φ (u+y*Complex.I)‖ * K y) ≤
      Real.sqrt (∫ y : ℝ, ‖Φ (u+y*Complex.I)‖^2) * Real.sqrt (Real.pi/(z.re-u)) := by
    rw [← hkint]
    simpa [K,W,Real.sqrt_eq_rpow,one_div] using hh
  have hproduct : Integrable (fun y : ℝ => ‖Φ (u+y*Complex.I)‖ * K y) :=
    hL.norm.integrable_mul hk
  have hdom (y : ℝ) : ‖Φ (u+y*Complex.I)/(W y)^(N+1)‖ ≤ (‖Φ (u+y*Complex.I)‖ * K y)/(z.re-u)^N := by
    change _ ≤ (‖Φ _‖ * ‖(W y)⁻¹‖) / _
    rw [norm_div,norm_pow,pow_succ,norm_inv,← div_eq_mul_inv, mul_comm (‖W y‖^N),div_mul_eq_div_div]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_left₀ hd.le (hw y) N
  have hmaj := hproduct.div_const ((z.re-u)^N)
  constructor
  · have hc : Continuous (fun y : ℝ => ((W y)^(N+1))⁻¹) := by
      apply Continuous.inv₀
      · dsimp [W]; fun_prop
      · intro y; exact pow_ne_zero _ (hw0 y)
    exact hmaj.mono' (by simpa only [div_eq_mul_inv,Pi.mul_def,W] using
      hL.aestronglyMeasurable.mul hc.aestronglyMeasurable) (.of_forall hdom)
  · have hb := norm_integral_le_of_norm_le hmaj (.of_forall hdom)
    rw [integral_div] at hb
    simpa [verticalLineIntegral,W,norm_mul] using hb.trans (div_le_div_of_nonneg_right hholder (by positivity))

private theorem nf_cauchy_recede_Hardy (Φ : ℂ → ℂ) (u : ℕ → ℝ) (M : ℝ)
    (hu : Tendsto u atTop atBot)
    (hL : ∀ᶠ n in atTop, MemLp (fun y : ℝ => Φ (u n+y*Complex.I)) 2 volume)
    (hM : ∀ᶠ n in atTop, (∫ y : ℝ, ‖Φ (u n+y*Complex.I)‖^2) ≤ M)
    (N : ℕ) (z : ℂ) :
    Tendsto (fun n => verticalLineIntegral (fun s => Φ s/(s-z)^(N+1)) (u n)) atTop (𝓝 0) := by
  have hd : Tendsto (fun n => z.re - u n) atTop atTop := by
    simpa only [sub_eq_add_neg, Function.comp_apply] using
      tendsto_atTop_add_const_left atTop z.re (tendsto_neg_atBot_atTop.comp hu)
  have hr : Tendsto (fun n => Real.pi/(z.re-u n)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hd
  have hzero : Tendsto (fun n => Real.sqrt M * Real.sqrt (Real.pi/(z.re-u n))) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul ((Real.continuous_sqrt.tendsto 0).comp hr)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (.of_forall (fun _ => norm_nonneg _)) ?_ hzero
  filter_upwards [hd.eventually_ge_atTop 1, hL, hM] with n hn hi hsum
  calc
    _ ≤ _ := (nf_cauchy_Hardy_all Φ (u n) z N (by linarith) hi).2
    _ ≤ _ := div_le_self (by positivity) (one_le_pow₀ hn)
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hsum) (Real.sqrt_nonneg _)

end MasulloGRH
open MasulloGRH

theorem solution (Φ : ℂ → ℂ) :
    (∀ (u : ℝ) (z : ℂ) (N : ℕ), u < z.re →
      MemLp (fun y : ℝ => Φ (u+y*Complex.I)) 2 volume →
      VerticalLineIntegrable (fun s => Φ s/(s-z)^(N+1)) u ∧
      ‖verticalLineIntegral (fun s => Φ s/(s-z)^(N+1)) u‖ ≤
        Real.sqrt (∫ y : ℝ, ‖Φ (u+y*Complex.I)‖^2) *
        Real.sqrt (Real.pi/(z.re-u)) / (z.re-u)^N) ∧
    (∀ (u : ℕ → ℝ) (M : ℝ), Tendsto u atTop atBot →
      (∀ᶠ n in atTop, MemLp (fun y : ℝ => Φ (u n+y*Complex.I)) 2 volume) →
      (∀ᶠ n in atTop, (∫ y : ℝ, ‖Φ (u n+y*Complex.I)‖^2) ≤ M) →
      ∀ (N : ℕ) (z : ℂ), Tendsto
        (fun n => verticalLineIntegral (fun s => Φ s/(s-z)^(N+1)) (u n)) atTop (𝓝 0)) := by
  exact ⟨nf_cauchy_Hardy_all Φ, nf_cauchy_recede_Hardy Φ⟩
