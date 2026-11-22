-- Prove2me | solution 1 for MasulloRH.actual_translated_zeta_contour_pole_limit
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T08:08:40.141428+00:00
-- url     : https://prove2.me/submissions/0e6d6b34-137b-45ac-aac0-0a33397585c9

import Mathlib
import Definitions.Def_Zeta23_Statement_SeamClosed
import Definitions.Def_Zeta23_WeilEF_VerticalLine
import Theorems.Thm_Zeta23_WeilEF_full_line_identity
import Theorems.Thm_Zeta23_WeilEF_EF_zero_sum_summable_gen
import Theorems.Thm_Zeta23_RvM_zeta_local_zero_count
import Theorems.Thm_MasulloRH_actual_zeta_zero_trace_absolute_little_o_sqrt
open Filter Topology Complex MeasureTheory Zeta23 Zeta23.WeilEF
private noncomputable def zkShift (k : ℝ → ℂ) (L : ℝ) (u : ℝ) : ℂ :=
  Complex.exp (-(L : ℂ)/2) * k (u-L)
private theorem zHshift (k : ℝ → ℂ) (L : ℝ) (s : ℂ) :
    Hfn (zkShift k L) s = Complex.exp ((s-1)*(L:ℂ)) * Hfn k s := by
  unfold Hfn paperFT zkShift
  rw [← integral_const_mul]
  rw [← integral_add_right_eq_self (fun u : ℝ => Complex.exp (-(L:ℂ)/2) * k (u-L) *
      Complex.exp (I * ((s-1/2)/I) * (u:ℂ))) L]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [add_sub_cancel_right, ofReal_add]
  have he : I * ((s-1/2)/I) = s-1/2 := by field_simp
  rw [he, mul_add, Complex.exp_add]
  have hp : Complex.exp (-(L:ℂ)/2) * Complex.exp ((s-1/2)*(L:ℂ)) =
      Complex.exp ((s-1)*(L:ℂ)) := by rw [← Complex.exp_add]; congr 1; ring
  rw [← hp]; ring
theorem solution (k : ℝ → ℂ) (hk : ContDiff ℝ 2 k) (hc : HasCompactSupport k)
    {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3/2) :
    Tendsto (fun L : ℝ =>
      let f := fun u : ℝ => Complex.exp (-(L : ℂ)/2) * k (u-L)
      (1/(2*Real.pi) : ℂ) * ∫ t : ℝ,
        (Hfn f ((c:ℂ)+t*I) + Hfn f (1-c-t*I)) * logDeriv completedRiemannZeta ((c:ℂ)+t*I))
      atTop (𝓝 (-Hfn k 1)) := by
  let S := fun L : ℝ => ∑' ρ : zetaZeroConfig.carrier, (zeroMult ρ : ℂ) * Hfn (zkShift k L) ρ
  have hcd (L : ℝ) : ContDiff ℝ 2 (zkShift k L) :=
    contDiff_const.mul (hk.comp (contDiff_id.sub contDiff_const))
  have hcomp (L : ℝ) : HasCompactSupport (fun u : ℝ => k (u-L)) := by
    simpa [Function.comp_def,sub_eq_add_neg] using hc.comp_homeomorph (Homeomorph.addRight (-L))
  have hcs (L : ℝ) : HasCompactSupport (zkShift k L) := by
    exact (hcomp L).mul_left
  obtain ⟨A,hA,hN⟩ := Zeta23.RvM.zeta_local_zero_count
  have has (L : ℝ) : Summable (fun ρ : zetaZeroConfig.carrier =>
      (zeroMult ρ : ℂ) * Hfn (zkShift k L) ρ) :=
    Zeta23.WeilEF.EF_zero_sum_summable_gen zetaZeroConfig hA hN (hcd L) (hcs L)
  have hs : Tendsto S atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) _ (MasulloRH.actual_zeta_zero_trace_absolute_little_o_sqrt k hk hc)
    intro L
    apply (norm_tsum_le_tsum_norm (has L).norm).trans
    apply le_of_eq
    apply tsum_congr
    intro ρ
    rw [zHshift, norm_mul,norm_mul, Complex.norm_exp]
    change _ = ‖(zeroMult ρ : ℂ) * Hfn k ρ‖ * _
    rw [norm_mul]
    simp only [Complex.mul_re, Complex.sub_re,Complex.one_re,Complex.ofReal_re,
      Complex.ofReal_im, mul_zero,sub_zero]
    ring
  have hp : Tendsto (fun L : ℝ => Hfn (zkShift k L) 0) atTop (𝓝 0) := by
    simp only [zHshift,zero_sub,neg_one_mul,← Complex.ofReal_neg,← Complex.ofReal_exp]
    simpa using ((Complex.continuous_ofReal.tendsto _).comp
      (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot)).mul (tendsto_const_nhds (x:=Hfn k 0))
  have h1 (L : ℝ) : Hfn (zkShift k L) 1 = Hfn k 1 := by simp [zHshift]
  have ht := (hs.sub hp).sub (tendsto_const_nhds (x:=Hfn k 1))
  simp only [sub_zero,zero_sub] at ht
  apply ht.congr'
  filter_upwards [] with L
  exact (h1 L ▸ full_line_identity zetaSeam (hcd L) (hcs L) hc1 hc2).symm
