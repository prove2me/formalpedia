-- Prove2me | solution 1 for JHolomorphic.eLpNorm_fderiv_integral_inv_sub_smul_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-22T09:09:27.992555+00:00
-- url     : https://prove2.me/submissions/cc49438c-4c21-4282-8d5a-a8a41876d693

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Theorems.Thm_JHolomorphic_norm_integral_inv_sub_smul_le
import Theorems.Thm_JHolomorphic_contDiff_integral_inv_sub_smul
import Theorems.Thm_JHolomorphic_eLpNorm_fderiv_le_of_contDiff



namespace JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal NNReal

set_option maxHeartbeats 1000000 in
/-- `L^p` bound on a disc for the derivatives of the Cauchy transform of smooth data. -/
theorem eLpNorm_fderiv_integral_inv_sub_smul_le_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] (p R : ℝ) (hp : 2 < p) (hR : 0 < R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ h : ℂ → E, ContDiff ℝ ∞ h → HasCompactSupport h →
      Function.support h ⊆ ball 0 (2 * R) →
      eLpNorm (fun z => fderiv ℝ (fun z => ∫ ζ, (z - ζ)⁻¹ • h ζ) z 1) (ENNReal.ofReal p)
          (volume.restrict (ball 0 R)) +
        eLpNorm (fun z => fderiv ℝ (fun z => ∫ ζ, (z - ζ)⁻¹ • h ζ) z Complex.I) (ENNReal.ofReal p)
          (volume.restrict (ball 0 R)) ≤
        ENNReal.ofReal M * eLpNorm h (ENNReal.ofReal p) volume := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℂ E
  have hp0 : 0 < p := by linarith
  have hP0 : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have hP1 : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  obtain ⟨C1, hC1, hC1b⟩ := norm_integral_inv_sub_smul_le (E := E) p (3 * R) hp (by positivity)
  obtain ⟨J₀, hJ₀def⟩ : ∃ J₀ : E →L[ℝ] E,
      J₀ = (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] E →L[ℝ] E) Complex.I := ⟨_, rfl⟩
  have hJ₀ : J₀.comp J₀ = -ContinuousLinearMap.id ℝ E := by
    ext x; simp [hJ₀def, smul_smul]
  obtain ⟨CF, hCF⟩ := eLpNorm_fderiv_le_of_contDiff (E := E) p (by linarith) J₀ hJ₀
  let χ : ContDiffBump (0 : ℂ) := ⟨R, 2 * R, hR, by linarith⟩
  have hχc : Continuous (fderiv ℝ χ) := (χ.contDiff (n := 1)).continuous_fderiv one_ne_zero
  obtain ⟨Bχ, hBχ⟩ := hχc.bounded_above_of_compact_support
    (χ.hasCompactSupport.fderiv (𝕜 := ℝ))
  have hBχ0 : 0 ≤ Bχ := (norm_nonneg _).trans (hBχ 0)
  set V : ℝ≥0∞ := volume (closedBall (0 : ℂ) (2 * R)) ^ (1 / p) with hVdef
  have hVfin : V ≠ ⊤ := by
    rw [hVdef]
    exact ENNReal.rpow_ne_top_of_nonneg (by positivity) measure_closedBall_lt_top.ne
  set M : ℝ := max CF 0 * (2 * Bχ * C1 * V.toReal + 2 * Real.pi) with hMdef
  refine ⟨M, by positivity, fun h hh hc hsupp => ?_⟩
  obtain ⟨hwd, hdbar⟩ := contDiff_integral_inv_sub_smul h hh hc
  set w : ℂ → E := fun z => ∫ ζ, (z - ζ)⁻¹ • h ζ with hwdef
  have hhm : MemLp h (ENNReal.ofReal p) volume := hh.continuous.memLp_of_hasCompactSupport hc
  have hhfin : eLpNorm h (ENNReal.ofReal p) volume ≠ ⊤ := hhm.eLpNorm_ne_top
  set Nh : ℝ := (eLpNorm h (ENNReal.ofReal p) volume).toReal with hNhdef
  have hwb : ∀ z ∈ closedBall (0 : ℂ) (2 * R), ‖w z‖ ≤ C1 * Nh := by
    intro z hz
    refine (hC1b h hhm (hsupp.trans (ball_subset_ball (by linarith))) z ?_).2
    exact closedBall_subset_ball (by linarith) hz
  set F : ℂ → E := fun z => χ z • w z with hFdef
  have hwd1 : ContDiff ℝ 1 w := hwd.of_le (by exact_mod_cast le_top)
  have hχ1 : ContDiff ℝ 1 (fun z => χ z) := χ.contDiff (n := 1)
  have hF1 : ContDiff ℝ 1 F := hχ1.smul hwd1
  have hFc : HasCompactSupport F := χ.hasCompactSupport.smul_right
  have hderF : ∀ z v, fderiv ℝ F z v = fderiv ℝ χ z v • w z + χ z • fderiv ℝ w z v := by
    intro z v
    rw [hFdef, fderiv_fun_smul ((hχ1.differentiable one_ne_zero) z) ((hwd1.differentiable one_ne_zero) z)]
    simp [add_comm]
  -- the pointwise bound on `∂̄F`
  have hpt : ∀ z, ‖fderiv ℝ F z 1 + J₀ (fderiv ℝ F z Complex.I)‖ ≤
      (closedBall (0 : ℂ) (2 * R)).indicator (fun _ => 2 * Bχ * (C1 * Nh)) z +
        2 * Real.pi * ‖h z‖ := by
    intro z
    have hdb := hdbar z
    have hexp : fderiv ℝ F z 1 + J₀ (fderiv ℝ F z Complex.I) =
        (fderiv ℝ χ z 1 • w z + Complex.I • (fderiv ℝ χ z Complex.I • w z)) +
          χ z • ((2 * Real.pi : ℂ) • h z) := by
      rw [hderF, hderF, ← hdb, hJ₀def]
      simp only [ContinuousLinearMap.lsmul_apply, smul_add]
      rw [smul_comm Complex.I (χ z)]
      abel
    rw [hexp]
    have hχz : ‖(χ z : ℝ)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg χ.nonneg]; exact χ.le_one
    have h2 : ‖χ z • ((2 * Real.pi : ℂ) • h z)‖ ≤ 2 * Real.pi * ‖h z‖ := by
      rw [norm_smul, norm_smul]
      have : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
        rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [this]
      calc ‖(χ z : ℝ)‖ * (2 * Real.pi * ‖h z‖) ≤ 1 * (2 * Real.pi * ‖h z‖) :=
            mul_le_mul_of_nonneg_right hχz (by positivity)
        _ = _ := one_mul _
    by_cases hz : z ∈ closedBall (0 : ℂ) (2 * R)
    · rw [indicator_of_mem hz]
      have hw := hwb z hz
      have hd : ∀ v : ℂ, ‖v‖ = 1 → ‖fderiv ℝ χ z v • w z‖ ≤ Bχ * (C1 * Nh) := by
        intro v hv
        rw [norm_smul]
        refine mul_le_mul ?_ hw (norm_nonneg _) hBχ0
        calc ‖fderiv ℝ χ z v‖ ≤ ‖fderiv ℝ χ z‖ * ‖v‖ := (fderiv ℝ χ z).le_opNorm v
          _ = ‖fderiv ℝ χ z‖ := by rw [hv, mul_one]
          _ ≤ Bχ := hBχ z
      have h1 : ‖fderiv ℝ χ z 1 • w z + Complex.I • (fderiv ℝ χ z Complex.I • w z)‖ ≤
          2 * Bχ * (C1 * Nh) := by
        calc _ ≤ ‖fderiv ℝ χ z 1 • w z‖ + ‖Complex.I • (fderiv ℝ χ z Complex.I • w z)‖ :=
              norm_add_le _ _
          _ = ‖fderiv ℝ χ z 1 • w z‖ + ‖fderiv ℝ χ z Complex.I • w z‖ := by
              rw [norm_smul Complex.I, Complex.norm_I, one_mul]
          _ ≤ Bχ * (C1 * Nh) + Bχ * (C1 * Nh) :=
              add_le_add (hd 1 (by simp)) (hd Complex.I (by simp))
          _ = _ := by ring
      exact (norm_add_le _ _).trans (add_le_add h1 h2)
    · rw [indicator_of_notMem hz, zero_add]
      have hz' : z ∉ tsupport (fderiv ℝ χ) := fun hm =>
        hz ((tsupport_fderiv_subset ℝ).trans χ.tsupport_eq.subset hm)
      have h0 : fderiv ℝ χ z = 0 := image_eq_zero_of_notMem_tsupport hz'
      rw [h0]
      simpa using h2
  -- `L^p` bound for `∂̄F`
  have hdbarF : eLpNorm (fun z => fderiv ℝ F z 1 + J₀ (fderiv ℝ F z Complex.I))
      (ENNReal.ofReal p) volume ≤
      (ENNReal.ofReal (2 * Bχ * C1) * V + ENNReal.ofReal (2 * Real.pi)) *
        eLpNorm h (ENNReal.ofReal p) volume := by
    have hmeas1 : AEStronglyMeasurable
        ((closedBall (0 : ℂ) (2 * R)).indicator (fun _ => 2 * Bχ * (C1 * Nh))) volume :=
      (aestronglyMeasurable_const.indicator measurableSet_closedBall)
    have hmeas2 : AEStronglyMeasurable (fun z => 2 * Real.pi * ‖h z‖) volume :=
      (continuous_const.mul hh.continuous.norm).aestronglyMeasurable
    calc _ ≤ eLpNorm (fun z => (closedBall (0 : ℂ) (2 * R)).indicator
              (fun _ => 2 * Bχ * (C1 * Nh)) z + 2 * Real.pi * ‖h z‖) (ENNReal.ofReal p) volume :=
          eLpNorm_mono_real hpt
      _ ≤ eLpNorm ((closedBall (0 : ℂ) (2 * R)).indicator (fun _ => 2 * Bχ * (C1 * Nh)))
              (ENNReal.ofReal p) volume +
            eLpNorm (fun z => 2 * Real.pi * ‖h z‖) (ENNReal.ofReal p) volume :=
          eLpNorm_add_le hmeas1 hmeas2 hP1
      _ = ENNReal.ofReal (2 * Bχ * C1) * V * eLpNorm h (ENNReal.ofReal p) volume +
            ENNReal.ofReal (2 * Real.pi) * eLpNorm h (ENNReal.ofReal p) volume := by
          congr 1
          · rw [eLpNorm_indicator_const measurableSet_closedBall hP0 ENNReal.ofReal_ne_top,
              ENNReal.toReal_ofReal hp0.le, hVdef]
            rw [show 2 * Bχ * (C1 * Nh) = (2 * Bχ * C1) * Nh by ring,
              Real.enorm_eq_ofReal (by positivity), ENNReal.ofReal_mul (by positivity), hNhdef,
              ENNReal.ofReal_toReal hhfin]
            ring
          · have : (fun z => 2 * Real.pi * ‖h z‖) = (2 * Real.pi) • fun z => ‖h z‖ := by
              funext z; simp
            rw [this, eLpNorm_const_smul, eLpNorm_norm, Real.enorm_eq_ofReal (by positivity)]
      _ = _ := by ring
  -- restriction to the disc `B_R`
  have hFw : ∀ v, ∀ z ∈ ball (0 : ℂ) R, fderiv ℝ w z v = fderiv ℝ F z v := by
    intro v z hz
    have hev : F =ᶠ[𝓝 z] w := by
      filter_upwards [isOpen_ball.mem_nhds hz] with y hy
      rw [hFdef]
      simp only
      rw [χ.one_of_mem_closedBall (ball_subset_closedBall hy), one_smul]
    rw [hev.fderiv_eq]
  have hres : ∀ v, eLpNorm (fun z => fderiv ℝ w z v) (ENNReal.ofReal p)
      (volume.restrict (ball 0 R)) ≤ eLpNorm (fun z => fderiv ℝ F z v) (ENNReal.ofReal p) volume := by
    intro v
    calc _ = eLpNorm (fun z => fderiv ℝ F z v) (ENNReal.ofReal p) (volume.restrict (ball 0 R)) :=
          eLpNorm_congr_ae ((ae_restrict_iff' measurableSet_ball).2
            (Eventually.of_forall (hFw v)))
      _ ≤ _ := eLpNorm_mono_measure _ Measure.restrict_le_self
  have hCF' := hCF F hF1 hFc
  calc _ ≤ eLpNorm (fun z => fderiv ℝ F z 1) (ENNReal.ofReal p) volume +
        eLpNorm (fun z => fderiv ℝ F z Complex.I) (ENNReal.ofReal p) volume :=
        add_le_add (hres 1) (hres Complex.I)
    _ ≤ ENNReal.ofReal CF * eLpNorm (fun z => fderiv ℝ F z 1 + J₀ (fderiv ℝ F z Complex.I))
          (ENNReal.ofReal p) volume := hCF'
    _ ≤ ENNReal.ofReal (max CF 0) * ((ENNReal.ofReal (2 * Bχ * C1) * V +
          ENNReal.ofReal (2 * Real.pi)) * eLpNorm h (ENNReal.ofReal p) volume) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) hdbarF
    _ = ENNReal.ofReal M * eLpNorm h (ENNReal.ofReal p) volume := by
        rw [hMdef, ← mul_assoc]
        congr 1
        rw [ENNReal.ofReal_mul (le_max_right _ _)]
        congr 1
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (p := 2 * Bχ * C1) (by positivity), ENNReal.ofReal_toReal hVfin]

end JHolomorphic

open JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal NNReal

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] (p R : ℝ) (hp : 2 < p) (hR : 0 < R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ h : ℂ → E, ContDiff ℝ ∞ h → HasCompactSupport h →
      Function.support h ⊆ ball 0 (2 * R) →
      eLpNorm (fun z => fderiv ℝ (fun z => ∫ ζ, (z - ζ)⁻¹ • h ζ) z 1) (ENNReal.ofReal p)
          (volume.restrict (ball 0 R)) +
        eLpNorm (fun z => fderiv ℝ (fun z => ∫ ζ, (z - ζ)⁻¹ • h ζ) z Complex.I) (ENNReal.ofReal p)
          (volume.restrict (ball 0 R)) ≤
        ENNReal.ofReal M * eLpNorm h (ENNReal.ofReal p) volume :=
  eLpNorm_fderiv_integral_inv_sub_smul_le_aux p R hp hR
