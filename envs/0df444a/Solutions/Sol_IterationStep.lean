-- Prove2me | solution 1 for IterationStep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:44:08.760769+00:00
-- url     : https://prove2.me/submissions/073f7299-e775-4bfd-b0d4-d210ade9a997

import Definitions.Def_PHigherOrder_PHarmNormalize
import Definitions.Def_PHigherOrder_PHarmRestrict
import Definitions.Def_PHigherOrder_Scales
import Definitions.Def_PHigherOrder_IterationStep
import Theorems.Thm_PHarmNormalize
import Theorems.Thm_PHarmRestrict
import Theorems.Thm_Scales


set_option autoImplicit false

theorem _root_.solution (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hL : LewisRigidityInput p) (F : FirstOrderEstimateInput p) (hIM : IMRegularityInput p)
    (k : ℕ) (hk : 2 ≤ k) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hks : (k : ℝ) + β < SOpt p) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ θ : ℝ, 0 < θ ∧ θ < 1 / 4 ∧
      ∀ (v : Plane → ℝ) (g : Plane → Plane), IsPHarm p (Metric.ball 0 1) v g →
        (∀ y ∈ Metric.ball (0 : Plane) 1, |v y| ≤ 1) → v 0 = 0 →
        ∀ R : ℝ, 0 < R → R ≤ 1 →
          (∀ y : Plane, ‖y‖ < R → |v y| ≤ R ^ ((k : ℝ) + β)) →
          R ^ (1 - ((k : ℝ) + β)) * ‖gradient v 0‖ ≤ δ →
          ∃ R' : ℝ, 0 < R' ∧ R' ≤ 1 ∧
            (∀ y : Plane, ‖y‖ < R' → |v y| ≤ R' ^ ((k : ℝ) + β)) ∧
            θ * R ≤ R' ∧ R' ≤ R / 4 := by
  classical
  have hs1 : (1 : ℝ) < (k : ℝ) + β := by
    have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hs0 : (0 : ℝ) < (k : ℝ) + β := by linarith
  -- STEP 0:  the constants `δ` and `θ`, fixed before `v`.
  obtain ⟨δ, hδ, Rs, hRne, hRmem, hscale⟩ := Scales p hp hp2 hL F hIM k hk β hβ0 hβ1 hks
  obtain ⟨θ, hθdef⟩ : ∃ t : ℝ, t = Rs.min' hRne := ⟨_, rfl⟩
  have hθmem : θ ∈ Rs := by rw [hθdef]; exact Finset.min'_mem Rs hRne
  refine ⟨δ, hδ, θ, (hRmem θ hθmem).1, (hRmem θ hθmem).2, ?_⟩
  intro v g hph hbd hv0 R hR0 hR1 hnorm hcont
  have hRne0 : R ≠ 0 := ne_of_gt hR0
  -- STEP 1:  the rescaled function.
  obtain ⟨M, hMdef⟩ : ∃ t : ℝ, t = R ^ ((k : ℝ) + β) := ⟨_, rfl⟩
  have hM0 : 0 < M := by rw [hMdef]; exact Real.rpow_pos_of_pos hR0 _
  have hMne : M ≠ 0 := ne_of_gt hM0
  have hRsm : ∀ x : Plane, ‖x‖ < 1 → ‖(0 : Plane) + R • x‖ < R := by
    intro x hx
    rw [zero_add, norm_smul, Real.norm_eq_abs, abs_of_pos hR0]
    calc R * ‖x‖ < R * 1 := mul_lt_mul_of_pos_left hx hR0
      _ = R := by ring
  -- (1a) the rescaled function is `p`-harmonic on `B_1`
  have hPN := PHarmNormalize p hp hp2 (Metric.ball 0 1) v g 0 R M 0 hR0 hM0 hph
  have hsubset : Metric.ball (0 : Plane) 1
      ⊆ {x : Plane | (0 : Plane) + R • x ∈ Metric.ball 0 1} := by
    intro x hx
    rw [Metric.mem_ball, dist_zero_right] at hx
    have hb : ‖(0 : Plane) + R • x‖ < 1 := lt_of_lt_of_le (hRsm x hx) hR1
    simpa [Metric.mem_ball, dist_zero_right] using hb
  have hvRsimp : (fun x : Plane => (v ((0 : Plane) + R • x) - 0) / M)
      = fun x : Plane => M⁻¹ * v (R • x) := by
    funext x
    rw [zero_add, sub_zero, div_eq_inv_mul]
  have hPR : IsPHarm p (Metric.ball 0 1) (fun x : Plane => M⁻¹ * v (R • x))
      (fun x => (R / M) • g ((0 : Plane) + R • x)) := by
    rw [← hvRsimp]
    exact (PHarmRestrict p hp hp2 _ _ _ hPN).1 _ Metric.isOpen_ball hsubset
  -- (1b) it vanishes at the origin
  have hvR0 : (fun x : Plane => M⁻¹ * v (R • x)) 0 = 0 := by
    show M⁻¹ * v (R • (0 : Plane)) = 0
    rw [smul_zero, hv0, mul_zero]
  -- (1c) it is bounded by `1` on `B_1`
  have hvRbd : ∀ y ∈ Metric.ball (0 : Plane) 1, |(fun x : Plane => M⁻¹ * v (R • x)) y| ≤ 1 := by
    intro y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    show |M⁻¹ * v (R • y)| ≤ 1
    have h := hnorm (R • y) (by rw [← zero_add (R • y)]; exact hRsm y hy)
    rw [← hMdef] at h
    rw [abs_mul, abs_of_pos (inv_pos.mpr hM0)]
    calc M⁻¹ * |v (R • y)| ≤ M⁻¹ * M := mul_le_mul_of_nonneg_left h (le_of_lt (inv_pos.mpr hM0))
      _ = 1 := by field_simp
  -- (1d) the continuation condition transfers
  obtain ⟨hvC1, -, -⟩ := F.est v g hph hbd
  have hvdiff : DifferentiableAt ℝ v 0 := by
    have h0 : (0 : Plane) ∈ Metric.ball (0 : Plane) (3 / 4) := Metric.mem_ball_self (by norm_num)
    exact ((hvC1.differentiableOn one_ne_zero) 0 h0).differentiableAt
      (Metric.isOpen_ball.mem_nhds h0)
  have hgradR : gradient (fun x : Plane => M⁻¹ * v (R • x)) 0 = (M⁻¹ * R) • gradient v 0 := by
    have hlin : HasFDerivAt (fun x : Plane => R • x) (R • ContinuousLinearMap.id ℝ Plane) 0 :=
      (R • ContinuousLinearMap.id ℝ Plane).hasFDerivAt
    have h1 : HasFDerivAt v (fderiv ℝ v 0) (R • (0 : Plane)) := by
      rw [smul_zero]; exact hvdiff.hasFDerivAt
    have hfull : HasFDerivAt (fun x : Plane => M⁻¹ * v (R • x))
        (M⁻¹ • ((fderiv ℝ v 0).comp (R • ContinuousLinearMap.id ℝ Plane))) 0 :=
      (h1.comp 0 hlin).const_mul M⁻¹
    refine ext_inner_right ℝ ?_
    intro w
    have hL : inner ℝ (gradient (fun x : Plane => M⁻¹ * v (R • x)) 0) w
        = fderiv ℝ (fun x : Plane => M⁻¹ * v (R • x)) 0 w := by
      rw [← toDual_gradient]; rfl
    have hvw : inner ℝ (gradient v 0) w = fderiv ℝ v 0 w := by
      rw [← toDual_gradient]; rfl
    rw [hL, hfull.fderiv, real_inner_smul_left, hvw]
    show M⁻¹ * ((fderiv ℝ v 0) (R • w)) = _
    rw [map_smul, smul_eq_mul]
    ring
  have hMR : M⁻¹ * R = R ^ (1 - ((k : ℝ) + β)) := by
    have h1 : (1 : ℝ) - ((k : ℝ) + β) = 1 + (-((k : ℝ) + β)) := by ring
    rw [h1, Real.rpow_add hR0, Real.rpow_one, Real.rpow_neg (le_of_lt hR0), hMdef]
    ring
  have hcontR : ‖gradient (fun x : Plane => M⁻¹ * v (R • x)) 0‖ ≤ δ := by
    rw [hgradR, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < M⁻¹ * R), hMR]
    exact hcont
  -- STEP 2:  the scale property.
  obtain ⟨ρ, hρmem, hρ⟩ := hscale (fun x : Plane => M⁻¹ * v (R • x))
    (fun x => (R / M) • g ((0 : Plane) + R • x)) hPR hvRbd hvR0 hcontR
  have hρ0 : 0 < ρ := (hRmem ρ hρmem).1
  have hρ4 : ρ < 1 / 4 := (hRmem ρ hρmem).2
  have hθρ : θ ≤ ρ := by rw [hθdef]; exact Finset.min'_le Rs ρ hρmem
  -- STEP 3:  the new radius.
  refine ⟨R * ρ, by positivity, by nlinarith, ?_, by nlinarith, by nlinarith⟩
  intro y hy
  obtain ⟨z, hzdef⟩ : ∃ t : Plane, t = R⁻¹ • y := ⟨_, rfl⟩
  have hRz : R • z = y := by
    rw [hzdef, smul_smul, mul_inv_cancel₀ hRne0, one_smul]
  have hznorm : ‖z‖ < ρ := by
    calc ‖z‖ = R⁻¹ * ‖y‖ := by
          rw [hzdef, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR0)]
      _ < R⁻¹ * (R * ρ) := mul_lt_mul_of_pos_left hy (inv_pos.mpr hR0)
      _ = ρ := by field_simp
  have h := hρ z hznorm
  have hzv : M⁻¹ * v (R • z) = M⁻¹ * v y := by rw [hRz]
  rw [hzv, abs_mul, abs_of_pos (inv_pos.mpr hM0)] at h
  have h4 : |v y| < M * ρ ^ ((k : ℝ) + β) :=
    calc |v y| = M * (M⁻¹ * |v y|) := by field_simp
      _ < M * ρ ^ ((k : ℝ) + β) := mul_lt_mul_of_pos_left h hM0
  calc |v y| ≤ M * ρ ^ ((k : ℝ) + β) := le_of_lt h4
    _ = R ^ ((k : ℝ) + β) * ρ ^ ((k : ℝ) + β) := by rw [hMdef]
    _ = (R * ρ) ^ ((k : ℝ) + β) := (Real.mul_rpow (le_of_lt hR0) (le_of_lt hρ0)).symm
