-- Prove2me | solution 1 for LogLogJam.lemma_5_9
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T09:27:11.773813+00:00
-- url     : https://prove2.me/submissions/f3d984b5-1347-425a-ab97-7c6a9e7befc2

import Definitions.Def_LogLogJam_GaussProtocol
import Theorems.Thm_LogLogJam_history_reference_density

open MeasureTheory Filter LogLogJam
open scoped ENNReal Topology

private theorem derivMeasurable {X : Type*} [MeasurableSpace X] (q : ℝ → X → ℝ)
    (hC : ∀ x, ContDiff ℝ 1 (fun t => q t x)) (hm : ∀ t, Measurable (q t)) :
    Measurable (fun z : ℝ × X => deriv (fun t => q t z.2) z.1) := by
  apply measurable_uncurry_of_continuous_of_measurable (fun x => (hC x).continuous_deriv_one)
  intro t
  let d (n : ℕ) : ℝ := 1 / (n+1 : ℝ)
  have hlim : Tendsto d atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,Eventually.of_forall fun n => by change 0 < 1 / (n+1 : ℝ); positivity⟩
  apply measurable_of_tendsto_metrizable (f := fun (n : ℕ) x => (d n)⁻¹ * (q (t+d n) x - q t x))
    (fun n => measurable_const.mul ((hm _).sub (hm _)))
  apply tendsto_pi_nhds.mpr
  intro x
  exact ((hC x).differentiable_one t).hasDerivAt.tendsto_slope_zero_right.comp hlim

private theorem atFirst {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (f : A → B → C) (h : Measurable (Function.uncurry f)) (x : A) : Measurable (f x) :=
  h.comp (measurable_prodMk_left (x := x))

private theorem atSecond {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (f : A → B → C) (h : Measurable (Function.uncurry f)) (y : B) : Measurable (fun x => f x y) :=
  h.comp (measurable_prodMk_right (y := y))

set_option maxHeartbeats 1000000 in
theorem solution {T : ℕ} (P : GaussProtocol T) (lam : ℝ) (hlam : 1 < lam) (t : ℕ)
    (ht : t ≤ T) :
    Jbar lam P t = ENNReal.ofReal (1 / Real.pi) * ∫⁻ s in Set.Ico 0 Real.pi, histInt lam s P t (postFisher lam) := by
  let G := {H : Hist t // ∀ i, IsCov (H i).1 (Matrix.of (H i).2.1)}
  obtain ⟨μ, hs, hc⟩ := history_reference_density P t ht
  let _ := hs
  obtain ⟨hpos, _, hC, hm, _, hrep⟩ := hc lam hlam
  let ν := (volume : Measure ℝ).restrict (Set.Ico 0 Real.pi)
  let q (s : ℝ) (H : G) := histDens lam s H.1
  let Q (s : ℝ) (H : G) := ENNReal.ofReal (q s H)
  let S (s : ℝ) (H : G) := ENNReal.ofReal ((deriv (fun y => Real.log (q y H)) s)^2)
  let W (s : ℝ) (H : G) := Q s H * S s H
  let Z (H : G) := postNorm lam H.1
  have hqm : Measurable (Function.uncurry q) :=
    measurable_uncurry_of_continuous_of_measurable (fun H => (hC H).continuous) hm
  have hQ : Measurable (Function.uncurry Q) := hqm.ennreal_ofReal
  have hS : Measurable (Function.uncurry S) :=
    ((derivMeasurable (fun s H => Real.log (q s H)) (fun H => (hC H).log (fun s => (hpos s H).ne'))
      (fun s => (hm s).log)).pow_const 2).ennreal_ofReal
  have hW : Measurable (Function.uncurry W) := hQ.mul hS
  have hZ (H : G) : 0 < Z H := by
    dsimp [Z,postNorm]
    rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le Real.pi_pos.le]
    apply intervalIntegral.integral_pos Real.pi_pos (hC H).continuous.continuousOn
      (fun s _ => (hpos s H).le)
    exact ⟨0,⟨le_rfl,Real.pi_pos.le⟩,hpos 0 H⟩
  have hZi (H : G) : ENNReal.ofReal (Z H) = ∫⁻ s, Q s H ∂ν :=
    ofReal_integral_eq_lintegral_ofReal ((hC H).continuous.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self)
      (Eventually.of_forall fun s => (hpos s H).le)
  have hZinv (H : G) : (ENNReal.ofReal (Z H))⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (hZ H)).ne'
  have point (H : G) : postFisher lam H.1 = (ENNReal.ofReal (Z H))⁻¹ * ∫⁻ s, W s H ∂ν := by
    rw [← lintegral_const_mul' _ _ (hZinv H)]
    apply lintegral_congr
    intro s
    have hl : (fun a => Real.log (post lam H.1 a)) = (fun a => Real.log (q a H) - Real.log (Z H)) := by
      funext a; exact Real.log_div (hpos a H).ne' (hZ H).ne'
    change ENNReal.ofReal (q s H / Z H) * ENNReal.ofReal
      ((deriv (fun a => Real.log (post lam H.1 a)) s)^2) = _
    rw [hl, deriv_sub_const, ENNReal.ofReal_div_of_pos (hZ H), div_eq_mul_inv]
    dsimp only [W,Q,S]
    ac_rfl
  have hpost : Measurable (fun H : G => postFisher lam H.1) := by
    simp_rw [point,hZi]
    exact (hQ.lintegral_prod_left (μ := ν)).inv.mul (hW.lintegral_prod_left (μ := ν))
  let R (s : ℝ) (H : G) := Q s H * postFisher lam H.1
  have hR : Measurable (Function.uncurry R) := hQ.mul (hpost.comp measurable_snd)
  have hslice (s : ℝ) : Measurable (S s) :=
    atFirst S hS s
  have hleft (s : ℝ) : protoFisher lam P t s = ∫⁻ H, W s H ∂μ :=
    hrep s (fun h : Hist t => ENNReal.ofReal ((deriv (fun y => Real.log (histDens lam y h)) s)^2))
      (hslice s)
  have hright (s : ℝ) : histInt lam s P t (postFisher lam) = ∫⁻ H, R s H ∂μ := hrep s (postFisher lam) hpost
  unfold Jbar
  simp_rw [hleft, hright]
  congr 1
  rw [lintegral_lintegral_swap hW.aemeasurable, lintegral_lintegral_swap hR.aemeasurable]
  apply lintegral_congr
  intro H
  dsimp only [R]
  rw [lintegral_mul_const _ (atSecond Q hQ H), ← hZi, point,
    ← mul_assoc, ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr (hZ H)).ne' ENNReal.ofReal_ne_top, one_mul]
