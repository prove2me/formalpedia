-- Prove2me | solution 1 for NoHair.TwoCentre.Model.no_escape
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T22:03:57.602448+00:00
-- url     : https://prove2.me/submissions/5a0d89a0-28d1-40b4-b9b3-655e8bf81840

import Definitions.Def_NoHair_TwoCentreBlackHole
import Theorems.Thm_NoHair_TwoCentre_Advanced_regular_horizon

open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Topology
open scoped ContDiff Manifold RealInnerProductSpace

namespace NoHair.TwoCentre.Model.Curves

noncomputable section

def radialSpeed (z : E4) (w : E4) : ℝ := ⟪angularDirection z, spatial w⟫

theorem spatial_inner (w v : E4) :
    ⟪spatial w, spatial v⟫ = w 1 * v 1 + w 2 * v 2 + w 3 * v 3 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, spatial]
  ring

private theorem radialSpeed_coords (z w : E4) :
    radialSpeed z w = dr z 1 * w 1 + dr z 2 * w 2 + dr z 3 * w 3 := by
  unfold radialSpeed
  rw [← Model.spatial_coordinates 0 (angularDirection z), spatial_inner]
  rfl

theorem metric_eval (z : manifold) (v w : E4) :
    metric z v w =
    Advanced.gvv (parameters z) * v 0 * w 0
    + Advanced.gvr (parameters z) * (v 0 * radialSpeed z w + radialSpeed z v * w 0)
    + Advanced.grr (parameters z) * radialSpeed z v * radialSpeed z w
    + Advanced.angularScale (parameters z) / ‖spatial z‖ ^ 2 *
      (⟪spatial v, spatial w⟫ - radialSpeed z v * radialSpeed z w) := by
  change Matrix.toLinearMap₂' ℝ (metricCoeffs z) (WithLp.ofLp v) (WithLp.ofLp w) = _
  rw [Matrix.toLinearMap₂'_apply (R := ℝ) (metricCoeffs z : Matrix (Fin 4) (Fin 4) ℝ) (WithLp.ofLp v) (WithLp.ofLp w), spatial_inner]
  simp only [radialSpeed_coords, Fin.sum_univ_four, smul_eq_mul, metricCoeffs]
  have hd : dr z 0 = 0 := rfl
  simp (config := {decide := true}) [dt, spatialDelta, hd]
  ring

theorem angular_unit (z : manifold) : ‖angularDirection z‖ = 1 := by
  have hz : (3 : ℝ) / 4 < ‖spatial z‖ := z.property.1
  have hpos : 0 < ‖spatial z‖ := by linarith
  rw [angularDirection, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ hpos.ne']

private def spatialL : E4 →L[ℝ] E3 := LinearMap.toContinuousLinearMap {
  toFun := spatial
  map_add' := fun v w => by ext i; rfl
  map_smul' := fun c v => by ext i; rfl }

set_option backward.isDefEq.respectTransparency false in
private theorem norm_curve_deriv {γ : ℝ → manifold} {t : ℝ}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E4) 1 γ) :
    HasDerivAt (fun s => ‖spatial (γ s)‖ - 1) (radialSpeed (γ t) (velocity γ t)) t := by
  have hval : HasMFDerivAt 𝓘(ℝ, E4) 𝓘(ℝ, E4) (Subtype.val : manifold → E4) (γ t)
      (ContinuousLinearMap.id ℝ E4) := by
    have hs : MDifferentiableAt 𝓘(ℝ, E4) 𝓘(ℝ, E4) (Subtype.val : manifold → E4) (γ t) := (contMDiff_subtype_val (n := (1 : ℕ∞ω)) (U := manifold) (I := 𝓘(ℝ, E4))).mdifferentiableAt one_ne_zero
    have he : mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) (Subtype.val : manifold → E4) (γ t) =
        ContinuousLinearMap.id ℝ E4 := mfderiv_extChartAt_self (I := 𝓘(ℝ, E4)) (x := γ t)
    exact he ▸ hs.hasMFDerivAt
  have compDer : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E4) (fun s => (γ s : E4)) t
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E4) γ t : ℝ →L[ℝ] E4) := by
    exact hval.comp t (hγ.mdifferentiableAt one_ne_zero).hasMFDerivAt
  have hcoord : HasDerivAt (fun s => (γ s : E4)) (velocity γ t : E4) t :=
    (hasMFDerivAt_iff_hasFDerivAt.mp compDer).hasDerivAt
  have hspace : HasDerivAt (fun s => spatial (γ s)) (spatial (velocity γ t)) t :=
    spatialL.hasFDerivAt.comp_hasDerivAt t hcoord
  have hz : (3 : ℝ) / 4 < ‖spatial (γ t)‖ := (γ t).property.1
  have hn : 0 < ‖spatial (γ t)‖ := by linarith
  have hnorm := (hspace.norm_sq.sqrt (pow_ne_zero 2 hn.ne')).sub_const 1
  simp only [Real.sqrt_sq (norm_nonneg _)] at hnorm
  convert! hnorm using 1
  rw [radialSpeed, angularDirection, real_inner_smul_left]
  field_simp

private theorem actual_inward (z : manifold) {v : E4}
    (hh : ‖spatial z‖ = 1) (hf : IsFutureTimelike metric orientation z v) : radialSpeed z v < 0 := by
  let c := angularDirection z 0
  let w := radialSpeed z v
  let a := 1 / (1 + c ^ 2)
  have hp : parameters z = (0, c) := Prod.ext (by change ‖spatial z‖ - 1 = 0; rw [hh]; norm_num) rfl
  obtain ⟨hvv, hvr, hrr, hang⟩ := Advanced.regular_horizon.2.1 c
  have hunit := angular_unit z
  have hdir : spatial (orientation z) = -a • angularDirection z := by
    simp [orientation, Model.spatial_coordinates, hp, hvr, hrr, a]
  let vo : E4 := orientation z
  have htime : vo 0 = 1 := rfl
  have hspeed : radialSpeed z (orientation z) = -a := by
    change ⟪angularDirection z, spatial vo⟫ = -a
    rw [hdir, real_inner_smul_right, real_inner_self_eq_norm_sq, hunit]
    ring
  have ht := hf.1
  have hfut : metric z v vo < 0 := hf.2
  rw [metric_eval, hp, hvv, hvr, hrr, hang, hh, real_inner_self_eq_norm_sq] at ht
  rw [metric_eval, hp, hvv, hvr, hrr, hang, hh, htime, hspeed, hdir,
    real_inner_smul_right, real_inner_comm (angularDirection z) (spatial v)] at hfut
  have hA : w ^ 2 ≤ ‖spatial v‖ ^ 2 := by
    have h := abs_real_inner_le_norm (angularDirection z) (spatial v)
    rw [hunit, one_mul] at h
    exact sq_le_sq' (abs_le.mp h).1 (abs_le.mp h).2
  change radialSpeed z v < 0
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : c * a < 2 := by
    dsimp [a]
    rw [mul_one_div, div_lt_iff₀ (by positivity)]
    nlinarith [sq_nonneg (c - 1 / 4)]
  change w < 0
  by_contra! hnon
  have hvineq : -a * v 0 + (1 - c * a) * w < 0 := by
    dsimp [w, radialSpeed] at hfut ⊢
    linarith
  have htineq : 2 * v 0 * w + c * w ^ 2 < 0 := by
    dsimp [w] at hA ⊢
    nlinarith
  nlinarith [mul_lt_mul_of_pos_left htineq ha, mul_nonpos_of_nonpos_of_nonneg hvineq.le hnon,
    mul_nonneg (sub_nonneg.mpr hb.le) (sq_nonneg w)]

theorem no_escape (γ : ℝ → manifold) (hγ : IsFutureTimelikeCurveIn metric orientation univ γ)
    (hstart : γ 0 ∉ outer) : γ 1 ∉ outer := by
  let r := fun t => ‖spatial (γ t)‖ - 1
  have h0 : r 0 ≤ 0 := by
    have h : ¬ 1 < ‖spatial (γ 0)‖ := fun h => hstart ⟨h, (γ 0).property.2⟩
    exact sub_nonpos.mpr (le_of_not_gt h)
  have hn := Advanced.regular_horizon.2.2 r
    (continuous_iff_continuousAt.mpr (fun t => (norm_curve_deriv (t := t) hγ.1).continuousAt)) h0 (by
      intro t ht hr
      have hh : ‖spatial (γ t)‖ = 1 := sub_eq_zero.mp hr
      have hw := actual_inward (γ t) hh ((hγ.2 t ht).2)
      refine ⟨0, 1, radialSpeed (γ t) (velocity γ t), 0, norm_curve_deriv hγ.1,
        le_rfl, by linarith, by linarith⟩)
  intro h
  exact (not_lt_of_ge (sub_nonpos.mp hn)) h.1

end
end NoHair.TwoCentre.Model.Curves

open NoHair.TwoCentre.Model.Curves

theorem solution (γ : ℝ → manifold) (hγ : IsFutureTimelikeCurveIn metric orientation univ γ)
    (hstart : γ 0 ∉ outer) : γ 1 ∉ outer := Curves.no_escape γ hγ hstart
