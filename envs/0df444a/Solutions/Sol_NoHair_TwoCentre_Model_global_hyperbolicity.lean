-- Prove2me | solution 1 for NoHair.TwoCentre.Model.global_hyperbolicity
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T22:18:10.507814+00:00
-- url     : https://prove2.me/submissions/e866c779-0ca4-47bf-b657-9d2af8b7a038

import Theorems.Thm_NoHair_TwoCentre_Model_closed_causal_diamonds
import Theorems.Thm_NoHair_TwoCentre_optical_confinement
import Theorems.Thm_NoHair_TwoCentre_Cartesian_exterior_and_frontier
import Theorems.Thm_NoHair_TwoCentre_Model_stationary_geometry

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


end
end NoHair.TwoCentre.Model.Curves


open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Filter Topology
open scoped ContDiff Manifold RealInnerProductSpace BigOperators

namespace NoHair.TwoCentre.Model.Signals

noncomputable section

private theorem spatial_cont : Continuous spatial := by
  have h : ContDiff ℝ ∞ spatial := contDiff_euclidean.2 (fun i => contDiff_piLp_apply (p := 2) (i := i.succ))
  exact h.continuous

private theorem outer_open : IsOpen Model.outer := by
  have h : IsOpen outerRegion := (isOpen_lt continuous_const spatial_cont.norm).inter
    (isOpen_ne_fun spatial_cont continuous_const)
  exact h.preimage continuous_subtype_val

private theorem outer_subset : outerRegion ⊆ spacetime := by
  intro z hz
  exact ⟨lt_trans (by norm_num) hz.1, hz.2⟩

private theorem model_chart_val {y : E4} (hy : y ∈ exterior) :
    (Model.chart y : E4) = toAdvanced y := by
  obtain ⟨_, hmap, _⟩ := Cartesian.exterior_and_frontier.2.1
  simp [Model.chart, outer_subset (hmap hy)]

private theorem model_chart_diffeo : IsDiffeoOnto Model.chart exterior Model.outer := by
  obtain ⟨χ, hf, hb, hl, hr, hfs, hbs⟩ := Cartesian.exterior_and_frontier.2.1
  have hm : MapsTo Model.chart exterior Model.outer := by
    intro y hy
    change (Model.chart y : E4) ∈ outerRegion
    rw [model_chart_val hy]
    exact hf hy
  refine ⟨χ ∘ Subtype.val, hm, (fun _ hy => hb hy), ?_, ?_, ?_, ?_⟩
  · intro y hy
    change χ (Model.chart y : E4) = y
    rw [model_chart_val hy, hl hy]
  · intro z hz
    apply Subtype.ext
    exact (model_chart_val (hb hz)).trans (hr hz)
  · intro y hy
    apply (ContMDiffWithinAt.subtypeVal_comp_iff manifold Model.chart exterior y).mp
    exact hfs.congr (fun _ hz => model_chart_val hz) y hy
  · exact hbs.comp (contMDiff_subtype_val.contMDiffOn) (fun _ hz => hz)

private theorem exterior_isOpen : IsOpen exterior := by
  have h (c : ℝ) : Continuous (squaredDistance c) := by unfold squaredDistance; fun_prop
  exact (isOpen_lt continuous_const (h (-1))).inter (isOpen_lt continuous_const (h 1))

private abbrev L (y : E4) := mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) Model.chart y

private theorem L_onto {y : E4} (hy : y ∈ exterior) : Function.Surjective (L y) := by
  obtain ⟨χ, hmap, hinv, hleft, hright, hs, ht⟩ := model_chart_diffeo
  have hx := hmap hy
  have hcomp : (Model.chart ∘ χ) =ᶠ[𝓝 (Model.chart y)] id :=
    Filter.mem_of_superset (outer_open.mem_nhds hx) (fun _ hz => hright hz)
  have hf := ((hs _ (hinv hx)).contMDiffAt (exterior_isOpen.mem_nhds (hinv hx))).mdifferentiableAt (by simp)
  have hi := ((ht _ hx).contMDiffAt (outer_open.mem_nhds hx)).mdifferentiableAt (by simp)
  have hder : mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) (Model.chart ∘ χ) (Model.chart y) =
      ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, E4) (Model.chart y)) := hcomp.mfderiv_eq.trans mfderiv_id
  rw [mfderiv_comp _ hf hi, hleft hy] at hder
  intro v
  exact ⟨mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) χ (Model.chart y) v, DFunLike.congr_fun hder v⟩

private theorem Upos (y : E4) : 0 < harmonicPotential y := by
  have h (c : ℝ) : 0 ≤ inverseDistance c y := by unfold inverseDistance; positivity
  unfold harmonicPotential
  linarith [h (-1), h 1]

private theorem metric_pullback {y : E4} (hy : y ∈ exterior) (v w : E4) :
    metric (Model.chart y) (L y v) (L y w) = -(v 0 * w 0) / harmonicPotential y ^ 2 +
      harmonicPotential y ^ 2 * ⟪spatial v, spatial w⟫ := by
  obtain ⟨_, _, _, _, _, _, _, hmatch⟩ := Model.stationary_geometry
  let B : E4 →L[ℝ] E4 →L[ℝ] ℝ := metric (Model.chart y)
  let A : E4 →L[ℝ] E4 := L y
  have expand (x : E4) : ∑ i, x i • coordBasis i = x := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, coordBasis] using
      (EuclideanSpace.basisFun (Fin 4) ℝ).sum_repr x
  have hbas (i j : Fin 4) : B (A (coordBasis i)) (A (coordBasis j)) = isotropicMetric y i j :=
    congrFun (congrFun (hmatch y hy).1 i) j
  change B (A v) (A w) = _
  calc
    _ = B (A (∑ i, v i • coordBasis i)) (A (∑ i, w i • coordBasis i)) := by rw [expand v, expand w]
    _ = _ := by
      simp only [Curves.spatial_inner, Fin.sum_univ_four]
      simp (config := {decide := true}) [hbas, isotropicMetric]
      ring

private theorem chart_time {y : E4} (hy : y ∈ exterior) : L y (coordBasis 0) = (coordBasis 0 : E4) := by
  have hreg (s : ℝ) : y + s • coordBasis 0 ∈ exterior := by
    simpa (config := {decide := true}) [exterior, squaredDistance, coordBasis] using hy
  have hs (s : ℝ) : spatial (y + s • coordBasis 0) = spatial y := by ext i; simp [spatial, coordBasis]
  have ht (s : ℝ) : (Model.chart (y + s • coordBasis 0) : E4) = (Model.chart y : E4) + s • coordBasis 0 := by
    rw [model_chart_val (hreg s), model_chart_val hy]
    simp only [toAdvanced, hs]
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [coordinates, coordBasis]
      ring
    · simp [coordinates, coordBasis]
  have h0 : y + (0 : ℝ) • coordBasis 0 = y := by simp
  have hγ : HasDerivAt (fun s : ℝ => y + s • coordBasis 0) (coordBasis 0) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (coordBasis 0)).const_add y
  have ⟨_, _, _, _, _, smooth, _⟩ := model_chart_diffeo
  let b := Model.chart y
  have hval : HasMFDerivAt 𝓘(ℝ, E4) 𝓘(ℝ, E4) (Subtype.val : manifold → E4) b
      (ContinuousLinearMap.id ℝ E4) := by
    have d : MDifferentiableAt 𝓘(ℝ, E4) 𝓘(ℝ, E4) (Subtype.val : manifold → E4) b :=
      contMDiff_subtype_val.mdifferentiableAt (n := (1 : ℕ∞ω)) one_ne_zero
    have he : mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) (Subtype.val : manifold → E4) b =
        ContinuousLinearMap.id ℝ E4 := mfderiv_extChartAt_self (I := 𝓘(ℝ, E4)) (x := b)
    exact he ▸ d.hasMFDerivAt
  have df : HasFDerivAt (fun z => (Model.chart z : E4)) (L y : E4 →L[ℝ] E4) y :=
    hasMFDerivAt_iff_hasFDerivAt.mp (hval.comp y
      (((smooth y hy).contMDiffAt (exterior_isOpen.mem_nhds hy)).mdifferentiableAt (by simp)).hasMFDerivAt)
  have df0 : HasFDerivAt (fun z => (Model.chart z : E4)) (L y : E4 →L[ℝ] E4) (y + (0 : ℝ) • coordBasis 0) := by rwa [h0]
  have hact := HasFDerivAt.comp_hasDerivAt (l := fun z : E4 => (Model.chart z : E4))
    (f := fun s : ℝ => y + s • coordBasis 0) (0 : ℝ) df0 hγ
  simp only [Function.comp_def] at hact
  have hdes : HasDerivAt (fun s : ℝ => (Model.chart y : E4) + s • coordBasis 0) (coordBasis 0) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (coordBasis 0)).const_add (Model.chart y : E4)
  rw [show (fun s : ℝ => (Model.chart (y + s • coordBasis 0) : E4)) = _ from funext ht] at hact
  exact hact.unique hdes

private theorem time_orientation_pair (z : manifold) (hz : z ∈ Model.outer) :
    metric z (coordBasis 0) (orientation z) < 0 := by
  let p := parameters z
  have hpr : 0 < p.1 := sub_pos.mpr hz.1
  have hH : 0 < Advanced.H p := by
    have hd : 0 ≤ 1 / Advanced.distanceToOther p := by unfold Advanced.distanceToOther; positivity
    unfold Advanced.H
    nlinarith [mul_nonneg hpr.le (show 0 ≤ 1 + 1 / Advanced.distanceToOther p by linarith)]
  have hH0 : 0 < Advanced.H₀ p := by unfold Advanced.H₀; linarith
  have hvr : 0 < Advanced.gvr p := by unfold Advanced.gvr; positivity
  have hvv : Advanced.gvv p < 0 := div_neg_of_neg_of_pos (neg_lt_zero.mpr (sq_pos_of_pos hpr)) (sq_pos_of_pos hH)
  let a := Advanced.gvr p / (1 + Advanced.grr p ^ 2)
  have ha : 0 < a := by dsimp [a]; positivity
  let T : E4 := orientation z
  have hT : spatial T = -a • angularDirection z := Model.spatial_coordinates _ _
  have hVT : T 0 = 1 := rfl
  have hn : Curves.radialSpeed z T = -a := by
    change ⟪angularDirection z, spatial T⟫ = -a
    rw [hT, real_inner_smul_right, real_inner_self_eq_norm_sq, Curves.angular_unit]
    ring
  have hs0 : spatial (coordBasis 0) = 0 := by ext i; simp [spatial, coordBasis]
  have h0 : Curves.radialSpeed z (coordBasis 0) = 0 := by simp [Curves.radialSpeed, hs0]
  change metric z (coordBasis 0) T < 0
  rw [Curves.metric_eval, hVT, h0, hn, hs0, inner_zero_left]
  change Advanced.gvv p * 1 * 1 + Advanced.gvr p * (1 * -a + 0 * 1) + _ * 0 * -a + _ * (0 - 0 * -a) < 0
  nlinarith [mul_pos ha hvr]

private noncomputable def iso : manifold → E4 := Classical.choose model_chart_diffeo
private theorem iso_spec :
    MapsTo Model.chart exterior Model.outer ∧ MapsTo iso Model.outer exterior ∧
    LeftInvOn iso Model.chart exterior ∧ RightInvOn iso Model.chart Model.outer ∧
    ContMDiffOn 𝓘(ℝ, E4) 𝓘(ℝ, E4) ∞ Model.chart exterior ∧
    ContMDiffOn 𝓘(ℝ, E4) 𝓘(ℝ, E4) ∞ iso Model.outer := Classical.choose_spec model_chart_diffeo

private theorem optical_future {y : E4} (hy : y ∈ exterior) (v : E4)
    (hf : IsFutureCausal metric orientation (Model.chart y) (L y v)) :
    0 < v 0 ∧ harmonicPotential y ^ 2 * ‖spatial v‖ ≤ v 0 := by
  let u := harmonicPotential y
  have hu : 0 < u := Upos y
  have hs0 : spatial (coordBasis 0) = 0 := by ext i; simp [spatial, coordBasis]
  obtain ⟨_, hm, _⟩ := model_chart_diffeo
  obtain ⟨_, _, _, _, hor, _⟩ := Model.stationary_geometry
  obtain ⟨w₀, hw₀⟩ := L_onto hy (orientation (Model.chart y))
  let w : E4 := w₀
  have hw : L y w = orientation (Model.chart y) := hw₀
  have hww := (metric_pullback hy w w).symm.trans_lt (show metric (Model.chart y) (L y w) (L y w) < 0 by
    rw [hw]; exact hor.2 _)
  have hwt := (metric_pullback hy (coordBasis 0) w).symm.trans_lt
    (show metric (Model.chart y) (L y (coordBasis 0)) (L y w) < 0 by
      rw [chart_time hy, hw]; exact time_orientation_pair _ (hm hy))
  rw [hs0, inner_zero_left] at hwt
  have hwpos : 0 < w 0 := by
    change -(1 * w 0) / u ^ 2 + u ^ 2 * 0 < 0 at hwt
    simpa [neg_div, hu.le, div_pos_iff_of_pos_right (sq_pos_of_pos hu)] using hwt
  rw [real_inner_self_eq_norm_sq] at hww
  have bound (a : E4) (hn : -(a 0 * a 0) / u ^ 2 + u ^ 2 * ‖spatial a‖ ^ 2 ≤ 0) :
      u ^ 2 * ‖spatial a‖ ≤ |a 0| := by
    have hsq := (le_div_iff₀ (sq_pos_of_pos hu)).mp (show u ^ 2 * ‖spatial a‖ ^ 2 ≤ (a 0 * a 0) / u ^ 2 by
      rw [neg_div] at hn; linarith)
    nlinarith [sq_abs (a 0), abs_nonneg (a 0), mul_nonneg (sq_nonneg u) (norm_nonneg (spatial a))]
  have hwbound : u ^ 2 * ‖spatial w‖ ≤ w 0 := (abs_of_pos hwpos) ▸ bound w hww.le
  have hvv := (metric_pullback hy v v).symm.trans_le hf.2.1
  rw [real_inner_self_eq_norm_sq] at hvv
  have hvbound := bound v hvv
  have hvpos : 0 < v 0 := by
    by_contra! hvneg
    rw [abs_of_nonpos hvneg] at hvbound
    have hi := (abs_le.mp (abs_real_inner_le_norm (spatial v) (spatial w))).1
    have hp := mul_le_mul hvbound hwbound (mul_nonneg (sq_nonneg u) (norm_nonneg _)) (neg_nonneg.mpr hvneg)
    have hpair := (metric_pullback hy v w).symm.trans_lt (show metric (Model.chart y) (L y v) (L y w) < 0 by
      rw [hw]; exact hf.2.2)
    change -(v 0 * w 0) / u^2 + u^2 * ⟪spatial v, spatial w⟫ < 0 at hpair
    rw [neg_div] at hpair
    have hpair' := (lt_div_iff₀ (sq_pos_of_pos hu)).mp
      (show u ^ 2 * ⟪spatial v, spatial w⟫ < v 0 * w 0 / u ^ 2 by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hi (sq_nonneg (u ^ 2))]
  exact ⟨hvpos, (abs_of_pos hvpos) ▸ hvbound⟩

private def isoV (γ : ℝ → manifold) (t : ℝ) : E4 :=
  mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) iso (γ t) (velocity γ t)

set_option backward.isDefEq.respectTransparency false in
private theorem lift_causal {γ : ℝ → manifold}
    (h : IsFutureCausalCurveIn metric orientation Model.outer γ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivAt (fun s => iso (γ s)) (isoV γ t) t ∧ iso (γ t) ∈ exterior ∧
    0 < isoV γ t 0 ∧ harmonicPotential (iso (γ t)) ^ 2 * ‖spatial (isoV γ t)‖ ≤ isoV γ t 0 := by
  obtain ⟨_, hb, _, hr, hs, hi⟩ := iso_spec
  have hz := (h.2 t ht).1
  have hy := hb hz
  have hchi := ((hi _ hz).contMDiffAt (outer_open.mem_nhds hz)).mdifferentiableAt (by simp)
  have hchart := ((hs _ hy).contMDiffAt (exterior_isOpen.mem_nhds hy)).mdifferentiableAt (by simp)
  have hcurve := (h.1.mdifferentiableAt (by simp) (x := t)).hasMFDerivAt
  have hcomp : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E4) (iso ∘ γ) t
      ((mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) iso (γ t)).comp (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E4) γ t)) :=
    hchi.hasMFDerivAt.comp t hcurve
  have der : HasDerivAt (fun s => iso (γ s)) (isoV γ t) t :=
    (hasMFDerivAt_iff_hasFDerivAt.mp hcomp).hasDerivAt
  have he : (Model.chart ∘ iso) =ᶠ[𝓝 (γ t)] id :=
    Filter.mem_of_superset (outer_open.mem_nhds hz) (fun x hx => hr hx)
  have hD : mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) (Model.chart ∘ iso) (γ t) =
      ContinuousLinearMap.id ℝ E4 := he.mfderiv_eq.trans mfderiv_id
  rw [mfderiv_comp _ hchart hchi] at hD
  have hdv : L (iso (γ t)) (isoV γ t) = velocity γ t := DFunLike.congr_fun hD _
  have hca : IsFutureCausal metric orientation (Model.chart (iso (γ t))) (L (iso (γ t)) (isoV γ t)) := by
    rw [hdv, hr hz]
    exact (h.2 t ht).2
  exact ⟨der,hy,optical_future hy _ hca⟩

private def clock (z : manifold) := iso z 0

private theorem interval_strict {γ : ℝ → manifold}
    (h : IsFutureCausalCurveIn metric orientation Model.outer γ) :
    StrictMonoOn (fun t => clock (γ t)) (Icc (0 : ℝ) 1) := by
  have hh (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s => clock (γ s)) (isoV γ t 0) t := by
    exact (PiLp.proj (p := 2) (β := fun _ : Fin 4 => ℝ) 0).hasFDerivAt.comp_hasDerivAt t (lift_causal h ht).1
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (fun t ht => (hh t ht).continuousAt.continuousWithinAt)
  intro t ht
  have ht' := interior_subset ht
  rw [(hh t ht').deriv]
  exact (lift_causal h ht').2.2.1

private theorem future_clock {p q : manifold} (hq : q ∈ causalFuture metric orientation Model.outer p) :
    clock p ≤ clock q := by
  rcases hq with eq | ⟨γ,h,hs,he⟩
  · exact le_of_eq (congrArg clock eq.symm)
  · have hlt := interval_strict h (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one) zero_lt_one
    simpa [hs,he] using hlt.le

private theorem spatial_dist (c : ℝ) (y : E4) :
    ‖spatial y - c • unitAxis‖ ^ 2 = squaredDistance c y := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp [spatial, unitAxis, squaredDistance, PiLp.sub_apply, PiLp.smul_apply]

private theorem iso_regular (y : E4) :
    y ∈ exterior ↔ spatial y ≠ -unitAxis ∧ spatial y ≠ unitAxis := by
  change 0 < squaredDistance (-1) y ∧ 0 < squaredDistance 1 y ↔ _
  rw [← spatial_dist, ← spatial_dist, neg_one_smul, one_smul]
  simp only [sq_pos_iff, norm_ne_zero_iff, sub_ne_zero]

private theorem optical_factor (y : E4) :
    harmonicPotential y = 1 + 1 / ‖spatial y - (-unitAxis)‖ + 1 / ‖spatial y - unitAxis‖ := by
  unfold harmonicPotential inverseDistance
  simp [← spatial_dist, Real.sqrt_sq (norm_nonneg _)]

private theorem spatial_deriv {f : ℝ → E4} {v : E4} {t : ℝ} (hd : HasDerivAt f v t) :
    HasDerivAt (fun s => spatial (f s)) (spatial v) t := by
  let A : E4 →L[ℝ] E3 := LinearMap.toContinuousLinearMap {
    toFun := spatial, map_add' := fun _ _ => by ext; rfl, map_smul' := fun _ _ => by ext; rfl }
  exact A.hasFDerivAt.comp_hasDerivAt t hd

private theorem time_deriv {f : ℝ → E4} {v : E4} {t : ℝ} (hd : HasDerivAt f v t) :
    HasDerivAt (fun s => f s 0) (v 0) t :=
  (PiLp.proj (p := 2) (β := fun _ : Fin 4 => ℝ) 0).hasFDerivAt.comp_hasDerivAt t hd

private theorem join_coords (z : E4) : coordinates (z 0) (spatial z) = z := by
  ext i
  exact Fin.cases rfl (fun _ => rfl) i

private theorem coord_cont : Continuous (fun p : ℝ × E3 => coordinates p.1 p.2) := by
  have h : ContDiff ℝ ∞ (fun p : ℝ × E3 => coordinates p.1 p.2) := by
    apply contDiff_euclidean.2
    intro i
    refine Fin.cases (by exact contDiff_fst) (fun j => ?_) i
    simp only [coordinates, WithLp.ofLp_toLp, Fin.cons_succ]
    fun_prop
  exact h.continuous

theorem hyperbolicity_from_closed
    (hcl : ∀ p ∈ Model.outer, ∀ q ∈ Model.outer,
      IsClosed (causalFuture metric orientation Model.outer p ∩ causalPast metric orientation Model.outer q)) :
    IsGloballyHyperbolicOn metric orientation Model.outer := by
  constructor
  · rintro p _ ⟨γ,h,hs,he⟩
    have lt := interval_strict h (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one) zero_lt_one
    simp [hs,he] at lt
  · intro p hp q hq
    obtain ⟨_, hback, _, hright, hsm, _⟩ := iso_spec
    let x₀ := spatial (iso p)
    have hreg := (iso_regular (iso p)).mp (hback hp)
    let budget := max 0 (clock q - clock p)
    obtain ⟨K, hc, h₁, h₂, htrap⟩ := optical_confinement (-unitAxis) unitAxis x₀ hreg.1 hreg.2
      budget (le_max_left _ _)
    let box := (Icc (clock p) (clock q)) ×ˢ (insert x₀ K)
    let ψ : ℝ × E3 → manifold := fun u => Model.chart (coordinates u.1 u.2)
    have hcomp : IsCompact box := isCompact_Icc.prod (hc.insert _)
    have hcoords : MapsTo (fun u : ℝ × E3 => coordinates u.1 u.2) box exterior := by
      intro u hu
      rw [iso_regular, Model.spatial_coordinates]
      rcases hu.2 with eq | hm
      · rw [eq]
        exact hreg
      · exact ⟨fun e => h₁ (e ▸ hm),fun e => h₂ (e ▸ hm)⟩
    have hψ : ContinuousOn ψ box := hsm.continuousOn.comp coord_cont.continuousOn hcoords
    apply (hcomp.image_of_continuousOn hψ).of_isClosed_subset (hcl p hp q hq)
    intro z hz
    have htime : clock z ∈ Icc (clock p) (clock q) := ⟨future_clock hz.1, future_clock hz.2⟩
    have hzin : z ∈ Model.outer ∧ spatial (iso z) ∈ insert x₀ K := by
      rcases hz.1 with hzp | ⟨γ,h,hs,he⟩
      · rw [show z = p from hzp]
        exact ⟨hp, mem_insert _ _⟩
      · have hstart : spatial (iso (γ 0)) = x₀ := by rw [hs]
        have hopt (s : ℝ) (hs' : s ∈ Icc (0 : ℝ) 1) :
            HasDerivAt (fun t => spatial (iso (γ t))) (spatial (isoV γ s)) s ∧
            HasDerivAt (fun t => iso (γ t) 0) (isoV γ s 0) s ∧
            spatial (iso (γ s)) ≠ -unitAxis ∧ spatial (iso (γ s)) ≠ unitAxis ∧
            (1 + 1 / ‖spatial (iso (γ s)) - (-unitAxis)‖ + 1 / ‖spatial (iso (γ s)) - unitAxis‖)^2 *
              ‖spatial (isoV γ s)‖ ≤ isoV γ s 0 := by
          obtain ⟨hd,hy,_,hv⟩ := lift_causal h hs'
          exact ⟨spatial_deriv hd,time_deriv hd,(iso_regular _).mp hy |>.1,(iso_regular _).mp hy |>.2,
            (optical_factor _ ▸ hv)⟩
        have htravel : iso (γ 1) 0 - iso (γ 0) 0 ≤ budget := by
          change clock (γ 1) - clock (γ 0) ≤ budget
          rw [he,hs]
          exact (sub_le_sub_right htime.2 _).trans (le_max_right _ _)
        have hend := htrap (fun s => spatial (iso (γ s))) (fun s => spatial (isoV γ s))
          (fun s => iso (γ s) 0) (fun s => isoV γ s 0) hstart hopt 1 (right_mem_Icc.mpr zero_le_one) htravel
        refine ⟨he ▸ (h.2 1 (right_mem_Icc.mpr zero_le_one)).1, Or.inr ?_⟩
        simpa only [he] using hend
    refine ⟨(clock z,spatial (iso z)),⟨htime,hzin.2⟩,?_⟩
    change Model.chart (coordinates (iso z 0) (spatial (iso z))) = z
    rw [join_coords, hright hzin.1]

end
end NoHair.TwoCentre.Model.Signals

open NoHair.TwoCentre.Model.Signals

theorem solution : IsGloballyHyperbolicOn metric orientation Model.outer :=
  hyperbolicity_from_closed Model.closed_causal_diamonds
