-- Prove2me | solution 1 for NoHair.TwoCentre.Model.chronological_access
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T22:08:02.910811+00:00
-- url     : https://prove2.me/submissions/f56c4b3f-83cd-40f6-b63b-794c91c91924

import Theorems.Thm_NoHair_TwoCentre_Cartesian_exterior_and_frontier
import Theorems.Thm_NoHair_TwoCentre_isotropic_electrovac_and_decay
import Theorems.Thm_NoHair_TwoCentre_Model_stationary_geometry
import Theorems.Thm_NoHair_TwoCentre_Model_no_escape

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

private theorem orient_isotropic {y : E4} (hy : y ∈ exterior) (v : E4)
    (hv : 0 < v 0) (ht : harmonicPotential y ^ 2 * ‖spatial v‖ < v 0) :
    IsFutureTimelike metric orientation (Model.chart y) (L y v) := by
  let u := harmonicPotential y
  have hu : 0 < u := Upos y
  have hs0 : spatial (coordBasis 0) = 0 := by ext i; simp [spatial, coordBasis]
  have ⟨_, hm, _⟩ := model_chart_diffeo
  obtain ⟨_, _, _, _, hor, _⟩ := Model.stationary_geometry
  obtain ⟨w₀, hw₀⟩ := L_onto hy (orientation (Model.chart y))
  let w : E4 := w₀
  have hw : L y w = orientation (Model.chart y) := hw₀
  have hww := (metric_pullback hy w w).symm.trans_lt (show metric (Model.chart y) (L y w) (L y w) < 0 by
    rw [hw]; exact hor.2 _)
  rw [real_inner_self_eq_norm_sq] at hww
  have htkw : metric (Model.chart y) (L y (coordBasis 0)) (L y w) < 0 := by
    rw [chart_time hy, hw]; exact time_orientation_pair _ (hm hy)
  have hwt := (metric_pullback hy (coordBasis 0) w).symm.trans_lt htkw
  rw [hs0, inner_zero_left] at hwt
  have hwpos : 0 < w 0 := by
    change -(1 * w 0) / u ^ 2 + u ^ 2 * 0 < 0 at hwt
    simp only [one_mul, mul_zero, add_zero, neg_div, neg_lt_zero] at hwt
    exact (div_pos_iff_of_pos_right (sq_pos_of_pos hu)).mp hwt
  have hwfast : u ^ 2 * ‖spatial w‖ < w 0 := by
    have hsq := (lt_div_iff₀ (sq_pos_of_pos hu)).mp (show u ^ 2 * ‖spatial w‖ ^ 2 < (w 0 * w 0) / u ^ 2 by
      change -(w 0 * w 0) / u ^ 2 + u ^ 2 * ‖spatial w‖ ^ 2 < 0 at hww
      rw [neg_div] at hww
      linarith)
    nlinarith [mul_nonneg (sq_nonneg u) (norm_nonneg (spatial w))]
  change u ^ 2 * ‖spatial v‖ < v 0 at ht
  have gneg (a b : E4) (ha : u ^ 2 * ‖spatial a‖ < a 0)
      (hb : u ^ 2 * ‖spatial b‖ < b 0) (hb' : 0 < b 0) :
      metric (Model.chart y) (L y a) (L y b) < 0 := by
    rw [metric_pullback hy]
    have hmul := mul_le_mul_of_nonneg_left hb.le (mul_nonneg (sq_nonneg u) (norm_nonneg (spatial a)))
    have hmul' := mul_lt_mul_of_pos_right ha hb'
    have hinner := real_inner_le_norm (spatial a) (spatial b)
    change -(a 0 * b 0) / u ^ 2 + u ^ 2 * ⟪spatial a, spatial b⟫ < 0
    have hcrit : u ^ 2 * ⟪spatial a, spatial b⟫ < a 0 * b 0 / u ^ 2 := by
      apply (lt_div_iff₀ (sq_pos_of_pos hu)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hinner (sq_nonneg (u ^ 2))]
    rw [neg_div]
    linarith
  exact ⟨gneg v v ht ht hv, hw ▸ gneg v w ht hwfast hwpos⟩

private theorem affine_timelike (y v : E4) (hreg : ∀ s : ℝ, y + s • v ∈ exterior) (hv : 0 < v 0)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, harmonicPotential (y + t • v) ^ 2 * ‖spatial v‖ < v 0) :
    IsFutureTimelikeCurveIn metric orientation univ (fun s : ℝ => Model.chart (y + s • v)) := by
  obtain ⟨_, _, _, _, _, hs, _⟩ := model_chart_diffeo
  let q := fun s : ℝ => y + s • v
  have ds (s : ℝ) : ContMDiffAt 𝓘(ℝ, E4) 𝓘(ℝ, E4) ∞ Model.chart (q s) :=
    (hs _ (hreg s)).contMDiffAt (exterior_isOpen.mem_nhds (hreg s))
  have dq : ContDiff ℝ ∞ q := by dsimp [q]; fun_prop
  refine ⟨fun s => ((ds s).of_le (by simp)).comp s ((dq.of_le (by simp)).contMDiff s), ?_⟩
  intro t ht
  refine ⟨mem_univ _, ?_⟩
  have ha : HasDerivAt q v t := by simpa [q] using ((hasDerivAt_id t).smul_const v).const_add y
  have dL : velocity (fun s : ℝ => Model.chart (y + s • v)) t = L (q t) v := by
    unfold velocity L
    change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E4) (Model.chart ∘ q) t 1 = _
    rw [mfderiv_comp _ ((ds t).mdifferentiableAt (by simp)) (dq.contMDiff.mdifferentiableAt (by simp)),
      mfderiv_eq_fderiv]
    exact congrArg (fun a : E4 => L (q t) a) ((ha.differentiableAt.hasFDerivAt.hasDerivAt).unique ha)
  rw [dL]
  exact orient_isotropic (hreg t) v hv (hb t ht)

private theorem line_avoids_poles {y : E4} (hy : y ∈ exterior) :
    ∃ k : Fin 4, k ≠ 0 ∧ ∀ s : ℝ, y + s • coordBasis k ∈ exterior := by
  by_cases ha : y 2 = 0 ∧ y 3 = 0
  · refine ⟨2, by decide, ?_⟩
    have h (c : ℝ) (hc : 0 < squaredDistance c y) (s : ℝ) : 0 < squaredDistance c (y + s • coordBasis 2) := by
      simp (config := {decide := true}) [squaredDistance, coordBasis, ha.1, ha.2] at hc ⊢
      nlinarith [sq_nonneg s]
    exact fun s => ⟨h _ hy.1 s, h _ hy.2 s⟩
  · refine ⟨1, by decide, ?_⟩
    have hperp : 0 < y 2 ^ 2 + y 3 ^ 2 := by
      by_cases h : y 2 = 0
      · have hz : y 3 ≠ 0 := fun hz => ha ⟨h, hz⟩
        linarith [sq_pos_of_ne_zero hz, sq_nonneg (y 2)]
      · linarith [sq_pos_of_ne_zero h, sq_nonneg (y 3)]
    have h (c s : ℝ) : 0 < squaredDistance c (y + s • coordBasis 1) := by
      simp (config := {decide := true}) [squaredDistance, coordBasis]
      nlinarith [sq_nonneg (y 1 + s - c)]
    exact fun s => ⟨h _ s, h _ s⟩

private theorem spatial_radius_bound (y : E4) {k : Fin 4} (hk : k ≠ 0) : |y k| ≤ spatialRadius y := by
  have hR : 0 ≤ spatialRadius y := Real.sqrt_nonneg _
  have hR2 : spatialRadius y ^ 2 = y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2 := Real.sq_sqrt (by positivity)
  rw [← sq_le_sq₀ (abs_nonneg _) hR, sq_abs]
  fin_cases k
  · exact False.elim (hk rfl)
  · change y 1 ^ 2 ≤ _
    linarith [sq_nonneg (y 2), sq_nonneg (y 3)]
  · change y 2 ^ 2 ≤ _
    linarith [sq_nonneg (y 1), sq_nonneg (y 3)]
  · change y 3 ^ 2 ≤ _
    linarith [sq_nonneg (y 1), sq_nonneg (y 2)]

private theorem U_cont {z : E4} (hz : z ∈ exterior) : ContinuousAt harmonicPotential z := by
  have h (c : ℝ) (hc : 0 < squaredDistance c z) : ContinuousAt (inverseDistance c) z := by
    unfold inverseDistance
    apply continuousAt_const.div
    · unfold squaredDistance
      fun_prop
    · exact (Real.sqrt_pos.mpr hc).ne'
  exact (continuousAt_const.add (h (-1) hz.1)).add (h 1 hz.2)

private theorem temporal_shift (u : E4) (s : ℝ) (c : ℝ) :
    squaredDistance c (u + s • coordBasis 0) = squaredDistance c u := by
  simp (config := {decide := true}) [squaredDistance, coordBasis]

private theorem signals_at {y : E4} (hy : y ∈ exterior) :
    Model.chart y ∈ chronoPastSet metric orientation (Model.chart '' exteriorRegion 2) ∧
    Model.chart y ∈ chronoFutureSet metric orientation (Model.chart '' exteriorRegion 2) := by
  obtain ⟨k, hk, hline⟩ := line_avoids_poles hy
  let d := |y k| + 3
  let x (s : ℝ) := y + (s * d) • coordBasis k
  let b := ‖spatial (d • coordBasis k)‖
  have hcx : Continuous x := by dsimp [x]; fun_prop
  have hcb : ContinuousOn (fun s => harmonicPotential (x s) ^ 2 * b) (Icc (-1 : ℝ) 1) := by
    intro s _
    have hr : x s ∈ exterior := hline (s * d)
    exact ((((U_cont hr).comp (f := x) hcx.continuousAt).pow 2).mul continuousAt_const).continuousWithinAt
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hcb
  have hBd (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 1) : harmonicPotential (x s) ^ 2 * b ≤ B := hB ⟨s, hs, rfl⟩
  have hB0 : 0 ≤ B := (mul_nonneg (sq_nonneg _) (norm_nonneg _)).trans (hBd 0 (by constructor <;> norm_num))
  let v := d • coordBasis k + (B + 1) • coordBasis 0
  have hv0 : v 0 = B + 1 := by simp [v, coordBasis, Ne.symm hk]
  have hvsp : spatial v = spatial (d • coordBasis k) := by ext i; simp [v, spatial, coordBasis]
  have hpath (t : ℝ) : y + t • v = x t + (t * (B + 1)) • coordBasis 0 := by
    dsimp [v, x]
    rw [smul_add, smul_smul, smul_smul, add_assoc]
  have hreg (t : ℝ) : y + t • v ∈ exterior := by
    rw [hpath]
    exact ⟨(temporal_shift _ _ _).symm ▸ (hline (t * d)).1, (temporal_shift _ _ _).symm ▸ (hline (t * d)).2⟩
  have hU (t : ℝ) : harmonicPotential (y + t • v) = harmonicPotential (x t) := by
    simp only [hpath, harmonicPotential, inverseDistance, temporal_shift]
  have hbound (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 1) : harmonicPotential (y + s • v) ^ 2 * ‖spatial v‖ < v 0 := by
    rw [hU, hvsp, hv0]
    exact lt_of_le_of_lt (hBd s hs) (by linarith)
  have hv : 0 < v 0 := by rw [hv0]; linarith
  have hf := affine_timelike y v hreg hv (fun t ht => hbound t ⟨by linarith [ht.1], ht.2⟩)
  have hback (t : ℝ) : (y - v) + t • v = y + (t - 1) • v := by rw [sub_smul, one_smul]; abel
  have hb := affine_timelike (y - v) v (fun s => (hback s).symm ▸ hreg (s - 1)) hv (fun t ht => by
    rw [hback]; exact hbound _ ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have hvk : v k = d := by simp [v, coordBasis, hk]
  have hfar : y + (1 : ℝ) • v ∈ exteriorRegion 2 := by
    have h := (le_abs_self _).trans (spatial_radius_bound (y + (1 : ℝ) • v) hk)
    simp only [one_smul, PiLp.add_apply, hvk] at h
    change 2 < spatialRadius _
    simp only [one_smul]
    dsimp [d] at h
    linarith [(abs_le.mp (le_refl |y k|)).1]
  have hfar' : y - v ∈ exteriorRegion 2 := by
    have h := (neg_le_abs _).trans (spatial_radius_bound (y - v) hk)
    simp only [PiLp.sub_apply, hvk] at h
    change 2 < spatialRadius _
    dsimp [d] at h
    linarith [le_abs_self (y k)]
  constructor
  · refine mem_iUnion.mpr ⟨Model.chart (y + (1 : ℝ) • v), mem_iUnion.mpr ⟨⟨_, hfar, rfl⟩, ?_⟩⟩
    exact ⟨_, hf, by simp, rfl⟩
  · refine mem_iUnion.mpr ⟨Model.chart (y - v), mem_iUnion.mpr ⟨⟨_, hfar', rfl⟩, ?_⟩⟩
    exact ⟨_, hb, by simp, by simp⟩

/-- Chronological communication with the far end on the full two-centre exterior. -/
theorem exterior_signals : Model.outer ⊆ chronoPastSet metric orientation (Model.chart '' exteriorRegion 2) ∧
    Model.outer ⊆ chronoFutureSet metric orientation (Model.chart '' exteriorRegion 2) := by
  obtain ⟨χ, _, hh, _, hr, _⟩ := model_chart_diffeo
  constructor <;> intro z hz
  · exact hr hz ▸ (signals_at (hh hz)).1
  · exact hr hz ▸ (signals_at (hh hz)).2

end
end NoHair.TwoCentre.Model.Signals

open NoHair.TwoCentre.Model.Signals

theorem solution :
    chronoPastSet metric orientation (Model.chart '' exteriorRegion 2) = outer ∧
    outer ⊆ chronoFutureSet metric orientation (Model.chart '' exteriorRegion 2) := by
  refine ⟨Subset.antisymm ?_ exterior_signals.1, exterior_signals.2⟩
  intro p hp
  obtain ⟨q, hq⟩ := mem_iUnion.mp hp
  obtain ⟨hq, hpq⟩ := mem_iUnion.mp hq
  obtain ⟨γ, ht, hstart, hend⟩ := hpq
  obtain ⟨_, hmap, _⟩ := model_chart_diffeo
  have hqout : q ∈ Model.outer := by
    obtain ⟨y, hy, rfl⟩ := hq
    exact hmap (isotropic_electrovac_and_decay.2 y hy).1
  by_contra hn
  exact Model.no_escape γ ht (hstart ▸ hn) (hend ▸ hqout)
