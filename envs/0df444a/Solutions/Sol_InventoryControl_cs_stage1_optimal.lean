-- Prove2me | solution 1 for InventoryControl.cs_stage1_optimal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T14:39:33.562413+00:00
-- url     : https://prove2.me/submissions/3f0ef4b9-ce6d-4cbd-94f7-e6cf90a9abce

import Mathlib
import Definitions.Def_InventoryControl_clarkScarf

open MeasureTheory ProbabilityTheory InventoryControl in
instance f4a8_isProb (mu sigma : ℝ) (n : ℕ) : IsProbabilityMeasure (csDemand mu sigma n) := by
  unfold csDemand; infer_instance

open MeasureTheory ProbabilityTheory InventoryControl in
lemma f4a8_int_id (mu sigma : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ => x) (csDemand mu sigma n) := by
  unfold csDemand newsboyDemand
  exact (memLp_id_gaussianReal 1).integrable le_rfl

open MeasureTheory ProbabilityTheory InventoryControl in
lemma f4a8_int_pos (mu sigma : ℝ) (n : ℕ) (y : ℝ) :
    Integrable (fun x : ℝ => max (x - y) 0) (csDemand mu sigma n) :=
  ((f4a8_int_id mu sigma n).sub (integrable_const y)).pos_part

open MeasureTheory ProbabilityTheory in
lemma f4a8_cdf_affine (m s x : ℝ) (hs : 0 < s) :
    cdf (gaussianReal m (Real.toNNReal (s ^ 2))) x = cdf (gaussianReal 0 1) ((x - m) / s) := by
  have hmap : gaussianReal m (Real.toNNReal (s ^ 2))
      = ((gaussianReal 0 1).map (s * ·)).map (· + m) := by
    rw [gaussianReal_map_const_mul, gaussianReal_map_add_const]
    congr 1
    · simp
    · ext
      simp [sq_nonneg]
  rw [cdf_eq_real, cdf_eq_real, hmap, Measure.map_map (by fun_prop) (by fun_prop)]
  rw [measureReal_def, measureReal_def, Measure.map_apply (by fun_prop) measurableSet_Iic]
  congr 2
  ext z
  simp only [Set.mem_preimage, Function.comp, Set.mem_Iic]
  rw [le_div_iff₀ hs]
  constructor <;> intro h <;> linarith

open MeasureTheory ProbabilityTheory InventoryControl in
lemma f4a8_stage1_convex (e1 e2 b1 mu sigma : ℝ) (L1 : ℕ) (hK : 0 ≤ e1 + e2 + b1) :
    ConvexOn ℝ Set.univ (csStage1Cost e1 e2 b1 mu sigma L1) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  unfold csStage1Cost
  have hx := f4a8_int_pos mu sigma (L1 + 1) x
  have hy := f4a8_int_pos mu sigma (L1 + 1) y
  have hxy := f4a8_int_pos mu sigma (L1 + 1) (a * x + b * y)
  have hle : ∫ u, max (u - (a * x + b * y)) 0 ∂(csDemand mu sigma (L1 + 1))
      ≤ a * ∫ u, max (u - x) 0 ∂(csDemand mu sigma (L1 + 1))
        + b * ∫ u, max (u - y) 0 ∂(csDemand mu sigma (L1 + 1)) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hx.const_mul a) (hy.const_mul b)]
    apply integral_mono hxy ((hx.const_mul a).add (hy.const_mul b))
    intro u
    have h1 : u - (a * x + b * y) = a * (u - x) + b * (u - y) := by
      have : u = a * u + b * u := by rw [← add_mul, hab, one_mul]
      linarith
    have h2 : a * (u - x) ≤ a * max (u - x) 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) ha
    have h3 : b * (u - y) ≤ b * max (u - y) 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) hb
    have h4 : 0 ≤ a * max (u - x) 0 := mul_nonneg ha (le_max_right _ _)
    have h5 : 0 ≤ b * max (u - y) 0 := mul_nonneg hb (le_max_right _ _)
    show max (u - (a * x + b * y)) 0 ≤ a * max (u - x) 0 + b * max (u - y) 0
    rw [h1]
    exact max_le (by linarith) (by linarith)
  have hK' := mul_le_mul_of_nonneg_left hle hK
  have hc : (e1 + e2) * ((((L1 + 1 : ℕ) : ℝ)) * mu)
      = a * ((e1 + e2) * ((((L1 + 1 : ℕ) : ℝ)) * mu)) + b * ((e1 + e2) * ((((L1 + 1 : ℕ) : ℝ)) * mu)) := by
    rw [← add_mul, hab, one_mul]
  push_cast at hc hK' ⊢
  nlinarith

open MeasureTheory ProbabilityTheory InventoryControl in
lemma f4a8_cdf_S1 (mu sigma : ℝ) (hs : 0 < sigma) (L1 : ℕ) (S1 : ℝ) :
    cdf (csDemand mu sigma (L1 + 1)) S1
      = cdf (gaussianReal 0 1) ((S1 - (L1 + 1) * mu) / (Real.sqrt (L1 + 1) * sigma)) := by
  have hpos : 0 < Real.sqrt ((L1 + 1 : ℕ) : ℝ) * sigma :=
    mul_pos (Real.sqrt_pos.2 (by positivity)) hs
  unfold csDemand newsboyDemand
  rw [f4a8_cdf_affine _ _ _ hpos]
  push_cast
  rfl

open MeasureTheory ProbabilityTheory InventoryControl in
lemma f4a8_S1_min (e1 e2 b1 mu sigma : ℝ) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) (hb : 0 < b1)
    (hs : 0 < sigma) (L1 : ℕ) (S1 : ℝ)
    (hS1 : cdf (gaussianReal 0 1)
      ((S1 - (L1 + 1) * mu) / (Real.sqrt (L1 + 1) * sigma)) = (e2 + b1) / (e1 + e2 + b1))
    (y : ℝ) :
    csStage1Cost e1 e2 b1 mu sigma L1 S1 ≤ csStage1Cost e1 e2 b1 mu sigma L1 y := by
  have hK : 0 < e1 + e2 + b1 := by linarith
  have hF : cdf (csDemand mu sigma (L1 + 1)) S1 = (e2 + b1) / (e1 + e2 + b1) := by
    rw [f4a8_cdf_S1 mu sigma hs]; exact hS1
  have hP : (csDemand mu sigma (L1 + 1)).real (Set.Ioi S1) = e1 / (e1 + e2 + b1) := by
    rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, ← cdf_eq_real, hF]
    field_simp
    ring
  have hy := f4a8_int_pos mu sigma (L1 + 1) y
  have hS := f4a8_int_pos mu sigma (L1 + 1) S1
  have hind : Integrable (fun x : ℝ => (S1 - y) * (Set.Ioi S1).indicator (fun _ => (1:ℝ)) x)
      (csDemand mu sigma (L1 + 1)) :=
    ((integrable_const (1:ℝ)).indicator measurableSet_Ioi).const_mul _
  have hle : ∫ x, max (x - S1) 0 ∂(csDemand mu sigma (L1 + 1))
      + ∫ x, (S1 - y) * (Set.Ioi S1).indicator (fun _ => (1:ℝ)) x ∂(csDemand mu sigma (L1 + 1))
      ≤ ∫ x, max (x - y) 0 ∂(csDemand mu sigma (L1 + 1)) := by
    rw [← integral_add hS hind]
    apply integral_mono (hS.add hind) hy
    intro x
    show max (x - S1) 0 + (S1 - y) * (Set.Ioi S1).indicator (fun _ => (1:ℝ)) x ≤ max (x - y) 0
    simp only [Set.indicator, Set.mem_Ioi]
    split_ifs with h
    · rw [max_eq_left (by linarith : (0:ℝ) ≤ x - S1)]
      have := le_max_left (x - y) 0
      linarith
    · rw [max_eq_right (by linarith : x - S1 ≤ 0)]
      have := le_max_right (x - y) 0
      linarith
  have hint : ∫ x, (S1 - y) * (Set.Ioi S1).indicator (fun _ => (1:ℝ)) x ∂(csDemand mu sigma (L1 + 1))
      = (S1 - y) * (e1 / (e1 + e2 + b1)) := by
    rw [integral_const_mul, integral_indicator_const _ measurableSet_Ioi, hP, smul_eq_mul, mul_one]
  rw [hint] at hle
  unfold csStage1Cost
  have hm := mul_le_mul_of_nonneg_left hle hK.le
  have hKe : (e1 + e2 + b1) * ((S1 - y) * (e1 / (e1 + e2 + b1))) = (S1 - y) * e1 := by
    field_simp
  rw [mul_add, hKe] at hm
  linarith

open MeasureTheory ProbabilityTheory InventoryControl in
lemma f4a8_subgrad (e1 e2 b1 mu sigma : ℝ) (hs : 0 < sigma) (L1 : ℕ) (hK : 0 ≤ e1 + e2 + b1)
    (a z : ℝ) :
    (e1 + (e1 + e2 + b1) * (cdf (gaussianReal 0 1)
        ((a - (L1 + 1) * mu) / (Real.sqrt (L1 + 1) * sigma)) - 1)) * (z - a)
      ≤ csStage1Cost e1 e2 b1 mu sigma L1 z - csStage1Cost e1 e2 b1 mu sigma L1 a := by
  set Φa := cdf (gaussianReal 0 1) ((a - (L1 + 1) * mu) / (Real.sqrt (L1 + 1) * sigma)) with hΦa
  have hF : cdf (csDemand mu sigma (L1 + 1)) a = Φa := by
    rw [f4a8_cdf_S1 mu sigma hs]
  have hP : (csDemand mu sigma (L1 + 1)).real (Set.Ioi a) = 1 - Φa := by
    rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, ← cdf_eq_real, hF]
  have hz := f4a8_int_pos mu sigma (L1 + 1) z
  have ha := f4a8_int_pos mu sigma (L1 + 1) a
  have hind : Integrable (fun x : ℝ => (a - z) * (Set.Ioi a).indicator (fun _ => (1:ℝ)) x)
      (csDemand mu sigma (L1 + 1)) :=
    ((integrable_const (1:ℝ)).indicator measurableSet_Ioi).const_mul _
  have hle : ∫ x, max (x - a) 0 ∂(csDemand mu sigma (L1 + 1))
      + ∫ x, (a - z) * (Set.Ioi a).indicator (fun _ => (1:ℝ)) x ∂(csDemand mu sigma (L1 + 1))
      ≤ ∫ x, max (x - z) 0 ∂(csDemand mu sigma (L1 + 1)) := by
    rw [← integral_add ha hind]
    apply integral_mono (ha.add hind) hz
    intro x
    show max (x - a) 0 + (a - z) * (Set.Ioi a).indicator (fun _ => (1:ℝ)) x ≤ max (x - z) 0
    simp only [Set.indicator, Set.mem_Ioi]
    split_ifs with h
    · rw [max_eq_left (by linarith : (0:ℝ) ≤ x - a)]
      have := le_max_left (x - z) 0
      linarith
    · rw [max_eq_right (by linarith : x - a ≤ 0)]
      have := le_max_right (x - z) 0
      linarith
  have hint : ∫ x, (a - z) * (Set.Ioi a).indicator (fun _ => (1:ℝ)) x ∂(csDemand mu sigma (L1 + 1))
      = (a - z) * (1 - Φa) := by
    rw [integral_const_mul, integral_indicator_const _ measurableSet_Ioi, hP, smul_eq_mul, mul_one]
  rw [hint] at hle
  have hm := mul_le_mul_of_nonneg_left hle hK
  unfold csStage1Cost
  nlinarith

lemma f4a8_hasDerivAt_of_subgrad (g p : ℝ → ℝ) (y : ℝ)
    (hsub : ∀ a z, p a * (z - a) ≤ g z - g a) (hp : ContinuousAt p y) :
    HasDerivAt g (p y) y := by
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  have hev : ∀ᶠ z in nhds y, |p z - p y| < c := by
    have hball := hp (Metric.ball_mem_nhds (p y) hc)
    filter_upwards [hball] with z hz
    have hz' : dist (p z) (p y) < c := hz
    rwa [Real.dist_eq] at hz'
  filter_upwards [hev] with z hz
  have h1 := hsub y z
  have h2 := hsub z y
  rw [Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul]
  rw [abs_le]
  have h3 : (p z - p y) * (z - y) ≤ |p z - p y| * |z - y| := by
    rw [← abs_mul]; exact le_abs_self _
  have h4 : |p z - p y| * |z - y| ≤ c * |z - y| :=
    mul_le_mul_of_nonneg_right hz.le (abs_nonneg _)
  have h5 : 0 ≤ c * |z - y| := mul_nonneg hc.le (abs_nonneg _)
  constructor
  · nlinarith
  · nlinarith

open MeasureTheory ProbabilityTheory in
lemma f4a8_cdf_cont : Continuous (cdf (gaussianReal 0 1)) := by
  rw [continuous_iff_continuousAt]
  intro a
  have hmono : Monotone (cdf (gaussianReal 0 1)) := monotone_cdf _
  rw [hmono.continuousAt_iff_leftLim_eq_rightLim]
  have hr : Function.rightLim (cdf (gaussianReal 0 1)) a = cdf (gaussianReal 0 1) a :=
    ((cdf (gaussianReal 0 1)).right_continuous a).rightLim_eq
  have hl : Function.leftLim (cdf (gaussianReal 0 1)) a = cdf (gaussianReal 0 1) a := by
    have h1 := (cdf (gaussianReal 0 1)).measure_singleton a
    rw [measure_cdf] at h1
    have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
    have h0 : gaussianReal 0 1 {a} = 0 := measure_singleton a
    rw [h0] at h1
    have h2 := hmono.leftLim_le (le_refl a)
    have h3 := ENNReal.ofReal_eq_zero.1 h1.symm
    linarith
  rw [hl, hr]

open MeasureTheory ProbabilityTheory InventoryControl in
theorem solution (e1 e2 b1 mu sigma : ℝ) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) (hb : 0 < b1)
    (hs : 0 < sigma) (L1 : ℕ) (S1 : ℝ) :
    ConvexOn ℝ Set.univ (csStage1Cost e1 e2 b1 mu sigma L1)
      ∧ HasDerivAt (csStage1Cost e1 e2 b1 mu sigma L1)
          (e1 + (e1 + e2 + b1)
            * (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)
                ((S1 - (L1 + 1) * mu) / (Real.sqrt (L1 + 1) * sigma)) - 1)) S1
      ∧ ((∀ y : ℝ, csStage1Cost e1 e2 b1 mu sigma L1 S1 ≤ csStage1Cost e1 e2 b1 mu sigma L1 y)
          ↔ ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)
              ((S1 - (L1 + 1) * mu) / (Real.sqrt (L1 + 1) * sigma))
              = (e2 + b1) / (e1 + e2 + b1)) := by
  have hK : 0 < e1 + e2 + b1 := by linarith
  have hcont : Continuous (fun a : ℝ => e1 + (e1 + e2 + b1) * (cdf (gaussianReal 0 1)
      ((a - (L1 + 1) * mu) / (Real.sqrt (L1 + 1) * sigma)) - 1)) :=
    continuous_const.add (continuous_const.mul ((f4a8_cdf_cont.comp
      ((continuous_id.sub continuous_const).div_const _)).sub continuous_const))
  have hderiv : HasDerivAt (csStage1Cost e1 e2 b1 mu sigma L1)
      (e1 + (e1 + e2 + b1) * (cdf (gaussianReal 0 1)
        ((S1 - (L1 + 1) * mu) / (Real.sqrt (L1 + 1) * sigma)) - 1)) S1 :=
    f4a8_hasDerivAt_of_subgrad _ (fun a : ℝ => e1 + (e1 + e2 + b1) * (cdf (gaussianReal 0 1)
      ((a - (L1 + 1) * mu) / (Real.sqrt (L1 + 1) * sigma)) - 1)) S1
      (fun a z => f4a8_subgrad e1 e2 b1 mu sigma hs L1 hK.le a z) hcont.continuousAt
  refine ⟨f4a8_stage1_convex e1 e2 b1 mu sigma L1 hK.le, hderiv,
    ⟨fun hmin => ?_, fun h => f4a8_S1_min e1 e2 b1 mu sigma he1 he2 hb hs L1 S1 h⟩⟩
  have h0 := IsLocalMin.hasDerivAt_eq_zero (Filter.Eventually.of_forall hmin) hderiv
  rw [eq_div_iff hK.ne']
  linarith
