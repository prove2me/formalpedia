-- Prove2me | solution 1 for KallMayerSLP.CondExp.proposition_4_4
-- status  : ACCEPTED   (prove)
-- author  : @ytako6706
-- created : 2026-11-25T08:06:36.079928+00:00
-- url     : https://prove2.me/submissions/25ec1d22-c49a-4fb5-a904-f3a8ddedff4c

import Mathlib
import Definitions.Def_StochasticOrders_MeanResidualLife_mrl
import Definitions.Def_LogConcaveOn

open MeasureTheory
open StochasticOrders.MeanResidualLife

/-- The density shifted to `u` and truncated to `x > 0`: `x ↦ f(u+x) 1{x>0}`. -/
noncomputable def mrlA (f : ℝ → ℝ) (u x : ℝ) : ℝ := if 0 < x then f (u + x) else 0

/-- Part 1: log-concavity gives `f p f q ≤ f c f d` when `c + d = p + q` with `c, d ∈ [p, q]`. -/
lemma mrl_lc_pair {f : ℝ → ℝ} (hlog : ConvexOptimization.LogConcaveOn Set.univ f)
    {p q c d : ℝ} (hpc : p ≤ c) (hcq : c ≤ q) (hpd : p ≤ d) (hdq : d ≤ q) (hsum : c + d = p + q) :
    f p * f q ≤ f c * f d := by
  have h0 : ∀ x, 0 ≤ f x := fun x => hlog.1 x trivial
  rcases (h0 p).lt_or_eq with hp | hp
  swap
  · rw [← hp, zero_mul]; exact mul_nonneg (h0 c) (h0 d)
  rcases (h0 q).lt_or_eq with hq | hq
  swap
  · rw [← hq, mul_zero]; exact mul_nonneg (h0 c) (h0 d)
  rcases (hpc.trans hcq).lt_or_eq with hpq | hpq
  swap
  · have hc : c = p := by linarith
    have hd : d = p := by linarith
    rw [hc, hd, ← hpq]
  set l := (q - c) / (q - p) with hl
  have hqp : 0 < q - p := by linarith
  have hl0 : 0 ≤ l := div_nonneg (by linarith) hqp.le
  have hl1 : l ≤ 1 := by rw [hl, div_le_one hqp]; linarith
  have hc : l • p + (1 - l) • q = c := by
    simp only [smul_eq_mul, hl]; field_simp; ring
  have hd : (1 - l) • p + l • q = d := by
    rw [show d = p + q - c by linarith]
    simp only [smul_eq_mul, hl]; field_simp; ring
  have h1 := hlog.2 p trivial q trivial l (1 - l) hl0 (by linarith) (by ring)
  have h2 := hlog.2 p trivial q trivial (1 - l) l (by linarith) hl0 (by ring)
  rw [hc] at h1
  rw [hd] at h2
  calc f p * f q = (f p ^ l * f q ^ (1 - l)) * (f p ^ (1 - l) * f q ^ l) := by
        have e1 : f p = f p ^ l * f p ^ (1 - l) := by
          rw [← Real.rpow_add hp]; simp
        have e2 : f q = f q ^ (1 - l) * f q ^ l := by
          rw [← Real.rpow_add hq]; simp
        conv_lhs => rw [e1, e2]
        ring
    _ ≤ f c * f d := mul_le_mul h1 h2 (by positivity) (h0 c)

/-- Part 2: the TP2 inequality for the shifted truncated densities. -/
lemma mrl_tp2 {f : ℝ → ℝ} (hlog : ConvexOptimization.LogConcaveOn Set.univ f) {s t : ℝ}
    (hst : s ≤ t) {x y : ℝ} (hyx : y ≤ x) :
    mrlA f t x * mrlA f s y ≤ mrlA f s x * mrlA f t y := by
  have h0 : ∀ x, 0 ≤ f x := fun x => hlog.1 x trivial
  unfold mrlA
  by_cases hy : 0 < y
  · have hx : 0 < x := lt_of_lt_of_le hy hyx
    simp only [if_pos hx, if_pos hy]
    have := mrl_lc_pair hlog (p := s + y) (q := t + x) (c := s + x) (d := t + y)
      (by linarith) (by linarith) (by linarith) (by linarith) (by ring)
    nlinarith [this]
  · simp only [if_neg hy, mul_zero]
    simp

/-- Part 3: a log-concave function on `ℝ` is measurable (its superlevel sets are intervals). -/
lemma mrl_measurable {f : ℝ → ℝ} (hlog : ConvexOptimization.LogConcaveOn Set.univ f) :
    Measurable f := by
  have h0 : ∀ x, 0 ≤ f x := fun x => hlog.1 x trivial
  refine measurable_of_Ici fun c => ?_
  apply Set.OrdConnected.measurableSet
  refine ⟨fun x hx y hy z hz => ?_⟩
  simp only [Set.mem_preimage, Set.mem_Ici] at hx hy ⊢
  rcases le_or_gt c 0 with hc | hc
  · exact hc.trans (h0 z)
  rcases hz.1.lt_or_eq with hxz | hxz
  swap
  · rw [← hxz]; exact hx
  have hxy : x < y := lt_of_lt_of_le hxz hz.2
  set a := (y - z) / (y - x)
  have hyx' : 0 < y - x := by linarith
  have ha0 : 0 ≤ a := div_nonneg (by linarith [hz.2]) hyx'.le
  have ha1 : a ≤ 1 := by rw [div_le_one hyx']; linarith
  have hz' : a • x + (1 - a) • y = z := by
    simp only [smul_eq_mul, a]; field_simp; ring
  have h := hlog.2 x trivial y trivial a (1 - a) ha0 (by linarith) (by ring)
  rw [hz'] at h
  calc c = c ^ a * c ^ (1 - a) := by rw [← Real.rpow_add hc]; simp
    _ ≤ f x ^ a * f y ^ (1 - a) := by
        apply mul_le_mul (Real.rpow_le_rpow hc.le hx ha0)
          (Real.rpow_le_rpow hc.le hy (by linarith)) (Real.rpow_nonneg hc.le _)
          (Real.rpow_nonneg (h0 x) _)
    _ ≤ f z := h

/-- Part 4: translating a half-line integral to `(0, ∞)`. -/
lemma mrl_shift (g : ℝ → ℝ) (u : ℝ) :
    ∫ y, (Set.Ioi u).indicator g y = ∫ x, (Set.Ioi (0 : ℝ)).indicator (fun x => g (u + x)) x := by
  have h := integral_add_left_eq_self (μ := (volume : Measure ℝ))
    (f := fun y => (Set.Ioi u).indicator g y) u
  rw [← h]
  congr 1
  funext x
  simp only [Set.indicator, Set.mem_Ioi]
  by_cases hx : 0 < x
  · simp [hx, show u < u + x by linarith]
  · simp [hx, show ¬ u < u + x by linarith]

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Ω → ℝ) (hξ : Measurable ξ) (f : ℝ → ℝ)
    (hdens : μ.map ξ = volume.withDensity (fun y => ENNReal.ofReal (f y)))
    (hlog : ConvexOptimization.LogConcaveOn Set.univ f) (hint : Integrable ξ μ) :
    AntitoneOn (mrl μ ξ) {t | 0 < μ {ω | t < ξ ω}} := by
  have h0 : ∀ x, 0 ≤ f x := fun x => hlog.1 x trivial
  have hfm : Measurable f := mrl_measurable hlog
  set F : ℝ → ENNReal := fun y => ENNReal.ofReal (f y) with hF
  have hFm : Measurable F := hfm.ennreal_ofReal
  have hFlt : ∀ᵐ y ∂(volume : Measure ℝ), F y < ⊤ := ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)
  have hFr : ∀ y, (F y).toReal = f y := fun y => ENNReal.toReal_ofReal (h0 y)
  have hprob : IsProbabilityMeasure (volume.withDensity F) := by
    rw [← hdens]; exact Measure.isProbabilityMeasure_map hξ.aemeasurable
  -- Part 5: integrability of the density and of `y f(y)`.
  have hf_int : Integrable f := by
    have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.withDensity F) := integrable_const 1
    rw [integrable_withDensity_iff_integrable_smul' hFm hFlt] at h1
    simpa [hFr] using h1
  have hyf_int : Integrable (fun y => f y * y) := by
    have h1 : Integrable id (μ.map ξ) :=
      (integrable_map_measure aestronglyMeasurable_id hξ.aemeasurable).mpr hint
    rw [hdens, integrable_withDensity_iff_integrable_smul' hFm hFlt] at h1
    simpa [hFr] using h1
  have hA_int : ∀ u, Integrable (mrlA f u) := by
    intro u
    have : mrlA f u = (Set.Ioi (0 : ℝ)).indicator (fun x => f (u + x)) := by
      funext x; simp [mrlA, Set.indicator, Set.mem_Ioi]
    rw [this]
    exact (hf_int.comp_add_left u).indicator measurableSet_Ioi
  have hxA_int : ∀ u, Integrable (fun x => x * mrlA f u x) := by
    intro u
    have : (fun x => x * mrlA f u x) = (Set.Ioi (0 : ℝ)).indicator
        (fun x => f (u + x) * (u + x) - u * f (u + x)) := by
      funext x; simp only [mrlA, Set.indicator, Set.mem_Ioi]; split_ifs <;> ring
    rw [this]
    exact ((hyf_int.comp_add_left u).sub ((hf_int.comp_add_left u).const_mul u)).indicator
      measurableSet_Ioi
  -- Part 6: the mean residual life as a ratio of Lebesgue integrals.
  have hD : ∀ u, (μ {ω | u < ξ ω}).toReal = ∫ x, mrlA f u x := by
    intro u
    have e1 : μ {ω | u < ξ ω} = (μ.map ξ) (Set.Ioi u) := by
      rw [Measure.map_apply hξ measurableSet_Ioi]; rfl
    rw [e1, ← measureReal_def, ← integral_indicator_one measurableSet_Ioi, hdens,
      integral_withDensity_eq_integral_toReal_smul hFm hFlt]
    have : (fun y => (F y).toReal • (Set.Ioi u).indicator (1 : ℝ → ℝ) y) =
        (Set.Ioi u).indicator f := by
      funext y; simp [Set.indicator, hFr]
    rw [this, mrl_shift]
    congr 1
  have hN : ∀ u, ∫ ω in {ω | u < ξ ω}, (ξ ω - u) ∂μ = ∫ x, x * mrlA f u x := by
    intro u
    have e1 : ∫ ω in {ω | u < ξ ω}, (ξ ω - u) ∂μ = ∫ y in Set.Ioi u, (y - u) ∂(μ.map ξ) := by
      rw [setIntegral_map (f := fun y => y - u) measurableSet_Ioi
        (measurable_id.sub_const u).aestronglyMeasurable hξ.aemeasurable]; rfl
    rw [e1, ← integral_indicator measurableSet_Ioi, hdens,
      integral_withDensity_eq_integral_toReal_smul hFm hFlt]
    have : (fun y => (F y).toReal • (Set.Ioi u).indicator (fun y => y - u) y) =
        (Set.Ioi u).indicator (fun y => f y * (y - u)) := by
      funext y; simp [Set.indicator, hFr]
    rw [this, mrl_shift]
    congr 1; funext x; simp only [mrlA, Set.indicator, Set.mem_Ioi]; split_ifs <;> ring
  -- Part 7: symmetrisation of the double integral.
  intro s hs t ht hst
  simp only [Set.mem_setOf_eq] at hs ht
  have hpos : ∀ u, 0 < μ {ω | u < ξ ω} → 0 < (μ {ω | u < ξ ω}).toReal :=
    fun u h => ENNReal.toReal_pos h.ne' (measure_ne_top _ _)
  have hDs := hpos s hs
  have hDt := hpos t ht
  unfold mrl
  rw [if_pos hDt, if_pos hDs, hN, hN, hD, hD]
  rw [hD] at hDs hDt
  rw [div_le_div_iff₀ hDt hDs]
  set a := mrlA f s with ha
  set b := mrlA f t with hb
  have hI1 : Integrable (fun z : ℝ × ℝ => (z.1 * a z.1) * b z.2) (volume.prod volume) :=
    (hxA_int s).mul_prod (hA_int t)
  have hI2 : Integrable (fun z : ℝ × ℝ => (z.1 * b z.1) * a z.2) (volume.prod volume) :=
    (hxA_int t).mul_prod (hA_int s)
  have hΦ : ∫ z : ℝ × ℝ, ((z.1 * a z.1) * b z.2 - (z.1 * b z.1) * a z.2) ∂(volume.prod volume) =
      (∫ x, x * a x) * (∫ x, b x) - (∫ x, x * b x) * (∫ x, a x) := by
    rw [integral_sub hI1 hI2, integral_prod_mul (fun x => x * a x) b,
      integral_prod_mul (fun x => x * b x) a]
  have hswapI : Integrable (fun z : ℝ × ℝ =>
      (z.2 * a z.2) * b z.1 - (z.2 * b z.2) * a z.1) (volume.prod volume) :=
    (hI1.sub hI2).swap
  have hswap : ∫ z : ℝ × ℝ, ((z.2 * a z.2) * b z.1 - (z.2 * b z.2) * a z.1)
      ∂(volume.prod volume) =
      ∫ z : ℝ × ℝ, ((z.1 * a z.1) * b z.2 - (z.1 * b z.1) * a z.2) ∂(volume.prod volume) :=
    integral_prod_swap (fun z : ℝ × ℝ => (z.1 * a z.1) * b z.2 - (z.1 * b z.1) * a z.2)
  have hsum : 0 ≤ ∫ z : ℝ × ℝ, (((z.1 * a z.1) * b z.2 - (z.1 * b z.1) * a z.2) +
      ((z.2 * a z.2) * b z.1 - (z.2 * b z.2) * a z.1)) ∂(volume.prod volume) := by
    apply integral_nonneg
    intro z
    show (0 : ℝ) ≤ _
    rcases le_total z.2 z.1 with h | h
    · have := mrl_tp2 hlog hst h
      rw [← ha, ← hb] at this
      nlinarith [mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 this)]
    · have := mrl_tp2 hlog hst h
      rw [← ha, ← hb] at this
      nlinarith [mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 this)]
  have hsplit : ∫ z : ℝ × ℝ, (((z.1 * a z.1) * b z.2 - (z.1 * b z.1) * a z.2) +
      ((z.2 * a z.2) * b z.1 - (z.2 * b z.2) * a z.1)) ∂(volume.prod volume) =
      (∫ z : ℝ × ℝ, ((z.1 * a z.1) * b z.2 - (z.1 * b z.1) * a z.2) ∂(volume.prod volume)) +
      ∫ z : ℝ × ℝ, ((z.2 * a z.2) * b z.1 - (z.2 * b z.2) * a z.1) ∂(volume.prod volume) :=
    integral_add (hI1.sub hI2) hswapI
  rw [hsplit, hswap, hΦ] at hsum
  nlinarith [hsum]
