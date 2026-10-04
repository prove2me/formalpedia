-- Prove2me | solution 1 for HunterPDE.Compactness.kolmogorov_riesz
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T04:03:19.229351+00:00
-- url     : https://prove2.me/submissions/d749c35c-2632-4218-9934-138e61e1d504

import Mathlib

open MeasureTheory
open scoped ENNReal BoundedContinuousFunction

namespace KR


abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

set_option linter.unusedSectionVars false

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

lemma eLpNorm_sub_ne_top (f g : Lp ℝ p (volume : Measure (E n))) :
    eLpNorm (⇑f - ⇑g) p volume ≠ ∞ := by
  have := (Lp.memLp f).sub (Lp.memLp g)
  exact this.eLpNorm_ne_top

lemma lp_dist_lt_iff (f g : Lp ℝ p (volume : Measure (E n))) {ε : ℝ} :
    dist f g < ε ↔ eLpNorm (⇑f - ⇑g) p volume < ENNReal.ofReal ε := by
  rw [Lp.dist_def, ← ENNReal.lt_ofReal_iff_toReal_lt (eLpNorm_sub_ne_top f g)]

/-- The translation `x ↦ x + h` as a continuous map, jointly continuous in `h`. -/
def Tr (n : ℕ) : E n → C(E n, E n) :=
  fun h => (ContinuousMap.curry (⟨fun q : E n × E n => q.2 + q.1, by fun_prop⟩ : C(E n × E n, E n))) h

lemma Tr_apply (h x : E n) : Tr n h x = x + h := rfl

lemma Tr_continuous : Continuous (Tr n) :=
  (ContinuousMap.curry (⟨fun q : E n × E n => q.2 + q.1, by fun_prop⟩ : C(E n × E n, E n))).continuous

lemma Tr_mp (h : E n) : MeasurePreserving (Tr n h) volume volume := by
  have : (⇑(Tr n h) : E n → E n) = fun x => x + h := funext (Tr_apply h)
  rw [this]
  exact measurePreserving_add_right (volume : Measure (E n)) h

/-- Translation as an additive map on `L^p`. -/
noncomputable def trL (h : E n) : Lp ℝ p (volume : Measure (E n)) →+ Lp ℝ p (volume : Measure (E n)) :=
  Lp.compMeasurePreserving (Tr n h) (Tr_mp h)

lemma trL_ae (h : E n) (f : Lp ℝ p (volume : Measure (E n))) :
    ⇑(trL h f) =ᵐ[volume] fun x => (f : E n → ℝ) (x + h) :=
  (Lp.coeFn_compMeasurePreserving f (Tr_mp h)).trans
    (Filter.EventuallyEq.of_eq (funext fun x => by simp [Tr_apply]))

lemma norm_trL (h : E n) (f : Lp ℝ p (volume : Measure (E n))) : ‖trL h f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving f (Tr_mp h)

lemma trL_zero (f : Lp ℝ p (volume : Measure (E n))) : trL (0 : E n) f = f :=
  Lp.ext ((trL_ae 0 f).trans (Filter.EventuallyEq.of_eq (funext fun x => by simp)))

lemma trL_continuous (hp : p ≠ ∞) (g : Lp ℝ p (volume : Measure (E n))) :
    Continuous (fun h : E n => trL h g) :=
  Continuous.compMeasurePreservingLp (f := fun _ : E n => g) continuous_const Tr_continuous Tr_mp hp

/-- The `eLpNorm` of the translation difference, as a norm in `L^p`. -/
lemma eLpNorm_translate (h : E n) (f : Lp ℝ p (volume : Measure (E n))) :
    eLpNorm (fun x => (f : E n → ℝ) (x + h) - (f : E n → ℝ) x) p volume =
      ENNReal.ofReal ‖trL h f - f‖ := by
  have h1 : eLpNorm (fun x => (f : E n → ℝ) (x + h) - (f : E n → ℝ) x) p volume =
      eLpNorm (⇑(trL h f - f)) p volume := by
    have h2 : ⇑(trL h f - f) =ᵐ[volume] fun x => (f : E n → ℝ) (x + h) - (f : E n → ℝ) x :=
      (Lp.coeFn_sub _ _).trans ((trL_ae h f).sub (Filter.EventuallyEq.refl _ _))
    exact eLpNorm_congr_ae h2.symm
  rw [h1, Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]

lemma translate_small (hp : p ≠ ∞) (g : Lp ℝ p (volume : Measure (E n))) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : E n, ‖h‖ < δ → ‖trL h g - g‖ < ε := by
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuous_iff.mp (trL_continuous hp g) 0 ε hε
  refine ⟨δ, hδ, fun h hh => ?_⟩
  have := hδ' h (by simpa [dist_eq_norm] using hh)
  rwa [trL_zero, dist_eq_norm] at this


/-- Tails of a single `L^p` function are small. -/
lemma tail_small (hp : p ≠ ∞) (g : Lp ℝ p (volume : Measure (E n))) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, eLpNorm (g : E n → ℝ) p (volume.restrict {x | R < ‖x‖}) < ENNReal.ofReal ε := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  set q := p.toReal with hqdef
  have hq : 0 < q := ENNReal.toReal_pos hp0 hp
  have hfin : ∫⁻ x, ‖(g : E n → ℝ) x‖ₑ ^ q ∂volume < ∞ :=
    lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hp (Lp.memLp g).eLpNorm_lt_top
  have hmeas : Measurable (fun x => ‖(g : E n → ℝ) x‖ₑ ^ q) :=
    ((Lp.stronglyMeasurable g).measurable.enorm).pow_const q
  let Fk : ℕ → E n → ℝ≥0∞ := fun k => Set.indicator {x : E n | (k : ℝ) < ‖x‖}
    (fun x => ‖(g : E n → ℝ) x‖ₑ ^ q)
  have hlim : Filter.Tendsto (fun k => ∫⁻ x, Fk k x ∂volume) Filter.atTop (nhds 0) := by
    have := tendsto_lintegral_of_dominated_convergence (μ := (volume : Measure (E n)))
      (F := Fk) (f := fun _ => 0) (bound := fun x => ‖(g : E n → ℝ) x‖ₑ ^ q)
      (fun k => hmeas.indicator (measurableSet_lt measurable_const measurable_norm))
      (fun k => Filter.Eventually.of_forall fun x => Set.indicator_le_self _ _ x)
      hfin.ne
      (Filter.Eventually.of_forall fun x => by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Filter.eventually_ge_atTop ⌈‖x‖⌉₊] with k hk
        have : ¬ ((k : ℝ) < ‖x‖) := by
          have := Nat.le_ceil ‖x‖
          have h2 : ‖x‖ ≤ (k : ℝ) := this.trans (by exact_mod_cast hk)
          exact not_lt.mpr h2
        simp [Fk, this])
    simpa using this
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal ε ^ q := ENNReal.rpow_pos (by simpa using hε) ENNReal.ofReal_ne_top
  obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds hpos)).exists
  refine ⟨k, ?_⟩
  have hS : MeasurableSet {x : E n | (k : ℝ) < ‖x‖} := measurableSet_lt measurable_const measurable_norm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp]
  have h1 : ∫⁻ x in {x : E n | (k : ℝ) < ‖x‖}, ‖(g : E n → ℝ) x‖ₑ ^ q ∂volume < ENNReal.ofReal ε ^ q := by
    rw [← lintegral_indicator hS]; exact hk
  calc (∫⁻ x in {x : E n | (k : ℝ) < ‖x‖}, ‖(g : E n → ℝ) x‖ₑ ^ q ∂volume) ^ (1 / q)
      < (ENNReal.ofReal ε ^ q) ^ (1 / q) :=
        ENNReal.rpow_lt_rpow h1 (by positivity)
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.rpow_mul, mul_one_div_cancel hq.ne', ENNReal.rpow_one]

/-- The forward direction of Kolmogorov–Riesz: a set with compact closure is bounded, tight and
equicontinuous under translations. -/
theorem forward (hp : p ≠ ∞) (F : Set (Lp ℝ p (volume : Measure (E n))))
    (hF : IsCompact (closure F)) :
    (∃ M : ℝ, ∀ f ∈ F, ‖f‖ ≤ M) ∧
    (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ f ∈ F,
      eLpNorm (f : E n → ℝ) p (volume.restrict {x : E n | R < ‖x‖}) < ENNReal.ofReal ε) ∧
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : E n, ‖h‖ < δ → ∀ f ∈ F,
      eLpNorm (fun x => (f : E n → ℝ) (x + h) - (f : E n → ℝ) x) p volume <
        ENNReal.ofReal ε) := by
  have htb : TotallyBounded F := hF.totallyBounded.subset subset_closure
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp (hF.isBounded.subset subset_closure)
    exact ⟨C, hC⟩
  · intro ε hε
    obtain ⟨t, htfin, hcov⟩ := Metric.totallyBounded_iff.mp htb (ε / 2) (half_pos hε)
    have hev : ∀ g ∈ t, ∀ᶠ R in Filter.atTop,
        eLpNorm (g : E n → ℝ) p (volume.restrict {x : E n | R < ‖x‖}) < ENNReal.ofReal (ε / 2) := by
      intro g _
      obtain ⟨R0, hR0⟩ := tail_small hp g (half_pos hε)
      refine Filter.eventually_atTop.2 ⟨R0, fun R hR => lt_of_le_of_lt ?_ hR0⟩
      exact eLpNorm_mono_measure _ (Measure.restrict_mono (fun x hx => lt_of_le_of_lt hR hx) le_rfl)
    obtain ⟨R, hR⟩ := ((Filter.eventually_all_finite htfin).2 hev).exists
    refine ⟨R, fun f hf => ?_⟩
    obtain ⟨g, hgt, hfg⟩ := Set.mem_iUnion₂.mp (hcov hf)
    have h1 : eLpNorm (⇑f - ⇑g) p (volume.restrict {x : E n | R < ‖x‖}) < ENNReal.ofReal (ε / 2) :=
      lt_of_le_of_lt (eLpNorm_mono_measure _ Measure.restrict_le_self)
        ((lp_dist_lt_iff f g).mp (by simpa [Metric.mem_ball] using hfg))
    have hsum : eLpNorm (f : E n → ℝ) p (volume.restrict {x : E n | R < ‖x‖}) ≤
        eLpNorm (⇑f - ⇑g) p (volume.restrict {x : E n | R < ‖x‖}) +
          eLpNorm (g : E n → ℝ) p (volume.restrict {x : E n | R < ‖x‖}) := by
      have := eLpNorm_add_le ((Lp.stronglyMeasurable f).aestronglyMeasurable.sub
        (Lp.stronglyMeasurable g).aestronglyMeasurable)
        (Lp.stronglyMeasurable g).aestronglyMeasurable (Fact.out : 1 ≤ p)
          (μ := volume.restrict {x : E n | R < ‖x‖})
      simpa using this
    calc eLpNorm (f : E n → ℝ) p (volume.restrict {x : E n | R < ‖x‖})
        ≤ _ := hsum
      _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
          ENNReal.add_lt_add h1 (hR g hgt)
      _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le]; congr 1; ring
  · intro ε hε
    have hε3 : 0 < ε / 3 := by positivity
    obtain ⟨t, htfin, hcov⟩ := Metric.totallyBounded_iff.mp htb (ε / 3) hε3
    have hev : ∀ g ∈ t, ∀ᶠ h in nhds (0 : E n), ‖trL h g - g‖ < ε / 3 := by
      intro g _
      have := (trL_continuous hp g).tendsto 0
      rw [trL_zero] at this
      filter_upwards [(Metric.tendsto_nhds.mp this) (ε / 3) hε3] with h hh
      simpa [dist_eq_norm] using hh
    obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp ((Filter.eventually_all_finite htfin).2 hev)
    refine ⟨δ, hδ, fun h hh f hf => ?_⟩
    obtain ⟨g, hgt, hfg⟩ := Set.mem_iUnion₂.mp (hcov hf)
    have hfg' : ‖f - g‖ < ε / 3 := by
      have := Metric.mem_ball.mp hfg
      rwa [dist_eq_norm] at this
    have hg := hδ' (y := h) (by simpa [dist_eq_norm] using hh) g hgt
    rw [eLpNorm_translate, ENNReal.ofReal_lt_ofReal_iff hε]
    have e : trL h f - f = (trL h (f - g) - (f - g)) + (trL h g - g) := by
      rw [map_sub]; abel
    calc ‖trL h f - f‖ ≤ ‖trL h (f - g) - (f - g)‖ + ‖trL h g - g‖ := by rw [e]; exact norm_add_le _ _
      _ ≤ (‖trL h (f - g)‖ + ‖f - g‖) + ‖trL h g - g‖ := by gcongr; exact norm_sub_le _ _
      _ < ε := by rw [norm_trL]; linarith





/-- Hölder bound for the normalised integral of a function over a finite measure. -/
lemma avg_enorm_le {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν]
    (hV0 : ν Set.univ ≠ 0) (hp : p ≠ ∞) (w : α → ℝ) (hw : AEStronglyMeasurable w ν) :
    ‖(ν Set.univ).toReal⁻¹ * ∫ a, w a ∂ν‖ₑ ≤ (ν Set.univ) ^ (-(1 / p.toReal)) * eLpNorm w p ν := by
  have hV : ν Set.univ ≠ ∞ := measure_ne_top _ _
  have hVpos : 0 < (ν Set.univ).toReal := ENNReal.toReal_pos hV0 hV
  have h1 : ‖∫ a, w a ∂ν‖ₑ ≤ eLpNorm w p ν * (ν Set.univ) ^ (1 - 1 / p.toReal) := by
    calc ‖∫ a, w a ∂ν‖ₑ ≤ ∫⁻ a, ‖w a‖ₑ ∂ν := enorm_integral_le_lintegral_enorm _
      _ = eLpNorm w 1 ν := (eLpNorm_one_eq_lintegral_enorm).symm
      _ ≤ eLpNorm w p ν * (ν Set.univ) ^ (1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal) :=
          eLpNorm_le_eLpNorm_mul_rpow_measure_univ Fact.out hw
      _ = _ := by simp
  have h2 : ‖(ν Set.univ).toReal⁻¹‖ₑ = (ν Set.univ)⁻¹ := by
    rw [Real.enorm_eq_ofReal (inv_nonneg.mpr hVpos.le), ENNReal.ofReal_inv_of_pos hVpos,
      ENNReal.ofReal_toReal hV]
  rw [enorm_mul, h2]
  calc (ν Set.univ)⁻¹ * ‖∫ a, w a ∂ν‖ₑ
      ≤ (ν Set.univ)⁻¹ * (eLpNorm w p ν * (ν Set.univ) ^ (1 - 1 / p.toReal)) := by gcongr
    _ = (ν Set.univ) ^ (-(1 / p.toReal)) * eLpNorm w p ν := by
      rw [← ENNReal.rpow_neg_one, mul_comm (eLpNorm w p ν), ← mul_assoc,
        ← ENNReal.rpow_add _ _ hV0 hV]
      congr 2; ring

/-- Local integrability of translates of an `L^p` function. -/
lemma integrableOn_translate (f : Lp ℝ p (volume : Measure (E n))) (x : E n) {B : Set (E n)}
    (hB : IsCompact B) : IntegrableOn (fun h => (f : E n → ℝ) (x + h)) B volume := by
  have hloc : LocallyIntegrable (f : E n → ℝ) volume :=
    (Lp.memLp f).locallyIntegrable Fact.out
  have h1 : IntegrableOn (f : E n → ℝ) ((fun h => x + h) '' B) volume :=
    hloc.integrableOn_isCompact (hB.image (continuous_const_add x))
  have h2 := ((measurePreserving_add_left (volume : Measure (E n)) x).integrableOn_comp_preimage
    (measurableEmbedding_addLeft x)).mpr h1
  rwa [Set.preimage_image_eq _ (add_right_injective x)] at h2

lemma eLpNorm_rpow_eq (hp : p ≠ ∞) {α : Type*} [MeasurableSpace α] (ν : Measure α) (u : α → ℝ) :
    (eLpNorm u p ν) ^ p.toReal = ∫⁻ a, ‖u a‖ₑ ^ p.toReal ∂ν := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp, ← ENNReal.rpow_mul,
    one_div_mul_cancel hq.ne', ENNReal.rpow_one]

lemma eLpNorm_translate_left (f : E n → ℝ) (hf : AEStronglyMeasurable f volume) (x : E n) :
    eLpNorm (fun h => f (x + h)) p volume = eLpNorm f p volume :=
  eLpNorm_comp_measurePreserving (g := f) (f := fun h => x + h) hf
    (measurePreserving_add_left (volume : Measure (E n)) x)

lemma ball_ne_zero {ρ : ℝ} (hρ : 0 < ρ) : volume (Metric.closedBall (0 : E n) ρ) ≠ 0 :=
  (Metric.measure_closedBall_pos volume (0 : E n) hρ).ne'

lemma ball_ne_top (ρ : ℝ) : volume (Metric.closedBall (0 : E n) ρ) ≠ ∞ :=
  measure_closedBall_lt_top.ne

/-- The average of `f` over the ball `x + closedBall 0 ρ`. -/
noncomputable def Av (n : ℕ) (ρ : ℝ) (f : E n → ℝ) (x : E n) : ℝ :=
  ((volume (Metric.closedBall (0 : E n) ρ)).toReal)⁻¹ *
    ∫ h in Metric.closedBall (0 : E n) ρ, f (x + h)

instance ballFinite (ρ : ℝ) : IsFiniteMeasure ((volume : Measure (E n)).restrict
    (Metric.closedBall (0 : E n) ρ)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact measure_closedBall_lt_top⟩

/-- Sup bound on the averages. -/
lemma Av_enorm_le (hp : p ≠ ∞) {ρ : ℝ} (hρ : 0 < ρ) (f : Lp ℝ p (volume : Measure (E n))) (x : E n) :
    ‖Av n ρ (f : E n → ℝ) x‖ₑ ≤
      (volume (Metric.closedBall (0 : E n) ρ)) ^ (-(1 / p.toReal)) * ENNReal.ofReal ‖f‖ := by
  set B := Metric.closedBall (0 : E n) ρ
  have hmeas : AEStronglyMeasurable (fun h => (f : E n → ℝ) (x + h))
      ((volume : Measure (E n)).restrict B) :=
    ((Lp.stronglyMeasurable f).measurable.comp (measurable_const_add x)).aestronglyMeasurable
  have h1 := avg_enorm_le ((volume : Measure (E n)).restrict B)
    (by rw [Measure.restrict_apply_univ]; exact ball_ne_zero hρ) hp _ hmeas
  rw [Measure.restrict_apply_univ] at h1
  have h2 : eLpNorm (fun h => (f : E n → ℝ) (x + h)) p ((volume : Measure (E n)).restrict B) ≤
      ENNReal.ofReal ‖f‖ := by
    calc _ ≤ eLpNorm (fun h => (f : E n → ℝ) (x + h)) p volume :=
          eLpNorm_mono_measure _ Measure.restrict_le_self
      _ = eLpNorm (f : E n → ℝ) p volume :=
          eLpNorm_translate_left _ (Lp.stronglyMeasurable f).aestronglyMeasurable x
      _ = ENNReal.ofReal ‖f‖ := by
          rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f)]
  unfold Av
  calc _ ≤ _ := h1
    _ ≤ _ := by gcongr





/-- The averages are equicontinuous, quantitatively. -/
lemma Av_sub_enorm_le (hp : p ≠ ∞) {ρ : ℝ} (hρ : 0 < ρ) (f : Lp ℝ p (volume : Measure (E n)))
    (x x' : E n) :
    ‖Av n ρ (f : E n → ℝ) x - Av n ρ (f : E n → ℝ) x'‖ₑ ≤
      (volume (Metric.closedBall (0 : E n) ρ)) ^ (-(1 / p.toReal)) *
        ENNReal.ofReal ‖trL (x - x') f - f‖ := by
  set B := Metric.closedBall (0 : E n) ρ
  have hBc : IsCompact B := isCompact_closedBall _ _
  have hdiff : Av n ρ (f : E n → ℝ) x - Av n ρ (f : E n → ℝ) x' =
      ((volume B).toReal)⁻¹ * ∫ h in B, ((f : E n → ℝ) (x + h) - (f : E n → ℝ) (x' + h)) := by
    unfold Av
    rw [integral_sub (integrableOn_translate f x hBc) (integrableOn_translate f x' hBc), mul_sub]
  rw [hdiff]
  set g : E n → ℝ := fun y => (f : E n → ℝ) (y + (x - x')) - (f : E n → ℝ) y with hg
  have hgm : Measurable g := by
    have hf := (Lp.stronglyMeasurable f).measurable
    exact (hf.comp (measurable_id.add_const _)).sub hf
  have hw : (fun h => (f : E n → ℝ) (x + h) - (f : E n → ℝ) (x' + h)) = fun h => g (x' + h) := by
    funext h
    simp only [hg]
    congr 2
    abel
  have h1 := avg_enorm_le ((volume : Measure (E n)).restrict B)
    (by rw [Measure.restrict_apply_univ]; exact ball_ne_zero hρ) hp
    (fun h => (f : E n → ℝ) (x + h) - (f : E n → ℝ) (x' + h))
    (by rw [hw]; exact (hgm.comp (measurable_const_add x')).aestronglyMeasurable)
  rw [Measure.restrict_apply_univ] at h1
  refine h1.trans ?_
  gcongr
  calc eLpNorm (fun h => (f : E n → ℝ) (x + h) - (f : E n → ℝ) (x' + h)) p
        ((volume : Measure (E n)).restrict B)
      ≤ eLpNorm (fun h => (f : E n → ℝ) (x + h) - (f : E n → ℝ) (x' + h)) p volume :=
        eLpNorm_mono_measure _ Measure.restrict_le_self
    _ = eLpNorm g p volume := by
        rw [hw]; exact eLpNorm_translate_left g hgm.aestronglyMeasurable x'
    _ = ENNReal.ofReal ‖trL (x - x') f - f‖ := eLpNorm_translate (x - x') f

/-- The averaging operator approximates `f` in `L^p`, given the translation modulus of `f`. -/
lemma approx_error (hp : p ≠ ∞) {ρ : ℝ} (hρ : 0 < ρ) (f : Lp ℝ p (volume : Measure (E n)))
    {ε : ℝ} (hmod : ∀ h : E n, ‖h‖ ≤ ρ → ‖trL h f - f‖ ≤ ε) :
    eLpNorm (fun x => (f : E n → ℝ) x - Av n ρ (f : E n → ℝ) x) p volume ≤ ENNReal.ofReal ε := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  set q := p.toReal with hqdef
  have hq : 0 < q := ENNReal.toReal_pos hp0 hp
  set B := Metric.closedBall (0 : E n) ρ with hB
  have hBc : IsCompact B := isCompact_closedBall _ _
  set V := volume B with hV
  have hV0 : V ≠ 0 := ball_ne_zero hρ
  have hVt : V ≠ ∞ := ball_ne_top ρ
  have hfm : Measurable (f : E n → ℝ) := (Lp.stronglyMeasurable f).measurable
  let G : E n → E n → ℝ≥0∞ := fun x h => ‖(f : E n → ℝ) x - (f : E n → ℝ) (x + h)‖ₑ ^ q
  have hpt : ∀ x, ‖(f : E n → ℝ) x - Av n ρ (f : E n → ℝ) x‖ₑ ^ q ≤ V⁻¹ * ∫⁻ h in B, G x h := by
    intro x
    have hVpos : 0 < V.toReal := ENNReal.toReal_pos hV0 hVt
    have heq : (f : E n → ℝ) x - Av n ρ (f : E n → ℝ) x =
        (V.toReal)⁻¹ * ∫ h in B, ((f : E n → ℝ) x - (f : E n → ℝ) (x + h)) := by
      unfold Av
      have hVpos' : 0 < (volume (Metric.closedBall (0 : E n) ρ)).toReal := hVpos
      rw [integral_sub (integrable_const ((f : E n → ℝ) x)) (integrableOn_translate f x hBc),
        setIntegral_const]
      simp only [smul_eq_mul, measureReal_def]
      simp only [hV, hB]
      field_simp
    have hmeas : AEStronglyMeasurable (fun h => (f : E n → ℝ) x - (f : E n → ℝ) (x + h))
        ((volume : Measure (E n)).restrict B) :=
      (measurable_const.sub (hfm.comp (measurable_const_add x))).aestronglyMeasurable
    have h1 := avg_enorm_le ((volume : Measure (E n)).restrict B)
      (by rw [Measure.restrict_apply_univ]; exact hV0) hp
      (fun h => (f : E n → ℝ) x - (f : E n → ℝ) (x + h)) hmeas
    rw [Measure.restrict_apply_univ, ← heq] at h1
    calc ‖(f : E n → ℝ) x - Av n ρ (f : E n → ℝ) x‖ₑ ^ q
        ≤ (V ^ (-(1 / q)) * eLpNorm (fun h => (f : E n → ℝ) x - (f : E n → ℝ) (x + h)) p
            ((volume : Measure (E n)).restrict B)) ^ q := ENNReal.rpow_le_rpow h1 hq.le
      _ = V⁻¹ * ∫⁻ h in B, G x h := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le, ← ENNReal.rpow_mul, eLpNorm_rpow_eq hp]
        have : -(1 / q) * q = -1 := by field_simp
        rw [this, ENNReal.rpow_neg_one]
  have hmeasG : Measurable (Function.uncurry G) := by
    have h1 : Measurable (fun z : E n × E n => (f : E n → ℝ) z.1) := hfm.comp measurable_fst
    have h2 : Measurable (fun z : E n × E n => (f : E n → ℝ) (z.1 + z.2)) :=
      hfm.comp (measurable_fst.add measurable_snd)
    exact (h1.sub h2).enorm.pow_const q
  have hinner : ∀ h ∈ B, ∫⁻ x, G x h ≤ ENNReal.ofReal ε ^ q := by
    intro h hh
    have hh' : ‖h‖ ≤ ρ := by simpa [hB] using hh
    have e1 : ∫⁻ x, G x h = ∫⁻ x, ‖(f : E n → ℝ) (x + h) - (f : E n → ℝ) x‖ₑ ^ q := by
      refine lintegral_congr fun x => ?_
      simp only [G]
      rw [enorm_sub_rev]
    rw [e1, ← eLpNorm_rpow_eq hp, eLpNorm_translate]
    exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (hmod h hh')) hq.le
  have hmain : ∫⁻ x, ‖(f : E n → ℝ) x - Av n ρ (f : E n → ℝ) x‖ₑ ^ q ≤ ENNReal.ofReal ε ^ q := by
    calc ∫⁻ x, ‖(f : E n → ℝ) x - Av n ρ (f : E n → ℝ) x‖ₑ ^ q
        ≤ ∫⁻ x, V⁻¹ * ∫⁻ h in B, G x h := lintegral_mono hpt
      _ = V⁻¹ * ∫⁻ x, ∫⁻ h in B, G x h :=
          lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hV0)
      _ = V⁻¹ * ∫⁻ h in B, ∫⁻ x, G x h := by
          rw [lintegral_lintegral_swap hmeasG.aemeasurable]
      _ ≤ V⁻¹ * ∫⁻ h in B, ENNReal.ofReal ε ^ q := by
          exact mul_le_mul' le_rfl (setLIntegral_mono' measurableSet_closedBall hinner)
      _ = ENNReal.ofReal ε ^ q := by
          rw [setLIntegral_const, mul_comm (ENNReal.ofReal ε ^ q) (volume B), ← mul_assoc,
            ENNReal.inv_mul_cancel hV0 hVt, one_mul]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp]
  calc (∫⁻ x, ‖(f : E n → ℝ) x - Av n ρ (f : E n → ℝ) x‖ₑ ^ q) ^ (1 / q)
      ≤ (ENNReal.ofReal ε ^ q) ^ (1 / q) := ENNReal.rpow_le_rpow hmain (by positivity)
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.rpow_mul, mul_one_div_cancel hq.ne', ENNReal.rpow_one]





/-- The real constant `V ^ (-1/q)` where `V` is the volume of the averaging ball. -/
noncomputable def C0 (n : ℕ) (p : ℝ≥0∞) (ρ : ℝ) : ℝ :=
  ((volume (Metric.closedBall (0 : E n) ρ)) ^ (-(1 / p.toReal))).toReal

lemma C0_nonneg (ρ : ℝ) : 0 ≤ C0 n p ρ := ENNReal.toReal_nonneg

lemma rpow_V_ne_top (hp : p ≠ ∞) {ρ : ℝ} (hρ : 0 < ρ) :
    (volume (Metric.closedBall (0 : E n) ρ)) ^ (-(1 / p.toReal)) ≠ ∞ := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  rw [ENNReal.rpow_neg]
  refine ENNReal.inv_ne_top.mpr ?_
  exact (ENNReal.rpow_pos (pos_iff_ne_zero.mpr (ball_ne_zero hρ)) (ball_ne_top ρ)).ne'

lemma Av_norm_le (hp : p ≠ ∞) {ρ : ℝ} (hρ : 0 < ρ) (f : Lp ℝ p (volume : Measure (E n))) (x : E n) :
    ‖Av n ρ (f : E n → ℝ) x‖ ≤ C0 n p ρ * ‖f‖ := by
  have h := Av_enorm_le hp hρ f x
  rw [← ofReal_norm] at h
  have hne : (volume (Metric.closedBall (0 : E n) ρ)) ^ (-(1 / p.toReal)) * ENNReal.ofReal ‖f‖ ≠ ∞ :=
    ENNReal.mul_ne_top (rpow_V_ne_top hp hρ) ENNReal.ofReal_ne_top
  have := (ENNReal.ofReal_le_iff_le_toReal hne).mp h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)] at this

lemma Av_sub_norm_le (hp : p ≠ ∞) {ρ : ℝ} (hρ : 0 < ρ) (f : Lp ℝ p (volume : Measure (E n)))
    (x x' : E n) :
    ‖Av n ρ (f : E n → ℝ) x - Av n ρ (f : E n → ℝ) x'‖ ≤ C0 n p ρ * ‖trL (x - x') f - f‖ := by
  have h := Av_sub_enorm_le hp hρ f x x'
  rw [← ofReal_norm] at h
  have hne : (volume (Metric.closedBall (0 : E n) ρ)) ^ (-(1 / p.toReal)) *
      ENNReal.ofReal ‖trL (x - x') f - f‖ ≠ ∞ :=
    ENNReal.mul_ne_top (rpow_V_ne_top hp hρ) ENNReal.ofReal_ne_top
  have := (ENNReal.ofReal_le_iff_le_toReal hne).mp h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)] at this

lemma continuous_Av (hp : p ≠ ∞) {ρ : ℝ} (hρ : 0 < ρ) (f : Lp ℝ p (volume : Measure (E n))) :
    Continuous (fun x : E n => Av n ρ (f : E n → ℝ) x) := by
  refine Metric.continuous_iff.mpr fun b ε hε => ?_
  have hC := C0_nonneg (n := n) (p := p) ρ
  obtain ⟨δ, hδ, hδ'⟩ := translate_small hp f (show 0 < ε / (C0 n p ρ + 1) by positivity)
  refine ⟨δ, hδ, fun a ha => ?_⟩
  have h1 := Av_sub_norm_le hp hρ f a b
  have h2 := hδ' (a - b) (by simpa [dist_eq_norm] using ha)
  rw [dist_eq_norm]
  calc ‖Av n ρ (f : E n → ℝ) a - Av n ρ (f : E n → ℝ) b‖
      ≤ C0 n p ρ * ‖trL (a - b) f - f‖ := h1
    _ ≤ C0 n p ρ * (ε / (C0 n p ρ + 1)) := by gcongr
    _ < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith

/-- A Tietze extension of a bounded continuous function on a closed set. -/
noncomputable def tiet {K : Set (E n)} (hK : IsClosed K) (u : K →ᵇ ℝ) : C(E n, ℝ) :=
  Classical.choose (ContinuousMap.exists_restrict_eq hK (u : C(K, ℝ)))

lemma tiet_apply {K : Set (E n)} (hK : IsClosed K) (u : K →ᵇ ℝ) (x : K) :
    tiet hK u x = u x := by
  have := Classical.choose_spec (ContinuousMap.exists_restrict_eq hK (u : C(K, ℝ)))
  exact congrFun (congrArg DFunLike.coe this) x

/-- The extension of `u` by `0` outside `K`. -/
noncomputable def extOf {K : Set (E n)} (hK : IsClosed K) (u : K →ᵇ ℝ) : E n → ℝ :=
  K.indicator (tiet hK u)

lemma extOf_memLp (hp : p ≠ ∞) {K : Set (E n)} (hK : IsCompact K) (u : K →ᵇ ℝ) :
    MemLp (extOf hK.isClosed u) p (volume : Measure (E n)) := by
  unfold extOf
  rw [memLp_indicator_iff_restrict hK.measurableSet]
  have : IsFiniteMeasure ((volume : Measure (E n)).restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  refine MemLp.of_bound (tiet hK.isClosed u).continuous.aestronglyMeasurable ‖u‖ ?_
  refine (ae_restrict_iff' hK.measurableSet).mpr (Filter.Eventually.of_forall fun x hx => ?_)
  have := tiet_apply hK.isClosed u ⟨x, hx⟩
  simp only at this
  rw [this]
  exact u.norm_coe_le_norm _

lemma extOf_measurable {K : Set (E n)} (hK : IsClosed K) (u : K →ᵇ ℝ) :
    Measurable (extOf hK u) :=
  (tiet hK u).continuous.measurable.indicator hK.measurableSet





/-- The backward direction of Kolmogorov–Riesz. -/
theorem backward (hp : p ≠ ∞) (F : Set (Lp ℝ p (volume : Measure (E n))))
    (hM : ∃ M : ℝ, ∀ f ∈ F, ‖f‖ ≤ M)
    (hT : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ f ∈ F,
      eLpNorm (f : E n → ℝ) p (volume.restrict {x : E n | R < ‖x‖}) < ENNReal.ofReal ε)
    (hE : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : E n, ‖h‖ < δ → ∀ f ∈ F,
      eLpNorm (fun x => (f : E n → ℝ) (x + h) - (f : E n → ℝ) x) p volume <
        ENNReal.ofReal ε) :
    IsCompact (closure F) := by
  have htb : TotallyBounded F := by
    rw [Metric.totallyBounded_iff]
    intro ε hε
    obtain ⟨M, hM⟩ := hM
    have hε5 : 0 < ε / 5 := by positivity
    obtain ⟨R, hR⟩ := hT (ε / 5) hε5
    obtain ⟨δ, hδ, hδ'⟩ := hE (ε / 5) hε5
    set ρ : ℝ := δ / 2 with hρdef
    have hρ : 0 < ρ := by positivity
    set K : Set (E n) := Metric.closedBall (0 : E n) R with hKdef
    have hKc : IsCompact K := isCompact_closedBall _ _
    have hKcompl : Kᶜ = {x : E n | R < ‖x‖} := by ext x; simp [hKdef, not_le]
    have hC := C0_nonneg (n := n) (p := p) ρ
    have hmod : ∀ h : E n, ‖h‖ ≤ ρ → ∀ f ∈ F, ‖trL h f - f‖ ≤ ε / 5 := by
      intro h hh f hf
      have h1 := hδ' h (by linarith) f hf
      rw [eLpNorm_translate, ENNReal.ofReal_lt_ofReal_iff hε5] at h1
      exact h1.le
    let ψ : Lp ℝ p (volume : Measure (E n)) → (K →ᵇ ℝ) := fun f =>
      BoundedContinuousFunction.mkOfCompact
        ⟨fun x : K => Av n ρ (f : E n → ℝ) x, (continuous_Av hp hρ f).comp continuous_subtype_val⟩
    have hψ : ∀ f (x : K), ψ f x = Av n ρ (f : E n → ℝ) x := fun f x => rfl
    have hcpt : IsCompact (closure (ψ '' F)) := by
      refine BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : ℝ) (C0 n p ρ * M))
        (isCompact_closedBall _ _) (ψ '' F) ?_ ?_
      · rintro u x ⟨f, hf, rfl⟩
        rw [mem_closedBall_zero_iff, hψ]
        calc ‖Av n ρ (f : E n → ℝ) x‖ ≤ C0 n p ρ * ‖f‖ := Av_norm_le hp hρ f x
          _ ≤ C0 n p ρ * M := mul_le_mul_of_nonneg_left (hM f hf) hC
      · refine (Metric.uniformEquicontinuous_iff.mpr ?_).equicontinuous
        intro ε' hε'
        obtain ⟨δ', hδ', hδ''⟩ := hE (ε' / (C0 n p ρ + 1)) (by positivity)
        refine ⟨δ', hδ', fun x y hxy i => ?_⟩
        obtain ⟨_, ⟨f, hf, rfl⟩⟩ := i
        have h1 := hδ'' ((x : E n) - (y : E n)) (by simpa [dist_eq_norm, Subtype.dist_eq] using hxy) f hf
        rw [eLpNorm_translate, ENNReal.ofReal_lt_ofReal_iff (by positivity)] at h1
        calc dist ((ψ f) x) ((ψ f) y) = ‖Av n ρ (f : E n → ℝ) x - Av n ρ (f : E n → ℝ) y‖ := by
              rw [hψ, hψ, dist_eq_norm]
          _ ≤ C0 n p ρ * ‖trL ((x : E n) - (y : E n)) f - f‖ := Av_sub_norm_le hp hρ f (x : E n) (y : E n)
          _ ≤ C0 n p ρ * (ε' / (C0 n p ρ + 1)) := mul_le_mul_of_nonneg_left h1.le hC
          _ < ε' := by
            rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
            nlinarith
    have htb' : TotallyBounded (ψ '' F) := hcpt.totallyBounded.subset subset_closure
    set cK : ℝ := ((volume K) ^ (p.toReal⁻¹)).toReal with hcK
    have hcK0 : 0 ≤ cK := ENNReal.toReal_nonneg
    set ε₃ : ℝ := (ε / 5) / (cK + 1) with hε₃
    have hε₃pos : 0 < ε₃ := by positivity
    obtain ⟨t, htfin, hcov⟩ := Metric.totallyBounded_iff.mp htb' ε₃ hε₃pos
    refine ⟨(fun u => (extOf_memLp hp hKc u).toLp (extOf hKc.isClosed u)) '' t,
      htfin.image _, ?_⟩
    intro f hf
    obtain ⟨u, hut, hu⟩ := Set.mem_iUnion₂.mp (hcov (Set.mem_image_of_mem ψ hf))
    refine Set.mem_iUnion₂.mpr ⟨_, Set.mem_image_of_mem _ hut, ?_⟩
    set g := (extOf_memLp hp hKc u).toLp (extOf hKc.isClosed u) with hg
    rw [Metric.mem_ball, lp_dist_lt_iff]
    have hae : ⇑g =ᵐ[volume] extOf hKc.isClosed u := MemLp.coeFn_toLp _
    rw [eLpNorm_congr_ae ((Filter.EventuallyEq.refl _ _).sub hae)]
    set G := tiet hKc.isClosed u with hGdef
    have hfm : Measurable (f : E n → ℝ) := (Lp.stronglyMeasurable f).measurable
    have hAvm : Measurable (fun x => Av n ρ (f : E n → ℝ) x) := (continuous_Av hp hρ f).measurable
    set T1 : E n → ℝ := Kᶜ.indicator (f : E n → ℝ) with hT1def
    set T2 : E n → ℝ := K.indicator (fun x => (f : E n → ℝ) x - Av n ρ (f : E n → ℝ) x) with hT2def
    set T3 : E n → ℝ := K.indicator (fun x => Av n ρ (f : E n → ℝ) x - G x) with hT3def
    have hdec : (⇑f - extOf hKc.isClosed u) = T1 + T2 + T3 := by
      funext x
      by_cases hx : x ∈ K
      · simp [extOf, hT1def, hT2def, hT3def, hx]
        try ring
      · simp [extOf, hT1def, hT2def, hT3def, hx]
    have hm1 : AEStronglyMeasurable T1 volume :=
      ((Lp.stronglyMeasurable f).aestronglyMeasurable).indicator hKc.measurableSet.compl
    have hm2 : AEStronglyMeasurable T2 volume :=
      ((hfm.sub hAvm).indicator hKc.measurableSet).aestronglyMeasurable
    have hm3 : AEStronglyMeasurable T3 volume :=
      ((hAvm.sub G.continuous.measurable).indicator hKc.measurableSet).aestronglyMeasurable
    have hb1 : eLpNorm T1 p volume ≤ ENNReal.ofReal (ε / 5) := by
      rw [hT1def, eLpNorm_indicator_eq_eLpNorm_restrict hKc.measurableSet.compl, hKcompl]
      exact (hR f hf).le
    have hb2 : eLpNorm T2 p volume ≤ ENNReal.ofReal (ε / 5) :=
      (eLpNorm_indicator_le _).trans (approx_error hp hρ f (fun h hh => hmod h hh f hf))
    have hb3 : eLpNorm T3 p volume ≤ ENNReal.ofReal (ε / 5) := by
      rw [hT3def, eLpNorm_indicator_eq_eLpNorm_restrict hKc.measurableSet]
      refine (eLpNorm_le_of_ae_bound (C := ε₃) ?_).trans ?_
      · refine (ae_restrict_iff' hKc.measurableSet).mpr (Filter.Eventually.of_forall fun x hx => ?_)
        have h1 : dist (ψ f ⟨x, hx⟩) (u ⟨x, hx⟩) < ε₃ :=
          lt_of_le_of_lt (BoundedContinuousFunction.dist_coe_le_dist _)
            (by simpa [Metric.mem_ball] using hu)
        rw [hψ, ← tiet_apply hKc.isClosed u ⟨x, hx⟩, dist_eq_norm] at h1
        exact h1.le
      · rw [Measure.restrict_apply_univ]
        have h2 : (volume K) ^ p.toReal⁻¹ = ENNReal.ofReal cK :=
          (ENNReal.ofReal_toReal
            (ENNReal.rpow_ne_top_of_nonneg (by positivity) hKc.measure_lt_top.ne)).symm
        rw [h2, ← ENNReal.ofReal_mul hcK0]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hε₃, mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith
    calc eLpNorm (⇑f - extOf hKc.isClosed u) p volume
        = eLpNorm (T1 + T2 + T3) p volume := by rw [hdec]
      _ ≤ eLpNorm (T1 + T2) p volume + eLpNorm T3 p volume :=
          eLpNorm_add_le (hm1.add hm2) hm3 Fact.out
      _ ≤ (eLpNorm T1 p volume + eLpNorm T2 p volume) + eLpNorm T3 p volume := by
          gcongr; exact eLpNorm_add_le hm1 hm2 Fact.out
      _ ≤ (ENNReal.ofReal (ε / 5) + ENNReal.ofReal (ε / 5)) + ENNReal.ofReal (ε / 5) := by
          gcongr
      _ = ENNReal.ofReal (ε / 5 + ε / 5 + ε / 5) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_add (by positivity) (by positivity)]
      _ < ENNReal.ofReal ε := by
          rw [ENNReal.ofReal_lt_ofReal_iff hε]; linarith
  exact isCompact_iff_totallyBounded_isComplete.mpr ⟨htb.closure, isClosed_closure.isComplete⟩


end KR

theorem solution {n : ℕ} (p : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (F : Set (Lp ℝ p (volume : Measure (EuclideanSpace ℝ (Fin n))))) :
    IsCompact (closure F) ↔
      ((∃ M : ℝ, ∀ f ∈ F, ‖f‖ ≤ M) ∧
        (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ f ∈ F,
          eLpNorm (f : EuclideanSpace ℝ (Fin n) → ℝ) p
            (volume.restrict {x : EuclideanSpace ℝ (Fin n) | R < ‖x‖}) < ENNReal.ofReal ε) ∧
        (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : EuclideanSpace ℝ (Fin n), ‖h‖ < δ → ∀ f ∈ F,
          eLpNorm (fun x => (f : EuclideanSpace ℝ (Fin n) → ℝ) (x + h) -
            (f : EuclideanSpace ℝ (Fin n) → ℝ) x) p volume < ENNReal.ofReal ε)) :=
  ⟨fun h => KR.forward hp F h, fun ⟨a, b, c⟩ => KR.backward hp F a b c⟩
