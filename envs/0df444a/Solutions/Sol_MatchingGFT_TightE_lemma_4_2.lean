-- Prove2me | solution 1 for MatchingGFT.TightE.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T18:25:19.688664+00:00
-- url     : https://prove2.me/submissions/4858916e-f12e-4078-9c49-ddbdc1377bb6

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Quantile
import Definitions.Def_MatchingGFT_TightE_Regularity
import Definitions.Def_MatchingGFT_TightE_CappedExp

open MeasureTheory Set

namespace CappedExpCalc

open MatchingGFT.TightE ProbabilityTheory Real Filter Topology

instance instProbExp : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos

lemma exp_ac : expMeasure 1 ≪ volume := by
  unfold expMeasure gammaMeasure; exact withDensity_absolutelyContinuous _ _

instance instNoAtomsExp : NullSingletonClass (expMeasure 1) := ⟨fun x => exp_ac (measure_singleton x)⟩

lemma E1_Iic (x : ℝ) : (expMeasure 1).real (Iic x) = if 0 ≤ x then 1 - Real.exp (-x) else 0 := by
  rw [← cdf_eq_real, cdf_expMeasure_eq one_pos]; simp

lemma E1_Ici (x : ℝ) : (expMeasure 1).real (Ici x) = if 0 ≤ x then Real.exp (-x) else 1 := by
  have h1 : (expMeasure 1).real (Ici x) = (expMeasure 1).real (Ioi x) :=
    measureReal_congr Ioi_ae_eq_Ici.symm
  rw [h1, ← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, E1_Iic]
  split_ifs <;> ring

lemma measurable_capB (L : ℝ) : Measurable fun x : ℝ => min x L :=
  measurable_id.min measurable_const

lemma measurable_capS (L : ℝ) : Measurable fun y : ℝ => L - min y L :=
  measurable_const.sub (measurable_capB L)

lemma F_real (L : ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    (cappedBuyerLaw L).real s = (expMeasure 1).real ((fun x => min x L) ⁻¹' s) := by
  unfold cappedBuyerLaw; rw [measureReal_def, Measure.map_apply (measurable_capB L) hs,
    measureReal_def]

lemma G_real (L : ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    (cappedSellerLaw L).real s = (expMeasure 1).real ((fun y => L - min y L) ⁻¹' s) := by
  unfold cappedSellerLaw; rw [measureReal_def, Measure.map_apply (measurable_capS L) hs,
    measureReal_def]

lemma F_Ici (L x : ℝ) : (cappedBuyerLaw L).real (Ici x) =
    if x ≤ L then (if 0 ≤ x then Real.exp (-x) else 1) else 0 := by
  rw [F_real L measurableSet_Ici]
  by_cases h1 : x ≤ L
  · rw [if_pos h1]
    have : (fun y => min y L) ⁻¹' Ici x = Ici x := by
      ext y; simp only [mem_preimage, mem_Ici, le_min_iff]; constructor
      · exact fun h => h.1
      · exact fun h => ⟨h, h1⟩
    rw [this, E1_Ici]
  · rw [if_neg h1]
    have : (fun y => min y L) ⁻¹' Ici x = ∅ := by
      ext y; simp only [mem_preimage, mem_Ici, le_min_iff, mem_empty_iff_false, iff_false,
        not_and]; intro _; exact h1
    rw [this]; simp

lemma G_Iic (L x : ℝ) : (cappedSellerLaw L).real (Iic x) =
    if 0 ≤ x then (if 0 ≤ L - x then Real.exp (-(L - x)) else 1) else 0 := by
  rw [G_real L measurableSet_Iic]
  by_cases h1 : 0 ≤ x
  · rw [if_pos h1]
    have : (fun y => L - min y L) ⁻¹' Iic x = Ici (L - x) := by
      ext y; simp only [mem_preimage, mem_Iic, mem_Ici]; constructor
      · intro h; rcases min_choice y L with h' | h' <;> rw [h'] at h <;> linarith [min_le_left y L]
      · intro h; have : L - x ≤ min y L := le_min h (by linarith)
        linarith
    rw [this, E1_Ici]
  · rw [if_neg h1]
    have : (fun y => L - min y L) ⁻¹' Iic x = ∅ := by
      ext y; simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false, not_le]
      linarith [min_le_right y L, not_le.mp h1]
    rw [this]; simp

lemma F_atom (L a : ℝ) (ha : a ≠ L) : (cappedBuyerLaw L).real {a} = 0 := by
  rw [F_real L (measurableSet_singleton a)]
  have hsub : (fun y => min y L) ⁻¹' {a} ⊆ {a} := by
    intro y hy
    simp only [mem_preimage, mem_singleton_iff] at hy ⊢
    rcases min_choice y L with h | h
    · rw [h] at hy; exact hy
    · rw [h] at hy; exact absurd hy.symm ha
  rw [measureReal_def, measure_mono_null hsub (measure_singleton a)]; simp

lemma G_atom (L a : ℝ) (ha : a ≠ 0) : (cappedSellerLaw L).real {a} = 0 := by
  rw [G_real L (measurableSet_singleton a)]
  have hsub : (fun y => L - min y L) ⁻¹' {a} ⊆ {L - a} := by
    intro y hy
    simp only [mem_preimage, mem_singleton_iff] at hy ⊢
    rcases min_choice y L with h | h
    · rw [h] at hy; linarith
    · rw [h] at hy; exact absurd hy.symm (by simpa using ha)
  rw [measureReal_def, measure_mono_null hsub (measure_singleton _)]; simp

lemma F_Ioi_L (L : ℝ) : (cappedBuyerLaw L).real (Ioi L) = 0 := by
  rw [F_real L measurableSet_Ioi]
  have : (fun y => min y L) ⁻¹' Ioi L = ∅ := by
    ext y; simp only [mem_preimage, mem_Ioi, mem_empty_iff_false, iff_false, not_lt]
    exact min_le_right y L
  rw [this]; simp

lemma G_Iio_0 (L : ℝ) : (cappedSellerLaw L).real (Iio 0) = 0 := by
  rw [G_real L measurableSet_Iio]
  have : (fun y => L - min y L) ⁻¹' Iio 0 = ∅ := by
    ext y; simp only [mem_preimage, mem_Iio, mem_empty_iff_false, iff_false, not_lt]
    linarith [min_le_right y L]
  rw [this]; simp

/-! ### Quantiles -/

lemma buyerQ (L : ℝ) (hL : 0 < L) {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) :
    buyerQuantile (cappedBuyerLaw L) ρ = min L (-Real.log ρ) := by
  have hlog : Real.log ρ < 0 := Real.log_neg hρ.1 hρ.2
  have hS : {x : ℝ | ρ ≤ (cappedBuyerLaw L).real (Ici x)} = Iic (min L (-Real.log ρ)) := by
    ext x
    simp only [mem_ofPred_eq, mem_Iic, le_min_iff, F_Ici]
    have key : ρ ≤ Real.exp (-x) ↔ Real.log ρ ≤ -x := (Real.log_le_iff_le_exp hρ.1).symm
    split_ifs with h1 h2
    · rw [key]; constructor
      · intro h; exact ⟨h1, by linarith⟩
      · intro h; linarith [h.2]
    · constructor
      · intro _; exact ⟨h1, by linarith⟩
      · intro _; exact hρ.2.le
    · constructor
      · intro h; linarith [hρ.1]
      · intro h; exact absurd h.1 h1
  unfold buyerQuantile; rw [hS, csSup_Iic]

lemma sellerQ (L : ℝ) (hL : 0 < L) {σ : ℝ} (hσ : σ ∈ Ioo (0 : ℝ) 1) :
    sellerQuantile (cappedSellerLaw L) σ = max 0 (L + Real.log σ) := by
  have hlog : Real.log σ < 0 := Real.log_neg hσ.1 hσ.2
  have hS : {x : ℝ | σ ≤ (cappedSellerLaw L).real (Iic x)} = Ici (max 0 (L + Real.log σ)) := by
    ext x
    simp only [mem_ofPred_eq, mem_Ici, max_le_iff, G_Iic]
    have key : σ ≤ Real.exp (-(L - x)) ↔ Real.log σ ≤ -(L - x) :=
      (Real.log_le_iff_le_exp hσ.1).symm
    split_ifs with h1 h2
    · rw [key]; constructor
      · intro h; exact ⟨h1, by linarith⟩
      · intro h; linarith [h.2]
    · constructor
      · intro _; exact ⟨h1, by linarith⟩
      · intro _; exact hσ.2.le
    · constructor
      · intro h; linarith [hσ.1]
      · intro h; exact absurd h.1 h1
  unfold sellerQuantile; rw [hS, csInf_Ici]

/-! ### Revenue and cost curves -/

/-- The explicit revenue curve `x ↦ x min(L, -log x)`. -/
noncomputable def Rt (L x : ℝ) : ℝ := x * min L (-Real.log x)

/-- The explicit cost curve `x ↦ x max(0, L + log x)`. -/
noncomputable def Kt (L x : ℝ) : ℝ := x * max 0 (L + Real.log x)

lemma revCurve_eq (L : ℝ) (hL : 0 < L) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    revCurve (cappedBuyerLaw L) x = Rt L x := by
  unfold revCurve Rt
  by_cases h0 : x = 0
  · simp [h0]
  by_cases h1 : x = 1
  · subst h1
    simp only [one_ne_zero, if_false, if_true, Real.log_one, neg_zero, one_mul,
      min_eq_right hL.le]
    apply leftLim_eq_of_tendsto
    have hev : (fun ρ : ℝ => ρ * buyerQuantile (cappedBuyerLaw L) ρ) =ᶠ[𝓝[<] (1 : ℝ)]
        fun ρ => ρ * min L (-Real.log ρ) := by
      filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 from one_pos)] with ρ hρ
      rw [buyerQ L hL hρ]
    refine Tendsto.congr' hev.symm ?_
    have hc : ContinuousAt (fun ρ : ℝ => ρ * min L (-Real.log ρ)) 1 := by
      apply ContinuousAt.mul continuousAt_id
      exact (continuous_min.continuousAt).comp (continuousAt_const.prodMk (Real.continuousAt_log one_ne_zero).neg)
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio 1))
    simpa [min_eq_right hL.le] using this
  · simp only [h0, h1, if_false]
    rw [buyerQ L hL ⟨lt_of_le_of_ne hx.1 (Ne.symm h0), lt_of_le_of_ne hx.2 h1⟩]

lemma costCurve_eq (L : ℝ) (hL : 0 < L) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    costCurve (cappedSellerLaw L) x = ((Kt L x : ℝ) : EReal) := by
  unfold costCurve Kt
  by_cases h0 : x = 0
  · simp [h0]
  by_cases h1 : x = 1
  · subst h1
    simp only [one_ne_zero, if_false, if_true, Real.log_one, add_zero, one_mul,
      max_eq_right hL.le]
    apply leftLim_eq_of_tendsto
    have hev : (fun σ : ℝ => ((σ * sellerQuantile (cappedSellerLaw L) σ : ℝ) : EReal)) =ᶠ[𝓝[<] (1 : ℝ)]
        fun σ => ((σ * max 0 (L + Real.log σ) : ℝ) : EReal) := by
      filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 from one_pos)] with σ hσ
      rw [sellerQ L hL hσ]
    refine Tendsto.congr' hev.symm ?_
    rw [EReal.tendsto_coe]
    have hc : ContinuousAt (fun σ : ℝ => σ * max 0 (L + Real.log σ)) 1 := by
      apply ContinuousAt.mul continuousAt_id
      exact (continuous_max.continuousAt).comp (continuousAt_const.prodMk (continuousAt_const.add (Real.continuousAt_log one_ne_zero)))
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio 1))
    simpa [max_eq_right hL.le] using this
  · simp only [h0, h1, if_false]
    rw [sellerQ L hL ⟨lt_of_le_of_ne hx.1 (Ne.symm h0), lt_of_le_of_ne hx.2 h1⟩]

lemma Rt_concave (L : ℝ) (hL : 0 < L) : ConcaveOn ℝ (Icc 0 1) (Rt L) := by
  have h1 : ConcaveOn ℝ (Icc (0 : ℝ) 1) fun x => L • id x := (concaveOn_id (convex_Icc 0 1)).smul hL.le
  have h2 : ConcaveOn ℝ (Icc (0 : ℝ) 1) negMulLog :=
    concaveOn_negMulLog.subset Icc_subset_Ici_self (convex_Icc 0 1)
  refine (h1.inf h2).congr ?_
  intro x hx
  simp only [Pi.inf_apply, smul_eq_mul, id, Rt, negMulLog]
  rw [mul_min_of_nonneg _ _ hx.1]; ring_nf

lemma Kt_convex (L : ℝ) (hL : 0 < L) : ConvexOn ℝ (Icc 0 1) (Kt L) := by
  have h1 : ConvexOn ℝ (Icc (0 : ℝ) 1) fun x => L • id x + x * Real.log x :=
    ((convexOn_id (convex_Icc 0 1)).smul hL.le).add
      (convexOn_mul_log.subset Icc_subset_Ici_self (convex_Icc 0 1))
  refine ((convexOn_const (0 : ℝ) (convex_Icc 0 1)).sup h1).congr ?_
  intro x hx
  simp only [Pi.sup_apply, smul_eq_mul, id, Kt]
  rw [mul_max_of_nonneg _ _ hx.1]; ring_nf

/-! ### Hulls and ironed slopes -/

lemma revHull_eq (L : ℝ) (hL : 0 < L) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    revHull (cappedBuyerLaw L) x = Rt L x := by
  unfold revHull
  apply IsLeast.csInf_eq
  constructor
  · exact ⟨Rt L, Rt_concave L hL, fun z hz => (revCurve_eq L hL hz).le, rfl⟩
  · rintro y ⟨g, _, hg, rfl⟩
    rw [← revCurve_eq L hL hx]; exact hg x hx

lemma costHull_eq (L : ℝ) (hL : 0 < L) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    costHull (cappedSellerLaw L) x = Kt L x := by
  unfold costHull
  apply IsGreatest.csSup_eq
  constructor
  · exact ⟨Kt L, Kt_convex L hL, fun z hz => (costCurve_eq L hL hz).ge, rfl⟩
  · rintro y ⟨g, _, hg, rfl⟩
    have := hg x hx
    rw [costCurve_eq L hL hx] at this
    exact EReal.coe_le_coe_iff.mp this

lemma slopeB (L : ℝ) (hL : 0 < L) {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) :
    ironedSlopeBuyer (cappedBuyerLaw L) ρ =
      if ρ ≤ Real.exp (-L) then L else -Real.log ρ - 1 := by
  unfold ironedSlopeBuyer
  have hev : revHull (cappedBuyerLaw L) =ᶠ[𝓝 ρ] Rt L := by
    filter_upwards [Icc_mem_nhds hρ.1 hρ.2] with x hx using revHull_eq L hL hx
  rw [Filter.EventuallyEq.derivWithin_eq (hev.filter_mono nhdsWithin_le_nhds) hev.eq_of_nhds]
  split_ifs with h
  · have hd : HasDerivWithinAt (Rt L) L (Iio ρ) ρ := by
      have h0 : HasDerivWithinAt (fun x : ℝ => L * x) L (Iio ρ) ρ := by
        simpa using ((hasDerivAt_id ρ).const_mul L).hasDerivWithinAt
      refine h0.congr_of_eventuallyEq ?_ ?_
      · filter_upwards [Ioo_mem_nhdsLT hρ.1] with x hx
        have : L ≤ -Real.log x := by
          have := Real.log_lt_log hx.1 (lt_of_lt_of_le hx.2 h)
          rw [Real.log_exp] at this; linarith
        rw [Rt, min_eq_left this, mul_comm]
      · have : L ≤ -Real.log ρ := by
          have := Real.log_le_log hρ.1 h
          rw [Real.log_exp] at this; linarith
        rw [Rt, min_eq_left this, mul_comm]
    exact hd.derivWithin (uniqueDiffWithinAt_Iio ρ)
  · push_neg at h
    have hd : HasDerivAt (Rt L) (-Real.log ρ - 1) ρ := by
      refine (hasDerivAt_negMulLog hρ.1.ne').congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds h] with x hx
      have : -Real.log x ≤ L := by
        have := Real.log_lt_log (Real.exp_pos _) hx
        rw [Real.log_exp] at this; linarith
      simp only [Rt, negMulLog, min_eq_right this]; ring
    exact hd.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iio ρ)

lemma slopeS (L : ℝ) (hL : 0 < L) {σ : ℝ} (hσ : σ ∈ Ioo (0 : ℝ) 1) :
    ironedSlopeSeller (cappedSellerLaw L) σ =
      if σ ≤ Real.exp (-L) then 0 else L + Real.log σ + 1 := by
  unfold ironedSlopeSeller
  have hev : costHull (cappedSellerLaw L) =ᶠ[𝓝 σ] Kt L := by
    filter_upwards [Icc_mem_nhds hσ.1 hσ.2] with x hx using costHull_eq L hL hx
  rw [Filter.EventuallyEq.derivWithin_eq (hev.filter_mono nhdsWithin_le_nhds) hev.eq_of_nhds]
  split_ifs with h
  · have hd : HasDerivWithinAt (Kt L) 0 (Iio σ) σ := by
      refine (hasDerivWithinAt_const σ (Iio σ) (0 : ℝ)).congr_of_eventuallyEq ?_ ?_
      · filter_upwards [Ioo_mem_nhdsLT hσ.1] with x hx
        have : L + Real.log x ≤ 0 := by
          have := Real.log_lt_log hx.1 (lt_of_lt_of_le hx.2 h)
          rw [Real.log_exp] at this; linarith
        rw [Kt, max_eq_left this, mul_zero]
      · have : L + Real.log σ ≤ 0 := by
          have := Real.log_le_log hσ.1 h
          rw [Real.log_exp] at this; linarith
        rw [Kt, max_eq_left this, mul_zero]
    exact hd.derivWithin (uniqueDiffWithinAt_Iio σ)
  · push_neg at h
    have hd : HasDerivAt (Kt L) (L + Real.log σ + 1) σ := by
      have h0 := (((hasDerivAt_id σ).const_mul L).add (hasDerivAt_mul_log hσ.1.ne')).congr_deriv
        (show L * 1 + (Real.log σ + 1) = L + Real.log σ + 1 by ring)
      refine h0.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds h] with x hx
      have : 0 ≤ L + Real.log x := by
        have := Real.log_lt_log (Real.exp_pos _) hx
        rw [Real.log_exp] at this; linarith
      simp only [Kt, id, Pi.add_apply, max_eq_right this]; ring
    exact hd.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iio σ)

/-! ### Virtual values -/

lemma expL_mem (L : ℝ) (hL : 0 < L) : Real.exp (-L) ∈ Ioo (0 : ℝ) 1 :=
  ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (by linarith)⟩

lemma vv (L : ℝ) (hL : 0 < L) (v : ℝ) :
    virtualValue (cappedBuyerLaw L) v =
      if v ≤ 0 then ⊥ else if v < L then ((v - 1 : ℝ) : EReal) else ((L : ℝ) : EReal) := by
  unfold virtualValue
  split_ifs with h1 h2
  · have : {ρ : ℝ | ρ ∈ Ioo (0 : ℝ) 1 ∧ buyerQuantile (cappedBuyerLaw L) ρ ≤ v} = ∅ := by
      ext ρ
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_le]
      intro hρ; rw [buyerQ L hL hρ]
      have := Real.log_neg hρ.1 hρ.2
      exact lt_of_le_of_lt h1 (lt_min hL (by linarith))
    rw [this, image_empty, _root_.sSup_empty]
  · push_neg at h1
    have hmem : Real.exp (-v) ∈ Ioo (0 : ℝ) 1 := ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (by linarith)⟩
    apply IsLUB.sSup_eq; apply IsGreatest.isLUB
    constructor
    · refine ⟨Real.exp (-v), ⟨hmem, ?_⟩, ?_⟩
      · rw [buyerQ L hL hmem, Real.log_exp, neg_neg]; exact min_le_right _ _
      · have : ¬ Real.exp (-v) ≤ Real.exp (-L) := by
          rw [Real.exp_le_exp]; linarith
        simp only; rw [slopeB L hL hmem, if_neg this, Real.log_exp, neg_neg]
    · rintro _ ⟨ρ, ⟨hρ, hQ⟩, rfl⟩
      rw [buyerQ L hL hρ] at hQ
      have hQ' : -Real.log ρ ≤ v := by
        rcases min_le_iff.mp hQ with h | h
        · linarith
        · exact h
      have : ¬ ρ ≤ Real.exp (-L) := by
        intro h
        have := Real.log_le_log hρ.1 h
        rw [Real.log_exp] at this; linarith
      simp only; rw [slopeB L hL hρ, if_neg this]
      exact EReal.coe_le_coe_iff.mpr (by linarith)
  · push_neg at h1 h2
    apply IsLUB.sSup_eq; apply IsGreatest.isLUB
    constructor
    · refine ⟨Real.exp (-L), ⟨expL_mem L hL, ?_⟩, ?_⟩
      · rw [buyerQ L hL (expL_mem L hL), Real.log_exp, neg_neg, min_self]; exact h2
      · simp only; rw [slopeB L hL (expL_mem L hL), if_pos le_rfl]
    · rintro _ ⟨ρ, ⟨hρ, _⟩, rfl⟩
      simp only; rw [slopeB L hL hρ]
      split_ifs with h
      · exact le_rfl
      · push_neg at h
        have := Real.log_lt_log (Real.exp_pos _) h
        rw [Real.log_exp] at this
        exact EReal.coe_le_coe_iff.mpr (by linarith)

lemma vc (L : ℝ) (hL : 0 < L) (c : ℝ) :
    virtualCost (cappedSellerLaw L) c =
      if c ≤ 0 then 0 else if c < L then ((c + 1 : ℝ) : EReal) else ⊤ := by
  unfold virtualCost
  split_ifs with h1 h2
  · rw [← EReal.coe_zero]
    apply IsGLB.sInf_eq; apply IsLeast.isGLB
    constructor
    · refine ⟨Real.exp (-L), ⟨expL_mem L hL, ?_⟩, ?_⟩
      · rw [sellerQ L hL (expL_mem L hL), Real.log_exp]; exact le_trans h1 (le_max_left _ _)
      · simp only; rw [slopeS L hL (expL_mem L hL), if_pos le_rfl]
    · rintro _ ⟨σ, ⟨hσ, _⟩, rfl⟩
      simp only; rw [slopeS L hL hσ]
      split_ifs with h
      · exact le_rfl
      · push_neg at h
        have := Real.log_lt_log (Real.exp_pos _) h
        rw [Real.log_exp] at this
        exact EReal.coe_le_coe_iff.mpr (by linarith)
  · push_neg at h1
    have hmem : Real.exp (c - L) ∈ Ioo (0 : ℝ) 1 :=
      ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (by linarith)⟩
    apply IsGLB.sInf_eq; apply IsLeast.isGLB
    constructor
    · refine ⟨Real.exp (c - L), ⟨hmem, ?_⟩, ?_⟩
      · rw [sellerQ L hL hmem, Real.log_exp]
        exact le_trans (le_of_eq (by ring)) (le_max_right _ _)
      · have : ¬ Real.exp (c - L) ≤ Real.exp (-L) := by
          rw [Real.exp_le_exp]; linarith
        simp only; rw [slopeS L hL hmem, if_neg this, Real.log_exp]
        congr 1; ring
    · rintro _ ⟨σ, ⟨hσ, hQ⟩, rfl⟩
      rw [sellerQ L hL hσ] at hQ
      have hQ' : c ≤ L + Real.log σ := by
        rcases le_max_iff.mp hQ with h | h
        · linarith
        · exact h
      have : ¬ σ ≤ Real.exp (-L) := by
        intro h
        have := Real.log_le_log hσ.1 h
        rw [Real.log_exp] at this; linarith
      simp only; rw [slopeS L hL hσ, if_neg this]
      exact EReal.coe_le_coe_iff.mpr (by linarith)
  · push_neg at h1 h2
    have : {σ : ℝ | σ ∈ Ioo (0 : ℝ) 1 ∧ c ≤ sellerQuantile (cappedSellerLaw L) σ} = ∅ := by
      ext σ
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_le]
      intro hσ; rw [sellerQ L hL hσ]
      have := Real.log_neg hσ.1 hσ.2
      exact lt_of_lt_of_le (max_lt hL (by linarith)) h2
    rw [this, image_empty, _root_.sInf_empty]

/-! ### Regularity -/

lemma revCurveLin_eq (L : ℝ) (hL : 0 < L) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    revCurveLin (cappedBuyerLaw L) x = Rt L x := by
  unfold revCurveLin
  split_ifs with h
  · have ha := h.choose_spec
    have haL : h.choose = L := by
      by_contra hne
      have := F_atom L _ hne
      linarith [ha.1]
    dsimp only
    rw [haL] at ha ⊢
    have hI : (cappedBuyerLaw L).real (Ici L) = Real.exp (-L) := by
      rw [F_Ici, if_pos le_rfl, if_pos hL.le]
    rw [F_Ioi_L, hI] at ha ⊢
    have hmem := expL_mem L hL
    rw [revCurve_eq L hL ⟨le_rfl, zero_le_one⟩, revCurve_eq L hL ⟨hmem.1.le, hmem.2.le⟩]
    have hx0 : 0 < x := ha.2.1
    have hxL : L ≤ -Real.log x := by
      have := Real.log_lt_log hx0 ha.2.2
      rw [Real.log_exp] at this; linarith
    simp only [Rt, Real.log_exp, neg_neg, min_self, min_eq_left hxL, zero_mul, sub_zero, add_zero,
      zero_add]
    field_simp
  · exact revCurve_eq L hL hx

lemma costCurveLin_eq (L : ℝ) (hL : 0 < L) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    costCurveLin (cappedSellerLaw L) x = Kt L x := by
  unfold costCurveLin
  split_ifs with h
  · have ha := h.choose_spec
    have ha0 : h.choose = 0 := by
      by_contra hne
      have := G_atom L _ hne
      linarith [ha.1]
    dsimp only
    rw [ha0] at ha ⊢
    have hI : (cappedSellerLaw L).real (Iic 0) = Real.exp (-L) := by
      rw [G_Iic, if_pos le_rfl, if_pos (by linarith), sub_zero]
    rw [G_Iio_0, hI] at ha ⊢
    have hmem := expL_mem L hL
    rw [costCurve_eq L hL ⟨le_rfl, zero_le_one⟩, costCurve_eq L hL ⟨hmem.1.le, hmem.2.le⟩]
    have hx0 : 0 < x := ha.2.1
    have hxL : L + Real.log x ≤ 0 := by
      have := Real.log_lt_log hx0 ha.2.2
      rw [Real.log_exp] at this; linarith
    simp only [Kt, Real.log_exp, add_neg_cancel, max_self, max_eq_left hxL, mul_zero, zero_mul,
      EReal.toReal_coe, sub_zero, add_zero]
  · rw [costCurve_eq L hL hx, EReal.toReal_coe]

lemma regularB (L : ℝ) (hL : 0 < L) : IsRegularBuyerLaw (cappedBuyerLaw L) :=
  (Rt_concave L hL).congr fun _ hx => (revCurveLin_eq L hL hx).symm

lemma regularS (L : ℝ) (hL : 0 < L) : IsRegularSellerLaw (cappedSellerLaw L) :=
  ((Kt_convex L hL).subset Ico_subset_Icc_self (convex_Ico 0 1)).congr
    fun _ hx => (costCurveLin_eq L hL (Ico_subset_Icc_self hx)).symm

/-! ### Supports -/

lemma E1_pos : ∀ᵐ x ∂(expMeasure 1), 0 < x := by
  rw [ae_iff]
  have : {a : ℝ | ¬ 0 < a} = Iic 0 := by ext a; simp
  rw [this]
  have h := E1_Iic 0
  simp only [le_refl, if_true, neg_zero, Real.exp_zero, sub_self] at h
  exact (measureReal_eq_zero_iff).mp h

lemma F_ae (L : ℝ) (hL : 0 < L) : ∀ᵐ v ∂(cappedBuyerLaw L), v ∈ Ioc 0 L := by
  unfold cappedBuyerLaw
  rw [ae_map_iff (measurable_capB L).aemeasurable (p := fun v => v ∈ Ioc 0 L) measurableSet_Ioc]
  filter_upwards [E1_pos] with x hx
  exact ⟨lt_min hx hL, min_le_right _ _⟩

lemma G_ae (L : ℝ) (hL : 0 < L) : ∀ᵐ c ∂(cappedSellerLaw L), c ∈ Ico 0 L := by
  unfold cappedSellerLaw
  rw [ae_map_iff (measurable_capS L).aemeasurable (p := fun v => v ∈ Ico 0 L) measurableSet_Ico]
  filter_upwards [E1_pos] with x hx
  exact ⟨by linarith [min_le_right x L], by linarith [lt_min hx hL]⟩

instance instProbF (L : ℝ) : IsProbabilityMeasure (cappedBuyerLaw L) := by
  unfold cappedBuyerLaw; exact Measure.isProbabilityMeasure_map (measurable_capB L).aemeasurable

instance instProbG (L : ℝ) : IsProbabilityMeasure (cappedSellerLaw L) := by
  unfold cappedSellerLaw; exact Measure.isProbabilityMeasure_map (measurable_capS L).aemeasurable

instance instProbPair (L : ℝ) : IsProbabilityMeasure (cappedPairLaw L) := by
  unfold cappedPairLaw; infer_instance

lemma pair_ae (L : ℝ) (hL : 0 < L) :
    ∀ᵐ p ∂(cappedPairLaw L), p.1 ∈ Ioc 0 L ∧ p.2 ∈ Ico 0 L := by
  unfold cappedPairLaw
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := cappedBuyerLaw L)
    (ν := cappedSellerLaw L)).ae (F_ae L hL)
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := cappedBuyerLaw L)
    (ν := cappedSellerLaw L)).ae (G_ae L hL)
  filter_upwards [h1, h2] with p hp1 hp2 using ⟨hp1, hp2⟩

lemma pair_integrable (L : ℝ) (hL : 0 < L) (f : ℝ × ℝ → ℝ) (hf : Measurable f) (C : ℝ)
    (hC : ∀ p : ℝ × ℝ, p.1 ∈ Ioc 0 L → p.2 ∈ Ico 0 L → |f p| ≤ C) :
    Integrable f (cappedPairLaw L) := by
  refine Integrable.mono' (integrable_const C) hf.aestronglyMeasurable ?_
  filter_upwards [pair_ae L hL] with p hp
  rw [Real.norm_eq_abs]; exact hC p hp.1 hp.2

/-! ### One-dimensional integrals -/

lemma integral_E1_cap (L : ℝ) (hL : 0 < L) (h : ℝ → ℝ) (hm : Measurable h) (C : ℝ)
    (hC : ∀ x ∈ Icc 0 L, |h x| ≤ C) :
    ∫ x, h (min x L) ∂(expMeasure 1) =
      (∫ x in (0 : ℝ)..L, h x * Real.exp (-x)) + h L * Real.exp (-L) := by
  have hpdf : ∀ x, (gammaPDF 1 1 x).toReal = if 0 ≤ x then Real.exp (-x) else 0 := by
    intro x
    rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg one_pos one_pos x), gammaPDFReal]
    simp
  have e1 : ∫ x, h (min x L) ∂(expMeasure 1) = ∫ x in Ici 0, Real.exp (-x) * h (min x L) := by
    unfold expMeasure gammaMeasure
    rw [integral_withDensity_eq_integral_toReal_smul (f := gammaPDF 1 1)
      (by exact (measurable_gammaPDFReal 1 1).ennreal_ofReal)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top), ← integral_indicator measurableSet_Ici]
    congr 1; ext x
    rw [hpdf, smul_eq_mul, indicator]
    by_cases hx : 0 ≤ x
    · rw [if_pos hx, if_pos (show x ∈ Ici (0 : ℝ) from hx)]
    · rw [if_neg hx, if_neg (show x ∉ Ici (0 : ℝ) from hx), zero_mul]
  have hmeas : Measurable fun x => Real.exp (-x) * h (min x L) :=
    (Real.measurable_exp.comp measurable_neg).mul (hm.comp (measurable_capB L))
  have hI1 : IntegrableOn (fun x => Real.exp (-x) * h (min x L)) (Ioc 0 L) := by
    refine Measure.integrableOn_of_bounded (M := C) measure_Ioc_lt_top.ne
      hmeas.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun x hx => ?_)
    rw [min_eq_left hx.2, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have h1 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hx.1])
    have h2 := hC x ⟨hx.1.le, hx.2⟩
    nlinarith [abs_nonneg (h x), Real.exp_pos (-x)]
  have hI2 : IntegrableOn (fun x => Real.exp (-x) * h (min x L)) (Ioi L) := by
    have : IntegrableOn (fun x => Real.exp (-1 * x) * h L) (Ioi L) :=
      (exp_neg_integrableOn_Ioi L one_pos).mul_const _
    refine this.congr_fun (fun x hx => ?_) measurableSet_Ioi
    (try simp only); rw [min_eq_right (le_of_lt hx), neg_one_mul]
  rw [e1, integral_Ici_eq_integral_Ioi, ← Ioc_union_Ioi_eq_Ioi hL.le,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hI1 hI2]
  have p1 : ∫ x in Ioc 0 L, Real.exp (-x) * h (min x L) =
      ∫ x in (0 : ℝ)..L, h x * Real.exp (-x) := by
    rw [intervalIntegral.integral_of_le hL.le]
    refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
    (try simp only); rw [min_eq_left hx.2, mul_comm]
  have p2 : ∫ x in Ioi L, Real.exp (-x) * h (min x L) = h L * Real.exp (-L) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun x => Real.exp (-x) * h L)
      (fun x hx => by (try simp only); rw [min_eq_right (le_of_lt hx)]),
      integral_mul_const, integral_exp_neg_Ioi, mul_comm]
  rw [p1, p2]

lemma integral_F (L : ℝ) (hL : 0 < L) (k : ℝ → ℝ) (hk : Measurable k) (C : ℝ)
    (hC : ∀ x ∈ Icc 0 L, |k x| ≤ C) :
    ∫ v, k v ∂(cappedBuyerLaw L) =
      (∫ x in (0 : ℝ)..L, k x * Real.exp (-x)) + k L * Real.exp (-L) := by
  unfold cappedBuyerLaw
  rw [integral_map (measurable_capB L).aemeasurable hk.aestronglyMeasurable]
  exact integral_E1_cap L hL k hk C hC

lemma integral_G (L : ℝ) (hL : 0 < L) (k : ℝ → ℝ) (hk : Measurable k) (C : ℝ)
    (hC : ∀ x ∈ Icc 0 L, |k x| ≤ C) :
    ∫ c, k c ∂(cappedSellerLaw L) =
      (∫ c in (0 : ℝ)..L, k c * Real.exp (c - L)) + k 0 * Real.exp (-L) := by
  unfold cappedSellerLaw
  rw [integral_map (measurable_capS L).aemeasurable hk.aestronglyMeasurable]
  have := integral_E1_cap L hL (fun t => k (L - t)) (hk.comp (measurable_const.sub measurable_id))
    C (fun x hx => hC (L - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩)
  simp only [sub_self] at this
  rw [this]
  congr 1
  have h2 : (fun y => k (L - y) * Real.exp (-y)) =
      fun y => (fun c => k c * Real.exp (c - L)) (L - y) := by
    ext y; simp only [sub_sub_cancel_left]
  rw [h2, intervalIntegral.integral_comp_sub_left (fun c => k c * Real.exp (c - L)) L]
  simp

lemma ftc {F f : ℝ → ℝ} (a b : ℝ) (hd : ∀ x, HasDerivAt F (f x) x) (hc : Continuous f) :
    ∫ x in a..b, f x = F b - F a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (hc.intervalIntegrable a b)

lemma bound_aux (L t : ℝ) (ht0 : 0 ≤ t) (htL : t ≤ L) :
    |Real.exp (-L) * (Real.exp t - 1)| ≤ 1 := by
  have h1 : 1 ≤ Real.exp t := Real.one_le_exp ht0
  have h2 : Real.exp t ≤ Real.exp L := Real.exp_le_exp.mpr htL
  have h3 : Real.exp (-L) * Real.exp L = 1 := by rw [← Real.exp_add]; simp
  rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (by linarith))]
  nlinarith [Real.exp_pos (-L)]

/-! ### Inner integrals -/

lemma inner_c (L : ℝ) (hL : 0 < L) (a : ℝ) (ha : a ≤ L) :
    ∫ c, max (a - c) 0 ∂(cappedSellerLaw L) = Real.exp (-L) * (Real.exp (max a 0) - 1) := by
  rw [integral_G L hL (fun c => max (a - c) 0) (by fun_prop) L (fun x hx => by
    rw [abs_of_nonneg (le_max_right _ _)]; exact max_le (by linarith [hx.1]) hL.le)]
  simp only [sub_zero]
  have hcont : Continuous fun c => max (a - c) 0 * Real.exp (c - L) := by fun_prop
  rcases le_or_gt a 0 with h0 | h0
  · have : EqOn (fun c => max (a - c) 0 * Real.exp (c - L)) (fun _ => (0 : ℝ)) (uIcc 0 L) := by
      intro c hc
      rw [uIcc_of_le hL.le] at hc
      (try simp only); rw [max_eq_right (by linarith [hc.1]), zero_mul]
    rw [intervalIntegral.integral_congr this, intervalIntegral.integral_zero, max_eq_right h0,
      Real.exp_zero]
    ring
  · rw [← intervalIntegral.integral_add_adjacent_intervals (b := a) (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)]
    have e1 : EqOn (fun c => max (a - c) 0 * Real.exp (c - L))
        (fun c => (a - c) * Real.exp (c - L)) (uIcc 0 a) := by
      intro c hc
      rw [uIcc_of_le h0.le] at hc
      (try simp only); rw [max_eq_left (by linarith [hc.2])]
    have e2 : EqOn (fun c => max (a - c) 0 * Real.exp (c - L)) (fun _ => (0 : ℝ)) (uIcc a L) := by
      intro c hc
      rw [uIcc_of_le ha] at hc
      (try simp only); rw [max_eq_right (by linarith [hc.1]), zero_mul]
    rw [intervalIntegral.integral_congr e1, intervalIntegral.integral_congr e2,
      intervalIntegral.integral_zero,
      ftc (F := fun c => (a - c + 1) * Real.exp (c - L)) (f := fun c => (a - c) * Real.exp (c - L))
        0 a (fun c => by
          have := (((hasDerivAt_id c).const_sub a).add_const 1).mul
            ((hasDerivAt_id c).sub_const L).exp
          exact this.congr_deriv (by (try simp only [id, Pi.neg_apply, Pi.mul_apply, id_eq]); ring)) (by fun_prop)]
    rw [max_eq_left h0.le]
    have : Real.exp (a - L) = Real.exp a * Real.exp (-L) := by rw [← Real.exp_add]; ring_nf
    rw [show (0 : ℝ) - L = -L by ring, this]
    ring

lemma inner_v (L : ℝ) (hL : 0 < L) (b : ℝ) (hb : 0 ≤ b) :
    ∫ v, max (v - b) 0 ∂(cappedBuyerLaw L) = Real.exp (-min b L) - Real.exp (-L) := by
  rw [integral_F L hL (fun v => max (v - b) 0) (by fun_prop) L (fun x hx => by
    rw [abs_of_nonneg (le_max_right _ _)]; exact max_le (by linarith [hx.2]) hL.le)]
  have hcont : Continuous fun x => max (x - b) 0 * Real.exp (-x) := by fun_prop
  rcases le_or_gt L b with h0 | h0
  · have : EqOn (fun x => max (x - b) 0 * Real.exp (-x)) (fun _ => (0 : ℝ)) (uIcc 0 L) := by
      intro x hx
      rw [uIcc_of_le hL.le] at hx
      (try simp only); rw [max_eq_right (by linarith [hx.2]), zero_mul]
    rw [intervalIntegral.integral_congr this, intervalIntegral.integral_zero,
      max_eq_right (by linarith : L - b ≤ 0), min_eq_right h0]
    ring
  · rw [← intervalIntegral.integral_add_adjacent_intervals (b := b) (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)]
    have e1 : EqOn (fun x => max (x - b) 0 * Real.exp (-x)) (fun _ => (0 : ℝ)) (uIcc 0 b) := by
      intro x hx
      rw [uIcc_of_le hb] at hx
      (try simp only); rw [max_eq_right (by linarith [hx.2]), zero_mul]
    have e2 : EqOn (fun x => max (x - b) 0 * Real.exp (-x))
        (fun x => (x - b) * Real.exp (-x)) (uIcc b L) := by
      intro x hx
      rw [uIcc_of_le h0.le] at hx
      (try simp only); rw [max_eq_left (by linarith [hx.1])]
    rw [intervalIntegral.integral_congr e1, intervalIntegral.integral_congr e2,
      intervalIntegral.integral_zero,
      ftc (F := fun x => -(x - b + 1) * Real.exp (-x)) (f := fun x => (x - b) * Real.exp (-x))
        b L (fun x => by
          have := (((hasDerivAt_id x).sub_const b).add_const 1).neg.mul (hasDerivAt_id x).neg.exp
          exact this.congr_deriv (by (try simp only [id, Pi.neg_apply, Pi.mul_apply, id_eq]); ring)) (by fun_prop),
      max_eq_left (by linarith : 0 ≤ L - b), min_eq_left h0.le]
    ring

/-! ### The three values -/

/-- The real representative of the buyer virtual value on `(0, L]`. -/
noncomputable def phiR (L v : ℝ) : ℝ := if v < L then v - 1 else L

/-- The real representative of the seller virtual cost on `[0, L)`. -/
noncomputable def psiR (c : ℝ) : ℝ := if c = 0 then 0 else c + 1

lemma measurable_phiR (L : ℝ) : Measurable (phiR L) := by
  unfold phiR; exact Measurable.ite measurableSet_Iio (measurable_id.sub_const 1) measurable_const

lemma measurable_psiR : Measurable psiR := by
  unfold psiR
  exact Measurable.ite (measurableSet_singleton 0) measurable_const (measurable_id.add_const 1)

lemma vv_ae (L : ℝ) (hL : 0 < L) {v : ℝ} (hv : v ∈ Ioc 0 L) :
    virtualValue (cappedBuyerLaw L) v = ((phiR L v : ℝ) : EReal) := by
  rw [vv L hL v, if_neg (not_le.mpr hv.1), phiR]; split_ifs <;> rfl

lemma vc_ae (L : ℝ) (hL : 0 < L) {c : ℝ} (hc : c ∈ Ico 0 L) :
    virtualCost (cappedSellerLaw L) c = ((psiR c : ℝ) : EReal) := by
  rw [vc L hL c, psiR]
  by_cases h0 : c = 0
  · subst h0; simp
  · have hpos : 0 < c := lt_of_le_of_ne hc.1 (Ne.symm h0)
    rw [if_neg (not_le.mpr hpos), if_pos hc.2, if_neg h0]

lemma toReal_max_coe (x : ℝ) : (max ((x : ℝ) : EReal) 0).toReal = max x 0 := by
  rcases le_total x 0 with h | h
  · rw [max_eq_right h, max_eq_right (by exact_mod_cast h)]; simp
  · rw [max_eq_left h, max_eq_left (by exact_mod_cast h)]; simp

lemma g_value (L : ℝ) (hL : 0 < L) : cappedG L = L * Real.exp (-L) := by
  have hint : Integrable (fun p : ℝ × ℝ => max (p.1 - p.2) 0) (cappedPairLaw L) :=
    pair_integrable L hL _ (by fun_prop) L (fun p h1 h2 => by
      rw [abs_of_nonneg (le_max_right _ _)]; exact max_le (by linarith [h1.2, h2.1]) hL.le)
  unfold cappedG
  unfold cappedPairLaw at hint ⊢
  rw [integral_prod _ hint]
  have hin : ∀ᵐ v ∂(cappedBuyerLaw L), ∫ c, max ((v, c).1 - (v, c).2) 0 ∂(cappedSellerLaw L) =
      Real.exp (-L) * (Real.exp (max v 0) - 1) := by
    filter_upwards [F_ae L hL] with v hv using inner_c L hL v hv.2
  rw [integral_congr_ae hin]
  rw [integral_F L hL (fun v => Real.exp (-L) * (Real.exp (max v 0) - 1)) (by fun_prop) 1
    (fun x hx => bound_aux L (max x 0) (le_max_right _ _) (max_le hx.2 hL.le))]
  have e : EqOn (fun x => Real.exp (-L) * (Real.exp (max x 0) - 1) * Real.exp (-x))
      (fun x => Real.exp (-L) * (1 - Real.exp (-x))) (uIcc 0 L) := by
    intro x hx
    rw [uIcc_of_le hL.le] at hx
    have : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
    (try simp only); rw [max_eq_left hx.1]
    linear_combination Real.exp (-L) * this
  rw [intervalIntegral.integral_congr e,
    ftc (F := fun x => Real.exp (-L) * (x + Real.exp (-x)))
      (f := fun x => Real.exp (-L) * (1 - Real.exp (-x))) 0 L (fun x => by
        have := ((hasDerivAt_id x).add (hasDerivAt_id x).neg.exp).const_mul (Real.exp (-L))
        exact this.congr_deriv (by (try simp only [id, Pi.neg_apply, Pi.mul_apply, id_eq]); ring)) (by fun_prop)]
  have h1 : Real.exp L * Real.exp (-L) = 1 := by rw [← Real.exp_add]; simp
  rw [max_eq_left hL.le, neg_zero, Real.exp_zero]
  linear_combination Real.exp (-L) * h1

lemma PS_value (L : ℝ) (hL : 2 ≤ L) :
    cappedPS L = Real.exp (-L) * (1 + (L - 2) / Real.exp 1) := by
  have hL0 : 0 < L := by linarith
  have hcongr : (fun p : ℝ × ℝ =>
      (max (virtualValue (cappedBuyerLaw L) p.1 - ((p.2 : ℝ) : EReal)) 0).toReal)
      =ᵐ[cappedPairLaw L] fun p => max (phiR L p.1 - p.2) 0 := by
    filter_upwards [pair_ae L hL0] with p hp
    rw [vv_ae L hL0 hp.1, ← EReal.coe_sub, toReal_max_coe]
  have hφle : ∀ v, phiR L v ≤ L := fun v => by unfold phiR; split_ifs with h <;> linarith
  have hint : Integrable (fun p : ℝ × ℝ => max (phiR L p.1 - p.2) 0) (cappedPairLaw L) :=
    pair_integrable L hL0 _
      ((((measurable_phiR L).comp measurable_fst).sub measurable_snd).max measurable_const) L
      (fun p h1 h2 => by
        rw [abs_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith [hφle p.1, h2.1]) hL0.le)
  unfold cappedPS
  rw [integral_congr_ae hcongr]
  unfold cappedPairLaw at hint ⊢
  rw [integral_prod _ hint]
  have hin : ∀ᵐ v ∂(cappedBuyerLaw L),
      ∫ c, max (phiR L (v, c).1 - (v, c).2) 0 ∂(cappedSellerLaw L) =
        Real.exp (-L) * (Real.exp (max (phiR L v) 0) - 1) :=
    ae_of_all _ fun v => inner_c L hL0 _ (hφle v)
  rw [integral_congr_ae hin]
  rw [integral_F L hL0 (fun v => Real.exp (-L) * (Real.exp (max (phiR L v) 0) - 1))
    (by have := measurable_phiR L; fun_prop) 1
    (fun x hx => bound_aux L (max (phiR L x) 0) (le_max_right _ _) (max_le (hφle x) hL0.le))]
  have e0 : ∫ x in (0 : ℝ)..L, Real.exp (-L) * (Real.exp (max (phiR L x) 0) - 1) * Real.exp (-x) =
      ∫ x in (0 : ℝ)..L, Real.exp (-L) * (Real.exp (max (x - 1) 0) - 1) * Real.exp (-x) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [Measure.ae_ne volume L] with x hxL hx
    rw [uIoc_of_le hL0.le] at hx
    rw [phiR, if_pos (lt_of_le_of_ne hx.2 hxL)]
  rw [e0]
  have hcont : Continuous fun x => Real.exp (-L) * (Real.exp (max (x - 1) 0) - 1) * Real.exp (-x) := by
    fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1) (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)]
  have e1 : EqOn (fun x => Real.exp (-L) * (Real.exp (max (x - 1) 0) - 1) * Real.exp (-x))
      (fun _ => (0 : ℝ)) (uIcc 0 1) := by
    intro x hx
    rw [uIcc_of_le zero_le_one] at hx
    (try simp only); rw [max_eq_right (by linarith [hx.2]), Real.exp_zero]; ring
  have e2 : EqOn (fun x => Real.exp (-L) * (Real.exp (max (x - 1) 0) - 1) * Real.exp (-x))
      (fun x => Real.exp (-L) * (Real.exp (-1) - Real.exp (-x))) (uIcc 1 L) := by
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    have : Real.exp (x - 1) * Real.exp (-x) = Real.exp (-1) := by
      rw [← Real.exp_add]; congr 1 <;> ring
    (try simp only); rw [max_eq_left (by linarith [hx.1])]
    linear_combination Real.exp (-L) * this
  rw [intervalIntegral.integral_congr e1, intervalIntegral.integral_congr e2,
    intervalIntegral.integral_zero,
    ftc (F := fun x => Real.exp (-L) * (x * Real.exp (-1) + Real.exp (-x)))
      (f := fun x => Real.exp (-L) * (Real.exp (-1) - Real.exp (-x))) 1 L (fun x => by
        have := (((hasDerivAt_id x).mul_const (Real.exp (-1))).add
          (hasDerivAt_id x).neg.exp).const_mul (Real.exp (-L))
        exact this.congr_deriv (by (try simp only [id, Pi.neg_apply, Pi.mul_apply, id_eq]); ring)) (by fun_prop)]
  have hpL : phiR L L = L := by simp [phiR]
  have h1 : Real.exp L * Real.exp (-L) = 1 := by rw [← Real.exp_add]; simp
  rw [hpL, max_eq_left hL0.le, show Real.exp (-1) = (Real.exp 1)⁻¹ from Real.exp_neg 1]
  linear_combination Real.exp (-L) * h1

lemma PB_value (L : ℝ) (hL : 2 ≤ L) :
    cappedPB L = Real.exp (-L) * (1 + (L - 2) / Real.exp 1) := by
  have hL0 : 0 < L := by linarith
  have hψ0 : ∀ c, 0 ≤ c → 0 ≤ psiR c := fun c hc => by unfold psiR; split_ifs <;> linarith
  have hcongr : (fun p : ℝ × ℝ =>
      (max (((p.1 : ℝ) : EReal) - virtualCost (cappedSellerLaw L) p.2) 0).toReal)
      =ᵐ[cappedPairLaw L] fun p => max (p.1 - psiR p.2) 0 := by
    filter_upwards [pair_ae L hL0] with p hp
    rw [vc_ae L hL0 hp.2, ← EReal.coe_sub, toReal_max_coe]
  have hint : Integrable (fun p : ℝ × ℝ => max (p.1 - psiR p.2) 0) (cappedPairLaw L) :=
    pair_integrable L hL0 _
      ((measurable_fst.sub (measurable_psiR.comp measurable_snd)).max measurable_const) L
      (fun p h1 h2 => by
        rw [abs_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith [hψ0 p.2 h2.1, h1.2]) hL0.le)
  unfold cappedPB
  rw [integral_congr_ae hcongr]
  unfold cappedPairLaw at hint ⊢
  rw [integral_prod_symm _ hint]
  have hin : ∀ᵐ c ∂(cappedSellerLaw L),
      ∫ v, max ((v, c).1 - psiR (v, c).2) 0 ∂(cappedBuyerLaw L) =
        Real.exp (-min (psiR c) L) - Real.exp (-L) := by
    filter_upwards [G_ae L hL0] with c hc using inner_v L hL0 _ (hψ0 c hc.1)
  rw [integral_congr_ae hin]
  rw [integral_G L hL0 (fun c => Real.exp (-min (psiR c) L) - Real.exp (-L))
    ((Real.measurable_exp.comp (measurable_psiR.min measurable_const).neg).sub measurable_const) 1
    (fun x hx => by
      have hm0 : 0 ≤ min (psiR x) L := le_min (hψ0 x hx.1) hL0.le
      have h1 : Real.exp (-min (psiR x) L) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have h2 : Real.exp (-L) ≤ Real.exp (-min (psiR x) L) :=
        Real.exp_le_exp.mpr (by linarith [min_le_right (psiR x) L])
      rw [abs_le]; constructor <;> linarith [Real.exp_pos (-L)])]
  have e0 : ∫ c in (0 : ℝ)..L, (Real.exp (-min (psiR c) L) - Real.exp (-L)) * Real.exp (c - L) =
      ∫ c in (0 : ℝ)..L, (Real.exp (-min (c + 1) L) - Real.exp (-L)) * Real.exp (c - L) := by
    refine intervalIntegral.integral_congr_ae (ae_of_all _ fun c hc => ?_)
    rw [uIoc_of_le hL0.le] at hc
    rw [psiR, if_neg hc.1.ne']
  rw [e0]
  have hcont : Continuous fun c => (Real.exp (-min (c + 1) L) - Real.exp (-L)) * Real.exp (c - L) := by
    fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := L - 1) (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)]
  have e1 : EqOn (fun c => (Real.exp (-min (c + 1) L) - Real.exp (-L)) * Real.exp (c - L))
      (fun c => Real.exp (-L - 1) - Real.exp (c - 2 * L)) (uIcc 0 (L - 1)) := by
    intro c hc
    rw [uIcc_of_le (by linarith)] at hc
    (try simp only); rw [min_eq_left (by linarith [hc.2]), sub_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1 <;> congr 1 <;> ring
  have e2 : EqOn (fun c => (Real.exp (-min (c + 1) L) - Real.exp (-L)) * Real.exp (c - L))
      (fun _ => (0 : ℝ)) (uIcc (L - 1) L) := by
    intro c hc
    rw [uIcc_of_le (by linarith)] at hc
    (try simp only); rw [min_eq_right (by linarith [hc.1]), sub_self, zero_mul]
  rw [intervalIntegral.integral_congr e1, intervalIntegral.integral_congr e2,
    intervalIntegral.integral_zero,
    ftc (F := fun c => c * Real.exp (-L - 1) - Real.exp (c - 2 * L))
      (f := fun c => Real.exp (-L - 1) - Real.exp (c - 2 * L)) 0 (L - 1) (fun c => by
        have := ((hasDerivAt_id c).mul_const (Real.exp (-L - 1))).sub
          ((hasDerivAt_id c).sub_const (2 * L)).exp
        exact this.congr_deriv (by (try simp only [id, Pi.neg_apply, Pi.mul_apply, id_eq]); ring)) (by fun_prop)]
  have hp0 : psiR 0 = 0 := by simp [psiR]
  have hA : Real.exp (-L - 1) = Real.exp (-L) * (Real.exp 1)⁻¹ := by
    rw [← Real.exp_neg, ← Real.exp_add]; congr 1 <;> ring
  have hB : Real.exp (L - 1 - 2 * L) = Real.exp (-L) * (Real.exp 1)⁻¹ := by
    rw [← Real.exp_neg, ← Real.exp_add]; congr 1 <;> ring
  have hC : Real.exp (0 - 2 * L) = Real.exp (-L) * Real.exp (-L) := by
    rw [← Real.exp_add]; congr 1 <;> ring
  rw [hp0, min_eq_left hL0.le, neg_zero, Real.exp_zero, hA, hB, hC]
  ring

end CappedExpCalc

open MatchingGFT.TightE CappedExpCalc in
theorem solution (L : ℝ) (hL : 2 ≤ L) :
    IsRegularBuyerLaw (cappedBuyerLaw L) ∧ IsRegularSellerLaw (cappedSellerLaw L) ∧
    (∀ᵐ v ∂cappedBuyerLaw L, virtualValue (cappedBuyerLaw L) v =
      if v < L then ((v - 1 : ℝ) : EReal) else ((L : ℝ) : EReal)) ∧
    (∀ᵐ c ∂cappedSellerLaw L, virtualCost (cappedSellerLaw L) c =
      if c = 0 then 0 else ((c + 1 : ℝ) : EReal)) ∧
    (∀ v ∈ Icc (0 : ℝ) L, virtualValue (cappedBuyerLaw L) v =
      if v = 0 then ⊥ else if v < L then ((v - 1 : ℝ) : EReal) else ((L : ℝ) : EReal)) ∧
    (∀ c ∈ Icc (0 : ℝ) L, virtualCost (cappedSellerLaw L) c =
      if c = 0 then 0 else if c < L then ((c + 1 : ℝ) : EReal) else ⊤) ∧
    (∀ z ∈ Icc (0 : ℝ) L, virtualCost (cappedSellerLaw L) (L - z) =
      ((L : ℝ) : EReal) - virtualValue (cappedBuyerLaw L) z) ∧
    cappedG L = L * Real.exp (-L) ∧
    cappedPS L = Real.exp (-L) * (1 + (L - 2) / Real.exp 1) ∧
    cappedPB L = Real.exp (-L) * (1 + (L - 2) / Real.exp 1) := by
  have hL0 : 0 < L := by linarith
  refine ⟨regularB L hL0, regularS L hL0, ?_, ?_, ?_, ?_, ?_, g_value L hL0, PS_value L hL,
    PB_value L hL⟩
  · filter_upwards [F_ae L hL0] with v hv
    rw [vv L hL0 v, if_neg (not_le.mpr hv.1)]
  · filter_upwards [G_ae L hL0] with c hc
    rw [vc L hL0 c]
    by_cases h0 : c = 0
    · simp [h0]
    · rw [if_neg (not_le.mpr (lt_of_le_of_ne hc.1 (Ne.symm h0))), if_pos hc.2, if_neg h0]
  · intro v hv
    rw [vv L hL0 v]
    by_cases h0 : v = 0
    · simp [h0]
    · rw [if_neg (not_le.mpr (lt_of_le_of_ne hv.1 (Ne.symm h0))), if_neg h0]
  · intro c hc
    rw [vc L hL0 c]
    by_cases h0 : c = 0
    · simp [h0]
    · rw [if_neg (not_le.mpr (lt_of_le_of_ne hc.1 (Ne.symm h0))), if_neg h0]
  · intro z hz
    rw [vc L hL0 (L - z), vv L hL0 z]
    rcases eq_or_lt_of_le hz.1 with h0 | h0
    · rw [← h0, if_neg (by linarith), if_neg (by linarith), if_pos le_rfl, EReal.coe_sub_bot]
    rcases eq_or_lt_of_le hz.2 with h1 | h1
    · rw [h1, sub_self, if_pos le_rfl, if_neg (not_le.mpr hL0), if_neg (lt_irrefl L),
        ← EReal.coe_sub, sub_self, EReal.coe_zero]
    · rw [if_neg (by linarith), if_pos (by linarith), if_neg (not_le.mpr h0), if_pos h1,
        ← EReal.coe_sub]
      congr 1; ring
