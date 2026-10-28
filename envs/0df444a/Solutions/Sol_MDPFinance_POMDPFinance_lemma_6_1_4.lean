-- Prove2me | solution 1 for MDPFinance.POMDPFinance.lemma_6_1_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T18:18:25.433447+00:00
-- url     : https://prove2.me/submissions/8324532b-7a4f-4b09-b0df-f36513f9d3a5

import Mathlib
import Definitions.Def_MDPFinance_POMDPFinance_Filter
import Definitions.Def_MDPFinance_POMDPFinance_Binomial
import Definitions.Def_MDPFinance_POMDPFinance_PowerLogValue

open MeasureTheory ProbabilityTheory

namespace S99P614
open MDPFinance.POMDPFinance

noncomputable def nu (q : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ioo (0:ℝ) 1)).withDensity fun θ => ENNReal.ofReal (q θ)

noncomputable def Lq (q : ℝ → ℝ) : ENNReal :=
  ∫⁻ θ in Set.Ioo (0:ℝ) 1, ENNReal.ofReal (q θ)

def G (q : ℝ → ℝ) : Prop :=
  Measurable q ∧ (∀ θ, 0 ≤ q θ) ∧ (∀ θ ∉ Set.Ioo (0:ℝ) 1, q θ = 0) ∧ 0 < Lq q ∧ Lq q < ⊤

lemma nu_univ (q : ℝ → ℝ) : nu q Set.univ = Lq q := by
  simp [nu, Lq, withDensity_apply _ MeasurableSet.univ]

lemma mOD_eq (q : ℝ → ℝ) : measureOfDensity q = (Lq q)⁻¹ • nu q := by
  unfold measureOfDensity MDPFinance.POMDPFinance.normalize; rw [← nu_univ]; rfl

lemma lintegral_mOD (q : ℝ → ℝ) (hq : Measurable q) (g : ℝ → ENNReal) (hg : Measurable g) :
    ∫⁻ y, g y ∂(measureOfDensity q) =
      (Lq q)⁻¹ * ∫⁻ y in Set.Ioo (0:ℝ) 1, ENNReal.ofReal (q y) * g y := by
  rw [mOD_eq, lintegral_smul_measure, nu, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hg]
  rfl

lemma G_child (q w : ℝ → ℝ) (hq : G q) (hw : Measurable w)
    (hw1 : ∀ θ ∈ Set.Ioo (0:ℝ) 1, 0 < w θ ∧ w θ ≤ 1) : G (fun θ => w θ * q θ) := by
  obtain ⟨hm, hn, hz, hpos, hfin⟩ := hq
  refine ⟨hw.mul hm, ?_, ?_, ?_, ?_⟩
  · intro θ
    by_cases h : θ ∈ Set.Ioo (0:ℝ) 1
    · exact mul_nonneg (hw1 θ h).1.le (hn θ)
    · simp [hz θ h]
  · intro θ h; simp [hz θ h]
  · rw [pos_iff_ne_zero]
    intro h0
    apply hpos.ne'
    unfold Lq at h0 ⊢
    rw [lintegral_eq_zero_iff (by fun_prop)] at h0 ⊢
    filter_upwards [ae_restrict_mem measurableSet_Ioo, h0] with x hx h
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at h ⊢
    have := (hw1 x hx).1
    nlinarith [hn x]
  · refine lt_of_le_of_lt ?_ hfin
    unfold Lq
    refine setLIntegral_mono (by fun_prop) fun x hx => ENNReal.ofReal_le_ofReal ?_
    have := hw1 x hx
    nlinarith [hn x]

lemma Phi_mOD (M : FilterMarket ℝ 1) (Fd : FilterOp M) (hQY : M.QY = Kernel.id)
    (z : Fin 1 → ℝ) (w : ℝ → ℝ) (hw : Measurable w)
    (hwz : ∀ θ ∈ Set.Ioo (0:ℝ) 1, M.qR θ z = w θ ∧ 0 < w θ ∧ w θ ≤ 1) (q : ℝ → ℝ) (hq : G q) :
    Fd.Phi (measureOfDensity q) z = measureOfDensity (fun θ => w θ * q θ) := by
  have hG := G_child q w hq hw fun θ h => (hwz θ h).2
  have hmR : Measurable fun y => M.qR y z :=
    M.hqR_meas.comp (measurable_id.prodMk measurable_const)
  have hden : ∫⁻ y, ENNReal.ofReal (M.qR y z) ∂(measureOfDensity q) =
      (Lq q)⁻¹ * Lq (fun θ => w θ * q θ) := by
    rw [lintegral_mOD q hq.1 _ (by fun_prop)]
    congr 1
    unfold Lq
    refine setLIntegral_congr_fun measurableSet_Ioo fun y hy => ?_
    simp only
    rw [(hwz y hy).1, ← ENNReal.ofReal_mul (hq.2.1 y), mul_comm]
  have hLq0 : (Lq q)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hq.2.2.2.2.ne
  have hLqT : (Lq q)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hq.2.2.2.1.ne'
  have hpos : 0 < ∫⁻ y, ENNReal.ofReal (M.qR y z) ∂(measureOfDensity q) := by
    rw [hden]; exact ENNReal.mul_pos hLq0 hG.2.2.2.1.ne'
  have hfin : ∫⁻ y, ENNReal.ofReal (M.qR y z) ∂(measureOfDensity q) < ⊤ := by
    rw [hden]; exact ENNReal.mul_lt_top hLqT.lt_top hG.2.2.2.2
  ext C hC
  rw [Fd.hPhi _ z hpos hfin C hC, hden, hQY]
  simp only [Kernel.id_apply, Measure.dirac_apply' _ hC]
  have hL := lintegral_mOD q hq.1 (fun y => ENNReal.ofReal (M.qR y z) * C.indicator 1 y)
    ((ENNReal.measurable_ofReal.comp hmR).mul (measurable_one.indicator hC))
  beta_reduce at hL
  rw [hL, ENNReal.mul_div_mul_left _ _ hLq0 hLqT]
  rw [mOD_eq, Measure.smul_apply, smul_eq_mul, nu, withDensity_apply _ hC, div_eq_mul_inv,
    mul_comm, ← lintegral_indicator hC]
  congr 1
  refine setLIntegral_congr_fun measurableSet_Ioo fun y hy => ?_
  rw [(hwz y hy).1]
  by_cases hyC : y ∈ C
  · simp [hyC, ENNReal.ofReal_mul (hwz y hy).2.1.le, mul_comm]
  · simp [hyC]


noncomputable def Pq (q : ℝ → ℝ) : ℝ := ∫ θ in Set.Ioo (0:ℝ) 1, q θ
noncomputable def Tq (q : ℝ → ℝ) : ℝ := ∫ θ in Set.Ioo (0:ℝ) 1, θ * q θ

lemma integrable_of_G (q : ℝ → ℝ) (hq : G q) :
    Integrable q (volume.restrict (Set.Ioo (0:ℝ) 1)) := by
  refine ⟨hq.1.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hq.2.1)]
  exact hq.2.2.2.2

lemma integrable_mul_of_G (q : ℝ → ℝ) (hq : G q) :
    Integrable (fun θ => θ * q θ) (volume.restrict (Set.Ioo (0:ℝ) 1)) := by
  refine (integrable_of_G q hq).mono' (measurable_id.mul hq.1).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hx.1, abs_of_nonneg (hq.2.1 x)]
  nlinarith [hx.2, hq.2.1 x]

lemma Pq_eq (q : ℝ → ℝ) (hq : G q) : Pq q = (Lq q).toReal := by
  unfold Pq Lq
  exact integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hq.2.1)
    hq.1.aestronglyMeasurable

lemma Pq_pos (q : ℝ → ℝ) (hq : G q) : 0 < Pq q := by
  rw [Pq_eq q hq]; exact ENNReal.toReal_pos hq.2.2.2.1.ne' hq.2.2.2.2.ne

lemma rhobar_eq (q : ℝ → ℝ) (hq : G q) : rhobar (measureOfDensity q) = Tq q / Pq q := by
  unfold rhobar
  rw [mOD_eq, integral_smul_measure, nu, integral_withDensity_eq_integral_toReal_smul
    (f := fun θ => ENNReal.ofReal (q θ)) hq.1.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) (fun x => x), Pq_eq q hq]
  simp only [ENNReal.toReal_ofReal (hq.2.1 _), smul_eq_mul, ENNReal.toReal_inv]
  unfold Tq
  simp_rw [mul_comm (q _)]
  rw [div_eq_inv_mul]

lemma rhobar_mem (q : ℝ → ℝ) (hq : G q) :
    0 ≤ rhobar (measureOfDensity q) ∧ rhobar (measureOfDensity q) ≤ 1 := by
  rw [rhobar_eq q hq]
  have hP := Pq_pos q hq
  have h0 : 0 ≤ Tq q := setIntegral_nonneg measurableSet_Ioo
    (fun x hx => mul_nonneg hx.1.le (hq.2.1 x))
  have h1 : Tq q ≤ Pq q := setIntegral_mono_on (integrable_mul_of_G q hq) (integrable_of_G q hq)
    measurableSet_Ioo (fun x hx => by nlinarith [hx.2, hq.2.1 x])
  exact ⟨div_nonneg h0 hP.le, (div_le_one hP).2 h1⟩

lemma LR_T (q q' : ℝ → ℝ) (hq : G q) (hq' : G q') (h : LikelihoodRatioOrder q q') :
    Tq q * Pq q' ≤ Tq q' * Pq q := by
  set μ := volume.restrict (Set.Ioo (0:ℝ) 1)
  have hI := integrable_of_G q hq
  have hI' := integrable_of_G q' hq'
  have hJ := integrable_mul_of_G q hq
  have hJ' := integrable_mul_of_G q' hq'
  have hnn : 0 ≤ ∫ x : ℝ × ℝ, (q x.1 * (x.2 * q' x.2) - (x.1 * q x.1) * q' x.2
      - q' x.1 * (x.2 * q x.2) + (x.1 * q' x.1) * q x.2) ∂(μ.prod μ) := by
    apply integral_nonneg
    intro x
    have e : (q x.1 * (x.2 * q' x.2) - (x.1 * q x.1) * q' x.2 - q' x.1 * (x.2 * q x.2)
        + (x.1 * q' x.1) * q x.2) = (x.2 - x.1) * (q x.1 * q' x.2 - q x.2 * q' x.1) := by ring
    simp only
    rw [e]
    rcases le_total x.1 x.2 with hle | hle
    · exact mul_nonneg (by linarith) (by linarith [h _ _ hle])
    · exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith [h _ _ hle])
  have i1 := hI.mul_prod hJ'
  have i2 := hJ.mul_prod hI'
  have i3 := hI'.mul_prod hJ
  have i4 := hJ'.mul_prod hI
  have e1 : ∫ z, q z.1 * (z.2 * q' z.2) ∂μ.prod μ = Pq q * Tq q' :=
    integral_prod_mul q (fun θ => θ * q' θ)
  have e2 : ∫ z, (z.1 * q z.1) * q' z.2 ∂μ.prod μ = Tq q * Pq q' :=
    integral_prod_mul (fun θ => θ * q θ) q'
  have e3 : ∫ z, q' z.1 * (z.2 * q z.2) ∂μ.prod μ = Pq q' * Tq q :=
    integral_prod_mul q' (fun θ => θ * q θ)
  have e4 : ∫ z, (z.1 * q' z.1) * q z.2 ∂μ.prod μ = Tq q' * Pq q :=
    integral_prod_mul (fun θ => θ * q' θ) q
  have E : ∫ x : ℝ × ℝ, (q x.1 * (x.2 * q' x.2) - (x.1 * q x.1) * q' x.2
      - q' x.1 * (x.2 * q x.2) + (x.1 * q' x.1) * q x.2) ∂(μ.prod μ) =
      Pq q * Tq q' - Tq q * Pq q' - Pq q' * Tq q + Tq q' * Pq q := by
    rw [integral_add, integral_sub, integral_sub, e1, e2, e3, e4]
    all_goals first | exact i1 | exact i2 | exact i3 | exact i4 | exact i1.sub i2 | exact (i1.sub i2).sub i3
  rw [E] at hnn
  nlinarith

lemma rhobar_mono (q q' : ℝ → ℝ) (hq : G q) (hq' : G q') (h : LikelihoodRatioOrder q q') :
    rhobar (measureOfDensity q) ≤ rhobar (measureOfDensity q') := by
  rw [rhobar_eq q hq, rhobar_eq q' hq', div_le_div_iff₀ (Pq_pos q hq) (Pq_pos q' hq')]
  exact LR_T q q' hq hq' h

lemma LR_mul (w q q' : ℝ → ℝ) (hw : ∀ θ ∈ Set.Ioo (0:ℝ) 1, 0 ≤ w θ)
    (hz : ∀ θ ∉ Set.Ioo (0:ℝ) 1, q θ = 0) (hz' : ∀ θ ∉ Set.Ioo (0:ℝ) 1, q' θ = 0)
    (h : LikelihoodRatioOrder q q') :
    LikelihoodRatioOrder (fun θ => w θ * q θ) (fun θ => w θ * q' θ) := by
  intro s t hst
  by_cases hs : s ∈ Set.Ioo (0:ℝ) 1
  · by_cases ht : t ∈ Set.Ioo (0:ℝ) 1
    · have := mul_le_mul_of_nonneg_left (h s t hst) (mul_nonneg (hw t ht) (hw s hs))
      simp only
      linarith [show w t * q t * (w s * q' s) = w t * w s * (q t * q' s) by ring,
        show w s * q s * (w t * q' t) = w t * w s * (q s * q' t) by ring]
    · simp [hz t ht, hz' t ht]
  · simp [hz s hs, hz' s hs]

lemma LR_ud (q : ℝ → ℝ) (hq : ∀ θ, 0 ≤ q θ) :
    LikelihoodRatioOrder (fun θ => (1 - θ) * q θ) (fun θ => θ * q θ) := by
  intro s t hst
  have := mul_nonneg (hq t) (hq s)
  have := mul_le_mul_of_nonneg_left (show (1 - t) * s ≤ (1 - s) * t by nlinarith) this
  simp only
  linarith [show (1 - t) * q t * (s * q s) = q t * q s * ((1 - t) * s) by ring,
    show (1 - s) * q s * (t * q t) = q t * q s * ((1 - s) * t) by ring]

lemma LR_smul (f g : ℝ → ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : LikelihoodRatioOrder f g) :
    LikelihoodRatioOrder (fun θ => a * f θ) (fun θ => b * g θ) := by
  intro s t hst
  have := mul_le_mul_of_nonneg_left (h s t hst) (mul_nonneg ha hb)
  simp only
  linarith [show a * f t * (b * g s) = a * b * (f t * g s) by ring,
    show a * f s * (b * g t) = a * b * (f s * g t) by ring]

/-! ### the recursion -/

lemma obj_cont (u dn i γ A B r : ℝ) (hγ : 0 < γ) :
    Continuous (binomialObjective u dn i γ A B r) := by
  unfold binomialObjective
  have h1 : Continuous fun α : ℝ => (1 + i + α * (u - 1 - i)) ^ γ :=
    (by fun_prop : Continuous fun α : ℝ => 1 + i + α * (u - 1 - i)).rpow_const
      fun _ => Or.inr hγ.le
  have h2 : Continuous fun α : ℝ => (1 + i + α * (dn - 1 - i)) ^ γ :=
    (by fun_prop : Continuous fun α : ℝ => 1 + i + α * (dn - 1 - i)).rpow_const
      fun _ => Or.inr hγ.le
  exact (continuous_const.mul h1).add (continuous_const.mul h2)

lemma obj_bdd (u dn i γ A B r : ℝ) (hγ : 0 < γ) :
    BddAbove (Set.range fun α : ℝ => ⨆ (_ : α ∈ Set.Icc (0:ℝ) 1),
      binomialObjective u dn i γ A B r α) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).bddAbove_image
    (obj_cont u dn i γ A B r hγ).continuousOn
  refine ⟨max C 0, ?_⟩
  rintro _ ⟨α, rfl⟩
  by_cases h : α ∈ Set.Icc (0:ℝ) 1
  · simp only [ciSup_pos h]
    exact le_max_of_le_left (hC ⟨α, h, rfl⟩)
  · haveI : IsEmpty (α ∈ Set.Icc (0:ℝ) 1) := ⟨h⟩
    dsimp only; rw [Real.iSup_of_isEmpty]; exact le_max_right _ _

lemma sup_mono (u dn i γ A B r A' B' r' : ℝ) (hγ : 0 < γ)
    (h : ∀ α ∈ Set.Icc (0:ℝ) 1, binomialObjective u dn i γ A B r α ≤
      binomialObjective u dn i γ A' B' r' α) :
    (⨆ α ∈ Set.Icc (0:ℝ) 1, binomialObjective u dn i γ A B r α) ≤
      ⨆ α ∈ Set.Icc (0:ℝ) 1, binomialObjective u dn i γ A' B' r' α := by
  refine ciSup_mono (obj_bdd u dn i γ A' B' r' hγ) fun α => ?_
  by_cases hα : α ∈ Set.Icc (0:ℝ) 1
  · simp only [ciSup_pos hα]; exact h α hα
  · haveI : IsEmpty (α ∈ Set.Icc (0:ℝ) 1) := ⟨hα⟩
    rw [Real.iSup_of_isEmpty, Real.iSup_of_isEmpty]

lemma dBin_nonneg (M : FilterMarket ℝ 1) (Fd : FilterOp M) (u dn i γ : ℝ) (hγ : 0 < γ)
    (hi : 0 < 1 + i) : ∀ k ρ, 0 ≤ dBin M Fd u dn i γ k ρ
  | 0, _ => by simp only [dBin]; positivity
  | k + 1, ρ => by
    simp only [dBin]
    refine mul_nonneg ?_ (Real.rpow_nonneg hi.le _)
    refine le_trans ?_ (le_ciSup (obj_bdd u dn i γ _ _ _ hγ) 2)
    haveI : IsEmpty ((2:ℝ) ∈ Set.Icc (0:ℝ) 1) := ⟨fun h => by norm_num at h⟩
    rw [Real.iSup_of_isEmpty]

lemma obj_mono (u dn i γ : ℝ) (hdn : 0 < dn) (hd : dn < 1 + i) (hi : 1 + i < u) (hγ : 0 < γ)
    (A B r A' B' r' α : ℝ) (hα : α ∈ Set.Icc (0:ℝ) 1) (hr : 0 ≤ r) (hrr : r ≤ r') (hr1 : r' ≤ 1)
    (hA : A ≤ A') (hB : B ≤ B') (hB0 : 0 ≤ B') (hBA : B' ≤ A') :
    binomialObjective u dn i γ A B r α ≤ binomialObjective u dn i γ A' B' r' α := by
  unfold binomialObjective
  have hY0 : 0 < 1 + i + α * (dn - 1 - i) := by nlinarith [hα.1, hα.2]
  have hXY : 1 + i + α * (dn - 1 - i) ≤ 1 + i + α * (u - 1 - i) := by nlinarith [hα.1]
  set X := (1 + i + α * (u - 1 - i)) ^ γ
  set Y := (1 + i + α * (dn - 1 - i)) ^ γ
  have hY : 0 ≤ Y := Real.rpow_nonneg hY0.le _
  have hXYr : Y ≤ X := Real.rpow_le_rpow hY0.le hXY hγ.le
  have h1 : r * A * X ≤ r * A' * X := by
    have := mul_le_mul_of_nonneg_left hA (mul_nonneg hr (hY.trans hXYr)); nlinarith
  have h2 : (1 - r) * B * Y ≤ (1 - r) * B' * Y := by
    have := mul_le_mul_of_nonneg_left hB (mul_nonneg (by linarith : (0:ℝ) ≤ 1 - r) hY)
    nlinarith
  have h3 : 0 ≤ A' * X - B' * Y := by
    have := mul_le_mul_of_nonneg_left hXYr hB0
    have := mul_le_mul_of_nonneg_right hBA (hY.trans hXYr)
    linarith
  have h4 := mul_nonneg (sub_nonneg.2 hrr) h3
  nlinarith

theorem main (M : FilterMarket ℝ 1) (Fd : FilterOp M) (u dn i : ℝ) (hdn : 0 < dn)
    (hd : dn < 1 + i) (hi : 1 + i < u) (hM : IsBinomialMarket M u dn i) (γ : ℝ) (hγ0 : 0 < γ) :
    ∀ (k : ℕ) (p p' : ℝ → ℝ), G p → G p' → LikelihoodRatioOrder p p' →
      dBin M Fd u dn i γ k (measureOfDensity p) ≤ dBin M Fd u dn i γ k (measureOfDensity p') := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _; rw [dBin, dBin]
  | succ k ih =>
    intro p p' hp hp' h
    have hwu : ∀ θ ∈ Set.Ioo (0:ℝ) 1, 0 < θ ∧ θ ≤ 1 := fun θ hθ => ⟨hθ.1, hθ.2.le⟩
    have hwd : ∀ θ ∈ Set.Ioo (0:ℝ) 1, 0 < 1 - θ ∧ 1 - θ ≤ 1 :=
      fun θ hθ => ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
    have hU : ∀ q, G q → Fd.Phi (measureOfDensity q) (ubar u i) =
        measureOfDensity (fun θ => θ * q θ) := fun q hq =>
      Phi_mOD M Fd hM.2.2 (ubar u i) (fun θ => θ) measurable_id
        (fun θ hθ => ⟨(hM.2.1 θ hθ).1, hwu θ hθ⟩) q hq
    have hD : ∀ q, G q → Fd.Phi (measureOfDensity q) (dbar dn i) =
        measureOfDensity (fun θ => (1 - θ) * q θ) := fun q hq =>
      Phi_mOD M Fd hM.2.2 (dbar dn i) (fun θ => 1 - θ) (by fun_prop)
        (fun θ hθ => ⟨(hM.2.1 θ hθ).2, hwd θ hθ⟩) q hq
    have gu := fun q (hq : G q) => G_child q (fun θ => θ) hq measurable_id hwu
    have gd := fun q (hq : G q) => G_child q (fun θ => 1 - θ) hq (by fun_prop) hwd
    have IA := ih _ _ (gu p hp) (gu p' hp')
      (LR_mul (fun θ => θ) p p' (fun θ hθ => hθ.1.le) hp.2.2.1 hp'.2.2.1 h)
    have IB := ih _ _ (gd p hp) (gd p' hp')
      (LR_mul (fun θ => 1 - θ) p p' (fun θ hθ => (hwd θ hθ).1.le) hp.2.2.1 hp'.2.2.1 h)
    have IBA := ih _ _ (gd p' hp') (gu p' hp')
      (LR_ud p' hp'.2.1)
    simp only [dBin]
    rw [hU p hp, hU p' hp', hD p hp, hD p' hp']
    refine mul_le_mul_of_nonneg_right (sup_mono u dn i γ _ _ _ _ _ _ hγ0 fun α hα =>
      obj_mono u dn i γ hdn hd hi hγ0 _ _ _ _ _ _ α hα (rhobar_mem p hp).1
        (rhobar_mono p p' hp hp' h) (rhobar_mem p' hp').2 IA IB
        (dBin_nonneg M Fd u dn i γ hγ0 (by linarith) _ _) IBA)
      (Real.rpow_nonneg (by linarith) _)

/-! ### final assembly -/

noncomputable def R (q : ℝ → ℝ) : ℝ → ℝ := Set.indicator (Set.Ioo (0:ℝ) 1) q

lemma mOD_R (q : ℝ → ℝ) : measureOfDensity (R q) = measureOfDensity q := by
  unfold measureOfDensity
  congr 1
  refine withDensity_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  simp [R, hx]

lemma LR_R (q q' : ℝ → ℝ) (h : LikelihoodRatioOrder q q') : LikelihoodRatioOrder (R q) (R q') := by
  intro s t hst
  by_cases hs : s ∈ Set.Ioo (0:ℝ) 1
  · by_cases ht : t ∈ Set.Ioo (0:ℝ) 1
    · simp only [R, Set.indicator_of_mem hs, Set.indicator_of_mem ht]; exact h s t hst
    · simp [R, Set.indicator_of_notMem ht]
  · simp [R, Set.indicator_of_notMem hs]

lemma G_prior (p0 : ℝ → ℝ) (hp0 : IsPriorDensity p0) : G (R p0) := by
  obtain ⟨hm, hn, h1⟩ := hp0
  have hL : Lq (R p0) = 1 := by
    rw [← h1]; unfold Lq
    refine setLIntegral_congr_fun measurableSet_Ioo fun y hy => ?_
    simp [R, hy]
  refine ⟨hm.indicator measurableSet_Ioo, fun θ => ?_, fun θ hθ => ?_, ?_, ?_⟩
  · unfold R; by_cases h : θ ∈ Set.Ioo (0:ℝ) 1
    · rw [Set.indicator_of_mem h]; exact hn θ
    · rw [Set.indicator_of_notMem h]
  · unfold R; rw [Set.indicator_of_notMem hθ]
  · rw [hL]; exact one_pos
  · rw [hL]; exact ENNReal.one_lt_top

lemma R_post (p0 : ℝ → ℝ) (m n : ℕ) :
    R (binomialPosteriorDensity p0 m n) = fun θ => (θ ^ m * (1 - θ) ^ (n - m)) * R p0 θ := by
  funext θ
  unfold R binomialPosteriorDensity
  by_cases h : θ ∈ Set.Ioo (0:ℝ) 1
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_notMem h]

lemma G_post (p0 : ℝ → ℝ) (hp0 : IsPriorDensity p0) (m n : ℕ) :
    G (R (binomialPosteriorDensity p0 m n)) := by
  rw [R_post]
  refine G_child _ _ (G_prior p0 hp0) (by fun_prop) fun θ hθ => ⟨?_, ?_⟩
  · have : 0 < 1 - θ := by linarith [hθ.2]
    have := hθ.1
    positivity
  · exact mul_le_one₀ (pow_le_one₀ hθ.1.le hθ.2.le)
      (pow_nonneg (by linarith [hθ.2]) _) (pow_le_one₀ (by linarith [hθ.2]) (by linarith [hθ.1]))

lemma mOD_wd (q : ℝ → ℝ) (hq : G q) :
    measureOfDensity q = (volume.restrict (Set.Ioo (0:ℝ) 1)).withDensity
      (fun θ => ENNReal.ofReal ((Lq q)⁻¹.toReal * q θ)) := by
  have hT : (Lq q)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hq.2.2.2.1.ne'
  rw [mOD_eq, nu, ← withDensity_smul' _ _ hT]
  congr 1
  funext θ
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hT]

end S99P614

open MDPFinance.POMDPFinance S99P614 in
theorem solution (M : FilterMarket ℝ 1) (Fd : FilterOp M) (u dn i : ℝ) (hdn : 0 < dn)
    (hd : dn < 1 + i) (hi : 1 + i < u) (hM : IsBinomialMarket M u dn i) (γ : ℝ) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (p0 : ℝ → ℝ) (hp0 : IsPriorDensity p0) (m n : ℕ) (hmn : m ≤ n) :
    LRMeasure (volume.restrict (Set.Ioo (0 : ℝ) 1))
        (Fd.Phi (measureOfDensity (binomialPosteriorDensity p0 m n)) (dbar dn i))
        (Fd.Phi (measureOfDensity (binomialPosteriorDensity p0 m n)) (ubar u i)) ∧
      (∀ p p' : ℝ → ℝ, p ∈ DQ0 p0 → p' ∈ DQ0 p0 → LikelihoodRatioOrder p p' →
        ∀ k : ℕ, dBin M Fd u dn i γ k (measureOfDensity p) ≤
          dBin M Fd u dn i γ k (measureOfDensity p')) := by
  refine ⟨?_, ?_⟩
  · set b := R (binomialPosteriorDensity p0 m n) with hb
    have hG : G b := G_post p0 hp0 m n
    have hwu : ∀ θ ∈ Set.Ioo (0:ℝ) 1, 0 < θ ∧ θ ≤ 1 := fun θ hθ => ⟨hθ.1, hθ.2.le⟩
    have hwd : ∀ θ ∈ Set.Ioo (0:ℝ) 1, 0 < 1 - θ ∧ 1 - θ ≤ 1 :=
      fun θ hθ => ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
    have gu := G_child b (fun θ => θ) hG measurable_id hwu
    have gd := G_child b (fun θ => 1 - θ) hG (by fun_prop) hwd
    rw [← mOD_R, ← hb,
      Phi_mOD M Fd hM.2.2 (ubar u i) (fun θ => θ) measurable_id
        (fun θ hθ => ⟨(hM.2.1 θ hθ).1, hwu θ hθ⟩) b hG,
      Phi_mOD M Fd hM.2.2 (dbar dn i) (fun θ => 1 - θ) (by fun_prop)
        (fun θ hθ => ⟨(hM.2.1 θ hθ).2, hwd θ hθ⟩) b hG, mOD_wd _ gu, mOD_wd _ gd]
    exact ⟨_, _, measurable_const.mul gd.1, measurable_const.mul gu.1,
      fun θ => mul_nonneg ENNReal.toReal_nonneg (gd.2.1 θ),
      fun θ => mul_nonneg ENNReal.toReal_nonneg (gu.2.1 θ), rfl, rfl,
      LR_smul _ _ _ _ ENNReal.toReal_nonneg ENNReal.toReal_nonneg (LR_ud b hG.2.1)⟩
  · rintro p p' ⟨m1, n1, -, rfl⟩ ⟨m2, n2, -, rfl⟩ h k
    rw [← mOD_R, ← mOD_R (binomialPosteriorDensity p0 m2 n2)]
    exact main M Fd u dn i hdn hd hi hM γ hγ0 k _ _ (G_post p0 hp0 m1 n1) (G_post p0 hp0 m2 n2)
      (LR_R _ _ h)
