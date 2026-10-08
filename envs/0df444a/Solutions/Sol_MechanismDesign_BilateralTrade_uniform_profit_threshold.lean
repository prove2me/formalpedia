-- Prove2me | solution 1 for MechanismDesign.BilateralTrade.uniform_profit_threshold
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-07T08:38:59.284165+00:00
-- url     : https://prove2.me/submissions/192646bd-b902-49c2-88f5-901647e9f8b4

import Mathlib
import Definitions.Def_MechanismDesign_BilateralTrade_Model

open MeasureTheory


namespace MechanismDesign.BilateralTrade
open Set Filter Topology

noncomputable def msMuS (E : Environment) : Measure ℝ :=
  (volume.restrict (Icc E.loS E.hiS)).withDensity (fun x => ENNReal.ofReal (E.fS x))
noncomputable def msMuB (E : Environment) : Measure ℝ :=
  (volume.restrict (Icc E.loB E.hiB)).withDensity (fun x => ENNReal.ofReal (E.fB x))

lemma ms_prior_eq (E : Environment) : E.prior = (msMuS E).prod (msMuB E) := by
  unfold msMuS msMuB Environment.prior Environment.typeSpace
  rw [prod_withDensity E.fS_measurable.ennreal_ofReal E.fB_measurable.ennreal_ofReal,
    Measure.prod_restrict, ← Measure.volume_eq_prod]
  refine withDensity_congr_ae ?_
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with θ hθ
  rw [ENNReal.ofReal_mul (E.fS_pos _ hθ.1).le]

lemma ms_muS_univ (E : Environment) : msMuS E univ = 1 := by
  rw [msMuS, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le E.loS_lt_hiS.le,
      E.fS_integral]; simp
  · exact (integrableOn_Icc_iff_integrableOn_Ioc (f := E.fS)).mpr
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le E.loS_lt_hiS.le).mp E.fS_intervalIntegrable)
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx using (E.fS_pos x hx).le

lemma ms_muB_univ (E : Environment) : msMuB E univ = 1 := by
  rw [msMuB, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le E.loB_lt_hiB.le,
      E.fB_integral]; simp
  · exact (integrableOn_Icc_iff_integrableOn_Ioc (f := E.fB)).mpr
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le E.loB_lt_hiB.le).mp E.fB_intervalIntegrable)
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx using (E.fB_pos x hx).le

instance ms_probS (E : Environment) : IsProbabilityMeasure (msMuS E) := ⟨ms_muS_univ E⟩
instance ms_probB (E : Environment) : IsProbabilityMeasure (msMuB E) := ⟨ms_muB_univ E⟩
instance ms_probP (E : Environment) : IsFiniteMeasure E.prior := by
  rw [ms_prior_eq]; infer_instance

lemma ms_integral_muS (E : Environment) (h : ℝ → ℝ) :
    ∫ x, h x ∂msMuS E = ∫ x in E.loS..E.hiS, h x * E.fS x := by
  have : (fun x => ENNReal.ofReal (E.fS x)) =
      fun x => ((Real.toNNReal (E.fS x) : NNReal) : ENNReal) := rfl
  rw [msMuS, this, integral_withDensity_eq_integral_smul E.fS_measurable.real_toNNReal,
    intervalIntegral.integral_of_le E.loS_lt_hiS.le, ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc (fun x hx => ?_)
  simp [NNReal.smul_def, Real.coe_toNNReal _ (E.fS_pos x hx).le, mul_comm]

lemma ms_integral_muB (E : Environment) (h : ℝ → ℝ) :
    ∫ x, h x ∂msMuB E = ∫ x in E.loB..E.hiB, h x * E.fB x := by
  have : (fun x => ENNReal.ofReal (E.fB x)) =
      fun x => ((Real.toNNReal (E.fB x) : NNReal) : ENNReal) := rfl
  rw [msMuB, this, integral_withDensity_eq_integral_smul E.fB_measurable.real_toNNReal,
    intervalIntegral.integral_of_le E.loB_lt_hiB.le, ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc (fun x hx => ?_)
  simp [NNReal.smul_def, Real.coe_toNNReal _ (E.fB_pos x hx).le, mul_comm]

lemma ms_ae_muS (E : Environment) : ∀ᵐ x ∂msMuS E, x ∈ Icc E.loS E.hiS :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Icc)
lemma ms_ae_muB (E : Environment) : ∀ᵐ x ∂msMuB E, x ∈ Icc E.loB E.hiB :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Icc)
lemma ms_ae_prior (E : Environment) : ∀ᵐ θ ∂E.prior, θ ∈ E.typeSpace :=
  (withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc))

lemma ms_int_bdd (E : Environment) {f : ℝ × ℝ → ℝ} (hf : Measurable f) (C : ℝ)
    (hC : ∀ θ ∈ E.typeSpace, |f θ| ≤ C) : Integrable f E.prior := by
  refine Integrable.of_bound hf.aestronglyMeasurable C ?_
  filter_upwards [ms_ae_prior E] with θ hθ
  simpa [Real.norm_eq_abs] using hC θ hθ

lemma ms_ii_bdd {g w : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hg : Measurable g) (C : ℝ)
    (hC : ∀ x ∈ Icc a b, |g x| ≤ C) (hw : IntervalIntegrable w volume a b) :
    IntervalIntegrable (fun x => g x * w x) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab] at hw ⊢
  refine Integrable.bdd_mul hw hg.aestronglyMeasurable (c := C) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  simpa using hC x (Ioc_subset_Icc_self hx)

lemma ms_fb_cases {E : Environment} {q : ℝ × ℝ → ℝ} (hq : IsFirstBestRule E q) {θ : ℝ × ℝ}
    (hθ : θ ∈ E.typeSpace) : (q θ = 1 ∧ θ.1 ≤ θ.2) ∨ (q θ = 0 ∧ θ.2 ≤ θ.1) := by
  obtain ⟨h01, h1, h2⟩ := hq θ hθ
  rcases h01 with h | h
  · right; refine ⟨h, le_of_not_gt fun hlt => ?_⟩
    have := h1 hlt; rw [h] at this; norm_num at this
  · left; refine ⟨h, le_of_not_gt fun hlt => ?_⟩
    have := h2 hlt; rw [h] at this; norm_num at this

lemma ms_fb_le {E : Environment} {q : ℝ × ℝ → ℝ} (hq : IsFirstBestRule E q) {θ θ' : ℝ × ℝ}
    (hθ : θ ∈ E.typeSpace) (hθ' : θ' ∈ E.typeSpace) :
    q θ' * (θ.2 - θ.1) ≤ q θ * (θ.2 - θ.1) := by
  rcases ms_fb_cases hq hθ with ⟨h, h'⟩ | ⟨h, h'⟩ <;>
  rcases (hq θ' hθ').1 with h2 | h2 <;> rw [h, h2] <;> nlinarith

lemma ms_q_abs {E : Environment} (m : DirectMechanism E) {θ : ℝ × ℝ} (hθ : θ ∈ E.typeSpace) :
    |m.q θ| ≤ 1 := by
  rcases m.q_mem θ hθ with h | h <;> rw [h] <;> norm_num

lemma ms_qsecS {E : Environment} (m : DirectMechanism E) (hqm : Measurable m.q) {x : ℝ}
    (hx : x ∈ Icc E.loS E.hiS) :
    IntervalIntegrable (fun y => m.q (x, y) * E.fB y) volume E.loB E.hiB :=
  ms_ii_bdd E.loB_lt_hiB.le (hqm.comp measurable_prodMk_left) 1
    (fun y hy => ms_q_abs m ⟨hx, hy⟩) E.fB_intervalIntegrable

lemma ms_qsecB {E : Environment} (m : DirectMechanism E) (hqm : Measurable m.q) {y : ℝ}
    (hy : y ∈ Icc E.loB E.hiB) :
    IntervalIntegrable (fun x => m.q (x, y) * E.fS x) volume E.loS E.hiS :=
  ms_ii_bdd E.loS_lt_hiS.le (hqm.comp measurable_prodMk_right) 1
    (fun x hx => ms_q_abs m ⟨hx, hy⟩) E.fS_intervalIntegrable

/-- seller's interim payoff from reporting `x'` with type `x`, as one integral -/
lemma ms_sellerU {E : Environment} (m : DirectMechanism E) {x' : ℝ} (x : ℝ)
    (hq : IntervalIntegrable (fun y => m.q (x', y) * E.fB y) volume E.loB E.hiB)
    (ht : IntervalIntegrable (fun y => m.tS (x', y) * E.fB y) volume E.loB E.hiB) :
    m.TS x' + (1 - m.QS x') * x =
      ∫ y in E.loB..E.hiB, (m.tS (x', y) + (1 - m.q (x', y)) * x) * E.fB y := by
  have e : (fun y => (m.tS (x', y) + (1 - m.q (x', y)) * x) * E.fB y) =
      fun y => m.tS (x', y) * E.fB y + (x * E.fB y - x * (m.q (x', y) * E.fB y)) := by
    ext y; ring
  rw [e, intervalIntegral.integral_add ht ((E.fB_intervalIntegrable.const_mul x).sub
    (hq.const_mul x)), intervalIntegral.integral_sub (E.fB_intervalIntegrable.const_mul x)
    (hq.const_mul x), intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    E.fB_integral]
  unfold DirectMechanism.TS DirectMechanism.QS; ring

lemma ms_buyerU {E : Environment} (m : DirectMechanism E) {y' : ℝ} (y : ℝ)
    (hq : IntervalIntegrable (fun x => m.q (x, y') * E.fS x) volume E.loS E.hiS)
    (ht : IntervalIntegrable (fun x => m.tB (x, y') * E.fS x) volume E.loS E.hiS) :
    m.QB y' * y - m.TB y' =
      ∫ x in E.loS..E.hiS, (m.q (x, y') * y - m.tB (x, y')) * E.fS x := by
  have e : (fun x => (m.q (x, y') * y - m.tB (x, y')) * E.fS x) =
      fun x => y * (m.q (x, y') * E.fS x) - m.tB (x, y') * E.fS x := by
    ext x; ring
  rw [e, intervalIntegral.integral_sub (hq.const_mul y) ht, intervalIntegral.integral_const_mul]
  unfold DirectMechanism.TB DirectMechanism.QB; ring

lemma ms_constS (E : Environment) (c : ℝ) : ∫ y in E.loB..E.hiB, c * E.fB y = c := by
  rw [intervalIntegral.integral_const_mul, E.fB_integral, mul_one]
lemma ms_constB (E : Environment) (c : ℝ) : ∫ x in E.loS..E.hiS, c * E.fS x = c := by
  rw [intervalIntegral.integral_const_mul, E.fS_integral, mul_one]


lemma ms_sellerU_ii {E : Environment} (m : DirectMechanism E) {x' : ℝ} (x : ℝ)
    (hq : IntervalIntegrable (fun y => m.q (x', y) * E.fB y) volume E.loB E.hiB)
    (ht : IntervalIntegrable (fun y => m.tS (x', y) * E.fB y) volume E.loB E.hiB) :
    IntervalIntegrable (fun y => (m.tS (x', y) + (1 - m.q (x', y)) * x) * E.fB y)
      volume E.loB E.hiB := by
  have e : (fun y => (m.tS (x', y) + (1 - m.q (x', y)) * x) * E.fB y) =
      fun y => m.tS (x', y) * E.fB y + (x * E.fB y - x * (m.q (x', y) * E.fB y)) := by
    ext y; ring
  rw [e]; exact ht.add ((E.fB_intervalIntegrable.const_mul x).sub (hq.const_mul x))

lemma ms_buyerU_ii {E : Environment} (m : DirectMechanism E) {y' : ℝ} (y : ℝ)
    (hq : IntervalIntegrable (fun x => m.q (x, y') * E.fS x) volume E.loS E.hiS)
    (ht : IntervalIntegrable (fun x => m.tB (x, y') * E.fS x) volume E.loS E.hiS) :
    IntervalIntegrable (fun x => (m.q (x, y') * y - m.tB (x, y')) * E.fS x)
      volume E.loS E.hiS := by
  have e : (fun x => (m.q (x, y') * y - m.tB (x, y')) * E.fS x) =
      fun x => y * (m.q (x, y') * E.fS x) - m.tB (x, y') * E.fS x := by
    ext x; ring
  rw [e]; exact (hq.const_mul y).sub ht

lemma ms_abs_aux {q q2 a b A B : ℝ} (hq : q = 0 ∨ q = 1) (hq2 : q2 = 0 ∨ q2 = 1)
    (ha : |a| ≤ A) (hb : |b| ≤ B) : |q2 * a + (q - q2) * b| ≤ A + B := by
  have ha' := abs_le.mp ha; have hb' := abs_le.mp hb
  rw [abs_le]
  rcases hq with h | h <;> rcases hq2 with h2 | h2 <;> subst h h2 <;> constructor <;> linarith

lemma ms_abs_mem {u a b : ℝ} (h : u ∈ Icc a b) : |u| ≤ |a| + |b| := by
  rw [abs_le]; have := neg_abs_le a; have := le_abs_self b; have := abs_nonneg a
  have := abs_nonneg b; constructor <;> linarith [h.1, h.2]

lemma ms_piv_tS_abs {E : Environment} {q : ℝ × ℝ → ℝ} (hq : IsFirstBestRule E q) {θ : ℝ × ℝ}
    (hθ : θ ∈ E.typeSpace) : |(pivot E q hq).tS θ| ≤ |E.hiS| + (|E.loB| + |E.hiB|) := by
  simp only [pivot]
  exact ms_abs_aux (hq θ hθ).1 (hq (E.hiS, θ.2) ⟨⟨E.loS_lt_hiS.le, le_rfl⟩, hθ.2⟩).1 le_rfl
    (ms_abs_mem hθ.2)

lemma ms_piv_tB_abs {E : Environment} {q : ℝ × ℝ → ℝ} (hq : IsFirstBestRule E q) {θ : ℝ × ℝ}
    (hθ : θ ∈ E.typeSpace) : |(pivot E q hq).tB θ| ≤ |E.loB| + (|E.loS| + |E.hiS|) := by
  simp only [pivot]
  exact ms_abs_aux (hq θ hθ).1 (hq (θ.1, E.loB) ⟨hθ.1, ⟨le_rfl, E.loB_lt_hiB.le⟩⟩).1 le_rfl
    (ms_abs_mem hθ.1)

lemma ms_piv_tS_meas {E : Environment} {q : ℝ × ℝ → ℝ} (hq : IsFirstBestRule E q)
    (hqm : Measurable q) : Measurable (pivot E q hq).tS := by
  simp only [pivot]; fun_prop

lemma ms_piv_tB_meas {E : Environment} {q : ℝ × ℝ → ℝ} (hq : IsFirstBestRule E q)
    (hqm : Measurable q) : Measurable (pivot E q hq).tB := by
  simp only [pivot]; fun_prop

lemma ms_piv_wd {E : Environment} {q : ℝ × ℝ → ℝ} (hq : IsFirstBestRule E q)
    (hqm : Measurable q) : (pivot E q hq).WellDefined where
  q_measurable := hqm
  tS_measurable := ms_piv_tS_meas hq hqm
  tB_measurable := ms_piv_tB_meas hq hqm
  tS_integrable := ms_int_bdd E (ms_piv_tS_meas hq hqm) _ (fun θ hθ => ms_piv_tS_abs hq hθ)
  tB_integrable := ms_int_bdd E (ms_piv_tB_meas hq hqm) _ (fun θ hθ => ms_piv_tB_abs hq hθ)
  tS_section := fun x hx => ms_ii_bdd E.loB_lt_hiB.le
    ((ms_piv_tS_meas hq hqm).comp measurable_prodMk_left) _
    (fun y hy => ms_piv_tS_abs hq (θ := (x, y)) ⟨hx, hy⟩) E.fB_intervalIntegrable
  tB_section := fun y hy => ms_ii_bdd E.loS_lt_hiS.le
    ((ms_piv_tB_meas hq hqm).comp measurable_prodMk_right) _
    (fun x hx => ms_piv_tB_abs hq (θ := (x, y)) ⟨hx, hy⟩) E.fS_intervalIntegrable

lemma ms_piv_adm {E : Environment} {q : ℝ × ℝ → ℝ} (hq : IsFirstBestRule E q)
    (hqm : Measurable q) : (pivot E q hq).Admissible := by
  have hwd := ms_piv_wd hq hqm
  set m := pivot E q hq with hm
  have qS : ∀ x ∈ Icc E.loS E.hiS, IntervalIntegrable (fun y => m.q (x, y) * E.fB y)
      volume E.loB E.hiB := fun x hx => ms_qsecS m hqm hx
  have qB : ∀ y ∈ Icc E.loB E.hiB, IntervalIntegrable (fun x => m.q (x, y) * E.fS x)
      volume E.loS E.hiS := fun y hy => ms_qsecB m hqm hy
  have mS : (E.hiS, 0).1 ∈ Icc E.loS E.hiS := ⟨E.loS_lt_hiS.le, le_rfl⟩
  have mB : (0, E.loB).2 ∈ Icc E.loB E.hiB := ⟨le_rfl, E.loB_lt_hiB.le⟩
  refine ⟨hwd, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro x hx x' hx'
    rw [ms_sellerU m x (qS x' hx') (hwd.tS_section x' hx'),
      ms_sellerU m x (qS x hx) (hwd.tS_section x hx)]
    refine intervalIntegral.integral_mono_on E.loB_lt_hiB.le
      (ms_sellerU_ii m x (qS x' hx') (hwd.tS_section x' hx'))
      (ms_sellerU_ii m x (qS x hx) (hwd.tS_section x hx)) (fun y hy => ?_)
    refine mul_le_mul_of_nonneg_right ?_ (E.fB_pos y hy).le
    have := ms_fb_le hq (θ := (x, y)) (θ' := (x', y)) ⟨hx, hy⟩ ⟨hx', hy⟩
    simp only [hm, pivot] at this ⊢
    linear_combination this
  · intro y hy y' hy'
    rw [ms_buyerU m y (qB y' hy') (hwd.tB_section y' hy'),
      ms_buyerU m y (qB y hy) (hwd.tB_section y hy)]
    refine intervalIntegral.integral_mono_on E.loS_lt_hiS.le
      (ms_buyerU_ii m y (qB y' hy') (hwd.tB_section y' hy'))
      (ms_buyerU_ii m y (qB y hy) (hwd.tB_section y hy)) (fun x hx => ?_)
    refine mul_le_mul_of_nonneg_right ?_ (E.fS_pos x hx).le
    have := ms_fb_le hq (θ := (x, y)) (θ' := (x, y')) ⟨hx, hy⟩ ⟨hx, hy'⟩
    simp only [hm, pivot] at this ⊢
    linear_combination this
  · intro x hx
    unfold DirectMechanism.US
    rw [ms_sellerU m x (qS x hx) (hwd.tS_section x hx)]
    calc x = ∫ y in E.loB..E.hiB, x * E.fB y := (ms_constS E x).symm
      _ ≤ _ := by
        refine intervalIntegral.integral_mono_on E.loB_lt_hiB.le
          (E.fB_intervalIntegrable.const_mul x)
          (ms_sellerU_ii m x (qS x hx) (hwd.tS_section x hx)) (fun y hy => ?_)
        refine mul_le_mul_of_nonneg_right ?_ (E.fB_pos y hy).le
        have := ms_fb_le hq (θ := (x, y)) (θ' := (E.hiS, y)) ⟨hx, hy⟩ ⟨mS, hy⟩
        have h0 : 0 ≤ q (E.hiS, y) := by
          rcases (hq (E.hiS, y) ⟨mS, hy⟩).1 with h | h <;> rw [h] <;> norm_num
        simp only [hm, pivot] at this ⊢
        nlinarith [mul_nonneg h0 (sub_nonneg.mpr hx.2)]
  · intro y hy
    unfold DirectMechanism.UB
    rw [ms_buyerU m y (qB y hy) (hwd.tB_section y hy)]
    refine intervalIntegral.integral_nonneg E.loS_lt_hiS.le (fun x hx => ?_)
    refine mul_nonneg ?_ (E.fS_pos x hx).le
    have := ms_fb_le hq (θ := (x, y)) (θ' := (x, E.loB)) ⟨hx, hy⟩ ⟨hx, mB⟩
    have h0 : 0 ≤ q (x, E.loB) := by
      rcases (hq (x, E.loB) ⟨hx, mB⟩).1 with h | h <;> rw [h] <;> norm_num
    simp only [hm, pivot] at this ⊢
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr hy.1)]


lemma ms_muS_pos (E : Environment) {a b : ℝ} (hab : a < b) (hsub : Ioo a b ⊆ Icc E.loS E.hiS) :
    0 < msMuS E (Ioo a b) := by
  rw [msMuS, withDensity_apply _ measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
    inter_eq_left.mpr hsub, lintegral_pos_iff_support E.fS_measurable.ennreal_ofReal,
    Measure.restrict_apply' measurableSet_Ioo]
  rw [inter_eq_right.mpr (fun x hx => by
    simpa [Function.mem_support, ENNReal.ofReal_eq_zero, not_le] using E.fS_pos x (hsub hx))]
  simpa using hab

lemma ms_muB_pos (E : Environment) {a b : ℝ} (hab : a < b) (hsub : Ioo a b ⊆ Icc E.loB E.hiB) :
    0 < msMuB E (Ioo a b) := by
  rw [msMuB, withDensity_apply _ measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
    inter_eq_left.mpr hsub, lintegral_pos_iff_support E.fB_measurable.ennreal_ofReal,
    Measure.restrict_apply' measurableSet_Ioo]
  rw [inter_eq_right.mpr (fun x hx => by
    simpa [Function.mem_support, ENNReal.ofReal_eq_zero, not_le] using E.fB_pos x (hsub hx))]
  simpa using hab

lemma ms_piv_def {E : Environment} {q : ℝ × ℝ → ℝ} (hq : IsFirstBestRule E q)
    (hqm : Measurable q) (hB : E.loB < E.hiS) (hS : E.loS < E.hiB) :
    (pivot E q hq).expectedSurplus < 0 := by
  have hwd := ms_piv_wd hq hqm
  set f : ℝ × ℝ → ℝ := fun θ => (pivot E q hq).tS θ - (pivot E q hq).tB θ with hf
  have hint : Integrable f E.prior := hwd.tS_integrable.sub hwd.tB_integrable
  have mS : E.hiS ∈ Icc E.loS E.hiS := ⟨E.loS_lt_hiS.le, le_rfl⟩
  have mB : E.loB ∈ Icc E.loB E.hiB := ⟨le_rfl, E.loB_lt_hiB.le⟩
  have hnn : 0 ≤ᵐ[E.prior] f := by
    filter_upwards [ms_ae_prior E] with θ hθ
    obtain ⟨x, y⟩ := θ
    have hx : x ∈ Icc E.loS E.hiS := hθ.1
    have hy : y ∈ Icc E.loB E.hiB := hθ.2
    rcases ms_fb_cases hq (θ := (x, y)) hθ with ⟨h1, i1⟩ | ⟨h1, i1⟩ <;>
    rcases ms_fb_cases hq (θ := (E.hiS, y)) ⟨mS, hy⟩ with ⟨h2, i2⟩ | ⟨h2, i2⟩ <;>
    rcases ms_fb_cases hq (θ := (x, E.loB)) ⟨hx, mB⟩ with ⟨h3, i3⟩ | ⟨h3, i3⟩ <;>
    simp only [hf, pivot, Pi.zero_apply, h1, h2, h3] at i1 i2 i3 ⊢ <;>
    linarith [hx.1, hx.2, hy.1, hy.2]
  set L := max E.loS E.loB with hL
  set U := min E.hiS E.hiB with hU
  have hLU : L < U := by
    rw [hL, hU, max_lt_iff, lt_min_iff, lt_min_iff]
    exact ⟨⟨E.loS_lt_hiS, hS⟩, ⟨hB, E.loB_lt_hiB⟩⟩
  set c := (L + U) / 2 with hc
  have hLc : L < c := by rw [hc]; linarith
  have hcU : c < U := by rw [hc]; linarith
  have hL1 : E.loS ≤ L := le_max_left _ _
  have hL2 : E.loB ≤ L := le_max_right _ _
  have hU1 : U ≤ E.hiS := min_le_left _ _
  have hU2 : U ≤ E.hiB := min_le_right _ _
  have hsubS : Ioo L c ⊆ Icc E.loS E.hiS := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hsubB : Ioo c U ⊆ Icc E.loB E.hiB := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hpos : 0 < ∫ θ, f θ ∂E.prior := by
    refine (integral_pos_iff_support_of_nonneg_ae hnn hint).mpr ?_
    calc (0 : ENNReal) < E.prior (Ioo L c ×ˢ Ioo c U) := by
          rw [ms_prior_eq, Measure.prod_prod]
          exact ENNReal.mul_pos (ms_muS_pos E hLc hsubS).ne' (ms_muB_pos E hcU hsubB).ne'
      _ ≤ E.prior (Function.support f) := by
          refine measure_mono (fun θ hθ => ?_)
          obtain ⟨x, y⟩ := θ
          obtain ⟨hx, hy⟩ := hθ
          have hxS := hsubS hx
          have hyB := hsubB hy
          have e1 : q (x, y) = 1 := (hq (x, y) ⟨hxS, hyB⟩).2.1 (by
            show x < y; linarith [hx.2, hy.1])
          have e2 : q (E.hiS, y) = 0 := (hq (E.hiS, y) ⟨mS, hyB⟩).2.2 (by
            show y < E.hiS; linarith [hy.2])
          have e3 : q (x, E.loB) = 0 := (hq (x, E.loB) ⟨hxS, mB⟩).2.2 (by
            show E.loB < x; linarith [hx.1])
          simp only [Function.mem_support, hf, pivot, e1, e2, e3]
          intro h; linarith [hx.2, hy.1]
  have e : (fun θ => (pivot E q hq).tB θ - (pivot E q hq).tS θ) = fun θ => -f θ := by
    ext θ; simp only [hf]; ring
  unfold DirectMechanism.expectedSurplus
  rw [e, integral_neg]; linarith


/-- `x` clamped to `[a, b]`. -/
noncomputable def msClamp (a b x : ℝ) : ℝ := max a (min x b)

lemma msClamp_mem {a b : ℝ} (hab : a ≤ b) (x : ℝ) : msClamp a b x ∈ Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩

lemma msClamp_of_mem {a b x : ℝ} (hx : x ∈ Icc a b) : msClamp a b x = x := by
  unfold msClamp; rw [min_eq_left hx.2, max_eq_right hx.1]

lemma msClamp_cont (a b : ℝ) : Continuous (msClamp a b) :=
  continuous_const.max (continuous_id.min continuous_const)

lemma msClamp_mono (a b : ℝ) : Monotone (msClamp a b) :=
  fun _ _ h => max_le_max le_rfl (min_le_min h le_rfl)

/-! ### The envelope argument -/

/-- If `(y - x) P x ≤ S y - S x` on `[a, b]`, then `S` has derivative `P x` at every interior
point where `P` is continuous. -/
lemma ms_re_deriv {P S : ℝ → ℝ} {a b : ℝ}
    (hsand : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, (y - x) * P x ≤ S y - S x) {x : ℝ}
    (hx : x ∈ Ioo a b) (hPc : ContinuousAt P x) : HasDerivAt S (P x) x := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hlo : Tendsto (fun y => min (P x) (P y)) (𝓝[≠] x) (𝓝 (P x)) := by
    have : Tendsto (fun y => min (P x) (P y)) (𝓝 x) (𝓝 (min (P x) (P x))) :=
      tendsto_const_nhds.min hPc
    rw [min_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hhi : Tendsto (fun y => max (P x) (P y)) (𝓝[≠] x) (𝓝 (P x)) := by
    have : Tendsto (fun y => max (P x) (P y)) (𝓝 x) (𝓝 (max (P x) (P x))) :=
      tendsto_const_nhds.max hPc
    rw [max_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hxI : x ∈ Icc a b := Ioo_subset_Icc_self hx
  have hev : ∀ᶠ y in 𝓝[≠] x, y ∈ Icc a b ∧ y ≠ x := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]
      with y hy hyI
    exact ⟨hyI, hy⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [hev] with y hy
    obtain ⟨hyI, hyx⟩ := hy
    have h1 := hsand x hxI y hyI
    have h2 := hsand y hyI x hxI
    rw [slope_def_field]
    rcases lt_or_gt_of_ne hyx with hlt | hgt
    · have hneg : y - x < 0 := by linarith
      rw [le_div_iff_of_neg hneg]
      calc (S y - S x) ≤ (y - x) * P y := by linarith
        _ ≤ min (P x) (P y) * (y - x) := by
          rw [mul_comm]; exact mul_le_mul_of_nonpos_right (min_le_right _ _) hneg.le
    · have hpos : 0 < y - x := by linarith
      rw [le_div_iff₀ hpos]
      calc min (P x) (P y) * (y - x) ≤ P x * (y - x) :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) hpos.le
        _ ≤ S y - S x := by linarith
  · filter_upwards [hev] with y hy
    obtain ⟨hyI, hyx⟩ := hy
    have h1 := hsand x hxI y hyI
    have h2 := hsand y hyI x hxI
    rw [slope_def_field]
    rcases lt_or_gt_of_ne hyx with hlt | hgt
    · have hneg : y - x < 0 := by linarith
      rw [div_le_iff_of_neg hneg]
      calc max (P x) (P y) * (y - x) ≤ P x * (y - x) :=
            mul_le_mul_of_nonpos_right (le_max_left _ _) hneg.le
        _ ≤ S y - S x := by linarith
    · have hpos : 0 < y - x := by linarith
      rw [div_le_iff₀ hpos]
      calc S y - S x ≤ (y - x) * P y := by linarith
        _ ≤ max (P x) (P y) * (y - x) := by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_right (le_max_right _ _) hpos.le

/-- The sandwich makes `P` monotone. -/
lemma ms_re_mono {P S : ℝ → ℝ} {a b : ℝ}
    (hsand : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, (y - x) * P x ≤ S y - S x) :
    MonotoneOn P (Icc a b) := by
  intro x hx y hy hxy
  rcases hxy.lt_or_eq with h | h
  · have h1 := hsand x hx y hy
    have h2 := hsand y hy x hx
    have : (y - x) * P x ≤ (y - x) * P y := by linarith
    exact le_of_mul_le_mul_left this (by linarith)
  · rw [h]

/-- The sandwich makes `S` continuous on `[a, b]` (it is Lipschitz). -/
lemma ms_re_cont {P S : ℝ → ℝ} {a b : ℝ}
    (hsand : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, (y - x) * P x ≤ S y - S x) :
    ContinuousOn S (Icc a b) := by
  rcases lt_or_ge b a with hba | hab
  · rw [Icc_eq_empty (not_le.mpr hba)]; exact continuousOn_empty _
  have hm := ms_re_mono hsand
  set L := max |P a| |P b| with hL
  have hbound : ∀ x ∈ Icc a b, |P x| ≤ L := by
    intro x hx
    have h1 := hm ⟨le_rfl, hab⟩ hx hx.1
    have h2 := hm hx ⟨hab, le_rfl⟩ hx.2
    rw [abs_le]
    constructor
    · have := neg_abs_le (P a); have := le_max_left |P a| |P b|; linarith
    · have := le_abs_self (P b); have := le_max_right |P a| |P b|; linarith
  have hlip : LipschitzOnWith (Real.toNNReal L) S (Icc a b) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ ((abs_nonneg _).trans (hbound x hx))]
    have h1 := hsand x hx y hy
    have h2 := hsand y hy x hx
    have bx := abs_le.mp (hbound x hx)
    have by' := abs_le.mp (hbound y hy)
    rcases le_total x y with hxy | hxy
    · rw [abs_of_nonpos (by linarith : x - y ≤ 0)]
      rw [abs_le]
      constructor <;> nlinarith
    · rw [abs_of_nonneg (by linarith : 0 ≤ x - y)]
      rw [abs_le]
      constructor <;> nlinarith
  exact hlip.continuousOn

/-- The countable set of discontinuities of `P` (through its clamped monotone extension). -/
lemma ms_re_countable {P : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hm : MonotoneOn P (Icc a b)) :
    ∃ D : Set ℝ, D.Countable ∧ ∀ x ∈ Ioo a b \ D, ContinuousAt P x := by
  have hmono : Monotone (fun x => P (msClamp a b x)) := fun x y hxy =>
    hm (msClamp_mem hab x) (msClamp_mem hab y) (msClamp_mono a b hxy)
  refine ⟨{x | ¬ContinuousAt (fun x => P (msClamp a b x)) x}, hmono.countable_not_continuousAt,
    fun x hx => ?_⟩
  have hc : ContinuousAt (fun x => P (msClamp a b x)) x := by
    by_contra h; exact hx.2 h
  refine hc.congr ?_
  filter_upwards [Ioo_mem_nhds hx.1.1 hx.1.2] with y hy
  rw [msClamp_of_mem (Ioo_subset_Icc_self hy)]

/-- The envelope formula: `S b - S a = ∫_a^b P`. -/
lemma ms_re_ftc {P S : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hsand : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, (y - x) * P x ≤ S y - S x) :
    S b - S a = ∫ x in a..b, P x := by
  obtain ⟨D, hD, hDc⟩ := ms_re_countable hab (ms_re_mono hsand)
  have hint : IntervalIntegrable P volume a b :=
    (ms_re_mono hsand).mono (by rw [uIcc_of_le hab]) |>.intervalIntegrable
  exact (integral_eq_of_hasDerivAt_off_countable_of_le S P hab hD (ms_re_cont hsand)
    (fun x hx => ms_re_deriv hsand hx.1 (hDc x hx)) hint).symm


lemma ms_TB_eq {E : Environment} (m : DirectMechanism E) (hwd : m.WellDefined) :
    Integrable m.TB (msMuB E) ∧ ∫ θ, m.tB θ ∂E.prior = ∫ y, m.TB y ∂msMuB E := by
  have hi := hwd.tB_integrable
  rw [ms_prior_eq] at hi ⊢
  have e : (fun y => ∫ x, m.tB (x, y) ∂msMuS E) = m.TB := by
    ext y; rw [ms_integral_muS]; rfl
  refine ⟨?_, ?_⟩
  · have := hi.integral_prod_right; rwa [e] at this
  · rw [integral_prod_symm _ hi, e]

lemma ms_TS_eq {E : Environment} (m : DirectMechanism E) (hwd : m.WellDefined) :
    Integrable m.TS (msMuS E) ∧ ∫ θ, m.tS θ ∂E.prior = ∫ x, m.TS x ∂msMuS E := by
  have hi := hwd.tS_integrable
  rw [ms_prior_eq] at hi ⊢
  have e : (fun x => ∫ y, m.tS (x, y) ∂msMuB E) = m.TS := by
    ext x; rw [ms_integral_muB]; rfl
  refine ⟨?_, ?_⟩
  · have := hi.integral_prod_left; rwa [e] at this
  · rw [integral_prod _ hi, e]

lemma ms_surplus_eq {E : Environment} (m : DirectMechanism E) (hwd : m.WellDefined) :
    m.expectedSurplus = ∫ y, m.TB y ∂msMuB E - ∫ x, m.TS x ∂msMuS E := by
  unfold DirectMechanism.expectedSurplus
  rw [integral_sub hwd.tB_integrable hwd.tS_integrable, (ms_TB_eq m hwd).2, (ms_TS_eq m hwd).2]

lemma ms_envB {E : Environment} (m : DirectMechanism E) (hic : m.IsIC) {y : ℝ}
    (hy : y ∈ Icc E.loB E.hiB) : m.UB y = m.UB E.loB + ∫ z in E.loB..y, m.QB z := by
  have := ms_re_ftc (P := m.QB) (S := m.UB) hy.1 (fun a ha b hb => by
    have ha' : a ∈ Icc E.loB E.hiB := ⟨ha.1, ha.2.trans hy.2⟩
    have hb' : b ∈ Icc E.loB E.hiB := ⟨hb.1, hb.2.trans hy.2⟩
    have := hic.2 b hb' a ha'
    unfold DirectMechanism.UB at *; linarith)
  linarith

lemma ms_envS {E : Environment} (m : DirectMechanism E) (hic : m.IsIC) {x : ℝ}
    (hx : x ∈ Icc E.loS E.hiS) : m.US x = m.US E.hiS - ∫ z in x..E.hiS, (1 - m.QS z) := by
  have := ms_re_ftc (P := fun z => 1 - m.QS z) (S := m.US) hx.2 (fun a ha b hb => by
    have ha' : a ∈ Icc E.loS E.hiS := ⟨hx.1.trans ha.1, ha.2⟩
    have hb' : b ∈ Icc E.loS E.hiS := ⟨hx.1.trans hb.1, hb.2⟩
    have := hic.1 b hb' a ha'
    unfold DirectMechanism.US at *; linarith)
  linarith

lemma ms_ae_ne (y : ℝ) : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ y := by
  rw [ae_iff]; simp

lemma ms_fb_eq {E : Environment} {q q' : ℝ × ℝ → ℝ} (hq : IsFirstBestRule E q)
    (hq' : IsFirstBestRule E q') {θ : ℝ × ℝ} (hθ : θ ∈ E.typeSpace) (hne : θ.1 ≠ θ.2) :
    q θ = q' θ := by
  rcases lt_or_gt_of_ne hne with h | h
  · rw [(hq θ hθ).2.1 h, (hq' θ hθ).2.1 h]
  · rw [(hq θ hθ).2.2 h, (hq' θ hθ).2.2 h]

lemma ms_QB_eq {E : Environment} (m m' : DirectMechanism E) (hq : IsFirstBestRule E m.q)
    (hq' : IsFirstBestRule E m'.q) {y : ℝ} (hy : y ∈ Icc E.loB E.hiB) : m.QB y = m'.QB y := by
  unfold DirectMechanism.QB
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ms_ae_ne y] with x hx hxI
  rw [uIoc_of_le E.loS_lt_hiS.le] at hxI
  rw [ms_fb_eq hq hq' (θ := (x, y)) ⟨Ioc_subset_Icc_self hxI, hy⟩ hx]

lemma ms_QS_eq {E : Environment} (m m' : DirectMechanism E) (hq : IsFirstBestRule E m.q)
    (hq' : IsFirstBestRule E m'.q) {x : ℝ} (hx : x ∈ Icc E.loS E.hiS) : m.QS x = m'.QS x := by
  unfold DirectMechanism.QS
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ms_ae_ne x] with y hy hyI
  rw [uIoc_of_le E.loB_lt_hiB.le] at hyI
  rw [ms_fb_eq hq hq' (θ := (x, y)) ⟨hx, Ioc_subset_Icc_self hyI⟩ (Ne.symm hy)]

lemma ms_piv_UB {E : Environment} {q : ℝ × ℝ → ℝ} (hq : IsFirstBestRule E q)
    (hqm : Measurable q) : (pivot E q hq).UB E.loB = 0 := by
  have hwd := ms_piv_wd hq hqm
  have mB : E.loB ∈ Icc E.loB E.hiB := ⟨le_rfl, E.loB_lt_hiB.le⟩
  unfold DirectMechanism.UB
  rw [ms_buyerU _ E.loB (ms_qsecB _ hqm mB) (hwd.tB_section _ mB)]
  have : (fun x => ((pivot E q hq).q (x, E.loB) * E.loB - (pivot E q hq).tB (x, E.loB)) * E.fS x)
      = fun _ => 0 := by
    ext x; simp only [pivot]; ring
  rw [this, intervalIntegral.integral_zero]

lemma ms_piv_US {E : Environment} {q : ℝ × ℝ → ℝ} (hq : IsFirstBestRule E q)
    (hqm : Measurable q) : (pivot E q hq).US E.hiS = E.hiS := by
  have hwd := ms_piv_wd hq hqm
  have mS : E.hiS ∈ Icc E.loS E.hiS := ⟨E.loS_lt_hiS.le, le_rfl⟩
  unfold DirectMechanism.US
  rw [ms_sellerU _ E.hiS (ms_qsecS _ hqm mS) (hwd.tS_section _ mS)]
  have : (fun y => ((pivot E q hq).tS (E.hiS, y) + (1 - (pivot E q hq).q (E.hiS, y)) * E.hiS)
      * E.fB y) = fun y => E.hiS * E.fB y := by
    ext y; simp only [pivot]; ring
  rw [this, ms_constS]

lemma ms_piv_max {E : Environment} {q : ℝ × ℝ → ℝ} (hq : IsFirstBestRule E q)
    (hqm : Measurable q) (m : DirectMechanism E) (hm : m.Admissible)
    (hfb : IsFirstBestRule E m.q) :
    m.expectedSurplus ≤ (pivot E q hq).expectedSurplus := by
  set p := pivot E q hq with hp
  have hpa : p.Admissible := ms_piv_adm hq hqm
  have hpq : IsFirstBestRule E p.q := hq
  obtain ⟨hwd, hic, hir⟩ := hm
  obtain ⟨pwd, pic, -⟩ := hpa
  -- buyer side
  have hB : ∀ y ∈ Icc E.loB E.hiB, m.TB y + m.UB E.loB = p.TB y + p.UB E.loB := by
    intro y hy
    have h1 := ms_envB m hic hy
    have h2 := ms_envB p pic hy
    have hQ : m.QB y = p.QB y := ms_QB_eq m p hfb hpq hy
    have hI : ∫ z in E.loB..y, m.QB z = ∫ z in E.loB..y, p.QB z := by
      refine intervalIntegral.integral_congr (fun z hz => ?_)
      rw [uIcc_of_le hy.1] at hz
      exact ms_QB_eq m p hfb hpq ⟨hz.1, hz.2.trans hy.2⟩
    unfold DirectMechanism.UB at h1 h2 ⊢
    rw [hQ, hI] at h1; linarith
  have hS : ∀ x ∈ Icc E.loS E.hiS, m.TS x - m.US E.hiS = p.TS x - p.US E.hiS := by
    intro x hx
    have h1 := ms_envS m hic hx
    have h2 := ms_envS p pic hx
    have hQ : m.QS x = p.QS x := ms_QS_eq m p hfb hpq hx
    have hI : ∫ z in x..E.hiS, (1 - m.QS z) = ∫ z in x..E.hiS, (1 - p.QS z) := by
      refine intervalIntegral.integral_congr (fun z hz => ?_)
      rw [uIcc_of_le hx.2] at hz
      rw [ms_QS_eq m p hfb hpq ⟨hx.1.trans hz.1, hz.2⟩]
    unfold DirectMechanism.US at h1 h2 ⊢
    rw [hQ, hI] at h1; linarith
  have iB : ∫ y, m.TB y ∂msMuB E + m.UB E.loB = ∫ y, p.TB y ∂msMuB E + p.UB E.loB := by
    have e1 : ∫ y, (m.TB y + m.UB E.loB) ∂msMuB E = ∫ y, (p.TB y + p.UB E.loB) ∂msMuB E :=
      integral_congr_ae (by filter_upwards [ms_ae_muB E] with y hy using hB y hy)
    rwa [integral_add (ms_TB_eq m hwd).1 (integrable_const _),
      integral_add (ms_TB_eq p pwd).1 (integrable_const _), integral_const, integral_const,
      probReal_univ, one_smul, one_smul] at e1
  have iS : ∫ x, m.TS x ∂msMuS E - m.US E.hiS = ∫ x, p.TS x ∂msMuS E - p.US E.hiS := by
    have e1 : ∫ x, (m.TS x - m.US E.hiS) ∂msMuS E = ∫ x, (p.TS x - p.US E.hiS) ∂msMuS E :=
      integral_congr_ae (by filter_upwards [ms_ae_muS E] with x hx using hS x hx)
    rwa [integral_sub (ms_TS_eq m hwd).1 (integrable_const _),
      integral_sub (ms_TS_eq p pwd).1 (integrable_const _), integral_const, integral_const,
      probReal_univ, one_smul, one_smul] at e1
  have u1 := ms_piv_UB hq hqm
  have u2 := ms_piv_US hq hqm
  have r1 := hir.2 E.loB ⟨le_rfl, E.loB_lt_hiB.le⟩
  have r2 := hir.1 E.hiS ⟨E.loS_lt_hiS.le, le_rfl⟩
  rw [ms_surplus_eq m hwd, ms_surplus_eq p pwd]
  rw [← hp] at u1 u2
  linarith


def msConst (E : Environment) (a b : ℝ) (ha : a = 0 ∨ a = 1) : DirectMechanism E :=
  ⟨fun _ => a, fun _ => b, fun _ => b, fun _ _ => ha⟩

lemma ms_const_wd (E : Environment) (a b : ℝ) (ha : a = 0 ∨ a = 1) :
    (msConst E a b ha).WellDefined where
  q_measurable := measurable_const
  tS_measurable := measurable_const
  tB_measurable := measurable_const
  tS_integrable := integrable_const _
  tB_integrable := integrable_const _
  tS_section := fun _ _ => E.fB_intervalIntegrable.const_mul b
  tB_section := fun _ _ => E.fS_intervalIntegrable.const_mul b

lemma ms_const_vals (E : Environment) (a b : ℝ) (ha : a = 0 ∨ a = 1) (x : ℝ) :
    (msConst E a b ha).QS x = a ∧ (msConst E a b ha).QB x = a ∧
    (msConst E a b ha).TS x = b ∧ (msConst E a b ha).TB x = b :=
  ⟨ms_constS E a, ms_constB E a, ms_constS E b, ms_constB E b⟩

lemma ms_const_ic (E : Environment) (a b : ℝ) (ha : a = 0 ∨ a = 1) :
    (msConst E a b ha).IsIC := by
  constructor
  · intro x _ x' _
    rw [(ms_const_vals E a b ha x).1, (ms_const_vals E a b ha x').1,
      (ms_const_vals E a b ha x).2.2.1, (ms_const_vals E a b ha x').2.2.1]
  · intro y _ y' _
    rw [(ms_const_vals E a b ha y).2.1, (ms_const_vals E a b ha y').2.1,
      (ms_const_vals E a b ha y).2.2.2, (ms_const_vals E a b ha y').2.2.2]

lemma ms_surplus_zero {E : Environment} (m : DirectMechanism E) (h : m.ExPostBB) :
    m.expectedSurplus = 0 := by
  unfold DirectMechanism.expectedSurplus
  rw [integral_congr_ae (g := fun _ => (0 : ℝ))
    (by filter_upwards [ms_ae_prior E] with θ hθ; simp [h θ hθ]), integral_zero]

theorem ms_main (E : Environment) :
    (∃ m : DirectMechanism E, m.Admissible ∧ m.ExPostBB ∧ IsFirstBestRule E m.q) ↔
      (E.hiS ≤ E.loB ∨ E.hiB ≤ E.loS) := by
  constructor
  · rintro ⟨m, hm, hbb, hfb⟩
    by_contra hc
    push_neg at hc
    have h1 := ms_piv_max hfb hm.1.q_measurable m hm hfb
    have h2 := ms_piv_def hfb hm.1.q_measurable hc.1 hc.2
    rw [ms_surplus_zero m hbb] at h1
    linarith
  · rintro (h | h)
    · refine ⟨msConst E 1 E.hiS (Or.inr rfl), ⟨ms_const_wd _ _ _ _, ms_const_ic _ _ _ _, ?_, ?_⟩,
        fun _ _ => rfl, fun θ hθ => ⟨Or.inr rfl, fun _ => rfl, fun hlt => ?_⟩⟩
      · intro x hx
        unfold DirectMechanism.US
        rw [(ms_const_vals E _ _ _ x).1, (ms_const_vals E _ _ _ x).2.2.1]; linarith [hx.2]
      · intro y hy
        unfold DirectMechanism.UB
        rw [(ms_const_vals E _ _ _ y).2.1, (ms_const_vals E _ _ _ y).2.2.2]; linarith [hy.1]
      · exfalso; linarith [hθ.1.2, hθ.2.1]
    · refine ⟨msConst E 0 0 (Or.inl rfl), ⟨ms_const_wd _ _ _ _, ms_const_ic _ _ _ _, ?_, ?_⟩,
        fun _ _ => rfl, fun θ hθ => ⟨Or.inl rfl, fun hlt => ?_, fun _ => rfl⟩⟩
      · intro x hx
        unfold DirectMechanism.US
        rw [(ms_const_vals E _ _ _ x).1, (ms_const_vals E _ _ _ x).2.2.1]; linarith
      · intro y hy
        unfold DirectMechanism.UB
        rw [(ms_const_vals E _ _ _ y).2.1, (ms_const_vals E _ _ _ y).2.2.2]; linarith
      · exfalso; linarith [hθ.1.1, hθ.2.2]


lemma ms_tri {a b : ℝ} (hab : a ≤ b) {w g : ℝ → ℝ} (hw : IntervalIntegrable w volume a b)
    (hg : IntervalIntegrable g volume a b) :
    ∫ y in a..b, w y * (∫ z in a..y, g z) = ∫ z in a..b, g z * (∫ y in z..b, w y) := by
  have hw' : Integrable w (volume.restrict (Ioc a b)) := hw.1
  have hg' : Integrable g (volume.restrict (Ioc a b)) := hg.1
  have hSm : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} := measurableSet_le measurable_snd measurable_fst
  set F : ℝ × ℝ → ℝ := {p : ℝ × ℝ | p.2 ≤ p.1}.indicator (fun p => w p.1 * g p.2) with hF
  have hint : Integrable F ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b))) :=
    (hw'.mul_prod hg').indicator hSm
  have key := integral_integral_swap (f := fun y z => F (y, z)) hint
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  have L : ∀ y ∈ Ioc a b, ∫ z, F (y, z) ∂(volume.restrict (Ioc a b)) =
      w y * ∫ z in a..y, g z := by
    intro y hy
    have : (fun z => F (y, z)) = (Iic y).indicator (fun z => w y * g z) := by
      ext z; rw [hF]; simp [Set.indicator_apply]
    rw [this, integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
      integral_const_mul, intervalIntegral.integral_of_le hy.1.le]
    have e : Iic y ∩ Ioc a b = Ioc a y := by
      ext z; simp only [mem_inter_iff, mem_Iic, mem_Ioc]
      exact ⟨fun ⟨h1, h2, _⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1, h2.trans hy.2⟩⟩
    rw [e]
  have R : ∀ z ∈ Ioc a b, ∫ y, F (y, z) ∂(volume.restrict (Ioc a b)) =
      g z * ∫ y in z..b, w y := by
    intro z hz
    have : (fun y => F (y, z)) = (Ici z).indicator (fun y => w y * g z) := by
      ext y; rw [hF]; simp [Set.indicator_apply]
    rw [this, integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
      integral_mul_const, intervalIntegral.integral_of_le hz.2, mul_comm]
    have e : Ici z ∩ Ioc a b = Icc z b := by
      ext y; simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
      exact ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h2⟩ => ⟨h1, hz.1.trans_le h1, h2⟩⟩
    rw [e, integral_Icc_eq_integral_Ioc]
  calc ∫ y in Ioc a b, w y * ∫ z in a..y, g z
      = ∫ y in Ioc a b, ∫ z, F (y, z) ∂(volume.restrict (Ioc a b)) :=
        (setIntegral_congr_fun measurableSet_Ioc (fun y hy => L y hy)).symm
    _ = ∫ z in Ioc a b, ∫ y, F (y, z) ∂(volume.restrict (Ioc a b)) := key
    _ = ∫ z in Ioc a b, g z * ∫ y in z..b, w y :=
        setIntegral_congr_fun measurableSet_Ioc (fun z hz => R z hz)


lemma ms_ii_bdd' {g w : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : AEStronglyMeasurable g (volume.restrict (Ioc a b))) (C : ℝ)
    (hC : ∀ x ∈ Icc a b, |g x| ≤ C) (hw : IntervalIntegrable w volume a b) :
    IntervalIntegrable (fun x => g x * w x) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab] at hw ⊢
  refine Integrable.bdd_mul hw hg (c := C) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  simpa using hC x (Ioc_subset_Icc_self hx)

lemma ms_ion {f : ℝ → ℝ} {a b : ℝ} (h : IntervalIntegrable f volume a b) (hab : a ≤ b) :
    IntegrableOn f (Icc a b) :=
  (integrableOn_Icc_iff_integrableOn_Ioc (f := f)).mpr
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp h)

lemma ms_q01 {E : Environment} (m : DirectMechanism E) {θ : ℝ × ℝ} (hθ : θ ∈ E.typeSpace) :
    0 ≤ m.q θ ∧ m.q θ ≤ 1 := by
  rcases m.q_mem θ hθ with h | h <;> rw [h] <;> norm_num

lemma ms_QB_bd {E : Environment} (m : DirectMechanism E) (hqm : Measurable m.q) {y : ℝ}
    (hy : y ∈ Icc E.loB E.hiB) : 0 ≤ m.QB y ∧ m.QB y ≤ 1 := by
  constructor
  · exact intervalIntegral.integral_nonneg E.loS_lt_hiS.le (fun x hx =>
      mul_nonneg (ms_q01 m (θ := (x, y)) ⟨hx, hy⟩).1 (E.fS_pos x hx).le)
  · calc m.QB y ≤ ∫ x in E.loS..E.hiS, 1 * E.fS x :=
          intervalIntegral.integral_mono_on E.loS_lt_hiS.le (ms_qsecB m hqm hy)
            (E.fS_intervalIntegrable.const_mul 1) (fun x hx => mul_le_mul_of_nonneg_right
              (ms_q01 m (θ := (x, y)) ⟨hx, hy⟩).2 (E.fS_pos x hx).le)
      _ = 1 := ms_constB E 1

lemma ms_QS_bd {E : Environment} (m : DirectMechanism E) (hqm : Measurable m.q) {x : ℝ}
    (hx : x ∈ Icc E.loS E.hiS) : 0 ≤ m.QS x ∧ m.QS x ≤ 1 := by
  constructor
  · exact intervalIntegral.integral_nonneg E.loB_lt_hiB.le (fun y hy =>
      mul_nonneg (ms_q01 m (θ := (x, y)) ⟨hx, hy⟩).1 (E.fB_pos y hy).le)
  · calc m.QS x ≤ ∫ y in E.loB..E.hiB, 1 * E.fB y :=
          intervalIntegral.integral_mono_on E.loB_lt_hiB.le (ms_qsecS m hqm hx)
            (E.fB_intervalIntegrable.const_mul 1) (fun y hy => mul_le_mul_of_nonneg_right
              (ms_q01 m (θ := (x, y)) ⟨hx, hy⟩).2 (E.fB_pos y hy).le)
      _ = 1 := ms_constS E 1

lemma ms_sandB {E : Environment} (m : DirectMechanism E) (hic : m.IsIC) :
    ∀ a ∈ Icc E.loB E.hiB, ∀ b ∈ Icc E.loB E.hiB, (b - a) * m.QB a ≤ m.UB b - m.UB a := by
  intro a ha b hb
  have := hic.2 b hb a ha
  unfold DirectMechanism.UB; linarith

lemma ms_sandS {E : Environment} (m : DirectMechanism E) (hic : m.IsIC) :
    ∀ a ∈ Icc E.loS E.hiS, ∀ b ∈ Icc E.loS E.hiS,
      (b - a) * (1 - m.QS a) ≤ m.US b - m.US a := by
  intro a ha b hb
  have := hic.1 b hb a ha
  unfold DirectMechanism.US; linarith

lemma ms_QB_ii {E : Environment} (m : DirectMechanism E) (hic : m.IsIC) :
    IntervalIntegrable m.QB volume E.loB E.hiB :=
  (ms_re_mono (ms_sandB m hic)).mono (by rw [uIcc_of_le E.loB_lt_hiB.le]) |>.intervalIntegrable

lemma ms_QS1_ii {E : Environment} (m : DirectMechanism E) (hic : m.IsIC) :
    IntervalIntegrable (fun x => 1 - m.QS x) volume E.loS E.hiS :=
  (ms_re_mono (ms_sandS m hic)).mono (by rw [uIcc_of_le E.loS_lt_hiS.le]) |>.intervalIntegrable

lemma ms_cdfB_cont (E : Environment) : ContinuousOn E.cdfB (Icc E.loB E.hiB) := by
  have := intervalIntegral.continuousOn_primitive_interval (a := E.loB) (b := E.hiB)
    (μ := volume) (f := E.fB) (by rw [uIcc_of_le E.loB_lt_hiB.le]; exact ms_ion E.fB_intervalIntegrable E.loB_lt_hiB.le)
  rw [uIcc_of_le E.loB_lt_hiB.le] at this; exact this

lemma ms_cdfS_cont (E : Environment) : ContinuousOn E.cdfS (Icc E.loS E.hiS) := by
  have := intervalIntegral.continuousOn_primitive_interval (a := E.loS) (b := E.hiS)
    (μ := volume) (f := E.fS) (by rw [uIcc_of_le E.loS_lt_hiS.le]; exact ms_ion E.fS_intervalIntegrable E.loS_lt_hiS.le)
  rw [uIcc_of_le E.loS_lt_hiS.le] at this; exact this

lemma ms_identB {E : Environment} (m : DirectMechanism E) (hqm : Measurable m.q) (hic : m.IsIC) :
    ∫ y, m.TB y ∂msMuB E = ∫ y, m.QB y * E.psiB y ∂msMuB E - m.UB E.loB := by
  rw [ms_integral_muB, ms_integral_muB]
  have hab := E.loB_lt_hiB.le
  have hQi := ms_QB_ii m hic
  have hPc : ContinuousOn (fun y => ∫ z in E.loB..y, m.QB z) (uIcc E.loB E.hiB) :=
    intervalIntegral.continuousOn_primitive_interval (by rw [uIcc_of_le hab]; exact ms_ion hQi hab)
  have hcdf' : ContinuousOn (fun y => 1 - E.cdfB y) (uIcc E.loB E.hiB) := by
    rw [uIcc_of_le hab]; exact continuousOn_const.sub (ms_cdfB_cont E)
  have i1 : IntervalIntegrable (fun y => (m.QB y * y) * E.fB y) volume E.loB E.hiB := by
    refine ms_ii_bdd' hab (hQi.1.aestronglyMeasurable.mul continuous_id.aestronglyMeasurable)
      (|E.loB| + |E.hiB|) (fun y hy => ?_) E.fB_intervalIntegrable
    rw [abs_mul]
    have h := ms_QB_bd m hqm hy
    have h1 : |m.QB y| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    have := mul_le_mul h1 (ms_abs_mem hy) (abs_nonneg _) zero_le_one
    linarith
  have i2 : IntervalIntegrable (fun y => E.fB y * ∫ z in E.loB..y, m.QB z) volume E.loB E.hiB :=
    E.fB_intervalIntegrable.mul_continuousOn hPc
  have i3 : IntervalIntegrable (fun y => m.QB y * (1 - E.cdfB y)) volume E.loB E.hiB :=
    hQi.mul_continuousOn hcdf'
  have tri := ms_tri hab E.fB_intervalIntegrable hQi
  have e1 : ∫ z in E.loB..E.hiB, m.QB z * ∫ y in z..E.hiB, E.fB y =
      ∫ z in E.loB..E.hiB, m.QB z * (1 - E.cdfB z) := by
    refine intervalIntegral.integral_congr (fun z hz => ?_)
    rw [uIcc_of_le hab] at hz
    rw [← intervalIntegral.integral_interval_sub_left E.fB_intervalIntegrable
      (E.fB_intervalIntegrable.mono_set (by
        rw [uIcc_of_le hab, uIcc_of_le hz.1]; exact Icc_subset_Icc le_rfl hz.2)), E.fB_integral]
    rfl
  have lhs : ∫ y in E.loB..E.hiB, m.TB y * E.fB y = ∫ y in E.loB..E.hiB,
      ((m.QB y * y) * E.fB y - E.fB y * (∫ z in E.loB..y, m.QB z) - m.UB E.loB * E.fB y) := by
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    rw [uIcc_of_le hab] at hy
    have h := ms_envB m hic hy
    have hu : m.UB y = m.QB y * y - m.TB y := rfl
    linear_combination (E.fB y) * (h.symm.trans hu)
  have rhs : ∫ y in E.loB..E.hiB, m.QB y * E.psiB y * E.fB y = ∫ y in E.loB..E.hiB,
      ((m.QB y * y) * E.fB y - m.QB y * (1 - E.cdfB y)) := by
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    rw [uIcc_of_le hab] at hy
    have hf := (E.fB_pos y hy).ne'
    simp only [Environment.psiB]
    field_simp
  rw [lhs, rhs, intervalIntegral.integral_sub (i1.sub i2) (E.fB_intervalIntegrable.const_mul _),
    intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_sub i1 i3, tri, e1, ms_constS]

lemma ms_identS {E : Environment} (m : DirectMechanism E) (hqm : Measurable m.q) (hic : m.IsIC) :
    ∫ x, m.TS x ∂msMuS E = m.US E.hiS - ∫ x, (1 - m.QS x) * E.psiS x ∂msMuS E := by
  rw [ms_integral_muS, ms_integral_muS]
  have hab := E.loS_lt_hiS.le
  have hQi := ms_QS1_ii m hic
  have hRc : ContinuousOn (fun x => ∫ z in x..E.hiS, (1 - m.QS z)) (uIcc E.loS E.hiS) := by
    have := intervalIntegral.continuousOn_primitive_interval' (a := E.hiS) hQi
      (by rw [uIcc_of_le hab]; exact ⟨hab, le_rfl⟩)
    refine this.neg.congr (fun x _ => ?_)
    exact intervalIntegral.integral_symm _ _
  have hcdf' : ContinuousOn E.cdfS (uIcc E.loS E.hiS) := by
    rw [uIcc_of_le hab]; exact ms_cdfS_cont E
  have i1 : IntervalIntegrable (fun x => ((1 - m.QS x) * x) * E.fS x) volume E.loS E.hiS := by
    refine ms_ii_bdd' hab (hQi.1.aestronglyMeasurable.mul continuous_id.aestronglyMeasurable)
      (|E.loS| + |E.hiS|) (fun x hx => ?_) E.fS_intervalIntegrable
    rw [abs_mul]
    have h := ms_QS_bd m hqm hx
    have h1 : |1 - m.QS x| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    have := mul_le_mul h1 (ms_abs_mem hx) (abs_nonneg _) zero_le_one
    linarith
  have i2 : IntervalIntegrable (fun x => E.fS x * ∫ z in x..E.hiS, (1 - m.QS z))
      volume E.loS E.hiS := E.fS_intervalIntegrable.mul_continuousOn hRc
  have i3 : IntervalIntegrable (fun x => (1 - m.QS x) * E.cdfS x) volume E.loS E.hiS :=
    hQi.mul_continuousOn hcdf'
  have tri := ms_tri hab hQi E.fS_intervalIntegrable
  have lhs : ∫ x in E.loS..E.hiS, m.TS x * E.fS x = ∫ x in E.loS..E.hiS,
      (m.US E.hiS * E.fS x - E.fS x * (∫ z in x..E.hiS, (1 - m.QS z)) -
        ((1 - m.QS x) * x) * E.fS x) := by
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [uIcc_of_le hab] at hx
    have h := ms_envS m hic hx
    have hu : m.US x = m.TS x + (1 - m.QS x) * x := rfl
    linear_combination (E.fS x) * (hu.symm.trans h)
  have rhs : ∫ x in E.loS..E.hiS, (1 - m.QS x) * E.psiS x * E.fS x = ∫ x in E.loS..E.hiS,
      (((1 - m.QS x) * x) * E.fS x + (1 - m.QS x) * E.cdfS x) := by
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [uIcc_of_le hab] at hx
    have hf := (E.fS_pos x hx).ne'
    simp only [Environment.psiS]
    field_simp
  rw [lhs, rhs, intervalIntegral.integral_sub
    ((E.fS_intervalIntegrable.const_mul _).sub i2) i1,
    intervalIntegral.integral_sub (E.fS_intervalIntegrable.const_mul _) i2,
    intervalIntegral.integral_add i1 i3, ← tri, ms_constB]
  have : ∫ x in E.loS..E.hiS, (1 - m.QS x) * E.cdfS x =
      ∫ y in E.loS..E.hiS, (1 - m.QS y) * ∫ z in E.loS..y, E.fS z := rfl
  rw [this]; ring


lemma ms_psiB_int (E : Environment) : Integrable E.psiB (msMuB E) := by
  have hab := E.loB_lt_hiB.le
  have : (fun x => ENNReal.ofReal (E.fB x)) =
      fun x => ((Real.toNNReal (E.fB x) : NNReal) : ENNReal) := rfl
  rw [msMuB, this, integrable_withDensity_iff_integrable_smul E.fB_measurable.real_toNNReal]
  have i1 : IntegrableOn (fun y => y * E.fB y - (1 - E.cdfB y)) (Icc E.loB E.hiB) := by
    refine Integrable.sub ?_ ?_
    · have := E.fB_intervalIntegrable.mul_continuousOn (g := id) continuousOn_id
      exact (ms_ion this hab).congr_fun (fun y _ => by simp [mul_comm]) measurableSet_Icc
    · exact (continuousOn_const.sub (ms_cdfB_cont E)).integrableOn_Icc
  refine Integrable.congr i1 ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  have hf := (E.fB_pos y hy).ne'
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (E.fB_pos y hy).le, Environment.psiB, smul_eq_mul]
  field_simp

lemma ms_psiS_int (E : Environment) : Integrable E.psiS (msMuS E) := by
  have hab := E.loS_lt_hiS.le
  have : (fun x => ENNReal.ofReal (E.fS x)) =
      fun x => ((Real.toNNReal (E.fS x) : NNReal) : ENNReal) := rfl
  rw [msMuS, this, integrable_withDensity_iff_integrable_smul E.fS_measurable.real_toNNReal]
  have i1 : IntegrableOn (fun y => y * E.fS y + E.cdfS y) (Icc E.loS E.hiS) := by
    refine Integrable.add ?_ ?_
    · have := E.fS_intervalIntegrable.mul_continuousOn (g := id) continuousOn_id
      exact (ms_ion this hab).congr_fun (fun y _ => by simp [mul_comm]) measurableSet_Icc
    · exact (ms_cdfS_cont E).integrableOn_Icc
  refine Integrable.congr i1 ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  have hf := (E.fS_pos y hy).ne'
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (E.fS_pos y hy).le, Environment.psiS, smul_eq_mul]
  field_simp

lemma ms_fubB {E : Environment} (m : DirectMechanism E) (hqm : Measurable m.q) :
    Integrable (fun θ => m.q θ * E.psiB θ.2) E.prior ∧
    ∫ θ, m.q θ * E.psiB θ.2 ∂E.prior = ∫ y, m.QB y * E.psiB y ∂msMuB E := by
  have hae := ms_ae_prior E
  rw [ms_prior_eq] at hae ⊢
  have hg := (ms_psiB_int E).comp_snd (msMuS E)
  have hi : Integrable (fun θ : ℝ × ℝ => m.q θ * E.psiB θ.2) ((msMuS E).prod (msMuB E)) := by
    refine hg.norm.mono' (hqm.aestronglyMeasurable.mul hg.aestronglyMeasurable) ?_
    filter_upwards [hae] with θ hθ
    rw [norm_mul]
    have := ms_q01 m hθ
    calc ‖m.q θ‖ * ‖E.psiB θ.2‖ ≤ 1 * ‖E.psiB θ.2‖ :=
          mul_le_mul_of_nonneg_right (by rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith)
            (norm_nonneg _)
      _ = _ := one_mul _
  refine ⟨hi, ?_⟩
  rw [integral_prod_symm _ hi]
  congr 1; ext y
  show ∫ x, m.q (x, y) * E.psiB y ∂msMuS E = _
  rw [integral_mul_const, ms_integral_muS]; rfl

lemma ms_fubS {E : Environment} (m : DirectMechanism E) (hqm : Measurable m.q) :
    Integrable (fun θ => m.q θ * E.psiS θ.1) E.prior ∧
    ∫ θ, m.q θ * E.psiS θ.1 ∂E.prior = ∫ x, m.QS x * E.psiS x ∂msMuS E ∧
    Integrable (fun x => m.QS x * E.psiS x) (msMuS E) := by
  have hae := ms_ae_prior E
  rw [ms_prior_eq] at hae ⊢
  have hg := (ms_psiS_int E).comp_fst (msMuB E)
  have hi : Integrable (fun θ : ℝ × ℝ => m.q θ * E.psiS θ.1) ((msMuS E).prod (msMuB E)) := by
    refine hg.norm.mono' (hqm.aestronglyMeasurable.mul hg.aestronglyMeasurable) ?_
    filter_upwards [hae] with θ hθ
    rw [norm_mul]
    have := ms_q01 m hθ
    calc ‖m.q θ‖ * ‖E.psiS θ.1‖ ≤ 1 * ‖E.psiS θ.1‖ :=
          mul_le_mul_of_nonneg_right (by rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith)
            (norm_nonneg _)
      _ = _ := one_mul _
  have e : (fun x => ∫ y, m.q (x, y) * E.psiS (x, y).1 ∂msMuB E) = fun x => m.QS x * E.psiS x := by
    ext x
    show ∫ y, m.q (x, y) * E.psiS x ∂msMuB E = _
    rw [integral_mul_const, ms_integral_muB]; rfl
  refine ⟨hi, ?_, ?_⟩
  · rw [integral_prod _ hi, e]
  · have := hi.integral_prod_left; rwa [e] at this

lemma ms_ident {E : Environment} (m : DirectMechanism E) (hm : m.Admissible) :
    m.expectedSurplus = ∫ θ, m.q θ * (E.psiB θ.2 - E.psiS θ.1) ∂E.prior +
      ∫ x, E.psiS x ∂msMuS E - m.UB E.loB - m.US E.hiS := by
  obtain ⟨hwd, hic, -⟩ := hm
  have hqm := hwd.q_measurable
  obtain ⟨iB, fB⟩ := ms_fubB m hqm
  obtain ⟨iS, fS, iQS⟩ := ms_fubS m hqm
  have e : (fun θ => m.q θ * (E.psiB θ.2 - E.psiS θ.1)) =
      fun θ => m.q θ * E.psiB θ.2 - m.q θ * E.psiS θ.1 := by ext; ring
  rw [ms_surplus_eq m hwd, ms_identB m hqm hic, ms_identS m hqm hic, e, integral_sub iB iS, fB, fS]
  have e2 : (fun x => (1 - m.QS x) * E.psiS x) = fun x => E.psiS x - m.QS x * E.psiS x := by
    ext; ring
  rw [e2, integral_sub (ms_psiS_int E) iQS]; ring


noncomputable def msPsS (E : Environment) (x : ℝ) : ℝ := E.psiS (msClamp E.loS E.hiS x)
noncomputable def msPsB (E : Environment) (y : ℝ) : ℝ := E.psiB (msClamp E.loB E.hiB y)
noncomputable def msQs (E : Environment) (θ : ℝ × ℝ) : ℝ :=
  if msPsS E θ.1 < msPsB E θ.2 then 1 else 0
noncomputable def msQBs (E : Environment) (y : ℝ) : ℝ := ∫ x in E.loS..E.hiS, msQs E (x, y) * E.fS x
noncomputable def msQSs (E : Environment) (x : ℝ) : ℝ := ∫ y in E.loB..E.hiB, msQs E (x, y) * E.fB y

noncomputable def msOpt (E : Environment) : DirectMechanism E where
  q := msQs E
  tS := fun θ => E.hiS - (1 - msQSs E θ.1) * θ.1 - ∫ z in θ.1..E.hiS, (1 - msQSs E z)
  tB := fun θ => msQBs E θ.2 * θ.2 - ∫ z in E.loB..θ.2, msQBs E z
  q_mem := fun θ _ => by unfold msQs; split_ifs <;> simp

lemma ms_psS_meas (E : Environment) : Measurable (msPsS E) := by
  unfold msPsS Environment.psiS
  have hc : Continuous (fun x => E.cdfS (msClamp E.loS E.hiS x)) :=
    (ms_cdfS_cont E).comp_continuous (msClamp_cont _ _) (fun x => msClamp_mem E.loS_lt_hiS.le x)
  exact (msClamp_cont _ _).measurable.add
    (hc.measurable.div (E.fS_measurable.comp (msClamp_cont _ _).measurable))

lemma ms_psB_meas (E : Environment) : Measurable (msPsB E) := by
  unfold msPsB Environment.psiB
  have hc : Continuous (fun x => E.cdfB (msClamp E.loB E.hiB x)) :=
    (ms_cdfB_cont E).comp_continuous (msClamp_cont _ _) (fun x => msClamp_mem E.loB_lt_hiB.le x)
  exact (msClamp_cont _ _).measurable.sub
    ((measurable_const.sub hc.measurable).div (E.fB_measurable.comp (msClamp_cont _ _).measurable))

lemma ms_qs_meas (E : Environment) : Measurable (msQs E) := by
  unfold msQs
  exact Measurable.ite (measurableSet_lt ((ms_psS_meas E).comp measurable_fst)
    ((ms_psB_meas E).comp measurable_snd)) measurable_const measurable_const

lemma ms_qs01 (E : Environment) (θ : ℝ × ℝ) : 0 ≤ msQs E θ ∧ msQs E θ ≤ 1 := by
  unfold msQs; split_ifs <;> norm_num

lemma ms_qs_monoB {E : Environment} (hreg : E.Regular) (x : ℝ) :
    Monotone (fun y => msQs E (x, y)) := by
  intro a b hab
  have hm : msPsB E a ≤ msPsB E b := hreg.2 (msClamp_mem E.loB_lt_hiB.le a)
    (msClamp_mem E.loB_lt_hiB.le b) (msClamp_mono _ _ hab)
  simp only [msQs]
  split_ifs with h1 h2 <;> first | exact absurd (h1.trans_le hm) h2 | norm_num

lemma ms_qs_antiS {E : Environment} (hreg : E.Regular) (y : ℝ) :
    Antitone (fun x => msQs E (x, y)) := by
  intro a b hab
  have hm : msPsS E a ≤ msPsS E b := hreg.1 (msClamp_mem E.loS_lt_hiS.le a)
    (msClamp_mem E.loS_lt_hiS.le b) (msClamp_mono _ _ hab)
  simp only [msQs]
  split_ifs with h1 h2 <;> first | exact absurd (hm.trans_lt h1) h2 | norm_num

lemma ms_qs_secB (E : Environment) (y : ℝ) :
    IntervalIntegrable (fun x => msQs E (x, y) * E.fS x) volume E.loS E.hiS :=
  ms_ii_bdd E.loS_lt_hiS.le ((ms_qs_meas E).comp measurable_prodMk_right) 1
    (fun x _ => by have := ms_qs01 E (x, y); rw [abs_le]; constructor <;> linarith)
    E.fS_intervalIntegrable

lemma ms_qs_secS (E : Environment) (x : ℝ) :
    IntervalIntegrable (fun y => msQs E (x, y) * E.fB y) volume E.loB E.hiB :=
  ms_ii_bdd E.loB_lt_hiB.le ((ms_qs_meas E).comp measurable_prodMk_left) 1
    (fun y _ => by have := ms_qs01 E (x, y); rw [abs_le]; constructor <;> linarith)
    E.fB_intervalIntegrable

lemma ms_QBs_mono {E : Environment} (hreg : E.Regular) : Monotone (msQBs E) := by
  intro a b hab
  exact intervalIntegral.integral_mono_on E.loS_lt_hiS.le (ms_qs_secB E a) (ms_qs_secB E b)
    (fun x hx => mul_le_mul_of_nonneg_right (ms_qs_monoB hreg x hab) (E.fS_pos x hx).le)

lemma ms_QSs_anti {E : Environment} (hreg : E.Regular) : Antitone (msQSs E) := by
  intro a b hab
  exact intervalIntegral.integral_mono_on E.loB_lt_hiB.le (ms_qs_secS E b) (ms_qs_secS E a)
    (fun y hy => mul_le_mul_of_nonneg_right (ms_qs_antiS hreg y hab) (E.fB_pos y hy).le)

lemma ms_QBs_bd (E : Environment) (y : ℝ) : 0 ≤ msQBs E y ∧ msQBs E y ≤ 1 := by
  constructor
  · exact intervalIntegral.integral_nonneg E.loS_lt_hiS.le (fun x hx =>
      mul_nonneg (ms_qs01 E (x, y)).1 (E.fS_pos x hx).le)
  · calc msQBs E y ≤ ∫ x in E.loS..E.hiS, 1 * E.fS x :=
          intervalIntegral.integral_mono_on E.loS_lt_hiS.le (ms_qs_secB E y)
            (E.fS_intervalIntegrable.const_mul 1) (fun x hx => mul_le_mul_of_nonneg_right
              (ms_qs01 E (x, y)).2 (E.fS_pos x hx).le)
      _ = 1 := ms_constB E 1

lemma ms_QSs_bd (E : Environment) (x : ℝ) : 0 ≤ msQSs E x ∧ msQSs E x ≤ 1 := by
  constructor
  · exact intervalIntegral.integral_nonneg E.loB_lt_hiB.le (fun y hy =>
      mul_nonneg (ms_qs01 E (x, y)).1 (E.fB_pos y hy).le)
  · calc msQSs E x ≤ ∫ y in E.loB..E.hiB, 1 * E.fB y :=
          intervalIntegral.integral_mono_on E.loB_lt_hiB.le (ms_qs_secS E x)
            (E.fB_intervalIntegrable.const_mul 1) (fun y hy => mul_le_mul_of_nonneg_right
              (ms_qs01 E (x, y)).2 (E.fB_pos y hy).le)
      _ = 1 := ms_constS E 1

lemma ms_mono_int {g : ℝ → ℝ} (hg : Monotone g) (c d : ℝ) :
    g c * (d - c) ≤ ∫ z in c..d, g z := by
  rcases le_total c d with h | h
  · calc g c * (d - c) = ∫ z in c..d, g c := by simp [mul_comm]
      _ ≤ _ := intervalIntegral.integral_mono_on h intervalIntegrable_const hg.intervalIntegrable
          (fun z hz => hg hz.1)
  · have : ∫ z in d..c, g z ≤ ∫ z in d..c, g c :=
      intervalIntegral.integral_mono_on h hg.intervalIntegrable intervalIntegrable_const
          (fun z hz => hg hz.2)
    rw [intervalIntegral.integral_symm]
    simp at this
    nlinarith

lemma ms_opt_TB (E : Environment) (y : ℝ) :
    (msOpt E).TB y = msQBs E y * y - ∫ z in E.loB..y, msQBs E z := by
  show ∫ x in E.loS..E.hiS, (msQBs E y * y - ∫ z in E.loB..y, msQBs E z) * E.fS x = _
  exact ms_constB E _

lemma ms_opt_TS (E : Environment) (x : ℝ) :
    (msOpt E).TS x = E.hiS - (1 - msQSs E x) * x - ∫ z in x..E.hiS, (1 - msQSs E z) := by
  show ∫ y in E.loB..E.hiB,
    (E.hiS - (1 - msQSs E x) * x - ∫ z in x..E.hiS, (1 - msQSs E z)) * E.fB y = _
  exact ms_constS E _

lemma ms_opt_adm {E : Environment} (hreg : E.Regular) : (msOpt E).Admissible := by
  have hQBm := ms_QBs_mono hreg
  have hQSa := ms_QSs_anti hreg
  have h1m : Monotone (fun z => 1 - msQSs E z) := fun a b h => by
    have := hQSa h; simp only; linarith
  have hPc : Continuous (fun y => ∫ z in E.loB..y, msQBs E z) :=
    intervalIntegral.continuous_primitive (μ := volume) (fun a b => hQBm.intervalIntegrable) _
  have hRc : Continuous (fun x => ∫ z in x..E.hiS, (1 - msQSs E z)) := by
    have := (intervalIntegral.continuous_primitive (μ := volume)
      (fun a b => h1m.intervalIntegrable) E.hiS).neg
    refine this.congr (fun x => ?_)
    exact (intervalIntegral.integral_symm _ _).symm
  have tBm : Measurable (msOpt E).tB := by
    show Measurable (fun θ : ℝ × ℝ => msQBs E θ.2 * θ.2 - ∫ z in E.loB..θ.2, msQBs E z)
    exact ((hQBm.measurable.comp measurable_snd).mul measurable_snd).sub
      (hPc.measurable.comp measurable_snd)
  have tSm : Measurable (msOpt E).tS := by
    show Measurable (fun θ : ℝ × ℝ =>
      E.hiS - (1 - msQSs E θ.1) * θ.1 - ∫ z in θ.1..E.hiS, (1 - msQSs E z))
    exact (measurable_const.sub ((measurable_const.sub (hQSa.measurable.comp measurable_fst)).mul
      measurable_fst)).sub (hRc.measurable.comp measurable_fst)
  have bB : ∀ θ ∈ E.typeSpace, |(msOpt E).tB θ| ≤ 3 * (|E.loB| + |E.hiB|) := by
    intro θ hθ
    show |msQBs E θ.2 * θ.2 - ∫ z in E.loB..θ.2, msQBs E z| ≤ _
    have h1 := ms_QBs_bd E θ.2
    have h2 : ‖∫ z in E.loB..θ.2, msQBs E z‖ ≤ 1 * |θ.2 - E.loB| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (fun z _ => by
        have := ms_QBs_bd E z; rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith)
    rw [Real.norm_eq_abs] at h2
    have h3 := ms_abs_mem hθ.2
    have h4 : |θ.2 - E.loB| ≤ |θ.2| + |E.loB| := abs_sub _ _
    have h5 : |msQBs E θ.2 * θ.2| ≤ |θ.2| := by
      rw [abs_mul]; have : |msQBs E θ.2| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      nlinarith [abs_nonneg θ.2, abs_nonneg (msQBs E θ.2)]
    calc _ ≤ |msQBs E θ.2 * θ.2| + |∫ z in E.loB..θ.2, msQBs E z| := abs_sub _ _
      _ ≤ _ := by linarith [abs_nonneg E.loB, abs_nonneg E.hiB]
  have bS : ∀ θ ∈ E.typeSpace, |(msOpt E).tS θ| ≤ |E.hiS| + 2 * (|E.loS| + |E.hiS|) + |E.hiS| := by
    intro θ hθ
    show |E.hiS - (1 - msQSs E θ.1) * θ.1 - ∫ z in θ.1..E.hiS, (1 - msQSs E z)| ≤ _
    have h1 := ms_QSs_bd E θ.1
    have h2 : ‖∫ z in θ.1..E.hiS, (1 - msQSs E z)‖ ≤ 1 * |E.hiS - θ.1| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (fun z _ => by
        have := ms_QSs_bd E z; rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith)
    rw [Real.norm_eq_abs] at h2
    have h3 := ms_abs_mem hθ.1
    have h4 : |E.hiS - θ.1| ≤ |E.hiS| + |θ.1| := abs_sub _ _
    have h5 : |(1 - msQSs E θ.1) * θ.1| ≤ |θ.1| := by
      rw [abs_mul]; have : |1 - msQSs E θ.1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      nlinarith [abs_nonneg θ.1, abs_nonneg (1 - msQSs E θ.1)]
    calc _ ≤ |E.hiS - (1 - msQSs E θ.1) * θ.1| + |∫ z in θ.1..E.hiS, (1 - msQSs E z)| :=
          abs_sub _ _
      _ ≤ |E.hiS| + |(1 - msQSs E θ.1) * θ.1| + |∫ z in θ.1..E.hiS, (1 - msQSs E z)| := by
          linarith [abs_sub E.hiS ((1 - msQSs E θ.1) * θ.1)]
      _ ≤ _ := by linarith [abs_nonneg E.loS, abs_nonneg E.hiS]
  have hwd : (msOpt E).WellDefined :=
    { q_measurable := ms_qs_meas E
      tS_measurable := tSm
      tB_measurable := tBm
      tS_integrable := ms_int_bdd E tSm _ bS
      tB_integrable := ms_int_bdd E tBm _ bB
      tS_section := fun x _ => by
        show IntervalIntegrable (fun y => (E.hiS - (1 - msQSs E x) * x -
          ∫ z in x..E.hiS, (1 - msQSs E z)) * E.fB y) volume _ _
        exact E.fB_intervalIntegrable.const_mul _
      tB_section := fun y _ => by
        show IntervalIntegrable (fun x => (msQBs E y * y - ∫ z in E.loB..y, msQBs E z) * E.fS x)
          volume _ _
        exact E.fS_intervalIntegrable.const_mul _ }
  refine ⟨hwd, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro x _ x' _
    show (msOpt E).TS x' + (1 - msQSs E x') * x ≤ (msOpt E).TS x + (1 - msQSs E x) * x
    rw [ms_opt_TS, ms_opt_TS]
    have hm := ms_mono_int h1m x' x
    have ha := intervalIntegral.integral_add_adjacent_intervals
      (h1m.intervalIntegrable (μ := volume) (a := x') (b := x))
      (h1m.intervalIntegrable (μ := volume) (a := x) (b := E.hiS))
    linarith
  · intro y _ y' _
    show msQBs E y' * y - (msOpt E).TB y' ≤ msQBs E y * y - (msOpt E).TB y
    rw [ms_opt_TB, ms_opt_TB]
    have hm := ms_mono_int hQBm y' y
    have ha := intervalIntegral.integral_add_adjacent_intervals
      (hQBm.intervalIntegrable (μ := volume) (a := E.loB) (b := y'))
      (hQBm.intervalIntegrable (μ := volume) (a := y') (b := y))
    linarith
  · intro x hx
    show x ≤ (msOpt E).TS x + (1 - msQSs E x) * x
    rw [ms_opt_TS]
    have : ∫ z in x..E.hiS, (1 - msQSs E z) ≤ ∫ z in x..E.hiS, (1 : ℝ) :=
      intervalIntegral.integral_mono_on hx.2 h1m.intervalIntegrable intervalIntegrable_const
        (fun z _ => by have := ms_QSs_bd E z; linarith)
    simp at this
    linarith
  · intro y hy
    show 0 ≤ msQBs E y * y - (msOpt E).TB y
    rw [ms_opt_TB]
    have : 0 ≤ ∫ z in E.loB..y, msQBs E z :=
      intervalIntegral.integral_nonneg hy.1 (fun z _ => (ms_QBs_bd E z).1)
    linarith


instance ms_probP' (E : Environment) : IsProbabilityMeasure E.prior := by
  rw [ms_prior_eq]; infer_instance

lemma ms_int_qpsi {E : Environment} (m : DirectMechanism E) (hqm : Measurable m.q) :
    Integrable (fun θ => m.q θ * (E.psiB θ.2 - E.psiS θ.1)) E.prior := by
  refine ((ms_fubB m hqm).1.sub (ms_fubS m hqm).1).congr (Eventually.of_forall fun θ => ?_)
  show m.q θ * E.psiB θ.2 - m.q θ * E.psiS θ.1 = _
  ring

lemma ms_profit_pt {E : Environment} (m : DirectMechanism E) {θ : ℝ × ℝ}
    (hθ : θ ∈ E.typeSpace) :
    m.q θ * (E.psiB θ.2 - E.psiS θ.1) ≤ profitRule E θ * (E.psiB θ.2 - E.psiS θ.1) := by
  have := ms_q01 m hθ
  unfold profitRule
  split_ifs with h
  · nlinarith
  · push_neg at h; nlinarith

lemma ms_opt_q {E : Environment} {θ : ℝ × ℝ} (hθ : θ ∈ E.typeSpace) :
    msQs E θ = profitRule E θ := by
  unfold msQs profitRule msPsS msPsB
  rw [msClamp_of_mem hθ.1, msClamp_of_mem hθ.2]

lemma ms_opt_UB (E : Environment) : (msOpt E).UB E.loB = 0 := by
  show msQBs E E.loB * E.loB - (msOpt E).TB E.loB = 0
  rw [ms_opt_TB]; simp

lemma ms_opt_US (E : Environment) : (msOpt E).US E.hiS = E.hiS := by
  show (msOpt E).TS E.hiS + (1 - msQSs E E.hiS) * E.hiS = E.hiS
  rw [ms_opt_TS]; simp

theorem ms_profit (E : Environment) (hreg : E.Regular) (m : DirectMechanism E)
    (hm : m.Admissible) :
    ((∀ m' : DirectMechanism E, m'.Admissible → m'.expectedSurplus ≤ m.expectedSurplus) →
      (∀ᵐ θ ∂E.prior, E.psiB θ.2 ≠ E.psiS θ.1 → m.q θ = profitRule E θ) ∧
      (∀ y ∈ Set.Icc E.loB E.hiB, m.TB y = y * m.QB y - ∫ z in E.loB..y, m.QB z) ∧
      (∀ x ∈ Set.Icc E.loS E.hiS,
        m.TS x = E.hiS - (1 - m.QS x) * x - ∫ z in x..E.hiS, (1 - m.QS z))) ∧
    ((∀ θ ∈ E.typeSpace, m.q θ = profitRule E θ) →
      (∀ y ∈ Set.Icc E.loB E.hiB, m.TB y = y * m.QB y - ∫ z in E.loB..y, m.QB z) →
      (∀ x ∈ Set.Icc E.loS E.hiS,
        m.TS x = E.hiS - (1 - m.QS x) * x - ∫ z in x..E.hiS, (1 - m.QS z)) →
      ∀ m' : DirectMechanism E, m'.Admissible → m'.expectedSurplus ≤ m.expectedSurplus) := by
  have hid := ms_ident m hm
  obtain ⟨hwd, hic, hir⟩ := hm
  have hqm := hwd.q_measurable
  have mB : E.loB ∈ Icc E.loB E.hiB := ⟨le_rfl, E.loB_lt_hiB.le⟩
  have mS : E.hiS ∈ Icc E.loS E.hiS := ⟨E.loS_lt_hiS.le, le_rfl⟩
  constructor
  · intro hmax
    obtain ⟨c, hc⟩ : ∃ c, c = m.UB E.loB := ⟨_, rfl⟩
    obtain ⟨d, hd⟩ : ∃ d, d = m.US E.hiS - E.hiS := ⟨_, rfl⟩
    have hc0 : 0 ≤ c := hc ▸ hir.2 _ mB
    have hd0 : 0 ≤ d := by have := hir.1 _ mS; rw [hd]; linarith
    let m3 : DirectMechanism E := ⟨m.q, fun θ => m.tS θ - d, fun θ => m.tB θ + c, m.q_mem⟩
    have TB3 : ∀ y ∈ Icc E.loB E.hiB, m3.TB y = m.TB y + c := by
      intro y hy
      show ∫ x in E.loS..E.hiS, (m.tB (x, y) + c) * E.fS x = _
      have e : (fun x => (m.tB (x, y) + c) * E.fS x) =
          fun x => m.tB (x, y) * E.fS x + c * E.fS x := by ext; ring
      rw [e, intervalIntegral.integral_add (hwd.tB_section y hy)
        (E.fS_intervalIntegrable.const_mul c), ms_constB]; rfl
    have TS3 : ∀ x ∈ Icc E.loS E.hiS, m3.TS x = m.TS x - d := by
      intro x hx
      show ∫ y in E.loB..E.hiB, (m.tS (x, y) - d) * E.fB y = _
      have e : (fun y => (m.tS (x, y) - d) * E.fB y) =
          fun y => m.tS (x, y) * E.fB y - d * E.fB y := by ext; ring
      rw [e, intervalIntegral.integral_sub (hwd.tS_section x hx)
        (E.fB_intervalIntegrable.const_mul d), ms_constS]; rfl
    have hwd3 : m3.WellDefined :=
      { q_measurable := hqm
        tS_measurable := hwd.tS_measurable.sub measurable_const
        tB_measurable := hwd.tB_measurable.add measurable_const
        tS_integrable := hwd.tS_integrable.sub (integrable_const d)
        tB_integrable := hwd.tB_integrable.add (integrable_const c)
        tS_section := fun x hx => by
          show IntervalIntegrable (fun y => (m.tS (x, y) - d) * E.fB y) volume _ _
          have e : (fun y => (m.tS (x, y) - d) * E.fB y) =
              fun y => m.tS (x, y) * E.fB y - d * E.fB y := by ext; ring
          rw [e]; exact (hwd.tS_section x hx).sub (E.fB_intervalIntegrable.const_mul d)
        tB_section := fun y hy => by
          show IntervalIntegrable (fun x => (m.tB (x, y) + c) * E.fS x) volume _ _
          have e : (fun x => (m.tB (x, y) + c) * E.fS x) =
              fun x => m.tB (x, y) * E.fS x + c * E.fS x := by ext; ring
          rw [e]; exact (hwd.tB_section y hy).add (E.fS_intervalIntegrable.const_mul c) }
    have hadm3 : m3.Admissible := by
      refine ⟨hwd3, ⟨fun x hx x' hx' => ?_, fun y hy y' hy' => ?_⟩,
        ⟨fun x hx => ?_, fun y hy => ?_⟩⟩
      · have := hic.1 x hx x' hx'
        show m3.TS x' + (1 - m.QS x') * x ≤ m3.TS x + (1 - m.QS x) * x
        rw [TS3 x' hx', TS3 x hx]; linarith
      · have := hic.2 y hy y' hy'
        show m.QB y' * y - m3.TB y' ≤ m.QB y * y - m3.TB y
        rw [TB3 y' hy', TB3 y hy]; linarith
      · show x ≤ m3.TS x + (1 - m.QS x) * x
        rw [TS3 x hx]
        have h1 := ms_envS m hic hx
        have h2 : ∫ z in x..E.hiS, (1 - m.QS z) ≤ ∫ z in x..E.hiS, (1 : ℝ) :=
          intervalIntegral.integral_mono_on hx.2 ((ms_QS1_ii m hic).mono_set (by
              rw [uIcc_of_le hx.2, uIcc_of_le E.loS_lt_hiS.le]; exact Icc_subset_Icc hx.1 le_rfl))
            intervalIntegrable_const (fun z hz => by
              have := ms_QS_bd m hqm ⟨hx.1.trans hz.1, hz.2⟩; linarith)
        simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at h2
        unfold DirectMechanism.US at h1 hd
        linarith
      · show 0 ≤ m.QB y * y - m3.TB y
        rw [TB3 y hy]
        have h1 := ms_envB m hic hy
        have h2 : 0 ≤ ∫ z in E.loB..y, m.QB z := intervalIntegral.integral_nonneg hy.1
          (fun z hz => (ms_QB_bd m hqm ⟨hz.1, hz.2.trans hy.2⟩).1)
        unfold DirectMechanism.UB at h1 hc
        linarith
    have hs3 : m3.expectedSurplus = m.expectedSurplus + (c + d) := by
      unfold DirectMechanism.expectedSurplus
      have e : (fun θ => m3.tB θ - m3.tS θ) = fun θ => (m.tB θ - m.tS θ) + (c + d) := by
        ext θ; show (m.tB θ + c) - (m.tS θ - d) = _; ring
      have hi : Integrable (fun θ => m.tB θ - m.tS θ) E.prior :=
        hwd.tB_integrable.sub hwd.tS_integrable
      rw [e, integral_add hi (integrable_const _), integral_const]
      simp
    have h3 := hmax m3 hadm3
    have hc' : c = 0 := by linarith
    have hd' : d = 0 := by linarith
    refine ⟨?_, ?_, ?_⟩
    · have hopt := hmax (msOpt E) (ms_opt_adm hreg)
      have hido := ms_ident (msOpt E) (ms_opt_adm hreg)
      rw [ms_opt_UB, ms_opt_US] at hido
      have i1 := ms_int_qpsi (msOpt E) (ms_qs_meas E)
      have i2 := ms_int_qpsi m hqm
      have hint := i1.sub i2
      have hnn : 0 ≤ᵐ[E.prior] fun θ => (msOpt E).q θ * (E.psiB θ.2 - E.psiS θ.1) -
          m.q θ * (E.psiB θ.2 - E.psiS θ.1) := by
        filter_upwards [ms_ae_prior E] with θ hθ
        have := ms_profit_pt m hθ
        show 0 ≤ msQs E θ * _ - _
        rw [ms_opt_q hθ]; linarith
      have key : ∫ θ, ((msOpt E).q θ * (E.psiB θ.2 - E.psiS θ.1) -
          m.q θ * (E.psiB θ.2 - E.psiS θ.1)) ∂E.prior = 0 := by
        have hge := integral_nonneg_of_ae hnn
        rw [integral_sub i1 i2] at hge ⊢
        linarith
      have hae := (integral_eq_zero_iff_of_nonneg_ae hnn hint).mp key
      filter_upwards [hae, ms_ae_prior E] with θ h0 hθ hne
      have h0' : (msQs E θ - m.q θ) * (E.psiB θ.2 - E.psiS θ.1) = 0 := by
        have : (msOpt E).q θ * (E.psiB θ.2 - E.psiS θ.1) -
            m.q θ * (E.psiB θ.2 - E.psiS θ.1) = 0 := h0
        rw [← this]; show _ = msQs E θ * _ - _; ring
      rcases mul_eq_zero.mp h0' with h | h
      · rw [← ms_opt_q hθ]; linarith
      · exact absurd (sub_eq_zero.mp h) hne
    · intro y hy
      have h1 := ms_envB m hic hy
      unfold DirectMechanism.UB at h1 hc
      linarith
    · intro x hx
      have h1 := ms_envS m hic hx
      unfold DirectMechanism.US at h1 hd
      linarith
  · intro hq hTB hTS m' hm'
    have hUB : m.UB E.loB = 0 := by
      unfold DirectMechanism.UB; rw [hTB _ mB]; simp; ring
    have hUS : m.US E.hiS = E.hiS := by
      unfold DirectMechanism.US; rw [hTS _ mS]; simp
    have hid' := ms_ident m' hm'
    have hle : ∫ θ, m'.q θ * (E.psiB θ.2 - E.psiS θ.1) ∂E.prior ≤
        ∫ θ, m.q θ * (E.psiB θ.2 - E.psiS θ.1) ∂E.prior :=
      integral_mono_ae (ms_int_qpsi m' hm'.1.q_measurable) (ms_int_qpsi m hqm)
        (by filter_upwards [ms_ae_prior E] with θ hθ
            rw [hq θ hθ]; exact ms_profit_pt m' hθ)
    have r1 := hm'.2.2.2 _ mB
    have r2 := hm'.2.2.1 _ mS
    linarith


/-- shifting the seller's receipts up by a nonnegative constant keeps admissibility -/
noncomputable def msShiftS {E : Environment} (m : DirectMechanism E) (e : ℝ) : DirectMechanism E :=
  ⟨m.q, fun θ => m.tS θ + e, m.tB, m.q_mem⟩

lemma ms_shiftS_TS {E : Environment} (m : DirectMechanism E) (hwd : m.WellDefined) (e : ℝ)
    {x : ℝ} (hx : x ∈ Icc E.loS E.hiS) : (msShiftS m e).TS x = m.TS x + e := by
  show ∫ y in E.loB..E.hiB, (m.tS (x, y) + e) * E.fB y = _
  have h : (fun y => (m.tS (x, y) + e) * E.fB y) =
      fun y => m.tS (x, y) * E.fB y + e * E.fB y := by ext; ring
  rw [h, intervalIntegral.integral_add (hwd.tS_section x hx)
    (E.fB_intervalIntegrable.const_mul e), ms_constS]; rfl

lemma ms_shiftS_adm {E : Environment} (m : DirectMechanism E) (hm : m.Admissible) {e : ℝ}
    (he : 0 ≤ e) : (msShiftS m e).Admissible := by
  obtain ⟨hwd, hic, hir⟩ := hm
  have hwd' : (msShiftS m e).WellDefined :=
    { q_measurable := hwd.q_measurable
      tS_measurable := hwd.tS_measurable.add measurable_const
      tB_measurable := hwd.tB_measurable
      tS_integrable := hwd.tS_integrable.add (integrable_const e)
      tB_integrable := hwd.tB_integrable
      tS_section := fun x hx => by
        show IntervalIntegrable (fun y => (m.tS (x, y) + e) * E.fB y) volume _ _
        have h : (fun y => (m.tS (x, y) + e) * E.fB y) =
            fun y => m.tS (x, y) * E.fB y + e * E.fB y := by ext; ring
        rw [h]; exact (hwd.tS_section x hx).add (E.fB_intervalIntegrable.const_mul e)
      tB_section := hwd.tB_section }
  refine ⟨hwd', ⟨fun x hx x' hx' => ?_, hic.2⟩, ⟨fun x hx => ?_, hir.2⟩⟩
  · have := hic.1 x hx x' hx'
    show (msShiftS m e).TS x' + (1 - m.QS x') * x ≤ (msShiftS m e).TS x + (1 - m.QS x) * x
    rw [ms_shiftS_TS m hwd e hx', ms_shiftS_TS m hwd e hx]; linarith
  · have := hir.1 x hx
    show x ≤ (msShiftS m e).TS x + (1 - m.QS x) * x
    rw [ms_shiftS_TS m hwd e hx]; unfold DirectMechanism.US at this; linarith

lemma ms_shiftS_surplus {E : Environment} (m : DirectMechanism E) (hwd : m.WellDefined) (e : ℝ) :
    (msShiftS m e).expectedSurplus = m.expectedSurplus - e := by
  unfold DirectMechanism.expectedSurplus
  have h : (fun θ => (msShiftS m e).tB θ - (msShiftS m e).tS θ) =
      fun θ => (m.tB θ - m.tS θ) - e := by
    ext θ; show m.tB θ - (m.tS θ + e) = _; ring
  have hi : Integrable (fun θ => m.tB θ - m.tS θ) E.prior :=
    hwd.tB_integrable.sub hwd.tS_integrable
  rw [h, integral_sub hi (integrable_const _), integral_const]
  simp

lemma ms_u_psiS (x : ℝ) : uniformEnv.psiS x = 2 * x := by
  simp [Environment.psiS, Environment.cdfS, uniformEnv]; ring

lemma ms_u_psiB (y : ℝ) : uniformEnv.psiB y = 2 * y - 1 := by
  simp [Environment.psiB, Environment.cdfB, uniformEnv]; ring

lemma ms_u_reg : uniformEnv.Regular := by
  refine ⟨fun a _ b _ h => ?_, fun a _ b _ h => ?_⟩
  · rw [ms_u_psiS, ms_u_psiS]; linarith
  · rw [ms_u_psiB, ms_u_psiB]; linarith

theorem ms_uprof_false : ¬ ((∃ m : DirectMechanism uniformEnv, m.Admissible ∧
      ∀ m' : DirectMechanism uniformEnv, m'.Admissible →
        m'.expectedSurplus ≤ m.expectedSurplus) ∧
    ∀ m : DirectMechanism uniformEnv, m.Admissible →
      ((∀ m' : DirectMechanism uniformEnv, m'.Admissible →
          m'.expectedSurplus ≤ m.expectedSurplus) ↔
        ∀ᵐ θ ∂uniformEnv.prior, m.q θ = if (1 : ℝ) / 2 < θ.2 - θ.1 then 1 else 0)) := by
  intro H
  have hopt : (msOpt uniformEnv).Admissible := ms_opt_adm ms_u_reg
  set m' := msShiftS (msOpt uniformEnv) 1 with hm'
  have hadm : m'.Admissible := ms_shiftS_adm _ hopt zero_le_one
  have hae : ∀ᵐ θ ∂uniformEnv.prior, m'.q θ = if (1 : ℝ) / 2 < θ.2 - θ.1 then 1 else 0 := by
    filter_upwards [ms_ae_prior uniformEnv] with θ hθ
    show msQs uniformEnv θ = _
    rw [ms_opt_q hθ]
    unfold profitRule
    rw [ms_u_psiS, ms_u_psiB]
    have : (2 * θ.1 < 2 * θ.2 - 1) ↔ ((1 : ℝ) / 2 < θ.2 - θ.1) := by
      constructor <;> intro h <;> linarith
    simp only [this]
  have hmax := ((H.2 m' hadm).mpr hae) (msOpt uniformEnv) hopt
  rw [hm', ms_shiftS_surplus _ hopt.1] at hmax
  linarith

end MechanismDesign.BilateralTrade

open MechanismDesign.BilateralTrade


theorem solution : ¬ ((∃ m : DirectMechanism uniformEnv, m.Admissible ∧
      ∀ m' : DirectMechanism uniformEnv, m'.Admissible →
        m'.expectedSurplus ≤ m.expectedSurplus) ∧
    ∀ m : DirectMechanism uniformEnv, m.Admissible →
      ((∀ m' : DirectMechanism uniformEnv, m'.Admissible →
          m'.expectedSurplus ≤ m.expectedSurplus) ↔
        ∀ᵐ θ ∂uniformEnv.prior, m.q θ = if (1 : ℝ) / 2 < θ.2 - θ.1 then 1 else 0)) :=
  ms_uprof_false
