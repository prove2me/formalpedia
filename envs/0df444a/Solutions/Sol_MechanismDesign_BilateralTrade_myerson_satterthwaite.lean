-- Prove2me | solution 1 for MechanismDesign.BilateralTrade.myerson_satterthwaite
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T08:20:22.364474+00:00
-- url     : https://prove2.me/submissions/e34490e7-735a-4db9-b3e4-0f6b86f65002

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

end MechanismDesign.BilateralTrade

open MechanismDesign.BilateralTrade


theorem solution (E : Environment) :
    (∃ m : DirectMechanism E, m.Admissible ∧ m.ExPostBB ∧ IsFirstBestRule E m.q) ↔
      (E.hiS ≤ E.loB ∨ E.hiB ≤ E.loS) := by
  exact ms_main E
