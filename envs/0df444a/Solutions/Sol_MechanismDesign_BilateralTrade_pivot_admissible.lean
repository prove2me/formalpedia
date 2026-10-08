-- Prove2me | solution 1 for MechanismDesign.BilateralTrade.pivot_admissible
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T08:15:41.501679+00:00
-- url     : https://prove2.me/submissions/ec1d7af9-90cd-420c-bb1f-e9c178f4e01a

import Mathlib
import Definitions.Def_MechanismDesign_BilateralTrade_Model

open MeasureTheory


namespace MechanismDesign.BilateralTrade
open Set

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

end MechanismDesign.BilateralTrade

open MechanismDesign.BilateralTrade


theorem solution (E : Environment) (q : ℝ × ℝ → ℝ) (hq : IsFirstBestRule E q)
    (hqm : Measurable q) :
    (pivot E q hq).Admissible := by
  exact ms_piv_adm hq hqm
