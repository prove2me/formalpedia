-- Prove2me | solution 1 for NagaevLD.FukNagaev.corollary_1_8
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T22:04:43.250493+00:00
-- url     : https://prove2.me/submissions/844b2f4d-6e0c-4cd3-a1e5-62ec217e062f

import Mathlib
import Definitions.Def_NagaevLD_FukNagaev_Setting



namespace NagaevLD.FukNagaev

open MeasureTheory ProbabilityTheory

open MeasureTheory ProbabilityTheory

theorem fn_eq_1_8_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (X : Fin n → Ω → ℝ) (x : ℝ) (yv : Fin n → ℝ) :
    P.real {ω | x ≤ S n X ω} ≤
      P.real {ω | x ≤ St X yv ω} + ∑ i, P.real {ω | yv i < X i ω} := by
  have hsub : {ω | x ≤ S n X ω} ⊆ {ω | x ≤ St X yv ω} ∪ ⋃ i, {ω | yv i < X i ω} := by
    intro ω hω
    by_cases hall : ∀ i, X i ω ≤ yv i
    · left
      have : St X yv ω = S n X ω := by
        unfold St S Xt
        exact Finset.sum_congr rfl (fun i _ => if_pos (hall i))
      simp only [Set.mem_setOf_eq] at hω ⊢; rw [this]; exact hω
    · right
      push_neg at hall
      obtain ⟨i, hi⟩ := hall
      exact Set.mem_iUnion.2 ⟨i, hi⟩
  calc P.real {ω | x ≤ S n X ω}
      ≤ P.real ({ω | x ≤ St X yv ω} ∪ ⋃ i, {ω | yv i < X i ω}) := measureReal_mono hsub
    _ ≤ P.real {ω | x ≤ St X yv ω} + P.real (⋃ i, {ω | yv i < X i ω}) :=
        measureReal_union_le _ _
    _ ≤ _ := add_le_add le_rfl (measureReal_iUnion_fintype_le _)

lemma Xt_le {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) (yv : Fin n → ℝ) (hyv : ∀ i, 0 < yv i)
    (i : Fin n) (ω : Ω) : Xt X yv i ω ≤ yv i := by
  unfold Xt; split_ifs with h
  · exact h
  · exact (hyv i).le

lemma Xt_measurable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (X : Fin n → Ω → ℝ)
    (hmeas : ∀ i, Measurable (X i)) (yv : Fin n → ℝ) (i : Fin n) : Measurable (Xt X yv i) := by
  unfold Xt
  exact Measurable.ite (measurableSet_le (hmeas i) measurable_const) (hmeas i) measurable_const

lemma Xt_indep {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {n : ℕ} (X : Fin n → Ω → ℝ) (hindep : iIndepFun X P) (yv : Fin n → ℝ) :
    iIndepFun (fun i => Xt X yv i) P := by
  have := hindep.comp (fun i (u : ℝ) => if u ≤ yv i then u else 0)
    (fun i => Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_id
      measurable_const)
  exact this

lemma exp_Xt_integrable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (X : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (yv : Fin n → ℝ)
    (hyv : ∀ i, 0 < yv i) (h : ℝ) (hh : 0 ≤ h) (i : Fin n) :
    Integrable (fun ω => Real.exp (h * Xt X yv i ω)) P := by
  refine Integrable.of_bound (C := Real.exp (h * yv i))
    (((Xt_measurable X hmeas yv i).const_mul h).exp.aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall (fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
  exact mul_le_mul_of_nonneg_left (Xt_le X yv hyv i ω) hh

theorem fn_eq_1_9_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (X : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (x : ℝ) (yv : Fin n → ℝ) (hyv : ∀ i, 0 < yv i)
    (h : ℝ) (hh : 0 < h) :
    P.real {ω | x ≤ St X yv ω} ≤ Real.exp (-h * x) * ∫ ω, Real.exp (h * St X yv ω) ∂P ∧
      Real.exp (-h * x) * ∫ ω, Real.exp (h * St X yv ω) ∂P =
        Real.exp (-h * x) * ∏ i, ∫ ω, Real.exp (h * Xt X yv i ω) ∂P := by
  have hS : (fun ω => St X yv ω) = ∑ i, Xt X yv i := by
    funext ω; simp [St, Finset.sum_apply]
  have hXm := Xt_measurable X hmeas yv
  have hind := Xt_indep P X hindep yv
  have hI := hind.integrable_exp_mul_sum (t := h) hXm (s := Finset.univ)
    (fun i _ => exp_Xt_integrable P X hmeas yv hyv h hh.le i)
  have h1 := measure_ge_le_exp_mul_mgf (μ := P) (X := ∑ i, Xt X yv i) x hh.le hI
  have h2 := hind.mgf_sum hXm (t := h) Finset.univ
  have e : {ω | x ≤ St X yv ω} = {ω | x ≤ (∑ i, Xt X yv i) ω} := by rw [← hS]
  have e2 : ∫ ω, Real.exp (h * St X yv ω) ∂P = mgf (∑ i, Xt X yv i) P h := by
    rw [mgf]; congr 1; funext ω; rw [← hS]
  refine ⟨?_, ?_⟩
  · rw [e, e2]; exact h1
  · rw [e2, h2]; rfl

theorem fn_cond_1_4_iff_core (t : ℝ) (ht : 2 ≤ t) (α β : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (hβ : β = 1 - α) (x : ℝ) (hx : 0 < x) (y : ℝ) (hy0 : 0 < y) (B A : ℝ) (hB : 0 < B)
    (hA : 0 < A) :
    cond_1_4 t α β x y B A ↔
      α * x / (Real.exp t * B) ≤
        max (t / y) (1 / y * Real.log (β * x * y ^ (t - 1) / A + 1)) := by
  unfold cond_1_4
  have hA' : A ≠ 0 := hA.ne'
  have e : max (t / y) (1 / y * Real.log (β * x * y ^ (t - 1) / A + 1)) =
      max t (Real.log (β * x * y ^ (t - 1) / A + 1)) / y := by
    rw [show 1 / y * Real.log (β * x * y ^ (t - 1) / A + 1) = Real.log (β * x * y ^ (t - 1) / A + 1) / y by ring]
    exact max_div_div_right hy0.le _ _
  rw [e, le_div_iff₀ hy0]
  have e2 : α * x * y / (Real.exp t * B) = α * x / (Real.exp t * B) * y := by ring
  rw [e2]
  constructor
  · rintro (h | h)
    · exact absurd h hA'
    · exact h
  · intro h; exact Or.inr h


open MeasureTheory ProbabilityTheory

lemma fn_exp_quad_neg (u : ℝ) (hu : u ≤ 0) : Real.exp u - 1 - u ≤ u ^ 2 / 2 := by
  let ψ : ℝ → ℝ := fun v => 1 + v + v ^ 2 / 2 - Real.exp v
  have hd : ∀ v, HasDerivAt ψ (1 + v - Real.exp v) v := by
    intro v
    have := (((hasDerivAt_id' v).const_add 1).add ((hasDerivAt_pow 2 v).div_const 2)).sub
      (Real.hasDerivAt_exp v)
    exact this.congr_deriv (by norm_num <;> ring)
  have hanti : AntitoneOn ψ (Set.Iic 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Iic 0)
    · exact fun v _ => (hd v).continuousAt.continuousWithinAt
    · exact fun v _ => (hd v).differentiableAt.differentiableWithinAt
    · intro v _
      rw [(hd v).deriv]
      have := Real.add_one_le_exp v
      linarith
  have := hanti (Set.mem_Iic.2 hu) (Set.mem_Iic.2 le_rfl) hu
  simp only [ψ, Real.exp_zero] at this
  linarith

lemma fn_exp_quad_pos (u : ℝ) (hu : 0 ≤ u) : Real.exp u - 1 - u ≤ Real.exp u * u ^ 2 / 2 := by
  let k : ℝ → ℝ := fun v => v ^ 2 / 2 - 1 + (1 + v) * Real.exp (-v)
  have hd : ∀ v, HasDerivAt k (v - v * Real.exp (-v)) v := by
    intro v
    have h1 := ((hasDerivAt_pow 2 v).div_const 2).sub_const 1
    have h2 := ((hasDerivAt_id' v).const_add 1).mul ((hasDerivAt_neg v).exp)
    exact (h1.add h2).congr_deriv (by norm_num <;> ring)
  have hmono : MonotoneOn k (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun v _ => (hd v).continuousAt.continuousWithinAt
    · exact fun v _ => (hd v).differentiableAt.differentiableWithinAt
    · intro v hv
      rw [interior_Ici] at hv
      rw [(hd v).deriv]
      have hv' : 0 < v := hv
      have : Real.exp (-v) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      nlinarith
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hu) hu
  simp only [k, neg_zero, Real.exp_zero] at this
  have he : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos u
  nlinarith

lemma fn_exp_quad_le (t u : ℝ) (ht : 0 ≤ t) (hu : u ≤ t) :
    Real.exp u - 1 - u ≤ Real.exp t * u ^ 2 / 2 := by
  rcases le_total u 0 with h | h
  · have := fn_exp_quad_neg u h
    have : 1 ≤ Real.exp t := Real.one_le_exp ht
    nlinarith [sq_nonneg u]
  · have := fn_exp_quad_pos u h
    have : Real.exp u ≤ Real.exp t := Real.exp_le_exp.2 hu
    nlinarith [sq_nonneg u]

lemma fn_g_mono (t : ℝ) (ht : 0 < t) (v w : ℝ) (hv : t ≤ v) (hvw : v ≤ w) :
    (Real.exp v - 1 - v) / v ^ t ≤ (Real.exp w - 1 - w) / w ^ t := by
  let g : ℝ → ℝ := fun z => (Real.exp z - 1 - z) / z ^ t
  have hd : ∀ z, 0 < z → HasDerivAt g
      (((Real.exp z - 1) * z ^ t - (Real.exp z - 1 - z) * (t * z ^ (t - 1))) / (z ^ t) ^ 2) z := by
    intro z hz
    have h1 := ((Real.hasDerivAt_exp z).sub_const 1).sub (hasDerivAt_id' z)
    have h2 := Real.hasDerivAt_rpow_const (x := z) (p := t) (Or.inl hz.ne')
    exact h1.div h2 (Real.rpow_pos_of_pos hz t).ne'
  have hmono : MonotoneOn g (Set.Ici t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici t)
    · exact fun z hz => (hd z (lt_of_lt_of_le ht hz)).continuousAt.continuousWithinAt
    · intro z hz
      rw [interior_Ici] at hz
      exact (hd z (lt_trans ht hz)).differentiableAt.differentiableWithinAt
    · intro z hz
      rw [interior_Ici] at hz
      have hz' : t < z := hz
      have hz0 : 0 < z := lt_trans ht hz'
      rw [(hd z hz0).deriv]
      apply div_nonneg _ (sq_nonneg _)
      have hzt : z ^ t = z * z ^ (t - 1) := by
        rw [← Real.rpow_one_add' hz0.le (by linarith)]; congr 1; ring
      rw [hzt]
      have hp : 0 < z ^ (t - 1) := Real.rpow_pos_of_pos hz0 _
      have hq : 0 ≤ Real.exp z - 1 - z := by linarith [Real.add_one_le_exp z]
      have hr : t * (Real.exp z - 1 - z) ≤ z * (Real.exp z - 1) := by
        have : 0 ≤ Real.exp z - 1 := by linarith [Real.add_one_le_exp z]
        nlinarith
      have : 0 ≤ (z * (Real.exp z - 1) - t * (Real.exp z - 1 - z)) * z ^ (t - 1) :=
        mul_nonneg (by linarith) hp.le
      nlinarith
  exact hmono (Set.mem_Ici.2 hv) (Set.mem_Ici.2 (le_trans hv hvw)) hvw

lemma fn_g_mono_h (t : ℝ) (ht : 0 < t) (h : ℝ) (hh : 0 < h) (u b : ℝ) (hu : t / h ≤ u)
    (hub : u ≤ b) :
    Real.exp (h * u) - 1 - h * u ≤ u ^ t * ((Real.exp (h * b) - 1 - h * b) / b ^ t) := by
  have hu0 : 0 < u := lt_of_lt_of_le (div_pos ht hh) hu
  have hb0 : 0 < b := lt_of_lt_of_le hu0 hub
  have hv : t ≤ h * u := by rw [div_le_iff₀ hh] at hu; linarith
  have := fn_g_mono t ht (h * u) (h * b) hv (mul_le_mul_of_nonneg_left hub hh.le)
  rw [Real.mul_rpow hh.le hu0.le, Real.mul_rpow hh.le hb0.le] at this
  have hht : 0 < h ^ t := Real.rpow_pos_of_pos hh t
  have hut : 0 < u ^ t := Real.rpow_pos_of_pos hu0 t
  have hbt : 0 < b ^ t := Real.rpow_pos_of_pos hb0 t
  rw [div_le_div_iff₀ (mul_pos hht hut) (mul_pos hht hbt)] at this
  rw [mul_div_assoc', le_div_iff₀ hbt]
  nlinarith

/-- `X ≤ b` almost surely. -/
lemma fn_ae_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) (b : ℝ)
    (hXb : P {ω | b < X ω} = 0) : ∀ᵐ ω ∂P, X ω ≤ b := by
  rw [ae_iff]; simpa [not_le] using hXb

lemma fn_part2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Measurable X) (t : ℝ) (ht : 0 ≤ t)
    (hL2 : MemLp X 2 P) (h : ℝ) (hh : 0 < h) :
    ∫ ω in {ω | X ω ≤ t / h}, (Real.exp (h * X ω) - 1 - h * X ω) ∂P ≤
        Real.exp t * (∫ ω, X ω ^ 2 ∂P) * h ^ 2 / 2 := by
  have hs : MeasurableSet {ω | X ω ≤ t / h} := measurableSet_le hX measurable_const
  have hsq : Integrable (fun ω => X ω ^ 2) P := hL2.integrable_sq
  have hG : Integrable (fun ω => Real.exp t * h ^ 2 / 2 * X ω ^ 2) P := hsq.const_mul _
  calc ∫ ω in {ω | X ω ≤ t / h}, (Real.exp (h * X ω) - 1 - h * X ω) ∂P
      ≤ ∫ ω in {ω | X ω ≤ t / h}, Real.exp t * h ^ 2 / 2 * X ω ^ 2 ∂P := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall (fun ω => by
            have := Real.add_one_le_exp (h * X ω); simp only [Pi.zero_apply]; linarith)
        · exact hG.integrableOn
        · refine (ae_restrict_iff' hs).2 (Filter.Eventually.of_forall (fun ω hω => ?_))
          have hω' : X ω ≤ t / h := hω
          have hu : h * X ω ≤ t := by rw [le_div_iff₀ hh] at hω'; linarith
          have := fn_exp_quad_le t (h * X ω) ht hu
          calc _ ≤ _ := this
            _ = _ := by ring
    _ ≤ ∫ ω, Real.exp t * h ^ 2 / 2 * X ω ^ 2 ∂P :=
        setIntegral_le_integral hG (Filter.Eventually.of_forall (fun ω => by
          simp only [Pi.zero_apply]; positivity))
    _ = Real.exp t * (∫ ω, X ω ^ 2 ∂P) * h ^ 2 / 2 := by
        rw [integral_const_mul]; ring

theorem fn_eq_1_13_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Measurable X) (b : ℝ) (hb : 0 < b) (hXb : P {ω | b < X ω} = 0)
    (t : ℝ) (ht : 2 ≤ t)
    (hL2 : MemLp X 2 P) (h : ℝ) (hh : 0 < h) (hht : h ≤ t / b) :
    ∫ ω in {ω | X ω ≤ b}, (Real.exp (h * X ω) - 1 - h * X ω) ∂P ≤
        ∫ ω in {ω | X ω ≤ t / h}, (Real.exp (h * X ω) - 1 - h * X ω) ∂P ∧
      ∫ ω in {ω | X ω ≤ t / h}, (Real.exp (h * X ω) - 1 - h * X ω) ∂P ≤
        Real.exp t * (∫ ω, X ω ^ 2 ∂P) * h ^ 2 / 2 := by
  refine ⟨le_of_eq ?_, fn_part2 P X hX t (by linarith) hL2 h hh⟩
  have hbt : b ≤ t / h := by
    rw [le_div_iff₀ hh]; rw [le_div_iff₀ hb] at hht; linarith
  apply setIntegral_congr_set
  rw [Filter.eventuallyEq_set]
  filter_upwards [fn_ae_le P X b hXb] with ω hω
  exact ⟨fun _ => le_trans hω hbt, fun _ => hω⟩

lemma fn_log_mgf_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Measurable X) (b : ℝ) (hXb : P {ω | b < X ω} = 0)
    (hint : Integrable X P) (h : ℝ) (hh : 0 ≤ h) (K : ℝ)
    (hK : ∫ ω, (Real.exp (h * X ω) - 1 - h * X ω) ∂P ≤ K) :
    Real.log (∫ ω, Real.exp (h * X ω) ∂P) ≤ h * (∫ ω, X ω ∂P) + K ∧
      Integrable (fun ω => Real.exp (h * X ω)) P := by
  have hE : Integrable (fun ω => Real.exp (h * X ω)) P := by
    refine Integrable.of_bound (C := Real.exp (h * b)) ((hX.const_mul h).exp.aestronglyMeasurable) ?_
    filter_upwards [fn_ae_le P X b hXb] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
    exact mul_le_mul_of_nonneg_left hω hh
  refine ⟨?_, hE⟩
  have hM : 0 < ∫ ω, Real.exp (h * X ω) ∂P := integral_exp_pos hE
  have hsplit : ∫ ω, (Real.exp (h * X ω) - 1 - h * X ω) ∂P =
      (∫ ω, Real.exp (h * X ω) ∂P) - 1 - h * ∫ ω, X ω ∂P := by
    have i1 : Integrable (fun ω => Real.exp (h * X ω) - 1) P := hE.sub (integrable_const _)
    have i2 : Integrable (fun ω => h * X ω) P := hint.const_mul h
    rw [integral_sub i1 i2, integral_sub hE (integrable_const _), integral_const_mul]
    simp
  have := Real.log_le_sub_one_of_pos hM
  linarith

theorem fn_lemma_1_4_a_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Measurable X) (b : ℝ) (hb : 0 < b) (hXb : P {ω | b < X ω} = 0)
    (t : ℝ) (ht : 2 ≤ t)
    (hL2 : MemLp X 2 P) (h : ℝ) (hh : 0 < h) (hht : h ≤ t / b) :
    Real.log (∫ ω, Real.exp (h * X ω) ∂P) ≤
      h * (∫ ω, X ω ∂P) + Real.exp t * (∫ ω, X ω ^ 2 ∂P) * h ^ 2 / 2 := by
  refine (fn_log_mgf_le P X hX b hXb (hL2.integrable one_le_two) h hh.le _ ?_).1
  obtain ⟨h1, h2⟩ := fn_eq_1_13_core P X hX b hb hXb t ht hL2 h hh hht
  refine le_trans (le_of_eq ?_) (le_trans h1 h2)
  rw [← setIntegral_univ]
  apply setIntegral_congr_set
  rw [Filter.eventuallyEq_set]
  filter_upwards [fn_ae_le P X b hXb] with ω hω
  simp [hω]

theorem fn_eq_1_16_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Measurable X) (b : ℝ) (hb : 0 < b) (hXb : P {ω | b < X ω} = 0)
    (t : ℝ) (ht : 2 ≤ t)
    (h : ℝ) (hht : t / b < h) :
    ∫ ω in {ω | t / h < X ω}, (Real.exp (h * X ω) - 1 - h * X ω) ∂P ≤
      (∫ ω in {ω | 0 ≤ X ω}, X ω ^ t ∂P) * (Real.exp (h * b) - 1 - h * b) / b ^ t := by
  have ht0 : 0 < t := by linarith
  have hh : 0 < h := lt_trans (div_pos ht0 hb) hht
  set c := (Real.exp (h * b) - 1 - h * b) / b ^ t with hc
  have hc0 : 0 ≤ c := by
    apply div_nonneg _ (Real.rpow_pos_of_pos hb t).le
    linarith [Real.add_one_le_exp (h * b)]
  have hs : MeasurableSet {ω | t / h < X ω} := measurableSet_lt measurable_const hX
  have hs0 : MeasurableSet {ω | 0 ≤ X ω} := measurableSet_le measurable_const hX
  have hGm : Measurable (fun ω => X ω ^ t * c) := (hX.pow_const t).mul_const c
  have hae := fn_ae_le P X b hXb
  have hGint : IntegrableOn (fun ω => X ω ^ t * c) {ω | 0 ≤ X ω} P := by
    refine Integrable.of_bound (C := b ^ t * c) hGm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem hs0] with ω hω hω0
    have hω0' : 0 ≤ X ω := hω0
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hω0' t) hc0)]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hω0' hω ht0.le) hc0
  have hsub : {ω | t / h < X ω} ⊆ {ω | 0 ≤ X ω} := by
    intro ω hω
    have : t / h < X ω := hω
    exact le_of_lt (lt_trans (div_pos ht0 hh) this)
  calc ∫ ω in {ω | t / h < X ω}, (Real.exp (h * X ω) - 1 - h * X ω) ∂P
      ≤ ∫ ω in {ω | t / h < X ω}, X ω ^ t * c ∂P := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall (fun ω => by
            have := Real.add_one_le_exp (h * X ω); simp only [Pi.zero_apply]; linarith)
        · exact hGint.mono_set hsub
        · filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem hs] with ω hω hω1
          exact fn_g_mono_h t ht0 h hh (X ω) b (le_of_lt hω1) hω
    _ ≤ ∫ ω in {ω | 0 ≤ X ω}, X ω ^ t * c ∂P := by
        apply setIntegral_mono_set hGint
        · filter_upwards [ae_restrict_mem hs0] with ω hω0
          exact mul_nonneg (Real.rpow_nonneg hω0 t) hc0
        · exact hsub.eventuallyLE
    _ = (∫ ω in {ω | 0 ≤ X ω}, X ω ^ t ∂P) * (Real.exp (h * b) - 1 - h * b) / b ^ t := by
        rw [integral_mul_const, hc, mul_div_assoc]

theorem fn_lemma_1_4_b_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Measurable X) (b : ℝ) (hb : 0 < b) (hXb : P {ω | b < X ω} = 0)
    (t : ℝ) (ht : 2 ≤ t)
    (hL2 : MemLp X 2 P) (h : ℝ) (hht : t / b < h) :
    Real.log (∫ ω, Real.exp (h * X ω) ∂P) ≤
      h * (∫ ω, X ω ∂P) + Real.exp t * (∫ ω, X ω ^ 2 ∂P) * h ^ 2 / 2 +
        (∫ ω in {ω | 0 ≤ X ω}, X ω ^ t ∂P) * (Real.exp (h * b) - 1 - h * b) / b ^ t := by
  have ht0 : 0 < t := by linarith
  have hh : 0 < h := lt_trans (div_pos ht0 hb) hht
  have hint := hL2.integrable one_le_two
  have hE := (fn_log_mgf_le P X hX b hXb hint h hh.le _ le_rfl).2
  have hFint : Integrable (fun ω => Real.exp (h * X ω) - 1 - h * X ω) P :=
    (hE.sub (integrable_const _)).sub (hint.const_mul h)
  have hs : MeasurableSet {ω | X ω ≤ t / h} := measurableSet_le hX measurable_const
  have hc : {ω | X ω ≤ t / h}ᶜ = {ω | t / h < X ω} := by ext ω; simp [not_le]
  have key := (fn_log_mgf_le P X hX b hXb hint h hh.le
    (Real.exp t * (∫ ω, X ω ^ 2 ∂P) * h ^ 2 / 2 +
      (∫ ω in {ω | 0 ≤ X ω}, X ω ^ t ∂P) * (Real.exp (h * b) - 1 - h * b) / b ^ t) (by
    rw [← integral_add_compl hs hFint, hc]
    exact add_le_add (fn_part2 P X hX t ht0.le hL2 h hh)
      (fn_eq_1_16_core P X hX b hb hXb t ht h hht))).1
  linarith


lemma fn_g_mono_h' (t : ℝ) (ht : 0 < t) (h : ℝ) (hh : 0 < h) (u w : ℝ) (hu : t / h ≤ u)
    (huw : u ≤ w) :
    (Real.exp (h * u) - 1 - h * u) / u ^ t ≤ (Real.exp (h * w) - 1 - h * w) / w ^ t := by
  have hu0 : 0 < u := lt_of_lt_of_le (div_pos ht hh) hu
  have := fn_g_mono_h t ht h hh u w hu huw
  rw [div_le_iff₀ (Real.rpow_pos_of_pos hu0 t)]
  linarith

lemma Xt_eq_indicator {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) (yv : Fin n → ℝ) (i : Fin n) :
    Xt X yv i = {ω | X i ω ≤ yv i}.indicator (X i) := by
  funext ω; unfold Xt Set.indicator; rfl

lemma Xt_sq_eq_indicator {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) (yv : Fin n → ℝ) (i : Fin n) :
    (fun ω => Xt X yv i ω ^ 2) = {ω | X i ω ≤ yv i}.indicator (fun ω => X i ω ^ 2) := by
  funext ω; by_cases h1 : X i ω ≤ yv i <;> simp [Xt, Set.indicator, h1]

lemma Xt_rpow_eq {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) (yv : Fin n → ℝ) (i : Fin n) (t : ℝ)
    (ht : 0 < t) :
    {ω | 0 ≤ Xt X yv i ω}.indicator (fun ω => Xt X yv i ω ^ t) =
      {ω | 0 ≤ X i ω ∧ X i ω ≤ yv i}.indicator (fun ω => |X i ω| ^ t) := by
  funext ω
  unfold Set.indicator Xt
  by_cases h1 : X i ω ≤ yv i
  · by_cases h2 : 0 ≤ X i ω
    · simp [h1, h2, abs_of_nonneg h2]
    · simp [h1, h2]
  · simp [h1, Real.zero_rpow ht.ne']

lemma fn_summand_facts {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (X : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (yv : Fin n → ℝ)
    (hyv : ∀ i, 0 < yv i) (t : ℝ) (ht : 0 < t)
    (hL2 : ∀ i, IntegrableOn (fun ω => X i ω ^ 2) {ω | X i ω ≤ yv i} P) (i : Fin n) :
    P {ω | yv i < Xt X yv i ω} = 0 ∧ MemLp (Xt X yv i) 2 P ∧
      ∫ ω, Xt X yv i ω ∂P = ∫ ω in {ω | X i ω ≤ yv i}, X i ω ∂P ∧
      ∫ ω, Xt X yv i ω ^ 2 ∂P = ∫ ω in {ω | X i ω ≤ yv i}, X i ω ^ 2 ∂P ∧
      ∫ ω in {ω | 0 ≤ Xt X yv i ω}, Xt X yv i ω ^ t ∂P =
        ∫ ω in {ω | 0 ≤ X i ω ∧ X i ω ≤ yv i}, |X i ω| ^ t ∂P := by
  have hs : MeasurableSet {ω | X i ω ≤ yv i} := measurableSet_le (hmeas i) measurable_const
  have hm := Xt_measurable X hmeas yv i
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have : {ω | yv i < Xt X yv i ω} = ∅ := by
      ext ω; simp only [Set.mem_empty_iff_false, iff_false]
      exact fun hω => absurd hω (not_lt.2 (Xt_le X yv hyv i ω))
    rw [this, measure_empty]
  · rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable, Xt_sq_eq_indicator]
    exact (hL2 i).integrable_indicator hs
  · rw [Xt_eq_indicator, integral_indicator hs]
  · rw [Xt_sq_eq_indicator, integral_indicator hs]
  · have hs1 : MeasurableSet {ω | 0 ≤ Xt X yv i ω} := measurableSet_le measurable_const hm
    have hs2 : MeasurableSet {ω | 0 ≤ X i ω ∧ X i ω ≤ yv i} :=
      (measurableSet_le measurable_const (hmeas i)).inter hs
    rw [← integral_indicator hs1, ← integral_indicator hs2, Xt_rpow_eq X yv i t ht]

lemma fn_prod_bound {n : ℕ} (M c : Fin n → ℝ) (hM : ∀ i, 0 < M i)
    (hc : ∀ i, Real.log (M i) ≤ c i) (p hx : ℝ) (hp : p ≤ Real.exp hx * ∏ i, M i) :
    p ≤ Real.exp (hx + ∑ i, c i) := by
  refine le_trans hp ?_
  rw [Real.exp_add, Real.exp_sum]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply Finset.prod_le_prod (fun i _ => (hM i).le)
  intro i _
  rw [← Real.log_le_iff_le_exp (hM i)]; exact hc i

theorem fn_eq_1_17_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (X : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (x : ℝ) (yv : Fin n → ℝ) (hyv : ∀ i, 0 < yv i)
    (y : ℝ) (hyy : ∀ i, yv i ≤ y)
    (t : ℝ) (ht : 2 ≤ t)
    (hL2 : ∀ i, IntegrableOn (fun ω => X i ω ^ 2) {ω | X i ω ≤ yv i} P)
    (h : ℝ) (hh : 0 < h) (hht : h ≤ t / y) :
    P.real {ω | x ≤ St X yv ω} ≤
      Real.exp (h * (muY P X yv - x) + 1 / 2 * Real.exp t * B2Y P X yv * h ^ 2) := by
  have ht0 : 0 < t := by linarith
  have h9 := (fn_eq_1_9_core P X hmeas hindep x yv hyv h hh).1
  rw [(fn_eq_1_9_core P X hmeas hindep x yv hyv h hh).2] at h9
  have hb := fun i => fn_summand_facts P X hmeas yv hyv t ht0 hL2 i
  have key := fn_prod_bound (fun i => ∫ ω, Real.exp (h * Xt X yv i ω) ∂P)
    (fun i => h * (∫ ω in {ω | X i ω ≤ yv i}, X i ω ∂P) +
      Real.exp t * (∫ ω in {ω | X i ω ≤ yv i}, X i ω ^ 2 ∂P) * h ^ 2 / 2)
    (fun i => integral_exp_pos (exp_Xt_integrable P X hmeas yv hyv h hh.le i))
    (fun i => by
      obtain ⟨h1, h2, h3, h4, -⟩ := hb i
      have hti : h ≤ t / yv i :=
        le_trans hht (div_le_div_of_nonneg_left ht0.le (hyv i) (hyy i))
      have := fn_lemma_1_4_a_core P (Xt X yv i) (Xt_measurable X hmeas yv i) (yv i) (hyv i) h1
        t ht h2 h hh hti
      rw [h3, h4] at this; exact this) _ _ h9
  refine le_trans key (le_of_eq ?_)
  congr 1
  unfold muY B2Y
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div, ← Finset.sum_mul,
    ← Finset.mul_sum]
  ring

theorem fn_eq_1_18_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (X : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (x : ℝ) (yv : Fin n → ℝ) (hyv : ∀ i, 0 < yv i)
    (y : ℝ) (hyy : ∀ i, yv i ≤ y)
    (t : ℝ) (ht : 2 ≤ t)
    (hL2 : ∀ i, IntegrableOn (fun ω => X i ω ^ 2) {ω | X i ω ≤ yv i} P)
    (h : ℝ) (hy0 : 0 < y) (hht : t / y < h) :
    P.real {ω | x ≤ St X yv ω} ≤
      Real.exp (h * (muY P X yv - x) + 1 / 2 * Real.exp t * B2Y P X yv * h ^ 2 +
        (Real.exp (h * y) - 1 - h * y) / y ^ t * AY P X yv t) := by
  have ht0 : 0 < t := by linarith
  have hh : 0 < h := lt_trans (div_pos ht0 hy0) hht
  have h9 := (fn_eq_1_9_core P X hmeas hindep x yv hyv h hh).1
  rw [(fn_eq_1_9_core P X hmeas hindep x yv hyv h hh).2] at h9
  have hb := fun i => fn_summand_facts P X hmeas yv hyv t ht0 hL2 i
  set cy := (Real.exp (h * y) - 1 - h * y) / y ^ t with hcy
  have hcy0 : 0 ≤ cy := by
    apply div_nonneg _ (Real.rpow_pos_of_pos hy0 t).le
    linarith [Real.add_one_le_exp (h * y)]
  have key := fn_prod_bound (fun i => ∫ ω, Real.exp (h * Xt X yv i ω) ∂P)
    (fun i => h * (∫ ω in {ω | X i ω ≤ yv i}, X i ω ∂P) +
      Real.exp t * (∫ ω in {ω | X i ω ≤ yv i}, X i ω ^ 2 ∂P) * h ^ 2 / 2 +
      cy * ∫ ω in {ω | 0 ≤ X i ω ∧ X i ω ≤ yv i}, |X i ω| ^ t ∂P)
    (fun i => integral_exp_pos (exp_Xt_integrable P X hmeas yv hyv h hh.le i))
    (fun i => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := hb i
      have hA0 : 0 ≤ ∫ ω in {ω | 0 ≤ X i ω ∧ X i ω ≤ yv i}, |X i ω| ^ t ∂P :=
        integral_nonneg (fun ω => Real.rpow_nonneg (abs_nonneg _) _)
      rcases le_or_gt h (t / yv i) with hti | hti
      · have := fn_lemma_1_4_a_core P (Xt X yv i) (Xt_measurable X hmeas yv i) (yv i) (hyv i)
          h1 t ht h2 h hh hti
        rw [h3, h4] at this
        have : 0 ≤ cy * ∫ ω in {ω | 0 ≤ X i ω ∧ X i ω ≤ yv i}, |X i ω| ^ t ∂P :=
          mul_nonneg hcy0 hA0
        linarith
      · have := fn_lemma_1_4_b_core P (Xt X yv i) (Xt_measurable X hmeas yv i) (yv i) (hyv i)
          h1 t ht h2 h hti
        rw [h3, h4, h5] at this
        have hth : t / h < yv i := by
          rw [div_lt_iff₀ hh]; rw [div_lt_iff₀ (hyv i)] at hti; linarith
        have hm := fn_g_mono_h' t ht0 h hh (yv i) y hth.le (hyy i)
        have : (∫ ω in {ω | 0 ≤ X i ω ∧ X i ω ≤ yv i}, |X i ω| ^ t ∂P) *
            (Real.exp (h * yv i) - 1 - h * yv i) / yv i ^ t ≤
            cy * ∫ ω in {ω | 0 ≤ X i ω ∧ X i ω ≤ yv i}, |X i ω| ^ t ∂P := by
          rw [mul_div_assoc, mul_comm]
          exact mul_le_mul_of_nonneg_right hm hA0
        linarith) _ _ h9
  refine le_trans key (le_of_eq ?_)
  congr 1
  unfold muY B2Y AY
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div,
    ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum]
  ring


lemma fn_B_nonneg {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n : ℕ}
    (X : Fin n → Ω → ℝ) (yv : Fin n → ℝ) : 0 ≤ B2Y P X yv :=
  Finset.sum_nonneg (fun i _ => integral_nonneg (fun ω => sq_nonneg _))

lemma fn_A_nonneg {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n : ℕ}
    (X : Fin n → Ω → ℝ) (yv : Fin n → ℝ) (t : ℝ) : 0 ≤ AY P X yv t :=
  Finset.sum_nonneg (fun i _ => integral_nonneg (fun ω => Real.rpow_nonneg (abs_nonneg _) _))

/-- Unified bound valid for all `h > 0`. -/
lemma fn_unified {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (X : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (x : ℝ) (yv : Fin n → ℝ) (hyv : ∀ i, 0 < yv i)
    (y : ℝ) (hy0 : 0 < y) (hyy : ∀ i, yv i ≤ y)
    (t : ℝ) (ht : 2 ≤ t)
    (hL2 : ∀ i, IntegrableOn (fun ω => X i ω ^ 2) {ω | X i ω ≤ yv i} P)
    (h : ℝ) (hh : 0 < h) :
    P.real {ω | x ≤ St X yv ω} ≤
      Real.exp (h * (muY P X yv - x) + 1 / 2 * Real.exp t * B2Y P X yv * h ^ 2 +
        (Real.exp (h * y) - 1) / y ^ t * AY P X yv t) := by
  have hA := fn_A_nonneg P X yv t
  have hyt : 0 < y ^ t := Real.rpow_pos_of_pos hy0 t
  have hhy : 0 ≤ h * y := (mul_pos hh hy0).le
  have he : 0 ≤ Real.exp (h * y) - 1 := by linarith [Real.add_one_le_exp (h * y)]
  rcases le_or_gt h (t / y) with h1 | h1
  · refine le_trans (fn_eq_1_17_core P X hmeas hindep x yv hyv y hyy t ht hL2 h hh h1) ?_
    rw [Real.exp_le_exp]
    have : 0 ≤ (Real.exp (h * y) - 1) / y ^ t * AY P X yv t :=
      mul_nonneg (div_nonneg he hyt.le) hA
    linarith
  · refine le_trans (fn_eq_1_18_core P X hmeas hindep x yv hyv y hyy t ht hL2 h hy0 h1) ?_
    rw [Real.exp_le_exp]
    have : (Real.exp (h * y) - 1 - h * y) / y ^ t * AY P X yv t ≤
        (Real.exp (h * y) - 1) / y ^ t * AY P X yv t :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by linarith) hyt.le) hA
    linarith

lemma fn_L_identity (t β x y A : ℝ) (hy0 : 0 < y) (hA : 0 < A) (hz : 0 ≤ β * x * y ^ (t - 1) / A) :
    (Real.exp (Real.log (β * x * y ^ (t - 1) / A + 1)) - 1) / y ^ t * A = β * x / y := by
  rw [Real.exp_log (by linarith), Real.rpow_sub_one hy0.ne']
  have hyt : 0 < y ^ t := Real.rpow_pos_of_pos hy0 t
  field_simp
  ring

/-- Key facts under `cond_1_6`. -/
lemma fn_cond16_facts (t α β x y B A : ℝ) (ht : 2 ≤ t) (hα0 : 0 < α) (hα1 : α < 1)
    (hβ : β = 1 - α) (hx : 0 < x) (hy0 : 0 < y) (hB0 : 0 ≤ B)
    (h16 : cond_1_6 t α β x y B A) :
    0 < A ∧ 0 < B ∧ 0 < Real.log (β * x * y ^ (t - 1) / A + 1) ∧
      Real.exp t * B * (Real.log (β * x * y ^ (t - 1) / A + 1) / y) < α * x ∧
      Real.exp t * B * (t / y) < α * x ∧ 0 ≤ β * x * y ^ (t - 1) / A := by
  obtain ⟨hA, hmax⟩ := h16
  have hB : 0 < B := by
    rcases hB0.eq_or_lt with h | h
    · rw [← h, mul_zero, div_zero] at hmax
      have := le_max_left t (Real.log (β * x * y ^ (t - 1) / A + 1)); linarith
    · exact h
  have hE : 0 < Real.exp t * B := mul_pos (Real.exp_pos t) hB
  have hz : 0 < β * x * y ^ (t - 1) / A := by
    have : 0 < β := by linarith
    have := Real.rpow_pos_of_pos hy0 (t - 1)
    positivity
  have hL1 := lt_of_le_of_lt (le_max_right _ _) hmax
  have ht1 := lt_of_le_of_lt (le_max_left _ _) hmax
  rw [lt_div_iff₀ hE] at hL1 ht1
  refine ⟨hA, hB, Real.log_pos (by linarith), ?_, ?_, hz.le⟩
  · rw [mul_div_assoc', div_lt_iff₀ hy0]; linarith
  · rw [mul_div_assoc', div_lt_iff₀ hy0]; linarith

theorem fn_eq_1_19_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (X : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (x : ℝ) (hx : 0 < x) (yv : Fin n → ℝ) (hyv : ∀ i, 0 < yv i)
    (y : ℝ) (hy0 : 0 < y) (hyy : ∀ i, yv i ≤ y)
    (t : ℝ) (ht : 2 ≤ t)
    (α β : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hβ : β = 1 - α)
    (hL2 : ∀ i, IntegrableOn (fun ω => X i ω ^ 2) {ω | X i ω ≤ yv i} P)
    (h14 : cond_1_4 t α β x y (B2Y P X yv) (AY P X yv t)) :
    P.real {ω | x ≤ St X yv ω} ≤ P6 t α x (muY P X yv) (B2Y P X yv) := by
  subst hβ
  have hB0 := fn_B_nonneg P X yv
  have hA0 := fn_A_nonneg P X yv t
  unfold P6
  split_ifs with hB
  · -- degenerate case: all truncated summands vanish a.s.
    have hzero : ∀ i, ∫ ω in {ω | X i ω ≤ yv i}, X i ω ^ 2 ∂P = 0 := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
        integral_nonneg (fun ω => sq_nonneg (X j ω)))).1 hB
      exact this i (Finset.mem_univ i)
    have hae : ∀ i, ∀ᵐ ω ∂P, Xt X yv i ω = 0 := by
      intro i
      have hs : MeasurableSet {ω | X i ω ≤ yv i} := measurableSet_le (hmeas i) measurable_const
      have h1 := (setIntegral_eq_zero_iff_of_nonneg_ae
        (Filter.Eventually.of_forall (fun ω => sq_nonneg (X i ω))) (hL2 i)).1 (hzero i)
      have h2 := (ae_restrict_iff' hs).1 h1
      filter_upwards [h2] with ω hω
      unfold Xt
      split_ifs with hle
      · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (hω hle)
      · rfl
    have hall : ∀ᵐ ω ∂P, ∀ i, Xt X yv i ω = 0 := ae_all_iff.2 hae
    have hnull : P {ω | x ≤ St X yv ω} = 0 := by
      apply measure_mono_null _ (ae_iff.1 hall)
      intro ω hω
      intro hcon
      have : St X yv ω = 0 := by
        unfold St; exact Finset.sum_eq_zero (fun i _ => hcon i)
      have hω' : x ≤ St X yv ω := hω
      linarith
    simp [measureReal_def, hnull]
  · have hBp : 0 < B2Y P X yv := lt_of_le_of_ne hB0 (Ne.symm hB)
    set B := B2Y P X yv with hBdef
    set μ := muY P X yv with hμdef
    set A := AY P X yv t with hAdef
    have hE : 0 < Real.exp t * B := mul_pos (Real.exp_pos t) hBp
    set h1 := α * x / (Real.exp t * B) with hh1
    have hh1p : 0 < h1 := div_pos (mul_pos hα0 hx) hE
    have hEh : Real.exp t * B * h1 = α * x := by rw [hh1]; field_simp
    have hP6 : -(α * x * (α * x / 2 - μ) / (Real.exp t * B)) = -(h1 * (α * x / 2 - μ)) := by
      rw [hh1]; ring
    rw [hP6]
    have hβ0 : 0 ≤ 1 - α := by linarith
    have hβx : 0 ≤ h1 * x * (1 - α) := by positivity
    have hq : 1 / 2 * Real.exp t * B * h1 ^ 2 = 1 / 2 * (α * x) * h1 := by
      rw [← hEh]; ring
    rcases le_or_gt h1 (t / y) with hc | hc
    · refine le_trans (fn_eq_1_17_core P X hmeas hindep x yv hyv y hyy t ht hL2 h1 hh1p hc) ?_
      rw [Real.exp_le_exp, hq]
      linarith
    · refine le_trans (fn_eq_1_18_core P X hmeas hindep x yv hyv y hyy t ht hL2 h1 hy0 hc) ?_
      rw [Real.exp_le_exp, hq]
      have hextra : (Real.exp (h1 * y) - 1 - h1 * y) / y ^ t * A ≤ h1 * x * (1 - α) := by
        rcases hA0.eq_or_lt with hA | hAp
        · rw [← hA, mul_zero]; exact hβx
        · have h14' : α * x * y / (Real.exp t * B) ≤
              max t (Real.log ((1 - α) * x * y ^ (t - 1) / A + 1)) := by
            rcases h14 with h | h
            · exact absurd h hAp.ne'
            · exact h
          have hyt : 0 < y ^ t := Real.rpow_pos_of_pos hy0 t
          have h1y : t < h1 * y := by rw [div_lt_iff₀ hy0] at hc; linarith
          have hmx : α * x * y / (Real.exp t * B) = h1 * y := by rw [hh1]; ring
          rw [hmx] at h14'
          have hL : h1 * y ≤ Real.log ((1 - α) * x * y ^ (t - 1) / A + 1) := by
            rcases le_total t (Real.log ((1 - α) * x * y ^ (t - 1) / A + 1)) with hm | hm
            · rw [max_eq_right hm] at h14'; exact h14'
            · rw [max_eq_left hm] at h14'; linarith
          have hz : 0 ≤ (1 - α) * x * y ^ (t - 1) / A := by
            have := Real.rpow_pos_of_pos hy0 (t - 1)
            positivity
          have hexp : Real.exp (h1 * y) ≤
              Real.exp (Real.log ((1 - α) * x * y ^ (t - 1) / A + 1)) := Real.exp_le_exp.2 hL
          have hid := fn_L_identity t (1 - α) x y A hy0 hAp hz
          have s1 : (Real.exp (h1 * y) - 1 - h1 * y) / y ^ t * A ≤
              (Real.exp (Real.log ((1 - α) * x * y ^ (t - 1) / A + 1)) - 1) / y ^ t * A := by
            apply mul_le_mul_of_nonneg_right _ hAp.le
            apply div_le_div_of_nonneg_right _ hyt.le
            nlinarith
          rw [hid] at s1
          have s2 : (1 - α) * x / y ≤ h1 * x * (1 - α) := by
            have hb0 : 0 ≤ (1 - α) * x := by positivity
            rw [div_le_iff₀ hy0]
            have : 1 ≤ h1 * y := by linarith
            nlinarith
          linarith
      linarith


theorem fn_p4_case_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (X : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (x : ℝ) (hx : 0 < x) (yv : Fin n → ℝ) (hyv : ∀ i, 0 < yv i)
    (y : ℝ) (hy0 : 0 < y) (hyy : ∀ i, yv i ≤ y)
    (t : ℝ) (ht : 2 ≤ t)
    (α β : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hβ : β = 1 - α)
    (hL2 : ∀ i, IntegrableOn (fun ω => X i ω ^ 2) {ω | X i ω ≤ yv i} P)
    (h16 : cond_1_6 t α β x y (B2Y P X yv) (AY P X yv t)) :
    P.real {ω | x ≤ St X yv ω} < P4 t α β x y (muY P X yv) (AY P X yv t) := by
  obtain ⟨hA, hB, hLpos, hEL, -, hz⟩ :=
    fn_cond16_facts t α β x y _ _ ht hα0 hα1 hβ hx hy0 (fn_B_nonneg P X yv) h16
  subst hβ
  set B := B2Y P X yv with hBdef
  set μ := muY P X yv with hμdef
  set A := AY P X yv t with hAdef
  set L := Real.log ((1 - α) * x * y ^ (t - 1) / A + 1) with hLdef
  have hh2 : 0 < L / y := div_pos hLpos hy0
  have hU := fn_unified P X hmeas hindep x yv hyv y hy0 hyy t ht hL2 (L / y) hh2
  have hLy : L / y * y = L := div_mul_cancel₀ L hy0.ne'
  rw [hLy, fn_L_identity t (1 - α) x y A hy0 hA hz] at hU
  refine lt_of_le_of_lt hU ?_
  unfold P4
  rw [Real.exp_lt_exp]
  have k := mul_lt_mul_of_pos_right hEL hh2
  have e1 : ((1 - α / 2) * x / y - μ / y) * L = ((1 - α / 2) * x - μ) * (L / y) := by ring
  rw [e1]
  nlinarith

theorem fn_eq_1_20_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (X : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (x : ℝ) (hx : 0 < x) (yv : Fin n → ℝ) (hyv : ∀ i, 0 < yv i)
    (y : ℝ) (hy0 : 0 < y) (hyy : ∀ i, yv i ≤ y)
    (t : ℝ) (ht : 2 ≤ t)
    (α β : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hβ : β = 1 - α)
    (hL2 : ∀ i, IntegrableOn (fun ω => X i ω ^ 2) {ω | X i ω ≤ yv i} P)
    (h16 : cond_1_6 t α β x y (B2Y P X yv) (AY P X yv t))
    (hextra : β * x ≥ muY P X yv ∨ β ≥ t * α / 2) :
    P.real {ω | x ≤ St X yv ω} < P5 t α β x y (muY P X yv) (AY P X yv t) := by
  obtain ⟨hA, hB, hLpos, hEL, hEt, hz⟩ :=
    fn_cond16_facts t α β x y _ _ ht hα0 hα1 hβ hx hy0 (fn_B_nonneg P X yv) h16
  subst hβ
  set B := B2Y P X yv with hBdef
  set μ := muY P X yv with hμdef
  set A := AY P X yv t with hAdef
  set L := Real.log ((1 - α) * x * y ^ (t - 1) / A + 1) with hLdef
  have hh2 : 0 < L / y := div_pos hLpos hy0
  have hty : 0 < t / y := div_pos (by linarith) hy0
  have k := mul_lt_mul_of_pos_right hEL hh2
  unfold P5
  have e1 : ((1 - α) * x / y - μ / y) * L = ((1 - α) * x - μ) * (L / y) := by ring
  rw [e1]
  rcases le_total t L with hLt | hLt
  · -- use the unified bound at h = L / y
    have hU := fn_unified P X hmeas hindep x yv hyv y hy0 hyy t ht hL2 (L / y) hh2
    have hLy : L / y * y = L := div_mul_cancel₀ L hy0.ne'
    rw [hLy, fn_L_identity t (1 - α) x y A hy0 hA hz] at hU
    refine lt_of_le_of_lt hU ?_
    rw [Real.exp_lt_exp]
    have k2 : t / y * (α * x) ≤ L / y * (α * x) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hLt hy0.le) (by positivity)
    simp only [div_eq_mul_inv] at k k2 ⊢
    nlinarith
  · rcases hextra with hμ | hb
    · -- use (1.17) at h = t / y
      have h17 := fn_eq_1_17_core P X hmeas hindep x yv hyv y hyy t ht hL2 (t / y) hty le_rfl
      refine lt_of_le_of_lt h17 ?_
      rw [Real.exp_lt_exp]
      have k3 := mul_lt_mul_of_pos_right hEt hty
      have k1 : 0 ≤ (t - L) * ((1 - α) * x - μ) / y :=
        div_nonneg (mul_nonneg (by linarith) (by linarith)) hy0.le
      have k4 : 0 < (1 - α) * x / y := div_pos (mul_pos (by linarith) hx) hy0
      simp only [div_eq_mul_inv] at k1 k3 k4 ⊢
      nlinarith
    · -- use (1.17) at h = L / y
      have hle : L / y ≤ t / y := div_le_div_of_nonneg_right hLt hy0.le
      have h17 := fn_eq_1_17_core P X hmeas hindep x yv hyv y hyy t ht hL2 (L / y) hh2 hle
      refine lt_of_le_of_lt h17 ?_
      rw [Real.exp_lt_exp]
      have k5 : 0 ≤ ((1 - α) - t * α / 2) * x / y :=
        div_nonneg (mul_nonneg (by linarith) hx.le) hy0.le
      have k6 : 0 < α * x * (L / y) := by positivity
      simp only [div_eq_mul_inv] at k k5 k6 ⊢
      nlinarith

theorem fn_theorem_1_3_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    {n : ℕ} (X : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (x : ℝ) (hx : 0 < x) (yv : Fin n → ℝ) (hyv : ∀ i, 0 < yv i)
    (y : ℝ) (hy0 : 0 < y) (hyy : ∀ i, yv i ≤ y)
    (t : ℝ) (ht : 2 ≤ t)
    (α β : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hβ : β = 1 - α)
    (hL2 : ∀ i, IntegrableOn (fun ω => X i ω ^ 2) {ω | X i ω ≤ yv i} P) :
    (cond_1_4 t α β x y (B2Y P X yv) (AY P X yv t) →
        P.real {ω | x ≤ S n X ω} ≤
          ∑ i, P.real {ω | yv i < X i ω} + P6 t α x (muY P X yv) (B2Y P X yv)) ∧
      (cond_1_6 t α β x y (B2Y P X yv) (AY P X yv t) →
        P.real {ω | x ≤ S n X ω} <
          ∑ i, P.real {ω | yv i < X i ω} + P4 t α β x y (muY P X yv) (AY P X yv t)) ∧
      (cond_1_6 t α β x y (B2Y P X yv) (AY P X yv t) →
        (β ≥ t * α / 2 ∨ β * x ≥ muY P X yv) →
        P.real {ω | x ≤ S n X ω} <
          ∑ i, P.real {ω | yv i < X i ω} + P5 t α β x y (muY P X yv) (AY P X yv t)) := by
  have h8 := fn_eq_1_8_core P X x yv
  refine ⟨fun h14 => ?_, fun h16 => ?_, fun h16 hor => ?_⟩
  · have := fn_eq_1_19_core P X hmeas hindep x hx yv hyv y hy0 hyy t ht α β hα0 hα1 hβ hL2 h14
    linarith
  · have := fn_p4_case_core P X hmeas hindep x hx yv hyv y hy0 hyy t ht α β hα0 hα1 hβ hL2 h16
    linarith
  · have := fn_eq_1_20_core P X hmeas hindep x hx yv hyv y hy0 hyy t ht α β hα0 hα1 hβ hL2 h16
      hor.symm
    linarith


lemma fn_mu_nonpos {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (X : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (yv : Fin n → ℝ)
    (hyv : ∀ i, 0 < yv i)
    (hint : ∀ i, Integrable (X i) P) (hmean : ∀ i, ∫ ω, X i ω ∂P = 0) : muY P X yv ≤ 0 := by
  unfold muY
  apply Finset.sum_nonpos
  intro i _
  have hs : MeasurableSet {ω | X i ω ≤ yv i} := measurableSet_le (hmeas i) measurable_const
  have hsplit := integral_add_compl hs (hint i)
  have hc : {ω | X i ω ≤ yv i}ᶜ = {ω | yv i < X i ω} := by ext ω; simp [not_le]
  rw [hc, hmean i] at hsplit
  have hpos : 0 ≤ ∫ ω in {ω | yv i < X i ω}, X i ω ∂P := by
    apply setIntegral_nonneg (measurableSet_lt measurable_const (hmeas i))
    intro ω hω
    have : yv i < X i ω := hω
    linarith [hyv i]
  linarith

lemma fn_not14_to_16 (t α β x y B A : ℝ) (hA : 0 ≤ A) (h : ¬ cond_1_4 t α β x y B A) :
    cond_1_6 t α β x y B A := by
  unfold cond_1_4 at h
  push_neg at h
  exact ⟨lt_of_le_of_ne hA (Ne.symm h.1), h.2⟩

lemma fn_P5_bound (t α β x y μ A : ℝ) (hy0 : 0 < y) (hx : 0 < x) (hβ0 : 0 < β)
    (hA : 0 < A) (hμ : μ ≤ 0) (hβt : β - t * α / 2 = 0) :
    P5 t α β x y μ A ≤ (A / (β * x * y ^ (t - 1))) ^ (β * x / y) := by
  unfold P5
  have hD : 0 < β * x * y ^ (t - 1) := by
    have := Real.rpow_pos_of_pos hy0 (t - 1); positivity
  set z := β * x * y ^ (t - 1) / A with hz
  have hzpos : 0 < z := div_pos hD hA
  have hL : 0 ≤ Real.log (z + 1) := Real.log_nonneg (by linarith)
  have hlog : Real.log z ≤ Real.log (z + 1) := Real.log_le_log hzpos (by linarith)
  rw [Real.rpow_def_of_pos (div_pos hA hD)]
  have hinv : A / (β * x * y ^ (t - 1)) = z⁻¹ := by rw [hz, inv_div]
  rw [hinv, Real.log_inv, Real.exp_le_exp, hβt, zero_mul, zero_div, zero_sub]
  have hc : 0 ≤ β * x / y := by positivity
  have h1 : (β * x / y - μ / y) * Real.log (z + 1) ≥ β * x / y * Real.log (z + 1) := by
    have : 0 ≤ -(μ / y) := by
      have := div_nonpos_of_nonpos_of_nonneg hμ hy0.le; linarith
    nlinarith
  have h2 : β * x / y * Real.log z ≤ β * x / y * Real.log (z + 1) :=
    mul_le_mul_of_nonneg_left hlog hc
  nlinarith

theorem fn_corollary_1_7_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    {n : ℕ} (X : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (x : ℝ) (hx : 0 < x) (yv : Fin n → ℝ) (hyv : ∀ i, 0 < yv i)
    (y : ℝ) (hy0 : 0 < y) (hyy : ∀ i, yv i ≤ y)
    (t : ℝ) (ht : 2 ≤ t)
    (hint : ∀ i, Integrable (X i) P) (hmean : ∀ i, ∫ ω, X i ω ∂P = 0)
    (α β : ℝ) (hβ : β = t / (t + 2)) (hα : α = 1 - β)
    (hL2 : ∀ i, IntegrableOn (fun ω => X i ω ^ 2) {ω | X i ω ≤ yv i} P) :
    P.real {ω | x ≤ S n X ω} ≤
      ∑ i, P.real {ω | yv i < X i ω} +
        (if B2Y P X yv = 0 then 0
          else Real.exp (-(α ^ 2 * x ^ 2 / (2 * Real.exp t * B2Y P X yv)))) +
        (AY P X yv t / (β * x * y ^ (t - 1))) ^ (β * x / y) := by
  have ht2 : 0 < t + 2 := by linarith
  have hαv : α = 2 / (t + 2) := by rw [hα, hβ]; field_simp; ring
  have hα0 : 0 < α := by rw [hαv]; positivity
  have hα1 : α < 1 := by rw [hαv, div_lt_one ht2]; linarith
  have hβ' : β = 1 - α := by linarith
  have hβ0 : 0 < β := by rw [hβ]; exact div_pos (by linarith) ht2
  have hβt : β - t * α / 2 = 0 := by rw [hβ, hαv]; field_simp; ring
  have hμ := fn_mu_nonpos P X hmeas yv hyv hint hmean
  have hA0 := fn_A_nonneg P X yv t
  have hB0 := fn_B_nonneg P X yv
  obtain ⟨T1, -, T3⟩ :=
    fn_theorem_1_3_core P X hmeas hindep x hx yv hyv y hy0 hyy t ht α β hα0 hα1 hβ' hL2
  have hthird : 0 ≤ (AY P X yv t / (β * x * y ^ (t - 1))) ^ (β * x / y) := by
    apply Real.rpow_nonneg
    have := Real.rpow_pos_of_pos hy0 (t - 1)
    positivity
  have hifnn : 0 ≤ (if B2Y P X yv = 0 then (0 : ℝ)
      else Real.exp (-(α ^ 2 * x ^ 2 / (2 * Real.exp t * B2Y P X yv)))) := by
    split_ifs
    · exact le_rfl
    · exact (Real.exp_pos _).le
  by_cases h14 : cond_1_4 t α β x y (B2Y P X yv) (AY P X yv t)
  · have h := T1 h14
    have hP6 : P6 t α x (muY P X yv) (B2Y P X yv) ≤
        (if B2Y P X yv = 0 then (0 : ℝ)
          else Real.exp (-(α ^ 2 * x ^ 2 / (2 * Real.exp t * B2Y P X yv)))) := by
      unfold P6
      split_ifs with hB
      · exact le_rfl
      · rw [Real.exp_le_exp, neg_le_neg_iff]
        have hBp : 0 < B2Y P X yv := lt_of_le_of_ne hB0 (Ne.symm hB)
        have hE : 0 < Real.exp t * B2Y P X yv := mul_pos (Real.exp_pos t) hBp
        rw [show 2 * Real.exp t * B2Y P X yv = 2 * (Real.exp t * B2Y P X yv) by ring,
          div_le_div_iff₀ (by positivity) hE]
        have : 0 ≤ α * x * (-muY P X yv) := by
          have : 0 ≤ -muY P X yv := by linarith
          positivity
        nlinarith
    linarith
  · have h16 := fn_not14_to_16 _ _ _ _ _ _ _ hA0 h14
    have h := T3 h16 (Or.inl (by linarith))
    have hP5 := fn_P5_bound t α β x y (muY P X yv) (AY P X yv t) hy0 hx hβ0 h16.1 hμ hβt
    linarith


lemma fn_markov {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Measurable X) (c : ℝ) (hc : 0 < c) (t : ℝ) (ht : 0 < t)
    (hAt : IntegrableOn (fun ω => |X ω| ^ t) {ω | 0 ≤ X ω} P) :
    P.real {ω | c < X ω} ≤ (∫ ω in {ω | c < X ω}, |X ω| ^ t ∂P) / c ^ t := by
  have hct : 0 < c ^ t := Real.rpow_pos_of_pos hc t
  have hs : MeasurableSet {ω | c < X ω} := measurableSet_lt measurable_const hX
  have hsub : {ω | c < X ω} ⊆ {ω | 0 ≤ X ω} := fun ω hω => by
    have : c < X ω := hω
    show 0 ≤ X ω
    linarith
  rw [le_div_iff₀ hct]
  have e : P.real {ω | c < X ω} * c ^ t = ∫ ω in {ω | c < X ω}, c ^ t ∂P := by
    rw [setIntegral_const, smul_eq_mul]
  rw [e]
  apply setIntegral_mono_on (integrableOn_const (by simp)) (hAt.mono_set hsub) hs
  intro ω hω
  have : c < X ω := hω
  rw [abs_of_pos (lt_trans hc this)]
  exact Real.rpow_le_rpow hc.le this.le ht.le

lemma fn_split {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) (hX : Measurable X) (c : ℝ) (hc : 0 < c) (t : ℝ)
    (hAt : IntegrableOn (fun ω => |X ω| ^ t) {ω | 0 ≤ X ω} P) :
    ∫ ω in {ω | 0 ≤ X ω}, |X ω| ^ t ∂P =
      ∫ ω in {ω | 0 ≤ X ω ∧ X ω ≤ c}, |X ω| ^ t ∂P + ∫ ω in {ω | c < X ω}, |X ω| ^ t ∂P := by
  have hU : {ω | 0 ≤ X ω} = {ω | 0 ≤ X ω ∧ X ω ≤ c} ∪ {ω | c < X ω} := by
    ext ω
    simp only [Set.mem_union]
    constructor
    · intro h
      rcases le_or_gt (X ω) c with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr h'
    · rintro (h | h)
      · exact h.1
      · have : c < X ω := h
        show 0 ≤ X ω
        linarith
  have hD : Disjoint {ω | 0 ≤ X ω ∧ X ω ≤ c} {ω | c < X ω} := by
    rw [Set.disjoint_left]
    intro ω h1 h2
    have a : X ω ≤ c := h1.2
    have b : c < X ω := h2
    linarith
  rw [hU] at hAt ⊢
  exact setIntegral_union hD (measurableSet_lt measurable_const hX)
    (hAt.mono_set Set.subset_union_left) (hAt.mono_set Set.subset_union_right)

theorem fn_corollary_1_8_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    {n : ℕ} (X : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (x : ℝ) (hx : 0 < x) (t : ℝ) (ht : 2 ≤ t)
    (hL2 : ∀ i, MemLp (X i) 2 P) (hmean : ∀ i, ∫ ω, X i ω ∂P = 0)
    (hAt : ∀ i, IntegrableOn (fun ω => |X i ω| ^ t) {ω | 0 ≤ X i ω} P) :
    P.real {ω | x ≤ S n X ω} ≤
      (1 + 2 / t) ^ t * Atplus P X t * x ^ (-t) +
        (if Bn2 P X = 0 then 0
          else Real.exp (-(2 * (t + 2) ^ (-2 : ℝ) * Real.exp (-t) * x ^ 2 / Bn2 P X))) := by
  have ht0 : 0 < t := by linarith
  have ht2 : 0 < t + 2 := by linarith
  set β := t / (t + 2) with hβ
  set α := 1 - β with hα
  have hβ0 : 0 < β := div_pos ht0 ht2
  have hαv : α = 2 / (t + 2) := by rw [hα, hβ]; field_simp; ring
  set c := β * x with hcdef
  have hc : 0 < c := mul_pos hβ0 hx
  have hint : ∀ i, Integrable (X i) P := fun i => (hL2 i).integrable one_le_two
  have hL2' : ∀ i, IntegrableOn (fun ω => X i ω ^ 2) {ω | X i ω ≤ (fun _ => c) i} P :=
    fun i => (hL2 i).integrable_sq.integrableOn
  have C := fn_corollary_1_7_core P X hmeas hindep x hx (fun _ => c) (fun _ => hc) c hc
    (fun _ => le_rfl) t ht hint hmean α β rfl rfl hL2'
  have hcc : c / c = 1 := div_self hc.ne'
  have hct : c * c ^ (t - 1) = c ^ t := by
    rw [Real.rpow_sub_one hc.ne']; field_simp
  rw [hcc, Real.rpow_one, hct] at C
  -- polynomial part
  have hctp : 0 < c ^ t := Real.rpow_pos_of_pos hc t
  have hpoly : ∑ i, P.real {ω | (fun _ => c) i < X i ω} + AY P X (fun _ => c) t / c ^ t ≤
      (1 + 2 / t) ^ t * Atplus P X t * x ^ (-t) := by
    have h1 : ∑ i, P.real {ω | (fun _ => c) i < X i ω} ≤
        ∑ i, (∫ ω in {ω | c < X i ω}, |X i ω| ^ t ∂P) / c ^ t :=
      Finset.sum_le_sum (fun i _ => fn_markov P (X i) (hmeas i) c hc t ht0 (hAt i))
    have h2 : (∑ i, (∫ ω in {ω | c < X i ω}, |X i ω| ^ t ∂P) / c ^ t) +
        AY P X (fun _ => c) t / c ^ t = Atplus P X t / c ^ t := by
      unfold AY Atplus
      rw [← Finset.sum_div, ← add_div, ← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [fn_split P (X i) (hmeas i) c hc t (hAt i)]
      ring
    have h3 : Atplus P X t / c ^ t = (1 + 2 / t) ^ t * Atplus P X t * x ^ (-t) := by
      have e1 : (1 + 2 / t) = β⁻¹ := by rw [hβ, inv_div]; field_simp
      rw [e1, Real.inv_rpow hβ0.le, Real.rpow_neg hx.le, hcdef, Real.mul_rpow hβ0.le hx.le]
      field_simp
    linarith
  -- Gaussian part
  have hBle : B2Y P X (fun _ => c) ≤ Bn2 P X := by
    unfold B2Y Bn2
    apply Finset.sum_le_sum
    intro i _
    rw [variance_of_integral_eq_zero (hmeas i).aemeasurable (hmean i)]
    exact setIntegral_le_integral (hL2 i).integrable_sq
      (Filter.Eventually.of_forall (fun ω => sq_nonneg (X i ω)))
  have hB0 := fn_B_nonneg P X (fun _ => c)
  have hgauss : (if B2Y P X (fun _ => c) = 0 then (0 : ℝ)
        else Real.exp (-(α ^ 2 * x ^ 2 / (2 * Real.exp t * B2Y P X (fun _ => c))))) ≤
      (if Bn2 P X = 0 then 0
          else Real.exp (-(2 * (t + 2) ^ (-2 : ℝ) * Real.exp (-t) * x ^ 2 / Bn2 P X))) := by
    by_cases hB : B2Y P X (fun _ => c) = 0
    · rw [if_pos hB]
      split_ifs
      · exact le_rfl
      · exact (Real.exp_pos _).le
    · have hBp : 0 < B2Y P X (fun _ => c) := lt_of_le_of_ne hB0 (Ne.symm hB)
      have hBn : 0 < Bn2 P X := lt_of_lt_of_le hBp hBle
      rw [if_neg hB, if_neg hBn.ne', Real.exp_le_exp, neg_le_neg_iff]
      set K := 2 * x ^ 2 / ((t + 2) ^ 2 * Real.exp t) with hK
      have hK0 : 0 ≤ K := by positivity
      have eL : 2 * (t + 2) ^ (-2 : ℝ) * Real.exp (-t) * x ^ 2 / Bn2 P X = K / Bn2 P X := by
        rw [Real.rpow_neg ht2.le, Real.rpow_two, Real.exp_neg, hK]
        field_simp
      have eR : α ^ 2 * x ^ 2 / (2 * Real.exp t * B2Y P X (fun _ => c)) =
          K / B2Y P X (fun _ => c) := by
        rw [hαv, hK]
        field_simp
      rw [eL, eR]
      exact div_le_div_of_nonneg_left hK0 hBp hBle
  linarith

end NagaevLD.FukNagaev

open NagaevLD.FukNagaev
open MeasureTheory ProbabilityTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (X : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (x : ℝ) (hx : 0 < x) (t : ℝ) (ht : 2 ≤ t)
    (hL2 : ∀ i, MemLp (X i) 2 P) (hmean : ∀ i, ∫ ω, X i ω ∂P = 0)
    (hAt : ∀ i, IntegrableOn (fun ω => |X i ω| ^ t) {ω | 0 ≤ X i ω} P) :
    P.real {ω | x ≤ S n X ω} ≤
      (1 + 2 / t) ^ t * Atplus P X t * x ^ (-t) +
        (if Bn2 P X = 0 then 0
          else Real.exp (-(2 * (t + 2) ^ (-2 : ℝ) * Real.exp (-t) * x ^ 2 / Bn2 P X))) := by
  exact fn_corollary_1_8_core P X hmeas hindep x hx t ht hL2 hmean hAt
