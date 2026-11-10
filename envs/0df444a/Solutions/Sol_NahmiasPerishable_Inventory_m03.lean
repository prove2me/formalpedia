-- Prove2me | solution 1 for NahmiasPerishable.Inventory.m03
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T13:39:36.561202+00:00
-- url     : https://prove2.me/submissions/b2b186f1-02d7-4aa9-b74c-3cd22d77f021

import Definitions.Def_NahmiasPerishable_Inventory_Threshold

open MeasureTheory Set Filter Topology
open scoped ENNReal
open NahmiasPerishable.Inventory

private noncomputable def u01Law : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

private instance : IsProbabilityMeasure u01Law := by
  constructor
  dsimp [u01Law]
  rw [Measure.restrict_apply_univ, Real.volume_Icc]
  norm_num

private noncomputable def u01Demand : Demand where
  law := u01Law
  prob := inferInstance
  nonneg := by
    dsimp [u01Law]
    rw [ae_restrict_iff' measurableSet_Icc]
    exact ae_of_all _ (fun d hd => hd.1)
  density := (Icc (0 : ℝ) 1).indicator 1
  measurable_density := measurable_one.indicator measurableSet_Icc
  law_density := (withDensity_indicator_one measurableSet_Icc).symm

private lemma integrable_shortage2 (z : ℝ) :
    Integrable (fun d : ℝ => 0 * pos (z - d) + 2 * pos (d - z)) u01Demand.law := by
  have hcont : Continuous (fun d : ℝ => 0 * pos (z - d) + 2 * pos (d - z)) := by
    unfold pos
    fun_prop
  exact hcont.integrableOn_Icc

private lemma hasDerivAt_max_sq (z d : ℝ) :
    HasDerivAt (fun t : ℝ => (max (t - z) 0) ^ 2) (0 * max (z - d) 0 + 2 * max (d - z) 0) d := by
  rw [zero_mul, zero_add]
  rcases lt_trichotomy d z with hlt | rfl | hgt
  · have h0 : ∀ᶠ t in 𝓝 d, (max (t - z) 0) ^ 2 = 0 := by
      filter_upwards [gt_mem_nhds hlt] with t ht
      rw [max_eq_right (by linarith), sq, mul_zero]
    have hd : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 d := hasDerivAt_const d 0
    have hmax : 2 * max (d - z) 0 = 0 := by rw [max_eq_right (by linarith), mul_zero]
    rw [hmax]
    exact hd.congr_of_eventuallyEq h0
  · rw [sub_self, max_self, mul_zero]
    rw [hasDerivAt_iff_isLittleO_nhds_zero]
    refine Asymptotics.IsLittleO.of_bound (fun c hc => ?_)
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hc] with h hh
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hh
    simp only [add_sub_cancel_left, sub_self, max_self, smul_zero, sub_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Real.norm_eq_abs, abs_sq]
    have h0 : 0 ≤ max h 0 := le_max_right h 0
    have hle : max h 0 ≤ |h| := max_le (le_abs_self h) (abs_nonneg h)
    nlinarith
  · have hpos : ∀ᶠ t in 𝓝 d, (max (t - z) 0) ^ 2 = (t - z) ^ 2 := by
      filter_upwards [lt_mem_nhds hgt] with t ht
      rw [max_eq_left (by linarith)]
    have hd : HasDerivAt (fun t : ℝ => (t - z) ^ 2) (2 * (d - z) ^ (2 - 1) * 1) d :=
      ((hasDerivAt_id d).sub_const z).pow 2
    have hmax : 2 * max (d - z) 0 = 2 * (d - z) ^ (2 - 1) * 1 := by
      rw [max_eq_left (by linarith)]; ring
    rw [hmax]
    exact hd.congr_of_eventuallyEq hpos

private lemma stockCost_u01 (z : ℝ) :
    stockCost u01Demand.law 0 2 z =
      (((max (1 - z) 0) ^ 2 - (max (-z) 0) ^ 2 : ℝ) : EReal) := by
  unfold stockCost ZhengQR.OrderQty.newsvendorCost
  rw [if_pos (integrable_shortage2 z)]
  congr 1
  change ∫ x in Icc (0 : ℝ) 1, (0 * max (z - x) 0 + 2 * max (x - z) 0) =
    (max (1 - z) 0) ^ 2 - (max (-z) 0) ^ 2
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hint : IntervalIntegrable (fun x : ℝ => 0 * max (z - x) 0 + 2 * max (x - z) 0) volume 0 1 :=
    (by fun_prop : Continuous (fun x : ℝ => 0 * max (z - x) 0 + 2 * max (x - z) 0)).intervalIntegrable 0 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_max_sq z x) hint]
  ring_nf

private lemma stockCost_u01_nonneg (z : ℝ) :
    (0 : EReal) ≤ stockCost u01Demand.law 0 2 z := by
  unfold stockCost ZhengQR.OrderQty.newsvendorCost
  rw [if_pos (integrable_shortage2 z)]
  exact EReal.coe_nonneg.mpr (integral_nonneg (fun d => by positivity))

private lemma stockCost_u01_anti {z₁ z₂ : ℝ} (hz : z₁ ≤ z₂) :
    stockCost u01Demand.law 0 2 z₂ ≤ stockCost u01Demand.law 0 2 z₁ := by
  unfold stockCost ZhengQR.OrderQty.newsvendorCost
  rw [if_pos (integrable_shortage2 z₂), if_pos (integrable_shortage2 z₁), EReal.coe_le_coe_iff]
  have h1 : Integrable (fun d : ℝ => 0 * max (z₂ - d) 0 + 2 * max (d - z₂) 0) u01Demand.law :=
    integrable_shortage2 z₂
  have h2 : Integrable (fun d : ℝ => 0 * max (z₁ - d) 0 + 2 * max (d - z₁) 0) u01Demand.law :=
    integrable_shortage2 z₁
  refine integral_mono h1 h2 (fun d => ?_)
  have hmax : max (d - z₂) 0 ≤ max (d - z₁) 0 := max_le_max_right 0 (by linarith)
  linarith

private noncomputable def model03 : FixedLife 1 :=
  linearModel 1 u01Demand false .fries .zero 1 0 2 0 (1 / 2)

private lemma stage_model03 (x : AgeState 1) (y : ℝ) :
    model03.control.stage x y = (y : EReal) + stockCost u01Demand.law 0 2 (total x + y) := by
  dsimp [model03, linearModel, FixedLife.control]
  simp

private lemma total_fifo_false (x : AgeState 1) (y d : ℝ) :
    total (fifo false x y d) = pos (y - pos (d - total x)) := by
  unfold fifo
  unfold total
  simp

private lemma ereal_neg_toENNReal_of_nonneg {a : EReal} (ha : 0 ≤ a) :
    (-a).toENNReal = 0 := by
  induction a using EReal.rec with
  | bot => contradiction
  | coe r =>
    have hr : 0 ≤ r := EReal.coe_nonneg.mp ha
    exact EReal.toENNReal_of_nonpos (EReal.coe_nonpos.mpr (by linarith))
  | top => simp

private lemma expectation_of_nonneg {f : ℝ → EReal} (hf : ∀ d, 0 ≤ f d) :
    expectation u01Demand.law f = (∫⁻ d, (f d).toENNReal ∂u01Demand.law).toEReal := by
  unfold expectation
  have hneg : (fun d => (-f d).toENNReal) = fun _ => 0 := by
    ext d
    exact ereal_neg_toENNReal_of_nonneg (hf d)
  rw [hneg, lintegral_zero, EReal.coe_ennreal_zero, sub_zero]

private lemma value_nonneg_and_anti (n : ℕ) :
    (∀ x : AgeState 1, 0 ≤ model03.control.value n x) ∧
    (∀ x₁ x₂ : AgeState 1, total x₁ ≤ total x₂ →
      model03.control.value n x₂ ≤ model03.control.value n x₁) := by
  induction n with
  | zero =>
    refine ⟨fun _ => le_rfl, fun _ _ _ => le_rfl⟩
  | succ n ih =>
    rcases ih with ⟨hnonneg, hanti⟩
    have hexp_nonneg : ∀ x y, 0 ≤ expectation model03.control.shock
        (fun d => model03.control.value n (model03.control.transfer x y d)) := by
      intro x y
      change 0 ≤ expectation u01Demand.law (fun d => model03.control.value n (fifo false x y d))
      rw [expectation_of_nonneg (fun d => hnonneg _)]
      exact EReal.coe_ennreal_nonneg _
    refine ⟨?_, ?_⟩
    · intro x
      simp only [ShockControl.value]
      refine le_iInf (fun y => ?_)
      rw [stage_model03]
      have hy : (0 : EReal) ≤ (y.val : EReal) := EReal.coe_nonneg.mpr y.2
      have hsc : (0 : EReal) ≤ stockCost u01Demand.law 0 2 (total x + y.val) :=
        stockCost_u01_nonneg _
      have hd : (0 : EReal) ≤ (model03.control.discount : EReal) *
          expectation model03.control.shock
            (fun d => model03.control.value n (model03.control.transfer x y.val d)) :=
        mul_nonneg (by dsimp [model03, linearModel, FixedLife.control]; norm_num)
          (hexp_nonneg x y.val)
      exact add_nonneg (add_nonneg hy hsc) hd
    · intro x₁ x₂ htot
      simp only [ShockControl.value]
      refine iInf_mono (fun y => ?_)
      rw [stage_model03, stage_model03]
      have htot_y : total x₁ + y.val ≤ total x₂ + y.val := by linarith
      have hstage : (y.val : EReal) + stockCost u01Demand.law 0 2 (total x₂ + y.val) ≤
          (y.val : EReal) + stockCost u01Demand.law 0 2 (total x₁ + y.val) :=
        add_le_add le_rfl (stockCost_u01_anti htot_y)
      have hexp : expectation model03.control.shock
          (fun d => model03.control.value n (model03.control.transfer x₂ y.val d)) ≤
          expectation model03.control.shock
          (fun d => model03.control.value n (model03.control.transfer x₁ y.val d)) := by
        change expectation u01Demand.law (fun d => model03.control.value n (fifo false x₂ y.val d)) ≤
          expectation u01Demand.law (fun d => model03.control.value n (fifo false x₁ y.val d))
        rw [expectation_of_nonneg (fun d => hnonneg _), expectation_of_nonneg (fun d => hnonneg _),
          EReal.coe_ennreal_le_coe_ennreal_iff]
        refine lintegral_mono (fun d => EReal.toENNReal_le_toENNReal (hanti _ _ ?_))
        rw [total_fifo_false, total_fifo_false]
        unfold pos
        exact max_le_max_right 0 (sub_le_sub_left (max_le_max_right 0 (by linarith)) _)
      have hdisc : (0 : EReal) ≤ (model03.control.discount : EReal) := by
        dsimp [model03, linearModel, FixedLife.control]; norm_num
      exact add_le_add hstage (mul_le_mul_of_nonneg_left hexp hdisc)

private lemma defined_model03 :
    model03.control.defined {x | canonical false x} := by
  intro n x _ y _
  change ExpectationDefined u01Demand.law (fun d => model03.control.value n (fifo false x y d))
  have hmono : Monotone (fun d : ℝ => model03.control.value n (fifo false x y d)) := by
    intro d₁ d₂ hd
    apply (value_nonneg_and_anti n).2
    rw [total_fifo_false, total_fifo_false]
    unfold pos
    exact max_le_max_right 0 (sub_le_sub_left (max_le_max_right 0 (by linarith)) _)
  refine ⟨hmono.measurable.aemeasurable, Or.inr ?_⟩
  have hneg : (fun d => (-model03.control.value n (fifo false x y d)).toENNReal) = fun _ => 0 := by
    ext d
    exact ereal_neg_toENNReal_of_nonneg ((value_nonneg_and_anti n).1 _)
  rw [hneg, lintegral_zero]
  exact ENNReal.zero_ne_top

private lemma objective_zero_eq (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    model03.control.objective 0 ((fun _ => x), 0) y =
      ((y + (max (1 - (x + y)) 0) ^ 2 : ℝ) : EReal) := by
  unfold ShockControl.objective
  have hval0 : model03.control.value 0 = fun _ => 0 := rfl
  have hexp0 : expectation model03.control.shock (fun _ : ℝ => (0 : EReal)) = 0 := by
    change expectation u01Demand.law (fun _ : ℝ => (0 : EReal)) = 0
    unfold expectation
    simp
  rw [hval0, hexp0, mul_zero, add_zero, stage_model03]
  have htot : total ((fun _ : Fin 1 => x), (0 : ℝ)) = x := by
    unfold total
    simp
  rw [htot, stockCost_u01 (x + y)]
  have hneg : max (-(x + y)) 0 = 0 := max_eq_right (by linarith)
  rw [hneg, zero_pow (by norm_num), sub_zero, ← EReal.coe_add]

private lemma quad_identity (x y : ℝ) :
    y + (max (1 - (x + y)) 0) ^ 2 - (3 / 4 - x) =
      (max (1 - (x + y)) 0 - (1 - (x + y))) + (max (1 - (x + y)) 0 - 1 / 2) ^ 2 := by
  ring

private lemma value_one_eq (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    model03.control.value 1 ((fun _ => x), 0) = ((3 / 4 - x : ℝ) : EReal) := by
  apply le_antisymm
  · let y0 : {y : ℝ // 0 ≤ y} := ⟨1 / 2 - x, by linarith⟩
    refine le_trans (iInf_le (fun y : {y : ℝ // 0 ≤ y} =>
      model03.control.objective 0 ((fun _ => x), 0) y.val) y0) ?_
    rw [objective_zero_eq x y0.val hx0 y0.2, EReal.coe_le_coe_iff]
    dsimp [y0]
    have h1 : 1 - (x + (1 / 2 - x)) = 1 / 2 := by ring
    rw [h1, max_eq_left (by norm_num)]
    linarith
  · refine le_iInf (fun y => ?_)
    change ((3 / 4 - x : ℝ) : EReal) ≤ model03.control.objective 0 ((fun _ => x), 0) y.val
    rw [objective_zero_eq x y.val hx0 y.2, EReal.coe_le_coe_iff]
    have hge : 0 ≤ max (1 - (x + y.val)) 0 - (1 - (x + y.val)) :=
      sub_nonneg.mpr (le_max_left _ _)
    have hsq : 0 ≤ (max (1 - (x + y.val)) 0 - 1 / 2) ^ 2 := sq_nonneg _
    linarith [quad_identity x y.val]

private lemma opt_zero_eq (q : ℕ → ℝ → ℝ)
    (hopt : ∀ n x, 0 ≤ x → model03.control.optimal n ((fun _ => x), 0) (q n x))
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    q 0 x = 1 / 2 - x := by
  rcases hopt 0 x hx0 with ⟨hq0, hqeq⟩
  rw [objective_zero_eq x (q 0 x) hx0 hq0, value_one_eq x hx0 hx1, EReal.coe_eq_coe_iff] at hqeq
  have hge : 0 ≤ max (1 - (x + q 0 x)) 0 - (1 - (x + q 0 x)) :=
    sub_nonneg.mpr (le_max_left _ _)
  have hsq : 0 ≤ (max (1 - (x + q 0 x)) 0 - 1 / 2) ^ 2 := sq_nonneg _
  have hid := quad_identity x (q 0 x)
  have hsq0 : (max (1 - (x + q 0 x)) 0 - 1 / 2) ^ 2 ≤ 0 := by linarith
  have hw : max (1 - (x + q 0 x)) 0 = 1 / 2 := by
    nlinarith [sq_nonneg (max (1 - (x + q 0 x)) 0 - 1 / 2)]
  linarith

set_option linter.unusedVariables false in
theorem solution : ¬ (∀ (D : Demand) (c p alpha : ℝ) (hc : 0 ≤ c) (hp : 0 ≤ p)
    (halpha : 0 < alpha ∧ alpha < 1)
    (hdefined : (linearModel 1 D false .fries .zero c 0 p 0 alpha).control.defined
      {x | canonical false x}),
    ∃ q : ℕ → ℝ → ℝ,
      (∀ n, ContDiffOn ℝ 1 (q n) (Ici 0)) ∧
      (∀ n x, 0 ≤ x →
        (linearModel 1 D false .fries .zero c 0 p 0 alpha).control.optimal n
          ((fun _ => x),0) (q n x)) ∧
      (∀ n x, 0 ≤ x → ∃ v : ℝ,
        HasDerivWithinAt (q n) v (Ici 0) x ∧ -1 < v ∧ v ≤ 0)) := by
  intro H
  rcases H u01Demand 1 2 (1 / 2) (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩
    defined_model03 with ⟨q, _, hopt, hderiv⟩
  rcases hderiv 0 0 le_rfl with ⟨v, hv, hvgt, _⟩
  have hlin : HasDerivWithinAt (fun x : ℝ => 1 / 2 - x) (-1) (Ici 0) 0 := by
    have hd : HasDerivAt (fun x : ℝ => 1 / 2 - x) (0 - 1) 0 :=
      (hasDerivAt_const (0 : ℝ) (1 / 2 : ℝ)).sub (hasDerivAt_id 0)
    simpa using hd.hasDerivWithinAt
  have heq : q 0 =ᶠ[𝓝[Ici 0] 0] (fun x : ℝ => 1 / 2 - x) := by
    rw [eventuallyEq_nhdsWithin_iff]
    filter_upwards [gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)] with x hxlt hxge
    exact opt_zero_eq q hopt x hxge (le_of_lt hxlt)
  have hqderiv : HasDerivWithinAt (q 0) (-1) (Ici 0) 0 :=
    hlin.congr_of_eventuallyEq heq (opt_zero_eq q hopt 0 le_rfl (by norm_num))
  have hL : ContinuousLinearMap.toSpanSingleton ℝ v =
      ContinuousLinearMap.toSpanSingleton ℝ (-1 : ℝ) :=
    (uniqueDiffWithinAt_Ici 0).eq hv hqderiv
  have hveq : v = -1 := by
    simpa using congr_arg (fun L : ℝ →L[ℝ] ℝ => L 1) hL
  linarith
