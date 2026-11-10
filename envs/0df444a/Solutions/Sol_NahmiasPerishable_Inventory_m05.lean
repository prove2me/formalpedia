-- Prove2me | solution 1 for NahmiasPerishable.Inventory.m05
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T12:16:24.686467+00:00
-- url     : https://prove2.me/submissions/572151a6-723e-495c-be51-46c9a1cedf2e

import Definitions.Def_NahmiasPerishable_Inventory_Threshold

open MeasureTheory Set
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

private lemma cdf_u01_one : cdf u01Demand.law 1 = 1 := by
  unfold cdf
  change ((volume.restrict (Icc (0 : ℝ) 1)) (Iic 1)).toReal = 1
  rw [Measure.restrict_apply measurableSet_Iic,
    inter_eq_self_of_subset_right (fun x hx => hx.2), Real.volume_Icc]
  norm_num

private lemma integrable_shortage (z : ℝ) :
    Integrable (fun d : ℝ => 0 * pos (z - d) + 1 * pos (d - z)) u01Demand.law := by
  have hcont : Continuous (fun d : ℝ => 0 * pos (z - d) + 1 * pos (d - z)) := by
    unfold pos
    fun_prop
  exact hcont.integrableOn_Icc

private lemma stockCost_nonneg (z : ℝ) :
    (0 : EReal) ≤ stockCost u01Demand.law 0 1 z := by
  unfold stockCost ZhengQR.OrderQty.newsvendorCost
  rw [if_pos (integrable_shortage z)]
  exact EReal.coe_nonneg.mpr (integral_nonneg (fun d => by positivity))

private lemma stockCost_of_one_le {z : ℝ} (hz : 1 ≤ z) :
    stockCost u01Demand.law 0 1 z = 0 := by
  unfold stockCost ZhengQR.OrderQty.newsvendorCost
  rw [if_pos (integrable_shortage z)]
  have hae : ∀ᵐ d ∂u01Demand.law, (0 * max (z - d) 0 + 1 * max (d - z) 0 : ℝ) = 0 := by
    change ∀ᵐ d ∂(volume.restrict (Icc (0 : ℝ) 1)), _
    rw [ae_restrict_iff' measurableSet_Icc]
    refine ae_of_all _ (fun d hd => ?_)
    have hle : d - z ≤ 0 := by linarith [hd.2]
    simp [max_eq_right hle]
  rw [integral_eq_zero_of_ae hae, EReal.coe_zero]

private lemma stockCost_pos_of_lt_one {z : ℝ} (hz : z < 1) :
    (0 : EReal) < stockCost u01Demand.law 0 1 z := by
  unfold stockCost ZhengQR.OrderQty.newsvendorCost
  rw [if_pos (integrable_shortage z)]
  rw [EReal.coe_pos]
  let m := max z 0
  have hm0 : 0 ≤ m := le_max_right z 0
  have hm1 : m < 1 := max_lt hz (by norm_num)
  let a := (m + 1) / 2
  let ε := (1 - m) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have haIcc : Icc a 1 ⊆ Icc (0 : ℝ) 1 := by
    intro d hd
    exact ⟨by dsimp [a] at hd; linarith [hd.1], hd.2⟩
  have hind_int : Integrable ((Icc a 1).indicator (fun _ : ℝ => ε)) u01Demand.law :=
    (integrable_const ε).indicator measurableSet_Icc
  have hmono : ∀ d : ℝ, (Icc a 1).indicator (fun _ : ℝ => ε) d ≤
      0 * max (z - d) 0 + 1 * max (d - z) 0 := by
    intro d
    by_cases hd : d ∈ Icc a 1
    · rw [Set.indicator_of_mem hd]
      have hmz : z ≤ m := le_max_left z 0
      have hda : a ≤ d := hd.1
      have hge : ε ≤ d - z := by dsimp [a, ε] at *; linarith
      have hmax : ε ≤ max (d - z) 0 := le_trans hge (le_max_left _ _)
      linarith
    · rw [Set.indicator_of_notMem hd]
      positivity
  have hint_le := integral_mono hind_int (by
    have hcont : Continuous (fun d : ℝ => 0 * max (z - d) 0 + 1 * max (d - z) 0) := by fun_prop
    exact hcont.integrableOn_Icc) hmono
  rw [integral_indicator measurableSet_Icc] at hint_le
  change (∫ x in Icc a 1, ε ∂(volume.restrict (Icc (0 : ℝ) 1))) ≤ _ at hint_le
  rw [Measure.restrict_restrict measurableSet_Icc,
    inter_eq_self_of_subset_left haIcc, setIntegral_const] at hint_le
  unfold Measure.real at hint_le
  rw [Real.volume_Icc] at hint_le
  simp only [smul_eq_mul] at hint_le
  have h1a : 1 - a = ε := by dsimp [a, ε]; ring
  rw [h1a, ENNReal.toReal_ofReal (le_of_lt hε)] at hint_le
  nlinarith

private noncomputable def model05 : FixedLife 1 :=
  linearModel 1 u01Demand true .nahmias .salvage 0 0 1 0 (1 / 2)

private lemma stage_model05 (x : AgeState 1) (y : ℝ) :
    model05.control.stage x y = stockCost u01Demand.law 0 1 (total x + y) := by
  dsimp [model05, linearModel, FixedLife.control]
  simp

private lemma expectation_zero05 :
    expectation u01Demand.law (fun _ : ℝ => (0 : EReal)) = 0 := by
  unfold expectation
  simp

private lemma value_model05 (n : ℕ) :
    model05.control.value n = fun _ => 0 := by
  induction n with
  | zero =>
    ext x
    dsimp [model05, linearModel, FixedLife.control, ShockControl.value]
    simp
  | succ n ih =>
    ext x
    simp only [ShockControl.value, ih]
    have hstage : ∀ y : {y : ℝ // 0 ≤ y},
        model05.control.stage x y.val = stockCost u01Demand.law 0 1 (total x + y.val) :=
      fun y => stage_model05 x y.val
    have hshock : model05.control.shock = u01Demand.law := rfl
    have hexp : expectation u01Demand.law (fun _ : ℝ => (0 : EReal)) = 0 := expectation_zero05
    simp_rw [hstage, hshock, hexp, mul_zero, add_zero]
    apply le_antisymm
    · let y0 : {y : ℝ // 0 ≤ y} := ⟨max (1 - total x) 0, le_max_right _ _⟩
      refine le_trans (iInf_le (fun y : {y : ℝ // 0 ≤ y} =>
        stockCost u01Demand.law 0 1 (total x + y.val)) y0) ?_
      have hge : 1 ≤ total x + y0.val := by
        dsimp [y0]
        linarith [le_max_left (1 - total x) 0]
      rw [stockCost_of_one_le hge]
    · exact le_iInf (fun y => stockCost_nonneg (total x + y.val))

private lemma defined_model05 :
    model05.control.defined {x | canonical true x} := by
  intro n x _ y _
  change ExpectationDefined u01Demand.law (fun d => model05.control.value n _)
  rw [value_model05 n]
  exact ⟨aemeasurable_const, Or.inl (by simp)⟩

private lemma bar_le_one :
    critical u01Demand true 0 0 1 (1 / 2) ≤ (1 : EReal) := by
  unfold critical lowerQuantile
  rw [if_pos rfl]
  apply sInf_le
  refine ⟨1, ?_, rfl⟩
  simp only [Set.mem_setOf_eq]
  rw [cdf_u01_one]
  norm_num

set_option linter.unusedVariables false in
theorem solution : ¬ (∀ (D : Demand) (b : Bool) (c h p theta alpha : ℝ)
    (hc : 0 ≤ c) (hh : 0 ≤ h) (hp : 0 ≤ p) (htheta : 0 ≤ theta)
    (hscale : 0 < p+h) (halpha : 0 < alpha ∧ alpha < 1)
    (hdefined : (linearModel 1 D b .nahmias .salvage c h p theta alpha).control.defined
      {x | canonical b x}),
    let M := linearModel 1 D b .nahmias .salvage c h p theta alpha
    let bar := critical D b c h p alpha
    ∃ q : ℕ → AgeState 1 → ℝ,
      (∀ n x, canonical b x → M.control.optimal n x (q n x)) ∧
      (∀ n x, canonical b x → (0 < q n x ↔ (total x : EReal) < bar)) ∧
      (∀ n x, canonical b x → 0 < total x → (total x : EReal) < bar →
        0 < total x+q n x ∧ ((total x+q n x : ℝ) : EReal) < bar) ∧
      (∀ n x, canonical b x → total x < 0 → q n x = |total x|+q n (0,0))) := by
  intro h
  rcases h u01Demand true 0 0 1 0 (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ⟨by norm_num, by norm_num⟩ defined_model05 with ⟨q, hq1, hq2, hq3, _⟩
  let x : AgeState 1 := (fun _ => 1 / 2, 0)
  have hcan : canonical true x := by
    refine ⟨⟨fun _ => by norm_num, by norm_num⟩, ?_, by decide⟩
    intro hx2
    dsimp [x] at hx2
    linarith
  have htot : total x = 1 / 2 := by
    unfold total
    dsimp [x]
    norm_num
  have htot_pos : 0 < total x := by linarith
  have hlt1 : total x + q 0 x < 1 := by
    by_cases hlt : (total x : EReal) < critical u01Demand true 0 0 1 (1 / 2)
    · have h3 := (hq3 0 x hcan htot_pos hlt).2
      have hle := lt_of_lt_of_le h3 bar_le_one
      exact EReal.coe_lt_coe_iff.mp hle
    · have hnotpos : ¬ (0 < q 0 x) := mt (hq2 0 x hcan).mp hlt
      have hqle : q 0 x ≤ 0 := not_lt.mp hnotpos
      linarith
  have hopt := (hq1 0 x hcan).2
  change model05.control.objective 0 x (q 0 x) = model05.control.value 1 x at hopt
  unfold ShockControl.objective at hopt
  rw [value_model05 0, value_model05 1] at hopt
  have hshock : model05.control.shock = u01Demand.law := rfl
  dsimp only at hopt
  rw [hshock, expectation_zero05, stage_model05] at hopt
  simp only [mul_zero, add_zero] at hopt
  have hpos := stockCost_pos_of_lt_one hlt1
  rw [hopt] at hpos
  exact lt_irrefl _ hpos
