-- Prove2me | solution 1 for MultiItemRev.KBundling.proposition_13_i
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T15:38:40.603264+00:00
-- url     : https://prove2.me/submissions/d6944cfa-dcbd-4d6a-aa37-db388833d084

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model
import Theorems.Thm_MultiItemRev_KBundling_myerson_one_good

open MeasureTheory
open scoped NNReal ENNReal

namespace KBP13Aux
open MultiItemRev.Decomp

/-- the tangent-line estimate behind the constant `w`. -/
lemma log_bound (w : ℝ) (hw : w * Real.exp (w + 1) = 1) (r1 r2 z : ℝ) (h1 : 0 < r1)
    (h2 : 0 < r2) (hz : r1 + r2 < z) :
    r1 * r2 / z * Real.log ((z - r1) * (z - r2) / (r1 * r2)) ≤ w * (r1 + r2) := by
  have hw0 : 0 < w := by
    by_contra h
    have := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) (Real.exp_pos (w + 1)).le
    linarith
  have hlogw : Real.log w = -(w + 1) := by
    have := congrArg Real.log hw
    rw [Real.log_mul hw0.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_one] at this
    linarith
  set s := r1 + r2
  set c := r1 * r2
  have hs : 0 < s := by positivity
  have hc : 0 < c := by positivity
  have hz0 : 0 < z := by linarith
  set y := (2 * z - s) / s
  have hy : 1 < y := by rw [lt_div_iff₀ hs]; linarith
  have hy0 : 0 < y := by linarith
  set A := (z - r1) * (z - r2) / c
  have hA : 0 < A := by
    have : 0 < z - r1 := by linarith
    have : 0 < z - r2 := by linarith
    positivity
  set l := 1 / y ^ 2
  have hl : 0 < l := by positivity
  -- log A ≤ l A - 1 - log l
  have hlogA : Real.log A ≤ l * A - 1 - Real.log l := by
    have := Real.log_le_sub_one_of_pos (mul_pos hl hA)
    rw [Real.log_mul hl.ne' hA.ne'] at this
    linarith
  have hlpos : 0 ≤ l - 1 - Real.log l := by
    have := Real.log_le_sub_one_of_pos hl; linarith
  have hc4 : c ≤ s ^ 2 / 4 := by
    simp only [c, s]; nlinarith [sq_nonneg (r1 - r2)]
  have hlogl : Real.log l = -2 * Real.log y := by
    simp only [l]
    rw [one_div, Real.log_inv, Real.log_pow]; push_cast; ring
  have hcA : c * A = (z - r1) * (z - r2) := by simp only [A]; field_simp
  -- c log A ≤ (s²/2) log y
  have hkey : c * Real.log A ≤ s ^ 2 / 2 * Real.log y := by
    have e1 : c * Real.log A ≤ c * (l * A - 1 - Real.log l) := mul_le_mul_of_nonneg_left hlogA hc.le
    have e2 : c * (l * A - 1 - Real.log l) = l * ((z - r1) * (z - r2) - c) +
        c * (l - 1 - Real.log l) := by rw [← hcA]; ring
    have e3 : c * (l - 1 - Real.log l) ≤ s ^ 2 / 4 * (l - 1 - Real.log l) :=
      mul_le_mul_of_nonneg_right hc4 hlpos
    have e4 : l * ((z - r1) * (z - r2) - c) + s ^ 2 / 4 * l = s ^ 2 / 4 := by
      have : (z - r1) * (z - r2) - c + s ^ 2 / 4 = (2 * z - s) ^ 2 / 4 := by
        simp only [c, s]; ring
      have hy2 : y ^ 2 = (2 * z - s) ^ 2 / s ^ 2 := by simp only [y]; rw [div_pow]
      rw [mul_comm (s ^ 2 / 4) l, ← mul_add, this]
      have hne : 2 * z - s ≠ 0 := by linarith
      simp only [l]; rw [hy2]; field_simp
    rw [hlogl] at e3
    nlinarith
  -- log y ≤ w (y + 1)
  have hly : Real.log y ≤ w * (y + 1) := by
    have := Real.log_le_sub_one_of_pos (mul_pos hw0 hy0)
    rw [Real.log_mul hw0.ne' hy0.ne', hlogw] at this
    linarith
  have h2z : 2 * z = s * (y + 1) := by simp only [y]; field_simp; ring
  rw [div_mul_eq_mul_div, div_le_iff₀ hz0]
  calc c * Real.log A ≤ s ^ 2 / 2 * Real.log y := hkey
    _ ≤ s ^ 2 / 2 * (w * (y + 1)) := by gcongr
    _ = w * s * z := by rw [show z = s * (y + 1) / 2 by linarith]; ring

/-- the explicit integral. -/
lemma integral_formula (r1 r2 z : ℝ) (h1 : 0 < r1) (h2 : 0 < r2) (hz : r1 + r2 < z) :
    ∫ t in (r2 / (z - r1))..1, r1 * t / (z * t - r2) =
      (r1 / z * (1 + r2 / z * Real.log (z * 1 - r2))) -
        (r1 / z * (r2 / (z - r1) + r2 / z * Real.log (z * (r2 / (z - r1)) - r2))) := by
  have hz0 : 0 < z := by linarith
  have hzr : 0 < z - r1 := by linarith
  have hu0 : r2 / (z - r1) ≤ 1 := by rw [div_le_one hzr]; linarith
  have hpos : ∀ t ∈ Set.Icc (r2 / (z - r1)) 1, 0 < z * t - r2 := by
    intro t ht
    have : z * (r2 / (z - r1)) - r2 = r1 * r2 / (z - r1) := by field_simp; ring
    have h0 : 0 < z * (r2 / (z - r1)) - r2 := by rw [this]; positivity
    nlinarith [ht.1]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := fun t => r1 / z * (t + r2 / z * Real.log (z * t - r2))) hu0
  · apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.add continuousOn_id
    apply ContinuousOn.mul continuousOn_const
    exact ContinuousOn.log (by fun_prop) (fun t ht => (hpos t ht).ne')
  · intro t ht
    have hp := hpos t (Set.Ioo_subset_Icc_self ht)
    have hd : HasDerivAt (fun t => z * t - r2) z t := by
      simpa using ((hasDerivAt_id t).const_mul z).sub_const r2
    have hl := hd.log hp.ne'
    have := (((hasDerivAt_id t).add (hl.const_mul (r2 / z))).const_mul (r1 / z))
    refine this.congr_deriv ?_
    field_simp
    ring
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hu0]
    exact ContinuousOn.div (continuousOn_const.mul continuousOn_id)
      ((continuousOn_const.mul continuousOn_id).sub continuousOn_const)
      fun t ht => (hpos t ht).ne'

end KBP13Aux

namespace KBP13Aux
open MultiItemRev.Decomp

lemma tail_of (ν : Measure ℝ≥0) (r : ℝ) (hT : ∀ x : ℝ≥0, (x : ℝ≥0∞) * ν {t | x ≤ t} ≤ ENNReal.ofReal r)
    (a : ℝ) (ha : 0 < a) : ν {t : ℝ≥0 | a ≤ (t : ℝ)} ≤ ENNReal.ofReal (r / a) := by
  have hset : {t : ℝ≥0 | a ≤ (t : ℝ)} = {t | a.toNNReal ≤ t} := by
    ext t; simp [Real.toNNReal_le_iff_le_coe]
  rw [hset]
  have h := hT a.toNNReal
  have hpos : (a.toNNReal : ℝ≥0∞) ≠ 0 := by simp [ha]
  rw [ENNReal.ofReal_div_of_pos ha, ENNReal.le_div_iff_mul_le (Or.inl (by simpa using ha))
    (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  simpa [ENNReal.ofReal, ha.le] using h

/-- `z · P[X₁ + X₂ ≥ z] ≤ r₁ + r₂ + (r₁r₂/z) log((z-r₁)(z-r₂)/(r₁r₂))` (Lemma 21 as a bound). -/
lemma tail_sum (ν1 ν2 : Measure ℝ≥0) [IsProbabilityMeasure ν1] [IsProbabilityMeasure ν2]
    (r1 r2 : ℝ) (h1 : 0 < r1) (h2 : 0 < r2)
    (hT1 : ∀ x : ℝ≥0, (x : ℝ≥0∞) * ν1 {t | x ≤ t} ≤ ENNReal.ofReal r1)
    (hT2 : ∀ x : ℝ≥0, (x : ℝ≥0∞) * ν2 {t | x ≤ t} ≤ ENNReal.ofReal r2)
    (z : ℝ≥0) (hz : r1 + r2 < z) :
    (z : ℝ≥0∞) * (ν1.prod ν2) {p | z ≤ p.1 + p.2} ≤
      ENNReal.ofReal (r1 + r2 + r1 * r2 / z * Real.log ((z - r1) * (z - r2) / (r1 * r2))) := by
  set zr : ℝ := (z : ℝ) with hzrdef
  have hz0 : 0 < zr := by linarith
  have hzr1 : 0 < zr - r1 := by linarith
  set u0 := r2 / (zr - r1) with hu0def
  have hu0 : 0 < u0 := by positivity
  have hu01 : u0 ≤ 1 := by rw [div_le_one hzr1]; linarith
  -- the majorant `h` of `x ↦ P[X₂ ≥ z - x]`
  let h : ℝ≥0 → ℝ := fun x => if (x : ℝ) < zr - r2 then r2 / (zr - x) else 1
  have hmeas : Measurable h := by
    refine Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) ?_ measurable_const
    fun_prop
  have hh_nonneg : ∀ x, 0 ≤ h x := by
    intro x; simp only [h]; split_ifs with hx
    · exact div_nonneg h2.le (by linarith)
    · norm_num
  have hh_le : ∀ x, h x ≤ 1 := by
    intro x; simp only [h]; split_ifs with hx
    · rw [div_le_one (by linarith)]; linarith
    · exact le_rfl
  have hS : MeasurableSet {p : ℝ≥0 × ℝ≥0 | z ≤ p.1 + p.2} :=
    measurableSet_le measurable_const (measurable_fst.add measurable_snd)
  rw [Measure.prod_apply hS]
  -- step 1: slice bound
  have hslice : ∀ x : ℝ≥0, ν2 (Prod.mk x ⁻¹' {p : ℝ≥0 × ℝ≥0 | z ≤ p.1 + p.2}) ≤
      ENNReal.ofReal (h x) := by
    intro x
    simp only [h]
    split_ifs with hx
    · have hsub : Prod.mk x ⁻¹' {p : ℝ≥0 × ℝ≥0 | z ≤ p.1 + p.2} ⊆
          {t : ℝ≥0 | zr - x ≤ (t : ℝ)} := by
        intro t ht
        simp only [Set.mem_preimage, Set.mem_setOf_eq] at ht ⊢
        have : (z : ℝ) ≤ x + t := by exact_mod_cast ht
        linarith
      exact (measure_mono hsub).trans (tail_of ν2 r2 hT2 _ (by linarith))
    · rw [ENNReal.ofReal_one]; exact prob_le_one
  refine le_trans (mul_le_mul_of_nonneg_left (lintegral_mono hslice) (by positivity)) ?_
  -- step 2: layer cake
  rw [lintegral_eq_lintegral_meas_lt ν1 (Filter.Eventually.of_forall hh_nonneg)
    hmeas.aemeasurable]
  set f : ℝ → ℝ≥0∞ := fun t => ν1 {a | t < h a}
  have hf1 : ∀ t ∈ Set.Ioi (1 : ℝ), f t = 0 := by
    intro t ht
    simp only [f]
    convert measure_empty (μ := ν1)
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    exact (hh_le a).trans (le_of_lt ht)
  have hf2 : ∀ t ∈ Set.Ioc 0 u0, f t ≤ 1 := fun t _ => prob_le_one
  have hf3 : ∀ t ∈ Set.Ioc u0 1, f t ≤ ENNReal.ofReal (r1 * t / (zr * t - r2)) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hu0 ht.1.le
    have hzt : r1 < zr - r2 / t := by
      have : r2 / t < zr - r1 := by
        rw [div_lt_iff₀ ht0]
        have := ht.1
        rw [hu0def, div_lt_iff₀ hzr1] at this
        linarith
      linarith
    have hsub : {a : ℝ≥0 | t < h a} ⊆ {a : ℝ≥0 | zr - r2 / t ≤ (a : ℝ)} := by
      intro a ha
      simp only [Set.mem_setOf_eq, h] at ha ⊢
      split_ifs at ha with hx
      · have hpos : 0 < zr - a := by
          have : (0 : ℝ) ≤ r2 := h2.le
          linarith
        rw [lt_div_iff₀ hpos] at ha
        rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ ht0]
        linarith
      · have : r2 ≤ r2 / t := by
          rw [le_div_iff₀ ht0]; nlinarith [ht.2]
        linarith [not_lt.mp hx]
    refine (measure_mono hsub).trans ((tail_of ν1 r1 hT1 _ (by linarith)).trans ?_)
    apply le_of_eq
    congr 1
    have : zr * t - r2 = t * (zr - r2 / t) := by field_simp
    rw [this]; field_simp
  have hsplit : Set.Ioi (0 : ℝ) = (Set.Ioc 0 u0 ∪ Set.Ioc u0 1) ∪ Set.Ioi 1 := by
    rw [Set.Ioc_union_Ioc_eq_Ioc hu0.le hu01, Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
  rw [hsplit, lintegral_union measurableSet_Ioi
      (Set.disjoint_left.mpr fun t ht ht' => by
        rcases ht with ht | ht
        · exact absurd (lt_of_le_of_lt (ht.2.trans hu01) ht') (lt_irrefl _)
        · exact absurd (lt_of_le_of_lt ht.2 ht') (lt_irrefl _)),
    lintegral_union measurableSet_Ioc (Set.Ioc_disjoint_Ioc_of_le le_rfl),
    setLIntegral_congr_fun measurableSet_Ioi hf1, lintegral_zero, add_zero]
  have hI2 : ∫⁻ t in Set.Ioc 0 u0, f t ≤ ENNReal.ofReal u0 := by
    calc ∫⁻ t in Set.Ioc 0 u0, f t ≤ ∫⁻ _ in Set.Ioc 0 u0, 1 :=
          setLIntegral_mono measurable_const hf2
      _ = ENNReal.ofReal u0 := by simp [Real.volume_Ioc]
  have hint : IntervalIntegrable (fun t => r1 * t / (zr * t - r2)) MeasureTheory.volume u0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hu01]
    refine ContinuousOn.div (continuousOn_const.mul continuousOn_id)
      ((continuousOn_const.mul continuousOn_id).sub continuousOn_const) fun t ht => ?_
    have : zr * u0 - r2 = r1 * r2 / (zr - r1) := by simp only [hu0def]; field_simp; ring
    have h0 : 0 < zr * u0 - r2 := by rw [this]; positivity
    nlinarith [ht.1]
  have hnn : ∀ t ∈ Set.Ioc u0 1, 0 ≤ r1 * t / (zr * t - r2) := by
    intro t ht
    have : zr * u0 - r2 = r1 * r2 / (zr - r1) := by simp only [hu0def]; field_simp; ring
    have h0 : 0 < zr * u0 - r2 := by rw [this]; positivity
    have : 0 < zr * t - r2 := by nlinarith [ht.1]
    have : 0 < t := lt_trans hu0 ht.1
    positivity
  have hI3 : ∫⁻ t in Set.Ioc u0 1, f t ≤
      ENNReal.ofReal (∫ t in u0..1, r1 * t / (zr * t - r2)) := by
    rw [intervalIntegral.integral_of_le hu01, ofReal_integral_eq_lintegral_ofReal
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hu01).mp hint)
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall hnn))]
    exact setLIntegral_mono (by fun_prop) hf3
  rw [integral_formula r1 r2 zr h1 h2 hz] at hI3
  show (z : ℝ≥0∞) * ((∫⁻ t in Set.Ioc 0 u0, f t) + ∫⁻ t in Set.Ioc u0 1, f t) ≤ _
  calc (z : ℝ≥0∞) * ((∫⁻ t in Set.Ioc 0 u0, f t) + ∫⁻ t in Set.Ioc u0 1, f t)
      ≤ ENNReal.ofReal zr * (ENNReal.ofReal u0 + ENNReal.ofReal
          (r1 / zr * (1 + r2 / zr * Real.log (zr * 1 - r2)) -
            r1 / zr * (r2 / (zr - r1) + r2 / zr * Real.log (zr * (r2 / (zr - r1)) - r2)))) := by
        rw [ENNReal.ofReal_coe_nnreal]
        gcongr
    _ = ENNReal.ofReal (r1 + r2 + r1 * r2 / zr * Real.log ((zr - r1) * (zr - r2) / (r1 * r2))) := by
        have hF : 0 ≤ r1 / zr * (1 + r2 / zr * Real.log (zr * 1 - r2)) -
            r1 / zr * (r2 / (zr - r1) + r2 / zr * Real.log (zr * (r2 / (zr - r1)) - r2)) := by
          rw [← integral_formula r1 r2 zr h1 h2 hz]
          refine intervalIntegral.integral_nonneg hu01 fun t ht => ?_
          have : zr * u0 - r2 = r1 * r2 / (zr - r1) := by simp only [hu0def]; field_simp; ring
          have h0 : 0 < zr * u0 - r2 := by rw [this]; positivity
          have : 0 < zr * t - r2 := by nlinarith [ht.1]
          have : 0 < t := lt_of_lt_of_le hu0 ht.1
          positivity
        rw [← ENNReal.ofReal_add hu0.le hF, ← ENNReal.ofReal_mul hz0.le]
        congr 1
        have hzr2 : 0 < zr - r2 := by linarith
        have e1 : zr * (r2 / (zr - r1)) - r2 = r1 * r2 / (zr - r1) := by field_simp; ring
        have e2 : Real.log ((zr - r1) * (zr - r2) / (r1 * r2)) =
            Real.log (zr * 1 - r2) - Real.log (zr * (r2 / (zr - r1)) - r2) := by
          rw [e1, mul_one, ← Real.log_div hzr2.ne' (by positivity)]
          congr 1
          field_simp
        rw [e2]
        simp only [u0]
        field_simp
        ring

end KBP13Aux

namespace KBP13Aux
open MultiItemRev.Decomp

lemma jointLaw_oneGood (a b : Measure ℝ≥0) [IsProbabilityMeasure a] [IsProbabilityMeasure b] :
    jointLaw (oneGood a) (oneGood b) =
      (a.prod b).map (fun p => (MeasurableEquiv.sumPiEquivProdPi (fun _ : Unit ⊕ Unit => ℝ≥0)).symm
        (fun _ => p.1, fun _ => p.2)) := by
  unfold jointLaw oneGood
  rw [Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_map (MeasurableEquiv.measurable _) (by fun_prop)]
  rfl

lemma srev_jointLaw_oneGood (a b : Measure ℝ≥0) [IsProbabilityMeasure a]
    [IsProbabilityMeasure b] :
    SRev (jointLaw (oneGood a) (oneGood b)) = Rev1 a + Rev1 b := by
  unfold SRev
  rw [Fintype.sum_sum_type]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  rw [jointLaw_oneGood]
  congr 2
  · rw [Measure.map_map (by fun_prop) (by fun_prop)]
    have : ((fun x : Unit ⊕ Unit → ℝ≥0 => x (Sum.inl default)) ∘
        fun p : ℝ≥0 × ℝ≥0 => (MeasurableEquiv.sumPiEquivProdPi (fun _ : Unit ⊕ Unit => ℝ≥0)).symm
          (fun _ => p.1, fun _ => p.2)) = Prod.fst := by
      funext p; rfl
    rw [this, Measure.map_fst_prod]; simp
  · rw [Measure.map_map (by fun_prop) (by fun_prop)]
    have : ((fun x : Unit ⊕ Unit → ℝ≥0 => x (Sum.inr default)) ∘
        fun p : ℝ≥0 × ℝ≥0 => (MeasurableEquiv.sumPiEquivProdPi (fun _ : Unit ⊕ Unit => ℝ≥0)).symm
          (fun _ => p.1, fun _ => p.2)) = Prod.snd := by
      funext p; rfl
    rw [this, Measure.map_snd_prod]; simp

lemma brev_jointLaw_oneGood (a b : Measure ℝ≥0) [IsProbabilityMeasure a]
    [IsProbabilityMeasure b] :
    BRev (jointLaw (oneGood a) (oneGood b)) = Rev1 ((a.prod b).map (fun p => p.1 + p.2)) := by
  unfold BRev
  rw [jointLaw_oneGood, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 2
  funext p
  simp only [Function.comp_apply, Fintype.sum_sum_type, Finset.univ_unique,
    Finset.sum_singleton]
  rfl

end KBP13Aux

open KBP13Aux in
theorem solution (w : ℝ) (hw : w * Real.exp (w + 1) = 1)
    (ν₁ ν₂ : Measure ℝ≥0) [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] :
    ENNReal.ofReal (1 / (w + 1)) * MultiItemRev.Decomp.BRev (MultiItemRev.Decomp.jointLaw (MultiItemRev.Decomp.oneGood ν₁) (MultiItemRev.Decomp.oneGood ν₂)) ≤
      MultiItemRev.Decomp.SRev (MultiItemRev.Decomp.jointLaw (MultiItemRev.Decomp.oneGood ν₁) (MultiItemRev.Decomp.oneGood ν₂)) := by
  have hw0 : 0 < w := by
    by_contra h
    have := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) (Real.exp_pos (w + 1)).le
    linarith
  have : IsProbabilityMeasure ((ν₁.prod ν₂).map (fun p => p.1 + p.2)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  rw [srev_jointLaw_oneGood, brev_jointLaw_oneGood,
    (MultiItemRev.KBundling.myerson_one_good _).1, ENNReal.mul_iSup]
  refine iSup_le fun z => ?_
  rw [show {t : ℝ≥0 | z ≤ t} = Set.Ici z from rfl, Measure.map_apply (by fun_prop) measurableSet_Ici]
  have hT : ∀ (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] (x : ℝ≥0),
      (x : ℝ≥0∞) * ν {t | x ≤ t} ≤ MultiItemRev.Decomp.Rev1 ν := by
    intro ν _ x
    rw [(MultiItemRev.KBundling.myerson_one_good ν).1]
    exact le_iSup (fun p : ℝ≥0 => (p : ℝ≥0∞) * ν {t | p ≤ t}) x
  set R1 := MultiItemRev.Decomp.Rev1 ν₁
  set R2 := MultiItemRev.Decomp.Rev1 ν₂
  rcases eq_or_ne R1 ⊤ with h1 | h1
  · rw [h1, top_add]; exact le_top
  rcases eq_or_ne R2 ⊤ with h2 | h2
  · rw [h2, add_top]; exact le_top
  set P := (ν₁.prod ν₂) ((fun p : ℝ≥0 × ℝ≥0 => p.1 + p.2) ⁻¹' Set.Ici z)
  have hP : P = (ν₁.prod ν₂) {p | z ≤ p.1 + p.2} := rfl
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  set r1 := R1.toReal + (ε : ℝ) / 2
  set r2 := R2.toReal + (ε : ℝ) / 2
  have hε' : (0 : ℝ) < ε := hε
  have hr1 : 0 < r1 := by positivity
  have hr2 : 0 < r2 := by positivity
  have hT1 : ∀ x : ℝ≥0, (x : ℝ≥0∞) * ν₁ {t | x ≤ t} ≤ ENNReal.ofReal r1 := by
    intro x
    refine (hT ν₁ x).trans ?_
    change R1 ≤ _
    rw [← ENNReal.ofReal_toReal h1]
    exact ENNReal.ofReal_le_ofReal (by simp only [r1]; linarith)
  have hT2 : ∀ x : ℝ≥0, (x : ℝ≥0∞) * ν₂ {t | x ≤ t} ≤ ENNReal.ofReal r2 := by
    intro x
    refine (hT ν₂ x).trans ?_
    change R2 ≤ _
    rw [← ENNReal.ofReal_toReal h2]
    exact ENNReal.ofReal_le_ofReal (by simp only [r2]; linarith)
  have hmain : (z : ℝ≥0∞) * P ≤ ENNReal.ofReal ((w + 1) * (r1 + r2)) := by
    rcases le_or_gt (z : ℝ) (r1 + r2) with hz | hz
    · calc (z : ℝ≥0∞) * P ≤ (z : ℝ≥0∞) * 1 := by gcongr; exact prob_le_one
        _ = ENNReal.ofReal (z : ℝ) := by simp
        _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith)
    · rw [hP]
      refine (tail_sum ν₁ ν₂ r1 r2 hr1 hr2 hT1 hT2 z hz).trans (ENNReal.ofReal_le_ofReal ?_)
      have := log_bound w hw r1 r2 z hr1 hr2 hz
      linarith
  calc ENNReal.ofReal (1 / (w + 1)) * ((z : ℝ≥0∞) * P)
      ≤ ENNReal.ofReal (1 / (w + 1)) * ENNReal.ofReal ((w + 1) * (r1 + r2)) := by gcongr
    _ = ENNReal.ofReal (r1 + r2) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
    _ = R1 + R2 + ε := by
        rw [ENNReal.ofReal_add hr1.le hr2.le]
        simp only [r1, r2]
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity),
          ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity), ENNReal.ofReal_toReal h1,
          ENNReal.ofReal_toReal h2]
        have : ENNReal.ofReal ((ε : ℝ) / 2) + ENNReal.ofReal ((ε : ℝ) / 2) = ε := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves,
            ENNReal.ofReal_coe_nnreal]
        rw [← this]
        ring
