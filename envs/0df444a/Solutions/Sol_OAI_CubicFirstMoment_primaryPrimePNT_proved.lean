-- Prove2me | solution 1 for OAI.CubicFirstMoment.primaryPrimePNT_proved
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:57:47.402239+00:00
-- url     : https://prove2.me/submissions/c1076211-f9e8-4f3a-a1ae-dd1dc0b756ff

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A007
import Definitions.Def_OAIQ096A009

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryPrimePNTProofLogCount
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unweight a prime logarithmic mean using a moving power cutoff. -/
noncomputable section
open scoped BigOperators
open Filter Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma selectedRationalTheta_le (P : ℕ → Prop) {X : ℝ} (hX : 1 ≤ X) :
    selectedRationalTheta P X ≤ selectedRationalCount P X * Real.log X := by
  calc
    _ ≤ ∑ _p ∈ selectedRationalPrimes P X, Real.log X := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' := Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1
      exact Real.log_le_log (by exact_mod_cast hp'.2.pos)
        ((Nat.le_floor_iff (by linarith)).mp hp'.1)
    _ = _ := by simp [selectedRationalCount]

lemma selectedRationalCount_upper (P : ℕ → Prop) {X α : ℝ}
    (hX : 1 < X) (hα : 0 < α) :
    selectedRationalCount P X * Real.log X / X ≤
      selectedRationalTheta P X / X / α + (X ^ α + 1) * Real.log X / X := by
  let S := selectedRationalPrimes P X
  let U := S.filter (fun p : ℕ => (p : ℝ) ≤ X ^ α)
  let V := S.filter (fun p : ℕ => ¬ (p : ℝ) ≤ X ^ α)
  have hY : 0 ≤ X ^ α := Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one hX)) _
  have hu : U.card ≤ ⌊X ^ α⌋₊ + 1 := by
    apply (Finset.card_le_card (t := Finset.range (⌊X ^ α⌋₊ + 1)) ?_).trans_eq
      (Finset.card_range _)
    intro p hp
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le
      ((Nat.le_floor_iff hY).mpr (Finset.mem_filter.mp hp).2))
  have hv : (V.card : ℝ) * (α * Real.log X) ≤ selectedRationalTheta P X := by
    calc
      _ = ∑ _p ∈ V, α * Real.log X := by simp
      _ ≤ ∑ p ∈ V, Real.log p := by
        apply Finset.sum_le_sum
        intro p hp
        have hlt := lt_of_not_ge (Finset.mem_filter.mp hp).2
        have hl := Real.log_le_log (Real.rpow_pos_of_pos (by linarith) _) hlt.le
        simpa only [Real.log_rpow (by linarith : (0 : ℝ) < X)] using hl
      _ ≤ selectedRationalTheta P X := by
        change (∑ p ∈ V, Real.log p) ≤ ∑ p ∈ S, Real.log p
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro p hp _
        have hpP := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
        exact Real.log_nonneg (by exact_mod_cast hpP.one_lt.le)
  have hcard : (U.card : ℝ) + V.card = S.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := S)
      (fun p => (p : ℝ) ≤ X ^ α)
  have hu' : (U.card : ℝ) ≤ X ^ α + 1 := by
    exact (by exact_mod_cast hu : (U.card : ℝ) ≤ ⌊X ^ α⌋₊ + 1).trans
      (by linarith [Nat.floor_le hY])
  have hm : (0 : ℝ) ≤ α * Real.log X := mul_nonneg hα.le (Real.log_nonneg hX.le)
  have hb : selectedRationalCount P X * (α * Real.log X) ≤
      selectedRationalTheta P X + (X ^ α + 1) * (α * Real.log X) := by
    change (S.card : ℝ) * _ ≤ _
    rw [← hcard, add_mul]
    linarith [mul_le_mul_of_nonneg_right hu' hm]
  have hb' := div_le_div_of_nonneg_right hb hα.le
  have heL : selectedRationalCount P X * (α * Real.log X) / α =
      selectedRationalCount P X * Real.log X := by field_simp
  have heR : (selectedRationalTheta P X + (X ^ α + 1) * (α * Real.log X)) / α =
      selectedRationalTheta P X / α + (X ^ α + 1) * Real.log X := by
    field_simp
  rw [heL,heR] at hb'
  have hfinal := div_le_div_of_nonneg_right hb' (show 0 ≤ X by linarith)
  simpa only [add_div, div_right_comm (selectedRationalTheta P X) α X] using hfinal

lemma power_log_remainder_tendsto_zero {α : ℝ} (hα : α < 1) :
    Tendsto (fun X : ℝ => (X ^ α + 1) * Real.log X / X) atTop (𝓝 0) := by
  have h1 := (isLittleO_log_rpow_atTop (sub_pos.mpr hα)).tendsto_div_nhds_zero
  have h2 := (isLittleO_log_rpow_atTop zero_lt_one).tendsto_div_nhds_zero
  have h := h1.add h2
  norm_num only [Real.rpow_one, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  rw [Real.rpow_sub hX, Real.rpow_one]
  field_simp

/-- A positive logarithmic prime mean gives the ordinary natural-density count. -/
theorem selectedRationalCount_limit (P : ℕ → Prop) {c : ℝ} (hc : 0 < c)
    (hθ : Tendsto (fun X => selectedRationalTheta P X / X) atTop (𝓝 c)) :
    Tendsto (fun X => selectedRationalCount P X * Real.log X / X) atTop (𝓝 c) := by
  apply tendsto_order.mpr
  constructor
  · intro d hd
    filter_upwards [hθ.eventually (Ioi_mem_nhds hd), eventually_ge_atTop (1 : ℝ)] with X hXd hX
    exact hXd.trans_le (div_le_div_of_nonneg_right (selectedRationalTheta_le P hX)
      (show 0 ≤ X by linarith))
  · intro d hd
    have hd0 : 0 < d := hc.trans hd
    let α := (c + d) / (2*d)
    have hα0 : 0 < α := by dsimp [α]; positivity
    have hα1 : α < 1 := by
      dsimp [α]
      apply (div_lt_one (by positivity : 0 < 2*d)).mpr
      linarith
    have hcd : c / α < d := by
      apply (div_lt_iff₀ hα0).mpr
      have he : d * α = (c + d) / 2 := by
        dsimp [α]
        field_simp
      rw [he]
      linarith
    have hu := (hθ.div_const α).add (power_log_remainder_tendsto_zero hα1)
    simp only [add_zero] at hu
    filter_upwards [hu.eventually (Iio_mem_nhds hcd), eventually_gt_atTop (1 : ℝ)] with X hXd hX
    exact (selectedRationalCount_upper P hX hα0).trans_lt hXd

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.Sobolev
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

section lemmas

omit [NormedSpace ℝ E] in
lemma tendsto_funscale {f : ℝ → E} (hf : ContinuousAt f 0) (x : ℝ) :
    Tendsto (fun R => funscale f R x) atTop (𝓝 (f 0)) :=
  hf.tendsto.comp (by simpa using tendsto_inv_atTop_zero.mul_const x)

end lemmas

namespace CS

variable {f : CS n E} {R x v : ℝ}

lemma continuous (f : CS n E) : Continuous f := f.h1.continuous

lemma hasDerivAt (f : CS (n + 1) E) (x : ℝ) : HasDerivAt f (f.deriv x) x :=
  (f.h1.differentiable (by simp)).differentiableAt.hasDerivAt

lemma deriv_smul {f : CS (n + 1) E} : (R • f).deriv = R • f.deriv := by
  ext x ; exact (f.hasDerivAt x |>.const_smul R).deriv

lemma deriv_scale {f : CS (n + 1) E} : (f.scale R).deriv = R⁻¹ • f.deriv.scale R := by
  ext v ; by_cases hR : R = 0
  · simp [hR, scale, deriv]
  · simp only [scale, hR, ↓reduceDIte, smul_apply]
    exact ((f.hasDerivAt (R⁻¹ • v)).scomp v
      (by simpa using! (hasDerivAt_id v).const_smul R⁻¹)).deriv

lemma deriv_scale' {f : CS (n + 1) E} :
    (f.scale R).deriv v = R⁻¹ • f.deriv (R⁻¹ • v) := by
  rw [deriv_scale, smul_apply]
  by_cases hR : R = 0 <;> simp [hR, scale, funscale]

lemma hasDerivAt_scale (f : CS (n + 1) E) (R x : ℝ) :
    HasDerivAt (f.scale R) (R⁻¹ • _root_.deriv f (R⁻¹ • x)) x := by
  convert hasDerivAt (f.scale R) x ; rw [deriv_scale'] ; rfl

lemma tendsto_scale (f : CS n E) (x : ℝ) : Tendsto (fun R => f.scale R x) atTop (𝓝 (f 0)) := by
  apply (tendsto_funscale f.continuous.continuousAt x).congr'
  filter_upwards [eventually_ne_atTop 0] with R hR ; simp [scale, hR]

lemma bounded : ∃ C, ∀ v, ‖f v‖ ≤ C := by
  obtain ⟨x, hx⟩ :=
    (continuous_norm.comp f.continuous).exists_forall_ge_of_hasCompactSupport f.h2.norm
  exact ⟨_, hx⟩

end CS

namespace trunc

lemma nonneg (g : trunc) (x : ℝ) : 0 ≤ g x := (Set.indicator_nonneg (by simp) x).trans (g.h3 x)

lemma le_one (g : trunc) (x : ℝ) : g x ≤ 1 :=
  (g.h4 x).trans <| Set.indicator_le_self' (by simp) x

lemma zero (g : trunc) : g =ᶠ[𝓝 0] 1 := by
  have : Set.Icc (-1) 1 ∈ 𝓝 (0 : ℝ) := by apply Icc_mem_nhds <;> linarith
  exact eventually_of_mem this (fun x hx => le_antisymm (g.le_one x) (by simpa [hx] using g.h3 x))

@[simp] lemma zero_at {g : trunc} : g 0 = 1 := g.zero.eq_of_nhds

end trunc

namespace W1

lemma continuous (f : W1 n E) : Continuous f := f.smooth.continuous

lemma differentiable (f : W1 (n + 1) E) : Differentiable ℝ f :=
  f.smooth.differentiable (by simp)

lemma hasDerivAt (f : W1 (n + 1) E) (x : ℝ) : HasDerivAt f (f.deriv x) x :=
  f.differentiable.differentiableAt.hasDerivAt

end W1

namespace W21

variable {f : W21}

lemma norm_nonneg {f : ℝ → ℂ} : 0 ≤ norm f :=
  add_nonneg (integral_nonneg (fun t => by simp))
    (mul_nonneg (by positivity) (integral_nonneg (fun t => by simp)))

lemma hf (f : W21) : Integrable f := f.integrable zero_le_two

lemma hf' (f : W21) : Integrable (deriv f) := by
  simpa [iteratedDeriv_succ] using f.integrable one_le_two

lemma hf'' (f : W21) : Integrable (deriv (deriv f))  := by
  simpa [iteratedDeriv_succ] using f.integrable le_rfl

end W21

theorem W21_approximation (f : W21) (g : trunc) :
    Tendsto (fun R => ‖f - (g.scale R * f : W21)‖) atTop (𝓝 0) := by

  -- Definitions
  let f' := f.deriv
  let f'' := f'.deriv
  let g' := (g : CS 2 ℝ).deriv
  let g'' := g'.deriv
  let h R v := 1 - g.scale R v
  let h' R := - (g.scale R).deriv
  let h'' R := - (g.scale R).deriv.deriv

  -- Properties of h
  have ch {R} : Continuous (fun v => (h R v : ℂ)) :=
    continuous_ofReal.comp <| continuous_const.sub (CS.continuous _)
  have ch' {R} : Continuous (fun v => (h' R v : ℂ)) := continuous_ofReal.comp (CS.continuous _)
  have ch'' {R} : Continuous (fun v => (h'' R v : ℂ)) := continuous_ofReal.comp (CS.continuous _)
  have dh R v : HasDerivAt (h R) (h' R v) v := by
    convert! CS.hasDerivAt_scale (g : CS 2 ℝ) R v |>.const_sub 1 using 1
    all_goals try with_reducible_and_instances rfl
    simp [h', CS.deriv_scale', show g.deriv.toFun = deriv g.toFun from rfl]
  have dh' R v : HasDerivAt (h' R) (h'' R v) v := ((g.scale R).deriv.hasDerivAt v).neg
  have hh1 R v : |h R v| ≤ 1 := by
    by_cases hR : R = 0 <;>
      simp only [CS.scale, funscale, smul_eq_mul, hR, ↓reduceDIte, Pi.zero_apply, sub_zero,
        abs_one, le_refl, h]
    rw [abs_le] ; constructor <;>
    linarith [g.le_one (R⁻¹ * v), g.nonneg (R⁻¹ * v)]
  have vR v : Tendsto (fun R : ℝ => v * R⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul v

  -- Proof
  convert_to Tendsto (fun R => W21.norm (fun v => h R v * f v)) atTop (𝓝 0)
  · ext R ; change W21.norm _ = _ ; congr ; ext v ; simp [h, sub_mul] ; rfl
  rw [show (0 : ℝ) = 0 + ((4 * π ^ 2)⁻¹ : ℝ) * 0 by simp]
  refine Tendsto.add ?_ (Tendsto.const_mul _ ?_)

  · let F R v := ‖h R v * f v‖
    have eh v : ∀ᶠ R in atTop, h R v = 0 := by
      filter_upwards [(vR v).eventually g.zero, eventually_ne_atTop 0] with R hR hR'
      simp [h, hR, CS.scale, hR', funscale, mul_comm R⁻¹]
    have e1 : ∀ᶠ (n : ℝ) in atTop, AEStronglyMeasurable (F n) volume := by
      apply Eventually.of_forall ; intro R
      exact (ch.mul f.continuous).norm.aestronglyMeasurable
    have e2 : ∀ᶠ (n : ℝ) in atTop, ∀ᵐ (a : ℝ), ‖F n a‖ ≤ ‖f a‖ := by
      apply Eventually.of_forall ; intro R
      apply Eventually.of_forall ; intro v
      simpa [F] using mul_le_mul (hh1 R v) le_rfl (by simp) zero_le_one
    have e4 : ∀ᵐ (a : ℝ), Tendsto (fun n ↦ F n a) atTop (𝓝 0) := by
      apply Eventually.of_forall ; intro v
      apply tendsto_nhds_of_eventually_eq ; filter_upwards [eh v] with R hR ; simp [F, hR]
    simpa [F] using tendsto_integral_filter_of_dominated_convergence _ e1 e2 f.hf.norm e4

  · let F R v := ‖h'' R v * f v + 2 * h' R v * f' v + h R v * f'' v‖
    convert_to Tendsto (fun R ↦ ∫ (v : ℝ), F R v) atTop (𝓝 0)
    · have this R v :
        deriv (deriv (fun v => h R v * f v)) v =
          h'' R v * f v + 2 * h' R v * f' v + h R v * f'' v := by
        have df v : HasDerivAt f (f' v) v := f.hasDerivAt v
        have df' v : HasDerivAt f' (f'' v) v := f'.hasDerivAt v
        have l3 v : HasDerivAt (fun v => h R v * f v) (h' R v * f v + h R v * f' v) v :=
          (dh R v).ofReal_comp.mul (df v)
        have l5 : HasDerivAt (fun v => h' R v * f v) (h'' R v * f v + h' R v * f' v) v :=
          (dh' R v).ofReal_comp.mul (df v)
        have l7 : HasDerivAt (fun v => h R v * f' v) (h' R v * f' v + h R v * f'' v) v :=
          (dh R v).ofReal_comp.mul (df' v)
        have d1 : deriv (fun v => h R v * f v) = fun v => h' R v * f v + h R v * f' v :=
          funext (fun v => (l3 v).deriv)
        rw [d1] ; convert! (l5.add l7).deriv using 1 ; ring
      simp_rw [this, F]

    obtain ⟨c1, mg'⟩ := g'.bounded
    obtain ⟨c2, mg''⟩ := g''.bounded
    let bound v := c2 * ‖f v‖ + 2 * c1 * ‖f' v‖ + ‖f'' v‖
    have e1 : ∀ᶠ (n : ℝ) in atTop, AEStronglyMeasurable (F n) volume := by
      apply Eventually.of_forall ; intro R ; apply (Continuous.norm ?_).aestronglyMeasurable
      exact ((ch''.mul f.continuous).add ((continuous_const.mul ch').mul f.deriv.continuous)).add
        (ch.mul f.deriv.deriv.continuous)
    have e2 : ∀ᶠ R in atTop, ∀ᵐ (a : ℝ), ‖F R a‖ ≤ bound a := by
      have hc1 : ∀ᶠ R in atTop, ∀ v, |h' R v| ≤ c1 := by
        filter_upwards [eventually_ge_atTop 1] with R hR v
        have hR' : R ≠ 0 := by linarith
        have : 0 ≤ R := by linarith
        simp only [CS.deriv_scale, CS.neg_apply, CS.smul_apply, smul_eq_mul, abs_neg, abs_mul,
          abs_inv, abs_eq_self.mpr this, ge_iff_le, h']
        simp only [CS.scale, hR', ↓reduceDIte, funscale, smul_eq_mul]
        convert_to _ ≤ c1 * 1
        · simp
        · rw [mul_comm]
          apply mul_le_mul (mg' _)
            (inv_le_of_inv_le₀ (by linarith) (by simpa using hR)) (by positivity)
          exact (abs_nonneg _).trans (mg' 0)
      have hc2 : ∀ᶠ R in atTop, ∀ v, |h'' R v| ≤ c2 := by
        filter_upwards [eventually_ge_atTop 1] with R hR v
        have e1 : 0 ≤ R := by linarith
        have e2 : R⁻¹ ≤ 1 := inv_le_of_inv_le₀ (by linarith) (by simpa using hR)
        have e3 : R ≠ 0 := by linarith
        simp only [CS.deriv_scale, CS.deriv_smul, CS.neg_apply, CS.smul_apply, smul_eq_mul, abs_neg,
          abs_mul, abs_inv, abs_eq_self.mpr e1, ge_iff_le, h'']
        convert_to _ ≤ 1 * (1 * c2)
        · simp
        apply mul_le_mul e2 ?_ (by positivity) zero_le_one
        apply mul_le_mul e2 ?_ (by positivity) zero_le_one
        simp only [CS.scale, e3, ↓reduceDIte, funscale, smul_eq_mul] ; apply mg''
      filter_upwards [hc1, hc2] with R hc1 hc2
      apply Eventually.of_forall ; intro v ; specialize hc1 v ; specialize hc2 v
      simp only [F, bound, norm_norm]
      refine (norm_add_le _ _).trans ?_ ; apply add_le_add
      · refine (norm_add_le _ _).trans ?_ ; apply add_le_add <;> simp only [Complex.norm_mul,
        Complex.norm_ofNat, norm_real, norm_eq_abs] <;> gcongr
      · simpa using mul_le_mul (hh1 R v) le_rfl (by simp) zero_le_one
    have e3 : Integrable bound volume :=
      (((f.hf.norm).const_mul _).add ((f.hf'.norm).const_mul _)).add f.hf''.norm
    have e4 : ∀ᵐ (a : ℝ), Tendsto (fun n ↦ F n a) atTop (𝓝 0) := by
      apply Eventually.of_forall ; intro v
      have evg' : g' =ᶠ[𝓝 0] 0 := by convert! ← g.zero.deriv ; exact deriv_const' _
      have evg'' : g'' =ᶠ[𝓝 0] 0 := by convert! ← evg'.deriv ; exact deriv_const' _
      refine tendsto_norm_zero.comp <| (ZeroAtFilter.add ?_ ?_).add ?_
      · have eh'' v : ∀ᶠ R in atTop, h'' R v = 0 := by
          filter_upwards [(vR v).eventually evg'', eventually_ne_atTop 0] with R hR hR'
          simp only [CS.deriv_scale, CS.deriv_smul, CS.neg_apply, CS.smul_apply, smul_eq_mul,
            neg_eq_zero, mul_eq_zero, inv_eq_zero, hR', false_or, h'']
          simp only [CS.scale, hR', ↓reduceDIte, funscale, smul_eq_mul, mul_comm R⁻¹]
          exact hR
        apply tendsto_nhds_of_eventually_eq
        filter_upwards [eh'' v] with R hR ; simp [hR]
      · have eh' v : ∀ᶠ R in atTop, h' R v = 0 := by
          filter_upwards [(vR v).eventually evg'] with R hR
          simp [g'] at hR
          simp [h', CS.deriv_scale', mul_comm R⁻¹, hR]
        apply tendsto_nhds_of_eventually_eq
        filter_upwards [eh' v] with R hR ; simp [hR]
      · simpa [h] using! ((g.tendsto_scale v).const_sub 1).ofReal.mul tendsto_const_nhds
    simpa [F] using tendsto_integral_filter_of_dominated_convergence bound e1 e2 e3 e4
end

section
-- module Solutions.OAIQ096_CM.Fourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open FourierTransform Real Complex MeasureTheory Filter Topology BoundedContinuousFunction
  SchwartzMap VectorFourier BigOperators

theorem fourierIntegral_self_add_deriv_deriv (f : W21) (u : ℝ) :
    (1 + u ^ 2) * 𝓕 (f : ℝ → ℂ) u =
      𝓕 (fun u : ℝ => (f u - (1 / (4 * π ^ 2)) * deriv^[2] f u : ℂ)) u := by
  have l1 : Integrable (fun x => (((π : ℂ) ^ 2)⁻¹ * 4⁻¹) * deriv (deriv f) x) := by
    apply Integrable.const_mul ; simpa [iteratedDeriv_succ] using f.integrable le_rfl
  have l4 : Differentiable ℝ f := f.differentiable
  have l5 : Differentiable ℝ (deriv f) := f.deriv.differentiable
  simp [f.hf, l1, add_mul, Real.fourier_deriv f.hf' l5 f.hf'', Real.fourier_deriv f.hf l4 f.hf']
  field_simp [pi_ne_zero] ; ring_nf ; simp
end

section
-- module Solutions.OAIQ096_CM.Mathlib_Analysis_Asymptotics_Asymptotics
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Filter Topology

namespace Asymptotics

variable {α : Type*} {β : Type*} {E : Type*} {F : Type*} {G : Type*} {E' : Type*}
  {F' : Type*} {G' : Type*} {E'' : Type*} {F'' : Type*} {G'' : Type*} {R : Type*}
  {R' : Type*} {𝕜 : Type*} {𝕜' : Type*}

variable [Norm E] [Norm F] [Norm G]

variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F'] [SeminormedAddCommGroup G']
  [NormedAddCommGroup E''] [NormedAddCommGroup F''] [NormedAddCommGroup G''] [SeminormedRing R]
  [SeminormedRing R']


theorem IsBigO.natCast {f g : ℝ → E} (h : f =O[atTop] g) :
    (fun n : ℕ => f n) =O[atTop] fun n : ℕ => g n :=
  h.comp_tendsto tendsto_natCast_atTop_atTop

end Asymptotics
end

section
-- module Solutions.OAIQ096_CM.Wiener
private local instance wienerCoeRealComplex {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option linter.style.header false

-- note: the opening of ArithmeticFunction introduces a notation σ that seems
-- impossible to hide, and hence parameters that are traditionally called σ will
-- have to be called σ' instead in this file.

open Real BigOperators ArithmeticFunction MeasureTheory Filter Set FourierTransform LSeries
  Asymptotics SchwartzMap
open Complex hiding log
open scoped Topology
open scoped ContDiff
open scoped ComplexConjugate

variable {n : ℕ} {A a b c d u x y t σ' : ℝ} {ψ Ψ : ℝ → ℂ} {F G : ℂ → ℂ} {f : ℕ → ℂ} {𝕜 : Type}
  [RCLike 𝕜]


lemma nterm_eq_norm_term {f : ℕ → ℂ} : nterm f σ' n = ‖term f σ' n‖ := by
  by_cases h : n = 0 <;> simp [nterm, term, h]

theorem norm_term_eq_nterm_re (s : ℂ) :
    ‖term f s n‖ = nterm f (s.re) n := by
  simp only [nterm, term, apply_ite (‖·‖), norm_zero, norm_div]
  apply ite_congr rfl (fun _ ↦ rfl)
  intro h
  congr
  refine norm_natCast_cpow_of_pos (by omega) s

lemma hf_coe1 (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hσ : 1 < σ') :
    ∑' i, (‖term f σ' i‖₊ : ENNReal) ≠ ⊤ := by
  simp_rw [ENNReal.tsum_coe_ne_top_iff_summable_coe, ← norm_toNNReal]
  norm_cast
  apply Summable.toNNReal
  convert hf σ' hσ with i
  simp [nterm_eq_norm_term]

-- TODO - add to mathlib
attribute [fun_prop] Real.continuous_fourierChar

lemma first_fourier_aux1 (hψ : AEMeasurable ψ) {x : ℝ} (n : ℕ) : AEMeasurable fun (u : ℝ) ↦
    (‖fourierChar (-(u * ((1 : ℝ) / ((2 : ℝ) * π) * (n / x).log))) • ψ u‖ₑ : ENNReal) := by
  fun_prop

lemma first_fourier_aux2a :
    (2 : ℂ) * π * -(y * (1 / (2 * π) * Real.log ((n) / x))) = -(y * ((n) / x).log) := by
  calc
    _ = -(y * (((2 : ℂ) * π) / (2 * π) * Real.log ((n) / x))) := by ring
    _ = _ := by rw [div_self (by norm_num), one_mul]

lemma first_fourier_aux2 (hx : 0 < x) (n : ℕ) :
    term f σ' n * 𝐞 (-(y * (1 / (2 * π) * Real.log (n / x)))) • ψ y =
    term f (σ' + y * I) n • (ψ y * x ^ (y * I)) := by
  by_cases hn : n = 0
  · simp [term, hn]
  simp only [term, hn, ↓reduceIte]
  calc
    _ = (f n * (cexp ((2 * π * -(y * (1 / (2 * π) * Real.log (n / x)))) * I) /
        ↑((n : ℝ) ^ σ'))) • ψ y := by
      rw [Circle.smul_def, fourierChar_apply, ofReal_cpow (by norm_num)]
      simp only [one_div, mul_inv_rev, mul_neg, ofReal_neg, ofReal_mul, ofReal_ofNat, ofReal_inv,
        neg_mul, smul_eq_mul, ofReal_natCast]
      ring
    _ = (f n * (x ^ (y * I) / n ^ (σ' + y * I))) • ψ y := by
      congr 2
      have l1 : 0 < (n : ℝ) := by simpa using Nat.pos_iff_ne_zero.mpr hn
      have l2 : (x : ℂ) ≠ 0 := by simp [hx.ne.symm]
      have l3 : (n : ℂ) ≠ 0 := by simp [hn]
      rw [Real.rpow_def_of_pos l1, Complex.cpow_def_of_ne_zero l2, Complex.cpow_def_of_ne_zero l3]
      push_cast
      simp_rw [← Complex.exp_sub]
      congr 1
      rw [first_fourier_aux2a, Real.log_div l1.ne.symm hx.ne.symm]
      push_cast
      rw [Complex.ofReal_log hx.le]
      ring
    _ = _ := by simp ; group

set_option backward.isDefEq.respectTransparency false in
lemma first_fourier (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hsupp : Integrable ψ) (hx : 0 < x) (hσ : 1 < σ') :
    ∑' n : ℕ, term f σ' n * (𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))) =
    ∫ t : ℝ, LSeries f (σ' + t * I) * ψ t * x ^ (t * I) := by

  calc
    _ = ∑' n, term f σ' n * ∫ (v : ℝ), 𝐞 (-(v * ((1 : ℝ) /
        ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      simp only [Real.fourier_eq]
      simp only [one_div, mul_inv_rev, RCLike.inner_apply', conj_trivial]
    _ = ∑' n, ∫ (v : ℝ), term f σ' n * 𝐞 (-(v * ((1 : ℝ) /
        ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      simp [integral_const_mul]
    _ = ∫ (v : ℝ), ∑' n, term f σ' n * 𝐞 (-(v * ((1 : ℝ) /
        ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      refine (integral_tsum ?_ ?_).symm
      · refine fun _ ↦ AEMeasurable.aestronglyMeasurable ?_
        have := hsupp.aemeasurable
        fun_prop
      · simp only [enorm_mul]
        simp_rw [lintegral_const_mul'' _ (first_fourier_aux1 hsupp.aemeasurable _)]
        calc
          _ = (∑' (i : ℕ), ‖term f σ' i‖ₑ) * ∫⁻ (a : ℝ), ‖ψ a‖ₑ ∂volume := by
            simp [ENNReal.tsum_mul_right, enorm_eq_nnnorm]
          _ ≠ ⊤ := ENNReal.mul_ne_top (hf_coe1 hf hσ)
            (ne_top_of_lt hsupp.2)
    _ = _ := by
      congr 1; ext y
      simp_rw [mul_assoc (LSeries _ _), ← smul_eq_mul (a := (LSeries _ _)), LSeries]
      rw [← Summable.tsum_smul_const]
      · simp_rw [first_fourier_aux2 hx]
      · apply Summable.of_norm
        convert hf σ' hσ with n
        rw [norm_term_eq_nterm_re]
        simp



attribute [fun_prop] measurable_coe_nnreal_ennreal

lemma second_fourier_integrable_aux1a (hσ : 1 < σ') :
    IntegrableOn (fun (x : ℝ) ↦ cexp (-((x : ℂ) * ((σ' : ℂ) - 1)))) (Ici (-Real.log x)) := by
  norm_cast
  suffices IntegrableOn (fun (x : ℝ) ↦ (rexp (-(x * (σ' - 1))))) (Ici (-x.log)) _ from this.ofReal
  simp_rw [fun (a x : ℝ) ↦ (by ring : -(x * a) = -a * x)]
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  apply exp_neg_integrableOn_Ioi
  linarith

lemma second_fourier_integrable_aux1 (hcont : Measurable ψ) (hsupp : Integrable ψ) (hσ : 1 < σ') :
    let ν : Measure (ℝ × ℝ) := (volume.restrict (Ici (-Real.log x))).prod volume
    Integrable (Function.uncurry fun (u : ℝ) (a : ℝ) ↦ ((rexp (-u * (σ' - 1))) : ℂ) •
    (𝐞 (Multiplicative.ofAdd (-(a * (u / (2 * π))))) : ℂ) • ψ a) ν := by
  intro ν
  constructor
  · apply Measurable.aestronglyMeasurable
    -- `Multiplicative.ofAdd x` is definitionally `x`; unfold it by `change` since `fun_prop`
    -- does not see through it.
    change Measurable (Function.uncurry fun (u : ℝ) (a : ℝ) ↦ ((rexp (-u * (σ' - 1))) : ℂ) •
      (𝐞 (-(a * (u / (2 * π)))) : ℂ) • ψ a)
    simp only [neg_mul, ofReal_exp, ofReal_neg, ofReal_mul, ofReal_sub, ofReal_one, smul_eq_mul]
    fun_prop
  · let f1 : ℝ → ENNReal := fun a1 ↦ ‖cexp (-(↑a1 * (↑σ' - 1)))‖ₑ
    let f2 : ℝ → ENNReal := fun a2 ↦ ‖ψ a2‖ₑ
    suffices ∫⁻ (a : ℝ × ℝ), f1 a.1 * f2 a.2 ∂ν < ⊤ by
      simpa [hasFiniteIntegral_iff_enorm, enorm_eq_nnnorm, Function.uncurry]
    refine (lintegral_prod_mul ?_ ?_).trans_lt ?_ <;> try fun_prop
    exact ENNReal.mul_lt_top (second_fourier_integrable_aux1a hσ).2 hsupp.2

lemma second_fourier_integrable_aux2 (hσ : 1 < σ') :
    IntegrableOn (fun (u : ℝ) ↦ cexp ((1 - ↑σ' - ↑t * I) * ↑u)) (Ioi (-Real.log x)) := by
  refine (integrable_norm_iff (Measurable.aestronglyMeasurable <| by fun_prop)).mp ?_
  suffices IntegrableOn (fun a ↦ rexp (-(σ' - 1) * a)) (Ioi (-x.log)) _ by simpa [Complex.norm_exp]
  apply exp_neg_integrableOn_Ioi
  linarith

lemma second_fourier_aux (hx : 0 < x) :
    -(cexp (-((1 - ↑σ' - ↑t * I) * ↑(Real.log x))) / (1 - ↑σ' - ↑t * I)) =
    ↑(x ^ (σ' - 1)) * (↑σ' + ↑t * I - 1)⁻¹ * ↑x ^ (↑t * I) := by
  calc
    _ = cexp (↑(Real.log x) * ((↑σ' - 1) + ↑t * I)) * (↑σ' + ↑t * I - 1)⁻¹ := by
      rw [← div_neg]; ring_nf
    _ = (x ^ ((↑σ' - 1) + ↑t * I)) * (↑σ' + ↑t * I - 1)⁻¹ := by
      rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr (ne_of_gt hx)), Complex.ofReal_log hx.le]
    _ = (x ^ ((σ' : ℂ) - 1)) * (x ^ (↑t * I)) * (↑σ' + ↑t * I - 1)⁻¹ := by
      rw [Complex.cpow_add _ _ (ofReal_ne_zero.mpr (ne_of_gt hx))]
    _ = _ := by rw [ofReal_cpow hx.le]; push_cast; ring

set_option backward.isDefEq.respectTransparency false in
lemma second_fourier (hcont : Measurable ψ) (hsupp : Integrable ψ)
    {x σ' : ℝ} (hx : 0 < x) (hσ : 1 < σ') :
    ∫ u in Ici (-log x), Real.exp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)) =
    (x^(σ' - 1) : ℝ) * ∫ t, (1 / (σ' + t * I - 1)) * ψ t * x^(t * I) ∂ volume := by

  conv in ↑(rexp _) * _ => { rw [Real.fourier_real_eq, ← smul_eq_mul, ← integral_smul] }
  rw [MeasureTheory.integral_integral_swap]
  swap
  · exact second_fourier_integrable_aux1 hcont hsupp hσ
  rw [← integral_const_mul]
  congr 1; ext t
  dsimp [Real.fourierChar, Circle.exp]

  simp_rw [mul_smul_comm, ← smul_mul_assoc, integral_mul_const]
  rw [fun (a b d : ℂ) ↦ show a * (b * (ψ t) * d) = (a * b * d) * ψ t by ring]
  congr 1
  conv =>
    lhs
    enter [2]
    ext a
    rw [AddChar.coe_mk, Submonoid.mk_smul, smul_eq_mul]
  push_cast
  simp_rw [← Complex.exp_add]
  have (u : ℝ) :
      2 * ↑π * -(↑t * (↑u / (2 * ↑π))) * I + -↑u * (↑σ' - 1) = (1 - σ' - t * I) * u := calc
    _ = -↑u * (↑σ' - 1) + (2 * ↑π) / (2 * ↑π) * -(↑t * ↑u) * I := by ring
    _ = -↑u * (↑σ' - 1) + 1 * -(↑t * ↑u) * I := by rw [div_self (by norm_num)]
    _ = _ := by ring
  simp_rw [this]
  let c : ℂ := (1 - ↑σ' - ↑t * I)
  have : c ≠ 0 := by simp [Complex.ext_iff, c, sub_ne_zero.mpr hσ.ne]
  let f' (u : ℝ) := cexp (c * u)
  let f := fun (u : ℝ) ↦ (f' u) / c
  have hderiv : ∀ u ∈ Ici (-Real.log x), HasDerivAt f (f' u) u := by
    intro u _
    rw [show f' u = cexp (c * u) * (c * 1) / c by simp only [f']; field_simp]
    exact (hasDerivAt_id' u).ofReal_comp.const_mul c |>.cexp.div_const c
  have hf : Tendsto f atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    suffices Tendsto (fun (x : ℝ) ↦ ‖cexp (c * ↑x)‖ / ‖c‖) atTop (𝓝 (0 / ‖c‖)) by
      simpa [f, f'] using this
    apply Filter.Tendsto.div_const
    suffices Tendsto (· * (1 - σ')) atTop atBot by simpa [Complex.norm_exp, mul_comm (1 - σ'), c]
    exact Tendsto.atTop_mul_const_of_neg (by linarith) fun ⦃s⦄ h ↦ h
  rw [integral_Ici_eq_integral_Ioi,
    integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (second_fourier_integrable_aux2 hσ) hf]
  simpa [f, f'] using second_fourier_aux hx


lemma one_add_sq_pos (u : ℝ) : 0 < 1 + u ^ 2 := zero_lt_one.trans_le (by simpa using sq_nonneg u)

lemma decay_bounds_key (f : W21) (u : ℝ) : ‖𝓕 (f : ℝ → ℂ) u‖ ≤ ‖f‖ * (1 + u ^ 2)⁻¹ := by
  have l1 : 0 < 1 + u ^ 2 := one_add_sq_pos _
  have l2 : 1 + u ^ 2 = ‖(1 : ℂ) + u ^ 2‖ := by
    norm_cast ; simp only [Real.norm_eq_abs, abs_eq_self.2 l1.le]
  have l3 : ‖1 / ((4 : ℂ) * ↑π ^ 2)‖ ≤ (4 * π ^ 2)⁻¹ := by simp
  have key := fourierIntegral_self_add_deriv_deriv f u
  simp only [Function.iterate_succ _ 1, Function.iterate_one, Function.comp_apply] at key
  rw [F_sub f.hf (f.hf''.const_mul (1 / (4 * ↑π ^ 2)))] at key
  rw [← div_eq_mul_inv, le_div_iff₀ l1, mul_comm, l2, ← norm_mul, key, sub_eq_add_neg]
  apply norm_add_le _ _ |>.trans
  change _ ≤ W21.norm _
  rw [norm_neg, F_mul, norm_mul, W21.norm]
  gcongr <;> apply VectorFourier.norm_fourierIntegral_le_integral_norm

lemma decay_bounds_cor (ψ : W21) :
    ∃ C : ℝ, ∀ u, ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ C / (1 + u ^ 2) := by
  simpa only [div_eq_mul_inv] using ⟨_, decay_bounds_key ψ⟩

set_option backward.isDefEq.respectTransparency false in
@[continuity, fun_prop] lemma continuous_FourierIntegral (ψ : W21) : Continuous (𝓕 (ψ : ℝ → ℂ)) :=
  VectorFourier.fourierIntegral_continuous continuous_fourierChar
    (by simp only [innerₗ_apply_apply, RCLike.inner_apply', conj_trivial, continuous_mul])
    ψ.hf

lemma W21.integrable_fourier (ψ : W21) (hc : c ≠ 0) :
    Integrable fun u ↦ 𝓕 (ψ : ℝ → ℂ) (u / c) := by
  have l1 (C) : Integrable (fun u ↦ C / (1 + (u / c) ^ 2)) volume := by
    simpa using! (integrable_inv_one_add_sq.comp_div hc).const_mul C
  have l2 : AEStronglyMeasurable (fun u ↦ 𝓕 (ψ : ℝ → ℂ) (u / c)) volume := by
    apply Continuous.aestronglyMeasurable ; fun_prop
  obtain ⟨C, h⟩ := decay_bounds_cor ψ
  apply @Integrable.mono' ℝ ℂ _ volume _ _ (fun u => C / (1 + (u / c) ^ 2)) (l1 C) l2 ?_
  apply Eventually.of_forall (fun x => h _)





lemma continuous_LSeries_aux (hf : Summable (nterm f σ')) :
    Continuous fun x : ℝ => LSeries f (σ' + x * I) := by

  have l1 i : Continuous fun x : ℝ ↦ term f (σ' + x * I) i := by
    by_cases h : i = 0
    · simpa [h] using continuous_const
    · simpa [h] using! continuous_const.div (continuous_const.cpow (by fun_prop) (by simp [h]))
        (fun x => by simp [h])
  have l2 n (x : ℝ) : ‖term f (σ' + x * I) n‖ = nterm f σ' n := by
    by_cases h : n = 0
    · simp [h, nterm]
    · simp [h, nterm, cpow_add _ _ (Nat.cast_ne_zero.mpr h),
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero h)]
  exact continuous_tsum l1 hf (fun n x => le_of_eq (l2 n x))

-- Here compact support is used but perhaps it is not necessary
set_option backward.isDefEq.respectTransparency false in
lemma limiting_fourier_aux (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (ψ : CS 2 ℂ) (hx : 1 ≤ x) (σ' : ℝ)
    (hσ' : 1 < σ') :
    ∑' n, term f σ' n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
    A * (x ^ (1 - σ') : ℝ) * ∫ u in Ici (- log x), rexp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ)
      (u / (2 * π)) = ∫ t : ℝ, G (σ' + t * I) * ψ t * x ^ (t * I) := by
  have hint : Integrable ψ := ψ.h1.continuous.integrable_of_hasCompactSupport ψ.h2
  have l3 : 0 < x := zero_lt_one.trans_le hx
  have l1 (σ') (hσ' : 1 < σ') := first_fourier hf hint l3 hσ'
  have l2 (σ') (hσ' : 1 < σ') := second_fourier ψ.h1.continuous.measurable hint l3 hσ'
  have l8 : Continuous fun t : ℝ ↦ (x : ℂ) ^ (t * I) :=
    continuous_const.cpow (continuous_ofReal.mul continuous_const) (by simp [l3])
  have l6 : Continuous fun t : ℝ ↦ LSeries f (↑σ' + ↑t * I) * ψ t * ↑x ^ (↑t * I) := by
    apply ((continuous_LSeries_aux (hf _ hσ')).mul ψ.h1.continuous).mul l8
  have l4 : Integrable fun t : ℝ ↦ LSeries f (↑σ' + ↑t * I) * ψ t * ↑x ^ (↑t * I) := by
    exact l6.integrable_of_hasCompactSupport ψ.h2.mul_left.mul_right
  have e2 (u : ℝ) : σ' + u * I - 1 ≠ 0 := by
    intro h ; have := congr_arg Complex.re h ; simp at this ; linarith
  have l7 : Continuous fun a ↦ A * ↑(x ^ (1 - σ')) * (↑(x ^ (σ' - 1)) *
      (1 / (σ' + a * I - 1) * ψ a * x ^ (a * I))) := by
    simp only [one_div, ← mul_assoc]
    refine ((continuous_const.mul <| Continuous.inv₀ ?_ e2).mul ψ.h1.continuous).mul l8
    fun_prop
  have l5 : Integrable fun a ↦ A * ↑(x ^ (1 - σ')) * (↑(x ^ (σ' - 1)) *
      (1 / (σ' + a * I - 1) * ψ a * x ^ (a * I))) := by
    apply l7.integrable_of_hasCompactSupport
    exact ψ.h2.mul_left.mul_right.mul_left.mul_left

  simp_rw [l1 σ' hσ', l2 σ' hσ', ← integral_const_mul, ← integral_sub l4 l5]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro u
  have e1 : 1 < ((σ' : ℂ) + (u : ℂ) * I).re := by simp [hσ']
  simp_rw [hG' e1, sub_mul, ← mul_assoc]
  simp only [one_div, sub_right_inj, mul_eq_mul_right_iff, cpow_eq_zero_iff, ofReal_eq_zero, ne_eq,
    mul_eq_zero, I_ne_zero, or_false]
  left ; left
  field_simp [e2]
  norm_cast
  simp [mul_assoc, ← rpow_add l3]

section nabla

variable {α E : Type*} [OfNat α 1] [Add α] [Sub α] {u : α → ℂ}

lemma cumsum_succ [AddCommMonoid E] {u : ℕ → E} (n : ℕ) :
    cumsum u (n + 1) = cumsum u n + u n := by
  simp [cumsum, Finset.sum_range_succ]

lemma neg_cumsum [AddCommGroup E] {u : ℕ → E} : -(cumsum u) = cumsum (-u) :=
  funext (fun n => by simp [cumsum])

lemma cumsum_nonneg {u : ℕ → ℝ} (hu : 0 ≤ u) : 0 ≤ cumsum u :=
  fun _ => Finset.sum_nonneg (fun i _ => hu i)

omit [Sub α] in
lemma neg_nabla [Ring E] {u : α → E} : -(nabla u) = nnabla u := by ext n ; simp [nabla, nnabla]

end nabla

lemma Finset.sum_shift_front {E : Type*} [Ring E] {u : ℕ → E} {n : ℕ} :
    cumsum u (n + 1) = u 0 + cumsum (shift u) n := by
  simp_rw [add_comm n, cumsum, sum_range_add, sum_range_one, add_comm 1] ; rfl

lemma Finset.sum_shift_back {E : Type*} [Ring E] {u : ℕ → E} {n : ℕ} :
    cumsum u (n + 1) = cumsum u n + u n := by
  simp [cumsum, Finset.range_add_one, add_comm]

lemma summation_by_parts {E : Type*} [Ring E] {a A b : ℕ → E} (ha : a = nabla A) {n : ℕ} :
    cumsum (a * b) (n + 1) = A (n + 1) * b n - A 0 * b 0 -
    cumsum (shift A * fun i => (b (i + 1) - b i)) n := by
  have l1 : ∑ x ∈ Finset.range (n + 1), A (x + 1) * b x = ∑ x ∈ Finset.range n,
      A (x + 1) * b x + A (n + 1) * b n :=
    Finset.sum_shift_back
  have l2 : ∑ x ∈ Finset.range (n + 1), A x * b x = A 0 * b 0 + ∑ x ∈ Finset.range n,
      A (x + 1) * b (x + 1) :=
    Finset.sum_shift_front
  simp only [cumsum, ha, Pi.mul_apply, nabla, sub_mul, Finset.sum_sub_distrib, l1, l2, shift,
    mul_sub]
  abel

lemma summation_by_parts' {E : Type*} [Ring E] {a b : ℕ → E} {n : ℕ} :
    cumsum (a * b) (n + 1) = cumsum a (n + 1) * b n - cumsum (shift (cumsum a) * nabla b) n := by
  simpa using! summation_by_parts (a := a) (b := b) (A := cumsum a) (by simp)

lemma summation_by_parts'' {E : Type*} [Ring E] {a b : ℕ → E} :
    shift (cumsum (a * b)) = shift (cumsum a) * b - cumsum (shift (cumsum a) * nabla b) := by
  ext n ; apply summation_by_parts'

lemma summable_iff_bounded {u : ℕ → ℝ} (hu : 0 ≤ u) :
    Summable u ↔ BoundedAtFilter atTop (cumsum u) := by
  have l1 : (cumsum u =O[atTop] 1) ↔ _ := isBigO_one_nat_atTop_iff
  have l2 n : ‖cumsum u n‖ = cumsum u n := by simpa using cumsum_nonneg hu n
  simp only [BoundedAtFilter, l1, l2]
  constructor <;> intro ⟨C, h1⟩
  · exact ⟨C, fun n => sum_le_hasSum _ (fun i _ => hu i) h1⟩
  · exact summable_of_sum_range_le hu h1

lemma Filter.EventuallyEq.summable {u v : ℕ → ℝ} (h : u =ᶠ[atTop] v) (hu : Summable v) :
    Summable u :=
  summable_of_isBigO_nat hu h.isBigO

lemma summable_congr_ae {u v : ℕ → ℝ} (huv : u =ᶠ[atTop] v) : Summable u ↔ Summable v := by
  constructor <;> intro h <;> simp [huv.summable, huv.symm.summable, h]

lemma BoundedAtFilter.add_const {u : ℕ → ℝ} {c : ℝ} :
    BoundedAtFilter atTop (fun n => u n + c) ↔ BoundedAtFilter atTop u := by
  have : u = fun n => (u n + c) + (-c) := by ext n ; ring
  simp only [BoundedAtFilter]
  constructor <;> intro h
  on_goal 1 => rw [this]
  all_goals { exact h.add (const_boundedAtFilter _ _) }

lemma BoundedAtFilter.comp_add {u : ℕ → ℝ} {N : ℕ} :
    BoundedAtFilter atTop (fun n => u (n + N)) ↔ BoundedAtFilter atTop u := by
  simp only [BoundedAtFilter, isBigO_iff, norm_eq_abs, Pi.one_apply,
    eventually_atTop]
  constructor <;> intro ⟨C, n₀, h⟩ <;> use C
  · refine ⟨n₀ + N, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (m := N) (n := n) (by grind)
    exact h _ <| Nat.add_le_add_iff_right.mp hn
  · exact ⟨n₀, fun n hn => h _ (by grind)⟩

lemma summable_iff_bounded' {u : ℕ → ℝ} (hu : ∀ᶠ n in atTop, 0 ≤ u n) :
    Summable u ↔ BoundedAtFilter atTop (cumsum u) := by
  obtain ⟨N, hu⟩ := eventually_atTop.mp hu
  have e2 : cumsum (fun i ↦ u (i + N)) = fun n => cumsum u (n + N) - cumsum u N := by
    ext n ; simp_rw [cumsum, add_comm _ N, Finset.sum_range_add] ; ring
  rw [← summable_nat_add_iff N, summable_iff_bounded (fun n => hu _ <| Nat.le_add_left N n), e2]
  simp_rw [sub_eq_add_neg, BoundedAtFilter.add_const, BoundedAtFilter.comp_add]

lemma bounded_of_shift {u : ℕ → ℝ} (h : BoundedAtFilter atTop (shift u)) :
    BoundedAtFilter atTop u := by
  simp only [BoundedAtFilter, isBigO_iff, eventually_atTop] at h ⊢
  obtain ⟨C, N, hC⟩ := h
  refine ⟨C, N + 1, fun n hn => ?_⟩
  simp only [shift] at hC
  have r1 : n - 1 ≥ N := Nat.le_sub_one_of_lt hn
  have r2 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  simpa [r2] using hC (n - 1) r1

lemma dirichlet_test' {a b : ℕ → ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hAb : BoundedAtFilter atTop (shift (cumsum a) * b)) (hbb : ∀ᶠ n in atTop, b (n + 1) ≤ b n)
    (h : Summable (shift (cumsum a) * nnabla b)) : Summable (a * b) := by
  have l1 : ∀ᶠ n in atTop, 0 ≤ (shift (cumsum a) * nnabla b) n := by
    filter_upwards [hbb] with n hb
    exact mul_nonneg (by simpa [shift] using! Finset.sum_nonneg (fun n _ ↦ ha n)) (sub_nonneg.mpr hb)
  rw [summable_iff_bounded (mul_nonneg ha hb)]
  rw [summable_iff_bounded' l1] at h
  apply bounded_of_shift
  simpa only [summation_by_parts'', sub_eq_add_neg, neg_cumsum, ← mul_neg, neg_nabla]
    using hAb.add h

lemma exists_antitone_of_eventually {u : ℕ → ℝ} (hu : ∀ᶠ n in atTop, u (n + 1) ≤ u n) :
    ∃ v : ℕ → ℝ, range v ⊆ range u ∧ Antitone v ∧ v =ᶠ[atTop] u := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hu
  let v (n : ℕ) := u (if n < N then N else n)
  refine ⟨v, ?_, ?_, ?_⟩
  · exact fun x ⟨n, hn⟩ => ⟨if n < N then N else n, hn⟩
  · refine antitone_nat_of_succ_le (fun n => ?_)
    by_cases h : n < N
    · by_cases h' : n + 1 < N <;> simp [v, h, h']
      have : n + 1 = N := by linarith
      simp [this]
    · have : ¬(n + 1 < N) := by linarith
      simp only [this, ↓reduceIte, h, ge_iff_le, v] ; apply hN ; linarith
  · have : ∀ᶠ n in atTop, ¬(n < N) := by simpa using ⟨N, fun b hb => by linarith⟩
    filter_upwards [this] with n hn ; simp [v, hn]

lemma summable_inv_mul_log_sq : Summable (fun n : ℕ => (n * (Real.log n) ^ 2)⁻¹) := by
  let u (n : ℕ) := (n * (Real.log n) ^ 2)⁻¹
  have l7 : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n :=
    tendsto_atTop.mp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop) 1
  have l8 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  have l9 : ∀ᶠ n in atTop, u (n + 1) ≤ u n := by
    filter_upwards [l7, l8] with n l2 l8; dsimp [u]; gcongr <;> simp
  obtain ⟨v, l1, l2, l3⟩ := exists_antitone_of_eventually l9
  rw [summable_congr_ae l3.symm]
  have l4 (n : ℕ) : 0 ≤ v n := by obtain ⟨k, hk⟩ := l1 ⟨n, rfl⟩ ; rw [← hk] ; positivity
  apply (summable_condensed_iff_of_nonneg l4 (fun _ _ _ a ↦ l2 a)).mp
  suffices this : ∀ᶠ k : ℕ in atTop, 2 ^ k * v (2 ^ k) = ((k : ℝ) ^ 2)⁻¹ * ((Real.log 2) ^ 2)⁻¹ by
    exact (summable_congr_ae this).mpr <| (Real.summable_nat_pow_inv.mpr one_lt_two).mul_right _
  have l5 : ∀ᶠ k in atTop, v (2 ^ k) = u (2 ^ k) :=
    l3.comp_tendsto <| tendsto_pow_atTop_atTop_of_one_lt Nat.le.refl
  filter_upwards [l5, l8] with k l5 l8
  simp only [l5, mul_inv_rev, Nat.cast_pow, Nat.cast_ofNat, log_pow, u]
  field_simp

lemma tendsto_mul_add_atTop {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (fun x => a * x + b) atTop atTop :=
  tendsto_atTop_add_const_right _ b (tendsto_id.const_mul_atTop ha)

lemma isLittleO_const_of_tendsto_atTop {α : Type*} [Preorder α] (a : ℝ) {f : α → ℝ}
    (hf : Tendsto f atTop atTop) : (fun _ => a) =o[atTop] f := by
  simp [tendsto_norm_atTop_atTop.comp hf]

lemma isLittleO_mul_add_sq (a b : ℝ) : (fun x => a * x + b) =o[atTop] (fun x => x ^ 2) := by
  apply IsLittleO.add
  · apply IsLittleO.const_mul_left ; simpa using isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) one_lt_two
  · apply isLittleO_const_of_tendsto_atTop _ <| tendsto_pow_atTop (by linarith)

lemma log_mul_add_isBigO_log {a : ℝ} (ha : 0 < a) (b : ℝ) :
    (fun x => Real.log (a * x + b)) =O[atTop] Real.log := by
  apply IsBigO.of_bound (2 : ℕ)
  have l2 : ∀ᶠ x : ℝ in atTop, 0 ≤ log x := tendsto_atTop.mp tendsto_log_atTop 0
  have l3 : ∀ᶠ x : ℝ in atTop, 0 ≤ log (a * x + b) :=
    tendsto_atTop.mp (tendsto_log_atTop.comp (tendsto_mul_add_atTop ha b)) 0
  have l5 : ∀ᶠ x : ℝ in atTop, 1 ≤ a * x + b := tendsto_atTop.mp (tendsto_mul_add_atTop ha b) 1
  have l1 : ∀ᶠ x : ℝ in atTop, a * x + b ≤ x ^ 2 := by
    filter_upwards [(isLittleO_mul_add_sq a b).eventuallyLE, l5] with x r2 l5
    simpa [abs_eq_self.mpr (zero_le_one.trans l5)] using r2
  filter_upwards [l1, l2, l3, l5] with x l1 l2 l3 l5
  simpa [abs_eq_self.mpr l2, abs_eq_self.mpr l3, Real.log_pow] using
    Real.log_le_log (by linarith) l1

lemma isBigO_log_mul_add {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Real.log =O[atTop] (fun x => Real.log (a * x + b)) := by
  convert! (log_mul_add_isBigO_log (b := -b / a) (inv_pos.mpr ha)).comp_tendsto
    (tendsto_mul_add_atTop (b := b) ha) using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [Function.comp_apply]
  congr
  field_simp
  simp

lemma log_isbigo_log_div {d : ℝ} (hb : 0 < d) :
    (fun n ↦ Real.log n) =O[atTop] (fun n ↦ Real.log (n / d)) := by
  convert isBigO_log_mul_add (inv_pos.mpr hb) 0 using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [add_zero]; field_simp)

lemma Asymptotics.IsBigO.add_isLittleO_right {f g : ℝ → ℝ} (h : g =o[atTop] f) :
    f =O[atTop] (f + g) := by
  rw [isLittleO_iff] at h ; specialize h (c := 2⁻¹) (by norm_num)
  rw [isBigO_iff'']
  refine ⟨2⁻¹, by norm_num, ?_⟩
  filter_upwards [h] with x h
  simp only [norm_eq_abs, Pi.add_apply] at h ⊢
  calc _ = |f x| - 2⁻¹ * |f x| := by ring
       _ ≤ |f x| - |g x| := by linarith
       _ ≤ |(|f x| - |g x|)| := le_abs_self _
       _ ≤ _ := by rw [← sub_neg_eq_add, ← abs_neg (g x)] ; exact abs_abs_sub_abs_le (f x) (-g x)

lemma Asymptotics.IsBigO.sq {α : Type*} [Preorder α] {f g : α → ℝ} (h : f =O[atTop] g) :
    (fun n ↦ f n ^ 2) =O[atTop] (fun n => g n ^ 2) := by
  simpa [pow_two] using h.mul h

lemma log_sq_isbigo_mul {a b : ℝ} (hb : 0 < b) :
    (fun x ↦ Real.log x ^ 2) =O[atTop] (fun x ↦ a + Real.log (x / b) ^ 2) := by
  apply (log_isbigo_log_div hb).sq.trans ; simp_rw [add_comm a]
  refine IsBigO.add_isLittleO_right <| isLittleO_const_of_tendsto_atTop _ ?_
  exact (tendsto_pow_atTop two_ne_zero).comp <|
    tendsto_log_atTop.comp <| tendsto_id.atTop_div_const hb

theorem log_add_div_isBigO_log (a : ℝ) {b : ℝ} (hb : 0 < b) :
    (fun x ↦ Real.log ((x + a) / b)) =O[atTop] fun x ↦ Real.log x := by
  convert log_mul_add_isBigO_log (inv_pos.mpr hb) (a / b) using 3 <;> first | rfl | ring

lemma log_add_one_sub_log_le {x : ℝ} (hx : 0 < x) : nabla Real.log x ≤ x⁻¹ := by
  have l1 : ContinuousOn Real.log (Icc x (x + 1)) := by
    apply continuousOn_log.mono ; intro t ⟨h1, _⟩ ; simp ; linarith
  have l2 t (ht : t ∈ Ioo x (x + 1)) : HasDerivAt Real.log t⁻¹ t :=
    Real.hasDerivAt_log (by linarith [ht.1])
  obtain ⟨t, ⟨ht1, _⟩, htx⟩ := exists_hasDerivAt_eq_slope Real.log (·⁻¹) (by linarith) l1 l2
  simp only [add_sub_cancel_left, div_one] at htx
  rw [nabla, ← htx, inv_le_inv₀ (by linarith) hx]
  exact ht1.le

lemma nabla_log_main : nabla Real.log =O[atTop] fun x ↦ 1 / x := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_gt_atTop 0] with x l1
  have l2 : log x ≤ log (x + 1) := log_le_log l1 (by linarith)
  simpa [nabla, abs_eq_self.mpr l1.le, abs_eq_self.mpr (sub_nonneg.mpr l2)] using
    log_add_one_sub_log_le l1

lemma nabla_log {b : ℝ} (hb : 0 < b) :
    nabla (fun x => Real.log (x / b)) =O[atTop] (fun x => 1 / x) := by
  refine EventuallyEq.trans_isBigO ?_ nabla_log_main
  filter_upwards [eventually_gt_atTop 0] with x l2
  rw [nabla, log_div (by linarith) (by linarith), log_div l2.ne.symm (by linarith), nabla] ; ring

lemma nnabla_mul_log_sq (a : ℝ) {b : ℝ} (hb : 0 < b) :
    nabla (fun x => x * (a + Real.log (x / b) ^ 2)) =O[atTop] (fun x => Real.log x ^ 2) := by

  have l1 : nabla (fun n => n * (a + Real.log (n / b) ^ 2)) = fun n =>
      a + Real.log ((n + 1) / b) ^ 2 +
        (n * (Real.log ((n + 1) / b) ^ 2 - Real.log (n / b) ^ 2)) := by
    ext n ; simp [nabla] ; ring
  have l2 := (isLittleO_const_of_tendsto_atTop a
    ((tendsto_pow_atTop two_ne_zero).comp tendsto_log_atTop)).isBigO
  have l3 := (log_add_div_isBigO_log 1 hb).sq
  have l4 : (fun x => Real.log ((x + 1) / b) + Real.log (x / b)) =O[atTop] Real.log := by
    simpa using (log_add_div_isBigO_log _ hb).add (log_add_div_isBigO_log 0 hb)
  have e2 : (fun x : ℝ => x * (Real.log x * (1 / x))) =ᶠ[atTop] Real.log := by
    filter_upwards [eventually_ge_atTop 1] with x hx using by field_simp
  have l5 : (fun n ↦ n * (Real.log n * (1 / n))) =O[atTop] (fun n ↦ (Real.log n) ^ 2) :=
    e2.trans_isBigO
      (by simpa using! (isLittleO_mul_add_sq 1 0).isBigO.comp_tendsto Real.tendsto_log_atTop)

  simp_rw [l1, _root_.sq_sub_sq]
  exact ((l2.add l3).add (isBigO_refl (·) atTop |>.mul (l4.mul (nabla_log hb)) |>.trans l5))

lemma nnabla_bound_aux1 (a : ℝ) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun x => x * (a + Real.log (x / b) ^ 2)) atTop atTop :=
  tendsto_id.atTop_mul_atTop₀ <| tendsto_atTop_add_const_left _ _ <|
    (tendsto_pow_atTop two_ne_zero).comp <| tendsto_log_atTop.comp <| tendsto_id.atTop_div_const hb

lemma nnabla_bound_aux2 (a : ℝ) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ x in atTop, 0 < x * (a + Real.log (x / b) ^ 2) :=
  (nnabla_bound_aux1 a hb).eventually (eventually_gt_atTop 0)

lemma Real.log_eventually_gt_atTop (a : ℝ) :
    ∀ᶠ x in atTop, a < Real.log x :=
  Real.tendsto_log_atTop.eventually (eventually_gt_atTop a)

lemma nnabla_bound_aux {x : ℝ} (hx : 0 < x) :
    nnabla (fun n ↦ 1 / (n * ((2 * π) ^ 2 + Real.log (n / x) ^ 2))) =O[atTop]
    (fun n ↦ 1 / (Real.log n ^ 2 * n ^ 2)) := by

  let d n : ℝ := n * ((2 * π) ^ 2 + Real.log (n / x) ^ 2)
  change (fun x_1 ↦ nnabla (fun n ↦ 1 / d n) x_1) =O[atTop] _

  have l2 : ∀ᶠ n in atTop, 0 < d n := (nnabla_bound_aux2 ((2 * π) ^ 2) hx)
  have l3 : ∀ᶠ n in atTop, 0 < d (n + 1) :=
    (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id).eventually l2
  have l1 : ∀ᶠ n : ℝ in atTop,
      nnabla (fun n ↦ 1 / d n) n = (d (n + 1) - d n) * (d n)⁻¹ * (d (n + 1))⁻¹ := by
    filter_upwards [l2, l3] with n l2 l3
    rw [nnabla, one_div, one_div, inv_sub_inv l2.ne.symm l3.ne.symm, div_eq_mul_inv, mul_inv,
      mul_assoc]

  have l4 : (fun n => (d n)⁻¹) =O[atTop] (fun n => (n * (Real.log n) ^ 2)⁻¹) := by
    apply IsBigO.inv_rev
    · refine (isBigO_refl _ _).mul <| (log_sq_isbigo_mul hx)
    · filter_upwards [Real.log_eventually_gt_atTop 0, eventually_gt_atTop 0] with x hx hx'
      rw [← not_imp_not]
      intro _
      positivity
  have l5 : (fun n => (d (n + 1))⁻¹) =O[atTop] (fun n => (n * (Real.log n) ^ 2)⁻¹) := by
    refine IsBigO.trans ?_ l4
    rw [isBigO_iff]; use 1
    have e3 : ∀ᶠ n in atTop, d n ≤ d (n + 1) := by
      filter_upwards [eventually_ge_atTop x] with n hn
      have e2 : 1 ≤ n / x := (one_le_div hx).mpr hn
      have : 0 ≤ n := hx.le.trans hn
      simp only [d]
      gcongr <;> simp [Real.log_nonneg, *]
    filter_upwards [l2, l3, e3] with n e1 e2 e3
    simp_rw [one_mul]
    exact norm_lt_norm_of_nonneg _ _ (inv_nonneg.2 e2.le) (inv_anti₀ e1 e3)

  have l6 : (fun n => d (n + 1) - d n) =O[atTop] (fun n => (Real.log n) ^ 2) := by
    simpa [d, nabla] using! (nnabla_mul_log_sq ((2 * π) ^ 2) hx)

  apply EventuallyEq.trans_isBigO l1

  apply ((l6.mul l4).mul l5).trans_eventuallyEq
  filter_upwards [eventually_ge_atTop 2, Real.log_eventually_gt_atTop 0] with n hn hn'
  field_simp

lemma nnabla_bound (C : ℝ) {x : ℝ} (hx : 0 < x) :
    nnabla (fun n => C / (1 + (Real.log (n / x) / (2 * π)) ^ 2) / n) =O[atTop]
    (fun n => (n ^ 2 * (Real.log n) ^ 2)⁻¹) := by
  field_simp
  simp only [div_eq_mul_inv, mul_inv, nnabla_mul, one_mul]
  apply IsBigO.const_mul_left
  simpa [div_eq_mul_inv, mul_pow, mul_comm] using nnabla_bound_aux hx

lemma cheby.bigO (h : cheby f) : cumsum (‖f ·‖) =O[atTop] ((↑) : ℕ → ℝ) := by
  have l1 : 0 ≤ cumsum (‖f ·‖) := cumsum_nonneg (fun _ => norm_nonneg _)
  obtain ⟨C, hC⟩ := h
  apply isBigO_of_le' (c := C) atTop
  intro n
  rw [Real.norm_eq_abs, abs_eq_self.mpr (l1 n)]
  simpa using hC n

lemma limiting_fourier_lim1_aux (hcheby : cheby f) (hx : 0 < x) (C : ℝ) (hC : 0 ≤ C) :
    Summable fun n ↦ ‖f n‖ / ↑n * (C / (1 + (1 / (2 * π) * Real.log (↑n / x)) ^ 2)) := by

  let a (n : ℕ) := (C / (1 + (Real.log (↑n / x) / (2 * π)) ^ 2) / ↑n)
  replace hcheby := hcheby.bigO

  have l1 : shift (cumsum (‖f ·‖)) =O[atTop] (fun n : ℕ => (↑(n + 1) : ℝ)) :=
    hcheby.comp_tendsto <| tendsto_add_atTop_nat 1
  have l2 : shift (cumsum (‖f ·‖)) =O[atTop] (fun n => (n : ℝ)) :=
    l1.trans
      (by simpa using (isBigO_refl _ _).add <| isBigO_iff.mpr ⟨1, by simpa using ⟨1, by tauto⟩⟩)
  have l5 : BoundedAtFilter atTop (fun n : ℕ => C / (1 + (Real.log (↑n / x) / (2 * π)) ^ 2)) := by
    simp only [BoundedAtFilter]
    field_simp
    apply isBigO_of_le' (c := C) ; intro n
    have : 0 ≤ 2 ^ 2 * π ^ 2 + Real.log (n / x) ^ 2 := by positivity
    simp only [norm_div, norm_mul, norm_eq_abs, abs_eq_self.mpr hC, norm_pow,
      abs_eq_self.mpr pi_nonneg, abs_eq_self.mpr this, Pi.one_apply, one_mem,
      CStarRing.norm_of_mem_unitary, mul_one, ge_iff_le, Nat.abs_ofNat]
    apply div_le_of_le_mul₀ this hC
    rw [mul_add, ← mul_assoc]
    apply le_add_of_le_of_nonneg le_rfl
    positivity
  have l3 : a =O[atTop] (fun n => 1 / (n : ℝ)) := by
    simpa [a] using! IsBigO.mul l5 (isBigO_refl (fun n : ℕ => 1 / (n : ℝ)) _)
  have l4 : nnabla a =O[atTop] (fun n : ℕ => (n ^ 2 * (Real.log n) ^ 2)⁻¹) := by
    convert (nnabla_bound C hx).natCast ; simp [nnabla, a]

  simp_rw [div_mul_eq_mul_div, mul_div_assoc, one_mul]
  apply dirichlet_test'
  · intro n ; exact norm_nonneg _
  · intro n ; positivity
  · apply (l2.mul l3).trans_eventuallyEq
    apply eventually_of_mem (Ici_mem_atTop 1)
    intro x (hx : 1 ≤ x)
    have : x ≠ 0 := Nat.one_le_iff_ne_zero.mp hx
    simp [this]
  · have : ∀ᶠ n : ℕ in atTop, x ≤ n := by simpa using eventually_ge_atTop ⌈x⌉₊
    filter_upwards [this] with n hn
    have e1 : 0 < (n : ℝ) := by linarith
    have e2 : 1 ≤ n / x := (one_le_div hx).mpr hn
    have e3 := Nat.le_succ n
    gcongr
    refine div_nonneg (Real.log_nonneg e2) (by norm_num [pi_nonneg])
  · apply summable_of_isBigO_nat summable_inv_mul_log_sq
    apply (l2.mul l4).trans_eventuallyEq
    apply eventually_of_mem (Ici_mem_atTop 2)
    intro x (hx : 2 ≤ x)
    have : (x : ℝ) ≠ 0 := by simp ; linarith
    have : Real.log x ≠ 0 := by
      have ll : 2 ≤ (x : ℝ) := by simp [hx]
      simp
      grind
    field_simp

theorem limiting_fourier_lim1 (hcheby : cheby f) (ψ : W21) (hx : 0 < x) :
    Tendsto (fun σ' : ℝ ↦
        ∑' n, term f σ' n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (n / x))) (𝓝[>] 1)
      (𝓝 (∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (n / x)))) := by

  obtain ⟨C, hC⟩ := decay_bounds_cor ψ
  have : 0 ≤ C := by simpa using (norm_nonneg _).trans (hC 0)
  refine tendsto_tsum_of_dominated_convergence
    (limiting_fourier_lim1_aux hcheby hx C this) (fun n => ?_) ?_
  · apply Tendsto.mul_const
    by_cases h : n = 0 <;> simp only [term, h, ↓reduceIte, CharP.cast_eq_zero, div_zero,
      tendsto_const_nhds_iff]
    refine tendsto_const_nhds.div ?_ (by simp [h])
    simpa using ((continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds).const_cpow
  · rw [eventually_nhdsWithin_iff]
    apply Eventually.of_forall
    intro σ' (hσ' : 1 < σ') n
    rw [norm_mul, ← nterm_eq_norm_term]
    refine mul_le_mul ?_ (hC _) (norm_nonneg _) (div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
    by_cases h : n = 0 <;> simp only [nterm, h, ↓reduceIte, CharP.cast_eq_zero, div_zero, le_refl]
    have : 1 ≤ (n : ℝ) := by simpa using! Nat.pos_iff_ne_zero.mpr h
    refine div_le_div₀ (norm_nonneg _) le_rfl (by simpa [Nat.pos_iff_ne_zero]) ?_
    simpa using Real.rpow_le_rpow_of_exponent_le this hσ'.le

theorem limiting_fourier_lim2_aux (x : ℝ) (C : ℝ) :
    Integrable (fun t ↦ max |x| 1 * (C / (1 + (t / (2 * π)) ^ 2)))
      (Measure.restrict volume (Ici (-Real.log x))) := by
  simp_rw [div_eq_mul_inv C]
  exact (((integrable_inv_one_add_sq.comp_div
    (by simp [pi_ne_zero])).const_mul _).const_mul _).restrict

theorem limiting_fourier_lim2 (A : ℝ) (ψ : W21) (hx : 1 ≤ x) :
    Tendsto (fun σ' ↦ A * ↑(x ^ (1 - σ')) *
        ∫ u in Ici (-Real.log x), rexp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)))
      (𝓝[>] 1) (𝓝 (A * ∫ u in Ici (-Real.log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)))) := by

  obtain ⟨C, hC⟩ := decay_bounds_cor ψ
  apply Tendsto.mul
  · suffices h : Tendsto (fun σ' : ℝ ↦ ofReal (x ^ (1 - σ'))) (𝓝[>] 1) (𝓝 1) by
      simpa using h.const_mul ↑A
    suffices h : Tendsto (fun σ' : ℝ ↦ x ^ (1 - σ')) (𝓝[>] 1) (𝓝 1) from
      (continuous_ofReal.tendsto 1).comp h
    have : Tendsto (fun σ' : ℝ ↦ σ') (𝓝 1) (𝓝 1) := fun _ a ↦ a
    have : Tendsto (fun σ' : ℝ ↦ 1 - σ') (𝓝[>] 1) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds (by simpa using this.const_sub 1)
    simpa using tendsto_const_nhds.rpow this (Or.inl (zero_lt_one.trans_le hx).ne.symm)
  · refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_
      (limiting_fourier_lim2_aux x C) ?_
    · apply Eventually.of_forall ; intro σ'
      apply Continuous.aestronglyMeasurable
      have := continuous_FourierIntegral ψ
      continuity
    · apply eventually_of_mem (U := Ioo 1 2)
      · apply Ioo_mem_nhdsGT_of_mem ; simp
      · intro σ' ⟨h1, h2⟩
        rw [ae_restrict_iff' measurableSet_Ici]
        apply Eventually.of_forall
        intro t (ht : - Real.log x ≤ t)
        rw [norm_mul]
        have hdom_nonneg : 0 ≤ max |x| 1 := by
          exact (abs_nonneg x).trans (le_max_left _ _)
        refine mul_le_mul ?_ (hC _) (norm_nonneg _) hdom_nonneg
        simp only [neg_mul, ofReal_exp, ofReal_neg, ofReal_mul, ofReal_sub, ofReal_one, norm_exp,
          neg_re, mul_re, ofReal_re, sub_re, one_re, ofReal_im, sub_im, one_im, sub_self, mul_zero,
          sub_zero]
        have : -Real.log x * (σ' - 1) ≤ t * (σ' - 1) := mul_le_mul_of_nonneg_right ht (by linarith)
        have : -(t * (σ' - 1)) ≤ Real.log x * (σ' - 1) := by simpa using neg_le_neg this
        have := Real.exp_monotone this
        apply this.trans
        have l1 : σ' - 1 ≤ 1 := by linarith
        have : 0 ≤ Real.log x := Real.log_nonneg hx
        have := mul_le_mul_of_nonneg_left l1 this
        refine (Real.exp_monotone this).trans ?_
        have hxabs : |x| = x := abs_of_nonneg (zero_le_one.trans hx)
        calc
          Real.exp (Real.log x * 1) = |x| := by
            simpa [mul_one, hxabs] using (Real.exp_log (zero_lt_one.trans_le hx))
          _ ≤ max |x| 1 := le_max_left _ _
    · apply Eventually.of_forall
      intro x
      suffices h : Tendsto (fun n ↦ ((rexp (-x * (n - 1))) : ℂ)) (𝓝[>] 1) (𝓝 1) by
        simpa using h.mul_const _
      apply Tendsto.mono_left ?_ nhdsWithin_le_nhds
      suffices h : Continuous (fun n ↦ ((rexp (-x * (n - 1))) : ℂ)) by simpa using h.tendsto 1
      continuity

theorem limiting_fourier_lim3 (hG : ContinuousOn G {s | 1 ≤ s.re}) (ψ : CS 2 ℂ) (hx : 1 ≤ x) :
    Tendsto (fun σ' : ℝ ↦ ∫ t : ℝ, G (σ' + t * I) * ψ t * x ^ (t * I)) (𝓝[>] 1)
      (𝓝 (∫ t : ℝ, G (1 + t * I) * ψ t * x ^ (t * I))) := by

  by_cases hh : tsupport ψ = ∅
  · simp [tsupport_eq_empty_iff.mp hh]
  obtain ⟨a₀, ha₀⟩ := Set.nonempty_iff_ne_empty.mpr hh

  let S : Set ℂ := reProdIm (Icc 1 2) (tsupport ψ)
  have l1 : IsCompact S := by
    refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨?_, ?_⟩
    · exact isClosed_Icc.reProdIm (isClosed_tsupport ψ)
    · exact (Metric.isBounded_Icc 1 2).reProdIm ψ.h2.isBounded
  have l2 : S ⊆ {s : ℂ | 1 ≤ s.re} := fun z hz => (mem_reProdIm.mp hz).1.1
  have l3 : ContinuousOn (‖G ·‖) S := (hG.mono l2).norm
  have l4 : S.Nonempty := ⟨1 + a₀ * I, by simp [S, mem_reProdIm, ha₀]⟩
  obtain ⟨z, -, hmax⟩ := l1.exists_isMaxOn l4 l3
  let MG := ‖G z‖
  let bound (a : ℝ) : ℝ := MG * ‖ψ a‖

  apply tendsto_integral_filter_of_dominated_convergence (bound := bound)
  · apply eventually_of_mem (U := Icc 1 2) (Icc_mem_nhdsGT_of_mem (by simp)) ; intro u hu
    apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · exact (hG.comp_continuous (by fun_prop) (by simp [hu.1])).mul ψ.h1.continuous
    · apply Continuous.const_cpow (by fun_prop) ; simp ; linarith
  · apply eventually_of_mem (U := Icc 1 2) (Icc_mem_nhdsGT_of_mem (by simp))
    intro u hu
    apply Eventually.of_forall ; intro v
    by_cases h : v ∈ tsupport ψ
    · have r1 : u + v * I ∈ S := by simp [S, mem_reProdIm, hu.1, hu.2, h]
      have r2 := isMaxOn_iff.mp hmax _ r1
      have r4 : (x : ℂ) ≠ 0 := by simp ; linarith
      have r5 : arg x = 0 := by simp [arg_eq_zero_iff] ; linarith
      have r3 : ‖(x : ℂ) ^ (v * I)‖ = 1 := by simp [norm_cpow_of_ne_zero r4, r5]
      simp_rw [norm_mul, r3, mul_one]
      exact mul_le_mul_of_nonneg_right r2 (norm_nonneg _)
    · have : v ∉ Function.support ψ := fun a ↦ h (subset_tsupport ψ a)
      simp at this ; simp [this, bound]

  · suffices h : Continuous bound by exact h.integrable_of_hasCompactSupport ψ.h2.norm.mul_left
    have := ψ.h1.continuous ; fun_prop
  · apply Eventually.of_forall ; intro t
    apply Tendsto.mul_const
    apply Tendsto.mul_const
    refine (hG (1 + t * I) (by simp)).tendsto.comp <| tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact ((continuous_ofReal.tendsto _).add tendsto_const_nhds).mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall (fun x (hx : 1 < x) => by simp [hx.le])

lemma limiting_fourier (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (ψ : CS 2 ℂ) (hx : 1 ≤ x) :
    ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)) =
      ∫ (t : ℝ), (G (1 + t * I)) * (ψ t) * x ^ (t * I) := by

  have l1 := limiting_fourier_lim1 hcheby ψ (by linarith)
  have l2 := limiting_fourier_lim2 A ψ hx
  have l3 := limiting_fourier_lim3 hG ψ hx
  apply tendsto_nhds_unique_of_eventuallyEq (l1.sub l2) l3
  simpa [eventuallyEq_nhdsWithin_iff] using! Eventually.of_forall (limiting_fourier_aux hG' hf ψ hx)




set_option backward.isDefEq.respectTransparency false in
lemma limiting_cor_aux {f : ℝ → ℂ} : Tendsto (fun x : ℝ ↦ ∫ t, f t * x ^ (t * I)) atTop (𝓝 0) := by

  have l1 : ∀ᶠ x : ℝ in atTop, ∀ t : ℝ, x ^ (t * I) = exp (log x * t * I) := by
    filter_upwards [eventually_ne_atTop 0, eventually_ge_atTop 0] with x hx hx' t
    rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx), ofReal_log hx'] ; ring_nf

  have l2 : ∀ᶠ x : ℝ in atTop, ∫ t, f t * x ^ (t * I) = ∫ t, f t * exp (log x * t * I) := by
    filter_upwards [l1] with x hx
    refine integral_congr_ae (Eventually.of_forall (fun x => by simp [hx]))

  simp_rw [tendsto_congr' l2]
  convert_to Tendsto (fun x => 𝓕 f (-Real.log x / (2 * π))) atTop (𝓝 0)
  · ext ; congr ; ext
    simp only [← ofReal_mul, mul_comm (f _), fourierChar, Circle.exp, ContinuousMap.coe_mk,
      innerₗ_apply_apply, RCLike.inner_apply, conj_trivial, AddChar.coe_mk, mul_neg, ofReal_neg,
      neg_mul]
    congr
    rw [← neg_mul] ; congr ; norm_cast ; field_simp
  refine (Real.zero_at_infty_fourier f).comp <| Tendsto.mono_right ?_ _root_.atBot_le_cocompact
  exact (tendsto_neg_atBot_iff.mpr tendsto_log_atTop).atBot_mul_const (inv_pos.mpr two_pi_pos)

lemma limiting_cor (ψ : CS 2 ℂ) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun x : ℝ ↦ ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))) atTop (𝓝 0) := by

  apply limiting_cor_aux.congr'
  filter_upwards [eventually_ge_atTop 1] with x hx using
    limiting_fourier hcheby hG hG' hf ψ hx |>.symm





lemma one_div_sub_one (n : ℕ) : 1 / (↑(n - 1) : ℝ) ≤ 2 / n := by
  match n with
  | 0 => simp
  | 1 => simp
  | n + 2 => { norm_cast ; rw [div_le_div_iff₀] <;> simp [mul_add] <;> linarith }

lemma pp_pos {a : ℝ} (ha : a ∈ Ioo (-1) 1) (x : ℝ) : 0 < pp a x := by
  simp only [pp]
  have : 0 < 1 - a := by linarith [ha.2]
  have : 0 < 1 + a := by linarith [ha.1]
  positivity

lemma hh_nonneg (a : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ hh a t := by dsimp only [hh] ; positivity

lemma hh_deriv (a : ℝ) {t : ℝ} (ht : t ≠ 0) : HasDerivAt (hh a) (hh' a t) t := by
  have e1 : t * (1 + (a * log t) ^ 2) ≠ 0 := mul_ne_zero ht (_root_.ne_of_lt (by positivity)).symm
  have l5 : HasDerivAt (fun t : ℝ => log t) t⁻¹ t := Real.hasDerivAt_log ht
  have l4 : HasDerivAt (fun t : ℝ => a * log t) (a * t⁻¹) t := l5.const_mul _
  have l3 : HasDerivAt (fun t : ℝ => (a * log t) ^ 2) (2 * a ^ 2 * t⁻¹ * log t) t := by
    convert! l4.pow 2 using 1 ; ring
  have l2 : HasDerivAt (fun t : ℝ => 1 + (a * log t) ^ 2) (2 * a ^ 2 * t⁻¹ * log t) t :=
    l3.const_add _
  have l1 : HasDerivAt (fun t : ℝ => t * (1 + (a * log t) ^ 2))
      (1 + 2 * a ^ 2 * log t + a ^ 2 * log t ^ 2) t := by
    convert! (hasDerivAt_id' t).mul l2 using 1; field_simp; ring
  convert! l1.inv e1 using 1; simp only [hh', pp, hh]; field_simp; ring

lemma hh_continuous (a : ℝ) : ContinuousOn (hh a) (Ioi 0) :=
  fun t (ht : 0 < t) => (hh_deriv a ht.ne.symm).continuousAt.continuousWithinAt

lemma hh'_nonpos {a x : ℝ} (ha : a ∈ Ioo (-1) 1) : hh' a x ≤ 0 := by
  have := pp_pos ha (log x)
  simp only [hh', neg_mul, Left.neg_nonpos_iff, ge_iff_le]
  positivity

lemma hh_antitone {a : ℝ} (ha : a ∈ Ioo (-1) 1) : AntitoneOn (hh a) (Ioi 0) := by
  have l1 x (hx : x ∈ interior (Ioi 0)) :
      HasDerivWithinAt (hh a) (hh' a x) (interior (Ioi 0)) x := by
    have : x ≠ 0 := by contrapose! hx ; simp [hx]
    exact (hh_deriv a this).hasDerivWithinAt
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi _) (hh_continuous _) l1
    (fun x _ => hh'_nonpos ha)

lemma gg_of_hh {x : ℝ} (hx : x ≠ 0) (i : ℝ) : gg x i = x⁻¹ * hh (1 / (2 * π)) (i / x) := by
  simp only [gg, hh]
  field_simp

lemma gg_le_one (i : ℕ) : gg x i ≤ 1 := by
  by_cases hi : i = 0 <;> simp only [gg, hi, CharP.cast_eq_zero, div_zero, one_div, mul_inv_rev,
    zero_div, Real.log_zero, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero, inv_one, mul_one, zero_le_one]
  have l1 : 1 ≤ (i : ℝ) := by simp ; omega
  have l2 : 1 ≤ 1 + (π⁻¹ * 2⁻¹ * Real.log (↑i / x)) ^ 2 := by
    simp only [le_add_iff_nonneg_right] ; positivity
  rw [← mul_inv] ; apply inv_le_one_of_one_le₀ ; simpa using mul_le_mul l1 l2 zero_le_one (by simp)

lemma one_div_two_pi_mem_Ioo : 1 / (2 * π) ∈ Ioo (-1) 1 := by
  constructor
  · trans 0
    · linarith
    · positivity
  · rw [div_lt_iff₀ (by positivity)]
    convert_to! 1 * 1 < 2 * π
    · simp
    · simp
    apply mul_lt_mul one_lt_two ?_ zero_lt_one zero_le_two
    trans 2
    · exact one_le_two
    · exact two_le_pi

lemma cancel_aux {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i * g i ≤ g (n - 1) * (C * n) + (C * (↑(n - 1 - 1) + 1) * g 0
      - C * (↑(n - 1 - 1) + 1) * g (n - 1) -
    ((n - 1 - 1) • (C * g 0) - ∑ x ∈ Finset.range (n - 1 - 1), C * g (x + 1))) := by

  have l1 (n : ℕ) :
      (g n - g (n + 1)) * ∑ i ∈ Finset.range (n + 1), f i ≤ (g n - g (n + 1)) * (C * (n + 1)) := by
    apply mul_le_mul le_rfl (by simpa using! hf' (n + 1)) (Finset.sum_nonneg (fun n _ ↦ hf n)) ?_
    simp only [sub_nonneg] ; apply hg' ; simp
  have l2 (x : ℕ) : C * (↑(x + 1) + 1) - C * (↑x + 1) = C := by simp ; ring
  have l3 (n : ℕ) : 0 ≤ cumsum f n := Finset.sum_nonneg (fun n _ ↦ hf n)

  convert_to ∑ i ∈ Finset.range n, (g i) • (f i) ≤ _
  · simp [mul_comm]
  rw [Finset.sum_range_by_parts, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  simp_rw [← neg_smul, neg_sub, smul_eq_mul]
  apply _root_.add_le_add
  · exact mul_le_mul le_rfl (hf' n) (l3 n) (hg _)
  · apply Finset.sum_le_sum (fun n _ => l1 n) |>.trans
    convert_to! ∑ i ∈ Finset.range (n - 1), (C * (↑i + 1)) • (g i - g (i + 1)) ≤ _
    · congr ; ext i ; simp ; ring
    rw [Finset.sum_range_by_parts]
    simp_rw [Finset.sum_range_sub', l2, smul_sub, smul_eq_mul, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range]
    apply le_of_eq ; ring_nf

lemma sum_range_succ (a : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, a (i + 1) = (∑ i ∈ Finset.range (n + 1), a i) - a 0 := by
  have := Finset.sum_range_sub a n
  rw [Finset.sum_sub_distrib, sub_eq_iff_eq_add] at this
  rw [Finset.sum_range_succ, this] ; ring

lemma cancel_aux' {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i * g i ≤
        C * n * g (n - 1)
      + C * cumsum g (n - 1 - 1 + 1)
      - C * (↑(n - 1 - 1) + 1) * g (n - 1)
      := by
  have := cancel_aux hf hg hf' hg' n
  simp only [nsmul_eq_mul, ← Finset.mul_sum, sum_range_succ] at this
  convert this using 1 <;> first | (with_reducible_and_instances rfl) | (unfold cumsum ; ring)

lemma cancel_main' {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hf0 : f 0 = 0) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    cumsum (f * g) n ≤ C * cumsum g n := by
  match n with
  | 0 => simp [cumsum]
  | 1 => specialize hg 0 ; specialize hf' 1 ; simp only [cumsum, Finset.range_one,
    Finset.sum_singleton, hf0, Nat.cast_one, mul_one, Pi.zero_apply, Pi.mul_apply, zero_mul,
    ge_iff_le] at hf' hg ⊢ ; positivity
  | n + 2 => convert! cancel_aux' hf hg hf' hg' (n + 2) using 1 ; simp [cumsum_succ] ; ring

theorem sum_le_integral {x₀ : ℝ} {f : ℝ → ℝ} {n : ℕ} (hf : AntitoneOn f (Ioc x₀ (x₀ + n)))
    (hfi : IntegrableOn f (Icc x₀ (x₀ + n))) :
    (∑ i ∈ Finset.range n, f (x₀ + ↑(i + 1))) ≤ ∫ x in x₀..x₀ + n, f x := by

  cases n with simp only [Nat.cast_add, Nat.cast_one, CharP.cast_eq_zero, add_zero,
      lt_self_iff_false, not_false_eq_true,
    Ioc_eq_empty, Finset.range_zero, Nat.cast_add, Nat.cast_one, Finset.sum_empty,
    intervalIntegral.integral_same, le_refl] at hf ⊢
  | succ n =>
  have : Finset.range (n + 1) = {0} ∪ Finset.Ico 1 (n + 1) := by
    ext i ; by_cases hi : i = 0 <;> simp [hi] ; omega
  simp only [this, Finset.singleton_union, Finset.mem_Ico, nonpos_iff_eq_zero, one_ne_zero,
    lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, and_true, not_false_eq_true,
    Finset.sum_insert, CharP.cast_eq_zero, zero_add, ge_iff_le]

  have l4 : IntervalIntegrable f volume x₀ (x₀ + 1) := by
    apply IntegrableOn.intervalIntegrable
    simp only [le_add_iff_nonneg_right, zero_le_one, uIcc_of_le]
    apply hfi.mono_set
    apply Icc_subset_Icc le_rfl
    simp
  have l5 x (hx : x ∈ Ioc x₀ (x₀ + 1)) : (fun x ↦ f (x₀ + 1)) x ≤ f x := by
    rcases hx with ⟨hx1, hx2⟩
    refine hf ⟨hx1, by linarith⟩ ⟨by linarith, by linarith⟩ hx2
  have l6 : ∫ x in x₀..x₀ + 1, f (x₀ + 1) = f (x₀ + 1) := by simp

  have l1 : f (x₀ + 1) ≤ ∫ x in x₀..x₀ + 1, f x := by
    rw [← l6] ; apply intervalIntegral.integral_mono_ae_restrict (by linarith) (by simp) l4
    apply eventually_of_mem _ l5
    have : (Ioc x₀ (x₀ + 1))ᶜ ∩ Icc x₀ (x₀ + 1) = {x₀} := by simp [← sdiff_eq_compl_inter]
    rw [mem_ae_iff, Measure.restrict_apply measurableSet_Ioc.compl, this]
    simp

  have l2 : AntitoneOn (fun x ↦ f (x₀ + x)) (Icc 1 ↑(n + 1)) := by
    intro u ⟨hu1, _⟩ v ⟨_, hv2⟩ huv ; push_cast at hv2
    refine hf ⟨?_, ?_⟩ ⟨?_, ?_⟩ ?_ <;> linarith

  have l3 := @AntitoneOn.sum_le_integral_Ico 1 (n + 1) (fun x => f (x₀ + x)) (by simp)
    (by simpa using l2)

  simp only [Nat.cast_add, Nat.cast_one, intervalIntegral.integral_comp_add_left] at l3
  convert! _root_.add_le_add l1 l3

  have := @intervalIntegral.integral_comp_mul_add ℝ _ _ 1 (n + 1) 1 f one_ne_zero x₀
  rw [intervalIntegral.integral_add_adjacent_intervals]
  · exact l4
  · apply IntegrableOn.intervalIntegrable
    simp only [add_le_add_iff_left, le_add_iff_nonneg_left, Nat.cast_nonneg, uIcc_of_le]
    apply hfi.mono_set
    apply Icc_subset_Icc
    · linarith
    · simp

lemma hh_integrable_aux (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (IntegrableOn (fun t ↦ a * hh b (t / c)) (Ici 0)) ∧
    (∫ (t : ℝ) in Ioi 0, a * hh b (t / c) = a * c / b * π) := by

  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  simp only [hh]

  let g (x : ℝ) := (a * c / b) * Real.arctan (b * log (x / c))
  let g₀ (x : ℝ) := if x = 0 then ((a * c / b) * (- (π / 2))) else g x
  let g' (x : ℝ) := a * (x / c * (1 + (b * Real.log (x / c)) ^ 2))⁻¹

  have l3 (x) (hx : 0 < x) : HasDerivAt Real.log x⁻¹ x := by apply Real.hasDerivAt_log (by linarith)
  have l4 (x) : HasDerivAt (fun t => t / c) (1 / c) x := (hasDerivAt_id x).div_const c
  have l2 (x) (hx : 0 < x) : HasDerivAt (fun t => log (t / c)) x⁻¹ x := by
    have := @HasDerivAt.comp _ _ _ _ _ _ (fun t => t / c) _ _ _  (l3 (x / c) (by positivity)) (l4 x)
    convert! this using 1 ; field_simp
  have l5 (x) (hx : 0 < x) := (l2 x hx).const_mul b
  have l1 (x) (hx : 0 < x) := (l5 x hx).arctan
  have l6 (x) (hx : 0 < x) : HasDerivAt g (g' x) x := by
    convert! (l1 x hx).const_mul (a * c / b) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [g']
    field_simp
  have key (x) (hx : 0 < x) : HasDerivAt g₀ (g' x) x := by
    apply (l6 x hx).congr_of_eventuallyEq
    apply eventually_of_mem <| Ioi_mem_nhds hx
    intro y (hy : 0 < y)
    simp [g₀, hy.ne.symm]

  have k1 : Tendsto g₀ atTop (𝓝 ((a * c / b) * (π / 2))) := by
    have : g =ᶠ[atTop] g₀ := by
      apply eventually_of_mem (Ioi_mem_atTop 0)
      intro y (hy : 0 < y)
      simp [g₀, hy.ne.symm]
    apply Tendsto.congr' this
    apply Tendsto.const_mul
    apply (tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
    apply Tendsto.const_mul_atTop hb
    apply tendsto_log_atTop.comp
    apply Tendsto.atTop_div_const hc
    apply tendsto_id

  have k2 : Tendsto g₀ (𝓝[>] 0) (𝓝 (g₀ 0)) := by
    have : g =ᶠ[𝓝[>] 0] g₀ := by
      apply eventually_of_mem self_mem_nhdsWithin
      intro x (hx : 0 < x) ; simp [g₀, hx.ne.symm]
    simp only [g₀]
    apply Tendsto.congr' this
    apply Tendsto.const_mul
    apply (tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp
    apply Tendsto.const_mul_atBot hb
    apply tendsto_log_nhdsGT_zero.comp
    rw [Metric.tendsto_nhdsWithin_nhdsWithin]
    intro ε hε
    refine ⟨c * ε, by positivity, fun x hx1 hx2 => ⟨?_, ?_⟩⟩
    · simp only [mem_Ioi] at hx1 ⊢ ; positivity
    · simp only [dist_zero_right, norm_eq_abs, norm_div, abs_eq_self.mpr hc.le] at hx2 ⊢
      rwa [div_lt_iff₀ hc, mul_comm]

  have k3 : ContinuousWithinAt g₀ (Ici 0) 0 := by
    rw [Metric.continuousWithinAt_iff]
    rw [Metric.tendsto_nhdsWithin_nhds] at k2
    intro ε hε
    obtain ⟨δ, hδ, h⟩ := k2 ε hε
    refine ⟨δ, hδ, fun {x} hx hd => ?_⟩
    rcases le_iff_lt_or_eq.mp (Set.mem_Ici.mp hx) with hx | hx
    · exact h hx hd
    · simp [g₀, ← hx, hε]

  have k4 : ∀ x ∈ Ioi 0, 0 ≤ g' x := by
    intro x (hx : 0 < x) ; simp only [mul_inv_rev, inv_div, g'] ; positivity

  constructor
  · convert_to IntegrableOn g' _
    exact integrableOn_Ioi_deriv_of_nonneg k3 key k4 k1
  · have := integral_Ioi_of_hasDerivAt_of_nonneg k3 key k4 k1
    simp only [mul_inv_rev, inv_div, mul_neg, ↓reduceIte, sub_neg_eq_add, g', g₀] at this ⊢
    convert this using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp ; ring)

lemma hh_integrable (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    IntegrableOn (fun t ↦ a * hh b (t / c)) (Ici 0) :=
  hh_integrable_aux ha hb hc |>.1

lemma hh_integral (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∫ (t : ℝ) in Ioi 0, a * hh b (t / c) = a * c / b * π :=
  hh_integrable_aux ha hb hc |>.2

lemma hh_integral' : ∫ t in Ioi 0, hh (1 / (2 * π)) t = 2 * π ^ 2 := by
  have := hh_integral (a := 1) (b := 1 / (2 * π)) (c := 1)
    (by positivity) (by positivity) (by positivity)
  convert this using 1 <;> first | (with_reducible_and_instances rfl) | (simp <;> ring)

lemma bound_sum_log {C : ℝ} (hf0 : f 0 = 0) (hf : chebyWith C f) {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤
      C * (1 + ∫ t in Ioi 0, hh (1 / (2 * π)) t) := by

  let ggg (i : ℕ) : ℝ := if i = 0 then 1 else gg x i

  have l0 : x ≠ 0 := by linarith
  have l1 i : 0 ≤ ggg i := by by_cases hi : i = 0 <;> simp only [gg, one_div, mul_inv_rev, hi,
    ↓reduceIte, zero_le_one, ggg] ; positivity
  have l2 : Antitone ggg := by
    intro i j hij ; by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp only [hj, ↓reduceIte, hi,
      le_refl, ggg]
    · exact gg_le_one _
    · omega
    · simp only [gg_of_hh l0]
      gcongr
      apply hh_antitone one_div_two_pi_mem_Ioo
      · simp only [mem_Ioi] ; positivity
      · simp only [mem_Ioi] ; positivity
      · gcongr
  have l3 : 0 ≤ C := by simpa [cumsum, hf0] using hf 1

  have l4 : 0 ≤ ∫ (t : ℝ) in Ioi 0, hh (π⁻¹ * 2⁻¹) t :=
    setIntegral_nonneg measurableSet_Ioi (fun x hx => hh_nonneg _ (LT.lt.le hx))

  have l5 {n : ℕ} : AntitoneOn (fun t ↦ x⁻¹ * hh (1 / (2 * π)) (t / x)) (Ioc 0 n) := by
    intro u ⟨hu1, _⟩ v ⟨hv1, _⟩ huv
    simp only
    apply mul_le_mul le_rfl ?_ (hh_nonneg _ (by positivity)) (by positivity)
    apply hh_antitone one_div_two_pi_mem_Ioo (by simp only [mem_Ioi] ; positivity)
      (by simp only [mem_Ioi] ; positivity)
    apply (div_le_div_iff_of_pos_right (by positivity)).mpr huv

  have l6 {n : ℕ} : IntegrableOn (fun t ↦ x⁻¹ * hh (π⁻¹ * 2⁻¹) (t / x)) (Icc 0 n) volume := by
    apply IntegrableOn.mono_set
      (hh_integrable (by positivity) (by positivity) (by positivity)) Icc_subset_Ici_self

  apply Real.tsum_le_of_sum_range_le (fun n => by positivity) ; intro n
  convert_to! ∑ i ∈ Finset.range n, ‖f i‖ * ggg i ≤ _
  · congr ; ext i
    by_cases hi : i = 0
    · simp [hi, hf0]
    · simp only [gg, hi, ↓reduceIte, ggg]
      field_simp

  apply cancel_main' (fun _ => norm_nonneg _) (by simp [hf0]) l1 hf l2 n |>.trans
  gcongr ; simp only [cumsum, gg_of_hh l0, one_div, mul_inv_rev, ggg]

  by_cases hn : n = 0
  · simp only [hn, Finset.range_zero, Finset.sum_empty] ; positivity
  replace hn : 0 < n := by omega
  have : Finset.range n = {0} ∪ Finset.Ico 1 n := by
    ext i ; simp ; by_cases hi : i = 0 <;> simp [hi, hn] ; omega
  simp only [this, Finset.singleton_union, Finset.mem_Ico, nonpos_iff_eq_zero, one_ne_zero,
    false_and, not_false_eq_true, Finset.sum_insert, ↓reduceIte, add_le_add_iff_left, ge_iff_le]
  convert_to! ∑ x_1 ∈ Finset.Ico 1 n, x⁻¹ * hh (π⁻¹ * 2⁻¹) (↑x_1 / x) ≤ _
  · apply Finset.sum_congr rfl (fun i hi => ?_)
    simp at hi
    have : i ≠ 0 := by omega
    simp [this]
  simp_rw [Finset.sum_Ico_eq_sum_range, add_comm 1]
  have := @sum_le_integral 0 (fun t => x⁻¹ * hh (π⁻¹ * 2⁻¹) (t / x)) (n - 1)
    (by simpa using l5) (by simpa using l6)
  simp only [zero_add] at this
  apply this.trans
  rw [@intervalIntegral.integral_comp_div ℝ _ _ 0 ↑(n - 1) x (fun t => x⁻¹ * hh (π⁻¹ * 2⁻¹) (t)) l0]
  simp only [zero_div, intervalIntegral.integral_const_mul, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ l0, one_mul]
  have : (0 : ℝ) ≤ ↑(n - 1) / x := by positivity
  rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
  simp only [this, ↓reduceIte, uIoc_of_le, smul_eq_mul, one_mul, ge_iff_le]
  apply integral_mono_measure
  · apply Measure.restrict_mono Ioc_subset_Ioi_self le_rfl
  · apply eventually_of_mem (self_mem_ae_restrict measurableSet_Ioi)
    intro x (hx : 0 < x)
    apply hh_nonneg _ hx.le
  · have := (@hh_integrable 1 (1 / (2 * π)) 1 (by positivity) (by positivity) (by positivity))
    simpa using! this.mono_set Ioi_subset_Ici_self

lemma bound_sum_log0 {C : ℝ} (hf : chebyWith C f) {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤
      C * (1 + ∫ t in Ioi 0, hh (1 / (2 * π)) t) := by

  let f0 i := if i = 0 then 0 else f i
  have l1 : chebyWith C f0 := by
    intro n ; refine Finset.sum_le_sum (fun i _ => ?_) |>.trans (hf n)
    by_cases hi : i = 0 <;> simp [hi, f0]
  have l2 i : ‖f i‖ / i = ‖f0 i‖ / i := by by_cases hi : i = 0 <;> simp [hi, f0]
  simp_rw [l2] ; apply bound_sum_log rfl l1 hx

lemma bound_sum_log' {C : ℝ} (hf : chebyWith C f) {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤ C * (1 + 2 * π ^ 2) := by
  simpa only [hh_integral'] using bound_sum_log0 hf hx

variable (f x) in
lemma summable_fourier_aux (ψ : W21) (i : ℕ) :
    ‖f i / i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (i / x))‖ ≤
      W21.norm ψ * (‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹) := by
  convert! mul_le_mul_of_nonneg_left (decay_bounds_key ψ (1 / (2 * π) * log (i / x)))
    (norm_nonneg (f i / i)) using 1
  · simp
  · change _ = _ * (W21.norm ψ * _)
    simp only [W21.norm, mul_inv_rev, one_div, Complex.norm_div, RCLike.norm_natCast]
    ring

lemma summable_fourier (x : ℝ) (hx : 0 < x) (ψ : W21) (hcheby : cheby f) :
    Summable fun i ↦ ‖f i / ↑i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑i / x))‖ := by
  have l5 : Summable fun i ↦ ‖f i‖ / ↑i * ((1 + (1 / (2 * ↑π) * ↑(Real.log (↑i / x))) ^ 2)⁻¹) := by
    simpa using limiting_fourier_lim1_aux hcheby hx 1 (zero_le_one' ℝ)
  have l6 := summable_fourier_aux x f ψ
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) l6
    (by simpa using l5.const_smul (W21.norm ψ))

lemma bound_I1 (x : ℝ) (hx : 0 < x) (ψ : W21) (hcheby : cheby f) :
    ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))‖ ≤
    W21.norm ψ • ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ := by

  have l5 : Summable fun i ↦ ‖f i‖ / ↑i * ((1 + (1 / (2 * ↑π) * ↑(Real.log (↑i / x))) ^ 2)⁻¹) := by
    simpa using limiting_fourier_lim1_aux hcheby hx 1 (zero_le_one' ℝ)
  have l6 := summable_fourier_aux x f ψ
  have l1 : Summable fun i ↦ ‖f i / ↑i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑i / x))‖ := by
    exact summable_fourier x hx ψ hcheby
  apply (norm_tsum_le_tsum_norm l1).trans
  simpa only [← Summable.tsum_const_smul _ l5] using!
    Summable.tsum_mono l1 (by simpa using l5.const_smul (W21.norm ψ)) l6

lemma bound_I1' {C : ℝ} (x : ℝ) (hx : 1 ≤ x) (ψ : W21) (hcheby : chebyWith C f) :
    ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))‖ ≤
      W21.norm ψ * C * (1 + 2 * π ^ 2) := by

  apply bound_I1 x (by linarith) ψ ⟨_, hcheby⟩ |>.trans
  rw [smul_eq_mul, mul_assoc]
  apply mul_le_mul le_rfl (bound_sum_log' hcheby hx) ?_ W21.norm_nonneg
  apply tsum_nonneg (fun i => by positivity)

lemma bound_I2 (x : ℝ) (ψ : W21) :
    ‖∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))‖ ≤ W21.norm ψ * (2 * π ^ 2) := by

  have key a : ‖𝓕 (ψ : ℝ → ℂ) (a / (2 * π))‖ ≤ W21.norm ψ * (1 + (a / (2 * π)) ^ 2)⁻¹ :=
    decay_bounds_key ψ _
  have twopi : 0 ≤ 2 * π := by simp [pi_nonneg]
  have l3 : Integrable (fun a ↦ (1 + (a / (2 * π)) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_div (by norm_num [pi_ne_zero])
  have l2 : IntegrableOn (fun i ↦ W21.norm ψ * (1 + (i / (2 * π)) ^ 2)⁻¹) (Ici (-Real.log x)) := by
    exact (l3.const_mul _).integrableOn
  have l1 : IntegrableOn (fun i ↦ ‖𝓕 (ψ : ℝ → ℂ) (i / (2 * π))‖) (Ici (-Real.log x)) := by
    refine ((l3.const_mul (W21.norm ψ)).mono' ?_ ?_).integrableOn
    · apply Continuous.aestronglyMeasurable ; fun_prop
    · simp only [norm_norm, key] ; simp
  have l5 : 0 ≤ᵐ[volume] fun a ↦ (1 + (a / (2 * π)) ^ 2)⁻¹ := by
    apply Eventually.of_forall ; intro x ; positivity
  refine (norm_integral_le_integral_norm _).trans <| (setIntegral_mono l1 l2 key).trans ?_
  rw [integral_const_mul] ; gcongr
  · apply W21.norm_nonneg
  refine (setIntegral_le_integral l3 l5).trans ?_
  rw [Measure.integral_comp_div (fun x => (1 + x ^ 2)⁻¹) (2 * π)]
  simp [abs_eq_self.mpr twopi] ; ring_nf ; rfl

lemma bound_main {C : ℝ} (A : ℂ) (x : ℝ) (hx : 1 ≤ x) (ψ : W21)
    (hcheby : chebyWith C f) :
    ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))‖ ≤
      W21.norm ψ * (C * (1 + 2 * π ^ 2) + ‖A‖ * (2 * π ^ 2)) := by

  have l1 := bound_I1' x hx ψ hcheby
  have l2 := mul_le_mul (le_refl ‖A‖) (bound_I2 x ψ) (by positivity) (by positivity)
  apply norm_sub_le _ _ |>.trans ; rw [norm_mul]
  convert _root_.add_le_add l1 l2 using 1 <;> first | rfl | ring


set_option backward.isDefEq.respectTransparency false in
lemma limiting_cor_W21 (ψ : W21) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun x : ℝ ↦ ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))) atTop (𝓝 0) := by

  -- Shorter notation for clarity
  let S1 x (ψ : ℝ → ℂ) := ∑' (n : ℕ), f n / ↑n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑n / x))
  let S2 x (ψ : ℝ → ℂ) := ↑A * ∫ (u : ℝ) in Ici (-Real.log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))
  let S x ψ := S1 x ψ - S2 x ψ ; change Tendsto (fun x ↦ S x ψ) atTop (𝓝 0)

  -- Build the truncation
  obtain g := exists_trunc
  let Ψ R := g.scale R * ψ
  have key R : Tendsto (fun x ↦ S x (Ψ R)) atTop (𝓝 0) := limiting_cor (Ψ R) hf hcheby hG hG'

  -- Choose the truncation radius
  obtain ⟨C, hcheby⟩ := hcheby
  have hC : 0 ≤ C := by
    have : ‖f 0‖ ≤ C := by simpa [cumsum] using hcheby 1
    have : 0 ≤ ‖f 0‖ := by positivity
    linarith
  have key2 : Tendsto (fun R ↦ W21.norm (ψ - Ψ R)) atTop (𝓝 0) := W21_approximation ψ g
  simp_rw [Metric.tendsto_nhds] at key key2 ⊢ ; intro ε hε
  let M := C * (1 + 2 * π ^ 2) + ‖(A : ℂ)‖ * (2 * π ^ 2)
  obtain ⟨R, hRψ⟩ := (key2 ((ε / 2) / (1 + M)) (by positivity)).exists
  simp only [dist_zero_right, Real.norm_eq_abs, abs_eq_self.mpr W21.norm_nonneg] at hRψ key

  -- Apply the compact support case
  filter_upwards [eventually_ge_atTop 1, key R (ε / 2) (by positivity)] with x hx key

  -- Control the tail term
  have key3 : ‖S x (ψ - Ψ R)‖ < ε / 2 := by
    have : ‖S x _‖ ≤ _ * M := @bound_main f C A x hx (ψ - Ψ R) hcheby
    apply this.trans_lt
    apply (mul_le_mul (d := 1 + M) le_rfl (by simp) (by positivity) W21.norm_nonneg).trans_lt
    have : 0 < 1 + M := by positivity
    convert! (mul_lt_mul_iff_left₀ this).mpr hRψ using 1 ; field_simp

  -- Conclude the proof
  have S1_sub_1 x : 𝓕 (⇑ψ - ⇑(Ψ R)) x = 𝓕 (ψ : ℝ → ℂ) x - 𝓕 ⇑(Ψ R) x := by
    have l1 : AEStronglyMeasurable (fun x_1 : ℝ ↦ cexp (-(2 * ↑π * (↑x_1 * ↑x) * I))) volume := by
      refine (Continuous.mul ?_ continuous_const).neg.cexp.aestronglyMeasurable
      apply continuous_const.mul <| contDiff_ofReal.continuous.mul continuous_const
    simp only [Real.fourier_eq', neg_mul, RCLike.inner_apply', conj_trivial, ofReal_neg,
      ofReal_mul, ofReal_ofNat, Pi.sub_apply, smul_eq_mul, mul_sub]
    apply integral_sub
    · apply ψ.hf.bdd_mul (c := 1) l1 ; simp [Complex.norm_exp]
    · apply (Ψ R : W21) |>.hf |>.bdd_mul (c := 1) l1
      simp [Complex.norm_exp]

  have S1_sub : S1 x (ψ - Ψ R) = S1 x ψ - S1 x (Ψ R) := by
    simp only [one_div, mul_inv_rev, S1_sub_1, mul_sub, S1] ; apply Summable.tsum_sub
    · have := summable_fourier x (by positivity) ψ ⟨_, hcheby⟩
      rw [summable_norm_iff] at this
      simpa using this
    · have := summable_fourier x (by positivity) (Ψ R) ⟨_, hcheby⟩
      rw [summable_norm_iff] at this
      simpa using! this

  have S2_sub : S2 x (ψ - Ψ R) = S2 x ψ - S2 x (Ψ R) := by
    simp only [S1_sub_1, S2] ; rw [integral_sub]
    · ring
    · exact ψ.integrable_fourier (by positivity) |>.restrict
    · exact (Ψ R : W21).integrable_fourier (by positivity) |>.restrict

  have S_sub : S x (ψ - Ψ R) = S x ψ - S x (Ψ R) := by simp [S, S1_sub, S2_sub] ; ring
  simpa [S_sub, Ψ] using norm_add_le _ _ |>.trans_lt (_root_.add_lt_add key3 key)

lemma limiting_cor_schwartz (ψ : 𝓢(ℝ, ℂ)) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun x : ℝ ↦ ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))) atTop (𝓝 0) :=
  limiting_cor_W21 ψ hf hcheby hG hG'





-- just the surjectivity is stated here, as this is all that is needed for the current
-- application, but perhaps one should state and prove bijectivity instead

lemma fourier_surjection_on_schwartz (f : 𝓢(ℝ, ℂ)) : ∃ g : 𝓢(ℝ, ℂ), 𝓕 g = f := by
  refine ⟨𝓕⁻ f, ?_⟩
  exact FourierTransform.fourier_fourierInv_eq f




lemma comp_exp_support0 {Ψ : ℝ → ℂ} (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    ∀ᶠ x in 𝓝 0, Ψ x = 0 :=
  notMem_tsupport_iff_eventuallyEq.mp (fun h => lt_irrefl 0 <| mem_Ioi.mp (hplus h))

lemma comp_exp_support1 {Ψ : ℝ → ℂ} (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    ∀ᶠ x in atBot, Ψ (exp x) = 0 :=
  Real.tendsto_exp_atBot <| comp_exp_support0 hplus

lemma comp_exp_support2 {Ψ : ℝ → ℂ} (hsupp : HasCompactSupport Ψ) :
    ∀ᶠ (x : ℝ) in atTop, (Ψ ∘ rexp) x = 0 := by
  simp only [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact,
    cocompact_eq_atBot_atTop] at hsupp
  exact Real.tendsto_exp_atTop hsupp.2

theorem comp_exp_support {Ψ : ℝ → ℂ} (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) : HasCompactSupport (Ψ ∘ rexp) := by
  simp only [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact,
    cocompact_eq_atBot_atTop]
  exact ⟨comp_exp_support1 hplus, comp_exp_support2 hsupp⟩

set_option backward.isDefEq.respectTransparency false in
lemma wiener_ikehara_smooth_aux (l0 : Continuous Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) (x : ℝ) (hx : 0 < x) :
    ∫ (u : ℝ) in Ioi (-Real.log x), ↑(rexp u) * Ψ (rexp u) = ∫ (y : ℝ) in Ioi (1 / x), Ψ y := by

  have l1 : ContinuousOn rexp (Ici (-Real.log x)) := by fun_prop
  have l2 : Tendsto rexp atTop atTop := Real.tendsto_exp_atTop
  have l3 t (_ : t ∈ Ioi (-log x)) : HasDerivWithinAt rexp (rexp t) (Ioi t) t :=
    (Real.hasDerivAt_exp t).hasDerivWithinAt
  have l4 : ContinuousOn Ψ (rexp '' Ioi (-Real.log x)) := by fun_prop
  have l5 : IntegrableOn Ψ (rexp '' Ici (-Real.log x)) volume :=
    (l0.integrable_of_hasCompactSupport hsupp).integrableOn
  have l6 : IntegrableOn (fun x ↦ rexp x • (Ψ ∘ rexp) x) (Ici (-Real.log x)) volume := by
    refine (Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_).integrableOn
    change HasCompactSupport (rexp • (Ψ ∘ rexp))
    exact (comp_exp_support hsupp hplus).smul_left
  have := MeasureTheory.integral_deriv_smul_comp_Ioi l1 l2 l3 l4 l5 l6
  simpa [Real.exp_neg, Real.exp_log hx] using this

theorem wiener_ikehara_smooth_sub (h1 : Integrable Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    Tendsto (fun x ↦ (↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y) - ↑A * ∫ (y : ℝ) in Ioi 0, Ψ y)
      atTop (𝓝 0) := by

  obtain ⟨ε, hε, hh⟩ := Metric.eventually_nhds_iff.mp <| comp_exp_support0 hplus
  apply tendsto_nhds_of_eventually_eq ; filter_upwards [eventually_gt_atTop ε⁻¹] with x hxε

  have l1 : Integrable (indicator (Ioi x⁻¹) (fun x : ℝ => Ψ x)) := h1.indicator measurableSet_Ioi
  have l2 : Integrable (indicator (Ioi 0) (fun x : ℝ => Ψ x)) := h1.indicator measurableSet_Ioi

  simp_rw [← MeasureTheory.integral_indicator measurableSet_Ioi, ← mul_sub, ← integral_sub l1 l2]
  simp only [mul_eq_zero, ofReal_eq_zero]
  right
  apply MeasureTheory.integral_eq_zero_of_ae
  apply Eventually.of_forall
  intro t
  simp only [Pi.zero_apply]

  have hε' : 0 < ε⁻¹ := by positivity
  have hx : 0 < x := by linarith
  have hx' : 0 < x⁻¹ := by positivity
  have hεx : x⁻¹ < ε := (inv_lt_comm₀ hε hx).mp hxε

  have l3 : Ioi 0 = Ioc 0 x⁻¹ ∪ Ioi x⁻¹ := by
    ext t ; simp only [mem_Ioi, mem_union, mem_Ioc] ; constructor <;> intro h
    · simp [h, le_or_gt]
    · cases h with
      | inl h => exact h.1
      | inr h => exact hx'.trans h
  have l4 : Disjoint (Ioc 0 x⁻¹) (Ioi x⁻¹) := by simp
  have l5 := Set.indicator_union_of_disjoint l4 Ψ
  rw [l3, l5]
  simp only
  rw [add_comm, sub_add_cancel_left]
  by_cases ht : t ∈ Ioc 0 x⁻¹
  · simp only [ht, indicator_of_mem, neg_eq_zero]
    apply hh ; simp only [mem_Ioc, dist_zero_right, norm_eq_abs] at ht ⊢
    apply hεx.trans_le'
    rw [abs_le] ; constructor <;> linarith
  simp [ht]



lemma wiener_ikehara_smooth (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x - A * ∫ y in Set.Ioi 0, Ψ y)
      atTop (𝓝 0) := by

  let h (x : ℝ) : ℂ := rexp (2 * π * x) * Ψ (exp (2 * π * x))
  have h1 : ContDiff ℝ ∞ h := by
    have : ContDiff ℝ ∞ (fun x : ℝ => (rexp (2 * π * x))) := (contDiff_const.mul contDiff_id).exp
    exact (contDiff_ofReal.comp this).mul (hsmooth.comp this)
  have h2 : HasCompactSupport h := by
    have : 2 * π ≠ 0 := by simp [pi_ne_zero]
    simpa using! (comp_exp_support hsupp hplus).comp_smul this |>.mul_left
  obtain ⟨g, hg⟩ := fourier_surjection_on_schwartz (toSchwartz h h1 h2)

  have l1 {y} (hy : 0 < y) : y * Ψ y = 𝓕 g (1 / (2 * π) * Real.log y) := by
    simp only [one_div, mul_inv_rev, hg, toSchwartz, ofReal_exp, ofReal_mul, ofReal_ofNat,
      toSchwartz_apply, ofReal_inv, h]
    field_simp
    norm_cast
    rw [Real.exp_log hy]

  have key := limiting_cor_schwartz g hf hcheby hG hG'

  have l2 : ∀ᶠ x in atTop, ∑' (n : ℕ), f n / ↑n * 𝓕 g (1 / (2 * π) * Real.log (↑n / x)) =
      ∑' (n : ℕ), f n * Ψ (↑n / x) / x := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    congr ; ext n
    by_cases hn : n = 0
    · simp [hn, (comp_exp_support0 hplus).self_of_nhds]
    rw [← l1 (by positivity)]
    have : (n : ℂ) ≠ 0 := by simpa using hn
    have : (x : ℂ) ≠ 0 := by simpa using hx.ne.symm
    simp only [ofReal_div, ofReal_natCast]
    field_simp

  have l3 : ∀ᶠ x in atTop, ↑A * ∫ (u : ℝ) in Ici (-Real.log x), 𝓕 g (u / (2 * π)) =
      ↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    congr 1
    simp only [hg, toSchwartz, ofReal_exp, ofReal_mul, ofReal_ofNat, toSchwartz_apply,
      ofReal_div, h]
    norm_cast ; field_simp; norm_cast
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    exact wiener_ikehara_smooth_aux hsmooth.continuous hsupp hplus x hx

  have l4 : Tendsto (fun x => (↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y) - ↑A * ∫ (y : ℝ) in Ioi 0, Ψ y)
      atTop (𝓝 0) := by
    exact wiener_ikehara_smooth_sub (hsmooth.continuous.integrable_of_hasCompactSupport hsupp) hplus

  simpa [tsum_div_const] using (key.congr' <| EventuallyEq.sub l2 l3) |>.add l4



lemma wiener_ikehara_smooth' (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x) atTop (nhds (A * ∫ y in Set.Ioi 0, Ψ y)) :=
  tendsto_sub_nhds_zero_iff.mp <| wiener_ikehara_smooth hf hcheby hG hG' hsmooth hsupp hplus

lemma wiener_ikehara_smooth_real {f : ℕ → ℝ} {Ψ : ℝ → ℝ}
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x) atTop (nhds (A * ∫ y in Set.Ioi 0, Ψ y)) := by

  let Ψ' := ofReal ∘ Ψ
  have l1 : ContDiff ℝ ∞ Ψ' := contDiff_ofReal.comp hsmooth
  have l2 : HasCompactSupport Ψ' := hsupp.comp_left rfl
  have l3 : closure (Function.support Ψ') ⊆ Ioi 0 := by rwa [Function.support_comp_eq] ; simp
  have key := (continuous_re.tendsto _).comp
    (@wiener_ikehara_smooth' A Ψ G f hf hcheby hG hG' l1 l2 l3)
  simp at key ; norm_cast at key

lemma interval_approx_inf (ha : 0 < a) (hab : a < b) :
    ∀ᶠ ε in 𝓝[>] 0, ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      closure (Function.support ψ) ⊆ Set.Ioi 0 ∧
        ψ ≤ indicator (Ico a b) 1 ∧ b - a - ε ≤ ∫ y in Ioi 0, ψ y := by

  have l1 : Iio ((b - a) / 3) ∈ 𝓝[>] 0 := nhdsWithin_le_nhds <| Iio_mem_nhds <| by
    rw [← sub_pos] at hab
    positivity
  filter_upwards [self_mem_nhdsWithin, l1] with ε (hε : 0 < ε) (hε' : ε < (b - a) / 3)
  have l2 : a < a + ε / 2 := by simp [hε]
  have l3 : b - ε / 2 < b := by simp [hε]
  obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := smooth_urysohn_support_Ioo l2 l3
  refine ⟨ψ, h1, h2, ?_, ?_, ?_⟩
  · simp [h5, hab.ne, Icc_subset_Ioi_iff hab.le, ha]
  · exact h4.trans <| indicator_le_indicator_of_subset Ioo_subset_Ico_self (by simp)
  · have l4 : 0 ≤ b - a - ε := by linarith
    have l5 : Icc (a + ε / 2) (b - ε / 2) ⊆ Ioi 0 := by
      intro t ht
      simp only [mem_Icc, mem_Ioi] at ht ⊢
      exact ha.trans <| l2.trans_le <| ht.1
    have l6 : Icc (a + ε / 2) (b - ε / 2) ∩ Ioi 0 = Icc (a + ε / 2) (b - ε / 2) :=
      inter_eq_left.mpr l5
    have l7 : ∫ y in Ioi 0, indicator (Icc (a + ε / 2) (b - ε / 2)) 1 y = b - a - ε := by
      simp only [measurableSet_Icc, integral_indicator_one, measureReal_restrict_apply, l6,
        volume_real_Icc]
      convert max_eq_left l4 using 1 <;> first | (with_reducible_and_instances rfl) | (ring_nf)
    have l8 : IntegrableOn ψ (Ioi 0) volume :=
      (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    rw [← l7] ; apply setIntegral_mono ?_ l8 h3
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Icc]
    apply IntegrableOn.mono ?_ subset_rfl Measure.restrict_le_self
    apply integrableOn_const <;>
    simp

lemma interval_approx_sup (ha : 0 < a) (hab : a < b) :
    ∀ᶠ ε in 𝓝[>] 0, ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      closure (Function.support ψ) ⊆ Set.Ioi 0 ∧
        indicator (Ico a b) 1 ≤ ψ ∧ ∫ y in Ioi 0, ψ y ≤ b - a + ε := by

  have l1 : Iio (a / 2) ∈ 𝓝[>] 0 := nhdsWithin_le_nhds <| Iio_mem_nhds (by linarith)
  filter_upwards [self_mem_nhdsWithin, l1] with ε (hε : 0 < ε) (hε' : ε < a / 2)
  have l2 : a - ε / 2 < a := by linarith
  have l3 : b < b + ε / 2 := by linarith
  obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := smooth_urysohn_support_Ioo l2 l3
  refine ⟨ψ, h1, h2, ?_, ?_, ?_⟩
  · have l4 : a - ε / 2 < b + ε / 2 := by linarith
    have l5 : ε / 2 < a := by linarith
    simp [h5, l4.ne, Icc_subset_Ioi_iff l4.le, l5]
  · apply le_trans ?_ h3
    apply indicator_le_indicator_of_subset Ico_subset_Icc_self (by simp)
  · have l4 : 0 ≤ b - a + ε := by linarith
    have l5 : Ioo (a - ε / 2) (b + ε / 2) ⊆ Ioi 0 := by intro t ht ; simp at ht ⊢ ; linarith
    have l6 : Ioo (a - ε / 2) (b + ε / 2) ∩ Ioi 0 = Ioo (a - ε / 2) (b + ε / 2) := inter_eq_left.mpr l5
    have l7 : ∫ y in Ioi 0, indicator (Ioo (a - ε / 2) (b + ε / 2)) 1 y = b - a + ε := by
      simp only [measurableSet_Ioo, integral_indicator_one, measureReal_restrict_apply, l6,
        volume_real_Ioo]
      convert max_eq_left l4 using 1 <;> first | (with_reducible_and_instances rfl) | (ring_nf)
    have l8 : IntegrableOn ψ (Ioi 0) volume := (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    rw [← l7]
    refine setIntegral_mono l8 ?_ h4
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Ioo]
    apply IntegrableOn.mono ?_ subset_rfl Measure.restrict_le_self
    apply integrableOn_const <;>
    simp

lemma WI_summable {f : ℕ → ℝ} {g : ℝ → ℝ} (hg : HasCompactSupport g) (hx : 0 < x) :
    Summable (fun n => f n * g (n / x)) := by
  obtain ⟨M, hM⟩ := hg.bddAbove.mono subset_closure
  apply summable_of_hasFiniteSupport
  unfold Function.HasFiniteSupport
  simp only [Function.support_mul] ; apply Finite.inter_of_right ; rw [finite_iff_bddAbove]
  exact ⟨Nat.ceil (M * x), fun i hi => by simpa using Nat.ceil_mono ((div_le_iff₀ hx).mp (hM hi))⟩

lemma WI_sum_le {f : ℕ → ℝ} {g₁ g₂ : ℝ → ℝ} (hf : 0 ≤ f) (hg : g₁ ≤ g₂) (hx : 0 < x)
    (hg₁ : HasCompactSupport g₁) (hg₂ : HasCompactSupport g₂) :
    (∑' n, f n * g₁ (n / x)) / x ≤ (∑' n, f n * g₂ (n / x)) / x := by
  apply div_le_div_of_nonneg_right ?_ hx.le
  exact Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (hg _) (hf _))
    (WI_summable hg₁ hx) (WI_summable hg₂ hx)

lemma WI_sum_Iab_le {f : ℕ → ℝ} (hpos : 0 ≤ f) {C : ℝ} (hcheby : chebyWith C f) (hb : 0 < b) (hxb : 2 / b < x) :
    (∑' n, f n * indicator (Ico a b) 1 (n / x)) / x ≤ C * 2 * b := by
  have hb' : 0 < 2 / b := by positivity
  have hx : 0 < x := by linarith
  have hxb' : 2 < x * b := (div_lt_iff₀ hb).mp hxb
  have l1 (i : ℕ) (hi : i ∉ Finset.range ⌈b * x⌉₊) : f i * indicator (Ico a b) 1 (i / x) = 0 := by
    simp_all [le_div_iff₀ hx]
  have l2 (i : ℕ) (_ : i ∈ Finset.range ⌈b * x⌉₊) : f i * indicator (Ico a b) 1 (i / x) ≤ |f i| := by
    rw [abs_eq_self.mpr (hpos _)]
    convert_to _ ≤ f i * 1
    · ring
    apply mul_le_mul_of_nonneg_left ?_ (hpos _)
    by_cases hi : (i / x) ∈ (Ico a b) <;> simp [hi]
  rw [tsum_eq_sum l1, div_le_iff₀ hx, mul_assoc, mul_assoc]
  apply Finset.sum_le_sum l2 |>.trans
  have := hcheby ⌈b * x⌉₊ ; simp only [norm_real, norm_eq_abs] at this ; apply this.trans
  have : 0 ≤ C := by have := hcheby 1 ; simp only [cumsum, Finset.range_one, norm_real,
    Finset.sum_singleton, Nat.cast_one, mul_one] at this ; exact (abs_nonneg _).trans this
  refine mul_le_mul_of_nonneg_left ?_ this
  apply (Nat.ceil_lt_add_one (by positivity)).le.trans
  linarith

lemma WI_sum_Iab_le' {f : ℕ → ℝ} (hpos : 0 ≤ f) {C : ℝ} (hcheby : chebyWith C f) (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, (∑' n, f n * indicator (Ico a b) 1 (n / x)) / x ≤ C * 2 * b := by
  filter_upwards [eventually_gt_atTop (2 / b)] with x hx using WI_sum_Iab_le hpos hcheby hb hx

lemma le_of_eventually_nhdsWithin {a b : ℝ} (h : ∀ᶠ c in 𝓝[>] b, a ≤ c) : a ≤ b := by
  apply le_of_forall_gt ; intro d hd
  have key : ∀ᶠ c in 𝓝[>] b, c < d := by
    apply eventually_of_mem (U := Iio d) ?_ (fun x hx => hx)
    rw [mem_nhdsWithin]
    refine ⟨Iio d, isOpen_Iio, hd, inter_subset_left⟩
  obtain ⟨x, h1, h2⟩ := (h.and key).exists
  linarith

lemma ge_of_eventually_nhdsWithin {a b : ℝ} (h : ∀ᶠ c in 𝓝[<] b, c ≤ a) : b ≤ a := by
  apply le_of_forall_lt ; intro d hd
  have key : ∀ᶠ c in 𝓝[<] b, c > d := by
    apply eventually_of_mem (U := Ioi d) ?_ (fun x hx => hx)
    rw [mem_nhdsWithin]
    refine ⟨Ioi d, isOpen_Ioi, hd, inter_subset_left⟩
  obtain ⟨x, h1, h2⟩ := (h.and key).exists
  linarith

lemma WI_tendsto_aux (a b : ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun c => c / A - (b - a)) (𝓝[>] (A * (b - a))) (𝓝[>] 0) := by
  rw [Metric.tendsto_nhdsWithin_nhdsWithin]
  intro ε hε
  refine ⟨A * ε, by positivity, ?_⟩
  intro x hx1 hx2
  constructor
  · simpa [lt_div_iff₀' hA]
  · simp only [Real.dist_eq, dist_zero_right, Real.norm_eq_abs] at hx2 ⊢
    have : |x / A - (b - a)| = |x - A * (b - a)| / A := by
      rw [← abs_eq_self.mpr hA.le, ← abs_div, abs_eq_self.mpr hA.le] ; congr ; field_simp
    rwa [this, div_lt_iff₀' hA]

lemma WI_tendsto_aux' (a b : ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun c => (b - a) - c / A) (𝓝[<] (A * (b - a))) (𝓝[>] 0) := by
  rw [Metric.tendsto_nhdsWithin_nhdsWithin]
  intro ε hε
  refine ⟨A * ε, by positivity, ?_⟩
  intro x hx1 hx2
  constructor
  · simpa [div_lt_iff₀' hA]
  · simp only [Real.dist_eq, dist_zero_right, norm_eq_abs] at hx2 ⊢
    have : |(b - a) - x / A| = |A * (b - a) - x| / A := by
      rw [← abs_eq_self.mpr hA.le, ← abs_div, abs_eq_self.mpr hA.le] ; congr ; field_simp
    rwa [this, div_lt_iff₀' hA, ← neg_sub, abs_neg]

theorem residue_nonneg {f : ℕ → ℝ} (hpos : 0 ≤ f)
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm (fun n ↦ ↑(f n)) σ')) (hcheby : cheby fun n ↦ ↑(f n))
    (hG : ContinuousOn G {s | 1 ≤ s.re}) (hG' : EqOn G (fun s ↦ LSeries (fun n ↦ ↑(f n)) s - ↑A / (s - 1)) {s | 1 < s.re}) : 0 ≤ A := by
  let S (g : ℝ → ℝ) (x : ℝ) := (∑' n, f n * g (n / x)) / x
  have hSnonneg {g : ℝ → ℝ} (hg : 0 ≤ g) : ∀ᶠ x : ℝ in atTop, 0 ≤ S g x := by
    filter_upwards [eventually_ge_atTop 0] with x hx
    exact div_nonneg (tsum_nonneg (fun i => mul_nonneg (hpos _) (hg _))) hx
  obtain ⟨ε, ψ, h1, h2, h3, h4, -⟩ := (interval_approx_sup zero_lt_one one_lt_two).exists
  have key := @wiener_ikehara_smooth_real A G f ψ hf hcheby hG hG' h1 h2 h3
  have l2 : 0 ≤ ψ := by apply le_trans _ h4 ; apply indicator_nonneg ; simp
  have l1 : ∀ᶠ x in atTop, 0 ≤ S ψ x := hSnonneg l2
  have l3 : 0 ≤ A * ∫ (y : ℝ) in Ioi 0, ψ y := ge_of_tendsto key l1
  have l4 : 0 < ∫ (y : ℝ) in Ioi 0, ψ y := by
    have r1 : 0 ≤ᵐ[Measure.restrict volume (Ioi 0)] ψ := Eventually.of_forall l2
    have r2 : IntegrableOn (fun y ↦ ψ y) (Ioi 0) volume :=
      (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    have r3 : Ico 1 2 ⊆ Function.support ψ := by intro x hx ; have := h4 x ; simp [hx] at this ⊢ ; linarith
    have r4 : Ico 1 2 ⊆ Function.support ψ ∩ Ioi 0 := by
      simp only [subset_inter_iff, r3, true_and] ; apply Ico_subset_Icc_self.trans ; rw [Icc_subset_Ioi_iff] <;> linarith
    have r5 : 1 ≤ volume ((Function.support fun y ↦ ψ y) ∩ Ioi 0) := by convert! volume.mono r4 ; norm_num
    simpa [setIntegral_pos_iff_support_of_nonneg_ae r1 r2] using! zero_lt_one.trans_le r5
  have := div_nonneg l3 l4.le ; field_simp at this ; exact this


lemma WienerIkeharaInterval {f : ℕ → ℝ} (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * (indicator (Ico a b) 1 (n / x))) / x) atTop (nhds (A * (b - a))) := by

  -- Take care of the trivial case `a = b`
  by_cases hab : a = b
  · simp [hab]
  replace hb : a < b := lt_of_le_of_ne hb hab ; clear hab

  -- Notation to make the proof more readable
  let S (g : ℝ → ℝ) (x : ℝ) :=  (∑' n, f n * g (n / x)) / x
  have hSnonneg {g : ℝ → ℝ} (hg : 0 ≤ g) : ∀ᶠ x : ℝ in atTop, 0 ≤ S g x := by
    filter_upwards [eventually_ge_atTop 0] with x hx
    refine div_nonneg ?_ hx
    refine tsum_nonneg (fun i => mul_nonneg (hpos _) (hg _))
  have hA : 0 ≤ A := residue_nonneg hpos hf hcheby hG hG'

  -- A few facts about the indicator function of `Icc a b`
  let Iab : ℝ → ℝ := indicator (Ico a b) 1
  change Tendsto (S Iab) atTop (𝓝 (A * (b - a)))
  have hIab : HasCompactSupport Iab := by simpa [Iab, HasCompactSupport, tsupport, hb.ne] using isCompact_Icc
  have Iab_nonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ S Iab x := hSnonneg (indicator_nonneg (by simp))
  have Iab2 : IsBoundedUnder (· ≤ ·) atTop (S Iab) := by
    obtain ⟨C, hC⟩ := hcheby ; exact ⟨C * 2 * b, WI_sum_Iab_le' hpos hC (by linarith)⟩
  have Iab3 : IsBoundedUnder (· ≥ ·) atTop (S Iab) := ⟨0, Iab_nonneg⟩
  have Iab0 : IsCoboundedUnder (· ≥ ·) atTop (S Iab) := Iab2.isCoboundedUnder_ge
  have Iab1 : IsCoboundedUnder (· ≤ ·) atTop (S Iab) := Iab3.isCoboundedUnder_le

  -- Bound from above by a smooth function
  have sup_le : limsup (S Iab) atTop ≤ A * (b - a) := by
    have l_sup : ∀ᶠ ε in 𝓝[>] 0, limsup (S Iab) atTop ≤ A * (b - a + ε) := by
      filter_upwards [interval_approx_sup ha hb] with ε ⟨ψ, h1, h2, h3, h4, h6⟩
      have l1 : Tendsto (S ψ) atTop _ := wiener_ikehara_smooth_real hf hcheby hG hG' h1 h2 h3
      have l6 : S Iab ≤ᶠ[atTop] S ψ := by
        filter_upwards [eventually_gt_atTop 0] with x hx using WI_sum_le hpos h4 hx hIab h2
      have l5 : IsBoundedUnder (· ≤ ·) atTop (S ψ) := l1.isBoundedUnder_le
      have l3 : limsup (S Iab) atTop ≤ limsup (S ψ) atTop := limsup_le_limsup l6 Iab1 l5
      apply l3.trans ; rw [l1.limsup_eq] ; gcongr
    obtain rfl | h := eq_or_ne A 0
    · simpa using l_sup
    apply le_of_eventually_nhdsWithin
    have key : 0 < A := lt_of_le_of_ne hA h.symm
    filter_upwards [WI_tendsto_aux a b key l_sup] with x hx
    simpa [mul_div_cancel₀ _ h] using hx

  -- Bound from below by a smooth function
  have le_inf : A * (b - a) ≤ liminf (S Iab) atTop := by
    have l_inf : ∀ᶠ ε in 𝓝[>] 0, A * (b - a - ε) ≤ liminf (S Iab) atTop := by
      filter_upwards [interval_approx_inf ha hb] with ε ⟨ψ, h1, h2, h3, h5, h6⟩
      have l1 : Tendsto (S ψ) atTop _ := wiener_ikehara_smooth_real hf hcheby hG hG' h1 h2 h3
      have l2 : S ψ ≤ᶠ[atTop] S Iab := by
        filter_upwards [eventually_gt_atTop 0] with x hx using WI_sum_le hpos h5 hx h2 hIab
      have l4 : IsBoundedUnder (· ≥ ·) atTop (S ψ) := l1.isBoundedUnder_ge
      have l3 : liminf (S ψ) atTop ≤ liminf (S Iab) atTop := liminf_le_liminf l2 l4 Iab0
      apply le_trans ?_ l3 ; rw [l1.liminf_eq] ; gcongr
    obtain rfl | h := eq_or_ne A 0
    · simpa using l_inf
    apply ge_of_eventually_nhdsWithin
    have key : 0 < A := lt_of_le_of_ne hA h.symm
    filter_upwards [WI_tendsto_aux' a b key l_inf] with x hx
    simpa [mul_div_cancel₀ _ h] using hx

  -- Combine the two bounds
  have : liminf (S Iab) atTop ≤ limsup (S Iab) atTop := liminf_le_limsup Iab2 Iab3
  refine tendsto_of_liminf_eq_limsup ?_ ?_ Iab2 Iab3 <;> linarith



lemma lt_ceil_mul_iff (hx : 0 < x) : n < ⌈b * x⌉₊ ↔ n / x < b := by
  rw [div_lt_iff₀ hx, Nat.lt_ceil]

lemma ceil_mul_le_iff (hx : 0 < x) : ⌈a * x⌉₊ ≤ n ↔ a ≤ n / x := by
  rw [le_div_iff₀ hx, Nat.ceil_le]

lemma mem_Ico_iff_div (hx : 0 < x) : n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊ ↔ n / x ∈ Ico a b := by
  rw [Finset.mem_Ico, mem_Ico, ceil_mul_le_iff hx, lt_ceil_mul_iff hx]

lemma tsum_indicator {f : ℕ → ℝ} (hx : 0 < x) :
    ∑' n, f n * (indicator (Ico a b) 1 (n / x)) = ∑ n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n := by
  have l1 : ∀ n ∉ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n * indicator (Ico a b) 1 (↑n / x) = 0 := by
    simp [mem_Ico_iff_div hx] ; tauto
  rw [tsum_eq_sum l1] ; apply Finset.sum_congr rfl ; simp only [mem_Ico_iff_div hx] ; intro n hn ; simp [hn]

lemma WienerIkeharaInterval_discrete {f : ℕ → ℝ} (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun x : ℝ ↦ (∑ n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n) / x) atTop (nhds (A * (b - a))) := by
  apply (WienerIkeharaInterval hpos hf hcheby hG hG' ha hb).congr'
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [tsum_indicator hx]

lemma WienerIkeharaInterval_discrete' {f : ℕ → ℝ} (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.Ico ⌈a * N⌉₊ ⌈b * N⌉₊, f n) / N) atTop (nhds (A * (b - a))) :=
  WienerIkeharaInterval_discrete hpos hf hcheby hG hG' ha hb |>.comp tendsto_natCast_atTop_atTop

-- TODO with `Ico`



/-- A version of the *Wiener-Ikehara Tauberian Theorem*: If `f` is a nonnegative arithmetic
function whose L-series has a simple pole at `s = 1` with residue `A` and otherwise extends
continuously to the closed half-plane `re s ≥ 1`, then `∑ n < N, f n` is asymptotic to `A*N`. -/

lemma tendsto_mul_ceil_div :
    Tendsto (fun (p : ℝ × ℕ) => ⌈p.1 * p.2⌉₊ / (p.2 : ℝ)) (𝓝[>] 0 ×ˢ atTop) (𝓝 0) := by
  rw [Metric.tendsto_nhds] ; intro δ hδ
  have l1 : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioo 0 (δ / 2) := inter_mem_nhdsWithin _ (Iio_mem_nhds (by positivity))
  have l2 : ∀ᶠ N : ℕ in atTop, 1 ≤ δ / 2 * N := by
    apply Tendsto.eventually_ge_atTop
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  filter_upwards [l1.prod_mk l2] with (ε, N) ⟨⟨hε, h1⟩, h2⟩ ; dsimp only at *
  have l3 : 0 < (N : ℝ) := by
    simp only [Nat.cast_pos, Nat.pos_iff_ne_zero] ; rintro rfl ; simp [zero_lt_one.not_ge] at h2
  have l5 : 0 ≤ ε * ↑N := by positivity
  have l6 : ε * N ≤ δ / 2 * N := mul_le_mul h1.le le_rfl (by positivity) (by positivity)
  simp only [dist_zero_right, norm_div, RCLike.norm_natCast, div_lt_iff₀ l3, gt_iff_lt]
  convert (Nat.ceil_lt_add_one l5).trans_le (add_le_add l6 h2) using 1 <;> first | rfl | ring

lemma S_sub_S {f : ℕ → 𝕜} {ε : ℝ} {N : ℕ} (hε : ε ≤ 1) : S f 0 N - S f ε N = cumsum f ⌈ε * N⌉₊ / N := by
  have hceilN : ⌈ε * N⌉₊ ≤ N := by
    simp only [Nat.ceil_le]
    exact mul_le_of_le_one_left N.cast_nonneg hε
  have r1 : Finset.range N = Finset.range ⌈ε * N⌉₊ ∪ Finset.Ico ⌈ε * N⌉₊ N := by
    ext n
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  have r2 : Disjoint (Finset.range ⌈ε * N⌉₊) (Finset.Ico ⌈ε * N⌉₊ N) := by
    rw [Finset.range_eq_Ico] ; apply Finset.Ico_disjoint_Ico_consecutive
  simp [S, r1, Finset.sum_union r2, cumsum, add_div]

lemma tendsto_S_S_zero {f : ℕ → ℝ} (hpos : 0 ≤ f) (hcheby : cheby f) :
    TendstoUniformlyOnFilter (S f) (S f 0) (𝓝[>] 0) atTop := by
  rw [Metric.tendstoUniformlyOnFilter_iff] ; intro δ hδ
  obtain ⟨C, hC⟩ := hcheby
  have l1 : ∀ᶠ (p : ℝ × ℕ) in 𝓝[>] 0 ×ˢ atTop, C * ⌈p.1 * p.2⌉₊ / p.2 < δ := by
    have r1 := tendsto_mul_ceil_div.const_mul C
    simp only [mul_div_assoc', mul_zero] at r1 ; exact r1 (Iio_mem_nhds hδ)
  have : Ioc 0 1 ∈ 𝓝[>] (0 : ℝ) := inter_mem_nhdsWithin _ (Iic_mem_nhds zero_lt_one)
  filter_upwards [l1, Eventually.prod_inl this _] with (ε, N) h1 h2
  have l2 : ‖cumsum f ⌈ε * ↑N⌉₊ / ↑N‖ ≤ C * ⌈ε * N⌉₊ / N := by
    have r1 := hC ⌈ε * N⌉₊
    have r2 : 0 ≤ cumsum f ⌈ε * N⌉₊ := by apply cumsum_nonneg hpos
    simp only [norm_real, norm_of_nonneg (hpos _), norm_div,
      norm_of_nonneg r2, Real.norm_natCast] at r1 ⊢
    apply div_le_div_of_nonneg_right r1 (by positivity)
  simpa [← S_sub_S h2.2] using! l2.trans_lt h1

theorem WienerIkeharaTheorem' {f : ℕ → ℝ} (hpos : 0 ≤ f)
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun N => cumsum f N / N) atTop (𝓝 A) := by

  convert_to Tendsto (S f 0) atTop (𝓝 A) ; · ext N ; simp [S, cumsum]
  apply (tendsto_S_S_zero hpos hcheby).tendsto_of_eventually_tendsto
  · have L0 : Ioc 0 1 ∈ 𝓝[>] (0 : ℝ) := inter_mem_nhdsWithin _ (Iic_mem_nhds zero_lt_one)
    apply eventually_of_mem L0
    · intro ε hε
      simpa using! WienerIkeharaInterval_discrete' hpos hf hcheby hG hG' hε.1 hε.2
  · have : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    simpa using (this.const_sub 1).const_mul A

theorem vonMangoldt_cheby : cheby Λ := by
  use Real.log 4 + 4
  intro N
  by_cases! h : N = 0
  · simp [h, cumsum]
  simp only [cumsum, norm_real, norm_eq_abs]
  rw [Nat.range_eq_Icc_zero_sub_one _ h, (by simp : N - 1 = ⌊(N : ℝ) - 1⌋₊)]
  simp_rw [abs_of_nonneg vonMangoldt_nonneg]
  rw [← Chebyshev.psi_eq_sum_Icc]
  grw [Chebyshev.psi_le_const_mul_self <| sub_nonneg_of_le <| Nat.one_le_cast_iff_ne_zero.mpr h]
  gcongr
  linarith


-- Proof extracted from the `EulerProducts` project so we can adapt it to the
-- version of the Wiener-Ikehara theorem proved above (with the `cheby`
-- hypothesis)
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryPrimePNTProofMangoldt
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The mod-three prime progression input, from the proved Wiener--Ikehara theorem
and Mathlib's unconditional residue-class von Mangoldt continuation. -/
noncomputable section
open scoped BigOperators
open ArithmeticFunction Filter Topology MeasureTheory LSeries
namespace CubicFirstMoment

/-- The required progression PNT at the von Mangoldt level. -/
theorem modThree_mangoldt_mean (a : ZMod 3) (ha : IsUnit a) :
    Tendsto (fun N : ℕ => cumsum (vonMangoldt.residueClass a) N / N)
      atTop (𝓝 (1/2 : ℝ)) := by
  let f := vonMangoldt.residueClass a
  have hpos : 0 ≤ f := vonMangoldt.residueClass_nonneg a
  have hf (σ : ℝ) (hσ : 1 < σ) : Summable (nterm (fun n => (f n : ℂ)) σ) := by
    have hs := LSeriesSummable_of_abscissaOfAbsConv_lt_re
      (f := fun n => (f n : ℂ)) (s := (σ : ℂ))
      ((vonMangoldt.abscissaOfAbsConv_residueClass_le_one a).trans_lt
        (by exact_mod_cast hσ))
    change Summable (fun n => nterm (fun n => (f n : ℂ)) σ n)
    simp_rw [nterm_eq_norm_term]
    exact hs.norm
  have hcheby : ∃ C : ℝ, ∀ N : ℕ,
      cumsum (fun n => ‖(f n : ℂ)‖) N ≤ C * N := by
    obtain ⟨C,hC⟩ := vonMangoldt_cheby
    refine ⟨C,fun N => (Finset.sum_le_sum ?_).trans (hC N)⟩
    intro n _
    simp only [f, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (vonMangoldt.residueClass_nonneg a n),
      abs_of_nonneg vonMangoldt_nonneg]
    exact vonMangoldt.residueClass_le a n
  have hG := vonMangoldt.continuousOn_LFunctionResidueClassAux a
  have hG' : Set.EqOn (vonMangoldt.LFunctionResidueClassAux a)
      (fun s => LSeries (fun n => (f n : ℂ)) s - ((1/2 : ℝ) : ℂ) / (s - 1)) {s | 1 < s.re} := by
    intro s hs
    simpa only [show Nat.totient 3 = 2 by decide, Nat.cast_ofNat, inv_eq_one_div,
      Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
      vonMangoldt.eqOn_LFunctionResidueClassAux ha hs
  exact WienerIkeharaTheorem' hpos hf hcheby hG hG'

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryPrimePNTProofTheta
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prime-power removal for the mod-three von Mangoldt mean. -/
noncomputable section
open scoped BigOperators
open ArithmeticFunction Filter Topology MeasureTheory
namespace CubicFirstMoment

theorem modThreePsi_limit (a : ZMod 3) (ha : IsUnit a) :
    Tendsto (fun X => modThreePsi a X / X) atTop (𝓝 (1/2 : ℝ)) := by
  have h := (modThree_mangoldt_mean a ha).comp
    ((tendsto_add_atTop_nat 1).comp (tendsto_nat_floor_atTop (α := ℝ)))
  have hratio : Tendsto (fun X : ℝ => (⌊X⌋₊ + 1 : ℝ) / X) atTop (𝓝 1) := by
    have hh := (tendsto_nat_floor_div_atTop (R := ℝ)).add tendsto_inv_atTop_zero
    simpa only [one_div, add_div, add_zero] using hh
  have hh := h.mul hratio
  norm_num at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  have hN : (⌊X⌋₊ + 1 : ℝ) ≠ 0 := by positivity
  rw [modThreePsi, cumsum, ← Nat.range_succ_eq_Icc_zero]
  field_simp

lemma rationalProgression_primePower_gap {a : ℕ} (ha : a < 3) (X : ℝ) :
    0 ≤ modThreePsi (a : ZMod 3) X - rationalProgressionTheta a X ∧
    modThreePsi (a : ZMod 3) X - rationalProgressionTheta a X ≤
      Chebyshev.psi X - Chebyshev.theta X := by
  let f := vonMangoldt.residueClass (a : ZMod 3)
  have hf (n : ℕ) : f n = if n % 3 = a then vonMangoldt n else 0 := by
    simp only [f, vonMangoldt.residueClass, Set.indicator_apply, Set.mem_ofPred_eq,
      ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha]
  have htheta : rationalProgressionTheta a X =
      ∑ n ∈ Finset.Icc 0 ⌊X⌋₊, if n.Prime then f n else 0 := by
    simp only [rationalProgressionTheta, rationalProgressionPrimes, Finset.sum_filter,
      Nat.primesLE_eq_filter_Icc_zero]
    apply Finset.sum_congr rfl
    intro n _
    rw [hf]
    by_cases hn : n.Prime <;> simp [hn,vonMangoldt_apply_prime]
  have heq : modThreePsi (a : ZMod 3) X - rationalProgressionTheta a X =
      ∑ n ∈ Finset.Icc 0 ⌊X⌋₊, if n.Prime then 0 else f n := by
    rw [htheta, modThreePsi, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hn : n.Prime <;> simp [hn,f]
  have hall : Chebyshev.psi X - Chebyshev.theta X =
      ∑ n ∈ Finset.Icc 0 ⌊X⌋₊, if n.Prime then 0 else vonMangoldt n := by
    rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc, Finset.sum_filter,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hn : n.Prime <;> simp [hn,vonMangoldt_apply_prime]
  rw [heq,hall]
  constructor
  · apply Finset.sum_nonneg
    intro n _
    split_ifs <;> [rfl; exact vonMangoldt.residueClass_nonneg _ _]
  · apply Finset.sum_le_sum
    intro n _
    split_ifs <;> [rfl; exact vonMangoldt.residueClass_le _ _]

lemma sqrt_log_div_tendsto_zero :
    Tendsto (fun X : ℝ => 2 * Real.sqrt X * Real.log X / X) atTop (𝓝 0) := by
  have h := ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)).tendsto_div_nhds_zero).const_mul 2
  norm_num at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  rw [← Real.sqrt_eq_rpow]
  have hs := ne_of_gt (Real.sqrt_pos.mpr hX)
  calc
    2 * (Real.log X / Real.sqrt X) =
        2 * Real.sqrt X * Real.log X / (Real.sqrt X ^ 2) := by field_simp
    _ = _ := by rw [Real.sq_sqrt hX.le]

theorem rationalProgressionTheta_limit {a : ℕ} (ha : a = 1 ∨ a = 2) :
    Tendsto (fun X => rationalProgressionTheta a X / X) atTop (𝓝 (1/2 : ℝ)) := by
  have hau : IsUnit (a : ZMod 3) := by
    rcases ha with rfl | rfl
    · exact isUnit_one
    · apply isUnit_iff_ne_zero.mpr
      decide
  have ha3 : a < 3 := by omega
  have hp := modThreePsi_limit (a : ZMod 3) hau
  have hl := hp.sub sqrt_log_div_tendsto_zero
  norm_num at hl
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hp
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    have hg := (rationalProgression_primePower_gap ha3 X).2
    have hh := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hX
    have hb : modThreePsi (a : ZMod 3) X - rationalProgressionTheta a X ≤
        2 * Real.sqrt X * Real.log X := hg.trans ((le_abs_self _).trans hh)
    have hd := div_le_div_of_nonneg_right hb (show 0 ≤ X by linarith)
    rw [sub_div] at hd
    linarith
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    apply div_le_div_of_nonneg_right _ (by linarith)
    exact sub_nonneg.mp (rationalProgression_primePower_gap ha3 X).1

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryPrimePNTProofAP
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The natural prime density of the split rational residue class.

The von Mangoldt input is derived from the Wiener--Ikehara theorem and Mathlib's residue-class continuation. -/
noncomputable section
open Filter Topology
namespace CubicFirstMoment

/-- The class `1 mod 3` has natural prime density one half. -/
theorem rationalProgressionCount_one_limit :
    Tendsto (fun X => rationalProgressionCount 1 X * Real.log X / X)
      atTop (𝓝 (1/2)) := by
  have heq (X : ℝ) : selectedRationalPrimes (fun p => p % 3 = 1) X =
      rationalProgressionPrimes 1 X := by
    ext p
    simp only [selectedRationalPrimes, rationalProgressionPrimes, Finset.mem_filter]
  have htheta : Tendsto (fun X => selectedRationalTheta (fun p => p % 3 = 1) X / X)
      atTop (𝓝 (1/2 : ℝ)) := by
    simpa only [selectedRationalTheta, heq, rationalProgressionTheta] using
      (rationalProgressionTheta_limit (a := 1) (Or.inl rfl))
  have h := selectedRationalCount_limit (fun p => p % 3 = 1)
    (by norm_num : (0 : ℝ) < 1/2)
    htheta
  simpa only [selectedRationalCount, heq, rationalProgressionCount] using h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryPrimePNTProofSplitting
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational splitting and the literal primary Eisenstein primes. -/
noncomputable section
open scoped BigOperators
open UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma normNat_natCast (n : ℕ) : normNat (n : Eisenstein) = n ^ 2 := by
  apply Nat.cast_injective (R := ℝ)
  simp only [normNat_cast, Nat.cast_pow]
  change Complex.normSq (n : ℂ) = _
  simp [Complex.normSq_apply, pow_two]

lemma primary_natCast_of_mod_one {p : ℕ} (hp : p % 3 = 1) :
    primary (p : Eisenstein) := by
  refine ⟨(p / 3 : ℕ), ?_⟩
  have h := Nat.mod_add_div p 3
  rw [hp] at h
  have h' : (1 : Eisenstein) + 3 * (p / 3 : ℕ) = p := by exact_mod_cast h
  linear_combination -h'

/-- Every primary prime lies over a rational prime, and its norm has degree at most two. -/
lemma primaryPrime_rational_below {z : Eisenstein} (hz : primaryPrime z) :
    ∃ p : ℕ, p.Prime ∧ z ∣ (p : Eisenstein) ∧
      (normNat z = p ∨ normNat z = p ^ 2) := by
  let : (modulus z).IsPrime := (Ideal.span_singleton_prime hz.2.ne_zero).mpr hz.2
  let : Finite (Residues z) := finite_residues hz.2.ne_zero
  let : Fintype (Residues z) := Fintype.ofFinite _
  let : Field (Residues z) := Fintype.fieldOfDomain _
  let p := ringChar (Residues z)
  have hp : Nat.Prime p := CharP.char_is_prime (Residues z) p
  have hd : z ∣ (p : Eisenstein) := by
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_natCast, CharP.cast_eq_zero]
  have hn : normNat z ∣ p ^ 2 := by
    obtain ⟨b, hb⟩ := hd
    rw [← normNat_natCast, hb, normNat_mul]
    exact dvd_mul_right _ _
  obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow hp).mp hn
  have hne : normNat z ≠ 1 := fun h => hz.2.not_isUnit
    ((isUnit_iff_normNat_eq_one z).mpr h)
  refine ⟨p, hp, hd, ?_⟩
  interval_cases k
  · simp at he; contradiction
  · exact Or.inl (by simpa using he)
  · exact Or.inr he

/-- If its norm is a rational prime, that prime is in the split class. -/
lemma primaryPrime_norm_prime_mod_one {z : Eisenstein} (hz : primaryPrime z)
    (hn : (normNat z).Prime) : normNat z % 3 = 1 := by
  have h := primaryPrime_norm_sub_one_dvd_three hz
  have hN : 1 ≤ normNat z := hn.one_lt.le
  omega

/-- In the split residue class the rational prime is reducible in the Eisenstein ring. -/
lemma not_prime_natCast_of_mod_one {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1) :
    ¬ Prime (p : Eisenstein) := by
  intro hprime
  let : Fact p.Prime := ⟨hp⟩
  have hp0 : (p : Eisenstein) ≠ 0 := hprime.ne_zero
  let : (modulus (p : Eisenstein)).IsPrime :=
    (Ideal.span_singleton_prime hp0).mpr hprime
  let : Finite (Residues (p : Eisenstein)) := finite_residues hp0
  let : Fintype (Residues (p : Eisenstein)) := Fintype.ofFinite _
  let : Field (Residues (p : Eisenstein)) := Fintype.fieldOfDomain _
  let q := Ideal.Quotient.mk (modulus (p : Eisenstein))
  have hpzero : (p : Residues (p : Eisenstein)) = 0 := by
    rw [← map_natCast q]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton.mpr (dvd_refl _))
  let : CharP (Residues (p : Eisenstein)) p :=
    (CharP.charP_iff_prime_eq_zero hp).mpr hpzero
  have homega : (q omegaE) ^ p = q omegaE := by
    rw [← map_pow]
    have hpow := (cube_pow_mod omegaE_cube p).symm
    simpa only [hmod, pow_one] using congrArg q hpow
  have hfix (x : Residues (p : Eisenstein)) : x ^ p = x := by
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨⟨a,b⟩, rfl⟩ := ofCoords_surjective z
    change (frobenius _ p) (q (ofCoords a b)) = q (ofCoords a b)
    simp only [ofCoords, map_add, map_mul, map_intCast]
    change (a : _) + b * (q omegaE) ^ p = _
    rw [homega]
  have hcard : Fintype.card (Residues (p : Eisenstein)) = p ^ 2 := by
    rw [← Nat.card_eq_fintype_card, residues_card hp0, normNat_natCast]
  have hdiv : Fintype.card (Residues (p : Eisenstein)) - 1 ∣ p - 1 := by
    apply (FiniteField.forall_pow_eq_one_iff (Residues (p : Eisenstein)) (p - 1)).mp
    intro u
    apply Units.ext
    have h := hfix (u : Residues (p : Eisenstein))
    have hh : (u : Residues (p : Eisenstein)) ^ (p - 1) * u = 1 * u := by
      calc
        _ = (u : Residues (p : Eisenstein)) ^ p := by
          rw [← pow_succ, Nat.sub_add_cancel hp.one_lt.le]
        _ = u := h
        _ = 1 * u := by simp
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
      mul_right_cancel₀ u.ne_zero hh
  rw [hcard] at hdiv
  have hle := Nat.le_of_dvd (Nat.sub_pos_of_lt hp.one_lt) hdiv
  have hpsq : 1 ≤ p ^ 2 := by nlinarith [hp.two_le]
  have hle' : p ^ 2 ≤ p := by omega
  nlinarith [hp.two_le]

/-- Each split rational prime is the norm of an actual primary prime. -/
theorem exists_primaryPrime_norm_of_mod_one {p : ℕ} (hp : p.Prime)
    (hmod : p % 3 = 1) : ∃ z : Eisenstein, primaryPrime z ∧ normNat z = p := by
  have hnu : ¬ IsUnit (p : Eisenstein) := by
    rw [isUnit_iff_normNat_eq_one, normNat_natCast]
    nlinarith [hp.two_le]
  have hnpr : ¬ Irreducible (p : Eisenstein) :=
    fun h => not_prime_natCast_of_mod_one hp hmod h.prime
  have hfac : ∃ a b : Eisenstein, (p : Eisenstein) = a * b ∧
      ¬ IsUnit a ∧ ¬ IsUnit b := by
    simpa only [irreducible_iff, hnu, not_false_eq_true, true_and,
      not_forall, not_or, exists_prop] using hnpr
  obtain ⟨a,b,hab,ha,hb⟩ := hfac
  have hNa : normNat a ≠ 1 := mt (isUnit_iff_normNat_eq_one a).mpr ha
  have hNb : normNat b ≠ 1 := mt (isUnit_iff_normNat_eq_one b).mpr hb
  have hnorm : normNat a * normNat b = p ^ 2 := by
    rw [← normNat_mul, ← hab, normNat_natCast]
  have hNa' : normNat a = p := (hp.mul_eq_prime_sq_iff hNa hNb).mp hnorm |>.1
  have hprim := primary_natCast_of_mod_one hmod
  have haunit := unit_residue_of_dvd_primary hprim
    (show a ∣ (p : Eisenstein) from ⟨b,hab⟩)
  refine ⟨primaryNormalize a, ⟨primaryNormalize_primary haunit,
    prime_primaryNormalize (prime_of_normNat_prime (hNa' ▸ hp))⟩, ?_⟩
  rw [normNat_primaryNormalize, hNa']

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryPrimePNTProofFibers
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact fibers above split rational primes, and the quadratic-norm remainder. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma normNat_intCast (a : ℤ) : normNat (a : Eisenstein) = a.natAbs ^ 2 := by
  apply Nat.cast_injective (R := ℝ)
  rw [normNat_cast]
  change Complex.normSq (a : ℂ) = _
  rw [Nat.cast_pow, ← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs, sq_abs]
  simp [Complex.normSq_apply, pow_two]

lemma primaryPrime_ne_conjugate_of_prime_norm {z : Eisenstein}
    (hn : (normNat z).Prime) : z ≠ conjugate z := by
  intro he
  obtain ⟨⟨a,b⟩, rfl⟩ := ofCoords_surjective z
  change (normNat (ofCoords a b)).Prime at hn
  change ofCoords a b = conjugate (ofCoords a b) at he
  have him := congrArg (fun w : Eisenstein => (w : ℂ).im) he
  simp only [ofCoords_coe, conjugate_coe, Complex.star_def, Complex.conj_im, Complex.add_im,
    Complex.intCast_im, Complex.mul_im, Complex.intCast_re, zero_mul,
    add_zero, zero_add, omega_im] at him
  have hb : b = 0 := by
    have hs : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    have : (b : ℝ) = 0 := by nlinarith
    exact_mod_cast this
  subst b
  have heq : ofCoords a 0 = (a : Eisenstein) := by simp [ofCoords]
  rw [heq, normNat_intCast] at hn
  exact Nat.Prime.not_prime_pow (by decide : 2 ≤ 2) hn

lemma pnt_primaryPrime_eq_or_conjugate_of_norm_eq {z w : Eisenstein}
    (hz : primaryPrime z) (hw : primaryPrime w) (hn : normNat w = normNat z) :
    w = z ∨ w = conjugate z := by
  have hd : w ∣ z * conjugate z := by
    rw [← normNat_cast_eq_mul_conjugate, ← hn, normNat_cast_eq_mul_conjugate]
    exact dvd_mul_right _ _
  rcases hw.2.dvd_or_dvd hd with h | h
  · exact Or.inl (primary_associated_eq hw.1 hz.1
      (hw.2.associated_of_dvd hz.2 h))
  · exact Or.inr (primary_associated_eq hw.1 (primary_conjugate hz.1)
      (hw.2.associated_of_dvd (primaryPrime_conjugate hz).2 h))

lemma primaryPrime_normFiber_card_le_two (X : ℝ) (n : ℕ) :
    ((primeCutoff X).filter (fun z => normNat z = n)).card ≤ 2 := by
  let S := (primeCutoff X).filter (fun z => normNat z = n)
  change S.card ≤ 2
  by_cases hs : S.Nonempty
  · obtain ⟨z,hz⟩ := hs
    have hzP := (mem_primeCutoff.mp (Finset.mem_filter.mp hz).1).1
    have hsub : S ⊆ {z, conjugate z} := by
      intro w hw
      have hwP := (mem_primeCutoff.mp (Finset.mem_filter.mp hw).1).1
      have hn := (Finset.mem_filter.mp hw).2.trans (Finset.mem_filter.mp hz).2.symm
      rcases pnt_primaryPrime_eq_or_conjugate_of_norm_eq hzP hwP hn with h | h
      · simp [h]
      · simp [h]
    apply (Finset.card_le_card hsub).trans
    by_cases h : z = conjugate z
    · rw [← h]
      simp
    · rw [Finset.card_pair h]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simp

/-- Exactly two primary primes lie above each split rational prime. -/
theorem primaryPrime_normFiber_card_eq_two {p : ℕ} (hp : p.Prime)
    (hmod : p % 3 = 1) {X : ℝ} (hpX : (p : ℝ) ≤ X) :
    ((primeCutoff X).filter (fun z => normNat z = p)).card = 2 := by
  obtain ⟨z,hz,hn⟩ := exists_primaryPrime_norm_of_mod_one hp hmod
  have hne := primaryPrime_ne_conjugate_of_prime_norm (hn ▸ hp)
  have he : (primeCutoff X).filter (fun w => normNat w = p) = {z,conjugate z} := by
    ext w
    simp only [Finset.mem_filter, mem_primeCutoff, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hw
      exact pnt_primaryPrime_eq_or_conjugate_of_norm_eq hz hw.1.1 (hw.2.trans hn.symm)
    · intro hw
      rcases hw with rfl | rfl
      · exact ⟨⟨hz, by rwa [← normNat_cast, hn]⟩, hn⟩
      · exact ⟨⟨primaryPrime_conjugate hz, by rwa [norm_conjugate, ← normNat_cast, hn]⟩,
          by simpa using hn⟩
  rw [he, Finset.card_pair hne]

/-- Every other norm is the square of a rational prime. -/
lemma primaryPrime_norm_square_of_not_prime {z : Eisenstein} (hz : primaryPrime z)
    (hn : ¬ (normNat z).Prime) :
    ∃ p : ℕ, p.Prime ∧ normNat z = p ^ 2 := by
  obtain ⟨p,hp,_hd,hshape⟩ := primaryPrime_rational_below hz
  exact ⟨p,hp,hshape.resolve_left (fun h => hn (h ▸ hp))⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryPrimePNTProofCounting
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite counting comparison with split rational primes. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- Prime-norm primary elements account for exactly twice the split rational count. -/
lemma primaryPrime_primeNorm_count (X : ℝ) (hX : 0 ≤ X) :
    ((primeCutoff X).filter (fun z => (normNat z).Prime)).card =
      2 * ((Nat.primesLE ⌊X⌋₊).filter (fun p => p % 3 = 1)).card := by
  let S := (primeCutoff X).filter (fun z => (normNat z).Prime)
  let T := (Nat.primesLE ⌊X⌋₊).filter (fun p => p % 3 = 1)
  have hmap : (S : Set Eisenstein).MapsTo normNat T := by
    intro z hz
    obtain ⟨hz,hzn⟩ := Finset.mem_filter.mp hz
    obtain ⟨hzP,hzX⟩ := mem_primeCutoff.mp hz
    apply Finset.mem_filter.mpr
    refine ⟨Nat.mem_primesLE.mpr ⟨?_, hzn⟩, primaryPrime_norm_prime_mod_one hzP hzn⟩
    apply (Nat.le_floor_iff hX).mpr
    rwa [normNat_cast]
  change S.card = 2 * T.card
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  calc
    (∑ p ∈ T, (S.filter (fun z => normNat z = p)).card) = ∑ _p ∈ T, 2 := by
      apply Finset.sum_congr rfl
      intro p hp
      obtain ⟨hpp,hpm⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpX,hpp⟩ := Nat.mem_primesLE.mp hpp
      have he : S.filter (fun z => normNat z = p) =
          (primeCutoff X).filter (fun z => normNat z = p) := by
        ext z
        simp only [S, Finset.mem_filter]
        constructor
        · exact fun h => ⟨h.1.1,h.2⟩
        · exact fun h => ⟨⟨h.1, h.2 ▸ hpp⟩,h.2⟩
      rw [he]
      exact primaryPrime_normFiber_card_eq_two hpp hpm
        ((Nat.le_floor_iff hX).mp hpX)
    _ = 2 * T.card := by simp [mul_comm]

/-- The remaining primary primes have square norm and contribute at most a square-root error. -/
lemma primaryPrime_squareNorm_count_le (X : ℝ) (hX : 0 ≤ X) :
    ((primeCutoff X).filter (fun z => ¬(normNat z).Prime)).card ≤
      2 * (Nat.sqrt ⌊X⌋₊ + 1) := by
  let S := (primeCutoff X).filter (fun z => ¬(normNat z).Prime)
  let T := Finset.range (Nat.sqrt ⌊X⌋₊ + 1)
  have hmap : (S : Set Eisenstein).MapsTo (fun z => Nat.sqrt (normNat z)) T := by
    intro z hz
    obtain ⟨hz,_⟩ := Finset.mem_filter.mp hz
    have hzX : normNat z ≤ ⌊X⌋₊ := (Nat.le_floor_iff hX).mpr
      (by rw [normNat_cast]; exact (mem_primeCutoff.mp hz).2)
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.sqrt_le_sqrt hzX))
  change S.card ≤ 2 * (Nat.sqrt ⌊X⌋₊ + 1)
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  calc
    (∑ p ∈ T, (S.filter (fun z => Nat.sqrt (normNat z) = p)).card) ≤ ∑ _p ∈ T, 2 := by
      apply Finset.sum_le_sum
      intro p _hp
      have hsub : S.filter (fun z => Nat.sqrt (normNat z) = p) ⊆
          (primeCutoff X).filter (fun z => normNat z = p ^ 2) := by
        intro z hz
        obtain ⟨hz,hzp⟩ := Finset.mem_filter.mp hz
        obtain ⟨hz,hzn⟩ := Finset.mem_filter.mp hz
        obtain ⟨q,_hq,hqN⟩ := primaryPrime_norm_square_of_not_prime
          (mem_primeCutoff.mp hz).1 hzn
        have hqp : q = p := by simpa only [hqN, Nat.sqrt_eq'] using hzp
        exact Finset.mem_filter.mpr ⟨hz, by rw [hqN,hqp]⟩
      exact (Finset.card_le_card hsub).trans (primaryPrime_normFiber_card_le_two X (p ^ 2))
    _ = 2 * (Nat.sqrt ⌊X⌋₊ + 1) := by simp [T,mul_comm]

/-- Literal count comparison; no prime ideal theorem is assumed. -/
theorem primaryPrimeCount_comparison (X : ℝ) (hX : 0 ≤ X) :
    let P := ((Nat.primesLE ⌊X⌋₊).filter (fun p => p % 3 = 1)).card
    2 * P ≤ (primeCutoff X).card ∧
      (primeCutoff X).card ≤ 2 * P + 2 * (Nat.sqrt ⌊X⌋₊ + 1) := by
  dsimp only
  have he := Finset.card_filter_add_card_filter_not (s := primeCutoff X)
    (p := fun z => (normNat z).Prime)
  have hmain := primaryPrime_primeNorm_count X hX
  have herr := primaryPrime_squareNorm_count_le X hX
  omega

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryPrimePNTProof
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The primary-prime PNT, from rational progressions and actual Eisenstein splitting. -/
noncomputable section
open Filter Topology Asymptotics
namespace CubicFirstMoment

private lemma sqrt_log_remainder_tendsto_zero :
    Tendsto (fun X : ℝ => 2 * (Real.sqrt X + 1) * Real.log X / X)
      atTop (𝓝 0) := by
  have h1 : Tendsto (fun X : ℝ => Real.log X / X) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using
      (isLittleO_log_rpow_atTop zero_lt_one).tendsto_div_nhds_zero
  have h := sqrt_log_div_tendsto_zero.add (h1.const_mul 2)
  norm_num only [add_zero, mul_zero] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext X
  ring

/-- The ordinary prime-ideal theorem in exactly the normalization used by the mains.
No prime-distribution or splitting hypothesis remains. -/
theorem primaryPrimePNT_proved_oai : PrimaryPrimePNT := by
  classical
  have hcount (X : ℝ) :
      ((Nat.primesLE ⌊X⌋₊).filter (fun p => p % 3 = 1)).card =
        (rationalProgressionPrimes 1 X).card := by
    apply congrArg Finset.card
    ext p
    simp only [rationalProgressionPrimes, Finset.mem_filter]
  have hm : Tendsto (fun X => 2 * rationalProgressionCount 1 X * Real.log X / X)
      atTop (𝓝 1) := by
    have h := rationalProgressionCount_one_limit.const_mul 2
    norm_num at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ext X
    ring
  have hu := hm.add sqrt_log_remainder_tendsto_zero
  norm_num at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hm hu
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    have hcmp := (primaryPrimeCount_comparison X (by linarith)).1
    rw [hcount] at hcmp
    have hc : 2 * rationalProgressionCount 1 X ≤ primaryPrimeCount X := by
      unfold rationalProgressionCount primaryPrimeCount
      exact_mod_cast hcmp
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (Real.log_nonneg hX)) (by linarith)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    have hcmp := (primaryPrimeCount_comparison X (by linarith)).2
    rw [hcount] at hcmp
    have hc : primaryPrimeCount X ≤ 2 * rationalProgressionCount 1 X +
        2 * (Nat.sqrt ⌊X⌋₊ + 1 : ℕ) := by
      unfold rationalProgressionCount primaryPrimeCount
      exact_mod_cast hcmp
    have hroot : (Nat.sqrt ⌊X⌋₊ : ℝ) ≤ Real.sqrt X := by
      have hs := Nat.sqrt_le' ⌊X⌋₊
      have hs' : (Nat.sqrt ⌊X⌋₊ : ℝ) ^ 2 ≤ X := by
        exact (by exact_mod_cast hs : (Nat.sqrt ⌊X⌋₊ : ℝ) ^ 2 ≤ ⌊X⌋₊).trans
          (Nat.floor_le (by linarith))
      nlinarith [Real.sqrt_nonneg X, Real.sq_sqrt (show 0 ≤ X by linarith),
        (show (0 : ℝ) ≤ (Nat.sqrt ⌊X⌋₊ : ℝ) by positivity)]
    have hc' : primaryPrimeCount X ≤
        2 * rationalProgressionCount 1 X + 2 * (Real.sqrt X + 1) := by
      push_cast at hc
      linarith
    have hb := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc' (Real.log_nonneg hX)) (show 0 ≤ X by linarith)
    simpa only [add_mul, add_div] using hb

end CubicFirstMoment

end

end OAI
end

theorem solution : type_of% @OAI.CubicFirstMoment.primaryPrimePNT_proved_oai := @OAI.CubicFirstMoment.primaryPrimePNT_proved_oai
