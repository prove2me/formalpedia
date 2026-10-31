-- Prove2me | solution 1 for OAI.CAT0Fillings.ChartGeometry.chord_scalar_average
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T03:05:31.669036+00:00
-- url     : https://prove2.me/submissions/b2413385-bb84-44a8-bb11-96a72e376c52

import Mathlib
import Definitions.Def_SharpCAT0Filling
import Definitions.Def_OAIQ29C0002
import Theorems.Thm_OAI_CAT0Fillings_ChartGeometry_chord_combined
import Theorems.Thm_OAI_CAT0Fillings_Conformal_chordBubble_bounded_derivatives

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Sobolev_CriticalNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.AnalyticMinimizer

lemma lpNorm_sq_eq_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} {p : ℝ} (hp : 0 < p) (hf : AEStronglyMeasurable f μ) :
    lpNorm f (ENNReal.ofReal p) μ ^ 2 = (∫ x, |f x|^p ∂μ)^(2/p) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by positivity) ENNReal.ofReal_ne_top hf]
  simp only [ENNReal.toReal_ofReal hp.le,Real.norm_eq_abs]
  rw [←Real.rpow_mul_natCast (integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _) ]
  congr 1
  simp only [Nat.cast_ofNat]
  ring

end CAT0Fillings.AnalyticMinimizer
end

section

open Set Filter MeasureTheory ENNReal
open scoped Topology ENNReal

namespace CAT0Fillings.AnalyticMinimizer
variable {α H : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup H] [NormedSpace ℝ H]

lemma criticalMass_nonneg (I : H →L[ℝ] Lp ℝ 2 μ) (p : ℝ) (u : H) :
    0 ≤ criticalMass I p u :=
  integral_nonneg fun point => Real.rpow_nonneg (abs_nonneg ((I u) point)) p

lemma criticalNorm_sq (I : H →L[ℝ] Lp ℝ 2 μ) {p : ℝ} (hp : 0 < p) (u : H) :
    criticalNorm I p u ^ 2 = criticalMass I p u ^ (2/p) :=
  lpNorm_sq_eq_integral hp (Lp.aestronglyMeasurable _)

lemma criticalMass_integrable (I : H →L[ℝ] Lp ℝ 2 μ) {p : ℝ} (hp : 0 < p) (u : H)
    (h : MemLp (I u) (ENNReal.ofReal p) μ) : Integrable (fun x => |(I u) x|^p) μ := by
  simpa only [toReal_ofReal hp.le,Real.norm_eq_abs] using h.integrable_norm_rpow (by positivity) ofReal_ne_top

end CAT0Fillings.AnalyticMinimizer
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Chord_AverageProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology

namespace CAT0Fillings.Conformal
lemma avg_pow_bound {τ : ℝ} (hτ : τ ∈ Icc (0:ℝ) 1) (n : ℕ) : |τ^n| ≤ 1 := by
  rw [abs_of_nonneg (pow_nonneg hτ.1 _)]
  exact pow_le_one₀ hτ.1 hτ.2
lemma avg_deriv_bound {d : ℝ → ℝ} {B τ t : ℝ} (hB : 0 ≤ B) (hτ : τ ∈ Icc (0:ℝ) 1)
    (hd : ∀ x, |d x| ≤ B ∧ |deriv d x| ≤ B) (n : ℕ) :
    |2*τ^n*d (τ*t)*deriv d (τ*t)| ≤ 2*B^2 := by
  rw [abs_mul,abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  calc
    _ ≤ 2*1*B*B := mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left (avg_pow_bound hτ _) (by norm_num)) (hd _).1 (abs_nonneg _) (by norm_num)) (hd _).2 (abs_nonneg _) (by positivity)
    _ = _ := by ring
lemma averageProfile_hasDerivAt {n : ℕ} (hn : 0 < n) {d : ℝ → ℝ} {B : ℝ}
    (hd : ContDiff ℝ 1 d) (hB : 0 ≤ B) (hdB : ∀ x, |d x| ≤ B ∧ |deriv d x| ≤ B) (t : ℝ) :
    HasDerivAt (averageProfile n d) (averageProfileDeriv n d t) t := by
  have hdc := hd.continuous_deriv_one
  have hmeas (x : ℝ) : AEStronglyMeasurable (fun τ : ℝ => τ^(n-1)*(d (τ*x))^2) (volume.restrict (Icc (0:ℝ) 1)) :=
    (by fun_prop : Continuous (fun τ : ℝ => τ^(n-1)*(d (τ*x))^2)).aestronglyMeasurable
  have hmeas' (x : ℝ) : AEStronglyMeasurable (fun τ : ℝ => 2*τ^n*d (τ*x)*deriv d (τ*x)) (volume.restrict (Icc (0:ℝ) 1)) :=
    (by fun_prop : Continuous (fun τ : ℝ => 2*τ^n*d (τ*x)*deriv d (τ*x))).aestronglyMeasurable
  have hi : Integrable (fun τ : ℝ => τ^(n-1)*(d (τ*t))^2) (volume.restrict (Icc (0:ℝ) 1)) :=
    (by fun_prop : Continuous (fun τ : ℝ => τ^(n-1)*(d (τ*t))^2)).integrableOn_Icc
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Icc (0:ℝ) 1))
    (F := fun x τ => τ^(n-1)*(d (τ*x))^2) (F' := fun x τ => 2*τ^n*d (τ*x)*deriv d (τ*x))
    (bound := fun _ => 2*B^2) (s := univ) (by simp) (Eventually.of_forall hmeas) hi (hmeas' t) ?_ (integrable_const _) ?_).2
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ x hx
    exact avg_deriv_bound hB hτ hdB n
  · filter_upwards [] with τ x hx
    have hg := ((hd.differentiable (by norm_num) (τ*x)).hasDerivAt.comp x ((hasDerivAt_id x).const_mul τ)).pow 2
    have hh := hg.const_mul (τ^(n-1))
    convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
    simp only [Function.comp_apply,Nat.cast_ofNat,mul_one]
    have hp : τ^(n-1)*τ = τ^n := by rw [←pow_succ,Nat.sub_add_cancel hn]
    calc
      _ = 2*(τ^(n-1)*τ)*d (τ*x)*deriv d (τ*x) := by rw [hp]
      _ = _ := by ring
lemma averageProfile_contDiff {n : ℕ} (hn : 0 < n) {d : ℝ → ℝ} {B : ℝ}
    (hd : ContDiff ℝ 1 d) (hB : 0 ≤ B) (hdB : ∀ x, |d x| ≤ B ∧ |deriv d x| ≤ B) :
    ContDiff ℝ 1 (averageProfile n d) := by
  have hdc := hd.continuous_deriv_one
  rw [contDiff_one_iff_deriv]
  constructor
  · exact fun t => (averageProfile_hasDerivAt hn hd hB hdB t).differentiableAt
  · have he : deriv (averageProfile n d) = averageProfileDeriv n d :=
      funext fun t => (averageProfile_hasDerivAt hn hd hB hdB t).deriv
    rw [he]
    apply continuous_of_dominated (bound := fun _ => 2*B^2)
    · intro t
      exact (by fun_prop : Continuous (fun τ : ℝ => 2*τ^n*d (τ*t)*deriv d (τ*t))).aestronglyMeasurable
    · intro t
      filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
      exact avg_deriv_bound hB hτ hdB n
    · exact integrable_const _
    · filter_upwards [] with τ
      fun_prop
lemma averageProfile_nonneg (n : ℕ) (d : ℝ → ℝ) (t : ℝ) : 0 ≤ averageProfile n d t := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
  exact mul_nonneg (pow_nonneg hτ.1 _) (sq_nonneg _)
end CAT0Fillings.Conformal
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Chord_Bubble
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory

namespace CAT0Fillings.Conformal
lemma chordBubble_contDiff {a : ℝ} (ha : 0 ≤ a) (q : ℝ) (m : ℕ∞) :
    ContDiff ℝ m (chordBubble q a) := by
  exact (by fun_prop : ContDiff ℝ m (fun t : ℝ => 1+a*t^2)).rpow_const_of_ne
    (fun t => ne_of_gt (by positivity))
lemma chordBubbleD_contDiff {a : ℝ} (ha : 0 ≤ a) (q : ℝ) (m : ℕ∞) :
    ContDiff ℝ m (chordBubbleD q a) := by
  have h := (by fun_prop : ContDiff ℝ m (fun t : ℝ => 1+a*t^2)).rpow_const_of_ne
    (p := -q-1) (fun t => ne_of_gt (by positivity))
  exact (by fun_prop : ContDiff ℝ m (fun t : ℝ => -2*q*a*t)).mul h
lemma chordBubble_hasDerivAt {a : ℝ} (ha : 0 ≤ a) (q t : ℝ) :
    HasDerivAt (chordBubble q a) (chordBubbleD q a t) t := by
  have hb := (((hasDerivAt_id t).pow 2).const_mul a).const_add 1
  simp only [Pi.pow_apply,id_eq] at hb
  have hh := hb.rpow_const (p := -q) (Or.inl (ne_of_gt (by positivity)))
  convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  simp only [chordBubbleD,Nat.cast_ofNat,mul_one]
  ring
lemma chordBubble_pos {a : ℝ} (ha : 0 ≤ a) (q t : ℝ) : 0 < chordBubble q a t :=
  Real.rpow_pos_of_pos (by positivity) _
lemma chordBubble_le_one {a q : ℝ} (ha : 0 ≤ a) (hq : 0 ≤ q) (t : ℝ) : chordBubble q a t ≤ 1 := by
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · nlinarith [mul_nonneg ha (sq_nonneg t)]
  · linarith
end CAT0Fillings.Conformal
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Chord_NonnegativeMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.ChordMeasure
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (ρ : α → ℝ)
lemma isProbability (hi : Integrable ρ μ) (hρ : 0 ≤ᵐ[μ] ρ) (hW : 0 < total μ ρ) :
    IsProbabilityMeasure (probability μ ρ) := by
  constructor
  rw [probability,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ←ofReal_integral_eq_lintegral_ofReal (hi.div_const _) (hρ.mono fun x hx => div_nonneg hx hW.le)]
  rw [integral_div]
  change ENNReal.ofReal (total μ ρ / total μ ρ) = 1
  rw [div_self hW.ne',ENNReal.ofReal_one]
lemma integral_probability (hi : AEStronglyMeasurable ρ μ) (hρ : 0 ≤ᵐ[μ] ρ)
    (hW : 0 < total μ ρ) (f : α → ℝ) :
    (∫ x, f x ∂probability μ ρ) = (∫ x, ρ x*f x ∂μ)/total μ ρ := by
  rw [probability,integral_withDensity_eq_integral_toReal_smul₀
    (hi.aemeasurable.div_const _).ennreal_ofReal (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [←integral_div]
  apply integral_congr_ae
  filter_upwards [hρ] with x hx
  rw [ENNReal.toReal_ofReal (div_nonneg hx hW.le),smul_eq_mul]
  ring
end CAT0Fillings.ChordMeasure
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Chord_Moments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace CAT0Fillings.Conformal
lemma beta_dimension {n β : ℝ} (hb : 0 < β) (hn : n*β = 1+2*β) : 2 < n := by
  exact (mul_lt_mul_iff_of_pos_right hb).mp (by linarith : 2*β < n*β)
lemma beta_half_dimension {n β : ℝ} (hb : 0 < β) (hn : n*β = 1+2*β) :
    1/(2*β) = (n-2)/2 := by
  apply (div_eq_div_iff (by positivity : (2*β:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0)).mpr
  nlinarith
lemma beta_inverse_half {β : ℝ} (hb : 0 < β) : 1/(2*(1/(2*β))) = β := by field_simp
lemma beta_critical_ratio {n β : ℝ} (hb : 0 < β) (hn : n*β = 1+2*β) :
    2/(2+4*β) = (n-2)/n := by
  have hn0 : 0 < n := lt_trans (by norm_num) (beta_dimension hb hn)
  apply (div_eq_div_iff (by positivity : (2+4*β:ℝ) ≠ 0) hn0.ne').mpr
  nlinarith
lemma beta_critical_product {n β : ℝ} (hb : 0 < β) (hn : n*β = 1+2*β) :
    -(1/(2*β))*(2+4*β) = -n := by
  rw [neg_mul,neg_inj]
  field_simp
  nlinarith
end CAT0Fillings.Conformal
end

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.ChordMeasure
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [Nonempty X]
  (μ : Measure X) [IsFiniteMeasure μ] {v : X → ℝ}
omit [CompactSpace X] [Nonempty X] [IsFiniteMeasure μ] in
lemma chord_measurable [CompactSpace X] [Nonempty X] [IsFiniteMeasure μ]
    (o : X) (hv : AEStronglyMeasurable v μ) (κ β : ℝ) :
    AEStronglyMeasurable (fun x => κ*dist o x*(v x)^β) μ := by
  exact (aestronglyMeasurable_const.mul (continuous_const.dist continuous_id).aestronglyMeasurable).mul
    (hv.aemeasurable.pow_const _).aestronglyMeasurable
end CAT0Fillings.ChordMeasure
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Chord_Fubini
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace CAT0Fillings

namespace ChordTransform

open MeasureTheory

lemma kernel_pos {n b a : ℝ} (hb : 0 ≤ b) (ha : 0 ≤ a) : 0 < kernel n b a :=
  Real.rpow_pos_of_pos (by positivity) _

lemma kernel_le_one {n b a : ℝ} (hn : 0 ≤ n) (hb : 0 ≤ b) (ha : 0 ≤ a) :
    kernel n b a ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith) (by linarith)

end ChordTransform

end CAT0Fillings

namespace CAT0Fillings.ChordAverage

lemma integrable_weight {q : ℝ} (hq : 0 < q) (a : ℝ) :
    IntervalIntegrable (fun u : ℝ => u^(q-1)) volume 0 a :=
  intervalIntegral.intervalIntegrable_rpow' (by linarith)

lemma weight_integral {q : ℝ} (hq : 0 < q) :
    ∫ u in (0 : ℝ)..1, u^(q-1) = 1/q := by
  rw [integral_rpow (Or.inl (by linarith))]
  simp only [sub_add_cancel, Real.one_rpow, Real.zero_rpow hq.ne', sub_zero]

end CAT0Fillings.ChordAverage

open Set Filter MeasureTheory
open scoped Topology

namespace CAT0Fillings.ChordIdentity

lemma rpow_shift_one {x r : ℝ} (hx : 0 < x) : x^(r+1) = x^r*x := by
  rw [Real.rpow_add hx, Real.rpow_one]

lemma rpow_shift_two {x r : ℝ} (hx : 0 < x) : x^(r+2) = x^r*x^2 := by
  rw [Real.rpow_add hx, Real.rpow_two]

lemma scalar_antiderivative {q b u : ℝ} (hb : 0 ≤ b) (hu : 0 < u) :
    HasDerivAt (fun u : ℝ => u^q*(1+b*u)^(-2*q))
      (q*(u^(q-1)*(1+b*u)^(-2*q-2) - b^2*u^(q+1)*(1+b*u)^(-2*q-2))) u := by
  have hp : 0 < 1+b*u := by positivity
  have h1 := (hasDerivAt_id u).rpow_const (p := q) (Or.inl hu.ne')
  have h2 := (((hasDerivAt_id u).const_mul b).const_add 1).rpow_const
    (p := -2*q) (Or.inl hp.ne')
  apply (h1.mul h2).congr_deriv
  dsimp only [id_eq]
  have hu1 : u^q = u^(q-1)*u := by
    convert rpow_shift_one (r := q-1) hu using 1 <;> first | (with_reducible_and_instances rfl) | (congr 1; ring)
  have hu2 : u^(q+1) = u^(q-1)*u^2 := by
    convert rpow_shift_two (r := q-1) hu using 1 <;> first | (with_reducible_and_instances rfl) | (congr 1; ring)
  have hp1 : (1+b*u)^(-2*q-1) = (1+b*u)^(-2*q-2)*(1+b*u) := by
    convert rpow_shift_one (r := -2*q-2) hp using 1 <;> first | (with_reducible_and_instances rfl) | (congr 1; ring)
  have hp2 : (1+b*u)^(-2*q) = (1+b*u)^(-2*q-2)*(1+b*u)^2 := by
    convert rpow_shift_two (r := -2*q-2) hp using 1 <;> first | (with_reducible_and_instances rfl) | (congr 1; ring)
  rw [hu1, hu2, hp1, hp2]
  ring

lemma integral_weighted_kernel {r b s : ℝ} (hr : -1 < r) (hb : 0 ≤ b) :
    IntervalIntegrable (fun u : ℝ => u^r*(1+b*u)^s) volume 0 1 := by
  apply (intervalIntegral.intervalIntegrable_rpow' hr).mul_continuousOn
  apply (continuousOn_const.add (continuousOn_const.mul continuousOn_id)).rpow_const
  intro u hu
  rw [uIcc_of_le zero_le_one] at hu
  have hu0 := hu.1
  exact Or.inl (ne_of_gt (by positivity : 0 < 1+b*u))

theorem scalar_identity {q b : ℝ} (hq : 0 < q) (hb : 0 ≤ b) :
    (1+b)^(-2*q) + q*b^2 * (∫ u in (0 : ℝ)..1, u^(q+1)*(1+b*u)^(-2*q-2)) =
      q * ∫ u in (0 : ℝ)..1, u^(q-1)*(1+b*u)^(-2*q-2) := by
  have hi1 := integral_weighted_kernel (r := q-1) (s := -2*q-2) (by linarith) hb
  have hi2 := integral_weighted_kernel (r := q+1) (s := -2*q-2) (by linarith) hb
  have hc : ContinuousOn (fun u : ℝ => u^q*(1+b*u)^(-2*q)) (Icc 0 1) := by
    apply ((continuousOn_id.rpow_const (fun _ _ => Or.inr hq.le))).mul
    apply (continuousOn_const.add (continuousOn_const.mul continuousOn_id)).rpow_const
    intro u hu
    have hu0 := hu.1
    exact Or.inl (ne_of_gt (by positivity : 0 < 1+b*u))
  have hi : IntervalIntegrable (fun u : ℝ =>
      q*(u^(q-1)*(1+b*u)^(-2*q-2) - b^2*u^(q+1)*(1+b*u)^(-2*q-2))) volume 0 1 := by
    simpa only [mul_assoc] using (hi1.sub (hi2.const_mul (b^2))).const_mul q
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (a := (0 : ℝ)) (b := 1) zero_le_one hc
    (fun u hu => scalar_antiderivative hb hu.1) hi
  simp only [mul_one, Real.one_rpow, one_mul, mul_zero, add_zero,
    Real.zero_rpow hq.ne', sub_zero] at H
  rw [intervalIntegral.integral_const_mul] at H
  simp only [mul_assoc] at H
  rw [intervalIntegral.integral_sub hi1 (hi2.const_mul (b^2)),
    intervalIntegral.integral_const_mul] at H
  nlinarith [H]

end CAT0Fillings.ChordIdentity

namespace CAT0Fillings.ChordTransform
open MeasureTheory Set

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]

lemma weighted_kernel_prod_integrable {b : α → ℝ}
    (hb : AEStronglyMeasurable b μ) (hb0 : ∀ᵐ x ∂μ, 0 ≤ b x)
    {q n a : ℝ} (hq : 0 < q) (hn : 0 ≤ n) (ha : 0 ≤ a) :
    Integrable (fun z : α × ℝ => z.2^(q-1)*kernel n (b z.1) (a*z.2))
      (μ.prod (volume.restrict (Ioc 0 1))) := by
  let ρ : Measure ℝ := volume.restrict (Ioc 0 1)
  have hw : Integrable (fun u : ℝ => u^(q-1)) ρ :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < q-1)).1
  have hm : AEStronglyMeasurable
      (fun z : α × ℝ => z.2^(q-1)*kernel n (b z.1) (a*z.2)) (μ.prod ρ) := by
    have hs : AEMeasurable (fun z : α × ℝ => z.2) (μ.prod ρ) := measurable_snd.aemeasurable
    exact ((hs.pow_const (q-1)).mul
      ((((hs.const_mul a).mul hb.aemeasurable.comp_fst).const_add 1).pow_const (-n))).aestronglyMeasurable
  have hi : Integrable (fun z : α × ℝ => z.2^(q-1)) (μ.prod ρ) := by
    simpa using (integrable_const (1 : ℝ) : Integrable (fun _ : α => (1 : ℝ)) μ).mul_prod hw
  apply hi.mono' hm
  have hc : ∀ᵐ z : α × ℝ ∂μ.prod ρ, 0 ≤ b z.1 :=
    Measure.quasiMeasurePreserving_fst.ae hb0
  have ht : ∀ᵐ z : α × ℝ ∂μ.prod ρ, z.2 ∈ Ioc (0 : ℝ) 1 :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioc)
  filter_upwards [hc, ht] with z hz ht
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (Real.rpow_nonneg ht.1.le _) (kernel_pos hz (mul_nonneg ha ht.1.le)).le)]
  exact mul_le_of_le_one_right (Real.rpow_nonneg ht.1.le _)
    (kernel_le_one hn hz (mul_nonneg ha ht.1.le))

theorem average_transform {b : α → ℝ}
    (hb : AEStronglyMeasurable b μ) (hb0 : ∀ᵐ x ∂μ, 0 ≤ b x)
    {q n a : ℝ} (hq : 0 < q) (hn : 0 ≤ n) (ha : 0 ≤ a) :
    ChordAverage.average q (transform μ n b) a =
      ∫ x, q * (∫ u in (0 : ℝ)..1, u^(q-1)*kernel n (b x) (a*u)) ∂μ := by
  have hi := weighted_kernel_prod_integrable μ hb hb0 hq hn ha
  rw [ChordAverage.average, integral_const_mul]
  congr 1
  simp only [intervalIntegral.integral_of_le zero_le_one]
  have heq := integral_integral_swap (f := fun x u => u^(q-1)*kernel n (b x) (a*u)) hi
  rw [heq]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [integral_const_mul]
  simp only [transform, mul_comm]

end CAT0Fillings.ChordTransform
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Chord_Identity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.AnalyticMinimizer
lemma quotient_bound_real {n W M E r : ℝ} (hn : 0 < n) (hW : 0 < W) (hM : 0 ≤ M)
    (h : n*W*M^r ≤ E*W^r) : (M/W)^r ≤ E/(n*W) := by
  rw [Real.div_rpow hM hW.le]
  apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hW _) (mul_pos hn hW)).mpr
  simpa only [mul_comm (M^r) (n*W)] using h
variable {α H : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup H] [NormedSpace ℝ H]
lemma critical_quotient_bound (I : H →L[ℝ] Lp ℝ 2 μ) (E : H → ℝ) {p n : ℝ}
    (hp : 0 < p) (hn : 0 < n) (v P : H) (hW : 0 < criticalMass I p v)
    (hE : E v = n*criticalMass I p v)
    (hmin : E v*(criticalNorm I p P)^2 ≤ E P*(criticalNorm I p v)^2) :
    (criticalMass I p P/criticalMass I p v)^(2/p) ≤ E P/(n*criticalMass I p v) := by
  rw [criticalNorm_sq I hp,criticalNorm_sq I hp,hE] at hmin
  exact quotient_bound_real hn hW (criticalMass_nonneg I p P) hmin
lemma critical_ratio_product (I : H →L[ℝ] Lp ℝ 2 μ) (p : ℝ) (v P : H)
    (hW : 0 < criticalMass I p v) (w : α → ℝ)
    (hw : 0 ≤ᵐ[μ] w) (hP : (I P : α → ℝ) =ᵐ[μ] fun x => I v x*w x) :
    criticalMass I p P/criticalMass I p v =
      ∫ x, (w x)^p ∂ChordMeasure.probability μ (fun x => |I v x|^p) := by
  rw [ChordMeasure.integral_probability μ _
    ((Lp.aestronglyMeasurable (I v)).aemeasurable.abs.pow_const p).aestronglyMeasurable
    (Eventually.of_forall fun x => Real.rpow_nonneg (abs_nonneg _) _) hW]
  congr 1
  apply integral_congr_ae
  filter_upwards [hw,hP] with x hx hPx
  rw [hPx,abs_mul,abs_of_nonneg hx,Real.mul_rpow (abs_nonneg _) hx]
lemma critical_scalar_start (I : H →L[ℝ] Lp ℝ 2 μ) (E : H → ℝ) {p n β : ℝ}
    (hp : 0 < p) (hn : 0 < n) (v P : H) (hW : 0 < criticalMass I p v)
    (hE : E v = n*criticalMass I p v)
    (hmin : E v*(criticalNorm I p P)^2 ≤ E P*(criticalNorm I p v)^2)
    (w F : α → ℝ) (hw : 0 ≤ᵐ[μ] w)
    (hP : (I P : α → ℝ) =ᵐ[μ] fun x => I v x*w x)
    (hEP : E P ≤ n*(∫ x, |I v x|^p*(w x)^2 ∂μ)+β*n*(∫ x, |I v x|^p*F x ∂μ)) :
    (∫ x, (w x)^p ∂ChordMeasure.probability μ (fun x => |I v x|^p))^(2/p) ≤
      (∫ x, (w x)^2 ∂ChordMeasure.probability μ (fun x => |I v x|^p))+
        β*(∫ x, F x ∂ChordMeasure.probability μ (fun x => |I v x|^p)) := by
  rw [←critical_ratio_product I p v P hW w hw hP]
  apply (critical_quotient_bound I E hp hn v P hW hE hmin).trans
  rw [ChordMeasure.integral_probability μ _ ((Lp.aestronglyMeasurable (I v)).aemeasurable.abs.pow_const p).aestronglyMeasurable
        (Eventually.of_forall fun x => Real.rpow_nonneg (abs_nonneg _) _) hW,
      ChordMeasure.integral_probability μ _ ((Lp.aestronglyMeasurable (I v)).aemeasurable.abs.pow_const p).aestronglyMeasurable
        (Eventually.of_forall fun x => Real.rpow_nonneg (abs_nonneg _) _) hW]
  change E P/(n*criticalMass I p v) ≤ _
  apply (div_le_iff₀ (mul_pos hn hW)).mpr
  convert hEP using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  have hW0 : (∫ x, |I v x|^p ∂μ) ≠ 0 := hW.ne'
  dsimp only [ChordMeasure.total,criticalMass]
  field_simp
end CAT0Fillings.AnalyticMinimizer
end

section
open Set Filter MeasureTheory
open scoped Topology

namespace CAT0Fillings.Conformal
lemma bubble_derivative_square {a : ℝ} (ha : 0 ≤ a) (q t : ℝ) :
    (chordBubbleD q a t)^2 = 4*q^2*a^2*t^2*(1+a*t^2)^(-2*q-2) := by
  have hb : 0 ≤ 1+a*t^2 := by positivity
  unfold chordBubbleD
  rw [mul_pow,←Real.rpow_mul_natCast hb,Nat.cast_ofNat]
  rw [show (-q-1)*2 = -2*q-2 by ring]
  ring
lemma profile_substitution {n : ℕ} (hn : 0 < n) {q a : ℝ} (hq : 0 < q)
    (ha : 0 ≤ a) (hnq : (n:ℝ) = 2*q+2) (t : ℝ) :
    averageProfile n (chordBubbleD q a) t =
      2*q^2*a^2*t^2*(∫ u in (0:ℝ)..1, u^(q+1)*(1+a*t^2*u)^(-2*q-2)) := by
  let g : ℝ → ℝ := fun u => u^(q+1)*(1+a*t^2*u)^(-2*q-2)
  have hg : ContinuousOn g (Icc 0 1) := by
    apply ContinuousOn.mul
    · exact continuousOn_id.rpow_const (fun u hu => Or.inr (by linarith))
    · have hb : Continuous (fun u : ℝ => 1+a*t^2*u) := by fun_prop
      exact hb.continuousOn.rpow_const (fun u hu => Or.inl (ne_of_gt (by
        have hu0 : 0 ≤ u := hu.1
        positivity)))
  have hsub := intervalIntegral.integral_comp_mul_deriv'
    (a := (0:ℝ)) (b := 1) (f := fun τ : ℝ => τ^2) (f' := fun τ => 2*τ) (g := g)
    (fun τ _ => by
      convert (hasDerivAt_id τ).pow 2 using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
      norm_num)
    (by fun_prop) (hg.mono (by
      rintro u ⟨τ,hτ,rfl⟩
      simp only [uIcc_of_le zero_le_one,mem_Icc] at hτ ⊢
      exact ⟨sq_nonneg _,pow_le_one₀ hτ.1 hτ.2⟩))
  norm_num only [zero_pow,one_pow] at hsub
  unfold averageProfile
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le zero_le_one,
    ←hsub,←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro τ hτ
  have hτ0 : 0 ≤ τ := (show τ ∈ Icc (0:ℝ) 1 by simpa only [uIcc_of_le zero_le_one] using hτ).1
  have hpow : (τ^2)^(q+1) = τ^n := by
    rw [←Real.rpow_natCast_mul hτ0,Nat.cast_ofNat,show 2*(q+1) = (n:ℝ) by linarith,Real.rpow_natCast]
  have hnat : τ^(n-1)*τ^2 = τ^n*τ := by
    rw [←pow_add,←pow_succ]
    congr 1
    omega
  dsimp only [Function.comp_apply,g]
  rw [bubble_derivative_square ha,hpow]
  have hbase : 1+a*(τ*t)^2 = 1+a*t^2*τ^2 := by ring
  rw [hbase]
  calc
    _ = 4*q^2*a^2*t^2*(τ^(n-1)*τ^2)*(1+a*t^2*τ^2)^(-2*q-2) := by ring
    _ = _ := by rw [hnat]; ring

lemma profile_scalar_identity {n : ℕ} (hn : 0 < n) {q a : ℝ} (hq : 0 < q)
    (ha : 0 ≤ a) (hnq : (n:ℝ) = 2*q+2) (t : ℝ) :
    (chordBubble q a t)^2 + (1/(2*q))*t^2*averageProfile n (chordBubbleD q a) t =
      q*(∫ u in (0:ℝ)..1, u^(q-1)*(1+a*t^2*u)^(-2*q-2)) := by
  rw [profile_substitution hn hq ha hnq t]
  have hw : (chordBubble q a t)^2 = (1+a*t^2)^(-2*q) := by
    unfold chordBubble
    rw [←Real.rpow_mul_natCast (show 0 ≤ 1+a*t^2 by positivity),Nat.cast_ofNat,show -q*2 = -2*q by ring]
  rw [hw]
  have h := ChordIdentity.scalar_identity hq (show 0 ≤ a*t^2 by positivity)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  field_simp
end CAT0Fillings.Conformal
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Chord_ProfileBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology

namespace CAT0Fillings.Conformal
lemma weighted_kernel_average_le_one {q b : ℝ} (hq : 0 < q) (hb : 0 ≤ b) :
    q*(∫ u in (0:ℝ)..1, u^(q-1)*(1+b*u)^(-2*q-2)) ≤ 1 := by
  calc
    _ ≤ q*(∫ u in (0:ℝ)..1, u^(q-1)) := by
      apply mul_le_mul_of_nonneg_left _ hq.le
      apply intervalIntegral.integral_mono_on zero_le_one
        (ChordIdentity.integral_weighted_kernel (by linarith) hb) (ChordAverage.integrable_weight hq 1)
      intro u hu
      apply mul_le_of_le_one_right (Real.rpow_nonneg hu.1 _)
      exact Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [mul_nonneg hb hu.1]) (by linarith)
    _ = 1 := by rw [ChordAverage.weight_integral hq]; field_simp
lemma profile_bound {n : ℕ} (hn : 0 < n) {q a : ℝ} (hq : 0 < q)
    (ha : 0 ≤ a) (hnq : (n:ℝ) = 2*q+2) (t : ℝ) :
    (chordBubble q a t)^2 + (1/(2*q))*t^2*averageProfile n (chordBubbleD q a) t ≤ 1 := by
  rw [profile_scalar_identity hn hq ha hnq t]
  exact weighted_kernel_average_le_one hq (by positivity)
lemma profile_term_bound {n : ℕ} (hn : 0 < n) {q a : ℝ} (hq : 0 < q)
    (ha : 0 ≤ a) (hnq : (n:ℝ) = 2*q+2) (t : ℝ) :
    |t^2*averageProfile n (chordBubbleD q a) t| ≤ 2*q := by
  have hf0 := averageProfile_nonneg n (chordBubbleD q a) t
  rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hf0)]
  have h := profile_bound hn hq ha hnq t
  have hle : (1/(2*q))*(t^2*averageProfile n (chordBubbleD q a) t) ≤ 1 := by
    nlinarith [sq_nonneg (chordBubble q a t)]
  have hh := mul_le_mul_of_nonneg_left hle (show 0 ≤ 2*q by positivity)
  field_simp at hh
  nlinarith
end CAT0Fillings.Conformal
end

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.Conformal
lemma bubbleProfile_continuous {n : ℕ} (hn : 0 < n) {q a : ℝ} (hq : 0 ≤ q) (ha : 0 < a) :
    Continuous (averageProfile n (chordBubbleD q a)) := by
  obtain ⟨B,hB,hbounds⟩ := chordBubble_bounded_derivatives ha hq
  apply (averageProfile_contDiff hn (chordBubbleD_contDiff ha.le q 1) hB ?_).continuous
  intro t
  refine ⟨?_,(hbounds t).2.2⟩
  simpa only [(chordBubble_hasDerivAt ha.le q t).deriv] using (hbounds t).2.1
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
lemma profile_integrable {s : α → ℝ} (hs : AEStronglyMeasurable s μ)
    {n : ℕ} (hn : 0 < n) {q a : ℝ} (hq : 0 < q) (ha : 0 < a)
    (hnq : (n:ℝ) = 2*q+2) :
    Integrable (fun x => (chordBubble q a (s x))^2) μ ∧
      Integrable (fun x => (s x)^2*averageProfile n (chordBubbleD q a) (s x)) μ := by
  have hw := (chordBubble_contDiff ha.le q 1).continuous.comp_aestronglyMeasurable hs
  have hm := (bubbleProfile_continuous hn hq.le ha).comp_aestronglyMeasurable hs
  constructor
  · apply (MemLp.of_bound (hw.pow 2) 1 ?_).integrable (by norm_num : (1:ℝ≥0∞) ≤ 1)
    filter_upwards [] with x
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_one₀ (chordBubble_pos ha.le q _).le (chordBubble_le_one ha.le hq.le _)
  · apply (MemLp.of_bound ((hs.pow 2).mul hm) (2*q) ?_).integrable (by norm_num : (1:ℝ≥0∞) ≤ 1)
    filter_upwards [] with x
    exact profile_term_bound hn hq ha.le hnq _
lemma profile_average {s : α → ℝ} (hs : AEStronglyMeasurable s μ)
    {n : ℕ} (hn : 0 < n) {q a : ℝ} (hq : 0 < q) (ha : 0 < a)
    (hnq : (n:ℝ) = 2*q+2) :
    (∫ x, (chordBubble q a (s x))^2 ∂μ)+
      (1/(2*q))*(∫ x, (s x)^2*averageProfile n (chordBubbleD q a) (s x) ∂μ) =
    ChordAverage.average q (ChordTransform.transform μ n (fun x => (s x)^2)) a := by
  obtain ⟨hw,hf⟩ := profile_integrable μ hs hn hq ha hnq
  rw [←integral_const_mul,←integral_add hw (hf.const_mul _),
    ChordTransform.average_transform μ (b := fun x => (s x)^2) (hs.pow 2) (Eventually.of_forall fun x => sq_nonneg (s x)) hq
      (Nat.cast_nonneg n) ha.le]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [←mul_assoc,profile_scalar_identity hn hq ha.le hnq (s x)]
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  dsimp only [ChordTransform.kernel]
  rw [hnq,show -(2*q+2) = -2*q-2 by ring]
  congr 2
  ring
end CAT0Fillings.Conformal
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Chord_Distribution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
open CAT0Fillings.Conformal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)
lemma chord_scalar_average_oai (hz : IsCycle T) (o : X) (v : q.Sobolev) {κ β a : ℝ}
    (hb : 0 < β) (ha : 0 < a) (hn : (k+1:ℝ)*β = 1+2*β)
    (hv : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion v x)
    (hm : ∀ b : ℝ, 0 < b → MemLp (q.inclusion v) (ENNReal.ofReal b) (MassMeasure.currentMassMeasure hT))
    (hpow : ∀ γ : ℝ, 1 ≤ γ → ∃ L : q.Sobolev,
      (q.closedGradient L : _ → _) =ᵐ[q.atlasMeasure]
        (fun z => (γ*(q.inclusion v (q.atlasParam z))^(γ-1)) • q.closedGradient v z))
    (heuler : ∀ ψ : q.Sobolev,
      4*β*inner ℝ (q.closedGradient v) (q.closedGradient ψ) +
        (k+1:ℝ)*inner ℝ (q.inclusion v) (q.inclusion ψ) =
      (k+1:ℝ)*(∫ x, ((q.inclusion v) x)^(1+4*β)*(q.inclusion ψ) x ∂MassMeasure.currentMassMeasure hT))
    (hr : ∀ (g : X → ℝ) (K : ℝ≥0), LipschitzWith K g →
      (∀ x, 0 ≤ g x) → (∀ x, g x ≤ 1) → q.radialVariation o g ≤ (k+1:ℝ)*q.sweptMass o g)
    (hW : 0 < AnalyticMinimizer.criticalMass q.inclusion (2+4*β) v)
    (hE : AnalyticMinimizer.energy q.inclusion q.closedGradient (4*β) (k+1:ℝ) v =
      (k+1:ℝ)*AnalyticMinimizer.criticalMass q.inclusion (2+4*β) v)
    (hmin : ∀ P : q.Sobolev,
      AnalyticMinimizer.energy q.inclusion q.closedGradient (4*β) (k+1:ℝ) v *
        (AnalyticMinimizer.criticalNorm q.inclusion (2+4*β) P)^2 ≤
      AnalyticMinimizer.energy q.inclusion q.closedGradient (4*β) (k+1:ℝ) P *
        (AnalyticMinimizer.criticalNorm q.inclusion (2+4*β) v)^2) :
    let μ := MassMeasure.currentMassMeasure hT
    let ν := ChordMeasure.probability μ (fun x => |q.inclusion v x|^(2+4*β))
    let b := fun x => (κ*dist o x*(q.inclusion v x)^β)^2
    (ChordTransform.transform ν (k+1) b a)^(((k+1:ℝ)-2)/(k+1:ℝ)) ≤
      ChordAverage.average (((k+1:ℝ)-2)/2) (ChordTransform.transform ν (k+1) b) a := by
  let μ := MassMeasure.currentMassMeasure hT
  let ν := ChordMeasure.probability μ (fun x => |q.inclusion v x|^(2+4*β))
  let s : X → ℝ := fun x => κ*dist o x*(q.inclusion v x)^β
  let c := 1/(2*β)
  let w := chordBubble c a
  let f := averageProfile (k+1) (chordBubbleD c a)
  have hc : 0 < c := by dsimp [c]; positivity
  have hnc : (k+1:ℝ) = 2*c+2 := by
    dsimp [c]
    rw [beta_half_dimension hb hn]
    ring
  have hp : 0 < 2+4*β := by positivity
  have hin := AnalyticMinimizer.criticalMass_integrable q.inclusion hp v (hm _ hp)
  let : IsProbabilityMeasure ν := ChordMeasure.isProbability μ _ hin
    (Eventually.of_forall fun point => Real.rpow_nonneg (abs_nonneg (q.inclusion v point)) _) hW
  have hsm : AEStronglyMeasurable s μ := ChordMeasure.chord_measurable μ o
    (Lp.aestronglyMeasurable (q.inclusion v)) κ β
  have hsν : AEStronglyMeasurable s ν := hsm.mono_ac (withDensity_absolutelyContinuous _ _)
  obtain ⟨P,hP,hEP⟩ := q.chord_combined hz o v (κ := κ) hb ha hn hv hm hpow heuler hr
  have hEP' : AnalyticMinimizer.energy q.inclusion q.closedGradient (4*β) (k+1:ℝ) P ≤
      (k+1:ℝ)*(∫ x, |q.inclusion v x|^(2+4*β)*(w (s x))^2 ∂μ)+
      β*(k+1:ℝ)*(∫ x, |q.inclusion v x|^(2+4*β)*((s x)^2*f (s x)) ∂μ) := by
    convert hEP using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
    congr 2
    · apply integral_congr_ae
      filter_upwards [hv] with x hx
      rw [abs_of_nonneg hx]
    · apply integral_congr_ae
      filter_upwards [hv] with x hx
      rw [abs_of_nonneg hx]
      ring
  have hvar := AnalyticMinimizer.critical_scalar_start q.inclusion
    (AnalyticMinimizer.energy q.inclusion q.closedGradient (4*β) (k+1:ℝ)) hp
    (by positivity : (0:ℝ) < k+1) v P hW hE (hmin P)
    (fun x => w (s x)) (fun x => (s x)^2*f (s x))
    (Eventually.of_forall fun x => (chordBubble_pos ha.le c (s x)).le) hP hEP'
  have hav := profile_average ν hsν (Nat.succ_pos k) hc ha (by simpa only [Nat.cast_succ] using hnc)
  rw [show 1/(2*c) = β from beta_inverse_half hb] at hav
  have hk : (∫ x, (w (s x))^(2+4*β) ∂ν) =
      ChordTransform.transform ν (k+1) (fun x => (s x)^2) a := by
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp only [w,chordBubble,ChordTransform.kernel]
    rw [←Real.rpow_mul (by positivity : (0:ℝ) ≤ 1+a*(s x)^2)]
    rw [show -c*(2+4*β) = -(k+1:ℝ) from beta_critical_product hb hn]
  rw [hk,beta_critical_ratio hb hn,hav] at hvar
  simpa only [c,beta_half_dimension hb hn,Nat.cast_succ] using hvar
end CAT0Fillings.ChartGeometry
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CAT0Fillings.ChartGeometry.chord_scalar_average_oai.{u_1} := @OAI.CAT0Fillings.ChartGeometry.chord_scalar_average_oai.{u_1}
