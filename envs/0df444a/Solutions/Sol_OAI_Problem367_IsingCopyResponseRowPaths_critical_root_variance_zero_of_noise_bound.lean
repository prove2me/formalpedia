-- Prove2me | solution 1 for OAI.Problem367.IsingCopyResponseRowPaths.critical_root_variance_zero_of_noise_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:44:51.706192+00:00
-- url     : https://prove2.me/submissions/c9f0303c-9620-4d45-a6b1-ca6cc767f295

import Mathlib
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Integral.Marginal
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI005
import Theorems.Thm_OAI_Problem367_IsingCopyResponseRowPaths_exists_actual_spatial_endpoint_constant
import Theorems.Thm_OAI_Problem367_IsingCriticalSmallLogLoss_exists_critical_small_log_bounds
import Theorems.Thm_OAI_Problem367_IsingRootDoubleExponential_integral_root_weight_mul_sq_le_double_exp

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_ShiftedLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

lemma shiftedLossCoefficient_pos {theta beta : ℝ} (hθ : theta ^ 2 < 1) :
    0 < shiftedLossCoefficient theta beta := by
  apply div_pos (sub_pos.mpr hθ)
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (Real.cosh_pos _)) (by positivity)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_AbsoluteContinuity
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace Problem367

theorem absolutelyContinuousOnInterval_comp_lipschitzOn
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : ℝ → X} {g : X → Y} {a b : ℝ} {s : Set X} {K : ℝ≥0}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : LipschitzOnWith K g s)
    (hfs : MapsTo f (uIcc a b) s) :
    AbsolutelyContinuousOnInterval (g ∘ f) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hfδ⟩ := hf (ε / (K + 1)) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro E hE hlen
  have hsmall := hfδ E hE hlen
  calc
    ∑ i ∈ Finset.range E.1, dist ((g ∘ f) (E.2 i).1) ((g ∘ f) (E.2 i).2)
      ≤ ∑ i ∈ Finset.range E.1, (K : ℝ) * dist (f (E.2 i).1) (f (E.2 i).2) := by
        apply Finset.sum_le_sum
        intro i hi
        exact hg.dist_le_mul _ (hfs (hE.1 i hi).1) _ (hfs (hE.1 i hi).2)
    _ = (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (K : ℝ) * (ε / (K + 1)) := mul_le_mul_of_nonneg_left hsmall.le K.2
    _ < ((K : ℝ) + 1) * (ε / (K + 1)) := by
      apply mul_lt_mul_of_pos_right (by linarith)
      positivity
    _ = ε := by field_simp

theorem absolutelyContinuousOnInterval_comp_contDiffOn_Icc
    {f g : ℝ → ℝ} {a b c d : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : ContDiffOn ℝ 1 g (Icc c d))
    (hfs : MapsTo f (uIcc a b) (Icc c d)) :
    AbsolutelyContinuousOnInterval (g ∘ f) a b := by
  obtain ⟨K, hK⟩ := hg.exists_lipschitzOnWith (by decide) (convex_Icc c d) isCompact_Icc
  exact absolutelyContinuousOnInterval_comp_lipschitzOn hf hK hfs

theorem ac_le_add_integral_of_neg_le_deriv
    {f k : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hk : IntervalIntegrable k volume a b)
    (hbound : ∀ᵐ x ∂volume.restrict (Icc a b), -k x ≤ deriv f x) :
    f a ≤ f b + ∫ x in a..b, k x := by
  have h := intervalIntegral.integral_mono_ae_restrict hab hk.neg
    hf.intervalIntegrable_deriv hbound
  simp only [Pi.neg_apply] at h
  rw [intervalIntegral.integral_neg, hf.integral_deriv_eq_sub] at h
  linarith

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_Osgood
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Problem367

lemma osgoodInner_pos {K x : ℝ} (hx : 0 < x) (hxK : x ≤ K) :
    0 < 1 + Real.log (K / x) := by
  have hratio : 1 ≤ K / x := (le_div_iff₀ hx).2 (by simpa using hxK)
  have hlog : 0 ≤ Real.log (K / x) := Real.log_nonneg hratio
  linarith

lemma hasDerivAt_osgoodTransform {K x : ℝ} (hx : 0 < x) (hxK : x ≤ K) :
    HasDerivAt (osgoodTransform K)
      (-1 / (x * (1 + Real.log (K / x)))) x := by
  have hK : 0 < K := hx.trans_le hxK
  have hratio : K / x ≠ 0 := ne_of_gt (div_pos hK hx)
  have hinner : 1 + Real.log (K / x) ≠ 0 := ne_of_gt (osgoodInner_pos hx hxK)
  have h := (((hasDerivAt_const x K).div (hasDerivAt_id x) (ne_of_gt hx)).log hratio).const_add 1
  convert! h.log hinner using 1
  all_goals try with_reducible_and_instances rfl
  dsimp
  field_simp
  ring

lemma continuousOn_criticalLogPrimitive {T : ℝ} (hT1 : T < 1) :
    ContinuousOn (fun t : ℝ => -(Real.log t)⁻¹) (Icc 0 T) := by
  intro t ht
  by_cases ht0 : t = 0
  · subst t
    have hlim : Tendsto (fun t : ℝ => -(Real.log t)⁻¹) (𝓝[≠] 0) (𝓝 0) := by
      simpa using Real.tendsto_log_nhdsNE_zero.inv_tendsto_atBot.neg
    have hcont0 : ContinuousAt (fun t : ℝ => -(Real.log t)⁻¹) 0 := by
      rw [continuousAt_iff_punctured_nhds]
      simpa using hlim
    exact hcont0.continuousWithinAt
  · have ht1 : t ≠ 1 := by linarith [ht.2]
    have htm1 : t ≠ -1 := by linarith [ht.1]
    exact ((Real.hasDerivAt_inv_log ht0 ht1 htm1).neg).continuousAt.continuousWithinAt

lemma hasDerivAt_criticalLogPrimitive {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    HasDerivAt (fun t : ℝ => -(Real.log t)⁻¹)
      (1 / (t * (Real.log (1 / t)) ^ 2)) t := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have htm1 : t ≠ -1 := by linarith
  convert! (Real.hasDerivAt_inv_log ht0 ht1.ne htm1).neg using 1
  all_goals try with_reducible_and_instances rfl
  simp only [one_div, Real.log_inv, neg_sq, neg_div, neg_neg]
  field_simp

lemma criticalLogCoefficient_integrable {T : ℝ} (hT1 : T < 1) :
    IntegrableOn (fun t : ℝ => 1 / (t * (Real.log (1 / t)) ^ 2)) (Ioc 0 T) := by
  apply intervalIntegral.integrableOn_deriv_of_nonneg (continuousOn_criticalLogPrimitive hT1)
  · intro t ht
    exact hasDerivAt_criticalLogPrimitive ht.1 (ht.2.trans hT1)
  · intro t ht
    have : 0 < t := ht.1
    positivity

lemma criticalCoefficient_integrable {T : ℝ} (hT1 : T < 1) :
    IntegrableOn (fun t : ℝ => 1 + t ^ (-(3 : ℝ) / 4) +
      1 / (t * (Real.log (1 / t)) ^ 2)) (Ioc 0 T) := by
  have hp : IntervalIntegrable (fun t : ℝ => t ^ (-(3 : ℝ) / 4)) volume 0 T :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc 0 T) := by
    exact integrableOn_const (by simp)
  exact (hc.add hp.1).add (criticalLogCoefficient_integrable hT1)

lemma criticalTimeCoefficient_integrable (T C : ℝ) {cutoff : ℝ} (hc : cutoff < 1) :
    IntegrableOn (criticalTimeCoefficient cutoff C) (Ioc 0 T) := by
  have hearly : IntegrableOn
      (fun t : ℝ => 1 + t ^ (-(3 : ℝ) / 4) + 1 / (t * (Real.log (1 / t)) ^ 2))
      (Iic cutoff) (volume.restrict (Ioc 0 T)) := by
    rw [IntegrableOn, Measure.restrict_restrict measurableSet_Iic]
    exact (criticalCoefficient_integrable hc).mono_set (by
      intro t ht
      exact ⟨ht.2.1, ht.1⟩)
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc 0 T) :=
    integrableOn_const (by simp)
  have hlate : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Iic cutoff)ᶜ
      (volume.restrict (Ioc 0 T)) := hconst.integrableOn
  have hpiece := Integrable.piecewise measurableSet_Iic hearly hlate
  change Integrable (fun t => criticalTimeCoefficient cutoff C t) (volume.restrict (Ioc 0 T))
  simpa only [criticalTimeCoefficient, Set.piecewise, Set.mem_Iic] using hpiece.const_mul C

lemma criticalTimeCoefficient_intervalIntegrable {T cutoff : ℝ} (C : ℝ)
    (hT : 0 ≤ T) (hc : cutoff < 1) :
    IntervalIntegrable (criticalTimeCoefficient cutoff C) volume 0 T := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2
  exact criticalTimeCoefficient_integrable T C hc

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_OsgoodIntegration
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace Problem367

theorem contDiffOn_osgoodTransform {c K : ℝ} (hc : 0 < c) (hcK : c ≤ K) :
    ContDiffOn ℝ 1 (fun z : ℝ => Real.log (1 + Real.log (K / z))) (Icc c K) := by
  have hK : 0 < K := hc.trans_le hcK
  have hdiv : ContDiffOn ℝ 1 (fun z : ℝ => K / z) (Icc c K) :=
    contDiffOn_const.div contDiffOn_id (fun z hz => ne_of_gt (hc.trans_le hz.1))
  apply (contDiffOn_const.add (hdiv.log ?_)).log
  · intro z hz
    have hzpos : 0 < z := hc.trans_le hz.1
    have hlog : 0 ≤ Real.log (K / z) := Real.log_nonneg ((one_le_div hzpos).2 hz.2)
    linarith
  · intro z hz
    exact ne_of_gt (div_pos hK (hc.trans_le hz.1))

theorem absolutelyContinuousOnInterval_osgoodTransform
    {V : ℝ → ℝ} {a b K : ℝ}
    (hV : AbsolutelyContinuousOnInterval V a b)
    (hpos : ∀ x ∈ uIcc a b, 0 < V x)
    (hupper : ∀ x ∈ uIcc a b, V x ≤ K) :
    AbsolutelyContinuousOnInterval
      (fun x => Real.log (1 + Real.log (K / V x))) a b := by
  obtain ⟨x, hx, hmin⟩ := (isCompact_uIcc : IsCompact (uIcc a b)).exists_isMinOn
    (nonempty_uIcc : (uIcc a b).Nonempty) hV.continuousOn
  have hmap : MapsTo V (uIcc a b) (Icc (V x) K) := by
    intro y hy
    exact ⟨hmin hy, hupper y hy⟩
  change AbsolutelyContinuousOnInterval
    ((fun z : ℝ => Real.log (1 + Real.log (K / z))) ∘ V) a b
  exact absolutelyContinuousOnInterval_comp_contDiffOn_Icc hV
    (contDiffOn_osgoodTransform (hpos x hx) (hupper x hx)) hmap

theorem integral_le_integral_abs_superinterval
    {k : ℝ → ℝ} {a b u t : ℝ}
    (hau : a ≤ u) (hut : u ≤ t) (htb : t ≤ b)
    (hk : IntervalIntegrable k volume a b) :
    (∫ x in u..t, k x) ≤ ∫ x in a..b, |k x| := by
  calc
    (∫ x in u..t, k x) ≤ |∫ x in u..t, k x| := le_abs_self _
    _ ≤ ∫ x in u..t, |k x| := intervalIntegral.abs_integral_le_integral_abs hut
    _ ≤ ∫ x in a..b, |k x| :=
      intervalIntegral.integral_mono_interval hau hut htb
        (Filter.Eventually.of_forall (fun x => abs_nonneg (k x))) hk.abs

theorem osgoodTransform_le_add_integral
    {V k : ℝ → ℝ} {a b K : ℝ} (hab : a ≤ b)
    (hV : AbsolutelyContinuousOnInterval V a b)
    (hpos : ∀ x ∈ Icc a b, 0 < V x)
    (hupper : ∀ x ∈ Icc a b, V x ≤ K)
    (hk : IntervalIntegrable k volume a b)
    (hbound : ∀ᵐ x ∂volume.restrict (Icc a b),
      deriv V x ≤ k x * V x * (1 + Real.log (K / V x))) :
    osgoodTransform K (V a) ≤ osgoodTransform K (V b) + ∫ x in a..b, k x := by
  have hAC : AbsolutelyContinuousOnInterval (fun x => osgoodTransform K (V x)) a b := by
    apply absolutelyContinuousOnInterval_osgoodTransform hV
    · simpa only [uIcc_of_le hab] using hpos
    · simpa only [uIcc_of_le hab] using hupper
  apply ac_le_add_integral_of_neg_le_deriv hab hAC hk
  filter_upwards [hbound, ae_restrict_of_ae hV.ae_differentiableAt,
    ae_restrict_mem measurableSet_Icc] with x hx hxDiff hxmem
  have hxU : x ∈ uIcc a b := by simpa only [uIcc_of_le hab] using hxmem
  have hd := (hasDerivAt_osgoodTransform (hpos x hxmem) (hupper x hxmem)).comp x
    (hxDiff hxU).hasDerivAt
  have hden : 0 < V x * (1 + Real.log (K / V x)) :=
    mul_pos (hpos x hxmem) (osgoodInner_pos (hpos x hxmem) (hupper x hxmem))
  have hquot : deriv V x / (V x * (1 + Real.log (K / V x))) ≤ k x := by
    apply (div_le_iff₀ hden).2
    simpa only [mul_assoc] using hx
  change -k x ≤ deriv (osgoodTransform K ∘ V) x
  rw [hd.deriv]
  convert! neg_le_neg hquot using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem osgoodTransform_le_add_integral_abs
    {V k : ℝ → ℝ} {a b u t K : ℝ}
    (hau : a ≤ u) (hut : u ≤ t) (htb : t ≤ b)
    (hV : AbsolutelyContinuousOnInterval V a b)
    (hpos : ∀ x ∈ Icc u t, 0 < V x)
    (hupper : ∀ x ∈ Icc a b, V x ≤ K)
    (hk : IntervalIntegrable k volume a b)
    (hbound : ∀ᵐ x ∂volume.restrict (Icc a b), 0 < V x →
      deriv V x ≤ k x * V x * (1 + Real.log (K / V x))) :
    osgoodTransform K (V u) ≤ osgoodTransform K (V t) + ∫ x in a..b, |k x| := by
  have hab : a ≤ b := hau.trans (hut.trans htb)
  have hsub : Icc u t ⊆ Icc a b := Icc_subset_Icc hau htb
  have hsubU : uIcc u t ⊆ uIcc a b := by
    simpa only [uIcc_of_le hab, uIcc_of_le hut] using hsub
  have hlocal : ∀ᵐ x ∂volume.restrict (Icc u t),
      deriv V x ≤ k x * V x * (1 + Real.log (K / V x)) := by
    have hb := hbound.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
    filter_upwards [hb, ae_restrict_mem measurableSet_Icc] with x hx hxmem
    exact hx (hpos x hxmem)
  have hcompare := osgoodTransform_le_add_integral hut (hV.mono hsubU) hpos
    (fun x hx => hupper x (hsub hx)) (hk.mono_set hsubU) hlocal
  linarith [integral_le_integral_abs_superinterval hau hut htb hk]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Critical_Comparison
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Real MeasureTheory

namespace Problem367

theorem exists_last_level_crossing {V : ℝ → ℝ} {a t z : ℝ}
    (hat : a ≤ t) (hV : ContinuousOn V (Icc a t))
    (ha : V a < z) (ht : z < V t) :
    ∃ u ∈ Icc a t, V u = z ∧ ∀ s ∈ Icc u t, z ≤ V s := by
  let S : Set ℝ := Icc a t ∩ V ⁻¹' {z}
  have hSclosed : IsClosed S :=
    hV.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hScompact : IsCompact S :=
    isCompact_Icc.of_isClosed_subset hSclosed inter_subset_left
  have hSne : S.Nonempty := by
    obtain ⟨u, hu, hVu⟩ := intermediate_value_Icc hat hV ⟨ha.le, ht.le⟩
    exact ⟨u, hu, hVu⟩
  obtain ⟨u, hu, hmax⟩ := hScompact.exists_isMaxOn hSne continuousOn_id
  have huat : u ∈ Icc a t := hu.1
  have hVu : V u = z := hu.2
  refine ⟨u, huat, hVu, ?_⟩
  intro s hs
  by_contra hsz
  have hsz' : V s < z := lt_of_not_ge hsz
  have hus : u < s := by
    apply lt_of_le_of_ne hs.1
    intro h
    subst s
    linarith
  have hst : s ≤ t := hs.2
  have hsub : Icc s t ⊆ Icc a t := by
    intro x hx
    exact ⟨huat.1.trans (hs.1.trans hx.1), hx.2⟩
  obtain ⟨v, hv, hVv⟩ :=
    intermediate_value_Icc hst (hV.mono hsub) ⟨hsz'.le, ht.le⟩
  have hvS : v ∈ S := ⟨hsub hv, hVv⟩
  have hvu : v ≤ u := hmax hvS
  linarith [hv.1]

theorem eq_zero_of_positive_interval_lower_bound {V : ℝ → ℝ} {a b : ℝ}
    (hV : ContinuousOn V (Icc a b)) (ha : V a = 0)
    (hnonneg : ∀ t ∈ Icc a b, 0 ≤ V t)
    (hbound : ∀ t ∈ Icc a b, 0 < V t →
      ∃ c > 0, ∀ u ∈ Icc a t,
        (∀ s ∈ Icc u t, 0 < V s) → c ≤ V u) :
    ∀ t ∈ Icc a b, V t = 0 := by
  intro t ht
  by_contra hzero
  have hpos : 0 < V t := lt_of_le_of_ne (hnonneg t ht) (Ne.symm hzero)
  obtain ⟨c, hc, hcbound⟩ := hbound t ht hpos
  let z : ℝ := min c (V t) / 2
  have hz : 0 < z := by dsimp [z] <;> positivity
  have hzc : z < c := by
    dsimp [z]
    linarith [min_le_left c (V t)]
  have hzt : z < V t := by
    dsimp [z]
    linarith [min_le_right c (V t)]
  have hsub : Icc a t ⊆ Icc a b := by
    intro x hx
    exact ⟨hx.1, hx.2.trans ht.2⟩
  obtain ⟨u, hu, hVu, hafter⟩ :=
    exists_last_level_crossing ht.1 (hV.mono hsub) (by simpa [ha] using hz) hzt
  have hcu : c ≤ V u := hcbound u hu (fun s hs => hz.trans_le (hafter s hs))
  linarith

theorem lower_bound_of_log_log_le {K z B : ℝ} (hK : 0 < K) (hz : 0 < z)
    (hbound : Real.log (1 + Real.log (K / z)) ≤ B) :
    min K (K / Real.exp (Real.exp B - 1)) ≤ z := by
  by_cases hKz : K ≤ z
  · exact (min_le_left _ _).trans hKz
  have hzK : z < K := lt_of_not_ge hKz
  have hratio : 1 ≤ K / z := (le_div_iff₀ hz).2 (by simpa using hzK.le)
  have hinner : 0 < 1 + Real.log (K / z) := by
    have := Real.log_nonneg hratio
    linarith
  have hlog : Real.log (K / z) ≤ Real.exp B - 1 := by
    have := (Real.log_le_iff_le_exp hinner).1 hbound
    linarith
  have hratio_bound : K / z ≤ Real.exp (Real.exp B - 1) :=
    (Real.log_le_iff_le_exp (div_pos hK hz)).1 hlog
  have hlast : K / Real.exp (Real.exp B - 1) ≤ z := by
    apply (div_le_iff₀ (Real.exp_pos _)).2
    have := (div_le_iff₀ hz).1 hratio_bound
    nlinarith
  exact (min_le_right _ _).trans hlast

theorem eq_zero_of_log_log_comparison {V : ℝ → ℝ} {a b K C : ℝ}
    (hV : ContinuousOn V (Icc a b)) (ha : V a = 0)
    (hnonneg : ∀ t ∈ Icc a b, 0 ≤ V t) (hK : 0 < K)
    (hcompare : ∀ t ∈ Icc a b, ∀ u ∈ Icc a t,
      (∀ s ∈ Icc u t, 0 < V s) →
      Real.log (1 + Real.log (K / V u)) ≤
        Real.log (1 + Real.log (K / V t)) + C) :
    ∀ t ∈ Icc a b, V t = 0 := by
  apply eq_zero_of_positive_interval_lower_bound hV ha hnonneg
  intro t ht hpos
  let B := Real.log (1 + Real.log (K / V t)) + C
  refine ⟨min K (K / Real.exp (Real.exp B - 1)), ?_, ?_⟩
  · exact lt_min hK (div_pos hK (Real.exp_pos _))
  · intro u hu hpositive
    apply lower_bound_of_log_log_le hK
      (hpositive u (left_mem_Icc.2 hu.2))
    exact hcompare t ht u hu hpositive

theorem eq_zero_of_ae_osgood {V k : ℝ → ℝ} {a b K : ℝ}
    (hV : AbsolutelyContinuousOnInterval V a b) (ha : V a = 0)
    (hnonneg : ∀ t ∈ Icc a b, 0 ≤ V t)
    (hupper : ∀ t ∈ Icc a b, V t ≤ K) (hK : 0 < K)
    (hk : IntervalIntegrable k volume a b)
    (hbound : ∀ᵐ t ∂volume.restrict (Icc a b), 0 < V t →
      deriv V t ≤ k t * V t * (1 + Real.log (K / V t))) :
    ∀ t ∈ Icc a b, V t = 0 := by
  apply eq_zero_of_log_log_comparison
    (C := ∫ t in a..b, |k t|)
    (hV.continuousOn.mono Icc_subset_uIcc) ha hnonneg hK
  intro t ht u hu hpositive
  simpa only [osgoodTransform] using
    osgoodTransform_le_add_integral_abs hu.1 hu.2 ht.2 hV hpositive hupper hk hbound

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Critical_Reduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Real

namespace Problem367

theorem log_sq_le_four_mul {I : ℝ} (hI : 1 ≤ I) :
    (Real.log I) ^ 2 ≤ 4 * I := by
  have hI0 : 0 ≤ I := le_trans zero_le_one hI
  have hlog0 : 0 ≤ Real.log I := Real.log_nonneg hI
  have hsqrt : 0 < Real.sqrt I := Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one hI)
  have hlog := Real.log_le_sub_one_of_pos hsqrt
  rw [Real.log_sqrt hI0] at hlog
  have hle : Real.log I ≤ 2 * Real.sqrt I := by linarith
  nlinarith [Real.sq_sqrt hI0, sq_nonneg (2 * Real.sqrt I - Real.log I)]

theorem log_three_halves_le_four_mul {I : ℝ} (hI : 1 ≤ I) :
    (Real.log I) ^ ((3 : ℝ) / 2) ≤ 4 * I := by
  have hlog0 : 0 ≤ Real.log I := Real.log_nonneg hI
  by_cases hlog1 : Real.log I ≤ 1
  · have hpow : (Real.log I) ^ ((3 : ℝ) / 2) ≤ 1 :=
      Real.rpow_le_one hlog0 hlog1 (by norm_num)
    linarith
  · have hpow := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hlog1)
      (show (3 : ℝ) / 2 ≤ 2 by norm_num)
    exact hpow.trans (by simpa using log_sq_le_four_mul hI)

theorem sqrt_mul_sqrt_le_of_le_mul {S V C : ℝ}
    (_hS : 0 ≤ S) (hV : 0 ≤ V) (hC : 1 ≤ C) (hSV : S ≤ C * V) :
    Real.sqrt V * Real.sqrt S ≤ C * V := by
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  calc
    Real.sqrt V * Real.sqrt S = Real.sqrt (V * S) := (Real.sqrt_mul hV S).symm
    _ ≤ Real.sqrt (V * (C * V)) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hSV hV)
    _ = Real.sqrt C * V := by
      rw [Real.sqrt_mul hV, Real.sqrt_mul hC0]
      calc
        Real.sqrt V * (Real.sqrt C * Real.sqrt V) = Real.sqrt C * (Real.sqrt V)^2 := by ring
        _ = Real.sqrt C * V := by rw [Real.sq_sqrt hV]
    _ ≤ C * V := by
      gcongr
      exact Real.sqrt_le_self_iff.2 (Or.inr hC)

theorem endpoint_sums_critical_reduction
    {D Q L Z S V C H I R W : ℝ}
    (hC : 1 ≤ C) (hH : 1 ≤ H) (hI : 1 ≤ I)
    (hS : 0 ≤ S) (hV : 0 ≤ V) (hVH : V ≤ H)
    (hSV : S ≤ C * V) (hR : 0 ≤ R) (hW : 0 ≤ W)
    (hQ : Q ≤ C * (S * (R + (Real.log I)^2) + V^2))
    (hL : L ≤ C * (V * (W + Real.log I) + V^2))
    (hZ : Z ≤ C * (Real.sqrt S * (W + (Real.log I)^((3 : ℝ)/2)) + V))
    (hD : D ≤ C * (V + Q + L + Real.sqrt V * Z)) :
    D ≤ C^2 * (9*C + 3*H + 3) * (S*R + V*(I+W)) := by
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  have hH0 : 0 ≤ H := le_trans zero_le_one hH
  have hI0 : 0 ≤ I := le_trans zero_le_one hI
  have hlog0 : 0 ≤ Real.log I := Real.log_nonneg hI
  have hlog : Real.log I ≤ I := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hlog2 := log_sq_le_four_mul hI
  have hlog3 := log_three_halves_le_four_mul hI
  have hsqrt := sqrt_mul_sqrt_le_of_le_mul hS hV hC hSV
  have hsqrtV : Real.sqrt V ≤ H :=
    (Real.sqrt_le_sqrt hVH).trans (Real.sqrt_le_self_iff.2 (Or.inr hH))
  have hV2 : V^2 ≤ H*V := by nlinarith
  have hVI : V ≤ V*I := by nlinarith
  have hHV : H*V ≤ H*V*I := by nlinarith
  have hSlog : S * (Real.log I)^2 ≤ 4*C*V*I := by
    calc
      S * (Real.log I)^2 ≤ (C*V) * (4*I) := mul_le_mul hSV hlog2 (sq_nonneg _) (by positivity)
      _ = 4*C*V*I := by ring
  have hQ' : Q ≤ C*(S*R + (4*C+H)*V*I) := by
    have hstep : S*(R+(Real.log I)^2)+V^2 ≤ S*R+(4*C+H)*V*I := by
      nlinarith
    exact hQ.trans (mul_le_mul_of_nonneg_left hstep hC0)
  have hL' : L ≤ C*(V*W + (1+H)*V*I) := by
    have hstep : V*(W+Real.log I)+V^2 ≤ V*W+(1+H)*V*I := by
      have := mul_le_mul_of_nonneg_left hlog hV
      nlinarith
    exact hL.trans (mul_le_mul_of_nonneg_left hstep hC0)
  have hZ' : Real.sqrt V * Z ≤ C*(C*V*W+(4*C+H)*V*I) := by
    calc
      Real.sqrt V * Z ≤ Real.sqrt V * (C*(Real.sqrt S*(W+(Real.log I)^((3:ℝ)/2))+V)) :=
        mul_le_mul_of_nonneg_left hZ (Real.sqrt_nonneg _)
      _ = C*((Real.sqrt V*Real.sqrt S)*(W+(Real.log I)^((3:ℝ)/2)) + Real.sqrt V*V) := by ring
      _ ≤ C*((C*V)*(W+4*I)+H*V*I) := by
        apply mul_le_mul_of_nonneg_left _ hC0
        apply add_le_add
        · exact mul_le_mul hsqrt (add_le_add le_rfl hlog3)
            (add_nonneg hW (Real.rpow_nonneg hlog0 _)) (by positivity)
        · exact (mul_le_mul_of_nonneg_right hsqrtV hV).trans hHV
      _ = C*(C*V*W+(4*C+H)*V*I) := by ring
  have hstart : D ≤ C*(V+C*(S*R+(4*C+H)*V*I)+C*(V*W+(1+H)*V*I)+
      C*(C*V*W+(4*C+H)*V*I)) := by
    apply hD.trans
    gcongr
  have hscale : 0 ≤ S*R := mul_nonneg hS hR
  have hVI0 : 0 ≤ V*I := mul_nonneg hV hI0
  have hVW0 : 0 ≤ V*W := mul_nonneg hV hW
  have hC2 : C ≤ C^2 := by nlinarith
  have hCpos : 0 ≤ C^2 := sq_nonneg C
  have hCV : C*V ≤ C^2*(V*I) := mul_le_mul hC2 hVI hV hCpos
  have hcoef1 : 1 ≤ 9*C+3*H+3 := by linarith
  have hcoef2 : 8*C+3*H+2 ≤ 9*C+3*H+3 := by linarith
  have hcoef3 : C+1 ≤ 9*C+3*H+3 := by linarith
  calc
    D ≤ C*V + C^2*(S*R) + C^2*(8*C+3*H+1)*(V*I) +
        C^2*(C+1)*(V*W) := by convert hstart using 1 <;> first | rfl | ring
    _ ≤ C^2*(V*I) + C^2*(S*R) + C^2*(8*C+3*H+1)*(V*I) +
        C^2*(C+1)*(V*W) := by gcongr
    _ = C^2*(S*R+(8*C+3*H+2)*(V*I)+(C+1)*(V*W)) := by ring
    _ ≤ C^2*((9*C+3*H+3)*(S*R)+(9*C+3*H+3)*(V*I)+
        (9*C+3*H+3)*(V*W)) := by
      apply mul_le_mul_of_nonneg_left _ hCpos
      apply add_le_add
      · apply add_le_add
        · simpa using mul_le_mul_of_nonneg_right hcoef1 hscale
        · exact mul_le_mul_of_nonneg_right hcoef2 hVI0
      · exact mul_le_mul_of_nonneg_right hcoef3 hVW0
    _ = C^2*(9*C+3*H+3)*(S*R+V*(I+W)) := by ring

theorem small_time_scale_reduction {S B V I J t : ℝ}
    (hB : 0 ≤ B) (hV : 0 ≤ V) (hI : 1 ≤ I) (hJ : 0 < J) (ht : 0 < t)
    (hS : S ≤ B*V*(t^((1:ℝ)/4)+I/J)) :
    S/t + V*(I+t^(-(3:ℝ)/4)) ≤
      (B+1)*V*I*(1+t^(-(3:ℝ)/4)+1/(t*J)) := by
  have hI0 : 0 ≤ I := le_trans zero_le_one hI
  have hW : 0 ≤ t^(-(3:ℝ)/4) := Real.rpow_nonneg ht.le _
  have htJ : 0 < t*J := mul_pos ht hJ
  have hpow : t^((1:ℝ)/4)/t = t^(-(3:ℝ)/4) := by
    rw [show -(3:ℝ)/4 = (1:ℝ)/4-1 by norm_num, Real.rpow_sub ht, Real.rpow_one]
  have hnoise : S/t ≤ B*V*(t^(-(3:ℝ)/4)+I/(t*J)) := by
    calc
      S/t ≤ (B*V*(t^((1:ℝ)/4)+I/J))/t := div_le_div_of_nonneg_right hS ht.le
      _ = B*V*(t^((1:ℝ)/4)/t+I/(t*J)) := by field_simp
      _ = B*V*(t^(-(3:ℝ)/4)+I/(t*J)) := by rw [hpow]
  have hfirst : (B+1)*V*t^(-(3:ℝ)/4) ≤ (B+1)*V*I*t^(-(3:ℝ)/4) := by
    have := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hI (show 0 ≤ (B+1)*V by positivity)) hW
    simpa using this
  have hsecond : B*V*I/(t*J) ≤ (B+1)*V*I/(t*J) := by gcongr; linarith
  have hthird : V*I ≤ (B+1)*V*I := by nlinarith [mul_nonneg hB (mul_nonneg hV hI0)]
  calc
    S/t + V*(I+t^(-(3:ℝ)/4)) ≤ B*V*(t^(-(3:ℝ)/4)+I/(t*J)) + V*(I+t^(-(3:ℝ)/4)) :=
      add_le_add hnoise le_rfl
    _ = (B+1)*V*t^(-(3:ℝ)/4) + B*V*I/(t*J) + V*I := by ring
    _ ≤ (B+1)*V*I*t^(-(3:ℝ)/4) + (B+1)*V*I/(t*J) + (B+1)*V*I :=
      add_le_add (add_le_add hfirst hsecond) hthird
    _ = (B+1)*V*I*(1+t^(-(3:ℝ)/4)+1/(t*J)) := by ring

theorem critical_differential_bound_of_endpoint_sums
    {D Q L Z S V C H I B J t : ℝ}
    (hC : 1 ≤ C) (hH : 1 ≤ H) (hI : 1 ≤ I) (hB : 0 ≤ B)
    (hS : 0 ≤ S) (hV : 0 ≤ V) (hVH : V ≤ H) (hSV : S ≤ C*V)
    (hJ : 0 < J) (ht : 0 < t)
    (hsmall : S ≤ B*V*(t^((1:ℝ)/4)+I/J))
    (hQ : Q ≤ C*(S*(1/t+(Real.log I)^2)+V^2))
    (hL : L ≤ C*(V*(t^(-(3:ℝ)/4)+Real.log I)+V^2))
    (hZ : Z ≤ C*(Real.sqrt S*(t^(-(3:ℝ)/4)+(Real.log I)^((3:ℝ)/2))+V))
    (hD : D ≤ C*(V+Q+L+Real.sqrt V*Z)) :
    D ≤ (C^2*(9*C+3*H+3)*(B+1))*V*I*
      (1+t^(-(3:ℝ)/4)+1/(t*J)) := by
  have hscale := endpoint_sums_critical_reduction hC hH hI hS hV hVH hSV
    (show 0 ≤ 1/t by positivity) (Real.rpow_nonneg ht.le _) hQ hL hZ hD
  have hreduce := small_time_scale_reduction hB hV hI hJ ht hsmall
  have hconst : 0 ≤ C^2*(9*C+3*H+3) := by positivity
  calc
    D ≤ C^2*(9*C+3*H+3)*(S/t+V*(I+t^(-(3:ℝ)/4))) := by
      simpa only [mul_one_div] using hscale
    _ ≤ C^2*(9*C+3*H+3)*((B+1)*V*I*(1+t^(-(3:ℝ)/4)+1/(t*J))) :=
      mul_le_mul_of_nonneg_left hreduce hconst
    _ = (C^2*(9*C+3*H+3)*(B+1))*V*I*(1+t^(-(3:ℝ)/4)+1/(t*J)) := by ring

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Critical_TimeUniqueness
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory

namespace Problem367

theorem eq_zero_of_ae_criticalTimeCoefficient {V : ℝ → ℝ} {T K cutoff C : ℝ}
    (hT : 0 ≤ T) (hc : cutoff < 1)
    (hV : AbsolutelyContinuousOnInterval V 0 T) (hzero : V 0 = 0)
    (hnonneg : ∀ t ∈ Icc 0 T, 0 ≤ V t)
    (hupper : ∀ t ∈ Icc 0 T, V t ≤ K) (hK : 0 < K)
    (hbound : ∀ᵐ t ∂volume.restrict (Icc 0 T), 0 < V t →
      deriv V t ≤ criticalTimeCoefficient cutoff C t * V t *
        (1 + Real.log (K / V t))) :
    ∀ t ∈ Icc 0 T, V t = 0 := by
  exact eq_zero_of_ae_osgood hV hzero hnonneg hupper hK
    (criticalTimeCoefficient_intervalIntegrable C hT hc) hbound

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_LogInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Real

namespace Problem367

theorem min_linear_exp_le_log_interpolation {A B c J K u : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 0 < c) (hJ : 0 < J)
    (hK : 1 ≤ K) (hu : 0 < u) (huK : u ≤ K) :
    min (A * u) (B * Real.exp (-c * J)) ≤
      (2 * (A + B) / c) * u * (1 + Real.log (K / u)) / J := by
  let I : ℝ := 1 + Real.log (K / u)
  let q : ℝ := c * J / 2
  have hq : 0 < q := by dsimp [q] <;> positivity
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hI : 1 ≤ I := by
    have hratio : 1 ≤ K / u := (one_le_div hu).2 huK
    have := Real.log_nonneg hratio
    dsimp [I]
    linarith
  change min (A * u) (B * Real.exp (-c * J)) ≤
    (2 * (A + B) / c) * u * I / J
  by_cases hsmall : u ≤ Real.exp (-q)
  · have hlogu : Real.log u ≤ -q := (Real.log_le_iff_le_exp hu).2 hsmall
    have hqI : q ≤ I := by
      dsimp [I]
      rw [Real.log_div (ne_of_gt hKpos) (ne_of_gt hu)]
      have := Real.log_nonneg hK
      linarith
    calc
      min (A * u) (B * Real.exp (-c * J)) ≤ A * u := min_le_left _ _
      _ ≤ (A + B) * u := by gcongr; linarith
      _ = (2 * (A + B) / c) * u * q / J := by
        dsimp [q]
        field_simp
      _ ≤ (2 * (A + B) / c) * u * I / J := by gcongr
  · have hlarge : Real.exp (-q) ≤ u := le_of_not_ge hsmall
    have hqexp : q ≤ Real.exp q := by
      have := Real.add_one_le_exp q
      linarith
    have hexp : Real.exp (-q) ≤ 1 / q := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_le_one_div_of_le hq hqexp
    have hexps : Real.exp (-c * J) = Real.exp (-q) * Real.exp (-q) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [q]
      ring
    calc
      min (A * u) (B * Real.exp (-c * J)) ≤ B * Real.exp (-c * J) := min_le_right _ _
      _ = B * Real.exp (-q) * Real.exp (-q) := by rw [hexps]; ring
      _ ≤ B * u * Real.exp (-q) := by gcongr
      _ ≤ (A + B) * u * (1 / q) := by gcongr; linarith
      _ ≤ ((A + B) * u * (1 / q)) * I := by
        have hnonneg : 0 ≤ (A + B) * u * (1 / q) := by positivity
        simpa using mul_le_mul_of_nonneg_left hI hnonneg
      _ = (2 * (A + B) / c) * u * I / J := by
        dsimp [q]
        field_simp

theorem small_log_loss_of_minimum {S A B c J K u R : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 0 < c) (hJ : 0 < J)
    (hK : 1 ≤ K) (hu : 0 < u) (huK : u ≤ K) (hR : 0 ≤ R)
    (hS : S ≤ A * R * u + min (A * u) (B * Real.exp (-c * J))) :
    S ≤ (A + 2 * (A + B) / c) * u *
      (R + (1 + Real.log (K / u)) / J) := by
  have hI : 0 ≤ 1 + Real.log (K / u) := by
    have := Real.log_nonneg ((one_le_div hu).2 huK)
    linarith
  have hC : 0 ≤ 2 * (A + B) / c := by positivity
  calc
    S ≤ A * R * u + (2 * (A + B) / c) * u * (1 + Real.log (K / u)) / J :=
      hS.trans (add_le_add le_rfl (min_linear_exp_le_log_interpolation hA hB hc hJ hK hu huK))
    _ ≤ (A + 2 * (A + B) / c) * R * u +
        (2 * (A + B) / c) * u * (1 + Real.log (K / u)) / J := by
      gcongr
      linarith
    _ ≤ (A + 2 * (A + B) / c) * R * u +
        (A + 2 * (A + B) / c) * u * (1 + Real.log (K / u)) / J := by
      gcongr
      linarith
    _ = (A + 2 * (A + B) / c) * u *
        (R + (1 + Real.log (K / u)) / J) := by ring

theorem small_time_log_loss_of_minimum {S A B c K u t : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 0 < c)
    (hK : 1 ≤ K) (hu : 0 < u) (huK : u ≤ K)
    (ht : 0 < t) (ht1 : t < 1)
    (hS : S ≤ A * t ^ ((1 : ℝ) / 4) * u +
      min (A * u) (B * Real.exp (-c * (Real.log (1 / t)) ^ 2))) :
    S ≤ (A + 2 * (A + B) / c) * u *
      (t ^ ((1 : ℝ) / 4) + (1 + Real.log (K / u)) / (Real.log (1 / t)) ^ 2) := by
  have hlog : 0 < Real.log (1 / t) := Real.log_pos ((one_lt_div ht).2 ht1)
  exact small_log_loss_of_minimum hA hB hc (sq_pos_of_pos hlog) hK hu huK
    (Real.rpow_nonneg ht.le _) hS

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Critical_Endgame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory

namespace Problem367

theorem CriticalEndpointBounds.differential_bound
    {D Q L Z S V C H A B c K t : ℝ}
    (h : CriticalEndpointBounds D Q L Z S V C A B c K t)
    (hC : 1 ≤ C) (hH : 1 ≤ H) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hc : 0 < c) (hK : 1 ≤ K) (hV : 0 < V) (hVK : V ≤ K)
    (hVH : V ≤ H) (ht : 0 < t) (ht1 : t < 1) :
    D ≤ (C ^ 2 * (9 * C + 3 * H + 3) * (A + 2 * (A + B) / c + 1)) *
      V * (1 + Real.log (K / V)) *
      (1 + t ^ (-(3 : ℝ) / 4) + 1 / (t * (Real.log (1 / t)) ^ 2)) := by
  have hI : 1 ≤ 1 + Real.log (K / V) := by
    have := Real.log_nonneg ((one_le_div hV).2 hVK)
    linarith
  have hJ : 0 < (Real.log (1 / t)) ^ 2 :=
    sq_pos_of_pos (Real.log_pos ((one_lt_div ht).2 ht1))
  exact critical_differential_bound_of_endpoint_sums hC hH hI
    (by positivity) h.noise_nonneg hV.le hVH h.noise_le hJ ht
    (small_time_log_loss_of_minimum hA hB hc hK hV hVK ht ht1 h.small_loss)
    h.quadratic h.linear h.square_root h.drift

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_EndpointTimeScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem inv_sqrt_sq_time {t : ℝ} (ht : 0 ≤ t) :
    (Real.sqrt t)⁻¹ ^ 2 = 1 / t := by
  rw [inv_pow, Real.sq_sqrt ht, one_div]

theorem mul_sqrt_eq_three_halves {x : ℝ} (hx : 0 ≤ x) :
    x * Real.sqrt x = x ^ ((3 : ℝ) / 2) := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · norm_num
  calc
    x * Real.sqrt x = x ^ (1 : ℝ) * x ^ ((1 : ℝ) / 2) := by
      rw [Real.rpow_one, Real.sqrt_eq_rpow]
    _ = x ^ ((1 : ℝ) + 1 / 2) := (Real.rpow_add hx _ _).symm
    _ = x ^ ((3 : ℝ) / 2) := by norm_num

theorem inv_sqrt_mul_sqrt_time {t : ℝ} (ht : 0 < t) :
    (Real.sqrt t)⁻¹ * Real.sqrt ((Real.sqrt t)⁻¹) = t ^ (-(3 : ℝ) / 4) := by
  rw [mul_sqrt_eq_three_halves (by positivity), Real.sqrt_eq_rpow,
    ← Real.rpow_neg_one, ← Real.rpow_mul ht.le, ← Real.rpow_mul ht.le]
  norm_num

theorem inv_sqrt_le_time_three_quarters {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (Real.sqrt t)⁻¹ ≤ t ^ (-(3 : ℝ) / 4) := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hs1 : Real.sqrt t ≤ 1 := by
    simpa using Real.sqrt_le_sqrt ht1
  have hi : 1 ≤ (Real.sqrt t)⁻¹ := (one_le_inv₀ hs).2 hs1
  have hsqrt1 : 1 ≤ Real.sqrt ((Real.sqrt t)⁻¹) := by
    simpa using Real.sqrt_le_sqrt hi
  rw [← inv_sqrt_mul_sqrt_time ht]
  simpa using mul_le_mul_of_nonneg_left hsqrt1 (inv_nonneg.2 hs.le)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Critical_GlobalEndgame
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory

namespace Problem367

theorem eq_zero_of_ae_small_critical_large_osgood
    {V : ℝ → ℝ} {T K cutoff C : ℝ}
    (hT : 0 ≤ T) (hc : cutoff < 1)
    (hV : AbsolutelyContinuousOnInterval V 0 T) (hzero : V 0 = 0)
    (hnonneg : ∀ t ∈ Icc 0 T, 0 ≤ V t)
    (hupper : ∀ t ∈ Icc 0 T, V t ≤ K) (hK : 0 < K)
    (hsmall : ∀ᵐ t ∂volume.restrict (Ioc 0 T), t ≤ cutoff → 0 < V t →
      deriv V t ≤ C * V t * (1 + Real.log (K / V t)) *
        (1 + t ^ (-(3 : ℝ) / 4) + 1 / (t * (Real.log (1 / t)) ^ 2)))
    (hlarge : ∀ᵐ t ∂volume.restrict (Ioc 0 T), cutoff < t → 0 < V t →
      deriv V t ≤ C * V t * (1 + Real.log (K / V t))) :
    ∀ t ∈ Icc 0 T, V t = 0 := by
  apply eq_zero_of_ae_criticalTimeCoefficient hT hc hV hzero hnonneg hupper hK
  rw [← restrict_Ioc_eq_restrict_Icc]
  filter_upwards [hsmall, hlarge] with t hs hl
  intro hpos
  by_cases ht : t ≤ cutoff
  · simpa only [criticalTimeCoefficient, ite_eq_left ht, mul_assoc, mul_left_comm,
      mul_comm] using hs ht hpos
  · simpa only [criticalTimeCoefficient, ite_eq_right ht, mul_one] using
      hl (lt_of_not_ge ht) hpos

theorem endpoint_sums_bounded_scale_reduction
    {D Q L Z S V C H I R W Rmax Wmax : ℝ}
    (hC : 1 ≤ C) (hH : 1 ≤ H) (hI : 1 ≤ I)
    (hS : 0 ≤ S) (hV : 0 ≤ V) (hVH : V ≤ H)
    (hSV : S ≤ C * V) (hR : 0 ≤ R) (hW : 0 ≤ W)
    (hRmax : R ≤ Rmax) (hWmax : W ≤ Wmax)
    (hQ : Q ≤ C * (S * (R + (Real.log I) ^ 2) + V ^ 2))
    (hL : L ≤ C * (V * (W + Real.log I) + V ^ 2))
    (hZ : Z ≤ C * (Real.sqrt S * (W + (Real.log I) ^ ((3 : ℝ) / 2)) + V))
    (hD : D ≤ C * (V + Q + L + Real.sqrt V * Z)) :
    D ≤ (C ^ 2 * (9 * C + 3 * H + 3) * (C * Rmax + 1 + Wmax)) * V * I := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hRmax0 : 0 ≤ Rmax := hR.trans hRmax
  have hWmax0 : 0 ≤ Wmax := hW.trans hWmax
  have hVI : V ≤ V * I := by nlinarith
  have hnoise : S * R ≤ (C * Rmax) * (V * I) := by
    calc
      S * R ≤ (C * V) * Rmax := mul_le_mul hSV hRmax hR (by positivity)
      _ = (C * Rmax) * V := by ring
      _ ≤ (C * Rmax) * (V * I) :=
        mul_le_mul_of_nonneg_left hVI (by positivity)
  have hlinear : V * (I + W) ≤ (1 + Wmax) * (V * I) := by
    calc
      V * (I + W) ≤ V * I + Wmax * V := by
        nlinarith [mul_le_mul_of_nonneg_left hWmax hV]
      _ ≤ V * I + Wmax * (V * I) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hVI hWmax0)
      _ = (1 + Wmax) * (V * I) := by ring
  have hscale := endpoint_sums_critical_reduction hC hH hI hS hV hVH hSV
    hR hW hQ hL hZ hD
  calc
    D ≤ C ^ 2 * (9 * C + 3 * H + 3) * (S * R + V * (I + W)) := hscale
    _ ≤ C ^ 2 * (9 * C + 3 * H + 3) *
        ((C * Rmax) * (V * I) + (1 + Wmax) * (V * I)) :=
      mul_le_mul_of_nonneg_left (add_le_add hnoise hlinear) (by positivity)
    _ = _ := by ring

theorem inv_le_inv_mul_sqrt {ω : ℝ} (hω : 0 < ω) (hω1 : ω ≤ 1) :
    ω⁻¹ ≤ ω⁻¹ * Real.sqrt (ω⁻¹) := by
  have hi : 1 ≤ ω⁻¹ := (one_le_inv₀ hω).2 hω1
  have hs : 1 ≤ Real.sqrt (ω⁻¹) := by
    exact (Real.one_le_sqrt).2 hi
  simpa using mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hω.le)

theorem CriticalSpatialEndpointBounds.small_time
    {D Q L Z S V C A B c K t : ℝ}
    (h : CriticalSpatialEndpointBounds D Q L Z S V C K (Real.sqrt t))
    (hC : 0 ≤ C) (hV : 0 ≤ V) (ht : 0 < t) (ht1 : t ≤ 1)
    (hsmall : S ≤ A * t ^ ((1 : ℝ) / 4) * V +
      min (A * V) (B * Real.exp (-c * (Real.log (1 / t)) ^ 2))) :
    CriticalEndpointBounds D Q L Z S V C A B c K t := by
  refine ⟨h.noise_nonneg, h.noise_le, hsmall, ?_, ?_, ?_, h.drift⟩
  · simpa only [inv_sqrt_sq_time ht.le] using h.quadratic
  · apply h.linear.trans
    apply mul_le_mul_of_nonneg_left _ hC
    apply add_le_add _ le_rfl
    apply mul_le_mul_of_nonneg_left _ hV
    exact add_le_add (inv_sqrt_le_time_three_quarters ht ht1) le_rfl
  · simpa only [inv_sqrt_mul_sqrt_time ht] using h.square_root

theorem CriticalSpatialEndpointBounds.late_time
    {D Q L Z S V C H K ω ε : ℝ}
    (h : CriticalSpatialEndpointBounds D Q L Z S V C K ω)
    (hC : 1 ≤ C) (hH : 1 ≤ H) (hV : 0 < V) (hVK : V ≤ K) (hVH : V ≤ H)
    (hε : 0 < ε) (hεω : ε ≤ ω) (hω1 : ω ≤ 1) :
    D ≤ criticalLateCoefficient C H ε * V * (1 + Real.log (K / V)) := by
  have hω : 0 < ω := hε.trans_le hεω
  have hωinv : 0 ≤ ω⁻¹ := inv_nonneg.mpr hω.le
  have hεinv : 0 ≤ ε⁻¹ := inv_nonneg.mpr hε.le
  have hinv : ω⁻¹ ≤ ε⁻¹ := (inv_le_inv₀ hω hε).2 hεω
  have hI : 1 ≤ 1 + Real.log (K / V) := by
    have := Real.log_nonneg ((one_le_div hV).2 hVK)
    linarith
  have hlinear : L ≤ C * (V *
      (ω⁻¹ * Real.sqrt (ω⁻¹) + Real.log (1 + Real.log (K / V))) + V ^ 2) := by
    apply h.linear.trans
    apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hC)
    apply add_le_add _ le_rfl
    apply mul_le_mul_of_nonneg_left _ hV.le
    exact add_le_add (inv_le_inv_mul_sqrt hω hω1) le_rfl
  exact endpoint_sums_bounded_scale_reduction hC hH hI h.noise_nonneg hV.le hVH
    h.noise_le (sq_nonneg _) (mul_nonneg hωinv (Real.sqrt_nonneg _))
    ((sq_le_sq₀ hωinv hεinv).2 hinv)
    (mul_le_mul hinv (Real.sqrt_le_sqrt hinv) (Real.sqrt_nonneg _) hεinv)
    h.quadratic hlinear h.square_root h.drift

theorem eq_zero_of_ae_critical_spatial_endpoint_bounds
    {V Q L Z S : ℝ → ℝ} {T cutoff C H A B c K : ℝ}
    (hT : 0 ≤ T) (hcutoff0 : 0 < cutoff) (hcutoff : cutoff < 1)
    (hC : 1 ≤ C) (hH : 1 ≤ H) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hc : 0 < c) (hK : 1 ≤ K)
    (hV : AbsolutelyContinuousOnInterval V 0 T) (hzero : V 0 = 0)
    (hnonneg : ∀ t ∈ Icc 0 T, 0 ≤ V t)
    (hupperK : ∀ t ∈ Icc 0 T, V t ≤ K)
    (hupperH : ∀ t ∈ Icc 0 T, V t ≤ H)
    (hendpoint : ∀ᵐ t ∂volume.restrict (Ioc 0 T), 0 < V t →
      CriticalSpatialEndpointBounds (deriv V t) (Q t) (L t) (Z t) (S t) (V t) C K
        (min (Real.sqrt t) 1))
    (hsmall : ∀ᵐ t ∂volume.restrict (Ioc 0 T), t ≤ cutoff → 0 < V t →
      S t ≤ A * t ^ ((1 : ℝ) / 4) * V t +
        min (A * V t) (B * Real.exp (-c * (Real.log (1 / t)) ^ 2))) :
    ∀ t ∈ Icc 0 T, V t = 0 := by
  let early := C ^ 2 * (9 * C + 3 * H + 3) * (A + 2 * (A + B) / c + 1)
  let late := criticalLateCoefficient C H (Real.sqrt cutoff)
  let M := max early late
  apply eq_zero_of_ae_small_critical_large_osgood (C := M) hT hcutoff hV hzero
    hnonneg hupperK (zero_lt_one.trans_le hK)
  · filter_upwards [hendpoint, hsmall, ae_restrict_mem measurableSet_Ioc] with t he hs ht
    intro htc hpos
    have hmem : t ∈ Icc 0 T := ⟨ht.1.le, ht.2⟩
    have ht1 : t < 1 := htc.trans_lt hcutoff
    have htpos : 0 < t := ht.1
    have hscale : min (Real.sqrt t) 1 = Real.sqrt t :=
      min_eq_left (Real.sqrt_le_one.2 ht1.le)
    have he' := he hpos
    rw [hscale] at he'
    have hb := (he'.small_time (zero_le_one.trans hC) hpos.le ht.1 ht1.le
      (hs htc hpos)).differential_bound hC hH hA hB hc hK hpos
        (hupperK t hmem) (hupperH t hmem) ht.1 ht1
    have hlog : 0 ≤ Real.log (K / V t) :=
      Real.log_nonneg ((one_le_div hpos).2 (hupperK t hmem))
    apply hb.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (le_max_left early late) hpos.le
  · filter_upwards [hendpoint, ae_restrict_mem measurableSet_Ioc] with t he ht
    intro htc hpos
    have hmem : t ∈ Icc 0 T := ⟨ht.1.le, ht.2⟩
    have hscale : Real.sqrt cutoff ≤ min (Real.sqrt t) 1 :=
      le_min (Real.sqrt_le_sqrt htc.le) (Real.sqrt_le_one.2 hcutoff.le)
    have hb := (he hpos).late_time hC hH hpos (hupperK t hmem) (hupperH t hmem)
      (Real.sqrt_pos.2 hcutoff0) hscale (min_le_right _ _)
    have hlog : 0 ≤ Real.log (K / V t) :=
      Real.log_nonneg ((one_le_div hpos).2 (hupperK t hmem))
    apply hb.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (le_max_right early late) hpos.le

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_CompensatedSquareEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal

namespace Problem367.DiscrepancyEnergy

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem secondMoment_le_of_ae_abs_le [IsProbabilityMeasure μ]
    {X : ℝ → Ω → ℝ} {t H : ℝ}
    (hInt : Integrable (fun ω => (X t ω) ^ 2) μ)
    (hbound : ∀ᵐ ω ∂μ, |X t ω| ≤ H) :
    (∫ ω, (X t ω) ^ 2 ∂μ) ≤ H ^ 2 := by
  have hsq : ∀ᵐ ω ∂μ, (X t ω) ^ 2 ≤ H ^ 2 := by
    filter_upwards [hbound] with ω hω
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hω)).2 hω
  calc
    (∫ ω, (X t ω) ^ 2 ∂μ) ≤ ∫ _ : Ω, H ^ 2 ∂μ := integral_mono_ae hInt (integrable_const _) hsq
    _ = H ^ 2 := by simp

end Problem367.DiscrepancyEnergy

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_CoupledSmallLogLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem cavityLogVarianceCoefficient_nonneg (theta : ℝ) :
    0 ≤ cavityLogVarianceCoefficient theta := by
  unfold cavityLogVarianceCoefficient
  positivity

theorem cavityLogTailCoefficient_nonneg (theta M : ℝ) :
    0 ≤ cavityLogTailCoefficient theta M := by
  unfold cavityLogTailCoefficient
  positivity

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ThresholdArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

lemma branching_pos {d : ℕ} (hd : 3 ≤ d) : 0 < (d : ℝ) - 1 := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

lemma threshold_sqrt_pos {d : ℕ} (hd : 3 ≤ d) :
    0 < Real.sqrt ((d : ℝ) - 1) :=
  Real.sqrt_pos.2 (branching_pos hd)

lemma threshold_iff_branching_sq {d : ℕ} {theta : ℝ}
    (hd : 3 ≤ d) (htheta : 0 ≤ theta) :
    theta ≤ 1 / Real.sqrt ((d : ℝ) - 1) ↔
      ((d : ℝ) - 1) * theta ^ 2 ≤ 1 := by
  have hb := (branching_pos hd).le
  have hs := threshold_sqrt_pos hd
  calc
    theta ≤ 1 / Real.sqrt ((d : ℝ) - 1) ↔
        theta * Real.sqrt ((d : ℝ) - 1) ≤ 1 := le_div_iff₀ hs
    _ ↔ (theta * Real.sqrt ((d : ℝ) - 1)) ^ 2 ≤ (1 : ℝ) ^ 2 :=
      (sq_le_sq₀ (mul_nonneg htheta hs.le) (by norm_num)).symm
    _ ↔ ((d : ℝ) - 1) * theta ^ 2 ≤ 1 := by
      rw [mul_pow, Real.sq_sqrt hb, one_pow, mul_comm]

lemma tanh_threshold_iff_branching_sq {d : ℕ} {beta : ℝ}
    (hd : 3 ≤ d) (hbeta : 0 ≤ beta) :
    Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1) ↔
      ((d : ℝ) - 1) * Real.tanh beta ^ 2 ≤ 1 :=
  threshold_iff_branching_sq hd (tanh_nonneg_of_beta_nonneg hbeta)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_SharedInnovationBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set Filter

namespace Problem367

theorem discrepancy_secondMoment_bounds
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {h h' : Ω → ℝ} {H : ℝ}
    (hmeas : AEStronglyMeasurable (fun ω => h ω - h' ω) μ)
    (hbound : ∀ᵐ ω ∂μ, |h ω - h' ω| ≤ H) :
    MemLp (fun ω => h ω - h' ω) 2 μ ∧
      0 ≤ (∫ ω, (h ω - h' ω) ^ 2 ∂μ) ∧
      (∫ ω, (h ω - h' ω) ^ 2 ∂μ) ≤ H ^ 2 := by
  have hLp : MemLp (fun ω => h ω - h' ω) 2 μ :=
    MemLp.of_bound hmeas H (by simpa only [Real.norm_eq_abs] using hbound)
  exact ⟨hLp, integral_nonneg (fun _ => sq_nonneg _),
    DiscrepancyEnergy.secondMoment_le_of_ae_abs_le
      (X := fun _ ω => h ω - h' ω) (t := 0) hLp.integrable_sq hbound⟩

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_SideSignalLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma sideSignalLossCoefficient_pos {theta : ℝ} (hθ0 : 0 < theta) (hθ1 : theta < 1) :
    0 < sideSignalLossCoefficient theta := by
  have hθsq : theta ^ 2 < 1 := by nlinarith
  exact mul_pos (mul_pos (shiftedLossCoefficient_pos hθsq) (sub_pos.mpr hθsq))
    (sq_pos_of_pos hθ0)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_ComponentSignalAttenuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Problem367.ComponentSignalAttenuation

open PlantedSymmetry

theorem lossCoefficient_pos {theta : ℝ} (hθ0 : 0 < theta) (hθ1 : theta < 1) :
    0 < lossCoefficient theta :=
  lt_min (div_pos (sideSignalLossCoefficient_pos hθ0 hθ1) (by norm_num)) (by norm_num)

end Problem367.ComponentSignalAttenuation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_CopyBounds
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Problem367

open PlantedSymmetry

theorem ae_observation_sub_bound_of_shared_progressive_innovation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F G : Filtration ℝ≥0 mΩ} {m m' : ℝ≥0 → Ω → ℝ}
    (hm : IsStronglyProgressive F m) (hm' : IsStronglyProgressive G m')
    (hb : ∀ t, ∀ᵐ ω ∂P, |m t ω| ≤ 1)
    (hb' : ∀ t, ∀ᵐ ω ∂P, |m' t ω| ≤ 1)
    {x x' w : Ω → ℝ} (t : ℝ≥0)
    (hx : ∀ᵐ ω ∂P, x ω = w ω + nnrealTimePrimitive m t ω)
    (hx' : ∀ᵐ ω ∂P, x' ω = w ω + nnrealTimePrimitive m' t ω) :
    ∀ᵐ ω ∂P, |x ω - x' ω| ≤ 2 * (t : ℝ) := by
  have hL := ae_lipschitzWith_nnrealTimePrimitive hm (C := 1) hb
  have hL' := ae_lipschitzWith_nnrealTimePrimitive hm' (C := 1) hb'
  filter_upwards [hL, hL', hx, hx'] with ω hω hω' hxω hxω'
  have h1 : |nnrealTimePrimitive m t ω| ≤ (t : ℝ) := by
    simpa only [Real.dist_eq, nnrealTimePrimitive, NNReal.coe_zero,
      intervalIntegral.integral_same, sub_zero, NNReal.coe_one, one_mul,
      NNReal.dist_eq, abs_of_nonneg t.coe_nonneg] using hω.dist_le_mul t 0
  have h2 : |nnrealTimePrimitive m' t ω| ≤ (t : ℝ) := by
    simpa only [Real.dist_eq, nnrealTimePrimitive, NNReal.coe_zero,
      intervalIntegral.integral_same, sub_zero, NNReal.coe_one, one_mul,
      NNReal.dist_eq, abs_of_nonneg t.coe_nonneg] using hω'.dist_le_mul t 0
  rw [hxω, hxω']
  have heq : (w ω + nnrealTimePrimitive m t ω) -
      (w ω + nnrealTimePrimitive m' t ω) =
      nnrealTimePrimitive m t ω - nnrealTimePrimitive m' t ω := by ring
  rw [heq]
  exact (abs_sub _ _).trans (by linarith)

theorem HasFreeIsingLaw.gibbsField_bound_of_observation_identDistrib
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) {X : Ω → TreeVertex d → ℝ}
    (hX : IdentDistrib X (observation t) P
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t))) :
    ∀ᵐ ω ∂P, |Real.artanh (infiniteGibbsSpinMean beta v (X ω)) - X ω v| ≤
      (d : ℝ) * beta := by
  have ha : Measurable Real.artanh := by unfold Real.artanh; fun_prop
  have hmeas := (ha.comp (measurable_infiniteGibbsSpinMean beta v)).sub
    (measurable_pi_apply v)
  apply hX.symm.ae_snd (measurableSet_le hmeas.abs measurable_const)
  filter_upwards [hμ.infiniteGibbsSpinMean_eq_posterior t v,
    hμ.gaussian_posterior_field_bound hbeta t v] with p heq hp
  simp only [Pi.sub_apply, Function.comp_apply]
  rw [heq]
  exact hp.2

theorem HasFreeIsingLaw.gibbsField_copy_bound_of_shared_innovation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    {F G : Filtration ℝ≥0 mΩ}
    {X X' : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hX : ∀ i, IsStronglyProgressive F (X i))
    (hX' : ∀ i, IsStronglyProgressive G (X' i))
    (t : ℝ≥0) (v : TreeVertex d)
    (hlaw : IdentDistrib (fun ω i => X i t ω) (observation t) P
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)))
    (hlaw' : IdentDistrib (fun ω i => X' i t ω) (observation t) P
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)))
    {w : Ω → ℝ}
    (hx : ∀ᵐ ω ∂P, X v t ω = w ω + nnrealTimePrimitive
      (fun s p => infiniteGibbsSpinMean beta v (fun i => X i s p)) t ω)
    (hx' : ∀ᵐ ω ∂P, X' v t ω = w ω + nnrealTimePrimitive
      (fun s p => infiniteGibbsSpinMean beta v (fun i => X' i s p)) t ω) :
    ∀ᵐ ω ∂P,
      |Real.artanh (infiniteGibbsSpinMean beta v (fun i => X i t ω)) -
        Real.artanh (infiniteGibbsSpinMean beta v (fun i => X' i t ω))| ≤
          2 * (t : ℝ) + 2 * (d : ℝ) * beta := by
  have hm := isStronglyProgressive_infiniteGibbsSpinMean F beta v X hX
  have hm' := isStronglyProgressive_infiniteGibbsSpinMean G beta v X' hX'
  have hobs := ae_observation_sub_bound_of_shared_progressive_innovation hm hm'
    (fun s => Filter.Eventually.of_forall
      (fun p => infiniteGibbsSpinMean_abs_le_one beta v _))
    (fun s => Filter.Eventually.of_forall
      (fun p => infiniteGibbsSpinMean_abs_le_one beta v _)) t hx hx'
  have hl := hμ.gibbsField_bound_of_observation_identDistrib hbeta t v hlaw
  have hr := hμ.gibbsField_bound_of_observation_identDistrib hbeta t v hlaw'
  filter_upwards [hobs, hl, hr] with ω hobsω hlω hrω
  have htriangle := abs_sub_le
    (Real.artanh (infiniteGibbsSpinMean beta v (fun i => X i t ω)))
    (X v t ω)
    (Real.artanh (infiniteGibbsSpinMean beta v (fun i => X' i t ω)))
  have htriangle' := abs_sub_le (X v t ω) (X' v t ω)
    (Real.artanh (infiniteGibbsSpinMean beta v (fun i => X' i t ω)))
  rw [abs_sub_comm (X' v t ω)] at htriangle'
  linarith

theorem HasFreeIsingLaw.gibbsField_copy_secondMoment_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    {F G : Filtration ℝ≥0 mΩ}
    {X X' : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hX : ∀ i, IsStronglyProgressive F (X i))
    (hX' : ∀ i, IsStronglyProgressive G (X' i))
    (t : ℝ≥0) (v : TreeVertex d)
    (hlaw : IdentDistrib (fun ω i => X i t ω) (observation t) P
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)))
    (hlaw' : IdentDistrib (fun ω i => X' i t ω) (observation t) P
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)))
    {w : Ω → ℝ}
    (hx : ∀ᵐ ω ∂P, X v t ω = w ω + nnrealTimePrimitive
      (fun s p => infiniteGibbsSpinMean beta v (fun i => X i s p)) t ω)
    (hx' : ∀ᵐ ω ∂P, X' v t ω = w ω + nnrealTimePrimitive
      (fun s p => infiniteGibbsSpinMean beta v (fun i => X' i s p)) t ω) :
    let U := fun ω =>
      Real.artanh (infiniteGibbsSpinMean beta v (fun i => X i t ω)) -
        Real.artanh (infiniteGibbsSpinMean beta v (fun i => X' i t ω))
    MemLp U 2 P ∧ 0 ≤ (∫ ω, (U ω) ^ 2 ∂P) ∧
      (∫ ω, (U ω) ^ 2 ∂P) ≤ (2 * (t : ℝ) + 2 * (d : ℝ) * beta) ^ 2 := by
  dsimp only
  have hb := hμ.gibbsField_copy_bound_of_shared_innovation hbeta hX hX'
    t v hlaw hlaw' hx hx'
  have ha : Measurable Real.artanh := by unfold Real.artanh; fun_prop
  have hm := isStronglyProgressive_infiniteGibbsSpinMean F beta v X hX
  have hm' := isStronglyProgressive_infiniteGibbsSpinMean G beta v X' hX'
  have hmeas := (ha.comp (((hm.stronglyAdapted t).mono (F.le t)).measurable)).sub
    (ha.comp (((hm'.stronglyAdapted t).mono (G.le t)).measurable))
  exact discrepancy_secondMoment_bounds hmeas.aestronglyMeasurable hb

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ConditionalCopyBounds
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Problem367.IsingConditionalCopyBounds

open PlantedSymmetry IsingObservationInnovation WienerSampler

theorem progressive_leftObservation {d : ℕ} (v : TreeVertex d) :
    IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration
      (fun t (q : CopySpace d) => q.2.1 v t) := by
  have had : StronglyAdapted ContinuousCopyBrownian.joinedFiltration
      (fun t (q : CopySpace d) => q.2.1 v t) := by
    intro t
    change StronglyMeasurable[ContinuousCopyBrownian.pastSpace t]
      (fun q : CopySpace d => q.2.1 v t)
    have hh : Measurable[ContinuousCopyBrownian.pastSpace t]
        (ContinuousCopyBrownian.history (ι := TreeVertex d) t) := comap_measurable _
    have hm := (continuous_eval_const t).measurable.comp
      ((measurable_pi_apply v).comp
        ((measurable_fst.comp measurable_snd).comp hh))
    simpa only [Function.comp_def, ContinuousCopyBrownian.history,
      ContinuousObservationHistory.stoppedArray,
      ContinuousObservationHistory.stoppedPath_apply, min_self] using hm.stronglyMeasurable
  exact had.isStronglyProgressive_of_continuous (fun q => (q.2.1 v).continuous)

theorem progressive_rightObservation {d : ℕ} (v : TreeVertex d) :
    IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration
      (fun t (q : CopySpace d) => q.2.2 v t) := by
  have had : StronglyAdapted ContinuousCopyBrownian.joinedFiltration
      (fun t (q : CopySpace d) => q.2.2 v t) := by
    intro t
    change StronglyMeasurable[ContinuousCopyBrownian.pastSpace t]
      (fun q : CopySpace d => q.2.2 v t)
    have hh : Measurable[ContinuousCopyBrownian.pastSpace t]
        (ContinuousCopyBrownian.history (ι := TreeVertex d) t) := comap_measurable _
    have hm := (continuous_eval_const t).measurable.comp
      ((measurable_pi_apply v).comp
        ((measurable_snd.comp measurable_snd).comp hh))
    simpa only [Function.comp_def, ContinuousCopyBrownian.history,
      ContinuousObservationHistory.stoppedArray,
      ContinuousObservationHistory.stoppedPath_apply, min_self] using hm.stronglyMeasurable
  exact had.isStronglyProgressive_of_continuous (fun q => (q.2.2 v).continuous)

section Copies

variable {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
variable {rho : Measure (Paths d)} [IsProbabilityMeasure rho]
variable {eta : Kernel (Paths d) (Paths d)} [IsMarkovKernel eta]

theorem ae_innovationMap_copies (hjoint : rho ⊗ₘ eta = graphLaw beta μ) :
    ∀ᵐ q : CopySpace d ∂rho ⊗ₘ (eta ×ₖ eta),
      innovationMap beta q.2.1 = q.1 ∧ innovationMap beta q.2.2 = q.1 := by
  have hgraph : ∀ᵐ q : Paths d × Paths d ∂rho ⊗ₘ eta,
      innovationMap beta q.2 = q.1 := by
    rw [hjoint, graphLaw]
    apply (ae_map_iff
      ((measurable_innovationMap beta).prodMk measurable_id).aemeasurable
      (measurableSet_eq_fun
        ((measurable_innovationMap beta).comp measurable_snd) measurable_fst)).mpr
    exact Filter.Eventually.of_forall (fun _ => rfl)
  have hleft := (measurePreserving_conditionalCopy_fst rho eta).quasiMeasurePreserving.ae hgraph
  have hright := (measurePreserving_conditionalCopy_snd rho eta).quasiMeasurePreserving.ae hgraph
  filter_upwards [hleft, hright] with q hl hr
  exact ⟨hl, hr⟩

theorem identDistrib_observation_copies
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (hjoint : rho ⊗ₘ eta = graphLaw beta μ) (t : ℝ≥0) :
    IdentDistrib (fun q : CopySpace d => fun i => q.2.1 i t) (observation t)
      (rho ⊗ₘ (eta ×ₖ eta)) (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ∧
    IdentDistrib (fun q : CopySpace d => fun i => q.2.2 i t) (observation t)
      (rho ⊗ₘ (eta ×ₖ eta)) (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  obtain ⟨hl, hr⟩ := measurePreserving_observation_copies hjoint
  have heval := hasLaw_observationLaw_eval μ t
  have hobs : HasLaw (observation t)
      ((μ.prod (gaussianNoiseLaw (TreeVertex d) t)).map (observation t))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
    ⟨(measurable_observation t).aemeasurable, rfl⟩
  exact ⟨(heval.comp hl.hasLaw).identDistrib hobs,
    (heval.comp hr.hasLaw).identDistrib hobs⟩

theorem ae_all_innovation_identities (hjoint : rho ⊗ₘ eta = graphLaw beta μ) :
    ∀ᵐ q : CopySpace d ∂rho ⊗ₘ (eta ×ₖ eta), ∀ v t,
      q.2.1 v t = q.1 v t + nnrealTimePrimitive
        (fun s (p : CopySpace d) => posterior beta v s p.2.1) t q ∧
      q.2.2 v t = q.1 v t + nnrealTimePrimitive
        (fun s (p : CopySpace d) => posterior beta v s p.2.2) t q := by
  filter_upwards [ae_innovationMap_copies hjoint] with q hq
  intro v t
  have hl := congrArg (fun x : Paths d => x v t) hq.1
  have hr := congrArg (fun x : Paths d => x v t) hq.2
  change q.2.1 v t - nnrealTimePrimitive
    (fun s (p : CopySpace d) => posterior beta v s p.2.1) t q = q.1 v t at hl
  change q.2.2 v t - nnrealTimePrimitive
    (fun s (p : CopySpace d) => posterior beta v s p.2.2) t q = q.1 v t at hr
  constructor <;> linarith

theorem ae_initial_observation_eq (hjoint : rho ⊗ₘ eta = graphLaw beta μ) :
    ∀ᵐ q : CopySpace d ∂rho ⊗ₘ (eta ×ₖ eta),
      (fun v => q.2.1 v 0) = (fun v => q.2.2 v 0) := by
  filter_upwards [ae_all_innovation_identities hjoint] with q hq
  funext v
  have hl := (hq v 0).1
  have hr := (hq v 0).2
  simp only [nnrealTimePrimitive, NNReal.coe_zero,
    intervalIntegral.integral_same, add_zero] at hl hr
  exact hl.trans hr.symm

theorem ae_initial_fieldDifference_zero (hjoint : rho ⊗ₘ eta = graphLaw beta μ)
    (v : TreeVertex d) :
    fieldDifference beta v 0 =ᵐ[rho ⊗ₘ (eta ×ₖ eta)] 0 := by
  filter_upwards [ae_initial_observation_eq hjoint] with q hq
  simp only [fieldDifference, IsingObservationInnovation.posterior, Pi.zero_apply]
  rw [hq, sub_self]

theorem initial_fieldDifference_secondMoment_zero
    (hjoint : rho ⊗ₘ eta = graphLaw beta μ) (v : TreeVertex d) :
    (∫ q, (fieldDifference beta v 0 q) ^ 2 ∂rho ⊗ₘ (eta ×ₖ eta)) = 0 := by
  have hzero := ae_initial_fieldDifference_zero hjoint v
  have heq : (fun q => (fieldDifference beta v 0 q) ^ 2) =ᵐ[rho ⊗ₘ (eta ×ₖ eta)]
      (fun _ => (0 : ℝ)) := hzero.mono (fun q hq => by simp [hq])
  rw [integral_congr_ae heq, integral_zero]

theorem fieldDifference_secondMoment_bounds
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (hjoint : rho ⊗ₘ eta = graphLaw beta μ) (t : ℝ≥0) (v : TreeVertex d) :
    MemLp (fieldDifference beta v t) 2 (rho ⊗ₘ (eta ×ₖ eta)) ∧
      0 ≤ (∫ q, (fieldDifference beta v t q) ^ 2 ∂rho ⊗ₘ (eta ×ₖ eta)) ∧
      (∫ q, (fieldDifference beta v t q) ^ 2 ∂rho ⊗ₘ (eta ×ₖ eta)) ≤
        (2 * (t : ℝ) + 2 * (d : ℝ) * beta) ^ 2 := by
  obtain ⟨hl, hr⟩ := identDistrib_observation_copies hμ hjoint t
  have hx := (ae_all_innovation_identities hjoint).mono (fun q hq => (hq v t).1)
  have hx' := (ae_all_innovation_identities hjoint).mono (fun q hq => (hq v t).2)
  exact hμ.gibbsField_copy_secondMoment_bounds hbeta
      progressive_leftObservation progressive_rightObservation t v hl hr hx hx'

end Copies

end Problem367.IsingConditionalCopyBounds

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ObservationComparison
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingObservationFactor

open IsingObservationInnovation

variable {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
variable [IsProbabilityMeasure μ]

theorem kernel_graphLaw :
    ((observationLaw μ).map (innovationMap beta)) ⊗ₘ kernel beta μ =
      IsingConditionalCopyBounds.graphLaw beta μ :=
  ObservableDisintegration.compProd_kernel (observationLaw μ)
    (measurable_innovationMap beta)

theorem initial_field_difference_energy (v : TreeVertex d) :
    (∫ p, (field beta v 0 p.2.1 - field beta v 0 p.2.2) ^ 2 ∂copies beta μ) = 0 := by
  have : IsProbabilityMeasure ((observationLaw μ).map (innovationMap beta)) :=
    (Measure.isProbabilityMeasure_map_iff
      (measurable_innovationMap beta).aemeasurable).mpr inferInstance
  exact IsingConditionalCopyBounds.initial_fieldDifference_secondMoment_zero
    kernel_graphLaw v

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyLinearLongBound
attribute [-simp] _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeOrbitAverage.suffixVertex_length _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.spinSign_flip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Problem367.IsingCopyResponseRowPaths
open IsingObservationFactor IsingConditionalCopyBounds ConnectedHull
open IsingRootAttenuation IsingRootDoubleExponential TreeOrbitAverage
open IsingCopyWeightedCut

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem linearEnergy_eq_root_weight (hb : 0 ≤ beta) (t : ℝ≥0) (v : TreeVertex d) :
    linearEnergy (μ := μ) hb t v =
      ∫ z, (fieldDifference beta (root d) t z) ^ 2 *
        rootAttenuation hb t v (observationCopy true z) ^ 2 ∂copies beta μ := rfl

theorem linearEnergy_le_double_exp
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (hd : 3 ≤ d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) (v : TreeVertex d) (hn : 2 ≤ v.1.length)
    {η : ℝ} (hη0 : 0 ≤ η)
    (hη : η ≤ ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) / 4)
    (hηlog : η ≤ Real.log ((d : ℝ) - 1) / 8)
    (hlength : 8 * Real.log 2 ≤
      ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) *
        (min (Real.sqrt (t : ℝ)) 1 * v.1.length)) :
    linearEnergy (μ := μ) hb t v ≤
      (∫ z, (fieldDifference beta (root d) t z) ^ 2 ∂copies beta μ) *
        Real.exp (-(η * min (Real.sqrt (t : ℝ)) 1) * v.1.length) +
      (2 * (t : ℝ) + 2 * (d : ℝ) * beta) ^ 2 *
        Real.exp (-(((d : ℝ) - 1) ^ ((v.1.length : ℝ) / 4)) /
          (2 * ((d : ℝ) - 1))) := by
  let n := v.1.length
  let k := n / 2 - 1
  let L := n - n / 2
  have hk : k + 1 = n / 2 := by dsimp [k, n]; omega
  have hsum : k + 1 + L = n := by dsimp [L]; omega
  let s : Extension ([] : List (Fin d)) (k + 1 + L) :=
    ⟨v.1, hsum.symm, by change v.1.IsChain (· ≠ ·); exact v.2⟩
  have hs : endpoint s = v := by apply Subtype.ext; rfl
  have hlevel : (n : ℝ) / 2 - 1 ≤ (k + 1 : ℕ) := by
    rw [hk]
    have hround : n ≤ 2 * (n / 2) + 1 := by omega
    have hr : (n : ℝ) ≤ 2 * (n / 2 : ℕ) + 1 := by exact_mod_cast hround
    linarith
  have htail : (n : ℝ) / 2 ≤ (L : ℝ) := by
    have hround : n ≤ 2 * L := by dsimp [L]; omega
    have hr : (n : ℝ) ≤ 2 * (L : ℝ) := by exact_mod_cast hround
    linarith
  have h := integral_root_weight_mul_sq_le_double_exp hμ hb hd hcritical ht true k L s
    hη0 (Nat.cast_nonneg n) hη hηlog hlevel htail hlength
  rw [hs, ← linearEnergy_eq_root_weight] at h
  simpa only [mul_comm (Real.exp _) (∫ z, (fieldDifference beta (root d) t z) ^ 2
    ∂copies beta μ)] using h

theorem exists_linear_energy_long_constants
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (hd : 3 ≤ d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1) :
    ∃ c a q C₀ : ℝ, 0 < c ∧ 0 < a ∧ 1 < q ∧ 0 < C₀ ∧
      ∀ (T t : ℝ≥0), 0 < t → t ≤ T → ∀ v : TreeVertex d,
        C₀ / min (Real.sqrt (t : ℝ)) 1 ≤ (v.1.length : ℝ) →
        linearEnergy (μ := μ) hb t v ≤
          (∫ z, (fieldDifference beta (root d) t z) ^ 2 ∂copies beta μ) *
            Real.exp (-(c * min (Real.sqrt (t : ℝ)) 1) * v.1.length) +
          (2 * (T : ℝ) + 2 * (d : ℝ) * beta) ^ 2 *
            Real.exp (-a * q ^ v.1.length) := by
  let b : ℝ := (d : ℝ) - 1
  have hb1 : 1 < b := by
    have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
    dsimp [b]
    linarith
  have hb0 : 0 < b := lt_trans zero_lt_one hb1
  have hθ : 0 < Real.tanh beta := by
    by_contra h
    have hz := le_antisymm (not_lt.mp h) (tanh_nonneg_of_beta_nonneg hb)
    simp [hz] at hcritical
  let γ := ComponentSignalAttenuation.lossCoefficient (Real.tanh beta)
  have hγ : 0 < γ := ComponentSignalAttenuation.lossCoefficient_pos hθ (Real.tanh_lt_one beta)
  let c := min (γ / 4) (Real.log b / 8)
  let a := 1 / (2 * b)
  let q := b ^ (1 / 4 : ℝ)
  let C₀ := max 2 (8 * Real.log 2 / γ)
  have hc : 0 < c := lt_min (div_pos hγ (by norm_num))
    (div_pos (Real.log_pos hb1) (by norm_num))
  have ha : 0 < a := by dsimp [a] <;> positivity
  have hq : 1 < q := Real.one_lt_rpow hb1 (by norm_num)
  have hC₀ : 0 < C₀ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨c, a, q, C₀, hc, ha, hq, hC₀, ?_⟩
  intro T t ht htT v hn
  let ω := min (Real.sqrt (t : ℝ)) 1
  have hω : 0 < ω := lt_min (Real.sqrt_pos.2 (show 0 < (t : ℝ) from ht)) zero_lt_one
  have hω1 : ω ≤ 1 := min_le_right _ _
  have hlarge : C₀ ≤ (v.1.length : ℝ) * ω := (div_le_iff₀ hω).mp hn
  have hnR : (2 : ℝ) ≤ v.1.length := by
    have hmul := mul_le_mul_of_nonneg_left hω1 (Nat.cast_nonneg v.1.length : (0 : ℝ) ≤ _)
    have htwo : (2 : ℝ) ≤ C₀ := le_max_left _ _
    nlinarith
  have hn2 : 2 ≤ v.1.length := by exact_mod_cast hnR
  have hlarge' : 8 * Real.log 2 / γ ≤ ω * (v.1.length : ℝ) :=
    (le_max_right _ _).trans (by simpa only [mul_comm] using hlarge)
  have hlength : 8 * Real.log 2 ≤ γ * (ω * v.1.length) := by
    have h := (div_le_iff₀ hγ).mp hlarge'
    nlinarith
  have h := linearEnergy_le_double_exp hμ hb hd hcritical ht v hn2 hc.le
    (min_le_left _ _) (min_le_right _ _) hlength
  have hpow : b ^ ((v.1.length : ℝ) / 4) = q ^ v.1.length := by
    rw [show (v.1.length : ℝ) / 4 = (1 / 4 : ℝ) * v.1.length by ring,
      Real.rpow_mul hb0.le, Real.rpow_natCast]
  have hexp : -b ^ ((v.1.length : ℝ) / 4) / (2 * b) = -a * q ^ v.1.length := by
    rw [hpow]
    dsimp [a]
    ring
  change linearEnergy (μ := μ) hb t v ≤ _ +
    (2 * (t : ℝ) + 2 * (d : ℝ) * beta) ^ 2 *
      Real.exp (-b ^ ((v.1.length : ℝ) / 4) / (2 * b)) at h
  rw [hexp] at h
  apply h.trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  apply pow_le_pow_left₀ (by positivity)
  have htTR : (t : ℝ) ≤ T := htT
  linarith

end Problem367.IsingCopyResponseRowPaths

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopySmallLogLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopySmallLogLoss

open IsingObservationInnovation IsingObservationFactor IsingCopyStationarity
open IsingCopySpectral

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem siteVariance_nonneg (o : TreeVertex d) (t : ℝ≥0) :
    0 ≤ siteVariance beta μ o t := integral_nonneg fun _ => sq_nonneg _

theorem logVariance_nonneg (hbeta : 0 ≤ beta) (v w : TreeVertex d) (t : ℝ≥0) :
    0 ≤ logVariance hbeta μ v w t := integral_nonneg fun _ => sq_nonneg _

end Problem367.IsingCopySmallLogLoss

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CriticalSmallLogLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem367.IsingCriticalSmallLogLoss

open IsingObservationInnovation IsingObservationFactor IsingCopySmallLogLoss
open IsingCopySpectral

theorem one_le_varianceScale (d : ℕ) (beta : ℝ) (T : ℝ≥0) :
    1 ≤ varianceScale d beta T := by
  unfold varianceScale
  linarith [sq_nonneg (2 * (T : ℝ) + 2 * (d : ℝ) * beta)]

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem siteVariance_zero (o : TreeVertex d) : siteVariance beta μ o 0 = 0 :=
  initial_field_difference_energy o

theorem siteVariance_le_varianceScale
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (o : TreeVertex d) {t T : ℝ≥0} (htT : t ≤ T) :
    siteVariance beta μ o t ≤ varianceScale d beta T := by
  have : IsProbabilityMeasure ((observationLaw μ).map (innovationMap beta)) := by first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply measurable_innovationMap <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have h := (IsingConditionalCopyBounds.fieldDifference_secondMoment_bounds
    hμ hbeta kernel_graphLaw t o).2.2
  have htime : (t : ℝ) ≤ T := htT
  have hb : 2 * (t : ℝ) + 2 * (d : ℝ) * beta ≤
      2 * (T : ℝ) + 2 * (d : ℝ) * beta := by linarith
  have hsq := (sq_le_sq₀ (by positivity : 0 ≤ 2 * (t : ℝ) + 2 * (d : ℝ) * beta)
    (by positivity : 0 ≤ 2 * (T : ℝ) + 2 * (d : ℝ) * beta)).2 hb
  exact h.trans (hsq.trans (by unfold varianceScale; linarith))

end Problem367.IsingCriticalSmallLogLoss

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyCriticalSpatialBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Problem367

theorem path_decay_mono {c c' ω : ℝ} (hcc : c ≤ c') (hω : 0 ≤ ω) (n : ℕ) :
    Real.exp (-(c' * ω) * n) ≤ Real.exp (-(c * ω) * n) := by
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcc hω) (Nat.cast_nonneg n : (0 : ℝ) ≤ _)
  nlinarith

theorem path_double_decay_mono {a a' q q' : ℝ}
    (ha : 0 ≤ a) (haa : a ≤ a') (hq : 0 ≤ q) (hqq : q ≤ q') (n : ℕ) :
    Real.exp (-a' * q' ^ n) ≤ Real.exp (-a * q ^ n) := by
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul haa (pow_le_pow_left₀ hq hqq n)
    (pow_nonneg hq n) (ha.trans haa)
  nlinarith

namespace IsingCopyResponseRowPaths
open IsingObservationFactor IsingConditionalCopyBounds ConnectedHull
open IsingCopySmallLogLoss IsingCriticalSmallLogLoss

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem exists_actual_spatial_endpoint_of_noise_bound
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1) (T : ℝ≥0)
    {B E c a q C₀ : ℝ} (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hc : 0 < c) (ha : 0 < a) (hq : 1 < q)
    (hnoise : ∀ (t : ℝ≥0), 0 < t → t ≤ T → ∀ (u w : TreeVertex d), treeAdj u w →
      ∀ v : TreeVertex d, C₀ / min (Real.sqrt (t : ℝ)) 1 ≤ (v.1.length : ℝ) →
        noiseEnergy (μ := μ) hb t v ≤
          B * (logVariance hb μ u w t) *
            ((v.1.length : ℝ) * Real.exp (-(c * min (Real.sqrt (t : ℝ)) 1) * v.1.length)) +
          E * ((v.1.length : ℝ) ^ 2 * Real.exp (-a * q ^ v.1.length))) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ (t : ℝ≥0), 0 < t → t ≤ T →
      ∀ (u w : TreeVertex d), treeAdj u w → 0 < siteVariance beta μ (root d) t →
      CriticalSpatialEndpointBounds
        (∫ z, IsingCopyEnergy.density beta (root d) t z ∂copies beta μ)
        (∑' n, noiseShellEnergy (μ := μ) hb t n)
        (∑' n, linearShellEnergy (μ := μ) hb t n)
        (∑' n, Real.sqrt (noiseShellEnergy (μ := μ) hb t n))
        (logVariance hb μ u w t) (siteVariance beta μ (root d) t)
        M (varianceScale d beta T) (min (Real.sqrt (t : ℝ)) 1) := by
  obtain ⟨cL, aL, qL, CL, hcL, haL, hqL, _, hlinear⟩ :=
    exists_linear_energy_long_constants hμ hb hd hcritical
  let BC := max B 1
  let EC := max E ((2 * (T : ℝ) + 2 * (d : ℝ) * beta) ^ 2)
  let cc := min c cL
  let aa := min a aL
  let qq := min q qL
  let CC := max C₀ CL
  have hBC : 0 ≤ BC := hB.trans (le_max_left _ _)
  have hEC : 0 ≤ EC := hE.trans (le_max_left _ _)
  have hcc : 0 < cc := lt_min hc hcL
  have haa : 0 < aa := lt_min ha haL
  have hqq : 1 < qq := lt_min hq hqL
  have htheta : Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1) := by
    apply (tanh_threshold_iff_branching_sq hd hb).mpr
    simpa only [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one] using hcritical.le
  obtain ⟨M, hM, hendpoint⟩ := exists_actual_spatial_endpoint_constant hμ hd hb htheta
    (C₀ := CC) hBC hEC hcc haa hqq
  refine ⟨M, hM, ?_⟩
  intro t ht htT u w huw hV
  have hω : 0 < min (Real.sqrt (t : ℝ)) 1 :=
    lt_min (Real.sqrt_pos.2 (show 0 < (t : ℝ) from ht)) zero_lt_one
  apply hendpoint t u w huw ht (varianceScale d beta T) (min (Real.sqrt (t : ℝ)) 1)
    hV (siteVariance_le_varianceScale hμ hb (root d) htT)
    (one_le_varianceScale d beta T) hω (min_le_right _ _) ?_ ?_
  · intro v hv
    have hvQ : C₀ / min (Real.sqrt (t : ℝ)) 1 ≤ (v.1.length : ℝ) :=
      (div_le_div_of_nonneg_right (le_max_left _ _) hω.le).trans hv
    have h := hnoise t ht htT u w huw v hvQ
    apply h.trans
    apply add_le_add
    · apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (logVariance_nonneg hb u w t)
      · exact mul_le_mul_of_nonneg_left (path_decay_mono (min_le_left _ _) hω.le _)
          (Nat.cast_nonneg v.1.length)
      · positivity
      · exact mul_nonneg hBC (logVariance_nonneg hb u w t)
    · apply mul_le_mul
      · exact le_max_left _ _
      · exact mul_le_mul_of_nonneg_left
          (path_double_decay_mono haa.le (min_le_left _ _)
            (zero_lt_one.trans hqq).le (min_le_left _ _) _) (sq_nonneg _)
      · positivity
      · exact hEC
  · intro v hv
    have hvL : CL / min (Real.sqrt (t : ℝ)) 1 ≤ (v.1.length : ℝ) :=
      (div_le_div_of_nonneg_right (le_max_right _ _) hω.le).trans hv
    have h := hlinear T t ht htT v hvL
    apply h.trans
    apply add_le_add
    · apply mul_le_mul
      · exact le_mul_of_one_le_left (siteVariance_nonneg (root d) t) (le_max_right _ _)
      · exact path_decay_mono (min_le_right _ _) hω.le _
      · exact (Real.exp_pos _).le
      · exact mul_nonneg hBC (siteVariance_nonneg (root d) t)
    · apply mul_le_mul
      · exact le_max_right _ _
      · exact path_double_decay_mono haa.le (min_le_right _ _)
          (zero_lt_one.trans hqq).le (min_le_right _ _) _
      · exact (Real.exp_pos _).le
      · exact hEC

end IsingCopyResponseRowPaths
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CriticalCopyEndgame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Problem367.IsingCriticalCopyEndgame

open IsingObservationFactor IsingCopySmallLogLoss IsingCriticalSmallLogLoss

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem siteVariance_eq_zero_of_spatial_endpoint_bounds
    (hd : 3 ≤ d) (hbeta : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * (Real.tanh beta) ^ 2 = 1)
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (T : ℝ≥0) (o v w : TreeVertex d) (hvw : treeAdj v w)
    {C : ℝ} (hC : 1 ≤ C) (Q L Z : ℝ → ℝ)
    (hAC : AbsolutelyContinuousOnInterval
      (fun s : ℝ => siteVariance beta μ o s.toNNReal) 0 (T : ℝ))
    (hendpoint : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) (T : ℝ)),
      0 < siteVariance beta μ o s.toNNReal →
      CriticalSpatialEndpointBounds
        (deriv (fun r : ℝ => siteVariance beta μ o r.toNNReal) s)
        (Q s) (L s) (Z s) (logVariance hbeta μ v w s.toNNReal)
        (siteVariance beta μ o s.toNNReal) C (varianceScale d beta T)
        (min (Real.sqrt s) 1)) :
    ∀ t : ℝ≥0, t ≤ T → siteVariance beta μ o t = 0 := by
  obtain ⟨c, δ, hc, hδ, hδ1, hsmall⟩ :=
    exists_critical_small_log_bounds hd hbeta hcritical
  have hupper (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (T : ℝ)) :
      siteVariance beta μ o s.toNNReal ≤ varianceScale d beta T :=
    siteVariance_le_varianceScale hμ hbeta o (Real.toNNReal_le_iff_le_coe.mpr hs.2)
  have hzero := eq_zero_of_ae_critical_spatial_endpoint_bounds
    (V := fun s : ℝ => siteVariance beta μ o s.toNNReal)
    (S := fun s : ℝ => logVariance hbeta μ v w s.toNNReal)
    (Q := Q) (L := L) (Z := Z)
    (cutoff := δ) (C := C) (H := varianceScale d beta T)
    (A := cavityLogVarianceCoefficient (Real.tanh beta))
    (B := cavityLogTailCoefficient (Real.tanh beta)
      (2 * (T : ℝ) + 2 * (d : ℝ) * beta))
    (c := c) (K := varianceScale d beta T)
    T.coe_nonneg hδ hδ1 hC (one_le_varianceScale d beta T)
    (cavityLogVarianceCoefficient_nonneg _) (cavityLogTailCoefficient_nonneg _ _)
    hc (one_le_varianceScale d beta T) hAC
    (by simpa only [Real.toNNReal_zero] using (siteVariance_zero (beta := beta) (μ := μ) o))
    (fun s _ => siteVariance_nonneg o s.toNNReal) hupper hupper hendpoint ?_
  · intro t htT
    simpa only [Real.toNNReal_coe] using hzero (t : ℝ) ⟨t.coe_nonneg, htT⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    intro hsδ _
    have he : (s.toNNReal : ℝ) = s := Real.coe_toNNReal s hs.1.le
    have hst : 0 < (s.toNNReal : ℝ) := by rw [he]; exact hs.1
    have hsd : (s.toNNReal : ℝ) ≤ δ := by rw [he]; exact hsδ
    simpa only [he] using
      (hsmall μ hμ T o v w hvw s.toNNReal hst
        (Real.toNNReal_le_iff_le_coe.mpr hs.2) hsd).1

end Problem367.IsingCriticalCopyEndgame

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CriticalSpatialRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Problem367.IsingCopyResponseRowPaths
open IsingObservationFactor IsingCopySmallLogLoss IsingCriticalSmallLogLoss
open ConnectedHull

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem exists_ae_critical_spatial_endpoint_of_noise_bound
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1) (T : ℝ≥0)
    (u w : TreeVertex d) (huw : treeAdj u w)
    {B E c a q C₀ : ℝ} (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hc : 0 < c) (ha : 0 < a) (hq : 1 < q)
    (hnoise : ∀ (t : ℝ≥0), 0 < t → t ≤ T → ∀ (u w : TreeVertex d), treeAdj u w →
      ∀ v : TreeVertex d, C₀ / min (Real.sqrt (t : ℝ)) 1 ≤ (v.1.length : ℝ) →
        noiseEnergy (μ := μ) hb t v ≤
          B * logVariance hb μ u w t *
            ((v.1.length : ℝ) * Real.exp (-(c * min (Real.sqrt (t : ℝ)) 1) * v.1.length)) +
          E * ((v.1.length : ℝ) ^ 2 * Real.exp (-a * q ^ v.1.length)))
    (hderiv : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) (T : ℝ)),
      deriv (fun r : ℝ => siteVariance beta μ (root d) r.toNNReal) s =
        ∫ z, IsingCopyEnergy.density beta (root d) s z ∂copies beta μ) :
    ∃ M : ℝ, 1 ≤ M ∧
      ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) (T : ℝ)),
      0 < siteVariance beta μ (root d) s.toNNReal →
      CriticalSpatialEndpointBounds
        (deriv (fun r : ℝ => siteVariance beta μ (root d) r.toNNReal) s)
        (∑' n, noiseShellEnergy (μ := μ) hb s.toNNReal n)
        (∑' n, linearShellEnergy (μ := μ) hb s.toNNReal n)
        (∑' n, Real.sqrt (noiseShellEnergy (μ := μ) hb s.toNNReal n))
        (logVariance hb μ u w s.toNNReal) (siteVariance beta μ (root d) s.toNNReal)
        M (varianceScale d beta T) (min (Real.sqrt s) 1) := by
  obtain ⟨M, hM, hendpoint⟩ := exists_actual_spatial_endpoint_of_noise_bound
    hμ hd hb hcritical T hB hE hc ha hq hnoise
  refine ⟨M, hM, ?_⟩
  filter_upwards [hderiv, ae_restrict_mem measurableSet_Ioc] with s hs hmem
  intro hV
  have he : (s.toNNReal : ℝ) = s := Real.coe_toNNReal s hmem.1.le
  have ht : 0 < s.toNNReal := Real.toNNReal_pos.mpr hmem.1
  have hT : s.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr hmem.2
  have h := hendpoint s.toNNReal ht hT u w huw hV
  simpa only [he, ← hs] using h

theorem critical_root_variance_zero_of_noise_bound_oai
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1) (T : ℝ≥0)
    (u w : TreeVertex d) (huw : treeAdj u w)
    {B E c a q C₀ : ℝ} (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hc : 0 < c) (ha : 0 < a) (hq : 1 < q)
    (hnoise : ∀ (t : ℝ≥0), 0 < t → t ≤ T → ∀ (u w : TreeVertex d), treeAdj u w →
      ∀ v : TreeVertex d, C₀ / min (Real.sqrt (t : ℝ)) 1 ≤ (v.1.length : ℝ) →
        noiseEnergy (μ := μ) hb t v ≤
          B * logVariance hb μ u w t *
            ((v.1.length : ℝ) * Real.exp (-(c * min (Real.sqrt (t : ℝ)) 1) * v.1.length)) +
          E * ((v.1.length : ℝ) ^ 2 * Real.exp (-a * q ^ v.1.length)))
    (hAC : AbsolutelyContinuousOnInterval
      (fun s : ℝ => siteVariance beta μ (root d) s.toNNReal) 0 (T : ℝ))
    (hderiv : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) (T : ℝ)),
      deriv (fun r : ℝ => siteVariance beta μ (root d) r.toNNReal) s =
        ∫ z, IsingCopyEnergy.density beta (root d) s z ∂copies beta μ) :
    ∀ t : ℝ≥0, t ≤ T → siteVariance beta μ (root d) t = 0 := by
  obtain ⟨M, hM, hendpoint⟩ := exists_ae_critical_spatial_endpoint_of_noise_bound
    hμ hd hb hcritical T u w huw hB hE hc ha hq hnoise hderiv
  exact IsingCriticalCopyEndgame.siteVariance_eq_zero_of_spatial_endpoint_bounds
    hd hb hcritical hμ T (root d) u w huw hM
    (fun s => ∑' n, noiseShellEnergy (μ := μ) hb s.toNNReal n)
    (fun s => ∑' n, linearShellEnergy (μ := μ) hb s.toNNReal n)
    (fun s => ∑' n, Real.sqrt (noiseShellEnergy (μ := μ) hb s.toNNReal n))
    hAC hendpoint

end Problem367.IsingCopyResponseRowPaths

end

end OAI
end

theorem solution : type_of% @OAI.Problem367.IsingCopyResponseRowPaths.critical_root_variance_zero_of_noise_bound_oai := @OAI.Problem367.IsingCopyResponseRowPaths.critical_root_variance_zero_of_noise_bound_oai
