-- Prove2me | solution 1 for OAI.CompleteCrouzeix.AdmissibleDomain.positive_ordered
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T02:35:27.024229+00:00
-- url     : https://prove2.me/submissions/590f8cd8-74d8-4d86-ad93-573a312bde53

import Mathlib
import Definitions.Def_StructuralCrouzeix
import Definitions.Def_OAIW2SC000

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_CircleIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_30 u_31 u_32 u_33 u_34

open Set Filter Metric Complex
open scoped Topology ComplexConjugate

open MeasureTheory Set Complex
open scoped Topology Real

open MeasureTheory Set Metric Complex Filter
open scoped Topology
section

lemma compact_parametric_hasDerivAt {α : Type u_31} [TopologicalSpace α]
    [CompactSpace α] [MeasurableSpace α] [BorelSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {U : Set ℂ} (hU : IsOpen U)
    {f f' : ℂ → α → ℂ}
    (hf : ContinuousOn (Function.uncurry f) (U ×ˢ univ))
    (hf' : ContinuousOn (Function.uncurry f') (U ×ˢ univ))
    (hd : ∀ z ∈ U, ∀ t, HasDerivAt (fun w => f w t) (f' z t) z)
    {z : ℂ} (hz : z ∈ U) :
    HasDerivAt (fun w => ∫ t, f w t ∂μ) (∫ t, f' z t ∂μ) z := by
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
  have hs : closedBall z (ε/2) ⊆ U := by
    exact (closedBall_subset_ball (by linarith : ε/2 < ε)).trans hεU
  obtain ⟨C,hC⟩ := (isCompact_closedBall z (ε/2)).prod isCompact_univ
    |>.exists_bound_of_continuousOn (hf'.mono (prod_mono hs (Subset.refl _)))
  have hc (w : ℂ) (hw : w ∈ U) : Continuous (f w) := by
    exact hf.comp_continuous (continuous_const.prodMk continuous_id)
      (fun t => ⟨hw,mem_univ t⟩)
  have hc' (w : ℂ) (hw : w ∈ U) : Continuous (f' w) := by
    exact hf'.comp_continuous (continuous_const.prodMk continuous_id)
      (fun t => ⟨hw,mem_univ t⟩)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := f) (F' := f') (bound := fun _ : α => C)
    (closedBall_mem_nhds z (by linarith : 0 < ε/2)) ?_ ?_ ?_ ?_ (integrable_const C) ?_).2
  · filter_upwards [hU.mem_nhds hz] with w hw
    exact (hc w hw).aestronglyMeasurable
  · exact (hc z hz).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact (hc' z hz).aestronglyMeasurable
  · filter_upwards [] with t
    intro w hw
    exact hC (w,t) ⟨hw,mem_univ t⟩
  · filter_upwards [] with t
    intro w hw
    exact hd w (hs hw) t

end

open MeasureTheory Set Metric Complex Filter
open scoped Topology


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_ExteriorProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_45

open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open MeasureTheory Set Complex
open scoped Topology Real
open MeasureTheory Set Metric Complex Filter
open scoped Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal InnerProductSpace
open scoped ComplexConjugate InnerProductSpace
open Set Metric Filter Complex
open scoped Topology

open MeasureTheory Set Complex
open scoped Topology
section

lemma interval_integral_swap_continuous {f : ℝ → ℝ → ℂ}
    (hf : ContinuousOn (Function.uncurry f) (Icc (0:ℝ) 1 ×ˢ Icc 0 1)) :
    (∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1, f s t) =
      ∫ t in (0:ℝ)..1, ∫ s in (0:ℝ)..1, f s t := by
  simp_rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc]
  apply integral_integral_swap
  rw [Measure.prod_restrict]
  exact hf.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

lemma analytic_segment_integral {U : Set ℂ} (hU : Convex ℝ U)
    {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F U) {z w : ℂ} (hz : z ∈ U) (hw : w ∈ U) :
    (∫ r in (0:ℝ)..1, (w-z) * deriv F (z + (r:ℂ)*(w-z))) = F w - F z := by
  have hm : MapsTo (fun r : ℝ => z + (r:ℂ)*(w-z)) (Icc 0 1) U := by
    intro r hr
    simpa only [Complex.real_smul] using hU.add_smul_sub_mem hz hw hr
  have hc : ContinuousOn (fun r : ℝ => (w-z) * deriv F (z+(r:ℂ)*(w-z))) (Icc 0 1) :=
    continuousOn_const.mul (hF.deriv.continuousOn.comp (by fun_prop) hm)
  have hd : ∀ r ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun r : ℝ => F (z+(r:ℂ)*(w-z)))
        ((w-z)*deriv F (z+(r:ℂ)*(w-z))) r := by
    intro r hr
    have hi := (((hasDerivAt_id r).ofReal_comp).mul_const (w-z)).const_add z
    simpa only [Function.comp_def, ofReal_one, one_mul, mul_one, id_eq, mul_comm] using
      ((hF _ (hm hr)).differentiableAt.hasDerivAt).comp r hi
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := 1)
    (fun r hr => hd r (by simpa using hr))
    (show ContinuousOn _ (uIcc (0:ℝ) 1) by simpa using hc).intervalIntegrable
  simpa using he

theorem convex_closed_curve_remainder {U : Set ℂ} (hU : Convex ℝ U)
    {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F U)
    {γ γ' : ℝ → ℂ} (hγ : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt γ (γ' t) t)
    (hγ' : ContinuousOn γ' (Icc 0 1)) (hend : γ 1 = γ 0)
    (hcurve : MapsTo γ (Icc 0 1) U) {z : ℂ} (hz : z ∈ U)
    (hne : ∀ t ∈ Icc (0:ℝ) 1, γ t ≠ z) :
    (∫ t in (0:ℝ)..1, γ' t / (γ t-z) * (F (γ t)-F z)) = 0 := by
  have hcγ : ContinuousOn γ (Icc (0:ℝ) 1) := fun t ht =>
    (hγ t ht).continuousAt.continuousWithinAt
  have hm : MapsTo (fun p : ℝ × ℝ => z+(p.2:ℂ)*(γ p.1-z))
      (Icc 0 1 ×ˢ Icc 0 1) U := by
    intro p hp
    simpa only [Complex.real_smul] using hU.add_smul_sub_mem hz (hcurve hp.1) hp.2
  have hpath : ContinuousOn (fun p : ℝ × ℝ => z+(p.2:ℂ)*(γ p.1-z))
      (Icc 0 1 ×ˢ Icc 0 1) := by
    exact continuousOn_const.add
      ((continuous_ofReal.continuousOn.comp continuousOn_snd (fun _ hp => hp.2)).mul
        ((hcγ.comp continuousOn_fst (fun _ hp => hp.1)).sub continuousOn_const))
  have hc : ContinuousOn
      (fun p : ℝ × ℝ => γ' p.1 * deriv F (z+(p.2:ℂ)*(γ p.1-z)))
      (Icc 0 1 ×ˢ Icc 0 1) :=
    (hγ'.comp continuousOn_fst (fun _ hp => hp.1)).mul
      (hF.deriv.continuousOn.comp hpath hm)
  have hinner : ∀ r ∈ Icc (0:ℝ) 1,
      (∫ t in (0:ℝ)..1, γ' t * deriv F (z+(r:ℂ)*(γ t-z))) = 0 := by
    intro r hr
    have hct : ContinuousOn (fun t => γ' t * deriv F (z+(r:ℂ)*(γ t-z))) (Icc 0 1) :=
      hc.comp (continuousOn_id.prodMk continuousOn_const) (fun t ht => ⟨ht,hr⟩)
    by_cases hr0 : r = 0
    · subst r
      simp only [ofReal_zero, zero_mul, add_zero]
      rw [intervalIntegral.integral_mul_const]
      have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := 1)
        (fun t ht => hγ t (by simpa using ht)) (show ContinuousOn _ (uIcc (0:ℝ) 1) by simpa using hγ').intervalIntegrable
      rw [hi,hend,sub_self,zero_mul]
    · have hd : ∀ t ∈ Icc (0:ℝ) 1,
          HasDerivAt (fun t => F (z+(r:ℂ)*(γ t-z)))
            ((r:ℂ)*(γ' t*deriv F (z+(r:ℂ)*(γ t-z)))) t := by
        intro t ht
        have hi : HasDerivAt (fun t => z+(r:ℂ)*(γ t-z)) ((r:ℂ)*γ' t) t :=
          (((hγ t ht).sub_const z).const_mul (r:ℂ)).const_add z
        have he := ((hF (z+(r:ℂ)*(γ t-z)) (hm (x := (t,r)) ⟨ht,hr⟩)).differentiableAt.hasDerivAt).comp t hi
        simpa only [Function.comp_def, mul_left_comm, mul_comm, mul_assoc] using he
      have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := 1)
        (fun t ht => hd t (by simpa using ht))
        (show ContinuousOn (fun t => (r:ℂ)*(γ' t*deriv F (z+(r:ℂ)*(γ t-z)))) (uIcc (0:ℝ) 1) by
          simpa using continuousOn_const.fun_mul hct).intervalIntegrable
      rw [intervalIntegral.integral_const_mul,hend,sub_self] at hi
      exact (mul_eq_zero.mp hi).resolve_left (ofReal_ne_zero.mpr hr0)
  calc
    _ = ∫ t in (0:ℝ)..1, ∫ r in (0:ℝ)..1,
        γ' t * deriv F (z+(r:ℂ)*(γ t-z)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Icc (0:ℝ) 1 := by simpa using ht
      change γ' t / (γ t-z) * (F (γ t)-F z) = _
      rw [← analytic_segment_integral hU hF hz (hcurve ht'),
        ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro r hr
      field_simp [sub_ne_zero.mpr (hne t ht')]
    _ = ∫ r in (0:ℝ)..1, ∫ t in (0:ℝ)..1,
        γ' t * deriv F (z+(r:ℂ)*(γ t-z)) := interval_integral_swap_continuous hc
    _ = ∫ r in (0:ℝ)..1, (0:ℂ) := by
      apply intervalIntegral.integral_congr
      intro r hr
      exact hinner r (by simpa using hr)
    _ = 0 := intervalIntegral.integral_zero

theorem convex_closed_curve_cauchy {U : Set ℂ} (hU : Convex ℝ U)
    {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F U)
    {γ γ' : ℝ → ℂ} (hγ : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt γ (γ' t) t)
    (hγ' : ContinuousOn γ' (Icc 0 1)) (hend : γ 1 = γ 0)
    (hcurve : MapsTo γ (Icc 0 1) U) {z : ℂ} (hz : z ∈ U)
    (hne : ∀ t ∈ Icc (0:ℝ) 1, γ t ≠ z) :
    (∫ t in (0:ℝ)..1, γ' t / (γ t-z) * F (γ t)) =
      (∫ t in (0:ℝ)..1, γ' t / (γ t-z)) * F z := by
  have hcγ : ContinuousOn γ (Icc (0:ℝ) 1) := fun t ht =>
    (hγ t ht).continuousAt.continuousWithinAt
  have hquot : ContinuousOn (fun t => γ' t / (γ t-z)) (Icc (0:ℝ) 1) :=
    hγ'.div (hcγ.sub continuousOn_const) (fun t ht => sub_ne_zero.mpr (hne t ht))
  have h1 : IntervalIntegrable (fun t => γ' t / (γ t-z) * F (γ t)) volume 0 1 :=
    (show ContinuousOn _ (uIcc (0:ℝ) 1) by
      simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1), Pi.mul_apply, Function.comp_def] using hquot.fun_mul (hF.continuousOn.comp hcγ hcurve)).intervalIntegrable
  have h2 : IntervalIntegrable (fun t => γ' t / (γ t-z) * F z) volume 0 1 :=
    (show ContinuousOn _ (uIcc (0:ℝ) 1) by
      simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1), Pi.mul_apply] using hquot.fun_mul (continuousOn_const (c := F z))).intervalIntegrable
  have he := convex_closed_curve_remainder hU hF hγ hγ' hend hcurve hz hne
  simp_rw [mul_sub] at he
  rw [intervalIntegral.integral_sub h1 h2,
    intervalIntegral.integral_mul_const] at he
  exact sub_eq_zero.mp he

end

open MeasureTheory Set Complex Metric
open scoped Topology
section

lemma reciprocalResolventDenom_ne_zero {a b : ℂ} {h : ℂ → ℂ} {z : ℂ}
    (ha : a ≠ 0) (hz : ∀ t : ℂ, 1 ≤ ‖t‖ → exteriorMap a b h t ≠ z)
    {s : ℂ} (hs : s ∈ closedBall 0 1) :
    reciprocalResolventDenom a b h z s ≠ 0 := by
  by_cases hs0 : s = 0
  · subst s; simpa [reciprocalResolventDenom] using ha
  have hsi : 1 ≤ ‖s⁻¹‖ := by
    rw [norm_inv]
    exact (one_le_inv₀ (norm_pos_iff.mpr hs0)).mpr (by simpa using hs)
  have he : reciprocalResolventDenom a b h z s = s*(exteriorMap a b h s⁻¹-z) := by
    simp only [reciprocalResolventDenom, exteriorMap, inv_inv]
    field_simp
    ring
  rw [he]
  exact mul_ne_zero hs0 (sub_ne_zero.mpr (hz _ hsi))

lemma reciprocalResolvent_analytic {a b : ℂ} {h : ℂ → ℂ} {z : ℂ}
    (ha : a ≠ 0) (hh : AnalyticOnNhd ℂ h (closedBall 0 1))
    (hz : ∀ t : ℂ, 1 ≤ ‖t‖ → exteriorMap a b h t ≠ z) :
    AnalyticOnNhd ℂ (reciprocalResolvent a b h z) (closedBall 0 1) := by
  intro s hs
  exact (analyticAt_const.sub ((analyticAt_id.pow 2).mul (hh.deriv s hs))).div
    (analyticAt_const.add (analyticAt_id.mul ((analyticAt_const.add (hh s hs)).sub
      analyticAt_const))) (reciprocalResolventDenom_ne_zero ha hz hs)

lemma reciprocalResolvent_eq {a b : ℂ} {h : ℂ → ℂ} {z t : ℂ}
    (ht : t ≠ 0) (hh : DifferentiableAt ℂ h t⁻¹) :
    reciprocalResolvent a b h z t⁻¹ =
      t*deriv (exteriorMap a b h) t / (exteriorMap a b h t-z) := by
  rw [(hasDerivAt_exteriorMap ht hh).deriv]
  simp only [reciprocalResolvent, reciprocalResolventDenom, exteriorMap]
  have he : a+t⁻¹*(b+h t⁻¹-z) = t⁻¹*(a*t+b+h t⁻¹-z) := by
    field_simp; ring
  rw [he, div_mul_eq_div_div, div_inv_eq_mul]
  congr 1
  field_simp

attribute [local instance] OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions_10
theorem exterior_cauchy_kernel_integral {a b : ℂ} {h : ℂ → ℂ} {z : ℂ}
    (ha : a ≠ 0) (hh : AnalyticOnNhd ℂ h (closedBall 0 1))
    (hz : ∀ t : ℂ, 1 ≤ ‖t‖ → exteriorMap a b h t ≠ z) :
    (∫ t : UnitAddCircle,
      (t.toCircle : ℂ)*deriv (exteriorMap a b h) (t.toCircle : ℂ) /
        (exteriorMap a b h (t.toCircle : ℂ)-z) ∂AddCircle.haarAddCircle) = 1 := by
  calc
    _ = ∫ t : UnitAddCircle, reciprocalResolvent a b h z (t.toCircle : ℂ)⁻¹
        ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [] with t
      apply (reciprocalResolvent_eq (Circle.coe_ne_zero _)
        (hh _ (by simp [mem_closedBall, dist_eq_norm, Circle.norm_coe])).differentiableAt).symm
    _ = reciprocalResolvent a b h z 0 :=
      integral_reciprocal_analytic (reciprocalResolvent_analytic ha hh hz)
    _ = 1 := by simp [reciprocalResolvent, reciprocalResolventDenom, ha]

lemma unitAddCircle_integral_eq_unitInterval {E : Type u_45}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℂ → E) :
    (∫ t : UnitAddCircle, f (t.toCircle : ℂ) ∂AddCircle.haarAddCircle) =
      ∫ r in (0:ℝ)..1, f (circleMap 0 1 (2*Real.pi*r)) := by
  rw [AddCircle.integral_haarAddCircle, ← AddCircle.intervalIntegral_preimage 1 0]
  simp only [inv_one, one_smul, zero_add]
  apply intervalIntegral.integral_congr
  intro r hr
  simp only [AddCircle.toCircle_apply_mk, Circle.coe_exp, circleMap,
    ofReal_one, one_mul, zero_add, div_one]

theorem circle_convex_cauchy {U : Set ℂ} (hU : Convex ℝ U)
    {F G : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F U)
    (hG : AnalyticOnNhd ℂ G (sphere 0 1))
    (hcurve : MapsTo G (sphere 0 1) U) {z : ℂ} (hz : z ∈ U)
    (hne : ∀ t ∈ sphere (0:ℂ) 1, G t ≠ z)
    (hmass : (∫ t : UnitAddCircle,
      (t.toCircle : ℂ)*deriv G (t.toCircle : ℂ) / (G (t.toCircle : ℂ)-z)
        ∂AddCircle.haarAddCircle) = 1) :
    (∫ t : UnitAddCircle,
      ((t.toCircle : ℂ)*deriv G (t.toCircle : ℂ) / (G (t.toCircle : ℂ)-z)) *
        F (G (t.toCircle : ℂ)) ∂AddCircle.haarAddCircle) = F z := by
  let τ : ℝ → ℂ := fun r => circleMap 0 1 (2*Real.pi*r)
  let c : ℂ := (2*Real.pi:ℝ)*I
  have hc : c ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr (mul_ne_zero (by norm_num) Real.pi_ne_zero)) I_ne_zero
  have hτ (r : ℝ) : τ r ∈ sphere (0:ℂ) 1 := by
    exact circleMap_mem_sphere 0 (by norm_num) _
  have hτc : Continuous τ := by dsimp [τ]; fun_prop
  have hτd (r : ℝ) : HasDerivAt τ (c*τ r) r := by
    have he := (hasDerivAt_circleMap 0 1 (2*Real.pi*r)).scomp r
      ((hasDerivAt_id r).const_mul (2*Real.pi))
    simpa only [Function.comp_def, id_eq, mul_one, one_mul, Complex.real_smul, τ, c,
      mul_assoc, mul_left_comm, mul_comm] using he
  have hγ (r : ℝ) : HasDerivAt (fun r => G (τ r)) (c*(τ r*deriv G (τ r))) r := by
    simpa only [Function.comp_def, mul_assoc, mul_comm, mul_left_comm] using
      ((hG _ (hτ r)).differentiableAt.hasDerivAt).comp r (hτd r)
  have hγ' : ContinuousOn (fun r => c*(τ r*deriv G (τ r))) (Icc (0:ℝ) 1) := by
    exact continuousOn_const.fun_mul (hτc.continuousOn.fun_mul
      (hG.deriv.continuousOn.comp hτc.continuousOn (fun r _ => hτ r)))
  have hend : G (τ 1) = G (τ 0) := by
    congr 1
    simpa [τ] using (periodic_circleMap 0 1) 0
  have he := convex_closed_curve_cauchy hU hF (fun r _ => hγ r) hγ' hend
    (fun r _ => hcurve (hτ r)) hz (fun r _ => hne _ (hτ r))
  have h1 : (fun r => c*(τ r*deriv G (τ r)) / (G (τ r)-z) * F (G (τ r))) =
      (fun r => c*((τ r*deriv G (τ r) / (G (τ r)-z))*F (G (τ r)))) := by
    funext r; ring
  have h2 : (fun r => c*(τ r*deriv G (τ r)) / (G (τ r)-z)) =
      (fun r => c*(τ r*deriv G (τ r) / (G (τ r)-z))) := by
    funext r; ring
  rw [h1,h2,intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at he
  erw [unitAddCircle_integral_eq_unitInterval (fun t : ℂ => t*deriv G t/(G t-z))] at hmass
  erw [unitAddCircle_integral_eq_unitInterval (fun t : ℂ => (t*deriv G t/(G t-z))*F (G t))]
  change (∫ r in (0:ℝ)..1, (τ r*deriv G (τ r) / (G (τ r)-z))*F (G (τ r))) = F z
  change (∫ r in (0:ℝ)..1, τ r*deriv G (τ r) / (G (τ r)-z)) = 1 at hmass
  rw [hmass,mul_one] at he
  exact mul_left_cancel₀ hc he

end

open Set Metric Complex MeasureTheory
open scoped Topology


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_HilbertSchmidt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_48 u_49 u_50 u_51 u_52 u_53

open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open MeasureTheory Set Complex
open scoped Topology Real
open MeasureTheory Set Metric Complex Filter
open scoped Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal InnerProductSpace
open scoped ComplexConjugate InnerProductSpace
open Set Metric Filter Complex
open scoped Topology
open MeasureTheory Set Complex
open scoped Topology
open MeasureTheory Set Complex Metric
open scoped Topology
open Set Filter Metric Complex
open scoped Topology

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

open MeasureTheory
variable {α : Type u_52} {E : Type u_53} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (B : α → E →L[ℂ] E) (hB : AEStronglyMeasurable B μ)
  (hBn : ∀ᵐ t ∂μ, ‖B t‖ ≤ 1)

lemma pointwiseL2L_norm : ‖pointwiseL2L B hB hBn‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa [pointwiseL2L] using pointwiseL2_norm B hB hBn u

lemma pointwiseL2L_adjoint (C : α → E →L[ℂ] E) (hC : AEStronglyMeasurable C μ)
    (hCn : ∀ᵐ t ∂μ, ‖C t‖ ≤ 1) (hBC : ∀ᵐ t ∂μ, (B t).adjoint = C t) :
    (pointwiseL2L B hB hBn).adjoint = pointwiseL2L C hC hCn := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro u v
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [pointwiseL2_ae C hC hCn u, pointwiseL2_ae B hB hBn v, hBC]
    with t hu hv ht
  change inner ℂ (pointwiseL2 C hC hCn u t) (v t) =
    inner ℂ (u t) (pointwiseL2 B hB hBn v t)
  rw [hu, hv, ← ht, ContinuousLinearMap.adjoint_inner_left]


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_HolomorphicEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix


universe u_61 u_62 u_63 u_64

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset
section

variable {A : Type u_61} [Ring A] [Algebra ℂ A]

lemma scalarJetEval_add {f g : ℂ → ℂ} {β : ℂ}
    (hf : AnalyticAt ℂ f β) (hg : AnalyticAt ℂ g β) (N : A) (s : ℕ) :
    scalarJetEval β N s (fun z => f z + g z) =
      scalarJetEval β N s f + scalarJetEval β N s g := by
  unfold scalarJetEval
  simp only [iteratedDeriv_fun_add hf.contDiffAt hg.contDiffAt,
    add_div, add_smul, Finset.sum_add_distrib]

lemma scalarJetEval_const {N : A} {s : ℕ} (hs : N^s = 0) (β c : ℂ) :
    scalarJetEval β N s (fun _ => c) = algebraMap ℂ A c := by
  simpa using scalarJetEval_polynomial hs β (C c)

lemma scalarJetEval_pow {f : ℂ → ℂ} {β : ℂ} (hf : AnalyticAt ℂ f β)
    {N : A} {s : ℕ} (hs : N^s = 0) (k : ℕ) :
    scalarJetEval β N s (fun z => f z ^ k) = (scalarJetEval β N s f) ^ k := by
  induction k with
  | zero => simpa using scalarJetEval_const hs β 1
  | succ k ih =>
    simp only [pow_succ]
    rw [scalarJetEval_mul (hf.fun_pow k) hf hs, ih]

lemma scalarJetEval_polynomial_comp {f : ℂ → ℂ} {β : ℂ}
    (hf : AnalyticAt ℂ f β) {N : A} {s : ℕ} (hs : N^s = 0) (p : ℂ[X]) :
    scalarJetEval β N s (fun z => p.eval (f z)) =
      Polynomial.aeval (scalarJetEval β N s f) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add, map_add]
    rw [scalarJetEval_add ((AnalyticOnNhd.eval_polynomial p (f β) (Set.mem_univ _)).fun_comp hf) ((AnalyticOnNhd.eval_polynomial q (f β) (Set.mem_univ _)).fun_comp hf), hp, hq]
  | monomial k c =>
    simp only [Polynomial.eval_monomial, Polynomial.aeval_monomial]
    rw [scalarJetEval_mul (analyticAt_const ..) (hf.fun_pow k) hs,
      scalarJetEval_const hs, scalarJetEval_pow hf hs]

lemma analytic_first_order_remainder {f : ℂ → ℂ} {β : ℂ}
    (hf : AnalyticAt ℂ f β) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R β ∧ ∀ᶠ z in nhds β,
      f z - f β = (z-β)*R z := by
  obtain ⟨R, hR, he⟩ := analytic_taylor_remainder hf 1
  refine ⟨R, hR, ?_⟩
  filter_upwards [he] with z hz
  simpa [jetPolynomial_eval, sub_eq_iff_eq_add, add_comm] using hz

lemma scalarJetEval_nilpotent_part {f : ℂ → ℂ} {β : ℂ}
    (hf : AnalyticAt ℂ f β) {N : A} {s : ℕ} (hs : N^s = 0) :
    (scalarJetEval β N s f - algebraMap ℂ A (f β)) ^ s = 0 := by
  obtain ⟨R, hR, he⟩ := analytic_first_order_remainder hf
  have hzero : scalarJetEval β N s (fun z => (f z - f β)^s) =
      scalarJetEval β N s (fun _ => (0 : ℂ)) := by
    apply scalarJetEval_eq_of_remainder (by fun_prop) (analyticAt_const ..) (hR.fun_pow s)
    filter_upwards [he] with z hz
    rw [sub_zero, hz, mul_pow]
  rw [scalarJetEval_pow (by fun_prop) hs,
    scalarJetEval_sub hf (analyticAt_const ..), scalarJetEval_const hs,
    scalarJetEval_const hs, map_zero] at hzero
  exact hzero

lemma scalarJetEval_comp {f g : ℂ → ℂ} {β : ℂ}
    (hf : AnalyticAt ℂ f β) (hg : AnalyticAt ℂ g (f β))
    {N : A} {s : ℕ} (hs : N^s = 0) :
    scalarJetEval β N s (fun z => g (f z)) =
      scalarJetEval (f β) (scalarJetEval β N s f - algebraMap ℂ A (f β)) s g := by
  let p := jetPolynomial (f β) s g
  obtain ⟨R, hR, he⟩ := analytic_taylor_remainder hg s
  obtain ⟨S, hS, hj⟩ := analytic_first_order_remainder hf
  have hRp : AnalyticAt ℂ (fun z => S z ^ s * R (f z)) β :=
    (hS.fun_pow s).fun_mul (hR.fun_comp hf)
  have hpoly : scalarJetEval β N s (fun z => g (f z)) =
      scalarJetEval β N s (fun z => p.eval (f z)) := by
    apply scalarJetEval_eq_of_remainder (hg.fun_comp hf) ((AnalyticOnNhd.eval_polynomial p (f β) (Set.mem_univ _)).fun_comp hf) hRp
    filter_upwards [hf.continuousAt.eventually he, hj] with z hz hw
    change g (f z) = p.eval (f z) + (f z-f β)^s * R (f z) at hz
    rw [hz, hw, mul_pow]
    ring
  rw [hpoly, scalarJetEval_polynomial_comp hf hs,
    scalarJetEval_taylor hg (scalarJetEval_nilpotent_part hf hs), sub_add_cancel]

end

open Module Set
open scoped DirectSum
variable {V : Type u_63} [AddCommGroup V] [Module ℂ V] [instFiniteDimensionalℂV : FiniteDimensional ℂ V]

lemma scalarJetEval_intertwine
    {V : Type u_63} [AddCommGroup V] [_root_.Module ℂ V] [FiniteDimensional ℂ V]
    {W : Type u_64} [AddCommGroup W] [Module ℂ W]
    (L : W →ₗ[ℂ] V) (S : Module.End ℂ W) (T : Module.End ℂ V)
    (h : ∀ x, T (L x) = L (S x)) (β : ℂ) (s : ℕ) (f : ℂ → ℂ) (x : W) :
    scalarJetEval β T s f (L x) = L (scalarJetEval β S s f x) := by
  have hp (k : ℕ) (x : W) : (T^k) (L x) = L ((S^k) x) := by
    induction k generalizing x with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, h,
        pow_succ', Module.End.mul_apply]
  simp only [scalarJetEval, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul, hp]

lemma primaryEval_on_generalized (T : Module.End ℂ V) (f : ℂ → ℂ)
    (β : ℂ) (x : T.maxGenEigenspace β) :
    primaryEval T f (x : V) =
      scalarJetEval β (T - algebraMap ℂ (Module.End ℂ V) β) (finrank ℂ V) f (x : V) := by
  rw [primaryEval_coe]
  exact (scalarJetEval_intertwine (T.maxGenEigenspace β).subtype
    (primaryNilpotent T β) (T - algebraMap ℂ (Module.End ℂ V) β)
    (fun _ => rfl) β (finrank ℂ V) f x).symm

lemma primaryEval_mapsTo_generalized (T : Module.End ℂ V) {f : ℂ → ℂ}
    (β : ℂ) (hf : AnalyticAt ℂ f β) :
    MapsTo (T.maxGenEigenspace β).subtype Set.univ
      ((primaryEval T f).maxGenEigenspace (f β)) := by
  intro x _
  change (x : V) ∈ (primaryEval T f).maxGenEigenspace (f β)
  rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank,
    Module.End.mem_genEigenspace_nat, LinearMap.mem_ker]
  have hp (k : ℕ) (x : T.maxGenEigenspace β) :
      ((primaryEval T f - algebraMap ℂ (Module.End ℂ V) (f β))^k) (x : V) =
        (((scalarJetEval β (primaryNilpotent T β) (finrank ℂ V) f -
          algebraMap ℂ (Module.End ℂ (T.maxGenEigenspace β)) (f β))^k) x : V) := by
    induction k generalizing x with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, LinearMap.sub_apply,
        primaryEval_coe, pow_succ', Module.End.mul_apply]
      rfl
  have he := hp (finrank ℂ V) x
  rw [scalarJetEval_nilpotent_part hf (primaryNilpotent_pow T β)] at he
  simpa only [Algebra.algebraMap_eq_smul_one,
    LinearMap.zero_apply, Submodule.coe_zero] using he

lemma primaryEval_comp (T : Module.End ℂ V) {f g : ℂ → ℂ}
    (hf : ∀ β ∈ spectrum ℂ T, AnalyticAt ℂ f β)
    (hg : ∀ β ∈ spectrum ℂ T, AnalyticAt ℂ g (f β)) :
    primaryEval T (fun z => g (f z)) = primaryEval (primaryEval T f) g := by
  apply primary_end_ext (T := T)
  intro β x
  by_cases hβ : β ∈ spectrum ℂ T
  · have hx : (x : V) ∈ (primaryEval T f).maxGenEigenspace (f β) :=
      primaryEval_mapsTo_generalized T β (hf β hβ) (by trivial : x ∈ Set.univ)
    rw [primaryEval_coe, primaryEval_on_generalized (primaryEval T f) g (f β) ⟨x, hx⟩]
    rw [scalarJetEval_comp (hf β hβ) (hg β hβ) (primaryNilpotent_pow T β)]
    symm
    apply scalarJetEval_intertwine (T.maxGenEigenspace β).subtype
    intro y
    change primaryEval T f (y : V) - (f β) • (y : V) = _
    rw [primaryEval_coe]
    rfl
  · have hspace : T.maxGenEigenspace β = ⊥ := by
      by_contra hn
      have he : T.HasGenEigenvalue β (finrank ℂ V) := by
        rwa [T.maxGenEigenspace_eq_genEigenspace_finrank β] at hn
      exact hβ (Module.End.hasEigenvalue_of_hasGenEigenvalue he).mem_spectrum
    have hx : x = 0 := by
      apply Subtype.ext
      simpa [hspace] using x.property
    simp [hx]


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_DiskCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_65 u_66 u_67 u_68 u_69 u_70 u_71 u_72 u_73 u_74 u_75 u_76 u_77 u_78 u_79 u_80

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset

section
open Filter Topology Set Module
variable {n : Type u_67} [Fintype n] [DecidableEq n]

lemma matrixAnalyticEval_polynomial (A : Matrix n n ℂ) (p : ℂ[X]) :
    matrixAnalyticEval A (fun z => p.eval z) = Polynomial.aeval A p := by
  apply Matrix.toLinAlgEquiv'.injective
  simp only [matrixAnalyticEval, AlgEquiv.apply_symm_apply, primaryEval_polynomial,
    Polynomial.aeval_algHom_apply]

end

open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder

open MeasureTheory
variable {n : Type u_73} [instFintypeN : Fintype n] [instDecidableEqN : DecidableEq n]

open scoped Kronecker

variable {m : Type u_74} [instFintypeM : Fintype m] [instDecidableEqM : DecidableEq m]

lemma matrix_integral_entry {X : Type u_75} [MeasurableSpace X] {μ : Measure X}
    {L : X → Matrix n n ℂ} (hL : Integrable L μ) (i j : n) :
    (∫ t, L t ∂μ) i j = ∫ t, L t i j ∂μ :=
  ((entryCLM i j).integral_comp_comm hL).symm

lemma continuous_kron
    {n : Type u_73} [Fintype n] [DecidableEq n] {m : Type u_74} [Fintype m] [DecidableEq m]
    {X : Type u_80} [TopologicalSpace X]
    {L : X → Matrix n n ℂ} {F : X → Matrix m m ℂ}
    (hL : Continuous L) (hF : Continuous F) : Continuous (fun t => L t ⊗ₖ F t) := by
  apply continuous_matrix
  intro i j
  exact ((entryCLM i.1 j.1).continuous.comp hL).mul
    ((entryCLM i.2 j.2).continuous.comp hF)


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_CompleteResolvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_81 u_82 u_83 u_84 u_85 u_86 u_87 u_88 u_89 u_90

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder

section
open Filter Topology Set Metric Module
open scoped Matrix.Norms.L2Operator Kronecker

variable {n : Type u_86} {m : Type u_87} [Fintype n] [DecidableEq n] [instFintypeM : Fintype m] [instDecidableEqM : DecidableEq m]

lemma matrixAnalyticEval_id (D : Matrix n n ℂ) :
    matrixAnalyticEval D (fun z => z) = D := by
  simpa using matrixAnalyticEval_polynomial D (Polynomial.X : ℂ[X])

lemma completeAnalyticEval_const
    {n : Type u_86} {m : Type u_87} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (D : Matrix n n ℂ) (C : Matrix m m ℂ) :
    completeAnalyticEval D (fun _ => C) = (1 : Matrix n n ℂ) ⊗ₖ C := by
  ext i j
  simp only [completeAnalyticEval, matrixAnalyticEval_const, Algebra.algebraMap_eq_smul_one,
    Matrix.smul_apply, smul_eq_mul, Matrix.kroneckerMap_apply]
  ring

end

open Filter Topology Set Metric Module
open scoped Matrix.Norms.L2Operator Kronecker
variable {n : Type u_89} {m : Type u_90} [Fintype n] [DecidableEq n] [instFintypeM : Fintype m] [instDecidableEqM : DecidableEq m]

lemma completeAnalyticEval_eqOn
    {n : Type u_89} {m : Type u_90} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (D : Matrix n n ℂ) {F G : ℂ → Matrix m m ℂ}
    {U : Set ℂ} (hU : IsOpen U) (hDU : spectrum ℂ D ⊆ U) (he : EqOn F G U) :
    completeAnalyticEval D F = completeAnalyticEval D G := by
  ext i j
  unfold completeAnalyticEval
  apply congrArg (fun M : Matrix n n ℂ => M i.1 j.1)
  apply matrixAnalyticEval_eventuallyEq
  intro z hz
  filter_upwards [hU.mem_nhds (hDU hz)] with w hw
  rw [he hw]

lemma matrix_entry_analytic {f : ℂ → Matrix m m ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (i j : m) : AnalyticAt ℂ (fun w => f w i j) z := by
  let L : Matrix m m ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun M => M i j, map_add' := by intros; rfl, map_smul' := by intros; rfl }
  exact (L.toContinuousLinearMap.analyticAt (f z)).comp hf


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_PolynomialCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_91 u_92 u_93 u_94 u_95 u_96 u_97 u_98 u_99 u_100 u_101 u_102 u_103 u_104 u_105 u_106 u_107

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder

section
open Filter Topology Set Metric Module
open scoped Matrix.Norms.L2Operator Kronecker
variable {n : Type u_91} [Fintype n] [DecidableEq n]

lemma kronecker_vectorize {m : Type u_95} [Fintype m] [DecidableEq m]
    (A : Matrix n n ℂ) (B : Matrix m m ℂ) (X : Matrix n m ℂ) :
    Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) (A ⊗ₖ B) (vectorize X) =
      vectorize (A*X*Bᵀ) := by
  apply PiLp.ext
  rintro ⟨i,j⟩
  change (Matrix.kronecker A B *ᵥ (fun p => X p.1 p.2)) (i,j) = (A*X*Bᵀ) i j
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  change A i l * B j k * X l k = _
  ring

end

section
open Filter Topology Set Metric Module
open scoped Matrix.Norms.L2Operator Kronecker
variable {n : Type u_96} {m : Type u_97} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

lemma matrixAnalyticEval_comp (A : Matrix n n ℂ) {f g : ℂ → ℂ}
    (hf : ∀ z ∈ spectrum ℂ A, AnalyticAt ℂ f z)
    (hg : ∀ z ∈ spectrum ℂ A, AnalyticAt ℂ g (f z)) :
    matrixAnalyticEval A (fun z => g (f z)) = matrixAnalyticEval (matrixAnalyticEval A f) g := by
  apply Matrix.toLinAlgEquiv'.injective
  simp only [matrixAnalyticEval, AlgEquiv.apply_symm_apply]
  exact primaryEval_comp _ (fun z hz => hf z (by simpa using hz))
    (fun z hz => hg z (by simpa using hz))

lemma completeAnalyticEval_comp
    {n : Type u_96} {m : Type u_97} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (A : Matrix n n ℂ) {f : ℂ → ℂ} {F : ℂ → Matrix m m ℂ}
    (hf : ∀ z ∈ spectrum ℂ A, AnalyticAt ℂ f z)
    (hF : ∀ i j, ∀ z ∈ spectrum ℂ A, AnalyticAt ℂ (fun w => F w i j) (f z)) :
    completeAnalyticEval A (fun z => F (f z)) = completeAnalyticEval (matrixAnalyticEval A f) F := by
  ext i j
  simp only [completeAnalyticEval]
  rw [matrixAnalyticEval_comp A hf (hF _ _)]

end

open Filter Topology Set Metric Module
open scoped Matrix.Norms.L2Operator Kronecker


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_CauchyEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_108 u_109 u_110 u_111 u_112 u_113 u_114 u_115

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder

section IntegralJets
open MeasureTheory Set Metric Complex Filter
open scoped Topology
variable {α : Type u_108} [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α]
  [BorelSpace α] {μ : Measure α} [IsFiniteMeasure μ]

lemma cauchyJet_hasDerivAt
    {α : Type u_108} [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α] [BorelSpace α]
    (s v : α → ℂ) (k : ℕ) {z : ℂ} {t : α}
    (hn : s t ≠ z) :
    HasDerivAt (fun w => cauchyJet s v k w t) (cauchyJet s v (k+1) z t) z := by
  have he := (hasDerivAt_const z ((k.factorial : ℂ)*v t)).div
    (((hasDerivAt_id z).const_sub (s t)).pow (k+1))
    (pow_ne_zero _ (sub_ne_zero.mpr hn))
  convert he using 1 <;> try rfl
  change ((k+1).factorial : ℂ)*v t/(s t-z)^(k+1+1) = _
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  simp only [id_eq, zero_mul, mul_neg_one, zero_sub]
  simp only [Pi.pow_apply, Nat.add_sub_cancel, pow_succ]
  field_simp

lemma cauchyJet_continuousOn
    {α : Type u_108} [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α] [BorelSpace α]
    {s v : α → ℂ} (hs : Continuous s) (hv : Continuous v)
    {U : Set ℂ} (hne : ∀ z ∈ U, ∀ t, s t ≠ z) (k : ℕ) :
    ContinuousOn (Function.uncurry (cauchyJet s v k)) (U ×ˢ univ) := by
  exact (continuous_const.mul (hv.comp continuous_snd)).continuousOn.div
    (((hs.comp continuous_snd).continuousOn.sub continuousOn_fst).pow (k+1))
    (fun p hp => pow_ne_zero _ (sub_ne_zero.mpr (hne p.1 hp.1 p.2)))

lemma cauchyJet_integrable {s v : α → ℂ} (hs : Continuous s) (hv : Continuous v)
    {z : ℂ} (hne : ∀ t, s t ≠ z) (k : ℕ) :
    Integrable (cauchyJet s v k z) μ := by
  exact ((continuous_const.mul hv).div ((hs.sub continuous_const).pow (k+1))
    (fun t => pow_ne_zero _ (sub_ne_zero.mpr (hne t)))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

lemma iteratedDeriv_cauchyIntegral {s v : α → ℂ} (hs : Continuous s) (hv : Continuous v)
    {U : Set ℂ} (hU : IsOpen U) (hne : ∀ z ∈ U, ∀ t, s t ≠ z) (k : ℕ)
    {z : ℂ} (hz : z ∈ U) :
    iteratedDeriv k (fun w => ∫ t, v t/(s t-w) ∂μ) z = ∫ t, cauchyJet s v k z t ∂μ := by
  induction k generalizing z with
  | zero => simp [cauchyJet]
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv k (fun w => ∫ t, v t/(s t-w) ∂μ) =ᶠ[nhds z]
        fun w => ∫ t, cauchyJet s v k w t ∂μ :=
      Filter.Eventually.mono (hU.mem_nhds hz) fun w hw => ih hw
    rw [he.deriv_eq]
    exact (compact_parametric_hasDerivAt hU (cauchyJet_continuousOn hs hv hne k)
      (cauchyJet_continuousOn hs hv hne (k+1))
      (fun w hw t => cauchyJet_hasDerivAt s v k (hne w hw t)) hz).deriv

lemma iteratedDeriv_cauchyKernel (s v : α → ℂ) (k : ℕ) {z : ℂ} {t : α}
    (hne : s t ≠ z) :
    iteratedDeriv k (fun w => v t/(s t-w)) z = cauchyJet s v k z t := by
  induction k generalizing z with
  | zero => simp [cauchyJet]
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv k (fun w => v t/(s t-w)) =ᶠ[nhds z]
        fun w => cauchyJet s v k w t :=
      Filter.Eventually.mono (isClosed_singleton.isOpen_compl.mem_nhds (show z ∈ ({s t} : Set ℂ)ᶜ from
        fun h => hne h.symm)) fun w hw => ih (fun h => hw h.symm)
    rw [he.deriv_eq]
    exact (cauchyJet_hasDerivAt s v k hne).deriv

end IntegralJets

section
open MeasureTheory Set Filter Module
open scoped Topology Matrix.Norms.L2Operator
variable {α : Type u_109} [MeasurableSpace α] {μ : Measure α}
  {n : Type u_110} [Fintype n] [DecidableEq n]

lemma matrix_integral_mulVec {F : α → Matrix n n ℂ} (hF : Integrable F μ) (x : n → ℂ) :
    (∫ t, F t ∂μ) *ᵥ x = ∫ t, F t *ᵥ x ∂μ := by
  let L : Matrix n n ℂ →L[ℂ] (n → ℂ) :=
    (show Matrix n n ℂ →ₗ[ℂ] (n → ℂ) from
      { toFun := fun B => B *ᵥ x
        map_add' := fun B C => Matrix.add_mulVec B C x
        map_smul' := fun c B => Matrix.smul_mulVec c B x }).toContinuousLinearMap
  exact (L.integral_comp_comm hF).symm

lemma matrixAnalyticEval_integral (A : Matrix n n ℂ) {F : ℂ → α → ℂ}
    (hi : Integrable (fun t => matrixAnalyticEval A (fun z => F z t)) μ)
    (hj : ∀ β ∈ spectrum ℂ A, ∀ k < Fintype.card n,
      Integrable (fun t => iteratedDeriv k (fun z => F z t) β) μ)
    (hd : ∀ β ∈ spectrum ℂ A, ∀ k < Fintype.card n,
      iteratedDeriv k (fun z => ∫ t, F z t ∂μ) β =
        ∫ t, iteratedDeriv k (fun z => F z t) β ∂μ) :
    matrixAnalyticEval A (fun z => ∫ t, F z t ∂μ) =
      ∫ t, matrixAnalyticEval A (fun z => F z t) ∂μ := by
  apply Matrix.toLinAlgEquiv'.injective
  apply primary_end_ext_spectrum (T := Matrix.toLinAlgEquiv' A)
  intro β hβ x
  have hb : β ∈ spectrum ℂ A := by simpa only [AlgEquiv.spectrum_eq] using hβ
  have he (f : ℂ → ℂ) :
      Matrix.toLinAlgEquiv' (matrixAnalyticEval A f) (x : n → ℂ) =
        ∑ k ∈ Finset.range (Fintype.card n),
          (iteratedDeriv k f β / (k.factorial : ℂ)) •
          (((primaryNilpotent (Matrix.toLinAlgEquiv' A) β)^k) x : n → ℂ) := by
    simp only [matrixAnalyticEval, AlgEquiv.apply_symm_apply, primaryEval_coe,
      scalarJetEval, LinearMap.sum_apply, LinearMap.smul_apply,
      Submodule.coe_sum, Submodule.coe_smul]
    simp
  rw [he, Matrix.toLinAlgEquiv'_apply, matrix_integral_mulVec hi]
  simp_rw [← Matrix.toLinAlgEquiv'_apply,he]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [hd β hb k (Finset.mem_range.mp hk),integral_smul_const,integral_div]
  · intro k hk
    exact ((hj β hb k (Finset.mem_range.mp hk)).div_const _).smul_const _

lemma matrixAnalyticEval_resolvent (A : Matrix n n ℂ) {s : ℂ}
    (hs : s ∉ spectrum ℂ A) :
    matrixAnalyticEval A (fun z => (s-z)⁻¹) = (s • (1 : Matrix n n ℂ)-A)⁻¹ := by
  have hn (z : ℂ) (hz : z ∈ spectrum ℂ A) : s-z ≠ 0 :=
    sub_ne_zero.mpr (fun h => hs (h ▸ hz))
  have hf (z : ℂ) (_ : z ∈ spectrum ℂ A) : AnalyticAt ℂ (fun z => s-z) z :=
    analyticAt_const.sub analyticAt_id
  have hg (z : ℂ) (hz : z ∈ spectrum ℂ A) : AnalyticAt ℂ (fun z => (s-z)⁻¹) z :=
    (hf z hz).inv (hn z hz)
  have he : matrixAnalyticEval A (fun _ => 1) =
      matrixAnalyticEval A (fun z => (s-z)⁻¹*(s-z)) := by
    apply matrixAnalyticEval_eventuallyEq
    intro z hz
    filter_upwards [(hf z hz).continuousAt.eventually_ne (hn z hz)] with w hw
    exact (inv_mul_cancel₀ hw).symm
  rw [matrixAnalyticEval_const, map_one, matrixAnalyticEval_mul A hg hf,
    matrixAnalyticEval_sub A (f := fun _ => s) (g := fun z => z)
      (fun _ _ => analyticAt_const) (fun _ _ => analyticAt_id),
    matrixAnalyticEval_const,matrixAnalyticEval_id,Algebra.algebraMap_eq_smul_one] at he
  exact (Matrix.inv_eq_left_inv he.symm).symm

lemma matrixAnalyticEval_cauchyKernel (A : Matrix n n ℂ) {s : ℂ}
    (hs : s ∉ spectrum ℂ A) (v : ℂ) :
    matrixAnalyticEval A (fun z => v/(s-z)) = v • (s • (1 : Matrix n n ℂ)-A)⁻¹ := by
  have hg : ∀ z ∈ spectrum ℂ A, AnalyticAt ℂ (fun z => (s-z)⁻¹) z := by
    intro z hz
    have hn : s ≠ z := fun h => hs (h ▸ hz)
    exact (analyticAt_const.sub analyticAt_id).inv (sub_ne_zero.mpr hn)
  simp_rw [div_eq_mul_inv]
  rw [matrixAnalyticEval_mul A (fun _ _ => analyticAt_const) hg,
    matrixAnalyticEval_const,matrixAnalyticEval_resolvent A hs]
  simp only [Algebra.smul_def]

end

section
open MeasureTheory Set Metric Complex Filter
open scoped Topology Matrix.Norms.L2Operator
variable {α : Type u_111} [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α]
  [BorelSpace α] {μ : Measure α} [IsFiniteMeasure μ]
  {n : Type u_112} [Fintype n] [DecidableEq n]

theorem matrix_cauchy_integral_evaluation (A : Matrix n n ℂ)
    {s v : α → ℂ} (hs : Continuous s) (hv : Continuous v)
    {U : Set ℂ} (hU : IsOpen U) (hAU : spectrum ℂ A ⊆ U)
    (hne : ∀ z ∈ U, ∀ t, s t ≠ z) :
    matrixAnalyticEval A (fun z => ∫ t, v t/(s t-z) ∂μ) =
      ∫ t, v t • (s t • (1 : Matrix n n ℂ)-A)⁻¹ ∂μ := by
  have hn (t : α) : s t ∉ spectrum ℂ A := fun h => hne _ (hAU h) t rfl
  have he (t : α) := matrixAnalyticEval_cauchyKernel A (hn t) (v t)
  have hi : Integrable (fun t => matrixAnalyticEval A (fun z => v t/(s t-z))) μ := by
    simp_rw [he]
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    apply hv.smul
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (matrix_resolvent_analytic A (hn t)).continuousAt.comp hs.continuousAt
  rw [matrixAnalyticEval_integral A hi]
  · exact integral_congr_ae (Filter.Eventually.of_forall he)
  · intro β hβ k _
    have hd : (fun t => iteratedDeriv k (fun z => v t/(s t-z)) β) = cauchyJet s v k β :=
      funext fun t => iteratedDeriv_cauchyKernel s v k (hne β (hAU hβ) t)
    rw [hd]
    exact cauchyJet_integrable hs hv (hne β (hAU hβ)) k
  · intro β hβ k _
    rw [iteratedDeriv_cauchyIntegral hs hv hU hne k (hAU hβ)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t =>
      (iteratedDeriv_cauchyKernel s v k (hne β (hAU hβ) t)).symm)

end

open MeasureTheory Set Metric Complex Filter
open scoped Topology Matrix.Norms.L2Operator Kronecker
variable {α : Type u_113} [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α]
  [BorelSpace α] {μ : Measure α} [IsFiniteMeasure μ]
  {n : Type u_114} {m : Type u_115} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

theorem complete_cauchy_integral_evaluation (A : Matrix n n ℂ)
    {s v : α → ℂ} (hs : Continuous s) (hv : Continuous v)
    {B : α → Matrix m m ℂ} (hB : Continuous B)
    {U : Set ℂ} (hU : IsOpen U) (hAU : spectrum ℂ A ⊆ U)
    (hne : ∀ z ∈ U, ∀ t, s t ≠ z) :
    completeAnalyticEval A (fun z i j => ∫ t, v t*B t i j/(s t-z) ∂μ) =
      ∫ t, (v t • (s t • (1 : Matrix n n ℂ)-A)⁻¹) ⊗ₖ B t ∂μ := by
  have hn (t : α) : s t ∉ spectrum ℂ A := fun h => hne _ (hAU h) t rfl
  have hrc := hv.smul (matrix_resolvent_continuous A hs hn)
  have hbc (i j : m) : Continuous (fun t => B t i j) := (entryCLM i j).continuous.comp hB
  have hri : Integrable (fun t => (v t • (s t • (1 : Matrix n n ℂ)-A)⁻¹) ⊗ₖ B t) μ := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    apply continuous_matrix
    intro i j
    change Continuous (fun t => (v t • (s t • (1 : Matrix n n ℂ)-A)⁻¹) i.1 j.1 * B t i.2 j.2)
    exact ((entryCLM i.1 j.1).continuous.comp hrc).mul (hbc i.2 j.2)
  ext i j
  dsimp only [completeAnalyticEval]
  have he := matrix_cauchy_integral_evaluation (μ := μ) A (s := s) (v := fun t => v t*B t i.2 j.2) hs (hv.mul (hbc i.2 j.2)) hU hAU hne
  rw [he,
    matrix_integral_entry hri]
  have ht : Integrable (fun t => (v t*B t i.2 j.2) • (s t • (1 : Matrix n n ℂ)-A)⁻¹) μ :=
    ((hv.mul (hbc i.2 j.2)).smul (matrix_resolvent_continuous A hs hn)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [matrix_integral_entry ht]
  apply integral_congr_ae
  filter_upwards [] with t
  change (v t*B t i.2 j.2) * (s t • (1 : Matrix n n ℂ)-A)⁻¹ i.1 j.1 =
    (v t*(s t • (1 : Matrix n n ℂ)-A)⁻¹ i.1 j.1)*B t i.2 j.2
  ring


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_BoundaryRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix


universe u_116 u_117 u_118 u_119 u_120 u_121 u_122 u_123 u_124 u_125 u_126 u_127 u_128 u_129 u_130 u_131 u_132 u_133 u_134 u_135 u_136 u_137 u_138 u_139 u_140 u_141 u_142 u_143 u_144 u_145 u_146 u_147 u_148 u_149 u_150 u_151 u_152 u_153

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset


open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder


open Set Filter Metric Complex
open scoped Topology ComplexConjugate

open MeasureTheory Set Complex
open scoped Topology Real

open MeasureTheory Set Complex
open scoped Topology

open MeasureTheory Set Complex Metric
open scoped Topology

section
open MeasureTheory Set Metric Complex Filter
open scoped Topology Matrix.Norms.L2Operator Kronecker MatrixOrder ComplexOrder
variable {n : Type u_150} {m : Type u_151} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

lemma boundaryDiskDensity_nonneg {D : Matrix n n ℂ} (hD : spectralRadius ℂ D < 1)
    (hc : Dᴴ*D ≤ 1) {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ boundaryDiskDensity D z := by
  let E : Matrix n n ℂ := 1-z⁻¹ • D
  let R : Matrix n n ℂ := E⁻¹
  have hu : IsUnit E := stable_disk_inverse_isUnit hD (by simp [norm_inv, hz])
  have hER : E*R = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det E).mp hu)
  have hzz : star z⁻¹ * z⁻¹ = 1 := by
    change conj z⁻¹ * z⁻¹ = 1
    rw [RCLike.conj_mul, norm_inv, hz]
    norm_num
  have hdef : Eᴴ+E-Eᴴ*E = 1-Dᴴ*D := by
    dsimp [E]
    simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,Matrix.conjTranspose_smul]
    simp only [sub_mul,mul_sub,Matrix.one_mul,Matrix.mul_one,Matrix.smul_mul,Matrix.mul_smul,
      smul_smul,mul_comm z⁻¹ (star z⁻¹),hzz,one_smul]
    abel
  have hcong : Rᴴ*(1-Dᴴ*D)*R = boundaryDiskDensity D z := by
    rw [← hdef]
    have hs := congrArg Matrix.conjTranspose hER
    simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_one] at hs
    change Rᴴ*(Eᴴ+E-Eᴴ*E)*R = R+Rᴴ-1
    calc
      _ = (Rᴴ*Eᴴ)*R + Rᴴ*(E*R) - (Rᴴ*Eᴴ)*(E*R) := by noncomm_ring
      _ = _ := by rw [hs,hER]; simp
  rw [← hcong]
  exact (Matrix.PosSemidef.conjTranspose_mul_mul_same
    (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hc)) R).nonneg

lemma coordinate_circle_cauchy {ψ H : ℂ → ℂ}
    (hψ : AnalyticOnNhd ℂ ψ (sphere 0 1))
    (hb : ∀ t ∈ sphere (0:ℂ) 1, ‖ψ t‖ = 1)
    (hH : AnalyticOnNhd ℂ H (closedBall 0 1))
    (hmass : ∀ z ∈ ball (0:ℂ) 1,
      (∫ t : UnitAddCircle, (t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ) /
        (ψ (t.toCircle : ℂ)-z) ∂AddCircle.haarAddCircle) = 1)
    {z : ℂ} (hz : z ∈ ball (0:ℂ) 1) :
    (∫ t : UnitAddCircle, ((t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ) /
      (ψ (t.toCircle : ℂ)-z))*H (ψ (t.toCircle : ℂ))
        ∂AddCircle.haarAddCircle) = H z := by
  apply circle_convex_cauchy (convex_closedBall (0:ℂ) 1) hH hψ
    (fun t ht => by simpa [mem_closedBall] using (hb t ht).le)
    (ball_subset_closedBall hz) _ (hmass z hz)
  intro t ht he
  have hh := hb t ht
  rw [he] at hh
  have hz' : ‖z‖ < 1 := by simpa using hz
  exact (ne_of_lt hz') hh

end

open MeasureTheory Set Metric Complex Filter
open scoped Topology Matrix.Norms.L2Operator Kronecker MatrixOrder ComplexOrder
variable {n : Type u_152} {m : Type u_153} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

lemma coordinate_circle_cauchy_matrix {ψ : ℂ → ℂ} {J : ℂ → Matrix n n ℂ}
    (hψ : AnalyticOnNhd ℂ ψ (sphere 0 1))
    (hb : ∀ t ∈ sphere (0:ℂ) 1, ‖ψ t‖ = 1)
    (hJ : ∀ i j, AnalyticOnNhd ℂ (fun z => J z i j) (closedBall 0 1))
    (hmass : ∀ z ∈ ball (0:ℂ) 1,
      (∫ t : UnitAddCircle, (t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ) /
        (ψ (t.toCircle : ℂ)-z) ∂AddCircle.haarAddCircle) = 1) :
    (∫ t : UnitAddCircle,
      ((t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ)/ψ (t.toCircle : ℂ)) •
        J (ψ (t.toCircle : ℂ)) ∂AddCircle.haarAddCircle) = J 0 := by
  have ht (t : UnitAddCircle) : (t.toCircle : ℂ) ∈ sphere (0:ℂ) 1 := by simp [Circle.norm_coe]
  have hc : Continuous (fun t : UnitAddCircle => (t.toCircle : ℂ)) := by fun_prop
  have hψc := hψ.continuousOn.comp_continuous hc ht
  have hψd := hψ.deriv.continuousOn.comp_continuous hc ht
  have hjc : Continuous (fun t : UnitAddCircle =>
      (t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ)/ψ (t.toCircle : ℂ)) :=
    (hc.mul hψd).div hψc (fun t => norm_ne_zero_iff.mp (by rw [hb _ (ht t)]; norm_num))
  have hJc : Continuous (fun t : UnitAddCircle => J (ψ (t.toCircle : ℂ))) := by
    apply continuous_matrix
    intro i j
    exact (hJ i j).continuousOn.comp_continuous hψc
      (fun t => by simpa [mem_closedBall] using (hb _ (ht t)).le)
  have hi := (hjc.smul hJc).integrable_of_hasCompactSupport (μ := AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  ext i j
  erw [matrix_integral_entry hi]
  convert! coordinate_circle_cauchy hψ hb (hJ i j) hmass (z := 0) (by simp) using 1
  apply integral_congr_ae
  filter_upwards [] with t
  change (t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ)/ψ (t.toCircle : ℂ) *
      J (ψ (t.toCircle : ℂ)) i j =
    (t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ)/(ψ (t.toCircle : ℂ)-0) *
      J (ψ (t.toCircle : ℂ)) i j
  rw [sub_zero]

theorem complete_pulled_disk_representation {D : Matrix n n ℂ}
    (hD : spectralRadius ℂ D < 1) {ψ : ℂ → ℂ}
    (hψ : AnalyticOnNhd ℂ ψ (sphere 0 1))
    (hb : ∀ t ∈ sphere (0:ℂ) 1, ‖ψ t‖ = 1)
    (hmass : ∀ z ∈ ball (0:ℂ) 1,
      (∫ t : UnitAddCircle, (t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ) /
        (ψ (t.toCircle : ℂ)-z) ∂AddCircle.haarAddCircle) = 1)
    {H : ℂ → Matrix m m ℂ}
    (hH : ∀ i j, AnalyticOnNhd ℂ (fun z => H z i j) (closedBall 0 1)) :
    (∫ t : UnitAddCircle,
      (((t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ)/ψ (t.toCircle : ℂ)) •
        boundaryDiskDensity D (ψ (t.toCircle : ℂ))) ⊗ₖ
          H (ψ (t.toCircle : ℂ)) ∂AddCircle.haarAddCircle) = completeAnalyticEval D H := by
  let c : UnitAddCircle → ℂ := fun t => (t.toCircle : ℂ)
  let s : UnitAddCircle → ℂ := fun t => ψ (c t)
  let v : UnitAddCircle → ℂ := fun t => c t*deriv ψ (c t)
  let j : UnitAddCircle → ℂ := fun t => v t/s t
  have ht (t : UnitAddCircle) : c t ∈ sphere (0:ℂ) 1 := by simp [c, Circle.norm_coe]
  have hc : Continuous c := by dsimp [c]; fun_prop
  have hs : Continuous s := hψ.continuousOn.comp_continuous hc ht
  have hv : Continuous v := hc.mul (hψ.deriv.continuousOn.comp_continuous hc ht)
  have hsn (t : UnitAddCircle) : s t ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [show ‖s t‖ = 1 from hb _ (ht t)]; norm_num)
  have hj : Continuous j := hv.div hs hsn
  have hsb (t : UnitAddCircle) : s t ∈ closedBall (0:ℂ) 1 := by
    simpa [mem_closedBall] using (hb _ (ht t)).le
  have hHc : Continuous (fun t => H (s t)) := by
    apply continuous_matrix
    intro a b
    exact (hH a b).continuousOn.comp_continuous hs hsb
  have hspec : spectrum ℂ D ⊆ ball (0:ℂ) 1 := fun z hz => by
    simpa using stable_spectrum_norm_lt_one hD hz
  have hne (z : ℂ) (hz : z ∈ ball (0:ℂ) 1) (t : UnitAddCircle) : s t ≠ z := by
    intro he
    have hh : ‖s t‖ = 1 := hb _ (ht t)
    rw [he] at hh
    have hz' : ‖z‖ < 1 := by simpa using hz
    exact (ne_of_lt hz') hh
  let K : UnitAddCircle → Matrix (n × m) (n × m) ℂ :=
    fun t => (v t • (s t • (1 : Matrix n n ℂ)-D)⁻¹) ⊗ₖ H (s t)
  let B : UnitAddCircle → Matrix (n × m) (n × m) ℂ :=
    fun t => j t • ((1-s t • Dᴴ)⁻¹ ⊗ₖ H (s t))
  let C : UnitAddCircle → Matrix (n × m) (n × m) ℂ :=
    fun t => j t • ((1 : Matrix n n ℂ) ⊗ₖ H (s t))
  have hKc : Continuous K := continuous_kron
    (hv.smul (matrix_resolvent_continuous D hs (fun t hz => hne _ (hspec hz) t rfl))) hHc
  have hR : AnalyticOnNhd ℂ (fun z : ℂ => (1-z • Dᴴ)⁻¹) (closedBall 0 1) := by
    intro z hz
    exact scalar_matrix_inverse_analytic (stable_star_disk_inverse_isUnit hD (by simpa using hz))
  have hBc : Continuous B := hj.smul (continuous_kron
    (hR.continuousOn.comp_continuous hs hsb) hHc)
  have hCc : Continuous C := hj.smul (continuous_kron continuous_const hHc)
  have hKi := hKc.integrable_of_hasCompactSupport (μ := AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  have hBi := hBc.integrable_of_hasCompactSupport (μ := AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  have hCi := hCc.integrable_of_hasCompactSupport (μ := AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  have hKe : (∫ t, K t ∂AddCircle.haarAddCircle) = completeAnalyticEval D H := by
    rw [← complete_cauchy_integral_evaluation D hs hv hHc isOpen_ball hspec hne]
    apply completeAnalyticEval_eqOn D isOpen_ball hspec
    intro z hz
    ext a b
    have he := coordinate_circle_cauchy hψ hb (hH a b) hmass hz
    convert he using 1
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp [v,s,c]
    ring
  have hBe : (∫ t, B t ∂AddCircle.haarAddCircle) = (1 : Matrix n n ℂ) ⊗ₖ H 0 := by
    have he := coordinate_circle_cauchy_matrix hψ hb
      (J := fun z => (1-z • Dᴴ)⁻¹ ⊗ₖ H z)
      (fun a b z hz => (matrix_entry_analytic (hR z hz) a.1 b.1).mul (hH a.2 b.2 z hz)) hmass
    simpa only [B,j,v,s,c,zero_smul,sub_zero,inv_one] using he
  have hCe : (∫ t, C t ∂AddCircle.haarAddCircle) = (1 : Matrix n n ℂ) ⊗ₖ H 0 := by
    exact coordinate_circle_cauchy_matrix hψ hb
      (J := fun z => (1 : Matrix n n ℂ) ⊗ₖ H z)
      (fun a b z hz => analyticAt_const.mul (hH a.2 b.2 z hz)) hmass
  calc
    _ = ∫ t, (K t+B t-C t) ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [boundaryDiskDensity_eq hD (hb _ (ht t))]
      change (j t • (s t • (s t • (1 : Matrix n n ℂ)-D)⁻¹ +
        (1-s t • Dᴴ)⁻¹-1)) ⊗ₖ H (s t) = K t+B t-C t
      dsimp [K,B,C,j]
      ext ⟨a₁,a₂⟩ ⟨b₁,b₂⟩
      simp only [Matrix.kronecker_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.add_apply, Matrix.sub_apply]
      field_simp [hsn t]
    _ = completeAnalyticEval D H := by
      erw [integral_sub (hKi.add hBi) hCi, integral_add hKi hBi, hKe,hBe,hCe]
      abel


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_PulledDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_154 u_155 u_156

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open MeasureTheory Set Complex
open scoped Topology Real
open MeasureTheory Set Complex
open scoped Topology
open MeasureTheory Set Complex Metric
open scoped Topology

section
open MeasureTheory Set Metric Complex Filter
open scoped Topology Matrix.Norms.L2Operator Kronecker MatrixOrder ComplexOrder
variable {n : Type u_154} [Fintype n] [DecidableEq n]

lemma pulledDiskDensity_nonneg {D : Matrix n n ℂ}
    (hD : spectralRadius ℂ D < 1) (hDc : Dᴴ*D ≤ 1) {ψ : ℂ → ℂ}
    (hb : ∀ t ∈ sphere (0:ℂ) 1, ‖ψ t‖ = 1)
    (hj : ∀ t ∈ sphere (0:ℂ) 1, 0 ≤ t*deriv ψ t/ψ t) (t : UnitAddCircle) :
    0 ≤ pulledDiskDensity D ψ t := by
  have ht : (t.toCircle : ℂ) ∈ sphere (0:ℂ) 1 := by simp [Circle.norm_coe]
  exact ((Matrix.nonneg_iff_posSemidef.mp (boundaryDiskDensity_nonneg hD hDc (hb _ ht))).smul
    (hj _ ht)).nonneg

theorem pulledDiskDensity_mass {D : Matrix n n ℂ}
    (hD : spectralRadius ℂ D < 1) {ψ : ℂ → ℂ}
    (hψ : AnalyticOnNhd ℂ ψ (sphere 0 1))
    (hb : ∀ t ∈ sphere (0:ℂ) 1, ‖ψ t‖ = 1)
    (hmass : ∀ z ∈ ball (0:ℂ) 1,
      (∫ t : UnitAddCircle, (t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ) /
        (ψ (t.toCircle : ℂ)-z) ∂AddCircle.haarAddCircle) = 1) :
    (∫ t : UnitAddCircle, pulledDiskDensity D ψ t ∂AddCircle.haarAddCircle) = 1 := by
  have he := complete_pulled_disk_representation (m := Unit) hD hψ hb hmass
    (H := fun _ => (1 : Matrix Unit Unit ℂ)) (fun _ _ _ _ => analyticAt_const)
  rw [completeAnalyticEval_const] at he
  have hc := pulledDiskDensity_continuous hD hψ hb
  have hi := hc.integrable_of_hasCompactSupport (μ := AddCircle.haarAddCircle)
    (HasCompactSupport.of_compactSpace _)
  have hkc : Continuous (fun t : UnitAddCircle =>
      (pulledDiskDensity D ψ t) ⊗ₖ (1 : Matrix Unit Unit ℂ)) :=
    continuous_kron hc continuous_const
  have hki := hkc.integrable_of_hasCompactSupport
    (μ := AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  change (∫ t : UnitAddCircle, (pulledDiskDensity D ψ t) ⊗ₖ (1 : Matrix Unit Unit ℂ)
    ∂AddCircle.haarAddCircle) = (1 : Matrix n n ℂ) ⊗ₖ (1 : Matrix Unit Unit ℂ) at he
  ext i j
  have hh := congrArg (fun M : Matrix (n × Unit) (n × Unit) ℂ => M (i,()) (j,())) he
  erw [matrix_integral_entry hki] at hh
  erw [matrix_integral_entry hi]
  simpa only [Matrix.kronecker_apply, Matrix.one_apply_eq, mul_one] using hh

end

open MeasureTheory Set Metric Complex Filter
open scoped Topology Matrix.Norms.L2Operator Kronecker MatrixOrder ComplexOrder
variable {n : Type u_155} {m : Type u_156} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

theorem interior_coordinate_exterior_representation (A : Matrix n n ℂ)
    {f g ψ G : ℂ → ℂ} {v : ℂ → Matrix m m ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hAU : spectrum ℂ A ⊆ U)
    (hf : ∀ z ∈ spectrum ℂ A, AnalyticAt ℂ f z)
    (hfd : ∀ z ∈ spectrum ℂ A, f z ∈ closedBall (0:ℂ) 1)
    (hg : AnalyticOnNhd ℂ g (closedBall 0 1))
    (hgf : ∀ z ∈ U, g (f z) = z)
    (hv : AnalyticOnNhd ℂ v (g '' closedBall 0 1))
    (hD : spectralRadius ℂ (matrixAnalyticEval A f) < 1)
    (hψ : AnalyticOnNhd ℂ ψ (sphere 0 1))
    (hb : ∀ t ∈ sphere (0:ℂ) 1, ‖ψ t‖ = 1)
    (hgb : ∀ t ∈ sphere (0:ℂ) 1, g (ψ t) = G t)
    (hmass : ∀ z ∈ ball (0:ℂ) 1,
      (∫ t : UnitAddCircle, (t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ) /
        (ψ (t.toCircle : ℂ)-z) ∂AddCircle.haarAddCircle) = 1) :
    completeAnalyticEval A v =
      ∫ t : UnitAddCircle, pulledDiskDensity (matrixAnalyticEval A f) ψ t ⊗ₖ
        v (G (t.toCircle : ℂ)) ∂AddCircle.haarAddCircle := by
  have hvg : AnalyticOnNhd ℂ (fun z => v (g z)) (closedBall 0 1) := by
    intro z hz
    exact (hv (g z) ⟨z,hz,rfl⟩).comp (hg z hz)
  have he : completeAnalyticEval A v =
      completeAnalyticEval (matrixAnalyticEval A f) (fun z => v (g z)) := by
    rw [← completeAnalyticEval_comp A hf
      (F := fun z => v (g z)) (fun i j z hz => matrix_entry_analytic (hvg (f z) (hfd z hz)) i j)]
    apply completeAnalyticEval_eqOn A hU hAU
    intro z hz
    change v z = v (g (f z))
    rw [hgf z hz]
  rw [he, ← complete_pulled_disk_representation hD hψ hb hmass
    (fun i j z hz => matrix_entry_analytic (hvg z hz) i j)]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [hgb _ (by simp [Circle.norm_coe])]
  rfl


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_DilationDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix


universe u_191 u_192 u_193 u_194 u_195 u_196 u_197 u_198 u_199 u_200 u_201 u_202 u_203 u_204 u_205 u_206 u_207 u_208 u_209 u_210 u_211 u_212 u_213 u_214

open MeasureTheory
open scoped ENNReal

section
variable {T : Type u_193} {H : Type u_194} [TopologicalSpace T] [CompactSpace T] [SecondCountableTopology T]
  [MeasurableSpace T] [BorelSpace T] {μ : Measure T} [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section MatrixDensity
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Kronecker
variable {n : Type u_195} {m : Type u_196} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

lemma baseAmplification_mul (A B : Matrix n n ℂ) :
    baseAmplification (m := m) (A*B) = baseAmplification A * baseAmplification B := by
  change Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) ((A*B) ⊗ₖ (1 : Matrix m m ℂ)) =
    Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) (A ⊗ₖ (1 : Matrix m m ℂ)) * Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) (B ⊗ₖ 1)
  rw [← map_mul, ← Matrix.mul_kronecker_mul, one_mul]

lemma baseAmplification_star (A : Matrix n n ℂ) :
    baseAmplification (m := m) Aᴴ = (baseAmplification A).adjoint := by
  change Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) (Aᴴ ⊗ₖ (1 : Matrix m m ℂ)) =
    star (Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) (A ⊗ₖ (1 : Matrix m m ℂ)))
  have he := map_star (Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ))
    (A ⊗ₖ (1 : Matrix m m ℂ))
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one] using he

lemma densityRootField_sq
    {T : Type u_193} [TopologicalSpace T] [CompactSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T] {n : Type u_195} {m : Type u_196} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m] (L : C(T,Matrix n n ℂ)) (hL : ∀ t, 0 ≤ L t) (t : T) :
    (densityRootField (m := m) L hL t).adjoint * densityRootField L hL t =
      baseAmplification (L t) := by
  change (baseAmplification (n := n) (m := m) (CFC.sqrt (L t))).adjoint *
    baseAmplification (n := n) (m := m) (CFC.sqrt (L t)) = baseAmplification (n := n) (m := m) (L t)
  rw [← baseAmplification_star, ← baseAmplification_mul]
  have hs : (CFC.sqrt (L t))ᴴ = CFC.sqrt (L t) :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (L t))).isHermitian.eq
  rw [hs, CFC.sqrt_mul_sqrt_self (L t) (hL t)]

lemma densityRootField_mass (L : C(T,Matrix n n ℂ)) (hL : ∀ t, 0 ≤ L t)
    (hmass : (∫ t, L t ∂μ) = 1) :
    (∫ t, (densityRootField (m := m) L hL t).adjoint * densityRootField L hL t ∂μ) = 1 := by
  simp_rw [densityRootField_sq]
  have hi : Integrable (fun t => L t) μ :=
    L.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have : CompleteSpace (EuclideanSpace ℂ (n × m)) := inferInstance
  have : CompleteSpace (EuclideanSpace ℂ (n × m) →L[ℂ] EuclideanSpace ℂ (n × m)) :=
    ContinuousLinearMap.instCompleteSpace
  rw [(baseAmplification (n := n) (m := m)).integral_comp_comm hi,
    hmass, baseAmplification_one]

end MatrixDensity

theorem positiveDilation_compression (S B : C(T,H →L[ℂ] H))
    (hmass : (∫ t, (S t).adjoint * S t ∂μ) = 1) (hB : ∀ t, ‖B t‖ ≤ 1) :
    let V := (positiveDilation S hmass).toContinuousLinearMap
    V.adjoint.comp ((pointwiseL2L (fun t => B t) B.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall hB)).comp V) =
        ∫ t, (S t).adjoint * B t * S t ∂μ := by
  dsimp only
  let V := (positiveDilation S hmass).toContinuousLinearMap
  let M := pointwiseL2L (μ := μ) (fun t => B t) B.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall hB)
  have hi : Integrable (fun t => (S t).adjoint * B t * S t) μ :=
    (show Continuous (fun t => (S t).adjoint * B t * S t) by fun_prop
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  change inner ℂ x (V.adjoint (M (V y))) =
    inner ℂ x ((∫ t, (S t).adjoint * B t * S t ∂μ) y)
  rw [ContinuousLinearMap.adjoint_inner_right, L2.inner_def]
  calc
    _ = ∫ t, inner ℂ (S t x) (B t (S t y)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [dilationLM_coe (μ := μ) S x, dilationLM_coe (μ := μ) S y,
        pointwiseL2_ae (fun t => B t) B.continuous.aestronglyMeasurable
          (Filter.Eventually.of_forall hB) (V y)] with t hx hy hM
      change inner ℂ ((dilationLM S x) t) ((pointwiseL2 (fun t => B t) B.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall hB) (V y)) t) = _
      rw [hx, hM]
      change inner ℂ (S t x) (B t ((dilationLM S y) t)) = _
      rw [hy]
    _ = ∫ t, inner ℂ x (((S t).adjoint * B t * S t) y) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [mul_apply_eq_comp, ContinuousLinearMap.adjoint_inner_right]
    _ = _ := by
      have hiy : Integrable (fun t => ((S t).adjoint * B t * S t) y) μ :=
        (ContinuousLinearMap.apply ℂ H y).integrable_comp hi
      rw [integral_inner hiy, ← ContinuousLinearMap.integral_apply hi]

end

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Kronecker

section
variable {n : Type u_197} {m : Type u_198} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

lemma coefficientMatrixHom_norm (B : Matrix m m ℂ) :
    ‖coefficientMatrixHom (n := n) B‖ ≤ ‖B‖ :=
  NonUnitalStarAlgHom.norm_apply_le (coefficientMatrixHom (n := n)) B

lemma coefficientAmplification_norm (B : Matrix m m ℂ) :
    ‖coefficientAmplification (n := n) B‖ ≤ ‖B‖ :=
  coefficientMatrixHom_norm B

lemma coefficientAmplification_star (B : Matrix m m ℂ) :
    coefficientAmplification (n := n) Bᴴ = (coefficientAmplification B).adjoint := by
  change Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) ((1 : Matrix n n ℂ) ⊗ₖ Bᴴ) =
    star (Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) ((1 : Matrix n n ℂ) ⊗ₖ B))
  have he := map_star (Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ))
    ((1 : Matrix n n ℂ) ⊗ₖ B)
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one] using he

end

section
open MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Kronecker
variable {T : Type u_199} [TopologicalSpace T] [CompactSpace T] [SecondCountableTopology T]
  [MeasurableSpace T] [BorelSpace T] {μ : Measure T} [IsFiniteMeasure μ]
  {n : Type u_200} {m : Type u_201} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

lemma coefficientMultiplierField_norm
    {T : Type u_199} [TopologicalSpace T] [CompactSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T] {n : Type u_200} {m : Type u_201} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m] (F : C(T,Matrix m m ℂ)) (hF : ∀ t, ‖F t‖ ≤ 1)
    (t : T) : ‖coefficientMultiplierField (n := n) F t‖ ≤ 1 :=
  (coefficientAmplification_norm (n := n) (F t)).trans (hF t)

lemma densityRootField_compression
    {T : Type u_199} [TopologicalSpace T] [CompactSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T] {n : Type u_200} {m : Type u_201} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m] (L : C(T,Matrix n n ℂ)) (hL : ∀ t, 0 ≤ L t)
    (F : C(T,Matrix m m ℂ)) (t : T) :
    (densityRootField (m := m) L hL t).adjoint * coefficientMultiplierField F t *
      densityRootField L hL t =
        Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) (L t ⊗ₖ F t) := by
  change (baseAmplification (n := n) (m := m) (CFC.sqrt (L t))).adjoint *
    coefficientAmplification (n := n) (F t) *
    baseAmplification (n := n) (m := m) (CFC.sqrt (L t)) = _
  rw [← baseAmplification_star]
  change Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) ((CFC.sqrt (L t))ᴴ ⊗ₖ (1 : Matrix m m ℂ)) *
    Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) ((1 : Matrix n n ℂ) ⊗ₖ F t) *
    Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) (CFC.sqrt (L t) ⊗ₖ (1 : Matrix m m ℂ)) = _
  rw [← map_mul, ← map_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp only [Matrix.mul_one, Matrix.one_mul]
  have hs : (CFC.sqrt (L t))ᴴ = CFC.sqrt (L t) :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (L t))).isHermitian.eq
  rw [hs, CFC.sqrt_mul_sqrt_self (L t) (hL t)]

end

section
variable {H : Type u_202} {K : Type u_203} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem isometric_multiplier_saturation (V : H →ₗᵢ[ℂ] K) (M : K →L[ℂ] K)
    (hM : ‖M‖ ≤ 1) {x y : H} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (he : V.toContinuousLinearMap.adjoint (M (V x)) = y) :
    M (V x) = V y ∧ M.adjoint (V y) = V x := by
  have hMy : M (V x) = V y := by
    apply eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := ℂ)
    · calc ‖M (V x)‖ ≤ ‖M‖ * ‖V x‖ := M.le_opNorm _
           _ ≤ ‖V y‖ := by rw [V.norm_map, V.norm_map, hx, hy, mul_one]; exact hM
    · change RCLike.re (inner ℂ (M (V x)) (V.toContinuousLinearMap y)) = _
      rw [← ContinuousLinearMap.adjoint_inner_left, he, inner_self_eq_norm_sq_to_K]
      simp [V.norm_map, hy]
  refine ⟨hMy, ?_⟩
  apply eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := ℂ)
  · calc ‖M.adjoint (V y)‖ ≤ ‖M.adjoint‖ * ‖V y‖ := M.adjoint.le_opNorm _
         _ ≤ ‖V x‖ := by
           rw [ContinuousLinearMap.adjoint.norm_map, V.norm_map, V.norm_map, hx, hy, mul_one]
           exact hM
  · rw [ContinuousLinearMap.adjoint_inner_left, hMy, inner_self_eq_norm_sq_to_K]
    simp [V.norm_map, hx, hy]

end

section
open MeasureTheory
variable {T : Type u_204} {H : Type u_205} [TopologicalSpace T] [CompactSpace T] [SecondCountableTopology T]
  [MeasurableSpace T] [BorelSpace T] {μ : Measure T} [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem positiveDilation_saturation (S B : C(T,H →L[ℂ] H))
    (hmass : (∫ t, (S t).adjoint * S t ∂μ) = 1) (hB : ∀ t, ‖B t‖ ≤ 1)
    {x y : H} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (he : (∫ t, (S t).adjoint * B t * S t ∂μ) x = y) :
    ∀ᵐ t ∂μ, B t (S t x) = S t y ∧ (B t).adjoint (S t y) = S t x := by
  let hBn : ∀ᵐ t ∂μ, ‖B t‖ ≤ 1 := Filter.Eventually.of_forall hB
  let M := pointwiseL2L (fun t => B t) B.continuous.aestronglyMeasurable hBn
  let V := positiveDilation S hmass
  have hcomp := positiveDilation_compression (μ := μ) S B hmass hB
  have hv : V.toContinuousLinearMap.adjoint (M (V x)) = y := by
    have hh := congrArg (fun f : H →L[ℂ] H => f x) hcomp
    exact hh.trans he
  obtain ⟨hforward,hback⟩ := isometric_multiplier_saturation V M
    (pointwiseL2L_norm _ _ _) hx hy hv
  have hC : Continuous (fun t => (B t).adjoint) := by fun_prop
  have hCn : ∀ᵐ t ∂μ, ‖(B t).adjoint‖ ≤ 1 := by
    filter_upwards [] with t
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact hB t
  have hadj := pointwiseL2L_adjoint (fun t => B t) B.continuous.aestronglyMeasurable hBn
    (fun t => (B t).adjoint) hC.aestronglyMeasurable hCn (Filter.Eventually.of_forall fun _ => rfl)
  have hback' : pointwiseL2L (fun t => (B t).adjoint) hC.aestronglyMeasurable hCn (V y) = V x := by
    rw [← hadj]
    exact hback
  have hfae : M (V x) =ᵐ[μ] V y := by rw [hforward]
  have hbae : pointwiseL2L (fun t => (B t).adjoint) hC.aestronglyMeasurable hCn (V y) =ᵐ[μ] V x := by rw [hback']
  filter_upwards [hfae, hbae, dilationLM_coe (μ := μ) S x,
    dilationLM_coe (μ := μ) S y,
    pointwiseL2_ae (fun t => B t) B.continuous.aestronglyMeasurable hBn (V x),
    pointwiseL2_ae (fun t => (B t).adjoint) hC.aestronglyMeasurable hCn (V y)]
    with t hf hb hxt hyt hmt hmat
  change (V x) t = S t x at hxt
  change (V y) t = S t y at hyt
  change (M (V x)) t = B t ((V x) t) at hmt
  change (pointwiseL2L (fun t => (B t).adjoint) hC.aestronglyMeasurable hCn (V y)) t =
    (B t).adjoint ((V y) t) at hmat
  exact ⟨by rwa [hmt, hxt, hyt] at hf, by rwa [hmat, hyt, hxt] at hb⟩
end

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
section
variable {n : Type u_206} {m : Type u_207} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

lemma weightedDensity_of_sqrt
    {n : Type u_206} {m : Type u_207} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    {L S : Matrix n n ℂ} (hS : Sᴴ*S = L)
    (X Y : Matrix n m ℂ) :
    weightedDensity L X Y = weightedDensity 1 (S*X) (S*Y) := by
  simp only [weightedDensity, Matrix.conjTranspose_mul, Matrix.mul_one]
  rw [← hS]
  congr 1
  simp only [Matrix.mul_assoc]

lemma weightedDensity_right
    {n : Type u_206} {m : Type u_207} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (L : Matrix n n ℂ) (X Y : Matrix n m ℂ)
    (F : Matrix m m ℂ) :
    weightedDensity L X (Y*Fᵀ) = F*weightedDensity L X Y := by
  simp only [weightedDensity, ← Matrix.mul_assoc, Matrix.transpose_mul,
    Matrix.transpose_transpose]

lemma weightedDensity_left
    {n : Type u_206} {m : Type u_207} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (L : Matrix n n ℂ) (X Y : Matrix n m ℂ)
    (F : Matrix m m ℂ) :
    weightedDensity L (X*Fᵀ) Y = weightedDensity L X Y * Fᴴ := by
  simp only [weightedDensity, Matrix.conjTranspose_mul, Matrix.transpose_mul,
    Matrix.conjTranspose_transpose_eq_transpose_conjTranspose, Matrix.transpose_transpose, Matrix.mul_assoc]

lemma weightedDensity_ordered_products (X Y : Matrix n m ℂ) (F : Matrix m m ℂ)
    (hY : Y = X*Fᵀ) (hX : X = Y*(Fᴴ)ᵀ) :
    weightedDensity 1 X X = Fᴴ*weightedDensity 1 X Y ∧
    weightedDensity 1 X Y = F*weightedDensity 1 X X ∧
    weightedDensity 1 Y Y = weightedDensity 1 X Y*Fᴴ := by
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ = weightedDensity 1 X (Y*(Fᴴ)ᵀ) := congrArg (weightedDensity 1 X) hX
      _ = _ := weightedDensity_right 1 X Y Fᴴ
  · calc
      _ = weightedDensity 1 X (X*Fᵀ) := congrArg (weightedDensity 1 X) hY
      _ = _ := weightedDensity_right 1 X X F
  · calc
      _ = weightedDensity 1 (X*Fᵀ) Y := congrArg (fun Z => weightedDensity 1 Z Y) hY
      _ = _ := weightedDensity_left 1 X Y F

end

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
variable {T : Type u_212} [TopologicalSpace T] [CompactSpace T] [SecondCountableTopology T]
  [MeasurableSpace T] [BorelSpace T] {μ : Measure T} [IsFiniteMeasure μ]
  {n : Type u_213} {m : Type u_214} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

lemma vectorize_injective
    {n : Type u_213} {m : Type u_214} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] :
    Function.Injective (vectorize (n := n) (m := m)) := by
  intro X Y h
  ext i j
  exact congrArg (fun v : EuclideanSpace ℂ (n × m) => v (i,j)) h

theorem actual_density_ordered (L : C(T,Matrix n n ℂ)) (hL : ∀ t, 0 ≤ L t)
    (hmass : (∫ t, L t ∂μ) = 1)
    (F : C(T,Matrix m m ℂ)) (hF : ∀ t, ‖F t‖ ≤ 1)
    {X Y : Matrix n m ℂ} (hx : ‖vectorize X‖ = 1) (hy : ‖vectorize Y‖ = 1)
    (he : (∫ t, Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) (L t ⊗ₖ F t) ∂μ)
      (vectorize X) = vectorize Y) :
    ∀ᵐ t ∂μ,
      weightedDensity (L t) X X = (F t)ᴴ * weightedDensity (L t) X Y ∧
      weightedDensity (L t) X Y = F t * weightedDensity (L t) X X ∧
      weightedDensity (L t) Y Y = weightedDensity (L t) X Y * (F t)ᴴ := by
  have he' : (∫ t, (densityRootField (m := m) L hL t).adjoint *
      coefficientMultiplierField (n := n) F t * densityRootField (m := m) L hL t ∂μ)
      (vectorize X) = vectorize Y := by
    simpa only [densityRootField_compression] using he
  have ha := positiveDilation_saturation (μ := μ) (densityRootField (m := m) L hL)
    (coefficientMultiplierField (n := n) F) (densityRootField_mass L hL hmass)
    (coefficientMultiplierField_norm F hF) hx hy he'
  filter_upwards [ha] with t ht
  let S : Matrix n n ℂ := CFC.sqrt (L t)
  have hs : Sᴴ*S = L t := by
    have hh : Sᴴ = S := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (L t))).isHermitian.eq
    rw [hh]
    exact CFC.sqrt_mul_sqrt_self (L t) (hL t)
  have hroot (Z : Matrix n m ℂ) : densityRootField (m := m) L hL t (vectorize Z) =
      vectorize (S*Z) := by
    change Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) (S ⊗ₖ (1 : Matrix m m ℂ)) (vectorize Z) = _
    rw [kronecker_vectorize]
    simp only [Matrix.transpose_one, Matrix.mul_one]
  have hcoeff (B : Matrix m m ℂ) (Z : Matrix n m ℂ) :
      coefficientAmplification (n := n) B (vectorize Z) = vectorize (Z*Bᵀ) := by
    change Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) ((1 : Matrix n n ℂ) ⊗ₖ B) (vectorize Z) = _
    rw [kronecker_vectorize, Matrix.one_mul]
  have hY : S*Y = (S*X)*(F t)ᵀ := by
    apply vectorize_injective
    have hh := ht.1
    change coefficientAmplification (n := n) (F t) (densityRootField L hL t (vectorize X)) =
      densityRootField L hL t (vectorize Y) at hh
    rw [hroot, hroot, hcoeff] at hh
    exact hh.symm
  have hX : S*X = (S*Y)*((F t)ᴴ)ᵀ := by
    apply vectorize_injective
    have hh := ht.2
    change (coefficientAmplification (n := n) (F t)).adjoint
      (densityRootField L hL t (vectorize Y)) = densityRootField L hL t (vectorize X) at hh
    rw [← coefficientAmplification_star, hroot, hroot, hcoeff] at hh
    exact hh.symm
  simpa only [← weightedDensity_of_sqrt hs] using
    weightedDensity_ordered_products (S*X) (S*Y) (F t) hY hX


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_ConformalJacobian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open Set Filter Metric Complex
open scoped Topology ComplexConjugate InnerProductSpace
namespace CompleteCrouzeix

lemma circle_log_derivative_real {ψ : ℂ → ℂ} {t : ℂ}
    (ht : ‖t‖ = 1) (hψ : DifferentiableAt ℂ ψ t)
    (hb : ∀ z : ℂ, ‖z‖ = 1 → ‖ψ z‖ = 1) :
    (t*deriv ψ t/ψ t).im = 0 := by
  have hp : ‖ψ t‖ = 1 := hb t ht
  have hd (s : ℝ) : HasDerivAt (fun s : ℝ => exp ((s:ℂ)*I)*t)
      (exp ((s:ℂ)*I)*I*t) s := by
    simpa using (((hasDerivAt_id s).ofReal_comp.mul_const I).cexp.mul_const t)
  have he : HasDerivAt (fun s : ℝ => ψ (exp ((s:ℂ)*I)*t))
      (I*t*deriv ψ t) 0 := by
    simpa only [ofReal_zero, zero_mul, exp_zero, one_mul, Function.comp_def,
      smul_eq_mul] using (show HasDerivAt ψ (deriv ψ t) (exp (((0:ℝ):ℂ)*I)*t) from by simpa using hψ.hasDerivAt).scomp 0 (hd 0)
  have hn : (fun s : ℝ => ‖ψ (exp ((s:ℂ)*I)*t)‖^2) = fun _ => (1:ℝ) := by
    funext s
    rw [hb _ (by rw [norm_mul, norm_exp_ofReal_mul_I, ht, one_mul]), one_pow]
  have heq := he.norm_sq
  rw [hn] at heq
  have hz := heq.unique (hasDerivAt_const (0:ℝ) (1:ℝ))
  have hi : inner ℝ (ψ t) (I*t*deriv ψ t) = -(conj (ψ t)*(t*deriv ψ t)).im := by
    rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply']
    change (conj (ψ t)*(I*t*deriv ψ t)).re = _
    rw [show conj (ψ t)*(I*t*deriv ψ t) = I*(conj (ψ t)*(t*deriv ψ t)) by ring]
    simp
  simp only [ofReal_zero, zero_mul, exp_zero, one_mul] at hz
  rw [hi] at hz
  have hconj : (ψ t)⁻¹ = conj (ψ t) := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hp]
    simp
  rw [div_eq_mul_inv, hconj, mul_comm (t*deriv ψ t)]
  linarith

lemma circle_log_derivative_nonneg {ψ : ℂ → ℂ} {t : ℂ}
    (_ht : ‖t‖ = 1) (hψ : DifferentiableAt ℂ ψ t)
    (hb : ‖ψ t‖ = 1)
    (hin : ∀ᶠ r : ℝ in 𝓝[Iic 1] 1, ‖ψ ((r:ℂ)*t)‖ ≤ 1) :
    0 ≤ (t*deriv ψ t/ψ t).re := by
  have hd : HasDerivAt (fun r : ℝ => (r:ℂ)*t) t 1 := by
    simpa using (hasDerivAt_id (1:ℝ)).ofReal_comp.mul_const t
  have he : HasDerivAt (fun r : ℝ => ψ ((r:ℂ)*t)) (t*deriv ψ t) 1 := by
    simpa only [ofReal_one, one_mul, Function.comp_def, smul_eq_mul] using
      (show HasDerivAt ψ (deriv ψ t) (((1:ℝ):ℂ)*t) from by simpa using hψ.hasDerivAt).scomp 1 hd
  have hm : IsLocalMaxOn (fun r : ℝ => ‖ψ ((r:ℂ)*t)‖^2) (Iic 1) 1 := by
    filter_upwards [hin] with r hr
    simpa only [ofReal_one, one_mul, hb, one_pow] using
      (pow_le_pow_left₀ (norm_nonneg _) hr 2)
  have hy : (-1:ℝ) ∈ posTangentConeAt (Iic (1:ℝ)) 1 := by
    apply mem_posTangentConeAt_of_segment_subset
    apply (convex_Iic (1:ℝ)).segment_subset <;> simp
  have hh := hm.hasFDerivWithinAt_nonpos he.norm_sq.hasFDerivAt.hasFDerivWithinAt hy
  simp only [ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, ofReal_one, one_mul] at hh
  have hi : inner ℝ (ψ t) (t*deriv ψ t) = (conj (ψ t)*(t*deriv ψ t)).re := by
    rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply']; rfl
  rw [hi] at hh
  have hconj : (ψ t)⁻¹ = conj (ψ t) := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hb]
    simp
  rw [div_eq_mul_inv, hconj, mul_comm (t*deriv ψ t)]
  linarith

end CompleteCrouzeix

end

end
end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_ConformalWinding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix


open Set Filter Metric Complex
open scoped Topology ComplexConjugate

open MeasureTheory Set Complex
open scoped Topology Real

open MeasureTheory Set Complex
open scoped Topology

open MeasureTheory Set Complex Metric
open scoped Topology

attribute [local instance] OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions_54
lemma circle_convex_integral_zero {K : Set ℂ} (hK : Convex ℝ K)
    {J G : ℂ → ℂ} (hJ : AnalyticOnNhd ℂ J K)
    (hG : AnalyticOnNhd ℂ G (sphere 0 1))
    (hcurve : MapsTo G (sphere 0 1) K) {a : ℂ} (ha : a ∈ K)
    (hne : ∀ t ∈ sphere (0:ℂ) 1, G t ≠ a)
    (hmass : (∫ t : UnitAddCircle,
      (t.toCircle : ℂ)*deriv G (t.toCircle : ℂ) / (G (t.toCircle : ℂ)-a)
        ∂AddCircle.haarAddCircle) = 1) :
    (∫ t : UnitAddCircle, (t.toCircle : ℂ)*deriv G (t.toCircle : ℂ)*
      J (G (t.toCircle : ℂ)) ∂AddCircle.haarAddCircle) = 0 := by
  have hF : AnalyticOnNhd ℂ (fun z => (z-a)*J z) K := by
    intro z hz; exact (analyticAt_id.sub analyticAt_const).mul (hJ z hz)
  have he := circle_convex_cauchy hK hF hG hcurve ha hne hmass
  simpa only [sub_self, zero_mul] using
    (show (∫ t : UnitAddCircle,
      (t.toCircle : ℂ)*deriv G (t.toCircle : ℂ)*J (G (t.toCircle : ℂ))
        ∂AddCircle.haarAddCircle) = (a-a)*J a from by
      calc
        _ = ∫ t : UnitAddCircle,
          ((t.toCircle : ℂ)*deriv G (t.toCircle : ℂ)/(G (t.toCircle : ℂ)-a))*
            ((G (t.toCircle : ℂ)-a)*J (G (t.toCircle : ℂ)))
              ∂AddCircle.haarAddCircle := by
          apply integral_congr_ae
          filter_upwards [] with t
          have ht : (t.toCircle : ℂ) ∈ sphere (0:ℂ) 1 := by
            simp [Circle.norm_coe]
          field_simp [sub_ne_zero.mpr (hne _ ht)]
        _ = _ := he)

lemma logarithmic_dslope_derivative {f : ℂ → ℂ} {a z : ℂ}
    (hfa : f z ≠ f a) (hza : z ≠ a) (hf : DifferentiableAt ℂ f z) :
    deriv f z / (f z-f a) = 1/(z-a) + deriv (dslope f a) z / dslope f a z := by
  have hd : deriv (dslope f a) z =
      (deriv f z*(z-a)-(f z-f a))/(z-a)^2 := by
    rw [(dslope_eventuallyEq_slope_of_ne f hza).deriv_eq]
    rw [show slope f a = (fun w => (f w-f a)/(w-a)) from
      funext (fun w => slope_def_field f a w)]
    simpa only [Pi.div_apply, id_eq, mul_one] using
      ((hf.hasDerivAt.sub_const (f a)).fun_div
        ((hasDerivAt_id z).sub_const a) (sub_ne_zero.mpr hza)).deriv
  rw [hd, dslope_of_ne _ hza, slope_def_field]
  field_simp
  ring

theorem conformal_circle_mass {K V : Set ℂ} (hK : Convex ℝ K)
    (hV : IsOpen V) (hKV : K ⊆ V) {f G : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f V) (hfi : InjOn f V)
    (hG : AnalyticOnNhd ℂ G (sphere 0 1))
    (hcurve : MapsTo G (sphere 0 1) K) {a : ℂ} (ha : a ∈ K)
    (hfa : deriv f a ≠ 0)
    (hne : ∀ t ∈ sphere (0:ℂ) 1, G t ≠ a)
    (hmass : (∫ t : UnitAddCircle,
      (t.toCircle : ℂ)*deriv G (t.toCircle : ℂ) / (G (t.toCircle : ℂ)-a)
        ∂AddCircle.haarAddCircle) = 1) :
    (∫ t : UnitAddCircle,
      (t.toCircle : ℂ)*deriv (f ∘ G) (t.toCircle : ℂ) /
        (f (G (t.toCircle : ℂ))-f a) ∂AddCircle.haarAddCircle) = 1 := by
  let J : ℂ → ℂ := fun z => deriv (dslope f a) z / dslope f a z
  have hq := analyticOnNhd_dslope hV hf (hKV ha)
  have hJ : AnalyticOnNhd ℂ J K := by
    intro z hz
    exact (hq.deriv z (hKV hz)).div (hq z (hKV hz))
      (dslope_ne_zero_of_injOn hfi (hKV ha) (hKV hz) hfa)
  have hz := circle_convex_integral_zero hK hJ hG hcurve ha hne hmass
  have ht (t : UnitAddCircle) : (t.toCircle : ℂ) ∈ sphere (0:ℂ) 1 := by
    simp [Circle.norm_coe]
  have htc : Continuous (fun t : UnitAddCircle => (t.toCircle : ℂ)) :=
    by fun_prop
  have hgc : Continuous (fun t : UnitAddCircle => G (t.toCircle : ℂ)) :=
    hG.continuousOn.comp_continuous htc ht
  have hdgc : Continuous (fun t : UnitAddCircle => deriv G (t.toCircle : ℂ)) :=
    hG.deriv.continuousOn.comp_continuous htc ht
  have h₁ : Integrable (fun t : UnitAddCircle =>
      (t.toCircle : ℂ)*deriv G (t.toCircle : ℂ)/(G (t.toCircle : ℂ)-a))
        AddCircle.haarAddCircle :=
    ((htc.mul hdgc).div (hgc.sub continuous_const)
      (fun t => sub_ne_zero.mpr (hne _ (ht t)))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h₂ : Integrable (fun t : UnitAddCircle =>
      (t.toCircle : ℂ)*deriv G (t.toCircle : ℂ)*J (G (t.toCircle : ℂ)))
        AddCircle.haarAddCircle :=
    ((htc.mul hdgc).mul
      (hJ.continuousOn.comp_continuous hgc (fun t => hcurve (ht t)))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    _ = ∫ t : UnitAddCircle,
      ((t.toCircle : ℂ)*deriv G (t.toCircle : ℂ)/(G (t.toCircle : ℂ)-a) +
        (t.toCircle : ℂ)*deriv G (t.toCircle : ℂ)*J (G (t.toCircle : ℂ)))
          ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [] with t
      have he : f (G (t.toCircle : ℂ)) ≠ f a :=
        fun he => hne _ (ht t) (hfi (hKV (hcurve (ht t))) (hKV ha) he)
      rw [deriv_comp _ (hf _ (hKV (hcurve (ht t)))).differentiableAt
        (hG _ (ht t)).differentiableAt]
      have heq := logarithmic_dslope_derivative he (hne _ (ht t))
        (hf _ (hKV (hcurve (ht t)))).differentiableAt
      change _ = _ + _*J _
      dsimp [J]
      linear_combination ((t.toCircle : ℂ)*deriv G (t.toCircle : ℂ))*heq
    _ = 1 := by rw [integral_add h₁ h₂, hmass, hz, add_zero]


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_DomainCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_244

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
namespace AdmissibleDomain
variable (D : AdmissibleDomain)
lemma inverse_ψ {t : ℂ} (ht : t ∈ sphere (0:ℂ) 1) : D.interior.fromDisk (D.ψ t) = D.G t :=
  D.interior.left_inverse _ (D.interior.closure_subset (D.G_boundary ht).1)
lemma ψ_jacobian {t : ℂ} (ht : t ∈ sphere (0:ℂ) 1) :
    0 ≤ t*deriv D.ψ t/D.ψ t := by
  rw [Complex.nonneg_iff]
  refine ⟨circle_log_derivative_nonneg (mem_sphere_zero_iff_norm.mp ht)
    (D.ψ_analytic t ht).differentiableAt (D.ψ_boundary ht) ?_,
    (circle_log_derivative_real (mem_sphere_zero_iff_norm.mp ht)
    (D.ψ_analytic t ht).differentiableAt (fun z hz => D.ψ_boundary (mem_sphere_zero_iff_norm.mpr hz))).symm⟩
  have hi : D.exterior.radius⁻¹ < 1 := inv_lt_one_of_one_lt₀ D.exterior.radius_gt
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (lt_mem_nhds hi)] with r hr hri
  have hr0 : 0 < r := (inv_pos.mpr (zero_lt_one.trans D.exterior.radius_gt)).trans hri
  have hnorm : ‖(r:ℂ)*t‖ = r := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr0,mem_sphere_zero_iff_norm.mp ht,mul_one]
  change ‖D.interior.toDisk (D.G ((r:ℂ)*t))‖ ≤ 1
  apply mem_closedBall_zero_iff.mp (D.interior.closure_maps _)
  rcases lt_or_eq_of_le (show r ≤ 1 from hr) with hlt|rfl
  · exact subset_closure ((D.exterior.interior_iff _ (by simpa only [hnorm] using hri)).mpr
      (mem_ball_zero_iff.mpr (by simpa only [hnorm] using hlt)))
  · simpa only [ofReal_one,one_mul] using (D.G_boundary ht).1
lemma G_mass {z : ℂ} (hz : z ∈ D.domain) :
    (∫ t : UnitAddCircle, (t.toCircle : ℂ)*deriv D.G (t.toCircle : ℂ) /
      (D.G (t.toCircle : ℂ)-z) ∂AddCircle.haarAddCircle) = 1 := by
  apply exterior_cauchy_kernel_integral D.exterior.leading_ne
    (D.exterior.analytic_regular.mono (closedBall_subset_ball D.exterior.radius_gt))
  intro t ht
  exact D.G_ne_interior hz ht
lemma ψ_mass {z : ℂ} (hz : z ∈ ball (0:ℂ) 1) :
    (∫ t : UnitAddCircle, (t.toCircle : ℂ)*deriv D.ψ (t.toCircle : ℂ) /
      (D.ψ (t.toCircle : ℂ)-z) ∂AddCircle.haarAddCircle) = 1 := by
  have ha := D.interior.inverse_ball z hz
  have hfa := D.interior.right_inverse z (D.interior.closedDisk_subset (ball_subset_closedBall hz))
  have hm := conformal_circle_mass D.convex.closure D.interior.outer_open
    D.interior.closure_subset D.interior.analytic_to D.interior.injective_to D.G_analytic
    (fun t ht => (D.G_boundary ht).1) (subset_closure ha)
    (D.interior.noncritical_to _ (D.interior.closure_subset (subset_closure ha)))
    (fun t ht => D.G_ne_interior ha (mem_sphere_zero_iff_norm.mp ht).ge) (D.G_mass ha)
  simpa only [hfa,ψ,Function.comp_apply] using hm
end AdmissibleDomain

end CompleteCrouzeix

end

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_BoundaryCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_245 u_246

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
namespace AdmissibleDomain
variable (D : AdmissibleDomain)
variable {n : Type u_245} {m : Type u_246} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
attribute [local instance] OAI.CompleteCrouzeix.AdmissibleDomain.instFactLtRealOfNat
lemma positive_representation [Nonempty n] (A : Matrix n n ℂ)
    (hA : spectrum ℂ A ⊆ D.domain) {v : ℂ → Matrix m m ℂ}
    (hv : AnalyticOnNhd ℂ v (closure D.domain)) :
    completeAnalyticEval A v = ∫ t : UnitAddCircle,
      pulledDiskDensity (matrixAnalyticEval A D.interior.toDisk) D.ψ t ⊗ₖ
        D.trace v hv t ∂AddCircle.haarAddCircle := by
  have hf (z : ℂ) (hz : z ∈ spectrum ℂ A) :=
    D.interior.analytic_to z (D.interior.closure_subset (subset_closure (hA hz)))
  apply interior_coordinate_exterior_representation A D.isOpen hA hf
    (fun z hz => ball_subset_closedBall (D.toDisk_maps (hA hz)))
    (D.interior.analytic_from.mono D.interior.closedDisk_subset)
    (fun z hz => D.interior.left_inverse z (D.interior.closure_subset (subset_closure hz)))
    (hv.mono (by rintro z ⟨w,hw,rfl⟩; exact D.interior.inverse_closed w hw))
    (matrixAnalyticEval_stable A hf (fun z hz => mem_ball_zero_iff.mp (D.toDisk_maps (hA hz))))
    D.ψ_analytic (fun _ ht => D.ψ_boundary ht) (fun _ ht => D.inverse_ψ ht) (fun _ hz => D.ψ_mass hz)
end AdmissibleDomain
end CompleteCrouzeix

end

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_PositiveDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u_253 u_254

namespace CompleteCrouzeix
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace AdmissibleDomain

section
variable (D : AdmissibleDomain)
variable {n : Type u_253} {m : Type u_254} [Fintype n] [DecidableEq n] [Nonempty n] [Fintype m] [DecidableEq m]
lemma positiveDensity_nonneg (A : Matrix n n ℂ) (hA : spectrum ℂ A ⊆ D.domain)
    (hc : (matrixAnalyticEval A D.interior.toDisk)ᴴ * matrixAnalyticEval A D.interior.toDisk ≤ 1)
    (t : UnitAddCircle) : 0 ≤ D.positiveDensity A hA t :=
  pulledDiskDensity_nonneg (D.coordinate_stable A hA) hc
    (fun _ ht => D.ψ_boundary ht) (fun _ ht => D.ψ_jacobian ht) t
attribute [local instance] OAI.CompleteCrouzeix.AdmissibleDomain.instFactLtRealOfNat_2
lemma positiveDensity_mass (A : Matrix n n ℂ) (hA : spectrum ℂ A ⊆ D.domain) :
    (∫ t, D.positiveDensity A hA t ∂AddCircle.haarAddCircle) = 1 :=
  pulledDiskDensity_mass (D.coordinate_stable A hA) D.ψ_analytic
    (fun _ ht => D.ψ_boundary ht) (fun _ hz => D.ψ_mass hz)
lemma positiveDensity_representation (A : Matrix n n ℂ) (hA : spectrum ℂ A ⊆ D.domain)
    {v : ℂ → Matrix m m ℂ} (hv : AnalyticOnNhd ℂ v (closure D.domain)) :
    completeAnalyticEval A v = ∫ t, D.positiveDensity A hA t ⊗ₖ D.trace v hv t
      ∂AddCircle.haarAddCircle := D.positive_representation A hA hv
lemma positiveDensity_operator_representation (A : Matrix n n ℂ) (hA : spectrum ℂ A ⊆ D.domain)
    {v : ℂ → Matrix m m ℂ} (hv : AnalyticOnNhd ℂ v (closure D.domain)) :
    Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) (completeAnalyticEval A v) =
      ∫ t, Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ)
        (D.positiveDensity A hA t ⊗ₖ D.trace v hv t) ∂AddCircle.haarAddCircle := by
  let e : Matrix (n × m) (n × m) ℂ →L[ℂ] _ :=
    (Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ)).toAlgEquiv.toLinearMap.toContinuousLinearMap
  have hi := (continuous_kron (D.positiveDensity A hA).continuous (D.trace v hv).continuous).integrable_of_hasCompactSupport
    (μ := AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  rw [D.positiveDensity_representation A hA hv]
  have : CompleteSpace (EuclideanSpace ℂ (n × m)) := inferInstance
  have : CompleteSpace (EuclideanSpace ℂ (n × m) →L[ℂ] EuclideanSpace ℂ (n × m)) :=
    ContinuousLinearMap.instCompleteSpace
  exact (e.integral_comp_comm hi).symm
end
end AdmissibleDomain
end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_OrderedDensities
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_255 u_256

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
variable {n : Type u_255} {m : Type u_256} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
namespace AdmissibleDomain
variable (D : AdmissibleDomain)
attribute [local instance] OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions_56
lemma positive_ordered_oai [Nonempty n] (A : Matrix n n ℂ) (hA : spectrum ℂ A ⊆ D.domain)
    (hc : (matrixAnalyticEval A D.interior.toDisk)ᴴ * matrixAnalyticEval A D.interior.toDisk ≤ 1)
    {F : ℂ → Matrix m m ℂ} (hF : AnalyticOnNhd ℂ F (closure D.domain))
    (hn : ∀ z ∈ closure D.domain, ‖F z‖ ≤ 1)
    {X Y : Matrix n m ℂ} (hx : ‖vectorize X‖ = 1) (hy : ‖vectorize Y‖ = 1)
    (he : Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) (completeAnalyticEval A F)
      (vectorize X) = vectorize Y) :
    ∀ᵐ t ∂AddCircle.haarAddCircle,
      weightedDensity (D.positiveDensity A hA t) X X = (D.trace F hF t)ᴴ * weightedDensity (D.positiveDensity A hA t) X Y ∧
      weightedDensity (D.positiveDensity A hA t) X Y = D.trace F hF t * weightedDensity (D.positiveDensity A hA t) X X ∧
      weightedDensity (D.positiveDensity A hA t) Y Y = weightedDensity (D.positiveDensity A hA t) X Y * (D.trace F hF t)ᴴ := by
  apply actual_density_ordered (D.positiveDensity A hA) (D.positiveDensity_nonneg A hA hc)
    (D.positiveDensity_mass A hA) (D.trace F hF)
    (fun t => hn _ (D.G_boundary (by simp [Circle.norm_coe])).1) hx hy
  rw [← D.positiveDensity_operator_representation A hA hF]
  exact he
end AdmissibleDomain
end CompleteCrouzeix

end

end

end OAI
end

theorem solution.{u_255, u_256} : type_of% @OAI.CompleteCrouzeix.AdmissibleDomain.positive_ordered_oai.{u_255, u_256} := @OAI.CompleteCrouzeix.AdmissibleDomain.positive_ordered_oai.{u_255, u_256}
