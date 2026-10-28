-- Prove2me | solution 1 for OAI.CompleteCrouzeix.AdmissibleDomain.ordered_modules
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T02:35:01.792782+00:00
-- url     : https://prove2.me/submissions/13fff269-595d-4bbf-bf84-44fb75f6404e

import Mathlib
import Definitions.Def_StructuralCrouzeix
import Definitions.Def_OAIW2SC000

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_ConformalGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_1 u_2

open Complex Metric Set Filter Real
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology

open Set Filter Metric Complex
open scoped Topology
section

theorem analytic_open_gluing {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g V)
    (he : EqOn f g (U ∩ V)) :
    ∃ q : ℂ → ℂ, AnalyticOnNhd ℂ q (U ∪ V) ∧ EqOn q f U ∧ EqOn q g V := by
  classical
  let q := fun z => if z ∈ U then f z else g z
  have hqf : EqOn q f U := fun _ hz => ite_eq_left hz
  have hqg : EqOn q g V := by
    intro z hz
    dsimp [q]
    split_ifs with hi
    · exact he ⟨hi,hz⟩
    · rfl
  refine ⟨q,?_,hqf,hqg⟩
  intro z hz
  rcases hz with hz | hz
  · apply (hf z hz).congr
    filter_upwards [hU.mem_nhds hz] with w hw
    exact (hqf hw).symm
  · apply (hg z hz).congr
    filter_upwards [hV.mem_nhds hz] with w hw
    exact (hqg hw).symm

theorem noncritical_holomorphic_inverse {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U) (hinj : InjOn f U)
    (hd : ∀ z ∈ U, deriv f z ≠ 0) :
    IsOpen (f '' U) ∧ ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (f '' U) ∧
      MapsTo g (f '' U) U ∧ (∀ z ∈ U, g (f z) = z) ∧
      (∀ w ∈ f '' U, f (g w) = w) := by
  classical
  have hopen : ∀ s ⊆ U, IsOpen s → IsOpen (f '' s) := by
    intro s hsU hs
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨z,hz,rfl⟩
    rw [← (hf z (hsU hz)).hasStrictDerivAt.map_nhds_eq (hd z (hsU hz))]
    exact image_mem_map (hs.mem_nhds hz)
  let e₀ := hinj.toPartialEquiv f U
  have ho : IsOpenMap (e₀.source.domRestrict e₀) := by
    intro s hs
    have hsub : (Subtype.val '' s : Set ℂ) ⊆ U := by
      rintro _ ⟨z,hz,rfl⟩
      exact z.property
    have hh := hopen (Subtype.val '' s) hsub (hU.isOpenMap_subtype_val s hs)
    convert hh using 1
    exact (Set.image_image f Subtype.val s).symm
  let e : OpenPartialHomeomorph ℂ ℂ :=
    OpenPartialHomeomorph.ofContinuousOpenRestrict e₀ hf.continuousOn ho hU
  have hg : AnalyticOnNhd ℂ (e.symm : ℂ → ℂ) e.target := by
    apply DifferentiableOn.analyticOnNhd _ e.open_target
    intro w hw
    have hz := e.map_target hw
    have hi := (hf (e.symm w) hz).hasStrictDerivAt.to_local_left_inverse
      (hd _ hz) (e.eventually_left_inverse hz)
    have hew : f (e.symm w) = w := e.right_inv hw
    rw [hew] at hi
    exact hi.hasDerivAt.differentiableAt.differentiableWithinAt
  exact ⟨hopen U Subset.rfl hU,e.symm,hg,e.symm.mapsTo,(fun z hz => e.left_inv hz),(fun w hw => e.right_inv hw)⟩


open Set Filter Metric Complex
open scoped Topology

end

open Set Filter Metric Complex
open scoped Topology

open Set Metric Filter Topology


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_ExteriorKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
namespace CompleteCrouzeix

theorem exteriorCorrection_analytic_right {G : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hG : AnalyticOnNhd ℂ G U) (hi : InjOn G U)
    (hd : ∀ w ∈ U, deriv G w ≠ 0) {w : ℂ} (hw : w ∈ U) :
    AnalyticOnNhd ℂ (exteriorCorrection G w) U := by
  have hq := analyticOnNhd_dslope hU hG hw
  intro t ht
  exact (analyticAt_id.mul (hq.deriv t ht)).div (hq t ht)
    (dslope_ne_zero_of_injOn hi hw ht (hd w hw))

end CompleteCrouzeix
end
end
end

end OAI
end

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
section

lemma fourier_natCast_toCircle (n : ℕ) (t : UnitAddCircle) :
    fourier (n : ℤ) t = (t.toCircle : ℂ)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, fourier_add, ih, fourier_one, pow_succ]

lemma fourier_neg_natCast_toCircle (n : ℕ) (t : UnitAddCircle) :
    fourier (-(n : ℤ)) t = ((t.toCircle : ℂ)⁻¹)^n := by
  rw [fourier_neg, fourier_natCast_toCircle, map_pow]
  congr 1
  exact (Circle.coe_inv_eq_conj t.toCircle).symm.trans (Circle.coe_inv t.toCircle)

attribute [local instance] OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions
lemma integral_analytic_mul_pow {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 1)) {n : ℕ} (hn : n ≠ 0) :
    (∫ t : UnitAddCircle, (t.toCircle : ℂ)^n * f (t.toCircle : ℂ)
      ∂AddCircle.haarAddCircle) = 0 := by
  simpa only [Pi.mul_apply, Pi.pow_apply, id_eq, zero_pow hn, zero_mul] using
    integral_analytic_circle ((analyticOnNhd_id.pow n).mul hf)

lemma integral_reciprocal_analytic_mul_inv_pow {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 1)) {n : ℕ} (hn : n ≠ 0) :
    (∫ t : UnitAddCircle, ((t.toCircle : ℂ)⁻¹)^n * f (t.toCircle : ℂ)⁻¹
      ∂AddCircle.haarAddCircle) = 0 := by
  rw [unitAddCircle_integral_eq_circleAverage
      (fun z => (z⁻¹)^n * f z⁻¹)]
  rw [Real.circleAverage_zero_one_congr_inv
      (f := fun z => z^n*f z)]
  rw [← unitAddCircle_integral_eq_circleAverage]
  exact integral_analytic_mul_pow hf hn

end

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

lemma analyticOnNhd_compact_integral {α : Type u_32} [TopologicalSpace α]
    [CompactSpace α] [MeasurableSpace α] [BorelSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {U : Set ℂ} (hU : IsOpen U)
    {f f' : ℂ → α → ℂ}
    (hf : ContinuousOn (Function.uncurry f) (U ×ˢ univ))
    (hf' : ContinuousOn (Function.uncurry f') (U ×ˢ univ))
    (hd : ∀ z ∈ U, ∀ t, HasDerivAt (fun w => f w t) (f' z t) z) :
    AnalyticOnNhd ℂ (fun w => ∫ t, f w t ∂μ) U := by
  apply DifferentiableOn.analyticOnNhd _ hU
  intro z hz
  exact (compact_parametric_hasDerivAt hU hf hf' hd hz).differentiableAt.differentiableWithinAt

attribute [local instance] OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions_1
lemma physicalCauchy_analytic {G : ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ G (sphere 0 1))
    {u : UnitAddCircle → ℂ} (hu : Continuous u) {U : Set ℂ} (hU : IsOpen U)
    (hne : ∀ z ∈ U, ∀ t : UnitAddCircle, G (t.toCircle : ℂ) ≠ z) :
    AnalyticOnNhd ℂ (physicalCauchy G u) U := by
  have hcc : Continuous (fun t : UnitAddCircle => (t.toCircle : ℂ)) :=
    continuous_subtype_val.comp AddCircle.continuous_toCircle
  have hm (t : UnitAddCircle) : (t.toCircle : ℂ) ∈ sphere (0:ℂ) 1 :=
    t.toCircle.property
  have hcG : Continuous (fun t : UnitAddCircle => G (t.toCircle : ℂ)) :=
    hG.continuousOn.comp_continuous hcc hm
  have hcdG : Continuous (fun t : UnitAddCircle => deriv G (t.toCircle : ℂ)) :=
    hG.deriv.continuousOn.comp_continuous hcc hm
  apply analyticOnNhd_compact_integral hU
    (f' := fun z t => u t*((t.toCircle : ℂ)*deriv G (t.toCircle : ℂ)/
      (G (t.toCircle : ℂ)-z)^2))
  · exact (hu.comp continuous_snd).continuousOn.fun_mul
      (((hcc.comp continuous_snd).continuousOn.fun_mul
        (hcdG.comp continuous_snd).continuousOn).div
        ((hcG.comp continuous_snd).continuousOn.sub continuousOn_fst)
        (fun p hp => sub_ne_zero.mpr (hne p.1 hp.1 p.2)))
  · exact (hu.comp continuous_snd).continuousOn.fun_mul
      (((hcc.comp continuous_snd).continuousOn.fun_mul
        (hcdG.comp continuous_snd).continuousOn).div
        (((hcG.comp continuous_snd).continuousOn.sub continuousOn_fst).pow 2)
        (fun p hp => pow_ne_zero _ (sub_ne_zero.mpr (hne p.1 hp.1 p.2))))
  · intro z hz t
    have he := (((hasDerivAt_const z ((t.toCircle : ℂ)*deriv G (t.toCircle : ℂ))).fun_div
      ((hasDerivAt_id z).const_sub (G (t.toCircle : ℂ))) (sub_ne_zero.mpr (hne z hz t))).const_mul (u t))
    simpa only [id_eq, neg_neg, zero_mul, sub_neg_eq_add, zero_add, mul_one, mul_neg_one, zero_sub] using he

lemma unitAddCircle_integral_affine {E : Type u_33}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℂ → E) (c : ℂ) (R : ℝ) :
    (∫ t : UnitAddCircle, f (c+R*(t.toCircle : ℂ)) ∂AddCircle.haarAddCircle) =
      Real.circleAverage f c R := by
  rw [unitAddCircle_integral_eq_circleAverage (fun z => f (c+R*z))]
  simp only [Real.circleAverage, circleMap, ofReal_one, one_mul, zero_add]

lemma analyticOnNhd_integral_of_continuous {α : Type u_34} [TopologicalSpace α]
    [CompactSpace α] [MeasurableSpace α] [BorelSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {U : Set ℂ} (hU : IsOpen U) {f : ℂ → α → ℂ}
    (hf : ContinuousOn (Function.uncurry f) (U ×ˢ univ))
    (ha : ∀ t, AnalyticOnNhd ℂ (fun z => f z t) U) :
    AnalyticOnNhd ℂ (fun z => ∫ t, f z t ∂μ) U := by
  intro c hc
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hc)
  let R := ε/2
  have hR : 0 < R := by dsimp [R]; positivity
  have hclosed : closedBall c R ⊆ U :=
    (closedBall_subset_ball (by dsimp [R]; linarith : R < ε)).trans hεU
  let G : ℂ → ℂ := fun z => c+R*z
  have hG : AnalyticOnNhd ℂ G univ :=
    analyticOnNhd_const.add (analyticOnNhd_const.mul analyticOnNhd_id)
  have hcd (t : UnitAddCircle) : G (t.toCircle : ℂ) ∈ sphere c R := by
    change dist (c+R*(t.toCircle : ℂ)) c = R
    rw [dist_eq_norm, add_sub_cancel_left, norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_pos hR, Circle.norm_coe, mul_one]
  have hcc : Continuous (fun t : UnitAddCircle => (t.toCircle : ℂ)) :=
    continuous_subtype_val.comp AddCircle.continuous_toCircle
  have hGc : Continuous G := by fun_prop
  have hGc' : deriv G = fun _ => (R : ℂ) := by
    funext z
    exact ((hasDerivAt_id z).const_mul (R:ℂ) |>.const_add c).deriv.trans (by simp)
  have hne (z : ℂ) (hz : z ∈ ball c R) (t : UnitAddCircle) :
      G (t.toCircle : ℂ) ≠ z := by
    intro he
    have ht := hcd t
    rw [he] at ht
    exact ne_of_lt hz ht
  let u : UnitAddCircle → ℂ := fun t => ∫ a, f (G (t.toCircle : ℂ)) a ∂μ
  have hfu : Continuous (fun p : UnitAddCircle × α => f (G (p.1.toCircle : ℂ)) p.2) := by
    exact hf.comp_continuous ((hGc.comp (hcc.comp continuous_fst)).prodMk continuous_snd)
      (fun p => ⟨hclosed (sphere_subset_closedBall (hcd p.1)),mem_univ _⟩)
  have hu : Continuous u := by
    exact continuousOn_univ.mp (continuousOn_integral_of_compact_support
      (μ := μ) isCompact_univ hfu.continuousOn (fun _ _ _ h => (h (mem_univ _)).elim))
  have hka := physicalCauchy_analytic (hG.mono (subset_univ _)) hu isOpen_ball hne
  have he (w : ℂ) (hw : w ∈ ball c R) :
      physicalCauchy G u w = ∫ a, f w a ∂μ := by
    have hkt : Continuous (fun p : UnitAddCircle × α =>
        f (G (p.1.toCircle : ℂ)) p.2 *
          ((p.1.toCircle : ℂ)*deriv G (p.1.toCircle : ℂ)/(G (p.1.toCircle : ℂ)-w))) := by
      apply hfu.mul
      rw [hGc']
      exact (((hcc.comp continuous_fst).mul continuous_const).div
        ((hGc.comp (hcc.comp continuous_fst)).sub continuous_const)
        (fun p => sub_ne_zero.mpr (hne w hw p.1)))
    change (∫ t : UnitAddCircle, (∫ a, f (G (t.toCircle : ℂ)) a ∂μ) *
      ((t.toCircle : ℂ)*deriv G (t.toCircle : ℂ)/(G (t.toCircle : ℂ)-w))
      ∂AddCircle.haarAddCircle) = _
    simp_rw [← integral_mul_const]
    rw [integral_integral_swap (hkt.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))]
    apply integral_congr_ae
    filter_upwards [] with a
    have hdiff : DiffContOnCl ℂ (fun z => f z a) (ball c |R|) := by
      constructor
      · rw [abs_of_pos hR]
        exact (ha a).differentiableOn.mono (ball_subset_closedBall.trans hclosed)
      · simpa only [abs_of_pos hR, closure_ball c (ne_of_gt hR)] using
          ((ha a).mono hclosed).continuousOn
    have hw' : w ∈ ball c |R| := by simpa [abs_of_pos hR] using hw
    rw [hGc']
    have hi := unitAddCircle_integral_affine
      (fun z => ((z-c)/(z-w))*f z a) c R
    simp only [add_sub_cancel_left] at hi
    rw [show (fun t : UnitAddCircle => f (G (t.toCircle : ℂ)) a *
        ((t.toCircle : ℂ)*(R:ℂ)/(G (t.toCircle : ℂ)-w))) =
      (fun t => ((c+R*(t.toCircle : ℂ)-c)/(c+R*(t.toCircle : ℂ)-w))*
        f (c+R*(t.toCircle : ℂ)) a) by
      funext t; dsimp [G]; ring]
    erw [unitAddCircle_integral_affine (fun z => ((z-c)/(z-w))*f z a) c R]
    exact hdiff.circleAverage_smul_div hw'
  exact (hka c (mem_ball_self hR)).congr
    (Filter.eventuallyEq_iff_exists_mem.mpr ⟨ball c R,isOpen_ball.mem_nhds (mem_ball_self hR),he⟩)

end

open MeasureTheory Set Metric Complex Filter
open scoped Topology

attribute [local instance] OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions_2
lemma circle_cauchy_pow (n : ℕ) {w : ℂ} (hw : w ∈ ball 0 1) :
    (∫ t : UnitAddCircle, (t.toCircle : ℂ)^n *
      ((t.toCircle : ℂ)/((t.toCircle : ℂ)-w)) ∂AddCircle.haarAddCircle) = w^n := by
  have hd : DiffContOnCl ℂ (fun z : ℂ => z^n) (ball 0 |(1:ℝ)|) := by
    exact (analyticOnNhd_id.pow n).differentiableOn.diffContOnCl
  have hw' : w ∈ ball 0 |(1:ℝ)| := by simpa using hw
  have he := hd.circleAverage_smul_div hw'
  rw [← unitAddCircle_integral_eq_circleAverage] at he
  simpa only [sub_zero, smul_eq_mul, mul_comm] using he

lemma circle_cauchy_inv_pow {n : ℕ} (hn : n ≠ 0) {w : ℂ} (hw : w ∈ ball 0 1) :
    (∫ t : UnitAddCircle, ((t.toCircle : ℂ)⁻¹)^n *
      ((t.toCircle : ℂ)/((t.toCircle : ℂ)-w)) ∂AddCircle.haarAddCircle) = 0 := by
  have hnz (s : ℂ) (hs : s ∈ closedBall 0 1) : 1-w*s ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    have hnw : ‖w‖ < 1 := by simpa [mem_ball, dist_zero_right] using hw
    have hns : ‖s‖ ≤ 1 := by simpa [mem_closedBall, dist_zero_right] using hs
    have hh : ‖w*s‖ < 1 := by
      rw [norm_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) hns) hnw
    rw [← he, norm_one] at hh
    exact (lt_irrefl 1) hh
  have ha : AnalyticOnNhd ℂ (fun s : ℂ => s^n/(1-w*s)) (closedBall 0 1) := by
    intro s hs
    exact (analyticAt_id.pow n).div (analyticAt_const.sub (analyticAt_const.mul analyticAt_id))
      (hnz s hs)
  have he := integral_reciprocal_analytic ha
  have hc : (fun t : UnitAddCircle => ((t.toCircle : ℂ)⁻¹)^n *
      ((t.toCircle : ℂ)/((t.toCircle : ℂ)-w))) =
      (fun t => ((t.toCircle : ℂ)⁻¹)^n/(1-w*(t.toCircle : ℂ)⁻¹)) := by
    funext t
    have ht : (t.toCircle : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have htw : (t.toCircle : ℂ)-w ≠ 0 := by
      apply sub_ne_zero.mpr
      intro ee
      have ht' := Circle.norm_coe t.toCircle
      rw [ee] at ht'
      have hw' : ‖w‖ < 1 := by simpa [mem_ball, dist_zero_right] using hw
      linarith
    field_simp
  rw [hc]
  simpa only [zero_pow hn, mul_zero, sub_zero, div_one] using he

lemma cauchyCorrectionIntegral_analytic {G : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hG : AnalyticOnNhd ℂ G U) (hi : InjOn G U)
    (hd : ∀ w ∈ U, deriv G w ≠ 0) (hTU : sphere 0 1 ⊆ U)
    {u : UnitAddCircle → ℂ} (hu : Continuous u) :
    AnalyticOnNhd ℂ (cauchyCorrectionIntegral G u) U := by
  have hcc : Continuous (fun t : UnitAddCircle => (t.toCircle : ℂ)) :=
    continuous_subtype_val.comp AddCircle.continuous_toCircle
  have hp : Continuous (fun p : ℂ × UnitAddCircle => (p.1,(p.2.toCircle : ℂ))) :=
    continuous_fst.prodMk (hcc.comp continuous_snd)
  have hb : ContinuousOn (fun p : ℂ × UnitAddCircle =>
      exteriorCorrection G p.1 (p.2.toCircle : ℂ)) (U ×ˢ univ) :=
    ContinuousOn.comp (g := Function.uncurry (exteriorCorrection G))
      (f := fun p : ℂ × UnitAddCircle => (p.1,(p.2.toCircle : ℂ)))
      (s := U ×ˢ (univ : Set UnitAddCircle)) (t := U ×ˢ U)
      (exteriorCorrection_continuousOn hU hG hi hd) hp.continuousOn
      (fun p hp => ⟨hp.1,hTU p.2.toCircle.property⟩)
  exact analyticOnNhd_integral_of_continuous hU
    ((hu.comp continuous_snd).continuousOn.fun_mul hb)
    (fun t => analyticOnNhd_const.mul (exteriorCorrection_analytic_left hU hG hi hd
      (hTU t.toCircle.property)))

lemma physicalCauchy_decompose {G : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hG : AnalyticOnNhd ℂ G U) (hi : InjOn G U)
    (hd : ∀ w ∈ U, deriv G w ≠ 0) (hTU : sphere 0 1 ⊆ U)
    {u : UnitAddCircle → ℂ} (hu : Continuous u) {w : ℂ}
    (hw : w ∈ U) (hwin : w ∈ ball 0 1) :
    physicalCauchy G u (G w) =
      (∫ t : UnitAddCircle, u t*((t.toCircle : ℂ)/((t.toCircle : ℂ)-w))
        ∂AddCircle.haarAddCircle) + cauchyCorrectionIntegral G u w := by
  have hcc : Continuous (fun t : UnitAddCircle => (t.toCircle : ℂ)) :=
    continuous_subtype_val.comp AddCircle.continuous_toCircle
  have hne (t : UnitAddCircle) : (t.toCircle : ℂ) ≠ w := by
    intro he
    have ht := t.toCircle.property
    rw [he] at ht
    exact ne_of_lt hwin ht
  have hc1 : Continuous (fun t : UnitAddCircle =>
      u t*((t.toCircle : ℂ)/((t.toCircle : ℂ)-w))) :=
    hu.mul (hcc.div (hcc.sub continuous_const) (fun t => sub_ne_zero.mpr (hne t)))
  have hc2 : Continuous (fun t : UnitAddCircle =>
      u t*exteriorCorrection G w (t.toCircle : ℂ)) :=
    hu.mul ((exteriorCorrection_analytic_right hU hG hi hd hw).continuousOn.comp_continuous
      hcc (fun t => hTU t.toCircle.property))
  rw [physicalCauchy, cauchyCorrectionIntegral, ← integral_add
    (hc1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hc2.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [exteriorCorrection_eq (hne t) (hG _ (hTU t.toCircle.property)).differentiableAt
    (fun he => hne t (hi (hTU t.toCircle.property) hw he))]
  ring

lemma physicalCauchy_pow {G : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hG : AnalyticOnNhd ℂ G U) (hi : InjOn G U)
    (hd : ∀ w ∈ U, deriv G w ≠ 0) (hTU : sphere 0 1 ⊆ U)
    (n : ℕ) {w : ℂ} (hw : w ∈ U) (hwin : w ∈ ball 0 1) :
    physicalCauchy G (fun t => (t.toCircle : ℂ)^n) (G w) =
      w^n + cauchyCorrectionIntegral G (fun t => (t.toCircle : ℂ)^n) w := by
  erw [physicalCauchy_decompose hU hG hi hd hTU
    ((continuous_subtype_val.comp AddCircle.continuous_toCircle).pow n) hw hwin,
    circle_cauchy_pow n hwin]
  rfl

lemma physicalCauchy_inv_pow {G : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hG : AnalyticOnNhd ℂ G U) (hi : InjOn G U)
    (hd : ∀ w ∈ U, deriv G w ≠ 0) (hTU : sphere 0 1 ⊆ U)
    {n : ℕ} (hn : n ≠ 0) {w : ℂ} (hw : w ∈ U) (hwin : w ∈ ball 0 1) :
    physicalCauchy G (fun t => ((t.toCircle : ℂ)⁻¹)^n) (G w) =
      cauchyCorrectionIntegral G (fun t => ((t.toCircle : ℂ)⁻¹)^n) w := by
  have hu : Continuous (fun t : UnitAddCircle => ((t.toCircle : ℂ)⁻¹)^n) :=
    ((continuous_subtype_val.comp AddCircle.continuous_toCircle).inv₀
      (fun t => Circle.coe_ne_zero _)).pow n
  rw [physicalCauchy_decompose hU hG hi hd hTU hu hw hwin,
    circle_cauchy_inv_pow hn hwin, zero_add]


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_MarkovOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u_35 u_36 u_37 u_38 u_39

open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open MeasureTheory Set Complex
open scoped Topology Real
open MeasureTheory Set Metric Complex Filter
open scoped Topology

open MeasureTheory Set Filter
open scoped ENNReal NNReal InnerProductSpace
namespace CompleteCrouzeix

section

variable {X : Type u_37} [MeasurableSpace X] (μ : Measure X)

namespace MarkovKernel
variable {μ} (K : MarkovKernel μ) [instIsFiniteMeasureΜ : IsFiniteMeasure μ]
  {E : Type u_38} [NormedAddCommGroup E] [instInnerProductSpaceℂE : InnerProductSpace ℂ E] [instCompleteSpaceE : CompleteSpace E]

lemma applyFun_const (c : E) (x : X) :
    K.applyFun (Lp.const 2 μ c) x = c := by
  unfold applyFun
  calc _ = ∫ y, K.kernel x y • c ∂μ := by
         apply integral_congr_ae
         filter_upwards [Lp.coeFn_const (p := 2) (μ := μ) c] with y hy
         rw [hy]; rfl
       _ = c := by rw [integral_smul_const, K.row x, one_smul]

lemma toCLM_const (c : E) : K.toCLM (Lp.const 2 μ c) = Lp.const 2 μ c := by
  apply Lp.ext
  filter_upwards [K.applyLp_ae (Lp.const 2 μ c), Lp.coeFn_const (p := 2) (μ := μ) c]
    with x hx hc
  exact hx.trans ((K.applyFun_const c x).trans hc.symm)

end MarkovKernel
end
open MeasureTheory Set Metric Complex ComplexConjugate
open scoped Topology Real

namespace AnalyticBidiskKernel
variable (K : AnalyticBidiskKernel)

attribute [local instance] OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions_3
lemma circleB_right_nonpos_fourier (w : UnitAddCircle) (n : ℤ) (hn : n ≤ 0) :
    (∫ t, K.circleB w t * fourier n t ∂AddCircle.haarAddCircle) = 0 := by
  cases n with
  | ofNat k =>
    have hk : k = 0 := Int.natCast_nonpos_iff.mp hn
    subst k
    simpa using K.circleB_row_integral w
  | negSucc k =>
    change (∫ t, K.circleB w t * fourier (-(↑(k+1) : ℤ)) t ∂AddCircle.haarAddCircle) = 0
    simp only [fourier_neg_natCast_toCircle]
    simpa only [circleB, mul_comm] using
      integral_reciprocal_analytic_mul_inv_pow (K.right _ (inv_circle_mem w))
        (Nat.succ_ne_zero k)

lemma circleB_left_nonpos_fourier (t : UnitAddCircle) (n : ℤ) (hn : n ≤ 0) :
    (∫ w, K.circleB w t * fourier n w ∂AddCircle.haarAddCircle) = 0 := by
  cases n with
  | ofNat k =>
    have hk : k = 0 := Int.natCast_nonpos_iff.mp hn
    subst k
    simpa using K.circleB_column_integral t
  | negSucc k =>
    change (∫ w, K.circleB w t * fourier (-(↑(k+1) : ℤ)) w ∂AddCircle.haarAddCircle) = 0
    simp only [fourier_neg_natCast_toCircle]
    simpa only [circleB, mul_comm] using
      integral_reciprocal_analytic_mul_inv_pow (K.left _ (inv_circle_mem t))
        (Nat.succ_ne_zero k)

lemma conj_circleB_right_nonneg_fourier (w : UnitAddCircle) (n : ℤ) (hn : 0 ≤ n) :
    (∫ t, conj (K.circleB w t) * fourier n t ∂AddCircle.haarAddCircle) = 0 := by
  have h := congrArg conj (K.circleB_right_nonpos_fourier w (-n) (by omega))
  rw [← integral_conj] at h
  simpa only [map_mul, ← fourier_neg, neg_neg, map_zero] using h

end AnalyticBidiskKernel
end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_FourierResolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u_40 u_41 u_42 u_43

open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open MeasureTheory Set Complex
open scoped Topology Real
open MeasureTheory Set Metric Complex Filter
open scoped Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal InnerProductSpace

open scoped ComplexConjugate InnerProductSpace
namespace CompleteCrouzeix

section

open scoped lp
variable {ι : Type u_42} {E : Type u_43} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [instCompleteSpaceE : CompleteSpace E]

open MeasureTheory

attribute [local instance] OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions_4
lemma scalarFourier_coefficient (j : Fin 3) (u : CircleL2) (n : ℤ) :
    fourierCoeff (scalarFourier.proj j u) n =
      if frequencyPart n = j then fourierCoeff u n else 0 := by
  simpa only [← fourierBasis_repr, scalarFourier, basisResolution] using
    basisProjection_repr (E := CircleL2) fourierBasis frequencyPart j u n

end

open MeasureTheory ComplexConjugate
open scoped Topology

attribute [local instance] OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions_5
lemma circle_fourier_ext {u v : CircleL2}
    (h : ∀ n : ℤ, fourierCoeff u n = fourierCoeff v n) : u = v := by
  apply fourierBasis.repr.injective
  apply lp.ext
  funext n
  simpa only [fourierBasis_repr] using h n

lemma circle_fourier_star (u : CircleL2) (n : ℤ) :
    fourierCoeff (star u : CircleL2) n = star (fourierCoeff u (-n)) := by
  rw [fourierCoeff, fourierCoeff]
  change _ = (starRingEnd ℂ) _
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star u] with t ht
  simp only [ht, Pi.star_apply, smul_eq_mul, map_mul, neg_neg,
    fourier_neg, RCLike.star_def]

lemma integral_fourier_nonzero (n : ℤ) (hn : n ≠ 0) :
    (∫ t : UnitAddCircle, fourier n t ∂AddCircle.haarAddCircle) = 0 := by
  have h := congrFun (fourierCoeff_fourier (T := 1) n) 0
  simpa [fourierCoeff, Pi.single_eq_of_ne hn.symm] using h

lemma scalarFourier_fourier (j : Fin 3) (n : ℤ) :
    scalarFourier.proj j (fourierLp 2 n) =
      if frequencyPart n = j then fourierLp 2 n else 0 := by
  apply circle_fourier_ext
  intro k
  rw [scalarFourier_coefficient]
  have hf : fourierCoeff (fourierLp 2 n : CircleL2) k = (Pi.single n (1 : ℂ) : ℤ → ℂ) k := by
    rw [fourierCoeff_congr_ae (coeFn_fourierLp 2 n), fourierCoeff_fourier]
  by_cases h : frequencyPart n = j
  · simp only [h, ite_true, hf]
    by_cases hkn : k = n
    · subst k; simp [h]
    · simp [Pi.single_eq_of_ne hkn]
  · have hz : fourierCoeff (0 : CircleL2) k = 0 := by
      rw [fourierCoeff_congr_ae (Lp.coeFn_zero _ _ _)]
      simp [fourierCoeff]
    simp only [h, ite_false, hz, hf]
    by_cases hkn : k = n
    · subst k; simp [h]
    · simp [Pi.single_eq_of_ne hkn]

namespace AnalyticBidiskKernel
variable (K : AnalyticBidiskKernel)

lemma kernel_complex (w t : UnitAddCircle) :
    (K.kernel w t : ℂ) = 1 + K.circleB w t + conj (K.circleB w t) := by
  apply Complex.ext <;> simp [kernel, Complex.add_re, Complex.add_im]; ring

attribute [local instance] OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions_5
lemma scalarM_fourier_ae (n : ℤ) :
    K.scalarM (fourierLp 2 n) =ᵐ[AddCircle.haarAddCircle]
      fun w => ∫ t, (K.kernel w t : ℂ) * fourier n t ∂AddCircle.haarAddCircle := by
  filter_upwards [K.toMarkovKernel.applyLp_ae (fourierLp 2 n : CircleL2)] with w hw
  refine hw.trans ?_
  apply integral_congr_ae
  filter_upwards [coeFn_fourierLp 2 n] with t ht
  rw [ht]
  rfl

lemma scalarM_fourier_positive_ae (n : ℤ) (hn : 0 < n) :
    K.scalarM (fourierLp 2 n) =ᵐ[AddCircle.haarAddCircle]
      fun w => ∫ t, K.circleB w t * fourier n t ∂AddCircle.haarAddCircle := by
  filter_upwards [K.scalarM_fourier_ae n] with w hw
  rw [hw]
  simp_rw [K.kernel_complex, add_mul, one_mul]
  have hB : Continuous (fun t => K.circleB w t * fourier n t) :=
    (K.continuous_circleB.comp (continuous_const.prodMk continuous_id)).mul
      (fourier n).continuous
  have hBc : Continuous (fun t => conj (K.circleB w t) * fourier n t) :=
    (Complex.continuous_conj.comp
      (K.continuous_circleB.comp (continuous_const.prodMk continuous_id))).mul
      (fourier n).continuous
  have hint (f : UnitAddCircle → ℂ) (hf : Continuous f) :
      Integrable f AddCircle.haarAddCircle :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he₁ : (∫ t, fourier n t + K.circleB w t * fourier n t +
      conj (K.circleB w t) * fourier n t ∂AddCircle.haarAddCircle) =
      (∫ t, fourier n t + K.circleB w t * fourier n t ∂AddCircle.haarAddCircle) +
      (∫ t, conj (K.circleB w t) * fourier n t ∂AddCircle.haarAddCircle) :=
    integral_add ((hint _ (fourier n).continuous).add (hint _ hB)) (hint _ hBc)
  have he₂ : (∫ t, fourier n t + K.circleB w t * fourier n t ∂AddCircle.haarAddCircle) =
      (∫ t, fourier n t ∂AddCircle.haarAddCircle) +
      (∫ t, K.circleB w t * fourier n t ∂AddCircle.haarAddCircle) :=
    integral_add (hint _ (fourier n).continuous) (hint _ hB)
  rw [he₁, he₂,
    integral_fourier_nonzero n (ne_of_gt hn),
    K.conj_circleB_right_nonneg_fourier w n (le_of_lt hn), zero_add, add_zero]

lemma scalarM_fourier_positive_coefficient (n k : ℤ) (hn : 0 < n) (hk : 0 ≤ k) :
    fourierCoeff (K.scalarM (fourierLp 2 n)) k = 0 := by
  rw [fourierCoeff_congr_ae (K.scalarM_fourier_positive_ae n hn), fourierCoeff]
  simp only [smul_eq_mul]
  simp_rw [← integral_const_mul]
  have hc : Continuous (fun p : UnitAddCircle × UnitAddCircle =>
      fourier (-k) p.1 * (K.circleB p.1 p.2 * fourier n p.2)) :=
    ((fourier (-k)).continuous.comp continuous_fst).mul
      (K.continuous_circleB.mul ((fourier n).continuous.comp continuous_snd))
  rw [integral_integral_swap
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  have hz (t : UnitAddCircle) :
      (∫ w, fourier (-k) w * (K.circleB w t * fourier n t)
        ∂AddCircle.haarAddCircle) = 0 := by
    simp_rw [show ∀ w, fourier (-k) w * (K.circleB w t * fourier n t) =
      (K.circleB w t * fourier (-k) w) * fourier n t from fun w => by ring]
    rw [integral_mul_const, K.circleB_left_nonpos_fourier t (-k) (by omega), zero_mul]
  simp_rw [hz, integral_zero]

lemma scalarM_star (u : CircleL2) : K.scalarM (star u) = star (K.scalarM u) := by
  apply Lp.ext
  filter_upwards [K.toMarkovKernel.applyLp_ae (star u),
    K.toMarkovKernel.applyLp_ae u, Lp.coeFn_star (K.scalarM u)] with w hs hu hstar
  change K.toMarkovKernel.applyLp (star u) w = _
  rw [hs,hstar]
  change K.toMarkovKernel.applyFun (star u) w = conj (K.toMarkovKernel.applyLp u w)
  rw [hu]
  unfold MarkovKernel.applyFun
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star u] with t ht
  rw [ht]
  change (K.kernel w t : ℂ) * conj (u t) = conj ((K.kernel w t : ℂ) * u t)
  simp

lemma star_fourierLp (n : ℤ) :
    star (fourierLp 2 n : CircleL2) = fourierLp 2 (-n) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (fourierLp 2 n : CircleL2),
    coeFn_fourierLp 2 n, coeFn_fourierLp 2 (-n)] with t hs hn hneg
  simp only [hs,Pi.star_apply,hn,hneg,fourier_neg,RCLike.star_def]

lemma scalarM_fourier_negative_coefficient (n k : ℤ) (hn : n < 0) (hk : k ≤ 0) :
    fourierCoeff (K.scalarM (fourierLp 2 n)) k = 0 := by
  have he : (fourierLp 2 n : CircleL2) = star (fourierLp 2 (-n) : CircleL2) := by
    simpa only [neg_neg] using (star_fourierLp (-n)).symm
  rw [he,K.scalarM_star,circle_fourier_star,
    K.scalarM_fourier_positive_coefficient (-n) (-k) (by omega) (by omega),star_zero]

lemma scalarM_fourier_zero : K.scalarM (fourierLp 2 0) = fourierLp 2 0 := by
  have he : (fourierLp 2 0 : CircleL2) = Lp.const 2 AddCircle.haarAddCircle 1 := by
    apply Lp.ext
    filter_upwards [coeFn_fourierLp 2 0,
      Lp.coeFn_const (p := 2) (μ := AddCircle.haarAddCircle) (1 : ℂ)] with t hf hc
    rw [hf,hc]
    simp
  rw [he]
  exact K.toMarkovKernel.toCLM_const 1

lemma scalarM_fourier_swap (n : ℤ) :
    K.scalarM (scalarFourier.proj 1 (fourierLp 2 n)) =
      scalarFourier.proj 2 (K.scalarM (fourierLp 2 n)) := by
  rw [scalarFourier_fourier]
  rcases lt_trichotomy n 0 with hn | hn | hn
  · have hfn : frequencyPart n ≠ 1 := by simp [frequencyPart,hn.ne,not_lt.mpr hn.le]
    simp only [hfn,ite_false,map_zero]
    apply circle_fourier_ext
    intro k
    have hz : fourierCoeff (0 : CircleL2) k = 0 := by
      rw [fourierCoeff_congr_ae (Lp.coeFn_zero _ _ _)]
      simp [fourierCoeff]
    rw [hz,scalarFourier_coefficient]
    split_ifs with hfk
    · have hk : k < 0 := by
        unfold frequencyPart at hfk
        split_ifs at hfk with h0 hp <;> simp_all
        omega
      exact (K.scalarM_fourier_negative_coefficient n k hn hk.le).symm
    · rfl
  · subst n
    rw [K.scalarM_fourier_zero,scalarFourier_fourier]
    simp [frequencyPart]
  · have hfn : frequencyPart n = 1 := by simp [frequencyPart,hn.ne',hn]
    simp only [hfn,ite_true]
    apply circle_fourier_ext
    intro k
    rw [scalarFourier_coefficient]
    split_ifs with hfk
    · rfl
    · have hk : 0 ≤ k := by
        by_contra hk
        have hk' : k < 0 := by omega
        exact hfk (by simp [frequencyPart,hk'.ne,not_lt.mpr hk'.le])
      exact K.scalarM_fourier_positive_coefficient n k hn hk

lemma scalarM_swap : K.scalarM.comp (scalarFourier.proj 1) =
    (scalarFourier.proj 2).comp K.scalarM := by
  apply ContinuousLinearMap.ext_on (s := Set.range (fourierLp (T := 1) 2))
  · change ∀ x, x ∈ closure (Submodule.span ℂ (Set.range (fourierLp (T := 1) 2)) : Set CircleL2)
    change ∀ x, x ∈ (Submodule.span ℂ (Set.range (fourierLp (T := 1) 2))).topologicalClosure
    rw [span_fourierLp_closure_eq_top (by norm_num : (2 : ENNReal) ≠ ∞)]
    intro x; trivial
  · rintro _ ⟨n,rfl⟩
    exact K.scalarM_fourier_swap n

end AnalyticBidiskKernel
end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_CauchyProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u_44

open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open MeasureTheory Set Complex
open scoped Topology Real
open MeasureTheory Set Metric Complex Filter
open scoped Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal InnerProductSpace
open scoped ComplexConjugate InnerProductSpace

namespace CompleteCrouzeix

section
open MeasureTheory Set Complex
open scoped Topology InnerProductSpace ComplexConjugate

attribute [local instance] OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions_6
lemma circleTest_apply (f : C(UnitAddCircle,ℂ)) (u : CircleL2) :
    circleTest f u = ∫ t, f t * u t ∂AddCircle.haarAddCircle := by
  change inner ℂ (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (star f)) u = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (μ := AddCircle.haarAddCircle)
    (p := 2) (𝕜 := ℂ) (star f)] with t ht
  rw [ht]
  simp [RCLike.inner_apply, mul_comm]

lemma circleTest_add (f g : C(UnitAddCircle,ℂ)) :
    circleTest (f+g) = circleTest f+circleTest g := by
  ext u
  simp only [circleTest, star_add, map_add, add_apply]

lemma circleTest_fourier (f : C(UnitAddCircle,ℂ)) (n : ℤ) :
    circleTest f (fourierLp 2 n) = ∫ t, f t * fourier n t ∂AddCircle.haarAddCircle := by
  rw [circleTest_apply]
  apply integral_congr_ae
  filter_upwards [coeFn_fourierLp 2 n] with t ht
  rw [ht]

lemma circleCLM_ext {E : Type u_44} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {L J : CircleL2 →L[ℂ] E} (h : ∀ n : ℤ, L (fourierLp 2 n) = J (fourierLp 2 n)) : L = J := by
  apply ContinuousLinearMap.ext_on (s := Set.range (fourierLp (T := 1) 2))
  · change ∀ x, x ∈ (Submodule.span ℂ (Set.range (fourierLp (T := 1) 2))).topologicalClosure
    rw [span_fourierLp_closure_eq_top (by norm_num : (2 : ENNReal) ≠ ∞)]
    intro x; trivial
  · rintro _ ⟨n,rfl⟩; exact h n

lemma circleTest_const_positive :
    (circleTest (1 : C(UnitAddCircle,ℂ))).comp (scalarFourier.proj 1) = 0 := by
  apply circleCLM_ext
  intro n
  simp only [ContinuousLinearMap.comp_apply, scalarFourier_fourier,
    zero_apply]
  split_ifs with hn
  · have hn' : 0 < n := by
      by_contra hnonpos
      by_cases hzero : n = 0
      · simp [frequencyPart, hzero] at hn
      · simp [frequencyPart, hzero, hnonpos] at hn
    rw [circleTest_fourier]
    simpa using integral_fourier_nonzero n (ne_of_gt hn')
  · exact map_zero _

namespace AnalyticBidiskKernel
variable (K : AnalyticBidiskKernel)

lemma rowKernel_eq (w : UnitAddCircle) : K.rowKernel w = 1 + K.rowB w + star (K.rowB w) := by
  ext t
  exact K.kernel_complex w t

attribute [local instance] OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions_6
lemma testB_positive (w : UnitAddCircle) :
    (circleTest (K.rowB w)).comp (scalarFourier.proj 1) = circleTest (K.rowB w) := by
  apply circleCLM_ext
  intro n
  simp only [ContinuousLinearMap.comp_apply, scalarFourier_fourier]
  split_ifs with hn
  · rfl
  · rw [map_zero, circleTest_fourier]
    symm
    apply K.circleB_right_nonpos_fourier
    by_contra hh
    have hn' : 0 < n := lt_of_not_ge hh
    exact hn (by simp [frequencyPart, ne_of_gt hn', hn'])

lemma testConjB_positive (w : UnitAddCircle) :
    (circleTest (star (K.rowB w))).comp (scalarFourier.proj 1) = 0 := by
  apply circleCLM_ext
  intro n
  simp only [ContinuousLinearMap.comp_apply, scalarFourier_fourier,
    zero_apply]
  split_ifs with hn
  · rw [circleTest_fourier]
    apply K.conj_circleB_right_nonneg_fourier
    by_contra hh
    have hn' : n < 0 := lt_of_not_ge hh
    exact (by simp [frequencyPart,ne_of_lt hn',not_lt.mpr hn'.le] at hn)
  · exact map_zero _

lemma testKernel_positive (w : UnitAddCircle) :
    (circleTest (K.rowKernel w)).comp (scalarFourier.proj 1) = circleTest (K.rowB w) := by
  rw [K.rowKernel_eq, circleTest_add, circleTest_add,
    ContinuousLinearMap.add_comp, ContinuousLinearMap.add_comp,
    circleTest_const_positive, K.testB_positive, K.testConjB_positive, zero_add, add_zero]

lemma scalarM_positive_ae (u : CircleL2) :
    K.scalarM (scalarFourier.proj 1 u) =ᵐ[AddCircle.haarAddCircle]
      fun w => ∫ t, K.circleB w t * u t ∂AddCircle.haarAddCircle := by
  filter_upwards [K.toMarkovKernel.applyLp_ae (scalarFourier.proj 1 u)] with w hw
  refine hw.trans ?_
  change (∫ t, (K.kernel w t : ℂ) * (scalarFourier.proj 1 u) t
    ∂AddCircle.haarAddCircle) = _
  change (∫ t, K.rowKernel w t * (scalarFourier.proj 1 u) t
    ∂AddCircle.haarAddCircle) = _
  rw [← circleTest_apply]
  have he := congrArg (fun L : CircleL2 →L[ℂ] ℂ => L u) (K.testKernel_positive w)
  exact he.trans (circleTest_apply (K.rowB w) u)

end AnalyticBidiskKernel
end

open MeasureTheory Set Complex
open scoped Topology

attribute [local instance] OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions_7
lemma analyticTrace_negative_coefficient (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 1)) (n : ℤ) (hn : n < 0) :
    fourierCoeff (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (analyticCircleTrace f hf)) n = 0 := by
  rw [fourierCoeff_congr_ae (ContinuousMap.coeFn_toLp (μ := AddCircle.haarAddCircle)
    (p := 2) (𝕜 := ℂ) (analyticCircleTrace f hf)),fourierCoeff]
  obtain ⟨k,hk⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -n by omega)
  have hk0 : k ≠ 0 := by omega
  simp only [hk, fourier_natCast_toCircle, smul_eq_mul, analyticCircleTrace,
    ContinuousMap.coe_mk]
  exact integral_analytic_mul_pow hf hk0

lemma analyticTrace_negative (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 1)) :
    scalarFourier.proj 2 (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ
      (analyticCircleTrace f hf)) = 0 := by
  apply circle_fourier_ext
  intro n
  rw [scalarFourier_coefficient]
  have hz : fourierCoeff (0 : CircleL2) n = 0 := by
    rw [fourierCoeff_congr_ae (Lp.coeFn_zero ℂ 2 AddCircle.haarAddCircle)]
    simp [fourierCoeff]
  rw [hz]
  split_ifs with hn
  · apply analyticTrace_negative_coefficient
    by_contra hh
    have hn0 : 0 ≤ n := le_of_not_gt hh
    by_cases he : n = 0
    · simp [frequencyPart,he] at hn
    · simp [frequencyPart,he,lt_of_le_of_ne hn0 (Ne.symm he)] at hn
  · rfl

lemma scalarCauchy_fix_of_parts (K : AnalyticBidiskKernel) (u : CircleL2)
    (h : scalarFourier.proj 2 u = K.scalarM (scalarFourier.proj 1 u)) :
    scalarFourier.cauchy K.scalarM u = u := by
  change scalarFourier.proj 0 u + scalarFourier.proj 1 u +
    K.scalarM (scalarFourier.proj 1 u) = u
  rw [← h]
  exact congrArg (fun L : CircleL2 →L[ℂ] CircleL2 => L u) scalarFourier.total

end CompleteCrouzeix

open Set Metric Filter Complex
open scoped Topology
namespace CompleteCrouzeix

section

section

theorem analytic_circle_gluing {U : Set ℂ} (hU : IsOpen U)
    (hTU : sphere 0 1 ⊆ U) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (ball 0 1)) (hg : AnalyticOnNhd ℂ g U)
    (he : ∀ z ∈ U ∩ ball 0 1, f z = g z) :
    ∃ q : ℂ → ℂ, AnalyticOnNhd ℂ q (closedBall 0 1) ∧ EqOn q g (sphere 0 1) := by
  classical
  let q := fun z => if z ∈ ball (0 : ℂ) 1 then f z else g z
  refine ⟨q,?_,?_⟩
  · intro z hz
    by_cases hi : z ∈ ball (0 : ℂ) 1
    · apply (hf z hi).congr
      filter_upwards [isOpen_ball.mem_nhds hi] with w hw
      simp only [q, ite_eq_left hw]
    · have hs : z ∈ sphere (0 : ℂ) 1 := by
        change dist z 0 = 1
        exact le_antisymm hz (le_of_not_gt hi)
      apply (hg z (hTU hs)).congr
      filter_upwards [hU.mem_nhds (hTU hs)] with w hw
      dsimp [q]
      split_ifs with hwi
      · exact (he w ⟨hw,hwi⟩).symm
      · rfl
  · intro z hz
    have hi : z ∉ ball (0 : ℂ) 1 := by
      intro hh
      exact ne_of_lt hh hz
    simp only [q, ite_eq_right hi]


open Set Metric Complex MeasureTheory
open scoped Topology

attribute [local instance] OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions_8
lemma scalarCauchy_fix_of_analytic_correction (K : AnalyticBidiskKernel)
    (u : C(UnitAddCircle,ℂ)) (q : ℂ → ℂ)
    (hq : AnalyticOnNhd ℂ q (closedBall 0 1))
    (he : ∀ w : UnitAddCircle, u w = q (w.toCircle : ℂ) +
      ∫ t, K.circleB w t * u t ∂AddCircle.haarAddCircle) :
    scalarFourier.cauchy K.scalarM (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ u) =
      ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ u := by
  let L : C(UnitAddCircle,ℂ) →L[ℂ] CircleL2 := ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ
  have hparts : L u = L (analyticCircleTrace q hq) + K.scalarM (scalarFourier.proj 1 (L u)) := by
    apply Lp.ext
    filter_upwards [ContinuousMap.coeFn_toLp (μ := AddCircle.haarAddCircle)
      (p := 2) (𝕜 := ℂ) u,
      ContinuousMap.coeFn_toLp (μ := AddCircle.haarAddCircle) (p := 2) (𝕜 := ℂ)
        (analyticCircleTrace q hq),
      Lp.coeFn_add (L (analyticCircleTrace q hq)) (K.scalarM (scalarFourier.proj 1 (L u))),
      K.scalarM_positive_ae (L u)] with w hu hq' hadd hM
    rw [hadd]
    change L u w = L (analyticCircleTrace q hq) w + K.scalarM (scalarFourier.proj 1 (L u)) w
    rw [hu,hq',hM]
    change u w = q (w.toCircle : ℂ) + ∫ t, K.circleB w t * L u t ∂AddCircle.haarAddCircle
    rw [he w]
    congr 1
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (μ := AddCircle.haarAddCircle)
      (p := 2) (𝕜 := ℂ) u] with t ht
    rw [ht]
  apply scalarCauchy_fix_of_parts
  calc
    scalarFourier.proj 2 (L u) =
      scalarFourier.proj 2 (L (analyticCircleTrace q hq)) +
        scalarFourier.proj 2 (K.scalarM (scalarFourier.proj 1 (L u))) := by
      rw [← map_add, ← hparts]
    _ = K.scalarM (scalarFourier.proj 1 (L u)) := by
      rw [analyticTrace_negative,zero_add]
      have hs := congrArg (fun T : CircleL2 →L[ℂ] CircleL2 => T (scalarFourier.proj 1 (L u))) K.scalarM_swap
      simp only [ContinuousLinearMap.comp_apply, scalarFourier.proj_proj] at hs
      simpa using hs.symm

end

open MeasureTheory Set Metric Complex
open scoped Topology

attribute [local instance] OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions_9
lemma canonicalCircleCauchy_analytic {u : UnitAddCircle → ℂ} (hu : Continuous u) :
    AnalyticOnNhd ℂ (fun w => ∫ t : UnitAddCircle,
      u t*((t.toCircle : ℂ)/((t.toCircle : ℂ)-w)) ∂AddCircle.haarAddCircle) (ball 0 1) := by
  have h : AnalyticOnNhd ℂ (physicalCauchy id u) (ball 0 1) :=
    physicalCauchy_analytic analyticOnNhd_id hu isOpen_ball (by
      intro z hz t he
      have ht := t.toCircle.property
      change (t.toCircle : ℂ) = z at he
      rw [he] at ht
      exact ne_of_lt hz ht)
  convert h using 1
  funext w
  simp [physicalCauchy]

lemma scalarCauchy_fix_physical_trace (K : AnalyticBidiskKernel)
    {G v : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hG : AnalyticOnNhd ℂ G U) (hi : InjOn G U)
    (hd : ∀ w ∈ U, deriv G w ≠ 0) (hTU : sphere 0 1 ⊆ U)
    (hv : AnalyticOnNhd ℂ (fun w => v (G w)) U)
    (hB : ∀ w t : UnitAddCircle, K.circleB w t = exteriorCorrection G w.toCircle t.toCircle)
    (hrep : ∀ w ∈ U ∩ ball 0 1,
      physicalCauchy G (fun t => v (G t.toCircle)) (G w) = v (G w)) :
    let u : C(UnitAddCircle,ℂ) := ⟨fun t => v (G t.toCircle),
      hv.continuousOn.comp_continuous
        (continuous_subtype_val.comp AddCircle.continuous_toCircle)
        (fun t => hTU t.toCircle.property)⟩
    scalarFourier.cauchy K.scalarM (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ u) =
      ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ u := by
  dsimp only
  let u : C(UnitAddCircle,ℂ) := ⟨fun t => v (G t.toCircle),
    hv.continuousOn.comp_continuous
      (continuous_subtype_val.comp AddCircle.continuous_toCircle)
      (fun t => hTU t.toCircle.property)⟩
  change scalarFourier.cauchy K.scalarM (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ u) = _
  have hJ := cauchyCorrectionIntegral_analytic hU hG hi hd hTU u.continuous
  obtain ⟨q,hq,hqT⟩ := analytic_circle_gluing hU hTU
    (canonicalCircleCauchy_analytic u.continuous) (hv.sub hJ) (by
      intro w hw
      apply eq_sub_iff_add_eq.mpr
      exact (physicalCauchy_decompose hU hG hi hd hTU u.continuous hw.1 hw.2).symm.trans
        (hrep w hw))
  apply scalarCauchy_fix_of_analytic_correction K u q hq
  intro w
  have he := hqT w.toCircle.property
  change q (w.toCircle : ℂ) = v (G w.toCircle) - cauchyCorrectionIntegral G u w.toCircle at he
  rw [he]
  have hj : cauchyCorrectionIntegral G u w.toCircle =
      ∫ t, K.circleB w t * u t ∂AddCircle.haarAddCircle := by
    apply integral_congr_ae
    filter_upwards [] with t
    rw [hB]
    exact mul_comm _ _
  change v (G w.toCircle) = _
  rw [hj,sub_add_cancel]

end


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

lemma actualExteriorKernel_circleB {a b : ℂ} {h : ℂ → ℂ} {R : ℝ}
    (hR : 1 < R) (ha : a ≠ 0) (hh : AnalyticOnNhd ℂ h (ball 0 R))
    (hi : InjOn (exteriorMap a b h) {t | R⁻¹ < ‖t‖})
    (hd : ∀ t, R⁻¹ < ‖t‖ → deriv (exteriorMap a b h) t ≠ 0)
    (hsupport : ∀ w t : Circle,
      0 ≤ (conj ((t : ℂ)*deriv (exteriorMap a b h) t)*
        (exteriorMap a b h t-exteriorMap a b h w)).re)
    (w t : UnitAddCircle) :
    (actualExteriorKernel hR ha hh hi hd hsupport).circleB w t =
      exteriorCorrection (exteriorMap a b h) w.toCircle t.toCircle := by
  have hw : (w.toCircle : ℂ)⁻¹ ∈ ball (0 : ℂ) R := by
    simpa only [mem_ball, dist_zero_right, norm_inv, Circle.norm_coe, inv_one] using hR
  have ht : (t.toCircle : ℂ)⁻¹ ∈ ball (0 : ℂ) R := by
    simpa only [mem_ball, dist_zero_right, norm_inv, Circle.norm_coe, inv_one] using hR
  have he := exteriorCorrection_eq_reciprocal (a := a) (b := b)
    (inv_ne_zero (Circle.coe_ne_zero w.toCircle)) (inv_ne_zero (Circle.coe_ne_zero t.toCircle))
    (hh _ hw).differentiableAt (hh _ ht).differentiableAt
    ((analyticOnNhd_dslope isOpen_ball hh hw) _ ht).differentiableAt
  change reciprocalCorrection a h (w.toCircle : ℂ)⁻¹ (t.toCircle : ℂ)⁻¹ = _
  simpa only [inv_inv] using he.symm

attribute [local instance] OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions_11
theorem actualExteriorCauchy_fix_trace {a b : ℂ} {h : ℂ → ℂ} {R : ℝ}
    (hR : 1 < R) (ha : a ≠ 0) (hh : AnalyticOnNhd ℂ h (ball 0 R))
    (hi : InjOn (exteriorMap a b h) {t | R⁻¹ < ‖t‖})
    (hd : ∀ t, R⁻¹ < ‖t‖ → deriv (exteriorMap a b h) t ≠ 0)
    (hsupport : ∀ w t : Circle,
      0 ≤ (conj ((t : ℂ)*deriv (exteriorMap a b h) t)*
        (exteriorMap a b h t-exteriorMap a b h w)).re)
    {Ω : Set ℂ} (hΩ : Convex ℝ Ω)
    (hboundary : MapsTo (exteriorMap a b h) (sphere 0 1) Ω)
    (hinner : MapsTo (exteriorMap a b h) ({t | R⁻¹ < ‖t‖} ∩ ball 0 1) Ω)
    {v : ℂ → ℂ} (hv : AnalyticOnNhd ℂ v Ω)
    (u : C(UnitAddCircle,ℂ)) (hu : ∀ t, u t = v (exteriorMap a b h t.toCircle)) :
    scalarFourier.cauchy (actualExteriorKernel hR ha hh hi hd hsupport).scalarM
      (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ u) =
        ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ u := by
  let G := exteriorMap a b h
  let U : Set ℂ := {t | R⁻¹ < ‖t‖}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_norm
  have hG : AnalyticOnNhd ℂ G U := analyticOnNhd_exteriorMap (lt_trans zero_lt_one hR) hh
  have hTU : sphere (0:ℂ) 1 ⊆ U := by
    intro t ht
    change R⁻¹ < ‖t‖
    rw [mem_sphere_zero_iff_norm.mp ht]
    exact (inv_lt_one₀ (lt_trans zero_lt_one hR)).mpr hR
  let V := U ∩ {w | AnalyticAt ℂ (fun w => v (G w)) w}
  have hV : IsOpen V := hU.inter (isOpen_analyticAt ℂ _)
  have hTV : sphere (0:ℂ) 1 ⊆ V := by
    intro t ht
    exact ⟨hTU ht,(hv _ (hboundary ht)).comp (hG t (hTU ht))⟩
  have hvV : AnalyticOnNhd ℂ (fun w => v (G w)) V := fun _ hw => hw.2
  have hp := scalarCauchy_fix_physical_trace (actualExteriorKernel hR ha hh hi hd hsupport)
    hV (hG.mono inter_subset_left) (hi.mono inter_subset_left)
    (fun w hw => hd w hw.1) hTV hvV
    (actualExteriorKernel_circleB hR ha hh hi hd hsupport) (v := v) (by
      intro w hw
      have hne : ∀ t : ℂ, 1 ≤ ‖t‖ → G t ≠ G w := by
        intro t ht he
        have htU : t ∈ U := lt_of_lt_of_le
          ((inv_lt_one₀ (lt_trans zero_lt_one hR)).mpr hR) ht
        have htw := hi htU hw.1.1 he
        have hwi : ‖w‖ < 1 := mem_ball_zero_iff.mp hw.2
        exact (not_lt_of_ge (htw ▸ ht)) hwi
      have hm := exterior_cauchy_kernel_integral ha
        (hh.mono (closedBall_subset_ball hR)) hne
      have he := circle_convex_cauchy hΩ hv (hG.mono hTU) hboundary
        (hinner ⟨hw.1.1,hw.2⟩)
        (fun t ht => hne t (le_of_eq (mem_sphere_zero_iff_norm.mp ht).symm)) hm
      change (∫ t : UnitAddCircle, v (G t.toCircle) *
        ((t.toCircle : ℂ)*deriv G t.toCircle/(G t.toCircle-G w))
          ∂AddCircle.haarAddCircle) = v (G w)
      simpa only [mul_comm] using he)
  dsimp only at hp
  convert hp using 1 <;> congr 2 <;> ext t <;> exact hu t


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_FourierExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_46 u_47

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

section
open Set Metric Complex MeasureTheory
open scoped Topology

theorem physicalCauchy_extension {G : ℂ → ℂ} {U Ω : Set ℂ}
    (hU : IsOpen U) (hG : AnalyticOnNhd ℂ G U) (hi : InjOn G U)
    (hd : ∀ w ∈ U, deriv G w ≠ 0) (hTU : sphere 0 1 ⊆ U)
    (hΩ : IsOpen Ω) (hboundary : frontier Ω ⊆ G '' sphere 0 1)
    (houtside : ∀ t ∈ U, G t ∈ Ω → t ∈ ball 0 1)
    (hdis : ∀ t ∈ sphere (0:ℂ) 1, G t ∉ Ω)
    {u : UnitAddCircle → ℂ} (hu : Continuous u) {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q U)
    (he : ∀ w ∈ U ∩ ball 0 1, physicalCauchy G u (G w) =
      q w + cauchyCorrectionIntegral G u w) :
    ∃ v : ℂ → ℂ, AnalyticOnNhd ℂ v (closure Ω) ∧
      EqOn v (physicalCauchy G u) Ω ∧
      ∀ t ∈ sphere (0:ℂ) 1, v (G t) = q t + cauchyCorrectionIntegral G u t := by
  obtain ⟨ho,g,hg,hgU,hgf,hfg⟩ := noncritical_holomorphic_inverse hU hG hi hd
  have hp : AnalyticOnNhd ℂ (physicalCauchy G u) Ω :=
    physicalCauchy_analytic (hG.mono hTU) hu hΩ (by
      intro z hz t he
      exact hdis t.toCircle t.toCircle.property (he ▸ hz))
  have hc := cauchyCorrectionIntegral_analytic hU hG hi hd hTU hu
  let f := fun z => q (g z) + cauchyCorrectionIntegral G u (g z)
  have hf : AnalyticOnNhd ℂ f (G '' U) := (hq.comp hg hgU).add (hc.comp hg hgU)
  obtain ⟨v,hv,hvp,hvf⟩ := analytic_open_gluing hΩ ho hp hf (by
    intro z hz
    have hw := hgU hz.2
    have hgz := hfg z hz.2
    have hwi : g z ∈ ball 0 1 := houtside (g z) hw (by rw [hgz]; exact hz.1)
    dsimp [f]
    rw [← he (g z) ⟨hw,hwi⟩,hgz])
  refine ⟨v,hv.mono ?_,hvp,?_⟩
  · intro z hz
    by_cases hi : z ∈ Ω
    · exact Or.inl hi
    · have hz' : z ∈ frontier Ω := by
        rw [frontier,Set.mem_sdiff]
        exact ⟨hz,by simpa only [hΩ.interior_eq] using hi⟩
      obtain ⟨t,ht,rfl⟩ := hboundary hz'
      exact Or.inr ⟨t,hTU ht,rfl⟩
  · intro t ht
    rw [hvf ⟨t,hTU ht,rfl⟩]
    dsimp [f]
    rw [hgf t (hTU ht)]

theorem physicalCauchy_fourier_extension {G : ℂ → ℂ} {U Ω : Set ℂ}
    (hU : IsOpen U) (hG : AnalyticOnNhd ℂ G U) (hi : InjOn G U)
    (hd : ∀ w ∈ U, deriv G w ≠ 0) (hTU : sphere 0 1 ⊆ U)
    (hΩ : IsOpen Ω) (hboundary : frontier Ω ⊆ G '' sphere 0 1)
    (houtside : ∀ t ∈ U, G t ∈ Ω → t ∈ ball 0 1)
    (hdis : ∀ t ∈ sphere (0:ℂ) 1, G t ∉ Ω) (n : ℤ) :
    ∃ v : ℂ → ℂ, AnalyticOnNhd ℂ v (closure Ω) ∧
      EqOn v (physicalCauchy G (fourier n)) Ω ∧
      ∀ t : UnitAddCircle, v (G t.toCircle) =
        (if 0 ≤ n then fourier n t else 0) +
          cauchyCorrectionIntegral G (fourier n) t.toCircle := by
  have he : ∃ q : ℂ → ℂ, AnalyticOnNhd ℂ q U ∧
      (∀ w ∈ U ∩ ball 0 1, physicalCauchy G (fourier n) (G w) =
        q w + cauchyCorrectionIntegral G (fourier n) w) ∧
      ∀ t : UnitAddCircle, q t.toCircle = if 0 ≤ n then fourier n t else 0 := by
    rcases n with n | n
    · refine ⟨fun w => w^n,analyticOnNhd_id.pow n,?_,?_⟩
      · intro w hw
        have hf : (fourier (Int.ofNat n) : UnitAddCircle → ℂ) =
            (fun t => (t.toCircle : ℂ)^n) := funext (fourier_natCast_toCircle n)
        rw [hf]
        exact physicalCauchy_pow hU hG hi hd hTU n hw.1 hw.2
      · intro t
        change (t.toCircle : ℂ)^n = if 0 ≤ (n:ℤ) then fourier (n:ℤ) t else 0
        rw [ite_eq_left (Int.natCast_nonneg n),fourier_natCast_toCircle]
    · refine ⟨fun _ => 0,analyticOnNhd_const,?_,?_⟩
      · intro w hw
        have hn : Int.negSucc n = -((n+1 : ℕ) : ℤ) := by omega
        rw [hn]
        have hf : (fourier (-((n+1:ℕ):ℤ)) : UnitAddCircle → ℂ) =
            (fun t => ((t.toCircle : ℂ)⁻¹)^(n+1)) :=
          funext (fourier_neg_natCast_toCircle (n+1))
        rw [hf,zero_add]
        exact physicalCauchy_inv_pow hU hG hi hd hTU (Nat.succ_ne_zero n) hw.1 hw.2
      · intro t
        rw [ite_eq_right (by omega : ¬0 ≤ Int.negSucc n)]
  obtain ⟨q,hq,he,hqt⟩ := he
  obtain ⟨v,hv,hvp,hvt⟩ := physicalCauchy_extension hU hG hi hd hTU hΩ hboundary
    houtside hdis (map_continuous (fourier n)) hq he
  exact ⟨v,hv,hvp,fun t => by rw [hvt t.toCircle t.toCircle.property,hqt t]⟩

end

section
open Set Metric Complex MeasureTheory
open scoped Topology

attribute [local instance] OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions_13
lemma scalarCauchy_fourier_ae (K : AnalyticBidiskKernel) (n : ℤ) :
    scalarFourier.cauchy K.scalarM (fourierLp 2 n) =ᵐ[AddCircle.haarAddCircle]
      fun w => (if 0 ≤ n then fourier n w else 0) +
        ∫ t, K.circleB w t * fourier n t ∂AddCircle.haarAddCircle := by
  let u : CircleL2 := fourierLp 2 n
  have hlo : scalarFourier.proj 0 u + scalarFourier.proj 1 u =
      if 0 ≤ n then u else 0 := by
    dsimp [u]
    rw [scalarFourier_fourier,scalarFourier_fourier]
    rcases lt_trichotomy n 0 with hn | hn | hn
    · simp [frequencyPart,hn.ne,not_lt.mpr hn.le,not_le.mpr hn]
    · simp [hn,frequencyPart]
    · simp [frequencyPart,hn.ne',hn,hn.le]
  have he : scalarFourier.cauchy K.scalarM u =
      (if 0 ≤ n then u else 0) + K.scalarM (scalarFourier.proj 1 u) := by
    change scalarFourier.proj 0 u + scalarFourier.proj 1 u + _ = _
    rw [hlo]
    rfl
  rw [show fourierLp 2 n = u from rfl,he]
  filter_upwards [Lp.coeFn_add (if 0 ≤ n then u else 0)
    (K.scalarM (scalarFourier.proj 1 u)),coeFn_fourierLp 2 n,
    Lp.coeFn_zero (E := ℂ) (p := 2) (μ := AddCircle.haarAddCircle),
    K.scalarM_positive_ae u] with w hadd hu hz hM
  rw [hadd]
  simp only [Pi.add_apply]
  rw [hM]
  congr 1
  · split_ifs <;> assumption
  · apply integral_congr_ae
    filter_upwards [coeFn_fourierLp 2 n] with t ht
    rw [show u t = fourier n t from ht]

theorem actualExteriorCauchy_fourier_trace {a b : ℂ} {h : ℂ → ℂ} {R : ℝ}
    (hR : 1 < R) (ha : a ≠ 0) (hh : AnalyticOnNhd ℂ h (ball 0 R))
    (hi : InjOn (exteriorMap a b h) {t | R⁻¹ < ‖t‖})
    (hd : ∀ t, R⁻¹ < ‖t‖ → deriv (exteriorMap a b h) t ≠ 0)
    (hsupport : ∀ w t : Circle,
      0 ≤ (conj ((t : ℂ)*deriv (exteriorMap a b h) t)*
        (exteriorMap a b h t-exteriorMap a b h w)).re)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (hboundary :
      exteriorMap a b h '' sphere 0 1 = frontier Ω)
    (houtside : ∀ t, R⁻¹ < ‖t‖ → exteriorMap a b h t ∈ Ω → t ∈ ball 0 1)
    (n : ℤ) :
    ∃ v : ℂ → ℂ, AnalyticOnNhd ℂ v (closure Ω) ∧
      EqOn v (physicalCauchy (exteriorMap a b h) (fourier n)) Ω ∧
      scalarFourier.cauchy (actualExteriorKernel hR ha hh hi hd hsupport).scalarM
        (fourierLp 2 n) =ᵐ[AddCircle.haarAddCircle]
          fun t => v (exteriorMap a b h t.toCircle) := by
  let G := exteriorMap a b h
  let U : Set ℂ := {t | R⁻¹ < ‖t‖}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_norm
  have hG : AnalyticOnNhd ℂ G U := analyticOnNhd_exteriorMap (lt_trans zero_lt_one hR) hh
  have hTU : sphere (0:ℂ) 1 ⊆ U := by
    intro t ht
    change R⁻¹ < ‖t‖
    rw [mem_sphere_zero_iff_norm.mp ht]
    exact (inv_lt_one₀ (lt_trans zero_lt_one hR)).mpr hR
  have hdis : ∀ t ∈ sphere (0:ℂ) 1, G t ∉ Ω := by
    intro t ht
    have hm : G t ∈ frontier Ω := hboundary ▸ mem_image_of_mem G ht
    simpa only [frontier,hΩ.interior_eq,Set.mem_sdiff] using hm.2
  obtain ⟨v,hv,hvp,hvt⟩ := physicalCauchy_fourier_extension hU hG hi hd hTU hΩ
    (by rw [← hboundary]) houtside hdis n
  refine ⟨v,hv,hvp,?_⟩
  filter_upwards [scalarCauchy_fourier_ae (actualExteriorKernel hR ha hh hi hd hsupport) n]
    with w hw
  rw [hw,hvt]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with point
  rw [actualExteriorKernel_circleB hR ha hh hi hd hsupport]
  exact mul_comm _ _

end

section
open Set Metric Complex MeasureTheory
open scoped Topology

lemma exteriorMap_circle_analytic {a b : ℂ} {h : ℂ → ℂ} {R : ℝ}
    (hR : 1 < R) (hh : AnalyticOnNhd ℂ h (ball 0 R)) :
    AnalyticOnNhd ℂ (exteriorMap a b h) (sphere 0 1) := by
  apply (analyticOnNhd_exteriorMap (a := a) (b := b) (lt_trans zero_lt_one hR) hh).mono
  intro t ht
  change R⁻¹ < ‖t‖
  rw [mem_sphere_zero_iff_norm.mp ht]
  exact (inv_lt_one₀ (lt_trans zero_lt_one hR)).mpr hR

attribute [local instance] OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions_14
theorem actualExteriorCauchy_module {a b : ℂ} {h : ℂ → ℂ} {R : ℝ}
    (hR : 1 < R) (ha : a ≠ 0) (hh : AnalyticOnNhd ℂ h (ball 0 R))
    (hi : InjOn (exteriorMap a b h) {t | R⁻¹ < ‖t‖})
    (hd : ∀ t, R⁻¹ < ‖t‖ → deriv (exteriorMap a b h) t ≠ 0)
    (hsupport : ∀ w t : Circle,
      0 ≤ (conj ((t : ℂ)*deriv (exteriorMap a b h) t)*
        (exteriorMap a b h t-exteriorMap a b h w)).re)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω)
    (hboundary : exteriorMap a b h '' sphere 0 1 = frontier Ω)
    (houtside : ∀ t, R⁻¹ < ‖t‖ → exteriorMap a b h t ∈ Ω → t ∈ ball 0 1)
    (hinner : MapsTo (exteriorMap a b h) ({t | R⁻¹ < ‖t‖} ∩ ball 0 1) (closure Ω))
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (closure Ω))
    (T : CircleL2 →L[ℂ] CircleL2)
    (hT : ∀ u : CircleL2, T u =ᵐ[AddCircle.haarAddCircle]
      fun t => f (exteriorMap a b h t.toCircle)*u t) :
    (scalarFourier.cauchy (actualExteriorKernel hR ha hh hi hd hsupport).scalarM).comp
      (T.comp (scalarFourier.cauchy (actualExteriorKernel hR ha hh hi hd hsupport).scalarM)) =
      T.comp (scalarFourier.cauchy (actualExteriorKernel hR ha hh hi hd hsupport).scalarM) := by
  let G := exteriorMap a b h
  let C := scalarFourier.cauchy (actualExteriorKernel hR ha hh hi hd hsupport).scalarM
  have hG : AnalyticOnNhd ℂ G (sphere 0 1) := exteriorMap_circle_analytic hR hh
  have hb : MapsTo G (sphere 0 1) (closure Ω) := by
    intro t ht
    apply frontier_subset_closure
    rw [← hboundary]
    exact mem_image_of_mem G ht
  apply circleCLM_ext
  intro n
  change C (T (C (fourierLp 2 n))) = T (C (fourierLp 2 n))
  obtain ⟨v,hv,_,hvt⟩ := actualExteriorCauchy_fourier_trace hR ha hh hi hd hsupport
    hΩ hboundary houtside n
  let u := physicalAnalyticTrace hG hb (fun z => f z*v z) (hf.mul hv)
  have hTu : T (C (fourierLp 2 n)) = ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ u := by
    apply Lp.ext
    filter_upwards [hT (C (fourierLp 2 n)),hvt,
      ContinuousMap.coeFn_toLp (μ := AddCircle.haarAddCircle) (p := 2) (𝕜 := ℂ) u]
      with t hTt hvt hut
    rw [hTt,hvt,hut]
    rfl
  rw [hTu]
  exact actualExteriorCauchy_fix_trace hR ha hh hi hd hsupport hcv.closure hb hinner
    (hf.mul hv) u (fun _ => rfl)

end

open MeasureTheory


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

section

variable {m : Type u_48} [Fintype m] [instDecidableEqM : DecidableEq m]

lemma hs_left_contraction {A : Matrix m m ℂ} (hA : ‖A‖ ≤ 1) (B : Matrix m m ℂ) :
    ‖toHS (A * B)‖ ≤ ‖toHS B‖ := by
  have hnorm : ‖Aᴴ * A‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_conjTranspose_mul_self]
    nlinarith [norm_nonneg A]
  have hle : Aᴴ * A ≤ 1 := by
    apply (CStarAlgebra.norm_le_one_iff_of_nonneg (Aᴴ * A)
      (Matrix.posSemidef_conjTranspose_mul_self A).nonneg).mp hnorm
  have hd : (1 - Aᴴ * A).PosSemidef := hle
  have ht := (hd.conjTranspose_mul_mul_same B).trace_nonneg
  have hr := (Complex.nonneg_iff.mp ht).1
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.trace_sub, Complex.sub_re] at hr
  have hsq : hsSq (A * B) ≤ hsSq B := by
    unfold hsSq
    rw [Matrix.conjTranspose_mul]
    simpa only [Matrix.mul_assoc] using sub_nonneg.mp hr
  rw [← norm_toHS_sq, ← norm_toHS_sq] at hsq
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

lemma hs_right_contraction {A : Matrix m m ℂ} (hA : ‖A‖ ≤ 1) (B : Matrix m m ℂ) :
    ‖toHS (B * A)‖ ≤ ‖toHS B‖ := by
  have h := hs_left_contraction (A := Aᴴ) (by simpa only [Matrix.l2_opNorm_conjTranspose] using hA) Bᴴ
  have hnorm (C : Matrix m m ℂ) : ‖toHS Cᴴ‖ = ‖toHS C‖ := by
    simpa only [hsStar_apply, fromHS_toHS] using hsStar.norm_map (toHS C)
  rw [← Matrix.conjTranspose_mul, hnorm, hnorm] at h
  exact h

open MeasureTheory

end

section
open scoped InnerProductSpace
variable {m : Type u_51} [Fintype m] [instDecidableEqM : DecidableEq m]

lemma hsLeft_norm {A : Matrix m m ℂ} (h : ‖A‖ ≤ 1) : ‖hsLeft A‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro B
  simpa using hs_left_contraction h (fromHS B)
lemma hsRight_norm {A : Matrix m m ℂ} (h : ‖A‖ ≤ 1) : ‖hsRight A‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro B
  simpa using hs_right_contraction h (fromHS B)

end

open MeasureTheory
variable {α : Type u_52} {E : Type u_53} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (B : α → E →L[ℂ] E) (hB : AEStronglyMeasurable B μ)
  (hBn : ∀ᵐ t ∂μ, ‖B t‖ ≤ 1)

lemma pointwiseL2L_norm : ‖pointwiseL2L B hB hBn‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa [pointwiseL2L] using pointwiseL2_norm B hB hBn u


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_OrderedMultiplication
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u_54 u_55 u_56 u_57 u_58 u_59 u_60

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

namespace CompleteCrouzeix

section

section

section

open MeasureTheory

variable {m : Type u_55} [Fintype m] [DecidableEq m]

attribute [local instance] OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions_15
lemma coordinate_matrixFourier (j : Fin 3) (u : MatrixCircleL2 (m := m)) (i : m × m) :
    l2Coordinate i (matrixFourier.proj j u) = scalarFourier.proj j (l2Coordinate i u) :=
  coordinate_entrywise _ _ _

end

open MeasureTheory
local instance instFactLtRealOfNat_solutions_16 : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
namespace AnalyticBidiskKernel
variable (K : AnalyticBidiskKernel)
variable {m : Type u_56} [Fintype m] [instDecidableEqM : DecidableEq m]

lemma coordinate_matrixM (u : MatrixCircleL2 (m := m)) (i : m × m) :
    l2Coordinate i (K.matrixM u) = K.scalarM (l2Coordinate i u) := by
  apply Lp.ext
  filter_upwards [K.toMarkovKernel.applyLp_ae (l2Coordinate i u),
    K.toMarkovKernel.applyLp_ae u, l2Coordinate_ae i (K.matrixM u)] with t h1 h2 h3
  rw [h3]
  change (K.toMarkovKernel.applyLp u t) i = K.toMarkovKernel.applyLp (l2Coordinate i u) t
  rw [h1,h2]
  unfold MarkovKernel.applyFun
  change (EuclideanSpace.proj (𝕜 := ℂ) i) (∫ y, K.toMarkovKernel.kernel t y • u y ∂AddCircle.haarAddCircle) = _
  rw [← (EuclideanSpace.proj (𝕜 := ℂ) i).integral_comp_comm
    (K.toMarkovKernel.integrable_row_smul u t)]
  apply integral_congr_ae
  filter_upwards [l2Coordinate_ae i u] with s hs
  rw [hs]
  rfl

end AnalyticBidiskKernel
end

open Set Metric Complex MeasureTheory
open scoped Topology
variable {ι : Type u_57} [Fintype ι] [DecidableEq ι]
local notation "V" => VectorL2 (μ := @AddCircle.haarAddCircle 1 inferInstance) (ι := ι)

attribute [local instance] OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions_17
lemma l2_sum_embedding_coordinate (u : V) :
    ∑ i, l2Embedding i (l2Coordinate i u) = u := by
  apply l2Coordinate_injective
  intro j
  simp only [map_sum,coordinate_embedding]
  simp

lemma entrywise_embedding (C : CircleL2 →L[ℂ] CircleL2) (j : ι) (u : CircleL2) :
    entrywiseL2 C (l2Embedding j u) = l2Embedding j (C u) := by
  apply l2Coordinate_injective
  intro i
  rw [coordinate_entrywise,coordinate_embedding,coordinate_embedding]
  split_ifs <;> simp

lemma entrywise_module_of_blocks (C : CircleL2 →L[ℂ] CircleL2) (T : V →L[ℂ] V)
    (h : ∀ i j : ι, C.comp (((l2Coordinate i).comp (T.comp (l2Embedding j))).comp C) =
      ((l2Coordinate i).comp (T.comp (l2Embedding j))).comp C) :
    (entrywiseL2 C).comp (T.comp (entrywiseL2 C)) = T.comp (entrywiseL2 C) := by
  ext1 u
  apply l2Coordinate_injective
  intro i
  change l2Coordinate i (entrywiseL2 C (T (entrywiseL2 C u))) =
    l2Coordinate i (T (entrywiseL2 C u))
  rw [coordinate_entrywise]
  rw [← l2_sum_embedding_coordinate u]
  simp only [map_sum,entrywise_embedding]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun L : CircleL2 →L[ℂ] CircleL2 => L (l2Coordinate j u)) (h i j)

theorem actualExteriorCauchy_vector_module {a b : ℂ} {h : ℂ → ℂ} {R : ℝ}
    (hR : 1 < R) (ha : a ≠ 0) (hh : AnalyticOnNhd ℂ h (ball 0 R))
    (hi : InjOn (exteriorMap a b h) {t | R⁻¹ < ‖t‖})
    (hd : ∀ t, R⁻¹ < ‖t‖ → deriv (exteriorMap a b h) t ≠ 0)
    (hsupport : ∀ w t : Circle,
      0 ≤ (conj ((t : ℂ)*deriv (exteriorMap a b h) t)*
        (exteriorMap a b h t-exteriorMap a b h w)).re)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω)
    (hboundary : exteriorMap a b h '' sphere 0 1 = frontier Ω)
    (houtside : ∀ t, R⁻¹ < ‖t‖ → exteriorMap a b h t ∈ Ω → t ∈ ball 0 1)
    (hinner : MapsTo (exteriorMap a b h) ({t | R⁻¹ < ‖t‖} ∩ ball 0 1) (closure Ω))
    {B : ℂ → EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι}
    (hB : AnalyticOnNhd ℂ B (closure Ω))
    (T : V →L[ℂ] V)
    (hT : ∀ u : V, T u =ᵐ[AddCircle.haarAddCircle]
      fun t => B (exteriorMap a b h t.toCircle) (u t)) :
    (entrywiseL2 (scalarFourier.cauchy (actualExteriorKernel hR ha hh hi hd hsupport).scalarM)).comp
      (T.comp (entrywiseL2 (scalarFourier.cauchy (actualExteriorKernel hR ha hh hi hd hsupport).scalarM))) =
      T.comp (entrywiseL2 (scalarFourier.cauchy (actualExteriorKernel hR ha hh hi hd hsupport).scalarM)) := by
  apply entrywise_module_of_blocks
  intro i j
  let φ : (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) →L[ℂ] ℂ :=
    (EuclideanSpace.proj i).comp ((ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ ι))
      (EuclideanSpace.single j 1))
  have hφ : AnalyticOnNhd ℂ (fun z => φ (B z)) (closure Ω) :=
    (φ.analyticOnNhd univ).comp hB (mapsTo_univ _ _)
  apply actualExteriorCauchy_module hR ha hh hi hd hsupport hΩ hcv hboundary houtside hinner hφ
  intro u
  filter_upwards [l2Coordinate_ae i (T (l2Embedding j u)),hT (l2Embedding j u),
    l2Embedding_ae j u] with t hcoord hTt hemb
  change l2Coordinate i (T (l2Embedding j u)) t = _
  rw [hcoord,hTt,hemb]
  have he : EuclideanSpace.single j (u t) = u t • EuclideanSpace.single j (1:ℂ) := by
    ext k
    simp only [PiLp.single_apply,PiLp.smul_apply,smul_eq_mul]
    split_ifs <;> simp
  rw [he,map_smul]
  change u t * φ (B (exteriorMap a b h t.toCircle)) = _
  exact mul_comm _ _

end

open Set Metric Complex MeasureTheory
open scoped Topology

attribute [local instance] OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions_18
lemma matrixCauchy_eq_entrywise {m : Type u_58} [Fintype m] [DecidableEq m]
    (K : AnalyticBidiskKernel) :
    (matrixFourier.cauchy K.matrixM : MatrixCircleL2 (m := m) →L[ℂ] _) =
      entrywiseL2 (scalarFourier.cauchy K.scalarM) := by
  ext1 u
  apply l2Coordinate_injective
  intro i
  simp only [FourierResolution.cauchy,add_apply,ContinuousLinearMap.comp_apply,
    map_add,coordinate_matrixFourier,K.coordinate_matrixM,coordinate_entrywise]

section ActualFields
variable {ι : Type u_59} [Fintype ι] [DecidableEq ι]
local notation "V" => VectorL2 (μ := @AddCircle.haarAddCircle 1 inferInstance) (ι := ι)

attribute [local instance] OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions_18
theorem actualExteriorCauchy_field_module {a b : ℂ} {h : ℂ → ℂ} {R : ℝ}
    (hR : 1 < R) (ha : a ≠ 0) (hh : AnalyticOnNhd ℂ h (ball 0 R))
    (hi : InjOn (exteriorMap a b h) {t | R⁻¹ < ‖t‖})
    (hd : ∀ t, R⁻¹ < ‖t‖ → deriv (exteriorMap a b h) t ≠ 0)
    (hsupport : ∀ w t : Circle,
      0 ≤ (conj ((t : ℂ)*deriv (exteriorMap a b h) t)*
        (exteriorMap a b h t-exteriorMap a b h w)).re)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω)
    (hboundary : exteriorMap a b h '' sphere 0 1 = frontier Ω)
    (houtside : ∀ t, R⁻¹ < ‖t‖ → exteriorMap a b h t ∈ Ω → t ∈ ball 0 1)
    (hinner : MapsTo (exteriorMap a b h) ({t | R⁻¹ < ‖t‖} ∩ ball 0 1) (closure Ω))
    {B : ℂ → EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι}
    (hB : AnalyticOnNhd ℂ B (closure Ω))
    (hn : ∀ t : UnitAddCircle, ‖B (exteriorMap a b h t.toCircle)‖ ≤ 1) :
    ∃ T : V →L[ℂ] V, ‖T‖ ≤ 1 ∧
      (∀ u : V, T u =ᵐ[AddCircle.haarAddCircle]
        fun t => B (exteriorMap a b h t.toCircle) (u t)) ∧
      (entrywiseL2 (scalarFourier.cauchy (actualExteriorKernel hR ha hh hi hd hsupport).scalarM)).comp
        (T.comp (entrywiseL2 (scalarFourier.cauchy (actualExteriorKernel hR ha hh hi hd hsupport).scalarM))) =
        T.comp (entrywiseL2 (scalarFourier.cauchy (actualExteriorKernel hR ha hh hi hd hsupport).scalarM)) := by
  have hb : MapsTo (exteriorMap a b h) (sphere 0 1) (closure Ω) := by
    intro t ht
    apply frontier_subset_closure
    rw [← hboundary]
    exact mem_image_of_mem _ ht
  have hBcont : Continuous (fun t : UnitAddCircle => B (exteriorMap a b h t.toCircle)) :=
    (hB.comp (exteriorMap_circle_analytic hR hh) hb).continuousOn.comp_continuous
      (continuous_subtype_val.comp AddCircle.continuous_toCircle) (fun t => t.toCircle.property)
  let T : V →L[ℂ] V := pointwiseL2L (fun t : UnitAddCircle => B (exteriorMap a b h t.toCircle))
    hBcont.aestronglyMeasurable (Filter.Eventually.of_forall hn)
  have hT : ∀ u : V, T u =ᵐ[AddCircle.haarAddCircle]
      fun t => B (exteriorMap a b h t.toCircle) (u t) :=
    fun u => pointwiseL2_ae _ hBcont.aestronglyMeasurable (Filter.Eventually.of_forall hn) u
  exact ⟨T,pointwiseL2L_norm _ hBcont.aestronglyMeasurable (Filter.Eventually.of_forall hn),hT,
    actualExteriorCauchy_vector_module hR ha hh hi hd hsupport hΩ hcv hboundary houtside hinner hB T hT⟩

end ActualFields

theorem actualExteriorCauchy_ordered_modules {m : Type u_60} [Fintype m] [DecidableEq m]
    {a b : ℂ} {h : ℂ → ℂ} {R : ℝ}
    (hR : 1 < R) (ha : a ≠ 0) (hh : AnalyticOnNhd ℂ h (ball 0 R))
    (hi : InjOn (exteriorMap a b h) {t | R⁻¹ < ‖t‖})
    (hd : ∀ t, R⁻¹ < ‖t‖ → deriv (exteriorMap a b h) t ≠ 0)
    (hsupport : ∀ w t : Circle,
      0 ≤ (conj ((t : ℂ)*deriv (exteriorMap a b h) t)*
        (exteriorMap a b h t-exteriorMap a b h w)).re)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω)
    (hboundary : exteriorMap a b h '' sphere 0 1 = frontier Ω)
    (houtside : ∀ t, R⁻¹ < ‖t‖ → exteriorMap a b h t ∈ Ω → t ∈ ball 0 1)
    (hinner : MapsTo (exteriorMap a b h) ({t | R⁻¹ < ‖t‖} ∩ ball 0 1) (closure Ω))
    {F : ℂ → Matrix m m ℂ} (hF : AnalyticOnNhd ℂ F (closure Ω))
    (hn : ∀ t : UnitAddCircle, ‖F (exteriorMap a b h t.toCircle)‖ ≤ 1) :
    let C : MatrixCircleL2 (m := m) →L[ℂ] _ :=
      matrixFourier.cauchy (actualExteriorKernel hR ha hh hi hd hsupport).matrixM
    ∃ L R : MatrixCircleL2 (m := m) →L[ℂ] MatrixCircleL2 (m := m),
      ‖L‖ ≤ 1 ∧ ‖R‖ ≤ 1 ∧
      (∀ u, L u =ᵐ[AddCircle.haarAddCircle]
        fun t => toHS (F (exteriorMap a b h t.toCircle)*fromHS (u t))) ∧
      (∀ u, R u =ᵐ[AddCircle.haarAddCircle]
        fun t => toHS (fromHS (u t)*F (exteriorMap a b h t.toCircle))) ∧
      C.comp (L.comp C) = L.comp C ∧ C.comp (R.comp C) = R.comp C := by
  let BL := fun z => hsLeft (F z)
  let BR := fun z => hsRight (F z)
  have hBL : AnalyticOnNhd ℂ BL (closure Ω) :=
    ((hsLeftL (m := m)).analyticOnNhd univ).comp hF (mapsTo_univ _ _)
  have hBR : AnalyticOnNhd ℂ BR (closure Ω) :=
    ((hsRightL (m := m)).analyticOnNhd univ).comp hF (mapsTo_univ _ _)
  obtain ⟨L,hLn,hLa,hLC⟩ := actualExteriorCauchy_field_module hR ha hh hi hd hsupport
    hΩ hcv hboundary houtside hinner hBL (fun t => hsLeft_norm (hn t))
  obtain ⟨T,hTn,hTa,hTC⟩ := actualExteriorCauchy_field_module hR ha hh hi hd hsupport
    hΩ hcv hboundary houtside hinner hBR (fun t => hsRight_norm (hn t))
  refine ⟨L,T,hLn,hTn,hLa,hTa,?_,?_⟩
  · simpa only [matrixCauchy_eq_entrywise] using hLC
  · simpa only [matrixCauchy_eq_entrywise] using hTC

end CompleteCrouzeix

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
lemma outside_imp (t : ℂ) (ht : D.exterior.radius⁻¹ < ‖t‖) (hz : D.G t ∈ D.domain) :
    t ∈ ball (0:ℂ) 1 := (D.exterior.interior_iff t ht).mp hz
lemma inner_maps : MapsTo D.G ({t | D.exterior.radius⁻¹ < ‖t‖} ∩ ball 0 1) (closure D.domain) := by
  intro t ht
  exact subset_closure ((D.exterior.interior_iff t ht.1).mpr ht.2)
end AdmissibleDomain
end CompleteCrouzeix

end

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
lemma ordered_modules_oai {F : ℂ → Matrix m m ℂ} (hF : AnalyticOnNhd ℂ F (closure D.domain))
    (hn : ∀ z ∈ closure D.domain, ‖F z‖ ≤ 1) :
    ∃ L R : MatrixCircleL2 (m := m) →L[ℂ] MatrixCircleL2 (m := m),
      ‖L‖ ≤ 1 ∧ ‖R‖ ≤ 1 ∧
      (∀ u, L u =ᵐ[AddCircle.haarAddCircle] fun t => toHS (D.trace F hF t*fromHS (u t))) ∧
      (∀ u, R u =ᵐ[AddCircle.haarAddCircle] fun t => toHS (fromHS (u t)*D.trace F hF t)) ∧
      D.cauchy.comp (L.comp D.cauchy) = L.comp D.cauchy ∧
      D.cauchy.comp (R.comp D.cauchy) = R.comp D.cauchy :=
  actualExteriorCauchy_ordered_modules D.exterior.radius_gt D.exterior.leading_ne
    D.exterior.analytic_regular D.exterior.injective D.exterior.noncritical D.support_circle
    D.isOpen D.convex D.exterior.boundary_image D.outside_imp D.inner_maps hF
    (fun t => hn _ (D.G_boundary (by simp [Circle.norm_coe])).1)
end AdmissibleDomain
end CompleteCrouzeix

end

end

end OAI
end

theorem solution.{u_256} : type_of% @OAI.CompleteCrouzeix.AdmissibleDomain.ordered_modules_oai.{u_256} := @OAI.CompleteCrouzeix.AdmissibleDomain.ordered_modules_oai.{u_256}
