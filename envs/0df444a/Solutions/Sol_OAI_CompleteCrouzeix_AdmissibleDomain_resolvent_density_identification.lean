-- Prove2me | solution 1 for OAI.CompleteCrouzeix.AdmissibleDomain.resolvent_density_identification
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T02:35:50.142377+00:00
-- url     : https://prove2.me/submissions/9307ae25-f7dd-47af-8e8e-eccd04bb8ba3

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

end CompleteCrouzeix

open Set Metric Filter Complex
open scoped Topology

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

open MeasureTheory Set Complex Metric
open scoped Topology

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
open scoped InnerProductSpace
variable {m : Type u_51} [Fintype m] [instDecidableEqM : DecidableEq m]

lemma hs_inner
    {m : Type u_51} [Fintype m] [DecidableEq m] (A B : Matrix m m ℂ) :
    inner ℂ (toHS A) (toHS B) = Matrix.trace (Aᴴ * B) := by
  simp only [PiLp.inner_apply, Fintype.sum_prod_type, RCLike.inner_apply,
    Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    toHS]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

end

open MeasureTheory


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

attribute [local instance] OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions_17
lemma entrywise_embedding (C : CircleL2 →L[ℂ] CircleL2) (j : ι) (u : CircleL2) :
    entrywiseL2 C (l2Embedding j u) = l2Embedding j (C u) := by
  apply l2Coordinate_injective
  intro i
  rw [coordinate_entrywise,coordinate_embedding,coordinate_embedding]
  split_ifs <;> simp

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

lemma primaryEval_intertwine (S T L : Module.End ℂ V)
    (h : ∀ x, T (L x) = L (S x)) (f : ℂ → ℂ) :
    primaryEval T f * L = L * primaryEval S f := by
  apply primary_end_ext (T := S)
  intro β x
  have hsub (y : V) :
      (T - algebraMap ℂ (Module.End ℂ V) β) (L y) =
        L ((S - algebraMap ℂ (Module.End ℂ V) β) y) := by
    simp only [LinearMap.sub_apply, algebraMap_end_apply, map_sub, map_smul, h]
  have hp (k : ℕ) (y : V) :
      ((T - algebraMap ℂ (Module.End ℂ V) β)^k) (L y) =
        L (((S - algebraMap ℂ (Module.End ℂ V) β)^k) y) := by
    induction k generalizing y with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, hsub, pow_succ', Module.End.mul_apply]
  have hx : L (x : V) ∈ T.maxGenEigenspace β := by
    have he := x.property
    simp only [Module.End.maxGenEigenspace_eq_genEigenspace_finrank,
      Module.End.mem_genEigenspace_nat, LinearMap.mem_ker] at he ⊢
    simpa only [Algebra.algebraMap_eq_smul_one, he, map_zero] using hp (finrank ℂ V) x
  change primaryEval T f (L x) = L (primaryEval S f x)
  rw [primaryEval_on_generalized T f β ⟨L x, hx⟩, primaryEval_on_generalized S f β x]
  exact scalarJetEval_intertwine L _ _ hsub β (finrank ℂ V) f x


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

lemma integral_conjTranspose {X : Type u_78} [MeasurableSpace X] {μ : Measure X}
    {L : X → Matrix n n ℂ} (hL : Integrable L μ) :
    (∫ t, (L t)ᴴ ∂μ) = (∫ t, L t ∂μ)ᴴ :=
  conjTransposeRCLM.integral_comp_comm hL

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

lemma matrixAnalyticEval_intertwine (A B L : Matrix n n ℂ) (hL : A*L=L*B) (f : ℂ → ℂ) :
    matrixAnalyticEval A f * L = L * matrixAnalyticEval B f := by
  apply Matrix.toLinAlgEquiv'.injective
  simp only [map_mul, matrixAnalyticEval, AlgEquiv.apply_symm_apply]
  apply primaryEval_intertwine
  intro x
  have he := congrArg (Matrix.toLinAlgEquiv' : Matrix n n ℂ ≃ₐ[ℂ] Module.End ℂ (n → ℂ)) hL
  simp only [map_mul] at he
  exact LinearMap.congr_fun he x

lemma matrixAnalyticEval_similarity {S : Matrix n n ℂ} (hS : IsUnit S)
    (A : Matrix n n ℂ) (f : ℂ → ℂ) :
    matrixAnalyticEval (S*A*S⁻¹) f = S*matrixAnalyticEval A f*S⁻¹ := by
  have hi : S⁻¹*S=1 := Matrix.nonsing_inv_mul S ((Matrix.isUnit_iff_isUnit_det S).mp hS)
  have hi' : S*S⁻¹=1 := Matrix.mul_nonsing_inv S ((Matrix.isUnit_iff_isUnit_det S).mp hS)
  have he := matrixAnalyticEval_intertwine (S*A*S⁻¹) A S (by rw [mul_assoc, mul_assoc, hi, mul_one]) f
  have h := congrArg (fun M => M*S⁻¹) he
  simpa only [mul_assoc, hi', mul_one] using h

lemma completeAnalyticEval_similarity {S : Matrix n n ℂ} (hS : IsUnit S)
    (A : Matrix n n ℂ) (F : ℂ → Matrix m m ℂ) :
    completeAnalyticEval (S*A*S⁻¹) F = (S ⊗ₖ (1 : Matrix m m ℂ)) *
      completeAnalyticEval A F * (S⁻¹ ⊗ₖ (1 : Matrix m m ℂ)) := by
  ext i j
  simp only [completeAnalyticEval, matrixAnalyticEval_similarity hS, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    ite_mul, zero_mul, Finset.sum_ite_eq]

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

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Kronecker

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
section
variable {n : Type u_206} {m : Type u_207} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

lemma weightedDensity_star
    {n : Type u_206} {m : Type u_207} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (L : Matrix n n ℂ) (X Y : Matrix n m ℂ) :
    (weightedDensity L X Y)ᴴ = weightedDensity Lᴴ Y X := by
  simp only [weightedDensity, Matrix.conjTranspose_transpose_eq_transpose_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

lemma inner_vectorize
    {n : Type u_206} {m : Type u_207} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (X Y : Matrix n m ℂ) :
    inner ℂ (vectorize X) (vectorize Y) = (Xᴴ*Y).trace := by
  simp only [vectorize, PiLp.inner_apply, RCLike.inner_apply, Fintype.sum_prod_type,
    Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change Y j i * (starRingEnd ℂ) (X j i) = (starRingEnd ℂ) (X j i) * Y j i
  exact mul_comm _ _

theorem weightedDensity_testing {L : Matrix n n ℂ} (hL : L.IsHermitian)
    (X Y : Matrix n m ℂ) (u : Matrix m m ℂ) :
    ((weightedDensity L X Y)ᴴ*u).trace =
      inner ℂ (vectorize Y) (Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ)
        (L ⊗ₖ u) (vectorize X)) := by
  rw [weightedDensity_star, hL.eq, kronecker_vectorize, inner_vectorize]
  simp only [weightedDensity, Matrix.mul_assoc]
  calc
    _ = ((Yᴴ * (L * X)) * uᵀ).trace := by
      simpa only [Matrix.transpose_transpose] using
        Matrix.trace_transpose_mul (Yᴴ * (L * X)) uᵀ
    _ = _ := by simp only [Matrix.mul_assoc]

end

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_DensityTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section


universe u_215 u_216 u_217 u_218 u_219 u_220 u_221 u_222 u_223 u_224 u_225 u_226 u_227 u_228 u_229 u_230 u_231 u_232 u_233 u_234 u_235 u_236 u_237 u_238 u_239 u_240

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


open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
open MeasureTheory

namespace CompleteCrouzeix

section
open MeasureTheory
open scoped Matrix.Norms.L2Operator Kronecker ComplexConjugate InnerProductSpace
variable {T : Type u_236} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T]
  [BorelSpace T] {μ : Measure T} [IsFiniteMeasure μ]
  {n : Type u_237} {m : Type u_238} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

lemma densityField_ae (L : C(T,Matrix n n ℂ)) (X Y : Matrix n m ℂ) :
    densityField (μ := μ) L X Y =ᵐ[μ]
      fun t => toHS (weightedDensity (L t) X Y) :=
  ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ _

lemma densityField_inner_continuous (L : C(T,Matrix n n ℂ))
    (hL : ∀ t, (L t).IsHermitian) (X Y : Matrix n m ℂ)
    (u : C(T,Matrix m m ℂ)) :
    inner ℂ (densityField (μ := μ) L X Y)
      (ContinuousMap.toLp 2 μ ℂ ⟨fun t => toHS (u t),toHSCLM.continuous.comp u.continuous⟩) =
      ∫ t, inner ℂ (vectorize Y)
        (Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) (L t ⊗ₖ u t) (vectorize X)) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [densityField_ae (μ := μ) L X Y,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ
      (⟨fun t => toHS (u t),toHSCLM.continuous.comp u.continuous⟩ : C(T,HSMatrix m))] with t ht hu
  rw [ht,hu]
  change inner ℂ (toHS (weightedDensity (L t) X Y)) (toHS (u t)) = _
  rw [hs_inner,weightedDensity_testing (hL t)]

lemma densityField_testing (L : C(T,Matrix n n ℂ))
    (hL : ∀ t, (L t).IsHermitian) (X Y : Matrix n m ℂ)
    (u : C(T,Matrix m m ℂ)) :
    inner ℂ (densityField (μ := μ) L X Y)
      (ContinuousMap.toLp 2 μ ℂ ⟨fun t => toHS (u t),toHSCLM.continuous.comp u.continuous⟩) =
      tensorTesting X Y (∫ t, L t ⊗ₖ u t ∂μ) := by
  rw [densityField_inner_continuous L hL X Y u]
  have hc : Continuous (fun t => L t ⊗ₖ u t) := by
    apply continuous_matrix
    intro i j
    change Continuous (fun t => L t i.1 j.1 * u t i.2 j.2)
    fun_prop
  have hi : Integrable (fun t => L t ⊗ₖ u t) μ :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change (∫ t, tensorTesting X Y (L t ⊗ₖ u t) ∂μ) = _
  exact (tensorTesting X Y).integral_comp_comm hi

end

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate Matrix.Norms.L2Operator Kronecker
variable {m : Type u_239} {n : Type u_240} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

attribute [local instance] OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions_52
lemma hsTraceLp_ae
    {m : Type u_239} [Fintype m] [DecidableEq m] (u : C(UnitAddCircle,Matrix m m ℂ)) :
    hsTraceLp u =ᵐ[AddCircle.haarAddCircle] fun t => toHS (u t) :=
  ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle _

lemma hsTraceLp_star (u : C(UnitAddCircle,Matrix m m ℂ)) :
    l2Star (hsTraceLp u) = hsTraceLp ⟨fun t => (u t)ᴴ,by fun_prop⟩ := by
  apply Lp.ext
  filter_upwards [l2StarL_ae (hsTraceLp u),hsTraceLp_ae u,
    hsTraceLp_ae (⟨fun t => (u t)ᴴ,by fun_prop⟩ : C(UnitAddCircle,Matrix m m ℂ))]
    with t ht hu hv
  change l2StarL (hsTraceLp u) t = _
  rw [ht,hu,hv]
  rfl

lemma matrixInner_ext_fourier {u v : MatrixCircleL2 (m := m)}
    (h : ∀ (ij : m × m) (k : ℤ),
      inner ℂ u (l2Embedding ij (fourierLp 2 k)) =
        inner ℂ v (l2Embedding ij (fourierLp 2 k))) : u = v := by
  apply l2Coordinate_injective
  intro ij
  have he : innerSL ℂ (l2Coordinate ij u) = innerSL ℂ (l2Coordinate ij v) := by
    apply circleCLM_ext
    intro k
    simpa only [innerSL_apply_apply,coordinate_inner] using h ij k
  exact innerSL_inj.mp he

lemma hsTraceLp_matrixFourierTrace (ij : m × m) (k : ℤ) :
    hsTraceLp (matrixFourierTrace ij k) = l2Embedding ij (fourierLp 2 k) := by
  apply Lp.ext
  filter_upwards [hsTraceLp_ae (matrixFourierTrace ij k),
    l2Embedding_ae ij (fourierLp (T := 1) 2 k),coeFn_fourierLp (T := 1) 2 k]
    with t hu hv hk
  rw [hu,hv,hk]
  apply PiLp.ext
  rintro ⟨i,j⟩
  simp only [toHS,matrixFourierTrace,ContinuousMap.coe_mk,
    Matrix.single_apply,PiLp.single_apply]
  rcases ij with ⟨i',j'⟩
  simp only [Prod.mk.injEq,eq_comm]

lemma densityInner_ext_fourier {u v : MatrixCircleL2 (m := m)}
    (h : ∀ (ij : m × m) (k : ℤ),
      inner ℂ u (hsTraceLp (matrixFourierTrace ij k)) =
        inner ℂ v (hsTraceLp (matrixFourierTrace ij k))) : u = v :=
  matrixInner_ext_fourier (by simpa only [hsTraceLp_matrixFourierTrace] using h)

lemma l2Star_inner (u v : MatrixCircleL2 (m := m)) :
    inner ℂ (l2Star u) (l2Star v) = conj (inner ℂ u v) := by
  rw [inner_conj_symm]
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [l2StarL_ae u,l2StarL_ae v] with t hu hv
  change inner ℂ (l2StarL u t) (l2StarL v t) = _
  rw [hu,hv,hsStar_apply,hsStar_apply]
  conv_rhs => rw [← toHS_fromHS (v t),← toHS_fromHS (u t)]
  rw [hs_inner,hs_inner,Matrix.conjTranspose_conjTranspose,Matrix.trace_mul_comm]

theorem density_adjoint_identification (C : MatrixCircleL2 (m := m) →L[ℂ] _)
    (p e : MatrixCircleL2 (m := m)) (a b : ℝ)
    (htest : ∀ ij k,
      inner ℂ e (hsTraceLp (matrixFourierTrace ij k)) =
        (a:ℂ)*inner ℂ p (C (hsTraceLp (matrixFourierTrace ij k))) +
        (b:ℂ)*conj (inner ℂ (l2Star p) (C (l2Star (hsTraceLp (matrixFourierTrace ij k)))))) :
    e = (a:ℂ) • C.adjoint p + (b:ℂ) • l2Star (C.adjoint (l2Star p)) := by
  apply densityInner_ext_fourier
  intro ij k
  rw [htest]
  simp only [inner_add_left,inner_smul_left,Complex.conj_ofReal,
    ContinuousLinearMap.adjoint_inner_left]
  congr 1
  have hj := l2Star_inner (C.adjoint (l2Star p))
    (l2Star (hsTraceLp (matrixFourierTrace ij k)))
  have he : l2Star (l2Star (hsTraceLp (matrixFourierTrace ij k))) =
      hsTraceLp (matrixFourierTrace ij k) := l2StarL_involutive _
  rw [he,ContinuousLinearMap.adjoint_inner_left] at hj
  exact congrArg (fun z : ℂ => (b:ℂ)*z) hj.symm

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
variable {n : Type u_245} {m : Type u_246} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
attribute [local instance] OAI.CompleteCrouzeix.AdmissibleDomain.instFactLtRealOfNat
lemma fourier_cauchy (ij : m × m) (k : ℤ) :
    ∃ (v : ℂ → Matrix m m ℂ) (hv : AnalyticOnNhd ℂ v (closure D.domain)),
      D.cauchy (hsTraceLp (matrixFourierTrace ij k)) = hsTraceLp (D.trace v hv) ∧
      ∀ z ∈ D.domain, ∀ i j, v z i j =
        ∫ t : UnitAddCircle, ((t.toCircle : ℂ)*deriv D.G (t.toCircle : ℂ)) *
          matrixFourierTrace ij k t i j / (D.G t.toCircle-z) ∂AddCircle.haarAddCircle := by
  obtain ⟨v,hv,hvp,hvt⟩ := actualExteriorCauchy_fourier_trace D.exterior.radius_gt
    D.exterior.leading_ne D.exterior.analytic_regular D.exterior.injective
    D.exterior.noncritical D.support_circle D.isOpen D.exterior.boundary_image D.outside_imp k
  let V : ℂ → Matrix m m ℂ := fun z => Matrix.single ij.1 ij.2 (v z)
  have hV : AnalyticOnNhd ℂ V (closure D.domain) := by
    intro z hz
    convert (hv z hz).smul (analyticAt_const : AnalyticAt ℂ
      (fun _ : ℂ => Matrix.single ij.1 ij.2 (1:ℂ)) z) using 1
    ext w i j
    change (if ij.1 = i ∧ ij.2 = j then v w else 0) =
      v w * (if ij.1 = i ∧ ij.2 = j then 1 else 0)
    split_ifs <;> simp
  refine ⟨V,hV,?_,?_⟩
  · rw [cauchy,hsTraceLp_matrixFourierTrace,matrixCauchy_eq_entrywise,entrywise_embedding]
    apply Lp.ext
    filter_upwards [l2Embedding_ae ij (scalarFourier.cauchy D.kernel.scalarM (fourierLp 2 k)),
      hvt,hsTraceLp_ae (D.trace V hV)] with t he ht hvv
    change (scalarFourier.cauchy D.kernel.scalarM (fourierLp 2 k)) t = v (D.G t.toCircle) at ht
    rw [he,ht,hvv]
    apply PiLp.ext
    rintro ⟨i,j⟩
    simp only [PiLp.single_apply,toHS,trace,ContinuousMap.coe_mk,V,Matrix.single_apply]
    rcases ij with ⟨i',j'⟩
    simp only [Prod.mk.injEq,eq_comm]
  · intro z hz i j
    simp only [V,Matrix.single_apply,matrixFourierTrace,ContinuousMap.coe_mk]
    split_ifs with hij
    · rw [hvp hz]
      refine integral_congr_ae (ae_of_all _ fun point => ?_)
      dsimp [physicalCauchy,G]
      ring
    · simp

lemma fourier_resolvent_eval (A : Matrix n n ℂ) (hA : spectrum ℂ A ⊆ D.domain)
    (ij : m × m) (k : ℤ) {v : ℂ → Matrix m m ℂ}
    (he : ∀ z ∈ D.domain, ∀ i j, v z i j =
      ∫ t : UnitAddCircle, ((t.toCircle : ℂ)*deriv D.G (t.toCircle : ℂ)) *
        matrixFourierTrace ij k t i j / (D.G t.toCircle-z) ∂AddCircle.haarAddCircle) :
    completeAnalyticEval A v = ∫ t : UnitAddCircle,
      D.resolventField A t ⊗ₖ matrixFourierTrace ij k t ∂AddCircle.haarAddCircle := by
  unfold resolventField
  rw [← complete_cauchy_integral_evaluation (μ := AddCircle.haarAddCircle) A D.curve_continuous D.normal_continuous
    (matrixFourierTrace ij k).continuous D.isOpen hA
    (fun z hz t => D.G_ne_interior hz (by simp [Circle.norm_coe]))]
  apply completeAnalyticEval_eqOn A D.isOpen hA
  intro z hz
  ext i j
  exact he z hz i j
end AdmissibleDomain
end CompleteCrouzeix

end

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_DensityAdjoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_247 u_248

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
variable {n : Type u_247} {m : Type u_248} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
attribute [local instance] OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions_55
lemma densityField_star (L : C(UnitAddCircle,Matrix n n ℂ)) (hL : ∀ t, (L t).IsHermitian)
    (X Y : Matrix n m ℂ) :
    l2Star (densityField (μ := AddCircle.haarAddCircle) L X Y) = densityField L Y X := by
  apply Lp.ext
  filter_upwards [l2StarL_ae (densityField (μ := AddCircle.haarAddCircle) L X Y),
    densityField_ae (μ := AddCircle.haarAddCircle) L X Y,
    densityField_ae (μ := AddCircle.haarAddCircle) L Y X] with t hs hx hy
  change l2StarL (densityField L X Y) t = _
  rw [hs,hx,hy,hsStar_apply,fromHS_toHS,weightedDensity_star,(hL t).eq]
end CompleteCrouzeix

end

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_TestingAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_249 u_250

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
variable {n : Type u_249} {m : Type u_250} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
lemma tensorTesting_star (X Y : Matrix n m ℂ) (M : Matrix (n × m) (n × m) ℂ) :
    tensorTesting X Y Mᴴ = conj (tensorTesting Y X M) := by
  change inner ℂ (vectorize Y) (Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) Mᴴ (vectorize X)) = _
  have hs : Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) Mᴴ =
      (Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) M).adjoint :=
    map_star (Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ)) M
  rw [hs,ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) M (vectorize Y)) (vectorize X) =
    conj (inner ℂ (vectorize X) (Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) M (vectorize Y)))
  rw [inner_conj_symm]
lemma tensorTesting_similarity {S : Matrix n n ℂ} (hS : S.IsHermitian) (hu : IsUnit S)
    {X Y : Matrix n m ℂ} {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hX : S*X = (a:ℂ) • X) (hY : S*Y = (b:ℂ) • Y)
    (A : Matrix n n ℂ) (v : ℂ → Matrix m m ℂ) :
    tensorTesting X Y (completeAnalyticEval A v) = (a/b:ℝ) *
      tensorTesting X Y (completeAnalyticEval (S*A*S⁻¹) v) := by
  have hSS : S⁻¹*S=1 := Matrix.nonsing_inv_mul S ((Matrix.isUnit_iff_isUnit_det S).mp hu)
  have hXi : S⁻¹*X = ((a⁻¹:ℝ):ℂ) • X := by
    have hh := congrArg (fun Z : Matrix n m ℂ => S⁻¹*Z) hX
    rw [← Matrix.mul_assoc,hSS,Matrix.one_mul,Matrix.mul_smul] at hh
    calc
      _ = ((a⁻¹:ℝ):ℂ) • ((a:ℂ) • (S⁻¹*X)) := by
        rw [smul_smul,← Complex.ofReal_mul,inv_mul_cancel₀ ha,Complex.ofReal_one,one_smul]
      _ = _ := congrArg (fun Z : Matrix n m ℂ => ((a⁻¹:ℝ):ℂ) • Z) hh.symm
  have hBX : Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) (S⁻¹ ⊗ₖ (1:Matrix m m ℂ))
      (vectorize X) = ((a⁻¹:ℝ):ℂ) • vectorize X := by
    rw [kronecker_vectorize,Matrix.transpose_one,Matrix.mul_one,hXi]
    exact vectorizeCLM.map_smul _ _
  have hBY : Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) (S ⊗ₖ (1:Matrix m m ℂ))
      (vectorize Y) = (b:ℂ) • vectorize Y := by
    rw [kronecker_vectorize,Matrix.transpose_one,Matrix.mul_one,hY]
    exact vectorizeCLM.map_smul _ _
  have hBH : (S ⊗ₖ (1:Matrix m m ℂ)).IsHermitian := by
    rw [Matrix.IsHermitian,Matrix.conjTranspose_kronecker,hS.eq,Matrix.conjTranspose_one]
  have he : tensorTesting X Y (completeAnalyticEval (S*A*S⁻¹) v) =
      (b/a:ℝ) * tensorTesting X Y (completeAnalyticEval A v) := by
    rw [completeAnalyticEval_similarity hu]
    change inner ℂ (vectorize Y) (Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) _ (vectorize X)) = _
    rw [map_mul,map_mul,mul_apply_eq_comp,mul_apply_eq_comp,hBX,map_smul]
    have hs : (Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) (S ⊗ₖ (1:Matrix m m ℂ))).adjoint =
        Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) (S ⊗ₖ (1:Matrix m m ℂ)) := by
      have hh : Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) (S ⊗ₖ (1:Matrix m m ℂ))ᴴ =
          (Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) (S ⊗ₖ (1:Matrix m m ℂ))).adjoint :=
        map_star (Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ)) _
      rw [hBH.eq] at hh
      exact hh.symm
    rw [← hs]
    rw [ContinuousLinearMap.adjoint_inner_right,hBY,inner_smul_left,inner_smul_right]
    simp only [Complex.conj_ofReal,ofReal_div,ofReal_inv]
    change (b:ℂ) * ((a:ℂ)⁻¹ * tensorTesting X Y (completeAnalyticEval A v)) = _
    ring
  rw [he]
  simp only [ofReal_div]
  field_simp [ha,hb]

lemma hermitianField_hermitian
    {n : Type u_249} [Fintype n] [DecidableEq n] (K : C(UnitAddCircle,Matrix n n ℂ))
    (t : UnitAddCircle) :
    (hermitianField K t).IsHermitian := by
  change (K t+(K t)ᴴ)ᴴ = K t+(K t)ᴴ
  rw [Matrix.conjTranspose_add,Matrix.conjTranspose_conjTranspose,add_comm]
lemma hermitianField_integral (K : C(UnitAddCircle,Matrix n n ℂ))
    (u : C(UnitAddCircle,Matrix m m ℂ)) :
    (∫ t, hermitianField K t ⊗ₖ u t ∂AddCircle.haarAddCircle) =
      (∫ t, K t ⊗ₖ u t ∂AddCircle.haarAddCircle) +
      (∫ t, K t ⊗ₖ (u t)ᴴ ∂AddCircle.haarAddCircle)ᴴ := by
  have hi : Integrable (fun t => K t ⊗ₖ u t) AddCircle.haarAddCircle :=
    (continuous_kron K.continuous u.continuous).integrable_of_hasCompactSupport
    (μ := AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  have his := (continuous_kron K.continuous u.continuous.matrix_conjTranspose).integrable_of_hasCompactSupport
    (μ := AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  have his' : Integrable (fun t => (K t ⊗ₖ (u t)ᴴ)ᴴ) AddCircle.haarAddCircle :=
    (continuous_kron K.continuous u.continuous.matrix_conjTranspose).matrix_conjTranspose.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he : (fun t => hermitianField K t ⊗ₖ u t) =
      (fun t => K t ⊗ₖ u t + (K t ⊗ₖ (u t)ᴴ)ᴴ) := by
    funext t
    simp only [hermitianField,ContinuousMap.coe_mk,Matrix.add_kronecker,
      Matrix.conjTranspose_kronecker,Matrix.conjTranspose_conjTranspose]
  rw [he,integral_add hi his',integral_conjTranspose his]
lemma densityField_testing_sum (K : C(UnitAddCircle,Matrix n n ℂ)) (X Y : Matrix n m ℂ)
    (u : C(UnitAddCircle,Matrix m m ℂ)) :
    inner ℂ (densityField (μ := AddCircle.haarAddCircle) (hermitianField K) X Y) (hsTraceLp u) =
      tensorTesting X Y (∫ t, K t ⊗ₖ u t ∂AddCircle.haarAddCircle) +
      conj (tensorTesting Y X (∫ t, K t ⊗ₖ (u t)ᴴ ∂AddCircle.haarAddCircle)) := by
  unfold hsTraceLp
  rw [densityField_testing (hermitianField K) (hermitianField_hermitian K),
    hermitianField_integral K u,map_add,tensorTesting_star]
lemma matrixFourierTrace_star
    {m : Type u_250} [Fintype m] [DecidableEq m] (ij : m × m) (k : ℤ) (t : UnitAddCircle) :
    (matrixFourierTrace ij k t)ᴴ = matrixFourierTrace ij.swap (-k) t := by
  ext i j
  by_cases h : ij.1 = j ∧ ij.2 = i
  · simp [matrixFourierTrace, Matrix.conjTranspose_apply,h.1,h.2]
  · have h' : ¬(ij.2 = i ∧ ij.1 = j) := by tauto
    simp [matrixFourierTrace, Matrix.conjTranspose_apply,h,h']
lemma hsTrace_matrixFourier_star (ij : m × m) (k : ℤ) :
    l2Star (hsTraceLp (matrixFourierTrace ij k)) = hsTraceLp (matrixFourierTrace ij.swap (-k)) := by
  rw [hsTraceLp_star]
  congr 1
  ext t i j
  exact congrArg (fun M : Matrix m m ℂ => M i j) (matrixFourierTrace_star ij k t)
end CompleteCrouzeix

end

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_DensityIdentification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_251 u_252

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
namespace AdmissibleDomain
variable (D : AdmissibleDomain)
variable {n : Type u_251} {m : Type u_252} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
attribute [local instance] OAI.CompleteCrouzeix.AdmissibleDomain.instFactLtRealOfNat_1
lemma resolvent_density_testing (A : Matrix n n ℂ) (hA : spectrum ℂ A ⊆ D.domain)
    {S : Matrix n n ℂ} (hS : S.IsHermitian) (hu : IsUnit S)
    (L : C(UnitAddCircle,Matrix n n ℂ)) (hL : ∀ t, (L t).IsHermitian)
    (hrep : ∀ (v : ℂ → Matrix m m ℂ) (hv : AnalyticOnNhd ℂ v (closure D.domain)),
      completeAnalyticEval (S*A*S⁻¹) v = ∫ t, L t ⊗ₖ D.trace v hv t ∂AddCircle.haarAddCircle)
    {X Y : Matrix n m ℂ} {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hX : S*X = (a:ℂ) • X) (hY : S*Y = (b:ℂ) • Y)
    (ij : m × m) (k : ℤ) :
    tensorTesting X Y (∫ t : UnitAddCircle, D.resolventField A t ⊗ₖ matrixFourierTrace ij k t
      ∂AddCircle.haarAddCircle) = (a/b:ℝ)*
      inner ℂ (densityField (μ := AddCircle.haarAddCircle) L X Y)
        (D.cauchy (hsTraceLp (matrixFourierTrace ij k))) := by
  obtain ⟨v,hv,hc,he⟩ := D.fourier_cauchy ij k
  rw [hc]
  unfold hsTraceLp
  rw [densityField_testing L hL,← hrep v hv,← D.fourier_resolvent_eval A hA ij k he]
  exact tensorTesting_similarity hS hu ha hb hX hY A v
lemma resolvent_density_identification_oai (A : Matrix n n ℂ) (hA : spectrum ℂ A ⊆ D.domain)
    {S : Matrix n n ℂ} (hS : S.IsHermitian) (hu : IsUnit S)
    (L : C(UnitAddCircle,Matrix n n ℂ)) (hL : ∀ t, (L t).IsHermitian)
    (hrep : ∀ (v : ℂ → Matrix m m ℂ) (hv : AnalyticOnNhd ℂ v (closure D.domain)),
      completeAnalyticEval (S*A*S⁻¹) v = ∫ t, L t ⊗ₖ D.trace v hv t ∂AddCircle.haarAddCircle)
    {X Y : Matrix n m ℂ} {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hX : S*X = (a:ℂ) • X) (hY : S*Y = (b:ℂ) • Y) :
    densityField (μ := AddCircle.haarAddCircle)
      (hermitianField ⟨D.resolventField A,D.resolvent_continuous A hA⟩) X Y =
      ((a/b:ℝ):ℂ) • D.cauchy.adjoint (densityField L X Y) +
      ((b/a:ℝ):ℂ) • l2Star (D.cauchy.adjoint (l2Star (densityField L X Y))) := by
  apply density_adjoint_identification
  intro ij k
  rw [densityField_testing_sum]
  simp only [ContinuousMap.coe_mk]
  rw [D.resolvent_density_testing A hA hS hu L hL hrep ha hb hX hY ij k]
  simp_rw [matrixFourierTrace_star]
  rw [D.resolvent_density_testing A hA hS hu L hL hrep hb ha hY hX ij.swap (-k)]
  rw [densityField_star L hL,hsTrace_matrixFourier_star]
  simp only [map_mul,Complex.conj_ofReal]
end AdmissibleDomain
end CompleteCrouzeix

end

end

end OAI
end

theorem solution.{u_251, u_252} : type_of% @OAI.CompleteCrouzeix.AdmissibleDomain.resolvent_density_identification_oai.{u_251, u_252} := @OAI.CompleteCrouzeix.AdmissibleDomain.resolvent_density_identification_oai.{u_251, u_252}
