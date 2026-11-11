-- Prove2me | solution 1 for OAI.DirectionalTransience.height_median_path_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:46:20.439288+00:00
-- url     : https://prove2.me/submissions/1bf131aa-e519-4375-8a7d-d6a02ce5dafa

import Mathlib
import Definitions.Def_OAIQ242Bal001

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CommonWordIncrement
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma realPartialSum_succ (X : ℕ → ℝ) (n : ℕ) :
    realPartialSum X (n+1) = realPartialSum X n+X n := by simp [realPartialSum,Finset.sum_range_succ]

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_GridOscillation
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma unitRamp_zero {t : ℝ} (ht : t ≤ 0) : unitRamp t = 0 := by
  simp [unitRamp,max_eq_left ht]
lemma unitRamp_one {t : ℝ} (ht : 1 ≤ t) : unitRamp t = 1 := by
  simp [unitRamp,max_eq_right (by linarith : 0 ≤ t),min_eq_left ht]
lemma unitRamp_self {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) : unitRamp t = t := by
  simp [unitRamp,max_eq_right ht,min_eq_right ht1]

lemma linearPolygon_formula (x : ℕ → ℝ) (N : ℕ) {t : ℝ}
    (ht : 0 ≤ t) (hN : ⌊t⌋₊ < N) :
    linearPolygon x N t = realPartialSum x ⌊t⌋₊ + (t-⌊t⌋₊)*x ⌊t⌋₊ := by
  let j := ⌊t⌋₊
  have hj : (j:ℝ) ≤ t := Nat.floor_le ht
  have hj1 : t < j+1 := Nat.lt_floor_add_one t
  have hNj : j+1 ≤ N := hN
  have hsplit : N = j+1+(N-(j+1)) := (Nat.add_sub_of_le hNj).symm
  unfold linearPolygon
  rw [hsplit,Finset.sum_range_add,Finset.sum_range_succ]
  have hleft : (∑ k ∈ Finset.range j, unitRamp (t-k)*x k) = realPartialSum x j := by
    unfold realPartialSum
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : (k:ℝ)+1 ≤ j := by exact_mod_cast Finset.mem_range.mp hk
    rw [unitRamp_one (by linarith),one_mul]
  rw [hleft,unitRamp_self (by linarith) (by linarith)]
  have htail : (∑ k ∈ Finset.range (N-(j+1)), unitRamp (t-(j+1+k))*x (j+1+k)) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
    rw [unitRamp_zero (by linarith),zero_mul]
  simpa [j] using congrArg (fun z => realPartialSum x j+(t-j)*x j+z) htail

lemma polygonPath_apply (N : ℕ) (scale : ℝ) (x : ℕ → ℝ) (t : unitInterval) :
    polygonPath N scale x t = linearPolygon x N (scale*t) := by
  simp only [polygonPath,ContinuousMap.sum_apply,ContinuousMap.smul_apply,
    ContinuousMap.coe_mk,smul_eq_mul,linearPolygon]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma scaledPolygon_apply (x : ℕ → ℝ) (r n T : ℝ) (t : unitInterval) :
    scaledPolygon x r n T t = linearPolygon x (⌊T*n⌋₊+1) (T*n*t)/r := by
  simp [scaledPolygon,polygonPath_apply,div_eq_inv_mul]

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_OrderedTimes
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.row_compact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma continuous_path_measure_ext (μ ν : Measure C(unitInterval,ℝ))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ I : Finset unitInterval, μ.map (fun f : C(unitInterval,ℝ) => I.restrict f) =
      ν.map (fun f : C(unitInterval,ℝ) => I.restrict f)) : μ = ν := by
  classical
  let e := TopologicalSpace.denseSeq unitInterval
  let E := fun f : C(unitInterval,ℝ) => fun n => f (e n)
  have hE : Continuous E := continuous_pi (fun n => continuous_eval_const _)
  have hEinj : Function.Injective E := by
    intro f g hfg
    apply ContinuousMap.coe_injective
    exact TopologicalSpace.denseRange_denseSeq unitInterval |>.equalizer
      f.continuous g.continuous hfg
  apply hE.measurableEmbedding hEinj |>.map_injective
  let P := fun J : Finset ℕ => (μ.map E).map J.restrict
  have : ∀ J, IsFiniteMeasure (P J) := fun _ => inferInstance
  apply IsProjectiveLimit.unique (P := P) (fun _ => rfl)
  intro J
  let I := J.image e
  let g := fun f : I → ℝ => fun j : J => f ⟨e j,Finset.mem_image_of_mem e j.2⟩
  have hg : Measurable g := by fun_prop
  have hm : Measurable (J.restrict : (ℕ → ℝ) → (J → ℝ)) := by fun_prop
  change (ν.map E).map J.restrict = (μ.map E).map J.restrict
  rw [Measure.map_map hm hE.measurable,Measure.map_map hm hE.measurable]
  have he : J.restrict ∘ E = g ∘ (fun f : C(unitInterval,ℝ) => I.restrict f) := rfl
  rw [he,← Measure.map_map hg (continuous_path_restrict I).measurable,
    ← Measure.map_map hg (continuous_path_restrict I).measurable,h I]

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CommonWidthProcess
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma abs_convex_sub_le {a b z q A : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (ha : |a-z| ≤ A) (hb : |b-z| ≤ A) : |(1-q)*a+q*b-z| ≤ A := by
  have he : (1-q)*a+q*b-z = (1-q)*(a-z)+q*(b-z) := by ring
  rw [he]
  calc
    _ ≤ |(1-q)*(a-z)|+|q*(b-z)| := abs_add_le _ _
    _ = (1-q)*|a-z|+q*|b-z| := by rw [abs_mul,abs_mul,abs_of_nonneg hq,abs_of_nonneg (by linarith : 0 ≤ 1-q)]
    _ ≤ (1-q)*A+q*A := add_le_add (mul_le_mul_of_nonneg_left ha (by linarith))
      (mul_le_mul_of_nonneg_left hb hq)
    _ = A := by ring

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_DifferentiableExp
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma differentiable_of_exp_eq {g f : ℂ → ℂ} (hg : Continuous g)
    (hf : Differentiable ℂ f) (he : ∀ z, Complex.exp (g z) = f z) :
    Differentiable ℂ g := by
  intro z
  have hn : f z ≠ 0 := by rw [← he]; exact Complex.exp_ne_zero _
  have hd : DifferentiableAt ℂ (fun w => Complex.log (f w/f z)+g z) z := by
    apply DifferentiableAt.add_const
    apply DifferentiableAt.clog ((hf z).div_const _)
    simp only [div_self hn]
    exact Complex.one_mem_slitPlane
  apply hd.congr_of_eventuallyEq
  have hc : ContinuousAt (fun w => (g w-g z).im) z := by fun_prop
  have hsmall : ∀ᶠ w in 𝓝 z, (g w-g z).im ∈ Set.Ioo (-Real.pi) Real.pi :=
    hc (IsOpen.mem_nhds isOpen_Ioo (by simp [Real.pi_pos]))
  filter_upwards [hsmall] with w hw
  rw [← he w,← he z,← Complex.exp_sub,Complex.log_exp hw.1 hw.2.le]
  exact (sub_add_cancel _ _).symm

lemma exists_entire_log {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hn : ∀ z, f z ≠ 0) (h0 : f 0 = 1) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ g 0 = 0 ∧ ∀ z, Complex.exp (g z) = f z := by
  have : ContractibleSpace (Set.univ : Set ℂ) := convex_univ.contractibleSpace Set.univ_nonempty
  obtain ⟨g,hgc,hge⟩ := Complex.exists_continuousOn_eqOn_exp_comp
    (U := Set.univ) (show SimplyConnectedSpace (Set.univ : Set ℂ) from inferInstance) isOpen_univ hf.continuous.continuousOn
    (by simpa only [Set.mem_image,Set.mem_univ,true_and,not_exists] using hn)
  have hg : Continuous g := continuousOn_univ.mp hgc
  have he : ∀ z, Complex.exp (g z) = f z := fun z => hge (Set.mem_univ z)
  refine ⟨fun z => g z-g 0,(differentiable_of_exp_eq hg hf he).sub_const _,by simp,?_⟩
  intro z
  rw [Complex.exp_sub,he,he,h0,div_one]

lemma entire_norm_quadratic_bound {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (h0 : g 0 = 0) {C : ℝ} (hC : 0 < C)
    (hb : ∀ z, (g z).re ≤ C*(1+‖z‖^2)) (z : ℂ) :
    ‖g z‖ ≤ 12*C*(1+‖z‖^2) := by
  let R := 2*‖z‖+1
  have hR : 0 < R := by dsimp [R] <;> positivity
  have hz : z ∈ Metric.ball 0 R := by
    rw [mem_ball_zero_iff]; dsimp [R] <;> linarith [norm_nonneg z]
  have hM : 0 < C*(1+R^2) := mul_pos hC (by positivity)
  have hm : Set.MapsTo g (Metric.ball 0 R) {w | w.re ≤ C*(1+R^2)} := by
    intro w hw
    exact (hb w).trans (mul_le_mul_of_nonneg_left
      (by nlinarith [mem_ball_zero_iff.mp hw,norm_nonneg w]) hC.le)
  have h := Complex.borelCaratheodory_zero hM hg.differentiableOn hm hR hz h0
  have hden : 0 < R-‖z‖ := by dsimp [R] <;> linarith [norm_nonneg z]
  calc ‖g z‖ ≤ 2*(C*(1+R^2))*‖z‖/(R-‖z‖) := h
    _ ≤ 2*(C*(1+R^2)) := by
      apply (div_le_iff₀ hden).2
      exact mul_le_mul_of_nonneg_left (by dsimp [R] <;> linarith) (by positivity)
    _ ≤ 12*C*(1+‖z‖^2) := by
      dsimp [R]
      nlinarith [mul_nonneg hC.le (sq_nonneg (‖z‖-1))]

lemma entire_third_deriv_zero {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ z, ‖g z‖ ≤ K*(1+‖z‖^2)) (c : ℂ) :
    iteratedDeriv 3 g c = 0 := by
  have hh : ∀ᶠ R : ℝ in atTop, ‖iteratedDeriv 3 g c‖ ≤ 30*K/R := by
    filter_upwards [eventually_ge_atTop (max 1 ‖c‖)] with R hR
    have hR1 : 1 ≤ R := (le_max_left _ _).trans hR
    have hRc : ‖c‖ ≤ R := (le_max_right _ _).trans hR
    have hRp : 0 < R := by linarith
    have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
      3 hRp hg.diffContOnCl (C := 5*K*R^2) (c := c) (fun z hz => by
        have hnorm : ‖z‖ ≤ 2*R := by
          calc ‖z‖ ≤ ‖z-c‖+‖c‖ := norm_le_norm_sub_add _ _
            _ ≤ 2*R := by rw [mem_sphere_iff_norm.mp hz]; linarith
        have hs : 1+‖z‖^2 ≤ 5*R^2 := by nlinarith [norm_nonneg z]
        calc ‖g z‖ ≤ K*(1+‖z‖^2) := hb z
          _ ≤ K*(5*R^2) := mul_le_mul_of_nonneg_left hs hK
          _ = 5*K*R^2 := by ring)
    calc ‖iteratedDeriv 3 g c‖ ≤ ((3:ℕ).factorial:ℝ)*(5*K*R^2)/R^3 := hc
      _ = 30*K/R := by norm_num; field_simp <;> ring
  have ht : Tendsto (fun R : ℝ => 30*K/R) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using (tendsto_const_nhds (x := (30*K:ℝ))).mul (tendsto_inv_atTop_zero : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0))
  exact norm_eq_zero.mp (le_antisymm (ge_of_tendsto ht hh) (norm_nonneg _))

theorem entire_log_quadratic {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (h0 : g 0 = 0) {C : ℝ} (hC : 0 < C)
    (hb : ∀ z, (g z).re ≤ C*(1+‖z‖^2)) :
    ∀ z, g z = deriv g 0*z + deriv (deriv g) 0*z^2/2 := by
  have h3 : ∀ z, deriv (deriv (deriv g)) z = 0 := by
    intro z
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
      entire_third_deriv_zero hg (by positivity : 0 ≤ 12*C)
        (entire_norm_quadratic_bound hg h0 hC hb) z
  have h2 : ∀ z, deriv (deriv g) z = deriv (deriv g) 0 :=
    fun z => is_const_of_deriv_eq_zero hg.deriv.deriv h3 z 0
  have hlin (z : ℂ) : HasDerivAt
      (fun w => deriv g w-(deriv g 0+deriv (deriv g) 0*w)) 0 z := by
    have h := (hg.deriv z).hasDerivAt.sub ((hasDerivAt_const z (deriv g 0)).add
      ((hasDerivAt_id z).const_mul (deriv (deriv g) 0)))
    convert! h using 1
    all_goals try with_reducible_and_instances rfl
    simp only [h2,zero_add,mul_one,sub_self]
  have h1 (z : ℂ) : deriv g z = deriv g 0+deriv (deriv g) 0*z := by
    have h := is_const_of_deriv_eq_zero (fun z => (hlin z).differentiableAt)
      (fun z => (hlin z).deriv) z 0
    simpa only [mul_zero,add_zero,sub_self,sub_eq_zero] using h
  have hpoly (z : ℂ) : HasDerivAt
      (fun w => g w-(deriv g 0*w+deriv (deriv g) 0*w^2/2)) 0 z := by
    have h := (hg z).hasDerivAt.sub (((hasDerivAt_id z).const_mul (deriv g 0)).add
      ((((hasDerivAt_id z).pow 2).const_mul (deriv (deriv g) 0)).div_const 2))
    convert! h using 1
    all_goals try with_reducible_and_instances rfl
    simp only [id_eq]
    rw [h1]; ring
  intro z
  have h := is_const_of_deriv_eq_zero (fun z => (hpoly z).differentiableAt)
    (fun z => (hpoly z).deriv) z 0
  simpa only [h0,zero_pow (by norm_num : 2 ≠ 0),mul_zero,zero_div,add_zero,sub_zero,sub_eq_zero]
    using h

theorem entire_gaussian_factor {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h0 : f 0 = 1) (A : ℂ)
    (hp : ∀ z, f z*f (-z) = Complex.exp (A*z^2)) {C : ℝ} (hC : 0 < C)
    (hb : ∀ z, ‖f z‖ ≤ Real.exp (C*(1+‖z‖^2))) :
    ∀ z, f z = Complex.exp (deriv f 0*z+A*z^2/2) := by
  have hn (z) : f z ≠ 0 := by
    intro hz
    have h := hp z
    rw [hz,zero_mul] at h
    exact Complex.exp_ne_zero _ h.symm
  obtain ⟨g,hg,hg0,he⟩ := exists_entire_log hf hn h0
  have hgb (z) : (g z).re ≤ C*(1+‖z‖^2) := by
    have h := hb z
    rw [← he z,Complex.norm_exp] at h
    exact Real.exp_le_exp.mp h
  have hpoly := entire_log_quadratic hg hg0 hC hgb
  let b := deriv (deriv g) 0
  have hprod (z : ℂ) : Complex.exp (b*z^2) = Complex.exp (A*z^2) := by
    have h := hp z
    rw [← he z,← he (-z),← Complex.exp_add,hpoly z,hpoly (-z)] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    dsimp [b]
    ring
  have h1 : Complex.exp b = Complex.exp A := by simpa using hprod 1
  have hd := congrArg (fun F : ℂ → ℂ => deriv F 1) (funext hprod)
  have hdb : deriv (fun z : ℂ => Complex.exp (b*z^2)) 1 = Complex.exp b*(b*2) := by
    simpa using ((((hasDerivAt_id (1:ℂ)).pow 2).const_mul b).cexp).deriv
  have hdA : deriv (fun z : ℂ => Complex.exp (A*z^2)) 1 = Complex.exp A*(A*2) := by
    simpa using ((((hasDerivAt_id (1:ℂ)).pow 2).const_mul A).cexp).deriv
  rw [hdb,hdA,h1] at hd
  have hbA : b = A := mul_right_cancel₀ (by norm_num : (2:ℂ) ≠ 0)
    (mul_left_cancel₀ (Complex.exp_ne_zero A) hd)
  have hdf : deriv f 0 = deriv g 0 := by
    have h := ((hg 0).hasDerivAt.cexp).deriv
    have hef : (fun z => Complex.exp (g z)) = f := funext he
    rw [hef,hg0,Complex.exp_zero,one_mul] at h
    exact h
  intro z
  rw [← he z,hpoly z,← hdf]
  change Complex.exp (deriv f 0*z+b*z^2/2) = _
  rw [hbA]

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SymmetrizedMgf
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma symmetrized_mgf (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    mgf (fun p : ℝ × ℝ => p.1-p.2) (μ.prod μ) t = mgf id μ t*mgf id μ (-t) := by
  simp only [mgf,mul_sub,Real.exp_sub,Real.exp_neg,neg_mul,id_eq,div_eq_mul_inv]
  exact integral_prod_mul (fun x : ℝ => Real.exp (t*x)) (fun y : ℝ => (Real.exp (t*y))⁻¹)

lemma symmetrized_complexMGF (μ : Measure ℝ) [IsProbabilityMeasure μ] (z : ℂ) :
    complexMGF (fun p : ℝ × ℝ => p.1-p.2) (μ.prod μ) z =
      complexMGF id μ z*complexMGF id μ (-z) := by
  simp only [complexMGF,Complex.ofReal_sub,mul_sub,Complex.exp_sub,Complex.exp_neg,neg_mul,
    id_eq,div_eq_mul_inv]
  exact integral_prod_mul (fun x : ℝ => Complex.exp (z*x)) (fun y : ℝ => (Complex.exp (z*y))⁻¹)

lemma iid_difference_gaussian_mgf_product (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (v : ℝ≥0) (hv : (μ.prod μ).map (fun p : ℝ × ℝ => p.1-p.2) = gaussianReal 0 v) (t : ℝ) :
    mgf id μ t*mgf id μ (-t) = Real.exp (v*t^2/2) := by
  rw [← symmetrized_mgf,mgf_gaussianReal hv]
  simp

lemma iid_difference_gaussian_integrableExpSet (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (v : ℝ≥0) (hv : (μ.prod μ).map (fun p : ℝ × ℝ => p.1-p.2) = gaussianReal 0 v) :
    integrableExpSet id μ = Set.univ := by
  ext t
  simp only [Set.mem_univ,iff_true,integrableExpSet,Set.mem_ofPred_eq]
  apply mgf_pos_iff.mp
  have h := iid_difference_gaussian_mgf_product μ v hv t
  have hh : 0 < mgf id μ t*mgf id μ (-t) := by rw [h]; exact Real.exp_pos _
  exact pos_of_mul_pos_left hh mgf_nonneg

lemma exp_mean_le_mgf (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : integrableExpSet id μ = Set.univ) (t : ℝ) :
    Real.exp (t*∫ x, x ∂μ) ≤ mgf id μ t := by
  have hi : Integrable id μ := integrable_of_mem_interior_integrableExpSet (by simp [hμ])
  have he : Integrable (fun x : ℝ => Real.exp (t*x)) μ := by
    have h : t ∈ integrableExpSet id μ := by rw [hμ]; trivial
    exact h
  have h := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (Eventually.of_forall fun x : ℝ => Set.mem_univ (t*x)) (hi.const_mul t) he
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  exact (integral_const_mul t (id : ℝ → ℝ)).symm

lemma iid_difference_gaussian_mgf_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (v : ℝ≥0) (hv : (μ.prod μ).map (fun p : ℝ × ℝ => p.1-p.2) = gaussianReal 0 v)
    (t : ℝ) : mgf id μ t ≤ Real.exp (t*(∫ x, x ∂μ)+v*t^2/2) := by
  have h := exp_mean_le_mgf μ (iid_difference_gaussian_integrableExpSet μ v hv) (-t)
  have hp := iid_difference_gaussian_mgf_product μ v hv t
  have hb := mul_le_mul_of_nonneg_left h (mgf_nonneg (X := id) (μ := μ) (t := t))
  rw [hp] at hb
  have he : Real.exp (t*(∫ x,x ∂μ)+v*t^2/2)*Real.exp (-t*(∫ x,x ∂μ)) =
      Real.exp (v*t^2/2) := by rw [← Real.exp_add]; congr 1; ring
  rw [← he] at hb
  exact (mul_le_mul_iff_left₀ (Real.exp_pos _)).mp hb

theorem iid_difference_gaussian (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (v : ℝ≥0) (hv : (μ.prod μ).map (fun p : ℝ × ℝ => p.1-p.2) = gaussianReal 0 v) :
    μ = gaussianReal (∫ x, x ∂μ) (v/2) := by
  have hset := iid_difference_gaussian_integrableExpSet μ v hv
  have hz (z : ℂ) : z.re ∈ interior (integrableExpSet id μ) := by simp [hset]
  have hf : Differentiable ℂ (complexMGF id μ) :=
    fun z => (hasDerivAt_complexMGF (hz z)).differentiableAt
  have h0 : complexMGF id μ 0 = 1 := by simp [complexMGF]
  have hp (z : ℂ) : complexMGF id μ z*complexMGF id μ (-z) =
      Complex.exp ((v:ℂ)/2*z^2) := by
    rw [← symmetrized_complexMGF,complexMGF_gaussianReal hv]
    congr 1
    simp only [Complex.ofReal_zero,mul_zero,zero_add]
    ring
  let m := ∫ x, x ∂μ
  let C := |m|+(v:ℝ)+1
  have hC : 0 < C := by dsimp [C] <;> positivity
  have hb (z : ℂ) : ‖complexMGF id μ z‖ ≤ Real.exp (C*(1+‖z‖^2)) := by
    refine norm_complexMGF_le_mgf.trans ((iid_difference_gaussian_mgf_bound μ v hv z.re).trans ?_)
    apply Real.exp_le_exp.mpr
    have hm : z.re*m ≤ |m| *‖z‖ := by
      calc z.re*m ≤ |z.re*m| := le_abs_self _
        _ = |m| *|z.re| := by rw [abs_mul]; ring
        _ ≤ |m| *‖z‖ := mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm z) (abs_nonneg m)
    have hs : z.re^2 ≤ ‖z‖^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg z.re) (Complex.abs_re_le_norm z) 2
    have ht : ‖z‖ ≤ 1+‖z‖^2 := by nlinarith [sq_nonneg (‖z‖-1)]
    have hmv := mul_le_mul_of_nonneg_left ht (abs_nonneg m)
    have hvz := mul_le_mul_of_nonneg_left hs v.2
    have hv0 := mul_nonneg v.2 (sq_nonneg ‖z‖)
    dsimp [C,m] at *
    nlinarith [norm_nonneg z,abs_nonneg (∫ x,x ∂μ)]
  have hfac := entire_gaussian_factor hf h0 ((v:ℂ)/2) hp hC hb
  have hd : deriv (complexMGF id μ) 0 = (∫ x, x ∂μ : ℝ) := by
    calc
      _ = ∫ x : ℝ, (x : ℂ) ∂μ := by
        simpa only [id_eq,zero_mul,Complex.exp_zero,mul_one] using
          (hasDerivAt_complexMGF (hz 0)).deriv
      _ = _ := integral_complex_ofReal
  apply Measure.ext_of_complexMGF_id_eq
  funext z
  rw [hfac z,complexMGF_id_gaussianReal,hd]
  congr 1
  push_cast
  ring

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma map_iid_difference_linear {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F]
    (μ : Measure E) [IsProbabilityMeasure μ] (L : E →L[ℝ] F) :
    ((μ.map L).prod (μ.map L)).map (fun p : F × F => p.1-p.2) =
      ((μ.prod μ).map (fun p : E × E => p.1-p.2)).map L := by
  rw [Measure.map_prod_map μ μ L.measurable L.measurable,
    Measure.map_map (show Measurable (fun p : F × F => p.1-p.2) by fun_prop)
      (L.measurable.prodMap L.measurable),
    Measure.map_map L.measurable (show Measurable (fun p : E × E => p.1-p.2) by fun_prop)]
  congr 1
  funext p
  exact (L.map_sub p.1 p.2).symm

theorem iid_difference_isGaussian {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsGaussian ν]
    (hmean : ∫ x, x ∂ν = 0)
    (hv : (μ.prod μ).map (fun p : E × E => p.1-p.2) = ν) : IsGaussian μ := by
  apply isGaussian_of_map_eq_gaussianReal
  intro L
  have hn : ν.map L = gaussianReal 0 (Var[L; ν]).toNNReal := by
    rw [IsGaussian.map_eq_gaussianReal,IsGaussian.integral_dual,hmean,map_zero]
  have hd : ((μ.map L).prod (μ.map L)).map (fun p : ℝ × ℝ => p.1-p.2) =
      gaussianReal 0 (Var[L; ν]).toNNReal := by
    rw [map_iid_difference_linear,hv,hn]
  haveI : IsProbabilityMeasure (μ.map L) := Measure.isProbabilityMeasure_map L.continuous.aemeasurable
  exact ⟨∫ x, x ∂μ.map L,(Var[L; ν]).toNNReal/2,iid_difference_gaussian _ _ hd⟩

lemma iid_difference_gaussian_centered_linear {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [CompleteSpace E] (μ ν : Measure E) [IsProbabilityMeasure μ] [IsGaussian ν]
    (hmean : ∫ x, x ∂ν = 0)
    (hv : (μ.prod μ).map (fun p : E × E => p.1-p.2) = ν) (L : E →L[ℝ] ℝ) :
    μ.map (fun x => L (x-∫ y, y ∂μ)) = gaussianReal 0 ((Var[L; ν]).toNNReal/2) := by
  have : IsGaussian μ := iid_difference_isGaussian μ ν hmean hv
  have hn : ν.map L = gaussianReal 0 (Var[L; ν]).toNNReal := by
    rw [IsGaussian.map_eq_gaussianReal,IsGaussian.integral_dual,hmean,map_zero]
  have hd : ((μ.map L).prod (μ.map L)).map (fun p : ℝ × ℝ => p.1-p.2) =
      gaussianReal 0 (Var[L; ν]).toNNReal := by rw [map_iid_difference_linear,hv,hn]
  have hg := iid_difference_gaussian (μ.map L) _ hd
  have hi : (∫ x, x ∂μ.map L) = L (∫ x, x ∂μ) := by
    rw [integral_map L.measurable.aemeasurable
      (show AEStronglyMeasurable (fun x : ℝ => x) (μ.map L) from measurable_id.aestronglyMeasurable)]
    exact IsGaussian.integral_dual L
  have he : (fun x => L (x-∫ y, y ∂μ)) = (fun x : ℝ => x-L (∫ y, y ∂μ)) ∘ L := by
    funext x; simp
  rw [he,← Measure.map_map (by fun_prop) L.measurable,hg,hi]
  simpa only [sub_self] using (gaussianReal_map_sub_const (μ := L (∫ y, y ∂μ))
    (v := (Var[L; ν]).toNNReal/2) (L (∫ y, y ∂μ)))

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_GaussianPiReal
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.row_compact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma isGaussian_pi_real {ι : Type*} [Fintype ι] (m : ι → ℝ) (v : ι → ℝ≥0) :
    IsGaussian (Measure.pi (fun i => gaussianReal (m i) (v i))) := by
  let μ := Measure.pi (fun i => gaussianReal (m i) (v i))
  have h (i : ι) : HasGaussianLaw (fun x : ι → ℝ => x i) μ := by
    refine ⟨?_⟩
    change IsGaussian (μ.map (fun x => x i))
    rw [(measurePreserving_eval (fun i => gaussianReal (m i) (v i)) i).map_eq]
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hi : iIndepFun (fun i (x : ι → ℝ) => x i) μ := iIndepFun_pi fun i => measurable_id.aemeasurable
  have hh := hi.hasGaussianLaw h
  have hh' : IsGaussian (μ.map id) := hh.isGaussian_map
  simpa only [Measure.map_id] using hh'

instance gaussianPathFiniteLaw_gaussian (T : ℝ) (I : Finset unitInterval) :
    IsGaussian (gaussianPathFiniteLaw T I) := by
  unfold gaussianPathFiniteLaw
  have := isGaussian_pi_real (fun _ : Fin I.card => (0:ℝ))
    (fun j => Real.toNNReal (T*((orderedTimes I j.succ:ℝ)-orderedTimes I j.castSucc)))
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma gaussianPathFiniteLaw_mean (T : ℝ) (I : Finset unitInterval) :
    ∫ x, x ∂gaussianPathFiniteLaw T I = 0 := by
  unfold gaussianPathFiniteLaw
  let μ := Measure.pi (fun j : Fin I.card => gaussianReal 0
    (Real.toNNReal (T*((orderedTimes I j.succ:ℝ)-orderedTimes I j.castSucc))))
  have : IsGaussian μ := isGaussian_pi_real _ _
  rw [integral_map (by fun_prop) (by fun_prop)]
  change (∫ x, incrementCumsum I (id x) ∂μ) = 0
  rw [(incrementCumsum I).integral_comp_comm IsGaussian.integrable_id]
  have hz : (∫ x, x ∂μ) = 0 := by
    ext j
    change (ContinuousLinearMap.proj j : (Fin I.card → ℝ) →L[ℝ] ℝ) (∫ x, x ∂μ) = 0
    rw [← IsGaussian.integral_dual (μ := μ) (.proj j)]
    simp [μ,integral_eval]
  simp only [id_eq,hz,map_zero]

lemma path_restrict_iid_diff (μ : Measure C(unitInterval,ℝ)) [IsProbabilityMeasure μ]
    (I : Finset unitInterval) :
    ((μ.map (fun g : C(unitInterval,ℝ) => I.restrict g)).prod (μ.map (fun g : C(unitInterval,ℝ) => I.restrict g))).map
      (fun p : (I → ℝ) × (I → ℝ) => p.1-p.2) =
    ((μ.prod μ).map (fun p : C(unitInterval,ℝ) × C(unitInterval,ℝ) => p.1-p.2)).map
      (fun g : C(unitInterval,ℝ) => I.restrict g) := by
  let L : C(unitInterval,ℝ) →L[ℝ] (I → ℝ) :=
    { toFun g := I.restrict g
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      cont := continuous_path_restrict I }
  exact map_iid_difference_linear μ L

lemma path_of_iid_difference_gaussian (G W : ProbabilityMeasure C(unitInterval,ℝ)) (T : ℝ)
    (hW : ∀ I : Finset unitInterval,
      (W : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g) = gaussianPathFiniteLaw T I)
    (hG : ((G : Measure C(unitInterval,ℝ)).prod G).map
      (fun p : C(unitInterval,ℝ) × C(unitInterval,ℝ) => p.1-p.2) = W) :
    ∀ I : Finset unitInterval, IsGaussian ((G : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g)) := by
  intro I
  let μ := (G : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g)
  haveI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map (continuous_path_restrict I).aemeasurable
  apply iid_difference_isGaussian μ (gaussianPathFiniteLaw T I) (gaussianPathFiniteLaw_mean T I)
  rw [path_restrict_iid_diff,hG,hW]

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_TightIidDifferenceTranslations
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
namespace DirectionalTransience

theorem tight_iid_difference_translations_support {E ι : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : ι → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (S : ι → Set E) (hS : ∀ i, ∀ᵐ x ∂μ i, x ∈ S i)
    (ht : IsTightMeasureSet (Set.range fun i =>
      ((μ i).prod (μ i)).map (fun p : E × E => p.1-p.2))) :
    ∃ c : ι → E, (∀ i, c i ∈ S i) ∧ IsTightMeasureSet (Set.range fun i => (μ i).map (fun x => x-c i)) := by
  obtain ⟨C,hC,hbound⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp ht
    (1/4) (by norm_num)
  have hdiff : Measurable (fun p : E × E => p.1-p.2) := measurable_fst.sub measurable_snd
  have hex (i : ι) : ∃ c : E, c ∈ S i ∧ (μ i) {x | x-c ∉ C} ≤ 1/2 := by
    have h := hbound _ ⟨i,rfl⟩
    rw [Measure.map_apply hdiff hC.measurableSet.compl,
      Measure.prod_apply_symm (hdiff hC.measurableSet.compl)] at h
    by_contra hn
    push Not at hn
    have hh : (1/2 : ℝ≥0∞) ≤ ∫⁻ y, (μ i) {x | x-y ∉ C} ∂μ i := by
      calc _ = ∫⁻ y : E, (1/2 : ℝ≥0∞) ∂μ i := by simp
        _ ≤ _ := lintegral_mono_ae ((hS i).mono fun y hy => (hn y hy).le)
    have : (1/2 : ℝ≥0∞) ≤ 1/4 := hh.trans h
    norm_num at this
  choose c hcs hc using hex
  refine ⟨c,hcs,isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr ?_⟩
  intro ε hε
  obtain ⟨K,hK,hKb⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp ht
    (ε/2) (ENNReal.div_pos hε.ne' (by norm_num))
  refine ⟨K+C,hK.add hC,?_⟩
  rintro _ ⟨i,rfl⟩
  let A := {x : E | x-c i ∉ K+C}
  let B := {y : E | y-c i ∈ C}
  have hb : (1/2 : ℝ≥0∞) ≤ μ i B := by
    have hc' : μ i Bᶜ ≤ 1/2 := hc i
    have hBm : MeasurableSet B := hC.measurableSet.preimage (measurable_id.sub_const _)
    rw [measure_compl hBm (measure_ne_top _ _),measure_univ] at hc'
    have hh := (tsub_le_iff_right.mp hc')
    apply ENNReal.le_of_add_le_add_left (by norm_num : (1/2 : ℝ≥0∞) ≠ ∞)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    exact ENNReal.add_halves 1
  have hAB : A ×ˢ B ⊆ (fun p : E × E => p.1-p.2) ⁻¹' Kᶜ := by
    rintro ⟨x,y⟩ ⟨hx,hy⟩ hxy
    apply hx
    have he : x-c i = (x-y)+(y-c i) := by abel
    rw [he]
    exact Set.add_mem_add hxy hy
  have hp : μ i A * μ i B ≤ ε/2 := by
    calc _ = (μ i).prod (μ i) (A ×ˢ B) := (Measure.prod_prod _ _).symm
      _ ≤ (μ i).prod (μ i) ((fun p : E × E => p.1-p.2) ⁻¹' Kᶜ) := measure_mono hAB
      _ = ((μ i).prod (μ i)).map (fun p : E × E => p.1-p.2) Kᶜ :=
        (Measure.map_apply hdiff hK.measurableSet.compl).symm
      _ ≤ ε/2 := hKb _ ⟨i,rfl⟩
  change ((μ i).map (fun x => x-c i)) (K+C)ᶜ ≤ ε
  rw [Measure.map_apply (show Measurable (fun x : E => x-c i) by fun_prop) (hK.add hC).measurableSet.compl]
  change μ i A ≤ ε
  have hhalf : μ i A / 2 ≤ ε/2 := by
    calc _ = μ i A * (1/2) := by simp [div_eq_mul_inv]
      _ ≤ μ i A * μ i B := by gcongr
      _ ≤ ε/2 := hp
  calc _ = (μ i A / 2)*2 := (ENNReal.div_mul_cancel (by norm_num) (by norm_num)).symm
    _ ≤ (ε/2)*2 := by gcongr
    _ = ε := ENNReal.div_mul_cancel (by norm_num) (by norm_num)

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_IidDifferenceCenteredHalf
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma iid_difference_centered_eq_half {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsGaussian ν]
    (hmean : ∫ x, x ∂ν = 0)
    (hv : (μ.prod μ).map (fun p : E × E => p.1-p.2) = ν)
    (a : ℝ) (ha : a^2 = 1/2) :
    μ.map (fun x => x-∫ y, y ∂μ) = ν.map (fun x => a • x) := by
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_eq_charFun_map_one,charFunDual_eq_charFun_map_one]
  rw [Measure.map_map L.measurable (show Measurable (fun x : E => x-∫ y, y ∂μ) by fun_prop),
    Measure.map_map L.measurable (show Measurable (fun x : E => a • x) by fun_prop)]
  change charFun (μ.map (fun x => L (x-∫ y, y ∂μ))) 1 =
    charFun (ν.map (fun x => L (a • x))) 1
  rw [iid_difference_gaussian_centered_linear μ ν hmean hv]
  have he : (fun x => L (a • x)) = (fun x : ℝ => a*x) ∘ L := by ext x; simp
  rw [he,← Measure.map_map (by fun_prop) L.measurable,IsGaussian.map_eq_gaussianReal,
    IsGaussian.integral_dual,hmean,map_zero,gaussianReal_map_const_mul,mul_zero]
  congr 2
  apply NNReal.eq
  simp [ha,div_eq_mul_inv,mul_comm]

lemma iid_diff_translation {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure E) [IsProbabilityMeasure μ] (c : E) :
    ((μ.map (fun x => x-c)).prod (μ.map (fun x => x-c))).map (fun p : E × E => p.1-p.2) =
      (μ.prod μ).map (fun p : E × E => p.1-p.2) := by
  have hf : Measurable (fun x : E => x-c) := by fun_prop
  rw [Measure.map_prod_map _ _ hf hf,Measure.map_map (show Measurable (fun p : E × E => p.1-p.2) by fun_prop)
    (hf.prodMap hf)]
  congr 1
  funext p
  change (p.1-c)-(p.2-c) = p.1-p.2
  abel

lemma weak_iid_difference_tendsto {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {μ : ℕ → ProbabilityMeasure E} {ν : ProbabilityMeasure E}
    (hμ : Tendsto μ atTop (𝓝 ν)) :
    Tendsto (fun n => ((μ n).prod (μ n)).map (f := fun pair : E × E => pair.1 - pair.2) (continuous_fst.sub continuous_snd).aemeasurable)
      atTop (𝓝 ((ν.prod ν).map (f := fun pair : E × E => pair.1 - pair.2) (continuous_fst.sub continuous_snd).aemeasurable)) :=
  (ProbabilityMeasure.continuous_map (continuous_fst.sub continuous_snd)).tendsto _ |>.comp
    (ProbabilityMeasure.continuous_prod.tendsto (ν,ν) |>.comp (hμ.prodMk_nhds hμ))

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma gaussian_median_half (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    gaussianReal m v (Set.Iic m) = 1/2 ∧ gaussianReal m v (Set.Ici m) = 1/2 := by
  have : NullSingletonClass (gaussianReal m v) := nullSingletonClass_gaussianReal hv
  have hs : gaussianReal m v (Set.Iio m) = gaussianReal m v (Set.Ioi m) := by
    have hh : (gaussianReal m v).map (fun x => 2*m-x) = gaussianReal m v := by
      rw [gaussianReal_map_const_sub]; congr 1; ring
    calc
      _ = (Measure.map (fun x => 2*m-x) (gaussianReal m v)) (Set.Iio m) := by rw [hh]
      _ = _ := by
        rw [Measure.map_apply (by fun_prop) measurableSet_Iio]
        apply congrArg (gaussianReal m v)
        ext x
        change 2*m-x < m ↔ m < x
        constructor <;> intro h <;> linarith
  have hl : gaussianReal m v (Set.Iio m) = gaussianReal m v (Set.Iic m) :=
    measure_congr Iio_ae_eq_Iic
  have hr : gaussianReal m v (Set.Ioi m) = gaussianReal m v (Set.Ici m) :=
    measure_congr Ioi_ae_eq_Ici
  have hsum : gaussianReal m v (Set.Iic m)+gaussianReal m v (Set.Ioi m) = 1 := by
    simpa only [Set.compl_Iic,measure_univ] using measure_add_measure_compl (μ := gaussianReal m v)
      measurableSet_Iic
  have he : gaussianReal m v (Set.Iic m) = 1/2 := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (by norm_num)).mp
    have hh := congrArg ENNReal.toReal hsum
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),← hs,hl] at hh
    norm_num at hh ⊢
    linarith
  exact ⟨he,by rw [← hr,← hs,hl,he]⟩

lemma gaussian_median_strict (m : ℝ) (v : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    (1/2 : ℝ≥0∞) < gaussianReal m v (Set.Iio (m+ε)) ∧
    (1/2 : ℝ≥0∞) < gaussianReal m v (Set.Ioi (m-ε)) := by
  by_cases hv : v = 0
  · subst v
    simp [hε,gaussianReal_zero_var]
  have hh := gaussian_median_half m v hv
  have hpos {a b : ℝ} (hab : a < b) : 0 < gaussianReal m v (Set.Ioo a b) := by
    apply pos_iff_ne_zero.mpr
    intro hz
    have hz' := gaussianReal_absolutelyContinuous' m hv hz
    have hp : 0 < (volume : Measure ℝ) (Set.Ioo a b) := by
      rw [Real.volume_Ioo]; exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
    exact hp.ne' hz'
  constructor
  · have hc : Set.Iic m ∪ Set.Ioo m (m+ε) = Set.Iio (m+ε) := by
      ext x; simp only [Set.mem_union,Set.mem_Iic,Set.mem_Ioo,Set.mem_Iio]; constructor
      · rintro (h|h) <;> linarith
      · intro h; by_cases hx : x ≤ m; exact Or.inl hx; exact Or.inr ⟨lt_of_not_ge hx,h⟩
    rw [← hc,measure_union (by exact Set.disjoint_left.mpr fun x hx hy => not_lt_of_ge hx hy.1)
      measurableSet_Ioo,hh.1]
    exact ENNReal.lt_add_right (by norm_num) (hpos (by linarith)).ne'
  · have hc : Set.Ici m ∪ Set.Ioo (m-ε) m = Set.Ioi (m-ε) := by
      ext x; simp only [Set.mem_union,Set.mem_Ici,Set.mem_Ioo,Set.mem_Ioi]; constructor
      · rintro (h|h) <;> linarith
      · intro h; by_cases hx : m ≤ x; exact Or.inl hx; exact Or.inr ⟨h,lt_of_not_ge hx⟩
    rw [← hc,measure_union (by exact Set.disjoint_left.mpr fun x hx hy => not_lt_of_ge hx hy.2)
      measurableSet_Ioo,hh.2]
    exact ENNReal.lt_add_right (by norm_num) (hpos (by linarith)).ne'

lemma median_tendsto_of_weak {μ : ℕ → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    (hμ : Tendsto μ atTop (𝓝 ν)) (b : ℕ → ℝ) (m : ℝ)
    (hb : ∀ n, (1/2 : ℝ≥0∞) ≤ (μ n : Measure ℝ) (Set.Iic (b n)) ∧
      (1/2 : ℝ≥0∞) ≤ (μ n : Measure ℝ) (Set.Ici (b n)))
    (hm : ∀ ε > 0, (1/2 : ℝ≥0∞) < (ν : Measure ℝ) (Set.Iio (m+ε)) ∧
      (1/2 : ℝ≥0∞) < (ν : Measure ℝ) (Set.Ioi (m-ε))) :
    Tendsto b atTop (𝓝 m) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hu := eventually_lt_of_lt_liminf ((hm ε hε).1.trans_le
    (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hμ isOpen_Iio))
  have hl := eventually_lt_of_lt_liminf ((hm ε hε).2.trans_le
    (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hμ isOpen_Ioi))
  rw [eventually_atTop] at hu hl
  obtain ⟨N,hN⟩ := hu
  obtain ⟨M,hM⟩ := hl
  refine ⟨max N M,fun n hn => ?_⟩
  have hu := hN n (le_trans (le_max_left _ _) hn)
  have hl := hM n (le_trans (le_max_right _ _) hn)
  rw [Real.dist_eq,abs_lt]
  constructor
  · by_contra! hh
    have he : Set.Ioi (m-ε) ⊆ (Set.Iic (b n))ᶜ := by intro x hx; simp only [Set.mem_compl_iff,Set.mem_Iic]; change m-ε < x at hx; linarith
    have hm' := (measure_mono (μ := (μ n : Measure ℝ)) he).trans_eq (measure_compl measurableSet_Iic (measure_ne_top _ _))
    rw [measure_univ] at hm'
    have hup : (μ n : Measure ℝ) (Set.Ioi (m-ε)) ≤ 1/2 := by
      calc _ ≤ 1-(μ n : Measure ℝ) (Set.Iic (b n)) := hm'
        _ ≤ 1-(1/2) := tsub_le_tsub_left (hb n).1 1
        _ = 1/2 := ENNReal.sub_half (by norm_num)
    exact not_lt_of_ge hup hl
  · by_contra! hh
    have he : Set.Iio (m+ε) ⊆ (Set.Ici (b n))ᶜ := by intro x hx; simp only [Set.mem_compl_iff,Set.mem_Ici]; change x < m+ε at hx; linarith
    have hm' := (measure_mono (μ := (μ n : Measure ℝ)) he).trans_eq (measure_compl measurableSet_Ici (measure_ne_top _ _))
    rw [measure_univ] at hm'
    have hup : (μ n : Measure ℝ) (Set.Iio (m+ε)) ≤ 1/2 := by
      calc _ ≤ 1-(μ n : Measure ℝ) (Set.Ici (b n)) := hm'
        _ ≤ 1-(1/2) := tsub_le_tsub_left (hb n).2 1
        _ = 1/2 := ENNReal.sub_half (by norm_num)
    exact not_lt_of_ge hup hu

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_WeakPathEvalTendsto
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.row_compact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma weak_path_eval_tendsto {μ : ℕ → ProbabilityMeasure C(unitInterval,ℝ)}
    {ν : ProbabilityMeasure C(unitInterval,ℝ)} (hμ : Tendsto μ atTop (𝓝 ν))
    {t : ℕ → unitInterval} {s : unitInterval} (ht : Tendsto t atTop (𝓝 s)) :
    Tendsto (fun n => (μ n).map (f := (fun path => path (t n))) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
      atTop (𝓝 (ν.map (f := (fun path => path s)) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))) := by
  have he : Continuous (fun p : C(unitInterval,ℝ) × unitInterval => p.1 p.2) := continuous_eval
  have hh := (ProbabilityMeasure.continuous_map he).tendsto
    (ν.prod (diracProba s)) |>.comp
    (ProbabilityMeasure.continuous_prod.tendsto (ν,diracProba s) |>.comp
      (hμ.prodMk_nhds (continuous_diracProba.tendsto s |>.comp ht)))
  have hid (V : ProbabilityMeasure C(unitInterval,ℝ)) (u : unitInterval) :
      (V.prod (diracProba u)).map (f := fun pair : C(unitInterval,ℝ) × unitInterval => pair.1 pair.2) he.aemeasurable =
        V.map (f := (fun path => path u)) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) := by
    apply Subtype.ext
    change ((V : Measure C(unitInterval,ℝ)).prod (Measure.dirac u)).map _ = _
    rw [Measure.prod_dirac,Measure.map_map he.measurable (by fun_prop)]
    rfl
  change Tendsto (fun n => ((μ n).prod (diracProba (t n))).map (f := fun pair : C(unitInterval,ℝ) × unitInterval => pair.1 pair.2) he.aemeasurable)
    atTop (𝓝 ((ν.prod (diracProba s)).map (f := fun pair : C(unitInterval,ℝ) × unitInterval => pair.1 pair.2) he.aemeasurable)) at hh
  simpa only [hid] using hh

lemma gaussian_median_nonstrict (m : ℝ) (v : ℝ≥0) :
    (1/2 : ℝ≥0∞) ≤ gaussianReal m v (Set.Iic m) ∧
    (1/2 : ℝ≥0∞) ≤ gaussianReal m v (Set.Ici m) := by
  by_cases hv : v = 0
  · subst v; simp [gaussianReal_zero_var]
  · exact ⟨(gaussian_median_half m v hv).1.ge,(gaussian_median_half m v hv).2.ge⟩

lemma continuous_gaussian_path_mean (G : ProbabilityMeasure C(unitInterval,ℝ))
    (m : unitInterval → ℝ) (v : unitInterval → ℝ≥0)
    (hg : ∀ t, (G : Measure C(unitInterval,ℝ)).map (fun g => g t) = gaussianReal (m t) (v t)) :
    Continuous m := by
  apply continuous_iff_seqContinuous.mpr
  intro t s ht
  apply median_tendsto_of_weak (weak_path_eval_tendsto tendsto_const_nhds ht)
  · intro n
    change (1/2 : ℝ≥0∞) ≤ ((G : Measure C(unitInterval,ℝ)).map (fun g => g (t n))) (Set.Iic (m (t n))) ∧
      (1/2 : ℝ≥0∞) ≤ ((G : Measure C(unitInterval,ℝ)).map (fun g => g (t n))) (Set.Ici (m (t n)))
    rw [hg]
    exact gaussian_median_nonstrict _ _
  · intro ε hε
    change (1/2 : ℝ≥0∞) < ((G : Measure C(unitInterval,ℝ)).map (fun g => g s)) (Set.Iio (m s+ε)) ∧
      (1/2 : ℝ≥0∞) < ((G : Measure C(unitInterval,ℝ)).map (fun g => g s)) (Set.Ioi (m s-ε))
    rw [hg]
    exact gaussian_median_strict _ _ hε

lemma weak_path_grid_medians_uniform {μ : ℕ → ProbabilityMeasure C(unitInterval,ℝ)}
    {G : ProbabilityMeasure C(unitInterval,ℝ)} (hμ : Tendsto μ atTop (𝓝 G))
    (m : unitInterval → ℝ) (v : unitInterval → ℝ≥0)
    (hg : ∀ t, (G : Measure C(unitInterval,ℝ)).map (fun g => g t) = gaussianReal (m t) (v t))
    (grid : ℕ → Set unitInterval) (b : ℕ → unitInterval → ℝ)
    (hb : ∀ n t, t ∈ grid n →
      (1/2 : ℝ≥0∞) ≤ ((μ n : Measure C(unitInterval,ℝ)).map (fun g => g t)) (Set.Iic (b n t)) ∧
      (1/2 : ℝ≥0∞) ≤ ((μ n : Measure C(unitInterval,ℝ)).map (fun g => g t)) (Set.Ici (b n t)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ t ∈ grid n, |b n t-m t| < ε := by
  by_contra hn
  simp only [eventually_atTop,not_exists,not_forall] at hn
  have hex : ∀ N : ℕ, ∃ n ≥ N, ∃ t ∈ grid n, ε ≤ |b n t-m t| := by
    intro N
    obtain ⟨n,hn⟩ := hn N
    push Not at hn
    obtain ⟨t,ht,hb⟩ := hn.2
    exact ⟨n,hn.1,t,ht,hb⟩
  choose n hn t htg hbad using hex
  have hnlim : Tendsto n atTop atTop := tendsto_atTop_mono hn tendsto_id
  obtain ⟨s,_,k,hk,ht⟩ := isCompact_univ.tendsto_subseq (fun n => Set.mem_univ (t n))
  have hm := continuous_gaussian_path_mean G m v hg |>.tendsto s |>.comp ht
  have hl := weak_path_eval_tendsto (hμ.comp (hnlim.comp hk.tendsto_atTop)) ht
  have hb' : Tendsto (fun i => b (n (k i)) (t (k i))) atTop (𝓝 (m s)) := by
    apply median_tendsto_of_weak hl
    · intro i; exact hb _ _ (htg _)
    · intro δ hδ
      change (1/2 : ℝ≥0∞) < ((G : Measure C(unitInterval,ℝ)).map (fun g => g s)) (Set.Iio (m s+δ)) ∧
        (1/2 : ℝ≥0∞) < ((G : Measure C(unitInterval,ℝ)).map (fun g => g s)) (Set.Ioi (m s-δ))
      rw [hg]
      exact gaussian_median_strict _ _ hδ
  have hz := (hb'.sub hm).abs
  have he := hz.eventually (gt_mem_nhds (show |m s-m s| < ε by simpa using hε))
  obtain ⟨i,hi⟩ := he.exists
  exact not_lt_of_ge (hbad (k i)) hi

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_PathPointMean
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma path_finite_gaussian_marginal (G : ProbabilityMeasure C(unitInterval,ℝ))
    (hG : ∀ I : Finset unitInterval,
      IsGaussian ((G : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g)))
    (t : unitInterval) : IsGaussian ((G : Measure C(unitInterval,ℝ)).map (fun g => g t)) := by
  let I : Finset unitInterval := {t}
  let μ := (G : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g)
  have : IsGaussian μ := hG I
  let L : (I → ℝ) →L[ℝ] ℝ := .proj ⟨t,by simp [I]⟩
  have he : μ.map L = (G : Measure C(unitInterval,ℝ)).map (fun g => g t) := by
    rw [Measure.map_map L.measurable (continuous_path_restrict I).measurable]
    rfl
  rw [← he]
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma path_marginal_eq_gaussian (G : ProbabilityMeasure C(unitInterval,ℝ))
    (hG : ∀ I : Finset unitInterval,
      IsGaussian ((G : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g)))
    (t : unitInterval) :
    (G : Measure C(unitInterval,ℝ)).map (fun g => g t) =
      gaussianReal (pathPointMean G t) (Var[fun g : C(unitInterval,ℝ) => g t; G]).toNNReal := by
  have : IsGaussian ((G : Measure C(unitInterval,ℝ)).map (fun g => g t)) := path_finite_gaussian_marginal G hG t
  rw [IsGaussian.eq_gaussianReal ((G : Measure C(unitInterval,ℝ)).map (fun g => g t)) inferInstance]
  congr 1
  · exact integral_map (continuous_eval_const t).measurable.aemeasurable measurable_id.aestronglyMeasurable
  · rw [variance_map measurable_id.aemeasurable (continuous_eval_const t).measurable.aemeasurable]; rfl

lemma continuous_pathPointMean (G : ProbabilityMeasure C(unitInterval,ℝ))
    (hG : ∀ I : Finset unitInterval,
      IsGaussian ((G : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g))) :
    Continuous (pathPointMean G) :=
  continuous_gaussian_path_mean G (pathPointMean G) _ (path_marginal_eq_gaussian G hG)

lemma path_finite_mean (G : ProbabilityMeasure C(unitInterval,ℝ)) (I : Finset unitInterval)
    (hG : IsGaussian ((G : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g))) :
    (∫ x, x ∂(G : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g)) =
      I.restrict (pathPointMean G) := by
  have := hG
  ext t
  change (ContinuousLinearMap.proj t : (I → ℝ) →L[ℝ] ℝ) (∫ x, x ∂(G : Measure C(unitInterval,ℝ)).map
    (fun g : C(unitInterval,ℝ) => I.restrict g)) = pathPointMean G t
  rw [← IsGaussian.integral_dual (μ := (G : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g)) (.proj t),integral_map
    (continuous_path_restrict I).measurable.aemeasurable (by fun_prop)]
  rfl

theorem path_iid_difference_centered (G W : ProbabilityMeasure C(unitInterval,ℝ)) (T : ℝ)
    (hW : ∀ I : Finset unitInterval,
      (W : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g) = gaussianPathFiniteLaw T I)
    (hG : ((G : Measure C(unitInterval,ℝ)).prod G).map
      (fun p : C(unitInterval,ℝ) × C(unitInterval,ℝ) => p.1-p.2) = W)
    (a : ℝ) (ha : a^2 = 1/2) :
    ∃ m : C(unitInterval,ℝ), (∀ t, m t = pathPointMean G t) ∧
      (G : Measure C(unitInterval,ℝ)).map (fun g => g-m) =
        (W : Measure C(unitInterval,ℝ)).map (fun g => a • g) := by
  have hg := path_of_iid_difference_gaussian G W T hW hG
  let m : C(unitInterval,ℝ) := ⟨pathPointMean G,continuous_pathPointMean G hg⟩
  refine ⟨m,fun _ => rfl,?_⟩
  apply continuous_path_measure_ext
  intro I
  let V := (G : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g)
  have hd : (V.prod V).map (fun p : (I → ℝ) × (I → ℝ) => p.1-p.2) = gaussianPathFiniteLaw T I := by
    rw [path_restrict_iid_diff,hG,hW]
  have hh := iid_difference_centered_eq_half V (gaussianPathFiniteLaw T I)
    (gaussianPathFiniteLaw_mean T I) hd a ha
  rw [path_finite_mean G I (hg I)] at hh
  rw [← hW I] at hh
  rw [Measure.map_map (show Measurable (fun x : I → ℝ => x-I.restrict (pathPointMean G)) by fun_prop)
    (continuous_path_restrict I).measurable,
    Measure.map_map (show Measurable (fun x : I → ℝ => a • x) by fun_prop)
    (continuous_path_restrict I).measurable] at hh
  rw [Measure.map_map (continuous_path_restrict I).measurable (show Measurable (fun g : C(unitInterval,ℝ) => g-m) by fun_prop),
    Measure.map_map (continuous_path_restrict I).measurable (show Measurable (fun g : C(unitInterval,ℝ) => a • g) by fun_prop)]
  exact hh

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_GridLinear
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.row_compact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma isClosed_gridLinear (q : ℝ) : IsClosed {f : C(unitInterval,ℝ) | GridLinear q f} := by
  simp only [GridLinear,Set.ofPred_forall]
  apply isClosed_iInter
  intro j
  apply isClosed_iInter
  intro u
  apply isClosed_iInter
  intro v
  apply isClosed_iInter
  intro t
  apply isClosed_iInter
  intro _
  apply isClosed_iInter
  intro _
  apply isClosed_iInter
  intro _
  apply isClosed_iInter
  intro _
  exact isClosed_eq (continuous_eval_const t) (by fun_prop)

lemma pathRestrictScale_apply (a t : unitInterval) (f : C(unitInterval,ℝ)) :
    pathRestrictScale a f t = f (a*t) := rfl

lemma gridLinear_uniform_on_shorter (q : ℕ → ℝ) (hq : Tendsto q atTop atTop)
    (f : ℕ → C(unitInterval,ℝ)) (hf : ∀ n, GridLinear (q n) (f n))
    (m : C(unitInterval,ℝ))
    (hgrid : ∀ ε > 0, ∀ᶠ n in atTop, ∀ (j : ℕ) (u : unitInterval),
      q n*(u:ℝ) = j → |f n u-m u| < ε)
    (a : unitInterval) (ha : (a:ℝ) < 1) :
    Tendsto (fun n => pathRestrictScale a (f n)) atTop (𝓝 (pathRestrictScale a m)) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨δ,hδ,hmod⟩ := Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous m.continuous)
    (ε/4) (by linarith)
  have he := hgrid (ε/4) (by linarith)
  have hbig := hq.eventually (eventually_gt_atTop (max (1/δ) (1/(1-(a:ℝ)))))
  rw [eventually_atTop] at he hbig
  obtain ⟨N,hN⟩ := he
  obtain ⟨M,hM⟩ := hbig
  refine ⟨max N M,fun n hn => ?_⟩
  have hqδ := lt_of_le_of_lt (le_max_left _ _) (hM n (le_trans (le_max_right _ _) hn))
  have hqa := lt_of_le_of_lt (le_max_right _ _) (hM n (le_trans (le_max_right _ _) hn))
  have hqpos : 0 < q n := lt_trans (one_div_pos.mpr hδ) hqδ
  have hqinvδ : 1/q n < δ := (one_div_lt hqpos hδ).mpr hqδ
  have hqinva : 1/q n < 1-(a:ℝ) := (one_div_lt hqpos (sub_pos.mpr ha)).mpr hqa
  rw [dist_eq_norm]
  apply lt_of_le_of_lt ?_ (half_lt_self hε)
  apply (ContinuousMap.norm_le_of_nonempty _).2
  intro t
  let z : unitInterval := a*t
  let j := ⌊q n*(z:ℝ)⌋₊
  have hz : 0 ≤ q n*(z:ℝ) := mul_nonneg hqpos.le z.2.1
  have hj : (j:ℝ) ≤ q n*(z:ℝ) := Nat.floor_le hz
  have hj' : q n*(z:ℝ) < (j:ℝ)+1 := Nat.lt_floor_add_one _
  have hza : (z:ℝ) ≤ (a:ℝ) := mul_le_of_le_one_right a.2.1 t.2.2
  have hu0 : 0 ≤ (j:ℝ)/q n := div_nonneg (Nat.cast_nonneg _) hqpos.le
  have hu1 : (j:ℝ)/q n ≤ (z:ℝ) := (div_le_iff₀ hqpos).2 (by simpa [mul_comm] using hj)
  have hv0 : 0 ≤ ((j:ℝ)+1)/q n := div_nonneg (by positivity) hqpos.le
  have hv1 : ((j:ℝ)+1)/q n ≤ 1 := by
    rw [add_div]
    linarith
  let u : unitInterval := ⟨(j:ℝ)/q n,hu0,hu1.trans z.2.2⟩
  let v : unitInterval := ⟨((j:ℝ)+1)/q n,hv0,hv1⟩
  have hqu : q n*(u:ℝ) = j := by dsimp [u]; field_simp
  have hqv : q n*(v:ℝ) = j+1 := by dsimp [v]; field_simp
  have hzv : (z:ℝ) ≤ v := (le_div_iff₀ hqpos).2 (by nlinarith)
  have hdu : dist u z < δ := by
    rw [Subtype.dist_eq,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hu1)]
    have hh : (z:ℝ)-(u:ℝ) < 1/q n := by
      apply (lt_div_iff₀ hqpos).2
      dsimp only [u]
      field_simp
      nlinarith
    linarith
  have hdv : dist v z < δ := by
    rw [Subtype.dist_eq,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hzv)]
    have hh : (v:ℝ)-(z:ℝ) ≤ 1/q n := by
      apply (le_div_iff₀ hqpos).2
      dsimp only [v]
      field_simp
      nlinarith
    linarith
  have hmu := hmod hdu
  have hmv := hmod hdv
  rw [Real.dist_eq] at hmu hmv
  have hgu := hN n (le_trans (le_max_left _ _) hn) j u hqu
  have hgv := hN n (le_trans (le_max_left _ _) hn) (j+1) v (by simpa using hqv)
  have heu : |f n u-m z| ≤ ε/2 := by
    calc _ ≤ |f n u-m u|+|m u-m z| := by simpa only [sub_add_sub_cancel] using abs_add_le (f n u-m u) (m u-m z)
      _ ≤ ε/2 := by linarith
  have hev : |f n v-m z| ≤ ε/2 := by
    calc _ ≤ |f n v-m v|+|m v-m z| := by simpa only [sub_add_sub_cancel] using abs_add_le (f n v-m v) (m v-m z)
      _ ≤ ε/2 := by linarith
  have hb := abs_convex_sub_le (q := q n*(z:ℝ)-j) (by linarith) (by linarith) heu hev
  rw [← hf n j u v z hqu hqv hu1 hzv] at hb
  simpa only [ContinuousMap.sub_apply,pathRestrictScale_apply,Real.norm_eq_abs] using hb

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma weak_sub_const_tendsto {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {μ : ℕ → ProbabilityMeasure E} {ν : ProbabilityMeasure E}
    (hμ : Tendsto μ atTop (𝓝 ν)) {c : ℕ → E} {b : E} (hc : Tendsto c atTop (𝓝 b)) :
    Tendsto (fun n => (μ n).map (f := (fun point => point-c n)) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
      atTop (𝓝 (ν.map (f := (fun point => point-b)) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))) := by
  have he : Continuous (fun p : E × E => p.1-p.2) := continuous_fst.sub continuous_snd
  have hh := (ProbabilityMeasure.continuous_map he).tendsto
    (ν.prod (diracProba b)) |>.comp
    (ProbabilityMeasure.continuous_prod.tendsto (ν,diracProba b) |>.comp
      (hμ.prodMk_nhds (continuous_diracProba.tendsto b |>.comp hc)))
  have hid (V : ProbabilityMeasure E) (u : E) :
      (V.prod (diracProba u)).map (f := fun pair : E × E => pair.1-pair.2) he.aemeasurable =
        V.map (f := (fun point => point-u)) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) := by
    apply Subtype.ext
    change ((V : Measure E).prod (Measure.dirac u)).map _ = _
    rw [Measure.prod_dirac,Measure.map_map he.measurable (by fun_prop)]
    rfl
  change Tendsto (fun n => ((μ n).prod (diracProba (c n))).map (f := fun pair : E × E => pair.1-pair.2) he.aemeasurable)
    atTop (𝓝 ((ν.prod (diracProba b)).map (f := fun pair : E × E => pair.1-pair.2) he.aemeasurable)) at hh
  simpa only [hid] using hh

lemma weak_sequence_tight {E : Type*} [MetricSpace E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {μ : ℕ → ProbabilityMeasure E} {ν : ProbabilityMeasure E}
    (hμ : Tendsto μ atTop (𝓝 ν)) :
    IsTightMeasureSet (Set.range (fun n => (μ n : Measure E))) := by
  have hc : IsCompact (closure (Set.range μ)) :=
    hμ.isCompact_insert_range.closure_of_subset (Set.subset_insert _ _)
  have h := isTightMeasureSet_of_isCompact_closure hc
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp

lemma GridLinear.sub {q : ℝ} {f g : C(unitInterval,ℝ)}
    (hf : GridLinear q f) (hg : GridLinear q g) : GridLinear q (f-g) := by
  intro j u v t hu hv htu htv
  simp only [ContinuousMap.sub_apply,hf j u v t hu hv htu htv,hg j u v t hu hv htu htv]
  ring

theorem path_grid_median_limit_from_iid_difference
    (μ : ℕ → ProbabilityMeasure C(unitInterval,ℝ)) (W : ProbabilityMeasure C(unitInterval,ℝ))
    (T : ℝ) (hW : ∀ I : Finset unitInterval,
      (W : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g) = gaussianPathFiniteLaw T I)
    (hd : Tendsto (fun n => ((μ n).prod (μ n)).map (f := fun pair : C(unitInterval,ℝ) × C(unitInterval,ℝ) => pair.1-pair.2) (continuous_fst.sub continuous_snd).aemeasurable) atTop (𝓝 W))
    (q : ℕ → ℝ) (hq : Tendsto q atTop atTop)
    (hμ : ∀ n, ∀ᵐ f ∂(μ n : Measure C(unitInterval,ℝ)), GridLinear (q n) f)
    (b : ℕ → C(unitInterval,ℝ)) (hbl : ∀ n, GridLinear (q n) (b n))
    (hb : ∀ n (j : ℕ) (t : unitInterval), q n*(t:ℝ) = j →
      (1/2 : ℝ≥0∞) ≤ ((μ n : Measure C(unitInterval,ℝ)).map (fun g => g t)) (Set.Iic (b n t)) ∧
      (1/2 : ℝ≥0∞) ≤ ((μ n : Measure C(unitInterval,ℝ)).map (fun g => g t)) (Set.Ici (b n t)))
    (s : ℝ) (hs : s^2 = 1/2) (a : unitInterval) (ha : (a:ℝ) < 1) :
    Tendsto (fun n => (μ n).map (f := (fun path => pathRestrictScale a (path-b n))) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop
      (𝓝 (W.map (f := (fun path => s • pathRestrictScale a path)) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))) := by
  have ht := weak_sequence_tight hd
  obtain ⟨c,hc,htc⟩ := tight_iid_difference_translations_support
    (fun n => (μ n : Measure C(unitInterval,ℝ))) (fun n => {f | GridLinear (q n) f}) hμ ht
  let V : ℕ → ProbabilityMeasure C(unitInterval,ℝ) := fun n =>
    (μ n).map (f := (fun path => path-c n)) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hcpt : IsCompact (closure (Set.range V)) := isCompact_closure_of_isTightMeasureSet (S := Set.range V) (by
    have he : {M : Measure C(unitInterval,ℝ) | ∃ Q ∈ Set.range V, (Q : Measure C(unitInterval,ℝ)) = M} =
        Set.range (fun i => (μ i : Measure C(unitInterval,ℝ)).map (fun x => x-c i)) := by
      ext M
      constructor
      · rintro ⟨Q,⟨i,rfl⟩,rfl⟩
        exact ⟨i,rfl⟩
      · rintro ⟨i,rfl⟩
        exact ⟨V i,⟨i,rfl⟩,rfl⟩
    rw [he]
    exact htc)
  apply Filter.tendsto_of_subseq_tendsto
  intro k hk
  obtain ⟨G,_,l,hl,hG⟩ := hcpt.tendsto_subseq (fun j => subset_closure (Set.mem_range_self (k j)))
  let n := k ∘ l
  have hn : Tendsto n atTop atTop := hk.comp hl.tendsto_atTop
  have hdG : ((G : Measure C(unitInterval,ℝ)).prod G).map
      (fun p : C(unitInterval,ℝ) × C(unitInterval,ℝ) => p.1-p.2) = W := by
    have h := weak_iid_difference_tendsto hG
    have he (i : ℕ) : ((V (n i)).prod (V (n i))).map (f := fun pair : C(unitInterval,ℝ) × C(unitInterval,ℝ) => pair.1-pair.2) (continuous_fst.sub continuous_snd).aemeasurable =
        ((μ (n i)).prod (μ (n i))).map (f := fun pair : C(unitInterval,ℝ) × C(unitInterval,ℝ) => pair.1-pair.2) (continuous_fst.sub continuous_snd).aemeasurable := by
      apply Subtype.ext
      exact iid_diff_translation (μ (n i)) (c (n i))
    change Tendsto (fun i => ((V (n i)).prod (V (n i))).map (f := fun pair : C(unitInterval,ℝ) × C(unitInterval,ℝ) => pair.1-pair.2) (continuous_fst.sub continuous_snd).aemeasurable) atTop _ at h
    simp only [he] at h
    exact congrArg (fun Q : ProbabilityMeasure C(unitInterval,ℝ) => (Q : Measure C(unitInterval,ℝ)))
      (tendsto_nhds_unique h (hd.comp hn))
  obtain ⟨m,hm,hcenter⟩ := path_iid_difference_centered G W T hW hdG s hs
  have hg := path_of_iid_difference_gaussian G W T hW hdG
  have hmed : ∀ ε > 0, ∀ᶠ i in atTop, ∀ (j : ℕ) (t : unitInterval),
      q (n i)*(t:ℝ) = j → |(b (n i)-c (n i)) t-m t| < ε := by
    intro ε hε
    have h := weak_path_grid_medians_uniform hG (pathPointMean G) _
      (path_marginal_eq_gaussian G hg) (fun i => {t | ∃ j : ℕ, q (n i)*(t:ℝ) = j})
      (fun i t => (b (n i)-c (n i)) t) ?_ hε
    · filter_upwards [h] with i hi j t ht
      simpa only [hm t] using hi t ⟨j,ht⟩
    · intro i t ht
      obtain ⟨j,hjt⟩ := ht
      have hbt := hb (n i) j t hjt
      change (1/2 : ℝ≥0∞) ≤ ((V (n i) : Measure C(unitInterval,ℝ)).map (fun g => g t)) _ ∧
        (1/2 : ℝ≥0∞) ≤ ((V (n i) : Measure C(unitInterval,ℝ)).map (fun g => g t)) _
      change (1/2 : ℝ≥0∞) ≤ (((μ (n i) : Measure C(unitInterval,ℝ)).map (fun g => g-c (n i))).map (fun g => g t)) _ ∧
        (1/2 : ℝ≥0∞) ≤ (((μ (n i) : Measure C(unitInterval,ℝ)).map (fun g => g-c (n i))).map (fun g => g t)) _
      rw [Measure.map_map (continuous_eval_const t).measurable (by fun_prop)]
      rw [Measure.map_apply (by fun_prop) measurableSet_Iic,Measure.map_apply (by fun_prop) measurableSet_Ici]
      rw [Measure.map_apply (continuous_eval_const t).measurable measurableSet_Iic,
        Measure.map_apply (continuous_eval_const t).measurable measurableSet_Ici] at hbt
      simpa only [Function.comp_def,Set.preimage,Set.mem_Iic,Set.mem_Ici,
        ContinuousMap.sub_apply,sub_le_sub_iff_right] using hbt
  have hmconv := gridLinear_uniform_on_shorter (q ∘ n) (hq.comp hn)
    (fun i => b (n i)-c (n i)) (fun i => (hbl _).sub (hc _)) m hmed a ha
  have hVres := (ProbabilityMeasure.continuous_map (pathRestrictScale a).continuous).tendsto G |>.comp hG
  have hcconv := weak_sub_const_tendsto hVres hmconv
  refine ⟨l,?_⟩
  have he (i : ℕ) : ((V (n i)).map (f := pathRestrictScale a) (pathRestrictScale a).continuous.aemeasurable).map (f := fun path => path-pathRestrictScale a (b (n i)-c (n i))) (continuous_id.sub continuous_const).aemeasurable =
      (μ (n i)).map (f := (fun path => pathRestrictScale a (path-b (n i)))) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) := by
    apply Subtype.ext
    change (((μ (n i) : Measure C(unitInterval,ℝ)).map _).map _).map _ = _
    rw [Measure.map_map (by fun_prop) (pathRestrictScale a).measurable,
      Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext f
    simp only [Function.comp_apply,← map_sub]
    congr 1
    abel
  have heG : (G.map (f := pathRestrictScale a) (pathRestrictScale a).continuous.aemeasurable).map (f := fun path => path-pathRestrictScale a m) (continuous_id.sub continuous_const).aemeasurable =
      W.map (f := (fun path => s • pathRestrictScale a path)) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) := by
    apply Subtype.ext
    change ((G : Measure C(unitInterval,ℝ)).map (pathRestrictScale a)).map
      (fun f => f-pathRestrictScale a m) =
        (W : Measure C(unitInterval,ℝ)).map (fun g => s • pathRestrictScale a g)
    rw [Measure.map_map (by fun_prop) (pathRestrictScale a).measurable]
    have hh := congrArg (fun M : Measure C(unitInterval,ℝ) => M.map (pathRestrictScale a)) hcenter
    rw [Measure.map_map (pathRestrictScale a).measurable (by fun_prop),
      Measure.map_map (pathRestrictScale a).measurable (by fun_prop)] at hh
    simpa only [Function.comp_def,map_sub,map_smul] using hh
  change Tendsto (fun i => ((V (n i)).map (f := pathRestrictScale a) (pathRestrictScale a).continuous.aemeasurable).map (f := fun path => path-pathRestrictScale a (b (n i)-c (n i))) (continuous_id.sub continuous_const).aemeasurable)
    atTop (𝓝 ((G.map (f := pathRestrictScale a) (pathRestrictScale a).continuous.aemeasurable).map (f := fun path => path-pathRestrictScale a m) (continuous_id.sub continuous_const).aemeasurable)) at hcconv
  simp only [he,heG] at hcconv
  convert hcconv using 1
  all_goals try with_reducible_and_instances rfl
  funext i
  apply Subtype.ext
  rfl

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_HeightIncrement
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma realPartialSum_heightIncrement (F : ℕ → ℝ) (h : ℕ) :
    realPartialSum (heightIncrement F) h = F h-F 0 := by
  induction h with
  | zero => simp [realPartialSum]
  | succ h ih => rw [realPartialSum_succ,ih,heightIncrement]; ring

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_HeightPolygon
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma heightPolygon_formula (F : ℕ → ℝ) (r n T : ℝ) (h : 0 ≤ T*n) (t : unitInterval) :
    heightPolygon F r n T t =
      (F ⌊T*n*(t:ℝ)⌋₊ + (T*n*(t:ℝ)-⌊T*n*(t:ℝ)⌋₊)*
        (F (⌊T*n*(t:ℝ)⌋₊+1)-F ⌊T*n*(t:ℝ)⌋₊))/r := by
  have ht : 0 ≤ T*n*(t:ℝ) := mul_nonneg h t.2.1
  have hN : ⌊T*n*(t:ℝ)⌋₊ < ⌊T*n⌋₊+1 :=
    Nat.lt_succ_of_le (Nat.floor_mono (mul_le_of_le_one_right h t.2.2))
  simp only [heightPolygon,ContinuousMap.add_apply,ContinuousMap.const_apply,scaledPolygon_apply,
    linearPolygon_formula _ _ ht hN,realPartialSum_heightIncrement,heightIncrement]
  ring

lemma heightPolygon_grid (F : ℕ → ℝ) (r n T : ℝ) (h : 0 ≤ T*n)
    (j : ℕ) (t : unitInterval) (ht : T*n*(t:ℝ) = j) :
    heightPolygon F r n T t = F j/r := by
  rw [heightPolygon_formula F r n T h,ht]
  simp

lemma scaledPolygon_sub (x y : ℕ → ℝ) (r n T : ℝ) :
    scaledPolygon (fun k => x k-y k) r n T = scaledPolygon x r n T-scaledPolygon y r n T := by
  ext t
  simp only [scaledPolygon_apply,ContinuousMap.sub_apply,linearPolygon,mul_sub,Finset.sum_sub_distrib,sub_div]

lemma heightPolygon_sub (F G : ℕ → ℝ) (r n T : ℝ) :
    heightPolygon (fun k => F k-G k) r n T = heightPolygon F r n T-heightPolygon G r n T := by
  have he : heightIncrement (fun k => F k-G k) = fun k => heightIncrement F k-heightIncrement G k := by
    funext k
    simp only [heightIncrement]
    ring
  ext t
  simp only [heightPolygon,he,scaledPolygon_sub,sub_div,ContinuousMap.add_apply,
    ContinuousMap.sub_apply,ContinuousMap.const_apply]
  ring

lemma heightPolygon_segment (F : ℕ → ℝ) (r n T : ℝ) (h : 0 ≤ T*n)
    (j : ℕ) (t : unitInterval) (hjt : (j:ℝ) ≤ T*n*(t:ℝ)) (htj : T*n*(t:ℝ) ≤ (j:ℝ)+1) :
    heightPolygon F r n T t =
      (F j+(T*n*(t:ℝ)-j)*(F (j+1)-F j))/r := by
  by_cases he : T*n*(t:ℝ) = (j:ℝ)+1
  · rw [heightPolygon_grid F r n T h (j+1) t (by simpa using he),he]
    congr 1
    ring
  · have hj : ⌊T*n*(t:ℝ)⌋₊ = j := Nat.floor_eq_iff (mul_nonneg h t.2.1) |>.mpr ⟨hjt,lt_of_le_of_ne htj he⟩
    rw [heightPolygon_formula F r n T h,hj]

lemma heightPolygon_gridLinear (F : ℕ → ℝ) (r n T : ℝ) (h : 0 ≤ T*n) :
    GridLinear (T*n) (heightPolygon F r n T) := by
  intro j u v t hu hv htu htv
  have hjt : (j:ℝ) ≤ T*n*(t:ℝ) := hu ▸ mul_le_mul_of_nonneg_left htu h
  have htj : T*n*(t:ℝ) ≤ (j:ℝ)+1 := hv ▸ mul_le_mul_of_nonneg_left htv h
  rw [heightPolygon_segment F r n T h j t hjt htj,
    heightPolygon_grid F r n T h j u hu,
    heightPolygon_grid F r n T h (j+1) v (by simpa using hv)]
  ring

lemma heightPolygon_restrict (F : ℕ → ℝ) (r n T S : ℝ) (hn : 0 ≤ n)
    (hT : 0 ≤ T) (hS : 0 ≤ S) (a : unitInterval) (ha : S*(a:ℝ) = T) :
    pathRestrictScale a (heightPolygon F r n S) = heightPolygon F r n T := by
  ext t
  rw [pathRestrictScale_apply,heightPolygon_formula F r n S (mul_nonneg hS hn),
    heightPolygon_formula F r n T (mul_nonneg hT hn)]
  have he : S*n*((a*t:unitInterval):ℝ) = T*n*(t:ℝ) := by
    change S*n*((a:ℝ)*(t:ℝ)) = T*n*(t:ℝ)
    rw [← ha]
    ring
  rw [he]

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_GaussianPathFiniteLawSmul
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.row_compact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma gaussianPathFiniteLaw_smul (T a : ℝ) (I : Finset unitInterval) :
    (gaussianPathFiniteLaw T I).map (fun x => a • x) = gaussianPathFiniteLaw (a^2*T) I := by
  unfold gaussianPathFiniteLaw
  let v := fun j : Fin I.card => Real.toNNReal (T*((orderedTimes I j.succ:ℝ)-orderedTimes I j.castSucc))
  have he (j : Fin I.card) : (gaussianReal 0 (v j)).map (fun x : ℝ => a*x) =
      gaussianReal 0 (Real.toNNReal ((a^2*T)*((orderedTimes I j.succ:ℝ)-orderedTimes I j.castSucc))) := by
    rw [gaussianReal_map_const_mul,mul_zero]
    congr 1
    have hsq : NNReal.mk (a^2) (sq_nonneg a) = Real.toNNReal (a^2) := by
      apply NNReal.eq
      simp only [NNReal.coe_mk,Real.coe_toNNReal']
      exact (max_eq_left (sq_nonneg a)).symm
    rw [hsq,← Real.toNNReal_mul (sq_nonneg a)]
    congr 1
    ring
  have hpi := Measure.pi_map_pi (μ := fun j : Fin I.card => gaussianReal 0 (v j))
    (f := fun _ (x : ℝ) => a*x) (fun _ => by fun_prop)
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rw [show (fun x => a • x) ∘ incrementCumsum I = incrementCumsum I ∘ (fun x => a • x) by ext x; simp]
  rw [← Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  change (Measure.pi (fun j => gaussianReal 0 (v j))).map (fun x i => a*x i) = _
  rw [hpi]
  congr 1
  funext j
  exact he j

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma median_div {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω → ℝ) (hF : Measurable F) (b r : ℝ)
    (hb : (1/2 : ℝ≥0∞) ≤ μ {x | F x ≤ b} ∧ (1/2 : ℝ≥0∞) ≤ μ {x | b ≤ F x}) :
    (1/2 : ℝ≥0∞) ≤ (μ.map (fun x => F x/r)) (Set.Iic (b/r)) ∧
    (1/2 : ℝ≥0∞) ≤ (μ.map (fun x => F x/r)) (Set.Ici (b/r)) := by
  rw [Measure.map_apply (hF.div_const r) measurableSet_Iic,
    Measure.map_apply (hF.div_const r) measurableSet_Ici]
  rcases lt_trichotomy r 0 with hr|hr|hr
  · simpa only [Set.preimage,Set.mem_Iic,Set.mem_Ici,div_le_div_right_of_neg hr] using hb.symm
  · subst r
    simp
  · simpa only [Set.preimage,Set.mem_Iic,Set.mem_Ici,div_le_div_iff_of_pos_right hr] using hb

lemma heightPathLaw_iid_difference {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → Ω → ℝ) (hF : ∀ k, Measurable (F k)) (r n T : ℝ) :
    (((heightPathLaw μ F hF r n T : Measure C(unitInterval,ℝ)).prod
      (heightPathLaw μ F hF r n T)).map (fun p : C(unitInterval,ℝ) × C(unitInterval,ℝ) => p.1-p.2)) =
      (μ.prod μ).map (fun p => heightPolygon (fun k => F k p.1-F k p.2) r n T) := by
  change ((μ.map _).prod (μ.map _)).map _ = _
  rw [Measure.map_prod_map _ _ (measurable_heightPolygon F hF _ _ _) (measurable_heightPolygon F hF _ _ _),
    Measure.map_map (by fun_prop) ((measurable_heightPolygon F hF _ _ _).prodMap (measurable_heightPolygon F hF _ _ _))]
  congr 1
  ext p t
  exact congrArg (fun g : C(unitInterval,ℝ) => g t) (heightPolygon_sub _ _ _ _ _).symm

theorem height_median_path_limit_oai {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : ℕ → Ω → ℝ)
    (hF : ∀ k, Measurable (F k)) (b : ℕ → ℝ)
    (hb : ∀ k, (1/2 : ℝ≥0∞) ≤ μ {x | F k x ≤ b k} ∧ (1/2 : ℝ≥0∞) ≤ μ {x | b k ≤ F k x})
    (r n : ℕ → ℝ) (hn : ∀ i, 0 ≤ n i) (hnlim : Tendsto n atTop atTop) (c : ℝ)
    (hd : ∀ S : ℝ, 0 ≤ S → ∃ W : ProbabilityMeasure C(unitInterval,ℝ),
      Tendsto (fun i => ((heightPathLaw μ F hF (r i) (n i) S).prod
        (heightPathLaw μ F hF (r i) (n i) S)).map (f := fun pair : C(unitInterval,ℝ) × C(unitInterval,ℝ) => pair.1-pair.2) (continuous_fst.sub continuous_snd).aemeasurable) atTop (𝓝 W) ∧
      ∀ I : Finset unitInterval,
        (W : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g) = gaussianPathFiniteLaw (S/c) I)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ W : ProbabilityMeasure C(unitInterval,ℝ),
      TendstoInDistribution (fun i x => heightPolygon (fun k => F k x-b k) (r i) (n i) T)
        atTop id (fun _ => μ) W ∧
      ∀ I : Finset unitInterval,
        (W : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g) = gaussianPathFiniteLaw (T/(2*c)) I := by
  let S := T+1
  have hS : 0 < S := by dsimp [S] <;> linarith
  let a : unitInterval := ⟨T/S,div_nonneg hT hS.le,(div_le_one hS).2 (by dsimp [S] <;> linarith)⟩
  have ha : (a:ℝ) < 1 := (div_lt_one hS).2 (by dsimp [S] <;> linarith)
  have haS : S*(a:ℝ) = T := by dsimp [a]; field_simp
  obtain ⟨WS,hWS,hWSf⟩ := hd S hS.le
  obtain ⟨WT,hWT,hWTf⟩ := hd T hT
  have hrestrict : WS.map (f := pathRestrictScale a) (pathRestrictScale a).continuous.aemeasurable = WT := by
    have h := (ProbabilityMeasure.continuous_map (pathRestrictScale a).continuous).tendsto WS |>.comp hWS
    have he (i : ℕ) : (((heightPathLaw μ F hF (r i) (n i) S).prod
        (heightPathLaw μ F hF (r i) (n i) S)).map (f := fun pair : C(unitInterval,ℝ) × C(unitInterval,ℝ) => pair.1-pair.2) (continuous_fst.sub continuous_snd).aemeasurable).map
        (f := pathRestrictScale a) (pathRestrictScale a).continuous.aemeasurable =
      ((heightPathLaw μ F hF (r i) (n i) T).prod
        (heightPathLaw μ F hF (r i) (n i) T)).map
          (f := fun pair : C(unitInterval,ℝ) × C(unitInterval,ℝ) => pair.1-pair.2) (continuous_fst.sub continuous_snd).aemeasurable := by
      apply Subtype.ext
      change (((heightPathLaw μ F hF (r i) (n i) S : Measure C(unitInterval,ℝ)).prod
        (heightPathLaw μ F hF (r i) (n i) S : Measure C(unitInterval,ℝ))).map
          (fun p : C(unitInterval,ℝ) × C(unitInterval,ℝ) => p.1-p.2)).map (pathRestrictScale a) =
        ((heightPathLaw μ F hF (r i) (n i) T : Measure C(unitInterval,ℝ)).prod
          (heightPathLaw μ F hF (r i) (n i) T : Measure C(unitInterval,ℝ))).map
            (fun p : C(unitInterval,ℝ) × C(unitInterval,ℝ) => p.1-p.2)
      rw [heightPathLaw_iid_difference,Measure.map_map (pathRestrictScale a).measurable (measurable_heightPolygon (fun k (p : Ω × Ω) => F k p.1-F k p.2) (fun k => ((hF k).comp measurable_fst).sub ((hF k).comp measurable_snd)) (r i) (n i) S),
        heightPathLaw_iid_difference]
      congr 1
      funext p
      exact heightPolygon_restrict _ _ _ _ _ (hn i) hT hS.le a haS
    exact tendsto_nhds_unique (by simpa only [Function.comp_def,he] using h) hWT
  let Q := fun i => heightPathLaw μ F hF (r i) (n i) S
  let B := fun i => heightPolygon b (r i) (n i) S
  let s := Real.sqrt (1/2)
  have hs : s^2 = 1/2 := Real.sq_sqrt (by norm_num)
  have hlim := path_grid_median_limit_from_iid_difference Q WS (S/c) hWSf hWS
    (fun i => S*n i) (hnlim.const_mul_atTop hS)
    (fun i => ?_) B (fun i => heightPolygon_gridLinear b _ _ _ (mul_nonneg hS.le (hn i)))
    (fun i j t ht => ?_) s hs a ha
  · let W := WT.map (f := fun path : C(unitInterval,ℝ) => s • path) (continuous_const_smul s).aemeasurable
    refine ⟨W,⟨fun i => (measurable_heightPolygon (fun k x => F k x-b k)
      (fun k => (hF k).sub_const _) _ _ _).aemeasurable,measurable_id.aemeasurable,?_⟩,?_⟩
    · have he (i : ℕ) : (Q i).map (f := fun path : C(unitInterval,ℝ) => pathRestrictScale a (path-B i)) ((pathRestrictScale a).continuous.comp (continuous_id.sub continuous_const)).aemeasurable =
        (⟨μ.map (fun x => heightPolygon (fun k => F k x-b k) (r i) (n i) T),
          (Measure.isProbabilityMeasure_map_iff
            (measurable_heightPolygon _ (fun k => (hF k).sub_const _) _ _ _).aemeasurable).2 inferInstance⟩ :
            ProbabilityMeasure C(unitInterval,ℝ)) := by
        apply Subtype.ext
        change (μ.map _).map _ = _
        rw [Measure.map_map (by fun_prop) (measurable_heightPolygon F hF _ _ _)]
        congr 1
        funext x
        change pathRestrictScale a (heightPolygon (fun k => F k x) (r i) (n i) S-B i) = _
        rw [← heightPolygon_sub]
        exact heightPolygon_restrict _ _ _ _ _ (hn i) hT hS.le a haS
      have heW : WS.map (f := fun path : C(unitInterval,ℝ) => s • pathRestrictScale a path) (Continuous.aemeasurable (by fun_prop)) = W := by
        rw [show W = (WS.map (f := pathRestrictScale a) (pathRestrictScale a).continuous.aemeasurable).map
          (f := fun path : C(unitInterval,ℝ) => s • path) (continuous_const_smul s).aemeasurable by rw [hrestrict]]
        apply Subtype.ext
        exact (Measure.map_map (by fun_prop) (pathRestrictScale a).measurable).symm
      change Tendsto _ atTop (𝓝 (W.map (f := id) aemeasurable_id))
      have hid : W.map (f := id) aemeasurable_id = W := by apply Subtype.ext; exact Measure.map_id
      rw [hid]
      simpa only [he,heW] using hlim
    · intro I
      change ((WT : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => s • g)).map _ = _
      rw [Measure.map_map (continuous_path_restrict I).measurable (by fun_prop)]
      have he : (fun g : C(unitInterval,ℝ) => I.restrict (s • g)) =
          (fun x : I → ℝ => s • x) ∘ (fun g : C(unitInterval,ℝ) => I.restrict g) := rfl
      change (WT : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict (s • g)) = _
      rw [he,← Measure.map_map (by fun_prop) (continuous_path_restrict I).measurable,hWTf,
        gaussianPathFiniteLaw_smul,hs]
      congr 1
      ring
  · change ∀ᵐ f ∂μ.map (fun x => heightPolygon (fun k => F k x) (r i) (n i) S), GridLinear (S*n i) f
    rw [ae_map_iff (measurable_heightPolygon F hF _ _ _).aemeasurable
      (isClosed_gridLinear _).measurableSet]
    exact ae_of_all _ (fun x => heightPolygon_gridLinear _ _ _ _ (mul_nonneg hS.le (hn i)))
  · change (1/2 : ℝ≥0∞) ≤ ((μ.map (fun x => heightPolygon (fun k => F k x) (r i) (n i) S)).map
        (fun g => g t)) (Set.Iic (B i t)) ∧
      (1/2 : ℝ≥0∞) ≤ ((μ.map (fun x => heightPolygon (fun k => F k x) (r i) (n i) S)).map
        (fun g => g t)) (Set.Ici (B i t))
    rw [Measure.map_map (continuous_eval_const t).measurable (measurable_heightPolygon F hF _ _ _)]
    have he : (fun g : C(unitInterval,ℝ) => g t) ∘ (fun x => heightPolygon (fun k => F k x) (r i) (n i) S) =
        fun x => F j x/r i := by
      funext x
      exact heightPolygon_grid _ _ _ _ (mul_nonneg hS.le (hn i)) j t ht
    rw [he,show B i t = b j/r i from heightPolygon_grid _ _ _ _ (mul_nonneg hS.le (hn i)) j t ht]
    exact median_div μ (F j) (hF j) (b j) (r i) (hb j)

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.DirectionalTransience.height_median_path_limit_oai.{u_1} := @OAI.DirectionalTransience.height_median_path_limit_oai.{u_1}
