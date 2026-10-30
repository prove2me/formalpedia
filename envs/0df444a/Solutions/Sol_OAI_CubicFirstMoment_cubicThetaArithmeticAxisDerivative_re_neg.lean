-- Prove2me | solution 1 for OAI.CubicFirstMoment.cubicThetaArithmeticAxisDerivative_re_neg
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:24:53.675837+00:00
-- url     : https://prove2.me/submissions/2c53953d-3fc8-4598-91e2-bd3dee0b1c9d

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A019

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicBesselDerivative
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiate the fixed order-one-third heat integral on its positive
axis. The dominating inverse Laplace moment is integrable there. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace CubicFirstMoment

lemma cubicBesselHeat_hasDerivAt (x t : ℝ) :
    HasDerivAt (fun y => cubicBesselHeat y t) (cubicBesselHeatDerivative x t) x := by
  have h := (((hasDerivAt_id x).neg.div_const t).exp).const_mul
    (t^(-4/3:ℝ)*Real.exp (-t))
  simp only [Pi.neg_apply,id_eq] at h
  refine h.congr_deriv ?_
  · unfold cubicBesselHeatDerivative cubicBesselHeat
    ring

lemma cubicBesselHeatDerivative_local_bound {a x t : ℝ} (hax : a≤x) (ht : 0<t) :
    ‖cubicBesselHeatDerivative x t‖≤t^(-7/3:ℝ)*Real.exp (-a/t) := by
  have h := div_le_div_of_nonneg_right (cubicBesselHeat_local_bound hax ht) ht.le
  have he : t^(-4/3:ℝ)/t=t^(-7/3:ℝ) := by
    calc
      _ = t^(-4/3:ℝ)/t^(1:ℝ) := by rw [Real.rpow_one]
      _ = t^((-4/3:ℝ)-1) := (Real.rpow_sub ht _ _).symm
      _ = _ := by norm_num
  simpa only [cubicBesselHeatDerivative,norm_div,norm_neg,Real.norm_eq_abs,
    abs_of_pos ht,mul_div_right_comm,he] using h

lemma cubicBesselHeat_integral_hasDerivAt {x : ℝ} (hx : 0<x) :
    HasDerivAt (fun y => ∫ t in Ioi (0:ℝ),cubicBesselHeat y t)
      (∫ t in Ioi (0:ℝ),cubicBesselHeatDerivative x t) x := by
  have hi : IntegrableOn (fun t : ℝ => t^(-7/3:ℝ)*Real.exp (-(x/2)/t)) (Ioi 0) := by
    convert integrable_inverse_laplace_rpow (by norm_num : (0:ℝ)<4/3)
      (show 0<x/2 by positivity) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s:=Ioi (x/2)) (bound:=fun t : ℝ => t^(-7/3:ℝ)*Real.exp (-(x/2)/t))
    (isOpen_Ioi.mem_nhds (by change x/2<x; linarith))
    (Eventually.of_forall (fun y => by
      apply Measurable.aestronglyMeasurable
      unfold cubicBesselHeat
      fun_prop)) (cubicBesselHeat_integrable hx) ?_ ?_ hi ?_).2
  · apply Measurable.aestronglyMeasurable
    unfold cubicBesselHeatDerivative cubicBesselHeat
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro y hy
    exact cubicBesselHeatDerivative_local_bound hy.le ht
  · filter_upwards with t
    intro y _
    exact cubicBesselHeat_hasDerivAt y t

theorem cubicBesselKernel_hasDerivAt {x : ℝ} (hx : 0<x) :
    HasDerivAt cubicBesselKernel (cubicBesselKernelDerivative x) x := by
  have hp := Real.hasDerivAt_rpow_const (x:=x) (p:=(1/6:ℝ)) (Or.inl (ne_of_gt hx))
  have h := hp.mul (cubicBesselHeat_integral_hasDerivAt hx)
  refine h.congr_deriv ?_
  · norm_num [cubicBesselKernelDerivative]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicBesselLogIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed cubic Bessel kernel in logarithmic coordinates. This form
will give quantitative sign estimates for the actual theta normalization. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubicBessel_scaled_heat {a t : ℝ} (ha : 0<a) (ht : 0<t) :
    (a^2)^(1/6:ℝ)*a*cubicBesselHeat (a^2) (a*t)=
      t^(-4/3:ℝ)*Real.exp (-a*(t+t⁻¹)) := by
  unfold cubicBesselHeat
  rw [Real.mul_rpow ha.le ht.le,←Real.rpow_natCast_mul ha.le]
  have hp : a^(2*(1/6:ℝ))*a*a^(-4/3:ℝ)=1 := by
    calc
      _ = a^(2*(1/6:ℝ))*a^(1:ℝ)*a^(-4/3:ℝ) := by rw [Real.rpow_one]
      _ = a^(2*(1/6:ℝ)+1+(-4/3:ℝ)) := by rw [←Real.rpow_add ha,←Real.rpow_add ha]
      _ = 1 := by norm_num
  have he : -(a^2)/(a*t)= -a*t⁻¹ := by field_simp
  rw [he]
  calc
    _ = (a^(2*(1/6:ℝ))*a*a^(-4/3:ℝ))*t^(-4/3:ℝ)*
        (Real.exp (-(a*t))*Real.exp (-a*t⁻¹)) := by ring_nf
    _ = _ := by rw [hp,one_mul,←Real.exp_add]; congr 2; ring_nf

lemma cubicBesselKernel_scaled_integral {a : ℝ} (ha : 0<a) :
    cubicBesselKernel (a^2)=
      ∫ t in Ioi (0:ℝ),t^(-4/3:ℝ)*Real.exp (-a*(t+t⁻¹)) := by
  have h := integral_comp_mul_left_Ioi' (cubicBesselHeat (a^2)) 0 ha
  rw [mul_zero,smul_eq_mul] at h
  rw [cubicBesselKernel,←h,←integral_const_mul,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  simpa only [mul_assoc] using cubicBessel_scaled_heat ha ht

lemma integral_comp_exp_whole (g : ℝ → ℝ) :
    ∫ x : ℝ, Real.exp x • g (Real.exp x) = ∫ y in Set.Ioi (0 : ℝ), g y := by
  have h := MeasureTheory.integral_image_eq_integral_abs_deriv_smul (s := Set.univ)
    MeasurableSet.univ (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (fun x _ y _ hxy => Real.exp_injective hxy) g
  rw [Set.image_univ, Real.range_exp, MeasureTheory.setIntegral_univ] at h
  simpa [abs_of_pos (Real.exp_pos _)] using h.symm

lemma cubicBesselKernel_log_integral {a : ℝ} (ha : 0<a) :
    cubicBesselKernel (a^2)=
      ∫ u : ℝ,Real.exp (-u/3)*Real.exp (-2*a*Real.cosh u) := by
  rw [cubicBesselKernel_scaled_integral ha,
    ←integral_comp_exp_whole (fun t : ℝ => t^(-4/3:ℝ)*Real.exp (-a*(t+t⁻¹)))]
  apply integral_congr_ae
  filter_upwards with u
  simp only [smul_eq_mul]
  rw [←Real.exp_mul]
  have he : Real.exp u*Real.exp (u*(-4/3))=Real.exp (-u/3) := by
    rw [←Real.exp_add]
    congr 1
    ring
  rw [←mul_assoc,he,Real.cosh_eq]
  rw [Real.exp_neg]
  congr 2
  ring_nf

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicBesselLogIntegrable
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute integrability of the logarithmic cubic Bessel weight. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubicBesselLogWeight_pos (a u : ℝ) : 0 < cubicBesselLogWeight a u :=
  mul_pos (Real.exp_pos _) (Real.exp_pos _)

lemma integrable_comp_exp_whole (g : ℝ → ℝ) :
    Integrable (fun x : ℝ => Real.exp x • g (Real.exp x)) ↔ IntegrableOn g (Set.Ioi (0 : ℝ)) := by
  have h := MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul (s := Set.univ)
    MeasurableSet.univ (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (fun x _ y _ hxy => Real.exp_injective hxy) g
  rw [Set.image_univ, Real.range_exp, MeasureTheory.integrableOn_univ] at h
  have h2 : (fun x : ℝ => |Real.exp x| • g (Real.exp x)) =
      fun x : ℝ => Real.exp x • g (Real.exp x) := by
    funext x
    rw [abs_of_pos (Real.exp_pos x)]
  rw [h2] at h
  exact h.symm

lemma cubicBesselLogWeight_integrable {a : ℝ} (ha : 0<a) :
    Integrable (cubicBesselLogWeight a) := by
  have hi : IntegrableOn (fun t : ℝ => cubicBesselHeat (a^2) (a*t)) (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff _ 0 ha).mpr
    simpa only [mul_zero] using cubicBesselHeat_integrable (sq_pos_of_pos ha)
  have hg : IntegrableOn (fun t : ℝ => t^(-4/3:ℝ)*Real.exp (-a*(t+t⁻¹))) (Ioi 0) := by
    apply ((hi.const_mul a).const_mul ((a^2)^(1/6:ℝ))).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simpa only [mul_assoc] using cubicBessel_scaled_heat ha ht
  have hl := (integrable_comp_exp_whole _).mpr hg
  apply hl.congr
  filter_upwards with u
  change Real.exp u*((Real.exp u)^(-4/3:ℝ)*Real.exp (-a*(Real.exp u+(Real.exp u)⁻¹)))=
    cubicBesselLogWeight a u
  rw [←Real.exp_mul]
  have he : Real.exp u*Real.exp (u*(-4/3))=Real.exp (-u/3) := by
    rw [←Real.exp_add]
    congr 1
    ring
  rw [←mul_assoc,he]
  unfold cubicBesselLogWeight
  rw [Real.cosh_eq,Real.exp_neg]
  congr 2
  ring

lemma cubicBesselKernel_log {a : ℝ} (ha : 0<a) :
    cubicBesselKernel (a^2)=∫ u : ℝ,cubicBesselLogWeight a u :=
  cubicBesselKernel_log_integral ha

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicBesselLogDerivative
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiation of the fixed cubic Bessel integral in logarithmic
coordinates, with an integrable local majorant. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace CubicFirstMoment

lemma cubicBesselLogWeight_hasDerivAt (a u : ℝ) :
    HasDerivAt (fun x => cubicBesselLogWeight x u) (cubicBesselLogDerivative a u) a := by
  have h := (((hasDerivAt_id a).const_mul (-2*Real.cosh u)).exp).const_mul (Real.exp (-u/3))
  simp only [id_eq] at h
  have he (x : ℝ) : Real.exp (-2*x*Real.cosh u)=Real.exp (-2*Real.cosh u*x) := by
    congr 1
    ring
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)).congr_deriv ?_
  · beta_reduce
    unfold cubicBesselLogWeight
    rw [he]
  · unfold cubicBesselLogDerivative cubicBesselLogWeight
    rw [he]
    ring

lemma cubicBesselLogDerivative_bound {a b : ℝ} (hb : 0<b) (hab : 2*b≤a) (u : ℝ) :
    ‖cubicBesselLogDerivative a u‖≤(1/b)*cubicBesselLogWeight b u := by
  let y := 2*Real.cosh u
  have hy : 0<y := mul_pos (by norm_num) (Real.cosh_pos u)
  have hp := power_exp_bound hb 1 y hy.le
  norm_num only [pow_one,Nat.factorial_one,Nat.cast_one] at hp
  have he : Real.exp (-a*y)≤Real.exp (-2*b*y) := Real.exp_le_exp.mpr (by nlinarith)
  have hmul := mul_le_mul_of_nonneg_left he hy.le
  have hsplit : y*Real.exp (-2*b*y)=(y*Real.exp (-b*y))*Real.exp (-b*y) := by
    have he : Real.exp (-2*b*y)=Real.exp (-b*y)*Real.exp (-b*y) := by
      rw [←Real.exp_add]
      congr 1
      ring
    rw [he]
    ring
  rw [hsplit] at hmul
  have hp' := mul_le_mul_of_nonneg_right hp (Real.exp_pos (-b*y)).le
  have h := mul_le_mul_of_nonneg_left (hmul.trans hp') (Real.exp_pos (-u/3)).le
  unfold cubicBesselLogDerivative cubicBesselLogWeight
  rw [norm_mul,norm_mul,Real.norm_eq_abs,abs_of_neg (by norm_num : (-2:ℝ)<0),
    Real.norm_of_nonneg (Real.cosh_pos u).le,
    Real.norm_of_nonneg (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le]
  dsimp [y] at h
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (ring_nf)

lemma cubicBesselLogDerivative_integrable {a : ℝ} (ha : 0<a) :
    Integrable (cubicBesselLogDerivative a) := by
  have hb : 0<a/2 := by linarith
  apply ((cubicBesselLogWeight_integrable hb).const_mul (1/(a/2))).mono'
    (by unfold cubicBesselLogDerivative cubicBesselLogWeight; fun_prop)
  exact Filter.Eventually.of_forall (cubicBesselLogDerivative_bound hb (by linarith))

theorem cubicBesselLogIntegral_hasDerivAt {a : ℝ} (ha : 0<a) :
    HasDerivAt (fun x => ∫ u : ℝ,cubicBesselLogWeight x u)
      (∫ u : ℝ,cubicBesselLogDerivative a u) a := by
  have hb : 0<a/4 := by linarith
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s:=Ioi (a/2)) (bound:=fun u => (1/(a/4))*cubicBesselLogWeight (a/4) u)
    (isOpen_Ioi.mem_nhds (by change a/2<a; linarith))
    (Filter.Eventually.of_forall (fun x => by
      unfold cubicBesselLogWeight; fun_prop))
    (cubicBesselLogWeight_integrable ha) ?_ ?_
    ((cubicBesselLogWeight_integrable hb).const_mul (1/(a/4))) ?_).2
  · unfold cubicBesselLogDerivative cubicBesselLogWeight
    fun_prop
  · exact Filter.Eventually.of_forall (fun u x hx =>
      cubicBesselLogDerivative_bound hb (by change a/2<x at hx; linarith) u)
  · exact Filter.Eventually.of_forall (fun u x _ => cubicBesselLogWeight_hasDerivAt x u)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicBesselLogSlope
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positivity and a strict slope estimate for the fixed Bessel kernel. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace CubicFirstMoment

lemma cubicBesselLogIntegral_pos {a : ℝ} (ha : 0<a) :
    0<∫ u : ℝ,cubicBesselLogWeight a u := by
  rw [integral_pos_iff_support_of_nonneg
    (fun u => (cubicBesselLogWeight_pos a u).le) (cubicBesselLogWeight_integrable ha)]
  have hs : Function.support (cubicBesselLogWeight a)=univ := by
    ext u
    simp only [Function.mem_support,mem_univ,iff_true]
    exact (cubicBesselLogWeight_pos a u).ne'
  rw [hs]
  simp

lemma cubicBesselLogIntegral_slope {a : ℝ} (ha : 0<a) :
    (∫ u : ℝ,cubicBesselLogDerivative a u)≤ -2*(∫ u : ℝ,cubicBesselLogWeight a u) := by
  rw [←integral_const_mul]
  apply integral_mono (cubicBesselLogDerivative_integrable ha)
    ((cubicBesselLogWeight_integrable ha).const_mul (-2))
  intro u
  unfold cubicBesselLogDerivative
  have hw := cubicBesselLogWeight_pos a u
  have hc := Real.one_le_cosh u
  nlinarith

lemma cubicBesselKernelDerivative_log {a : ℝ} (ha : 0<a) :
    2*a*cubicBesselKernelDerivative (a^2)=∫ u : ℝ,cubicBesselLogDerivative a u := by
  have hp : HasDerivAt (fun x : ℝ => x^2) (2*a) a := by
    convert (hasDerivAt_id a).pow 2 using 1
    all_goals first | rfl | (funext x; rfl) | norm_num [id_eq]
  have hK := (cubicBesselKernel_hasDerivAt (sq_pos_of_pos ha)).comp_of_eq a hp rfl
  have hI := cubicBesselLogIntegral_hasDerivAt ha
  have he : (fun x : ℝ => cubicBesselKernel (x^2))=ᶠ[𝓝 a]
      (fun x => ∫ u : ℝ,cubicBesselLogWeight x u) := by
    filter_upwards [show Ioi (0:ℝ)∈𝓝 a from Ioi_mem_nhds ha] with x hx
    exact cubicBesselKernel_log hx
  have h := hK.unique (hI.congr_of_eventuallyEq he)
  simpa only [pow_one,mul_one,smul_eq_mul,mul_comm,mul_left_comm,mul_assoc] using h

lemma cubicThetaWhittakerDerivative_re_neg {v : ℝ} (hv : 0<v)
    (hvπ : 1<4*Real.pi*v) : (cubicThetaWhittakerDerivative v).re<0 := by
  let a := 2*Real.pi*v
  have ha : 0<a := by dsimp [a]; positivity
  let I := ∫ u : ℝ,cubicBesselLogWeight a u
  let J := ∫ u : ℝ,cubicBesselLogDerivative a u
  have hI : 0<I := cubicBesselLogIntegral_pos ha
  have hJ : J≤ -2*I := cubicBesselLogIntegral_slope ha
  have hK : cubicBesselKernel (a^2)=I := cubicBesselKernel_log ha
  have hD : 2*a*cubicBesselKernelDerivative (a^2)=J := cubicBesselKernelDerivative_log ha
  have hle := mul_le_mul_of_nonneg_left hJ (show 0≤a/2 by positivity)
  change cubicBesselKernel (a^2)/2+a^2*cubicBesselKernelDerivative (a^2)<0
  rw [hK]
  have hid : a^2*cubicBesselKernelDerivative (a^2)=(a/2)*J := by rw [←hD]; ring
  rw [hid]
  have hcoef : 1<2*a := by dsimp [a]; nlinarith
  nlinarith [mul_pos (show 0<2*a-1 by linarith) hI]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicBesselSymmetricSlope
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An even real integral for the negative Whittaker slope. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubic_cosh_quadratic (u : ℝ) : 1+u^2/2≤Real.cosh u := by
  have h := (Real.hasSum_cosh u).summable.sum_le_tsum (Finset.range 2)
    (fun n _ => by rw [pow_mul]; positivity)
  norm_num [Finset.sum_range_succ] at h
  rwa [←Real.cosh_eq_tsum] at h

lemma cubic_even_exp_integral (f : ℝ → ℝ) (he : ∀ u,f (-u)=f u)
    (hi : Integrable (fun u => f u*Real.exp (-u/3))) :
    Integrable (fun u => f u*Real.cosh (u/3)) ∧
    (∫ u : ℝ,f u*Real.exp (-u/3))=∫ u : ℝ,f u*Real.cosh (u/3) := by
  have hi' : Integrable (fun u => f u*Real.exp (u/3)) := by
    convert hi.comp_neg using 1
    all_goals try with_reducible_and_instances rfl
    funext u
    simp only [he,neg_neg]
  have hf : (fun u => f u*Real.cosh (u/3))=
      (fun u => (f u*Real.exp (-u/3)+f u*Real.exp (u/3))/2) := by
    funext u
    rw [Real.cosh_eq]
    ring_nf
  refine ⟨hf ▸ (hi.add hi').div_const 2,?_⟩
  have hn : (∫ u : ℝ,f u*Real.exp (u/3))=∫ u : ℝ,f u*Real.exp (-u/3) := by
    convert integral_neg_eq_self (fun u : ℝ => f u*Real.exp (-u/3)) volume using 1
    all_goals try with_reducible_and_instances rfl
    apply integral_congr_ae
    filter_upwards with u
    simp only [he,neg_neg]
  rw [hf,integral_div,integral_add hi hi',hn]
  ring

lemma cubicWhittakerNegativeSlope_integral {v : ℝ} (hv : 0<v) :
    Integrable (cubicWhittakerNegativeSlope v) ∧
    -(cubicThetaWhittakerDerivative v).re=
      (1/2:ℝ)*(∫ u : ℝ,cubicWhittakerNegativeSlope v u) := by
  let a := 2*Real.pi*v
  have ha : 0<a := by dsimp [a]; positivity
  let f := fun u : ℝ => (2*a*Real.cosh u-1)*Real.exp (-2*a*Real.cosh u)
  have hi : Integrable (fun u => f u*Real.exp (-u/3)) := by
    convert ((cubicBesselLogDerivative_integrable ha).const_mul (-a)).sub
      (cubicBesselLogWeight_integrable ha) using 1
    all_goals try with_reducible_and_instances rfl
    funext u
    dsimp [f,cubicBesselLogDerivative,cubicBesselLogWeight]
    ring
  have he := cubic_even_exp_integral f (by intro u; simp [f,Real.cosh_neg]) hi
  have hid : cubicWhittakerNegativeSlope v=(fun u => f u*Real.cosh (u/3)) := by
    funext u
    dsimp [cubicWhittakerNegativeSlope,f,a]
    ring_nf
  refine ⟨hid ▸ he.1,?_⟩
  have hD := cubicBesselKernelDerivative_log ha
  have hK := cubicBesselKernel_log ha
  change -(cubicBesselKernel (a^2)/2+a^2*cubicBesselKernelDerivative (a^2))=_
  rw [hid,←he.2]
  have hf : (fun u => f u*Real.exp (-u/3))=
      (fun u => -a*cubicBesselLogDerivative a u-cubicBesselLogWeight a u) := by
    funext u
    dsimp [f,cubicBesselLogDerivative,cubicBesselLogWeight]
    ring
  rw [hf,integral_sub ((cubicBesselLogDerivative_integrable ha).const_mul (-a))
    (cubicBesselLogWeight_integrable ha),integral_const_mul,←hD,←hK]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicBesselSlopeLower
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Lower estimates on finite intervals for the actual negative slope. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubic_slopeProfile_hasDerivAt (z : ℝ) :
    HasDerivAt (fun x : ℝ => (x-1)*Real.exp (-x))
      ((2-z)*Real.exp (-z)) z := by
  have hd : HasDerivAt (fun x : ℝ => -x) (-1) z := by
    convert (hasDerivAt_id z).neg using 1
    all_goals try with_reducible_and_instances rfl
    funext x; rfl
  have hg : HasDerivAt (fun x : ℝ => x-1) 1 z := by
    convert (hasDerivAt_id z).sub_const 1 using 1
    all_goals try with_reducible_and_instances rfl
    funext x; rfl
  convert hg.mul hd.exp using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma cubic_slopeProfile_antitone :
    AntitoneOn (fun x : ℝ => (x-1)*Real.exp (-x)) (Ici 2) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _) (by fun_prop)
    (fun z _ => (cubic_slopeProfile_hasDerivAt z).differentiableAt.differentiableWithinAt)
  intro z hz
  rw [(cubic_slopeProfile_hasDerivAt z).deriv]
  have hz' : 2≤z := (interior_subset hz)
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.exp_pos _).le

lemma cubicWhittakerNegativeSlope_lower {v q : ℝ} (hx : 2≤4*Real.pi*v)
    {u : ℝ} (hq : 4*Real.pi*v*Real.cosh u≤q) :
    (q-1)*Real.exp (-q) ≤ cubicWhittakerNegativeSlope v u := by
  have hx0 : 0≤4*Real.pi*v := by linarith
  have hz : 2≤4*Real.pi*v*Real.cosh u := by
    nlinarith [Real.one_le_cosh u]
  have h := cubic_slopeProfile_antitone hz (hz.trans hq) hq
  have hn : 0≤(4*Real.pi*v*Real.cosh u-1)*Real.exp (-4*Real.pi*v*Real.cosh u) :=
    mul_nonneg (by linarith) (Real.exp_pos _).le
  change (q-1)*Real.exp (-q)≤
    (4*Real.pi*v*Real.cosh u-1)*Real.exp (-(4*Real.pi*v*Real.cosh u)) at h
  have hn' : 0≤(4*Real.pi*v*Real.cosh u-1)*
      Real.exp (-(4*Real.pi*v*Real.cosh u)) := by simpa only [neg_mul] using hn
  simpa only [cubicWhittakerNegativeSlope,neg_mul] using
    h.trans (le_mul_of_one_le_right hn' (Real.one_le_cosh (u/3)))

lemma cubicWhittakerNegativeSlope_even (v u : ℝ) :
    cubicWhittakerNegativeSlope v (-u)=cubicWhittakerNegativeSlope v u := by
  simp [cubicWhittakerNegativeSlope,Real.cosh_neg,neg_div]

lemma cubicWhittakerNegativeSlope_nonneg {v : ℝ} (hx : 1≤4*Real.pi*v) (u : ℝ) :
    0 ≤ cubicWhittakerNegativeSlope v u := by
  unfold cubicWhittakerNegativeSlope
  have hx0 : 0≤4*Real.pi*v := by linarith
  have hz : 1≤4*Real.pi*v*Real.cosh u := by nlinarith [Real.one_le_cosh u]
  exact mul_nonneg (mul_nonneg (by linarith) (Real.exp_pos _).le) (Real.cosh_pos _).le

lemma cubicWhittakerNegativeSlope_interval_lower {v a b q : ℝ} (hv : 0<v)
    (hx : 2≤4*Real.pi*v) (hab : a≤b)
    (hq : ∀ u∈Ioc a b,4*Real.pi*v*Real.cosh u≤q) :
    (b-a)*((q-1)*Real.exp (-q))≤∫ u in Ioc a b,cubicWhittakerNegativeSlope v u := by
  have hi := (cubicWhittakerNegativeSlope_integral hv).1.integrableOn (s:=Ioc a b)
  have h : (∫ _u in Ioc a b,(q-1)*Real.exp (-q))≤
      ∫ u in Ioc a b,cubicWhittakerNegativeSlope v u := by
    apply setIntegral_mono_on (integrableOn_const (by simp [Real.volume_Ioc])) hi measurableSet_Ioc
    intro u hu
    exact cubicWhittakerNegativeSlope_lower hx (hq u hu)
  simpa only [setIntegral_const,Measure.real,Real.volume_Ioc,smul_eq_mul,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab)] using h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicBesselSlopeNumerics
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational bounds used only for the first nonzero theta frequency. -/
noncomputable section
namespace CubicFirstMoment

lemma cubic_exp_one_le : Real.exp 1≤87/32 := by
  linarith [Real.exp_one_lt_d9]

lemma cubic_cosh_half_le : Real.cosh (1/2:ℝ)≤8/7 := by
  have hc := Real.cosh_le_exp_half_sq (1/2:ℝ)
  have he := Real.exp_bound_div_one_sub_of_interval (x:=(1/8:ℝ)) (by norm_num) (by norm_num)
  norm_num at hc he ⊢
  exact hc.trans he

lemma cubic_cosh_one_le : Real.cosh (1:ℝ)≤8/5 := by
  rw [Real.cosh_eq]
  linarith [Real.exp_one_lt_d9,Real.exp_neg_one_lt_d9]

lemma cubic_cosh_three_halves_le : Real.cosh (3/2:ℝ)≤12/5 := by
  have he3 : Real.exp (3:ℝ)≤(87/32:ℝ)^3 := by
    calc
      _ = Real.exp 1^3 := by norm_num [←Real.exp_nat_mul]
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le cubic_exp_one_le 3
  have he : Real.exp (3/2:ℝ)≤9/2 := by
    have hsq : Real.exp (3/2:ℝ)^2=Real.exp 3 := by
      rw [←Real.exp_nat_mul]
      norm_num
    nlinarith [Real.exp_pos (3/2:ℝ)]
  have hepos : (4:ℝ)≤Real.exp (3/2:ℝ) := by
    have h1 : (8/3:ℝ)≤Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hhalf : (3/2:ℝ)≤Real.exp (1/2:ℝ) := by linarith [Real.add_one_le_exp (1/2:ℝ)]
    calc
      _ ≤ Real.exp 1*Real.exp (1/2:ℝ) := by nlinarith [Real.exp_pos (1:ℝ)]
      _ = Real.exp (3/2:ℝ) := by rw [←Real.exp_add]; norm_num
  have heneg : Real.exp (-(3/2:ℝ))≤1/4 := by
    rw [Real.exp_neg]
    apply (inv_le_comm₀ (Real.exp_pos _) (by norm_num)).mpr
    norm_num
    exact hepos
  rw [Real.cosh_eq]
  linarith

lemma cubic_exp_three_le : Real.exp (3:ℝ)≤21 := by
  have h := pow_le_pow_left₀ (Real.exp_pos _).le cubic_exp_one_le 3
  rw [←Real.exp_nat_mul] at h
  norm_num at h
  linarith

lemma cubic_exp_four_le : Real.exp (4:ℝ)≤55 := by
  have h := pow_le_pow_left₀ (Real.exp_pos _).le cubic_exp_one_le 4
  rw [←Real.exp_nat_mul] at h
  norm_num at h
  linarith

lemma cubic_exp_six_le : Real.exp (6:ℝ)≤405 := by
  have h := pow_le_pow_left₀ (Real.exp_pos _).le cubic_exp_one_le 6
  rw [←Real.exp_nat_mul] at h
  norm_num at h
  linarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicBesselFirstSlope
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A certified lower bound at the first theta frequency. -/
noncomputable section
open MeasureTheory Set Filter
namespace CubicFirstMoment

lemma cubicWhittakerFirstSlope_lower {v : ℝ} (hv : 0<v)
    (hx : 2≤4*Real.pi*v) (hx' : 4*Real.pi*v≤5/2) :
    (81/1000:ℝ)≤ -(cubicThetaWhittakerDerivative v).re := by
  let F := cubicWhittakerNegativeSlope v
  have hi := cubicWhittakerNegativeSlope_integral hv
  have hc : Continuous F := by unfold F cubicWhittakerNegativeSlope; fun_prop
  have hnon : ∀ u,0≤F u := cubicWhittakerNegativeSlope_nonneg (by linarith)
  have habs : (fun u => F |u|)=F := by
    funext u
    rcases le_total 0 u with hu | hu
    · rw [abs_of_nonneg hu]
    · rw [abs_of_nonpos hu]
      exact cubicWhittakerNegativeSlope_even v u
  have heven : (∫ u : ℝ,F u)=2*(∫ u in Ioi 0,F u) := by
    simpa only [habs] using (integral_comp_abs (f:=F))
  have he : -(cubicThetaWhittakerDerivative v).re=∫ u in Ioi 0,F u := by
    rw [hi.2,heven]
    ring
  have hbound (a b q : ℝ) (ha : 0≤a) (hab : a≤b)
      (hq : (4*Real.pi*v)*Real.cosh b≤q) :
      (b-a)*((q-1)*Real.exp (-q))≤∫ u in Ioc a b,F u := by
    apply cubicWhittakerNegativeSlope_interval_lower hv hx hab
    intro u hu
    have hu0 : 0≤u := ha.trans hu.1.le
    have hb0 : 0≤b := ha.trans hab
    have hcosh : Real.cosh u≤Real.cosh b := Real.cosh_le_cosh.mpr (by
      rw [abs_of_nonneg hu0,abs_of_nonneg hb0]; exact hu.2)
    exact (mul_le_mul_of_nonneg_left hcosh (by linarith)).trans hq
  have h01 := hbound 0 (1/2) 3 (by norm_num) (by norm_num) (by
    nlinarith [cubic_cosh_half_le,Real.cosh_pos (1/2:ℝ)])
  have h12 := hbound (1/2) 1 4 (by norm_num) (by norm_num) (by
    nlinarith [cubic_cosh_one_le,Real.cosh_pos (1:ℝ)])
  have h23 := hbound 1 (3/2) 6 (by norm_num) (by norm_num) (by
    nlinarith [cubic_cosh_three_halves_le,Real.cosh_pos (3/2:ℝ)])
  have hs1 := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    (hc.intervalIntegrable 0 (1/2)) (hc.intervalIntegrable (1/2) 1)
  have hs2 := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    (hc.intervalIntegrable 0 1) (hc.intervalIntegrable 1 (3/2))
  rw [intervalIntegral.integral_of_le (by norm_num),
    intervalIntegral.integral_of_le (by norm_num),
    intervalIntegral.integral_of_le (by norm_num)] at hs1 hs2
  have hm : (∫ u in Ioc (0:ℝ) (3/2),F u)≤∫ u in Ioi 0,F u := by
    apply setIntegral_mono_set (hi.1.integrableOn (s:=Ioi 0))
      (Eventually.of_forall hnon)
    exact Eventually.of_forall (fun _ hu => hu.1)
  have h3 : (1/21:ℝ)≤Real.exp (-3) := by
    rw [Real.exp_neg]
    simpa using (inv_le_inv₀ (by norm_num : (0:ℝ)<21) (Real.exp_pos 3)).mpr cubic_exp_three_le
  have h4 : (1/55:ℝ)≤Real.exp (-4) := by
    rw [Real.exp_neg]
    simpa using (inv_le_inv₀ (by norm_num : (0:ℝ)<55) (Real.exp_pos 4)).mpr cubic_exp_four_le
  have h6 : (1/405:ℝ)≤Real.exp (-6) := by
    rw [Real.exp_neg]
    simpa using (inv_le_inv₀ (by norm_num : (0:ℝ)<405) (Real.exp_pos 6)).mpr cubic_exp_six_le
  rw [he]
  norm_num at h01 h12 h23
  linarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicBesselGaussianSlope
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quantitative Gaussian majorant for the actual negative Whittaker slope. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubic_cosh_exponential_bound {x : ℝ} (hx : 1≤x) (u : ℝ) :
    (x*Real.cosh u-1)*Real.exp (-x*Real.cosh u)*Real.cosh (u/3)≤
      x*Real.exp (-x)*Real.exp (-((x-1)/2-1/18)*u^2) := by
  let y := Real.cosh u
  have hy : 0<y := Real.cosh_pos u
  have he : y≤Real.exp (y-1) := by simpa using Real.add_one_le_exp (y-1)
  have hq := cubic_cosh_quadratic u
  have hc := Real.cosh_le_exp_half_sq (u/3)
  have h0 : 0≤x := by linarith
  calc
    _ ≤ (x*y)*Real.exp (-x*y)*Real.cosh (u/3) := by
      dsimp [y]
      gcongr
      linarith
    _ ≤ (x*Real.exp (y-1))*Real.exp (-x*y)*Real.exp ((u/3)^2/2) := by
      gcongr
    _ = x*Real.exp ((y-1)+(-x*y)+(u/3)^2/2) := by
      rw [mul_assoc,mul_assoc,←Real.exp_add,←Real.exp_add]
      congr 2
      ring
    _ ≤ x*Real.exp (-x+(-((x-1)/2-1/18)*u^2)) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) h0
      have hh := mul_le_mul_of_nonneg_left hq (sub_nonneg.mpr hx)
      dsimp [y]
      nlinarith
    _ = _ := by rw [Real.exp_add,mul_assoc]

lemma cubicWhittakerNegativeSlope_gaussian {v : ℝ} (hv : 0<v)
    (hx : 2≤4*Real.pi*v) :
    -(cubicThetaWhittakerDerivative v).re≤
      (4*Real.pi*v/2)*Real.exp (-4*Real.pi*v)*
        Real.sqrt (Real.pi/((4*Real.pi*v-1)/2-1/18)) := by
  let x := 4*Real.pi*v
  let b := (x-1)/2-1/18
  have hb : 0<b := by dsimp [b,x]; linarith
  have hi := cubicWhittakerNegativeSlope_integral hv
  have hg : Integrable (fun u : ℝ => x*Real.exp (-x)*Real.exp (-b*u^2)) :=
    (integrable_exp_neg_mul_sq hb).const_mul _
  have hm : (∫ u : ℝ,cubicWhittakerNegativeSlope v u)≤
      ∫ u : ℝ,x*Real.exp (-x)*Real.exp (-b*u^2) := by
    apply integral_mono hi.1 hg
    intro u
    simpa only [cubicWhittakerNegativeSlope,x,b,neg_mul] using
      cubic_cosh_exponential_bound (show 1≤x by dsimp [x]; linarith) u
  rw [integral_const_mul,integral_gaussian] at hm
  rw [hi.2]
  have hm' := mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ)≤1/2)
  convert hm' using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp [x,b]; simp only [neg_mul]; ring)

lemma cubicThetaWhittakerDerivative_gaussian {v : ℝ} (hv : 0<v)
    (hx : 2≤4*Real.pi*v) :
    ‖cubicThetaWhittakerDerivative v‖≤
      (4*Real.pi*v/2)*Real.exp (-4*Real.pi*v)*
        Real.sqrt (Real.pi/((4*Real.pi*v-1)/2-1/18)) := by
  have hn := cubicThetaWhittakerDerivative_re_neg hv (by linarith)
  have he : ‖cubicThetaWhittakerDerivative v‖= -(cubicThetaWhittakerDerivative v).re := by
    change ‖((_:ℝ):ℂ)‖= -(_ : ℝ)
    change _ < 0 at hn
    rw [Complex.norm_real,Real.norm_eq_abs]
    change |(cubicThetaWhittakerDerivative v).re|= -(cubicThetaWhittakerDerivative v).re
    exact abs_of_neg hn
  rw [he]
  exact cubicWhittakerNegativeSlope_gaussian hv hx

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimaryCoefficients
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact primary cube coefficients isolated in DR v3 (5.17).
This connects the constructed theta expansion to the completed Gauss sum. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaFrequency_primary_norm (c d : Eisenstein) :
    ‖cubicThetaFrequency (lambdaE*c*d^3)‖ =
      Real.sqrt 3*Real.sqrt (norm c)*(Real.sqrt (norm d))^3/9 := by
  have hcN := norm_nonneg c
  have hdN := norm_nonneg d
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (by positivity)).mp
  rw [cubicThetaFrequency_sq]
  have he : norm (lambdaE*c*d^3) = 3*norm c*norm d^3 := by
    change Complex.normSq (((lambdaE*c*d^3:Eisenstein):ℂ)) = _
    simp only [Subalgebra.coe_mul,Subalgebra.coe_pow,Complex.normSq_mul,
      map_pow,lambdaE_coe,traceLambda_normSq]
    rfl
  rw [he]
  calc
    _ = (Real.sqrt 3)^2*(Real.sqrt (norm c))^2*
        ((Real.sqrt (norm d))^2)^3/81 := by
      rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3),Real.sq_sqrt hcN,Real.sq_sqrt hdN]
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoefficientEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact squared sizes of the theta coefficients, for normalization by
their Fourier energy. The zero classes remain in the formula. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaTwistedGauss_unit_lambda_norm {c : Eisenstein} (hc : primary c)
    (hs : Squarefree c) (u : Eisensteinˣ) :
    ‖cubicThetaTwistedGauss c ((u:Eisenstein)^4*lambdaE^2)‖=1 := by
  have hu : IsCoprime c ((u:Eisenstein)^4) := by
    refine ⟨0,(↑(u⁻¹):Eisenstein)^4,?_⟩
    simp only [zero_mul,zero_add,←mul_pow]
    simp
  have hcop : IsCoprime c ((u:Eisenstein)^4*lambdaE^2) :=
    hu.mul_right (primary_coprime_lambda hc).pow_right
  rw [cubicThetaTwistedGauss,norm_mul,norm_star,
    norm_cubicSymbol_of_isCoprime hc hcop,norm_gauss_of_squarefree hc hs,one_mul]

lemma CubicThetaCoordinates.coefficient_norm {n : Eisenstein} (R : CubicThetaCoordinates n) :
    ‖R.coefficient‖=
      if R.order%3=0 ∧ 3≤R.order then R.amplitude
      else if R.order%3=1 ∧ ((R.unit:Eisenstein)=1 ∨ (R.unit:Eisenstein)=-1)
        then R.amplitude else 0 := by
  classical
  unfold coefficient
  split_ifs
  · rw [norm_mul,norm_mul,norm_star,cubicThetaUnitPhase_norm,
      cubicThetaTwistedGauss_unit_lambda_norm R.squarefree_primary R.squarefree,
      mul_one,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg R.amplitude_nonneg]
  · rw [norm_mul,norm_star,norm_gauss_of_squarefree R.squarefree_primary R.squarefree,
      mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg R.amplitude_nonneg]
  · exact norm_zero

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaAmplitudeTail
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit coefficient formulas give sharper tail bounds than the
uniform bound 81. Only the two ramification classes that can occur are used. -/
noncomputable section
namespace CubicFirstMoment

lemma CubicThetaCoordinates.amplitude_high_order_bound {n : Eisenstein}
    (R : CubicThetaCoordinates n) (hk : 3≤R.order) : R.amplitude≤27 := by
  have hc := one_le_norm (primary_ne_zero R.squarefree_primary)
  have hd := one_le_norm (primary_ne_zero R.cube_primary)
  have hs : 1≤Real.sqrt (norm R.squarefreePart) := by simpa using Real.sqrt_le_sqrt hc
  have hpow : (3:ℝ)^(4-((R.order/3:ℕ):ℝ))≤27 := by
    have hk' : 1≤R.order/3 := by omega
    have hkR : (1:ℝ)≤(R.order/3:ℕ) := by exact_mod_cast hk'
    calc
      _ ≤ (3:ℝ)^(3:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 27 := by norm_num
  unfold amplitude
  exact (div_le_self (by positivity) (one_le_mul_of_one_le_of_one_le hs hd)).trans hpow

lemma CubicThetaCoordinates.nonzero_order_cases {n : Eisenstein}
    (R : CubicThetaCoordinates n) (h : R.coefficient≠0) :
    (R.order=1 ∧ ((R.unit:Eisenstein)=1 ∨ (R.unit:Eisenstein)=-1)) ∨ 3≤R.order := by
  by_cases hk : 3≤R.order
  · exact Or.inr hk
  · left
    unfold coefficient at h
    split_ifs at h with h0 h1
    · exact (hk h0.2).elim
    · exact ⟨by omega,h1.2⟩
    · exact (h rfl).elim

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaIntegerBox
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite coordinate boxes for the quantitative arithmetic theta tail. -/
noncomputable section
open scoped BigOperators
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubicThetaIntegerBox_mem (p : CubicThetaIntegerPoint) (k : ℕ) :
    p∈cubicThetaIntegerBox k ↔ cubicThetaIntegerRadius p≤k := by
  simp only [cubicThetaIntegerBox,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc,cubicThetaIntegerRadius,
    max_le_iff]
  omega

lemma cubicThetaIntegerBox_card (k : ℕ) :
    (cubicThetaIntegerBox k).card=(2*k+1)^2 := by
  unfold cubicThetaIntegerBox
  rw [Finset.product_eq_sprod,Finset.card_product,Int.card_Icc]
  have h : ((k:ℤ)+1- -(k:ℤ)).toNat=2*k+1 := by omega
  rw [h]
  ring

lemma cubicThetaIntegerBox_card_bound {k : ℕ} (hk : 1≤k) :
    ((cubicThetaIntegerBox k).card:ℝ)≤9*(k:ℝ)^2 := by
  rw [cubicThetaIntegerBox_card]
  have hkR : (1:ℝ)≤k := by exact_mod_cast hk
  push_cast
  nlinarith

lemma cubicThetaInteger_finite_sum_bound (S : Finset CubicThetaIntegerPoint)
    (f : CubicThetaIntegerPoint → ℝ) (g : ℕ → ℝ) (hg : ∀ k,0≤g k)
    (hf : ∀ p∈S,f p≤g (cubicThetaIntegerRadius p)) :
    ∑ p∈S,f p≤∑ k∈S.image cubicThetaIntegerRadius,
      ((cubicThetaIntegerBox k).card:ℝ)*g k := by
  classical
  calc
    _ ≤ ∑ p∈S,g (cubicThetaIntegerRadius p) := Finset.sum_le_sum hf
    _ = ∑ k∈S.image cubicThetaIntegerRadius,
        ∑ p∈S with cubicThetaIntegerRadius p=k,g (cubicThetaIntegerRadius p) := by
      exact (Finset.sum_fiberwise_of_maps_to (fun p hp => Finset.mem_image_of_mem _ hp)
        (fun p => g (cubicThetaIntegerRadius p))).symm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k _
      have hsub : S.filter (fun p => cubicThetaIntegerRadius p=k)⊆cubicThetaIntegerBox k := by
        intro p hp
        apply (cubicThetaIntegerBox_mem p k).mpr
        exact (Finset.mem_filter.mp hp).2.le
      calc
        _ = ((S.filter (fun p => cubicThetaIntegerRadius p=k)).card:ℝ)*g k := by
          rw [Finset.sum_congr rfl (fun p hp => by rw [(Finset.mem_filter.mp hp).2])]
          simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub) (hg k)

lemma cubicThetaInteger_tsum_bound (f : CubicThetaIntegerPoint → ℝ) (g : ℕ → ℝ)
    (hf0 : ∀ p,0≤f p) (hg : ∀ k,0≤g k)
    (hf : ∀ p,f p≤g (cubicThetaIntegerRadius p))
    (hs : Summable (fun k => ((cubicThetaIntegerBox k).card:ℝ)*g k)) :
    Summable f ∧ (∑' p,f p)≤∑' k,((cubicThetaIntegerBox k).card:ℝ)*g k := by
  have hbound (S : Finset CubicThetaIntegerPoint) :
      ∑ p∈S,f p≤∑' k,((cubicThetaIntegerBox k).card:ℝ)*g k := by
    exact (cubicThetaInteger_finite_sum_bound S f g hg (fun p _ => hf p)).trans
      (hs.sum_le_tsum _ (fun k _ => mul_nonneg (Nat.cast_nonneg _) (hg k)))
  exact ⟨summable_of_sum_le hf0 hbound,Real.tsum_le_of_sum_le hf0 hbound⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaMassPushforward
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summable nonnegative coordinate masses pushed to the actual Fourier lattice. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaMassPushforward_properties {ι κ : Type*} (g : ι → κ) (w : ι → ℝ)
    (hw0 : ∀ p,0≤w p) (hw : Summable w) :
    Summable (cubicThetaMassPushforward g w) ∧
    (∑' n,cubicThetaMassPushforward g w n)=∑' p,w p ∧
    (∀ n,0 ≤ cubicThetaMassPushforward g w n) ∧
    ∀ p,w p ≤ cubicThetaMassPushforward g w (g p) := by
  have hnon : ∀ q : ι × κ,0≤(if g q.1=q.2 then w q.1 else 0) := by
    intro q; split_ifs <;> first | exact hw0 _ | exact le_rfl
  have hrows (p : ι) : Summable (fun n : κ => if g p=n then w p else 0) :=
    (hasSum_ite_eq' (g p) (w p)).summable
  have houter : Summable (fun p : ι => ∑' n : κ,if g p=n then w p else 0) := by
    simpa only [tsum_ite_eq'] using hw
  have hp : Summable (fun q : ι × κ => if g q.1=q.2 then w q.1 else 0) :=
    (summable_prod_of_nonneg hnon).mpr ⟨hrows,houter⟩
  have hs := (summable_prod_of_nonneg (fun q : κ × ι => hnon (q.2,q.1))).mp hp.prod_symm
  have he : (∑' n,cubicThetaMassPushforward g w n)=∑' p,w p := by
    change (∑' n,∑' p,if g p=n then w p else 0)=_
    have hc := hp.tsum_comm (f := fun p n => if g p=n then w p else 0)
    exact hc.trans (by simp only [tsum_ite_eq'])
  refine ⟨hs.2,he,fun n => tsum_nonneg (fun p => hnon (p,n)),?_⟩
  intro p
  have h := (hs.1 (g p)).sum_le_tsum {p} (fun q _ => hnon (q,g p))
  simpa only [cubicThetaMassPushforward,Finset.sum_singleton,ite_true, if_true] using h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoefficientTailSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact support and coefficient bounds for the arithmetic remainder after
removing the two leading Fourier frequencies. -/
noncomputable section
namespace CubicFirstMoment

lemma cubic_primary_norm_ge_four {m : Eisenstein} (hm : primary m) (hne : m≠1) :
    4≤norm m := by
  obtain ⟨w,hw⟩ := hm
  have hw0 : w≠0 := by intro h; rw [h,mul_zero,sub_eq_zero] at hw; exact hne hw
  have hw1 : 1≤‖(w:ℂ)‖ := by
    have h := one_le_norm hw0
    rw [norm,Complex.normSq_eq_norm_sq] at h
    nlinarith [_root_.norm_nonneg (w:ℂ)]
  have h3 : ‖(m:ℂ)-1‖=3*‖(w:ℂ)‖ := by
    have h := congrArg (fun z : Eisenstein => (z:ℂ)) hw
    simp only [Subalgebra.coe_sub,Subalgebra.coe_one,Subalgebra.coe_mul] at h
    change (m:ℂ)-1=(3:ℂ)*(w:ℂ) at h
    rw [h,norm_mul]
    norm_num
  have htri := norm_sub_le (m:ℂ) 1
  norm_num only [norm_one] at htri
  have hm2 : 2≤‖(m:ℂ)‖ := by linarith
  rw [norm,Complex.normSq_eq_norm_sq]
  nlinarith

lemma CubicThetaCoordinates.coefficient_norm_le_amplitude {n : Eisenstein}
    (R : CubicThetaCoordinates n) : ‖R.coefficient‖≤R.amplitude := by
  rw [R.coefficient_norm]
  split_ifs <;> first | exact le_rfl | exact R.amplitude_nonneg

lemma CubicThetaCoordinates.amplitude_order_one_bound {n : Eisenstein}
    (R : CubicThetaCoordinates n) (hk : R.order=1)
    (hm : R.squarefreePart*R.cubePart^3≠1) : R.amplitude≤81/2 := by
  have hden : 2≤Real.sqrt (norm R.squarefreePart)*norm R.cubePart := by
    have hc1 := one_le_norm (primary_ne_zero R.squarefree_primary)
    have hd1 := one_le_norm (primary_ne_zero R.cube_primary)
    have hs1 : 1≤Real.sqrt (norm R.squarefreePart) := by simpa using Real.sqrt_le_sqrt hc1
    by_cases hc : R.squarefreePart=1
    · have hd : R.cubePart≠1 := by intro h; apply hm; simp [hc,h]
      have hd4 := cubic_primary_norm_ge_four R.cube_primary hd
      nlinarith
    · have hc4 := cubic_primary_norm_ge_four R.squarefree_primary hc
      have hs2 : 2≤Real.sqrt (norm R.squarefreePart) := by
        convert Real.sqrt_le_sqrt hc4 using 1
        all_goals try with_reducible_and_instances rfl
        norm_num
      nlinarith
  have h := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤81) (by norm_num : (0:ℝ)<2) hden
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  norm_num [CubicThetaCoordinates.amplitude,hk]

lemma cubicThetaArithmetic_remainder_support {n : Eisenstein}
    (hp : n≠lambdaE) (hm : n≠ -lambdaE) (hc : cubicThetaArithmeticCoefficient n≠0) :
    (∃ m : Eisenstein,primary m ∧ m≠1 ∧ (n=lambdaE*m ∨ n= -lambdaE*m) ∧
      ‖cubicThetaArithmeticCoefficient n‖≤81/2) ∨
    (∃ m : Eisenstein,m≠0 ∧ n=lambdaE^3*m ∧ ‖cubicThetaArithmeticCoefficient n‖≤27) := by
  classical
  have hR : Nonempty (CubicThetaCoordinates n) := by
    by_contra h
    exact hc (by simp [cubicThetaArithmeticCoefficient,h])
  let R := Classical.choice hR
  have hcR : R.coefficient≠0 := by rwa [cubicThetaArithmeticCoefficient_formula R] at hc
  rcases R.nonzero_order_cases hcR with ⟨hk,hu⟩ | hk
  · left
    let m := R.squarefreePart*R.cubePart^3
    have hmp : primary m := primary_mul R.squarefree_primary (by
      simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using
        primary_mul R.cube_primary (primary_mul R.cube_primary R.cube_primary))
    have he : n=lambdaE*m ∨ n= -lambdaE*m := by
      rcases hu with hu | hu
      · left; rw [R.numerator_eq,hk,pow_one,hu,one_mul]
      · right; rw [R.numerator_eq,hk,pow_one,hu]; ring
    have hm1 : m≠1 := by
      intro h
      rcases he with he | he
      · exact hp (by simpa only [h,mul_one] using he)
      · exact hm (by simpa only [h,mul_one] using he)
    refine ⟨m,hmp,hm1,he,?_⟩
    rw [cubicThetaArithmeticCoefficient_formula R]
    exact R.coefficient_norm_le_amplitude.trans (R.amplitude_order_one_bound hk hm1)
  · right
    let m := (R.unit:Eisenstein)*lambdaE^(R.order-3)*(R.squarefreePart*R.cubePart^3)
    have he : n=lambdaE^3*m := by
      rw [R.numerator_eq,show R.order=3+(R.order-3) by omega,pow_add]
      dsimp [m]
      ring
    have hm0 : m≠0 := by intro h; exact R.ne_zero (by rw [he,h,mul_zero])
    refine ⟨m,hm0,he,?_⟩
    rw [cubicThetaArithmeticCoefficient_formula R]
    exact R.coefficient_norm_le_amplitude.trans (R.amplitude_high_order_bound hk)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoordinateNormBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Square-root norm bounds outside finite coordinate boxes. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaIntAbs_cast (i : ℤ) : (i.natAbs:ℝ)=|(i:ℝ)| := by
  have h := congrArg (fun z : ℤ => (z:ℝ)) (Int.natCast_natAbs i)
  simpa only [Int.cast_natCast,Int.cast_abs] using h

lemma cubicThetaQuadratic_nonneg (x y : ℝ) : 0≤x^2-x*y+y^2 := by
  nlinarith [sq_nonneg (x-y),sq_nonneg x,sq_nonneg y]

lemma cubicThetaQuadratic_lower (x y : ℝ) :
    (3/4:ℝ)*x^2≤x^2-x*y+y^2 ∧ (3/4:ℝ)*y^2≤x^2-x*y+y^2 := by
  constructor <;> nlinarith [sq_nonneg (x-2*y),sq_nonneg (2*x-y)]

lemma cubicThetaIntegerQuadratic_sqrt_lower (p : CubicThetaIntegerPoint) :
    (6/7:ℝ)*cubicThetaIntegerRadius p≤Real.sqrt (cubicThetaIntegerQuadratic p) := by
  apply (Real.le_sqrt (by positivity) (cubicThetaQuadratic_nonneg _ _)).mpr
  unfold cubicThetaIntegerRadius
  rcases le_total p.2.natAbs p.1.natAbs with h | h
  · rw [max_eq_left h,cubicThetaIntAbs_cast]
    have hq := (cubicThetaQuadratic_lower (p.1:ℝ) p.2).1
    nlinarith [sq_abs (p.1:ℝ)]
  · rw [max_eq_right h,cubicThetaIntAbs_cast]
    have hq := (cubicThetaQuadratic_lower (p.1:ℝ) p.2).2
    nlinarith [sq_abs (p.2:ℝ)]

lemma cubicThetaPrimaryQuadratic_sqrt_lower (p : CubicThetaIntegerPoint)
    (hp : 2 ≤ cubicThetaIntegerRadius p) :
    2*(cubicThetaIntegerRadius p:ℝ)≤Real.sqrt (cubicThetaPrimaryQuadratic p) := by
  apply (Real.le_sqrt (by positivity) (cubicThetaQuadratic_nonneg _ _)).mpr
  have hpR : (2:ℝ) ≤ cubicThetaIntegerRadius p := by exact_mod_cast hp
  unfold cubicThetaIntegerRadius at hpR ⊢
  rcases le_total p.2.natAbs p.1.natAbs with h | h
  · rw [max_eq_left h,cubicThetaIntAbs_cast] at hpR ⊢
    have hq := (cubicThetaQuadratic_lower (1+3*(p.1:ℝ)) (3*(p.2:ℝ))).1
    have hprod := mul_nonneg (abs_nonneg (p.1:ℝ)) (show 0≤|(p.1:ℝ)|-2 by linarith)
    have hi := neg_abs_le (p.1:ℝ)
    nlinarith [sq_abs (p.1:ℝ)]
  · rw [max_eq_right h,cubicThetaIntAbs_cast] at hpR ⊢
    have hq := (cubicThetaQuadratic_lower (1+3*(p.1:ℝ)) (3*(p.2:ℝ))).2
    nlinarith [sq_abs (p.2:ℝ)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGeometricNumerics
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary exponential and polynomial bounds for the two coordinate tails. -/
noncomputable section
namespace CubicFirstMoment

lemma cubic_exp_one_lower : (2718/1000:ℝ)≤Real.exp 1 := by
  linarith [Real.exp_one_gt_d9]

lemma cubic_exp_tail_lower : (120:ℝ)≤Real.exp (241/50:ℝ) := by
  have h4 : (2718/1000:ℝ)^4≤Real.exp 4 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2718/1000) cubic_exp_one_lower 4
    simpa only [←Real.exp_nat_mul,Nat.cast_ofNat,mul_one] using h
  have hf := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤41/50) 4
  norm_num [Finset.sum_range_succ] at hf
  have hmul := mul_le_mul h4 hf (by norm_num) (Real.exp_pos 4).le
  rw [←Real.exp_add] at hmul
  norm_num at hmul
  linarith

lemma cubic_exp_six_lower : (400:ℝ)≤Real.exp 6 := by
  have h := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2718/1000) cubic_exp_one_lower 6
  rw [←Real.exp_nat_mul] at h
  norm_num at h
  linarith

lemma cubic_nat_le_two_pow_pred {k : ℕ} (hk : 1≤k) : k≤2^(k-1) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
  induction n with
  | zero => norm_num
  | succ n ih =>
    norm_num only [Nat.succ_sub_one] at ih ⊢
    calc
      n+1+1≤2*(n+1) := by omega
      _ ≤2*2^n := Nat.mul_le_mul_left 2 (ih (by omega))
      _ =2^(n+1) := by rw [pow_succ]; omega

lemma cubic_nat_fourth_geometric {k : ℕ} (hk : 1≤k) :
    (k:ℝ)^4≤(16:ℝ)^k/16 := by
  have h := pow_le_pow_left₀ (by positivity : (0:ℝ)≤k)
    (show (k:ℝ)≤2^(k-1) by exact_mod_cast cubic_nat_le_two_pow_pred hk) 4
  have hp : ((2:ℝ)^(k-1))^4=16^(k-1) := by
    rw [←pow_mul,Nat.mul_comm,pow_mul]
    norm_num
  rw [hp] at h
  have he : (16:ℝ)^k/16=16^(k-1) := by
    nth_rw 1 [←Nat.sub_add_cancel hk]
    rw [pow_add]
    norm_num
  rwa [he]

lemma cubic_exp_nat_tail_bound (k : ℕ) :
    Real.exp (-(241/50:ℝ)*(k:ℝ))≤(1/120:ℝ)^k := by
  have h : Real.exp (-(241/50:ℝ))≤1/120 := by
    rw [Real.exp_neg]
    exact (inv_le_comm₀ (Real.exp_pos _) (by norm_num)).mpr (by norm_num; exact cubic_exp_tail_lower)
  calc
    _ = Real.exp (-(241/50:ℝ))^k := by rw [←Real.exp_nat_mul]; congr 1; ring
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le h k

lemma cubic_exp_nat_high_bound (k : ℕ) :
    Real.exp (-(6:ℝ)*(k:ℝ))≤(1/400:ℝ)^k := by
  have h : Real.exp (-(6:ℝ))≤1/400 := by
    rw [Real.exp_neg]
    exact (inv_le_comm₀ (Real.exp_pos _) (by norm_num)).mpr (by norm_num; exact cubic_exp_six_lower)
  calc
    _ = Real.exp (-(6:ℝ))^k := by rw [←Real.exp_nat_mul]; congr 1; ring
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le h k

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoordinateProfile
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise geometric majorants beyond the finite coordinate boxes. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubicThetaRadiusProfile_derivative (κ r : ℝ) :
    HasDerivAt (cubicThetaRadiusProfile κ) (r*(2-κ*r)*Real.exp (-κ*r)) r := by
  have hp : HasDerivAt (fun t : ℝ => t^2) (2*r) r := by
    convert (hasDerivAt_id r).pow 2 using 1
    all_goals first | rfl | (funext t; rfl) | (norm_num [id_eq])
  have he : HasDerivAt (fun t : ℝ => -κ*t) (-κ) r := by
    convert (hasDerivAt_id r).const_mul (-κ) using 1
    all_goals first | rfl | (funext t; rfl) | (simp)
  refine (hp.mul he.exp).congr_deriv ?_
  · ring

lemma cubicThetaRadiusProfile_antitone {κ : ℝ} (hκ : 2≤κ) :
    AntitoneOn (cubicThetaRadiusProfile κ) (Ici 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _) (by unfold cubicThetaRadiusProfile; fun_prop)
    (fun r _ => (cubicThetaRadiusProfile_derivative κ r).differentiableAt.differentiableWithinAt)
  intro r hr
  rw [(cubicThetaRadiusProfile_derivative κ r).deriv]
  have hr' : 1 ≤ r := interior_subset hr
  have hκr : 2≤κ*r := by nlinarith
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)) (Real.exp_pos _).le

lemma cubicThetaPrimaryTailMass_bound (p : CubicThetaIntegerPoint)
    (hp : 2 ≤ cubicThetaIntegerRadius p) :
    cubicThetaPrimaryTailMass p≤4*(cubicThetaIntegerRadius p:ℝ)^2*
      Real.exp (-(241/50:ℝ)*(cubicThetaIntegerRadius p:ℝ)) := by
  have hk : (2:ℝ) ≤ cubicThetaIntegerRadius p := by exact_mod_cast hp
  have hN : 0 ≤ cubicThetaPrimaryQuadratic p :=
    cubicThetaQuadratic_nonneg (1+3*(p.1:ℝ)) (3*(p.2:ℝ))
  have hr := cubicThetaPrimaryQuadratic_sqrt_lower p hp
  have h := cubicThetaRadiusProfile_antitone (by norm_num : (2:ℝ)≤241/100)
    (by change 1≤2*(cubicThetaIntegerRadius p:ℝ); linarith)
    (by change 1≤Real.sqrt (cubicThetaPrimaryQuadratic p); linarith) hr
  unfold cubicThetaRadiusProfile at h
  rw [Real.sq_sqrt hN] at h
  unfold cubicThetaPrimaryTailMass
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring_nf

lemma cubicThetaRamifiedTailMass_bound (p : CubicThetaIntegerPoint)
    (hp : 2 ≤ cubicThetaIntegerRadius p) :
    cubicThetaRamifiedTailMass p≤(cubicThetaIntegerRadius p:ℝ)^2*
      Real.exp (-(6:ℝ)*(cubicThetaIntegerRadius p:ℝ)) := by
  have hk : (2:ℝ) ≤ cubicThetaIntegerRadius p := by exact_mod_cast hp
  have hN : 0 ≤ cubicThetaIntegerQuadratic p := cubicThetaQuadratic_nonneg (p.1:ℝ) p.2
  have hr := cubicThetaIntegerQuadratic_sqrt_lower p
  have h := cubicThetaRadiusProfile_antitone (by norm_num : (2:ℝ)≤29/4)
    (by change 1≤(6/7:ℝ)*(cubicThetaIntegerRadius p:ℝ); linarith)
    (by change 1≤Real.sqrt (cubicThetaIntegerQuadratic p); linarith) hr
  unfold cubicThetaRadiusProfile at h
  rw [Real.sq_sqrt hN] at h
  unfold cubicThetaRamifiedTailMass
  apply h.trans
  apply mul_le_mul
  · nlinarith [sq_nonneg (cubicThetaIntegerRadius p:ℝ)]
  · apply Real.exp_le_exp.mpr
    nlinarith
  · exact (Real.exp_pos _).le
  · positivity

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGeometricAfter
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact sums of the two truncated geometric majorants. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubic_geometric_after {q : ℝ} (hq : |q|<1) (C : ℝ) (R : ℕ) :
    HasSum (fun k : ℕ => if R<k then C*q^k else 0)
      (C*q^(R+1)*(1-q)⁻¹) := by
  let f := fun k : ℕ => if R<k then C*q^k else 0
  have hs : HasSum (fun n => f (n+(R+1))) (C*q^(R+1)*(1-q)⁻¹) := by
    convert (hasSum_geometric_of_abs_lt_one hq).mul_left (C*q^(R+1)) using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    simp only [f,ite_eq_left (by omega : R<n+(R+1)),pow_add]
    ring
  have hh := hs.sum_range_add (f:=f)
  have hz : ∑ k∈Finset.range (R+1),f k=0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hk' := Finset.mem_range.mp hk
    simp only [f,ite_eq_right (by omega : ¬R<k)]
  rw [hz,zero_add] at hh
  exact hh

lemma cubic_primary_geometric_after :
    Summable (fun k : ℕ => if 3<k then (9/4:ℝ)*(2/15:ℝ)^k else 0) ∧
      (∑' k : ℕ,if 3<k then (9/4:ℝ)*(2/15:ℝ)^k else 0)<1/1000 := by
  have h := cubic_geometric_after (by norm_num : |(2/15:ℝ)|<1) (9/4:ℝ) 3
  refine ⟨h.summable,?_⟩
  rw [h.tsum_eq]
  norm_num

lemma cubic_ramified_geometric_after :
    Summable (fun k : ℕ => if 2<k then (9/16:ℝ)*(1/25:ℝ)^k else 0) ∧
      (∑' k : ℕ,if 2<k then (9/16:ℝ)*(1/25:ℝ)^k else 0)<1/10000 := by
  have h := cubic_geometric_after (by norm_num : |(1/25:ℝ)|<1) (9/16:ℝ) 2
  refine ⟨h.summable,?_⟩
  rw [h.tsum_eq]
  norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFarCoordinateTail
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summable quantitative tails outside the two finite coordinate boxes. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaPrimary_box_geometric (k : ℕ) :
    ((cubicThetaIntegerBox k).card:ℝ)*
      (if 3<k then 4*(k:ℝ)^2*Real.exp (-(241/50:ℝ)*(k:ℝ)) else 0)≤
      if 3<k then (9/4:ℝ)*(2/15:ℝ)^k else 0 := by
  split_ifs with hk
  · have hcard := cubicThetaIntegerBox_card_bound (show 1≤k by omega)
    have hpow := cubic_nat_fourth_geometric (show 1≤k by omega)
    have hexp := cubic_exp_nat_tail_bound k
    calc
      _ ≤ (9*(k:ℝ)^2)*(4*(k:ℝ)^2*Real.exp (-(241/50:ℝ)*(k:ℝ))) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 36*(k:ℝ)^4*Real.exp (-(241/50:ℝ)*(k:ℝ)) := by ring
      _ ≤ 36*((16:ℝ)^k/16)*(1/120:ℝ)^k := by gcongr
      _ = (9/4:ℝ)*(16*(1/120:ℝ))^k := by rw [mul_pow]; ring
      _ = _ := by norm_num
  · norm_num

lemma cubicThetaRamified_box_geometric (k : ℕ) :
    ((cubicThetaIntegerBox k).card:ℝ)*
      (if 2<k then (k:ℝ)^2*Real.exp (-(6:ℝ)*(k:ℝ)) else 0)≤
      if 2<k then (9/16:ℝ)*(1/25:ℝ)^k else 0 := by
  split_ifs with hk
  · have hcard := cubicThetaIntegerBox_card_bound (show 1≤k by omega)
    have hpow := cubic_nat_fourth_geometric (show 1≤k by omega)
    have hexp := cubic_exp_nat_high_bound k
    calc
      _ ≤ (9*(k:ℝ)^2)*((k:ℝ)^2*Real.exp (-(6:ℝ)*(k:ℝ))) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 9*(k:ℝ)^4*Real.exp (-(6:ℝ)*(k:ℝ)) := by ring
      _ ≤ 9*((16:ℝ)^k/16)*(1/400:ℝ)^k := by gcongr
      _ = (9/16:ℝ)*(16*(1/400:ℝ))^k := by rw [mul_pow]; ring
      _ = _ := by norm_num
  · norm_num

lemma cubicThetaPrimary_far_tail :
    Summable (fun p => if 3 < cubicThetaIntegerRadius p then cubicThetaPrimaryTailMass p else 0) ∧
    (∑' p,if 3 < cubicThetaIntegerRadius p then cubicThetaPrimaryTailMass p else 0)<1/1000 := by
  let g := fun k : ℕ => if 3<k then 4*(k:ℝ)^2*Real.exp (-(241/50:ℝ)*(k:ℝ)) else 0
  have hg : ∀ k,0≤g k := by intro k; dsimp [g]; split_ifs <;> positivity
  have hb := cubicThetaPrimary_box_geometric
  have hs : Summable (fun k => ((cubicThetaIntegerBox k).card:ℝ)*g k) :=
    cubic_primary_geometric_after.1.of_nonneg_of_le
      (fun k => mul_nonneg (Nat.cast_nonneg _) (hg k)) hb
  have h := cubicThetaInteger_tsum_bound
    (fun p => if 3 < cubicThetaIntegerRadius p then cubicThetaPrimaryTailMass p else 0) g
    (by
      intro p
      split_ifs
      · exact mul_nonneg (cubicThetaQuadratic_nonneg _ _) (Real.exp_pos _).le
      · exact le_rfl) hg
    (by intro p; dsimp [g]; split_ifs with hp
        · exact cubicThetaPrimaryTailMass_bound p (by omega)
        · exact le_rfl) hs
  refine ⟨h.1,h.2.trans_lt ?_⟩
  exact (hs.tsum_le_tsum hb cubic_primary_geometric_after.1).trans_lt cubic_primary_geometric_after.2

lemma cubicThetaRamified_far_tail :
    Summable (fun p => if 2 < cubicThetaIntegerRadius p then cubicThetaRamifiedTailMass p else 0) ∧
    (∑' p,if 2 < cubicThetaIntegerRadius p then cubicThetaRamifiedTailMass p else 0)<1/10000 := by
  let g := fun k : ℕ => if 2<k then (k:ℝ)^2*Real.exp (-(6:ℝ)*(k:ℝ)) else 0
  have hg : ∀ k,0≤g k := by intro k; dsimp [g]; split_ifs <;> positivity
  have hb := cubicThetaRamified_box_geometric
  have hs : Summable (fun k => ((cubicThetaIntegerBox k).card:ℝ)*g k) :=
    cubic_ramified_geometric_after.1.of_nonneg_of_le
      (fun k => mul_nonneg (Nat.cast_nonneg _) (hg k)) hb
  have h := cubicThetaInteger_tsum_bound
    (fun p => if 2 < cubicThetaIntegerRadius p then cubicThetaRamifiedTailMass p else 0) g
    (by
      intro p
      split_ifs
      · exact mul_nonneg (cubicThetaQuadratic_nonneg _ _) (Real.exp_pos _).le
      · exact le_rfl) hg
    (by intro p; dsimp [g]; split_ifs with hp
        · exact cubicThetaRamifiedTailMass_bound p (by omega)
        · exact le_rfl) hs
  refine ⟨h.1,h.2.trans_lt ?_⟩
  exact (hs.tsum_le_tsum hb cubic_ramified_geometric_after.1).trans_lt cubic_ramified_geometric_after.2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFiniteExponential
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite rational certificates for the exponential factors in the two
coordinate boxes. Every bound is checked from the positive Taylor series. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubic_exp_neg_le_taylor {x b : ℝ} (hx : 0≤x) (hb : 0<b) (n : ℕ)
    (h : b⁻¹≤∑ i∈Finset.range n,x^i/(i.factorial:ℝ)) :
    Real.exp (-x)≤b := by
  rw [Real.exp_neg]
  exact (inv_le_comm₀ (Real.exp_pos _) hb).mpr
    (h.trans (Real.sum_le_exp_of_nonneg hx n))

lemma cubic_primary_exp_4 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 4)≤(20167/2500000:ℝ) := by
  have hr : 2≤Real.sqrt 4 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(241/50:ℝ))≤(20167/2500000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_7 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 7)≤(8523/5000000:ℝ) := by
  have hr : (529/200:ℝ)≤Real.sqrt 7 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(127489/20000:ℝ))≤(8523/5000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_13 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 13)≤(843/5000000:ℝ) := by
  have hr : (721/200:ℝ)≤Real.sqrt 13 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(173761/20000:ℝ))≤(843/5000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_16 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 16)≤(651/10000000:ℝ) := by
  have hr : 4≤Real.sqrt 16 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(241/25:ℝ))≤(651/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_19 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 19)≤(11/400000:ℝ) := by
  have hr : (2179/500:ℝ)≤Real.sqrt 19 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(525139/50000:ℝ))≤(11/400000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_25 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 25)≤(59/10000000:ℝ) := by
  have hr : 5≤Real.sqrt 25 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(241/20:ℝ))≤(59/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_28 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 28)≤(29/10000000:ℝ) := by
  have hr : (5291/1000:ℝ)≤Real.sqrt 28 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(1275131/100000:ℝ))≤(29/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_31 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 31)≤(3/2000000:ℝ) := by
  have hr : (5567/1000:ℝ)≤Real.sqrt 31 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(1341647/100000:ℝ))≤(3/2000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_37 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 37)≤(1/2000000:ℝ) := by
  have hr : (3041/500:ℝ)≤Real.sqrt 37 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(732881/50000:ℝ))≤(1/2000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_43 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 43)≤(1/5000000:ℝ) := by
  have hr : (6557/1000:ℝ)≤Real.sqrt 43 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(1580237/100000:ℝ))≤(1/5000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_49 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 49)≤(1/10000000:ℝ) := by
  have hr : 7≤Real.sqrt 49 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(1687/100:ℝ))≤(1/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_52 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 52)≤(1/10000000:ℝ) := by
  have hr : (7211/1000:ℝ)≤Real.sqrt 52 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(1737851/100000:ℝ))≤(1/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_61 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 61)≤(1/10000000:ℝ) := by
  have hr : (781/100:ℝ)≤Real.sqrt 61 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(188221/10000:ℝ))≤(1/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_64 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 64)≤(1/10000000:ℝ) := by
  have hr : 8≤Real.sqrt 64 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(482/25:ℝ))≤(1/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_67 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 67)≤(1/10000000:ℝ) := by
  have hr : (1637/200:ℝ)≤Real.sqrt 67 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(394517/20000:ℝ))≤(1/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_73 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 73)≤(1/10000000:ℝ) := by
  have hr : (1068/125:ℝ)≤Real.sqrt 73 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(64347/3125:ℝ))≤(1/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_76 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 76)≤(1/10000000:ℝ) := by
  have hr : (8717/1000:ℝ)≤Real.sqrt 76 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(2100797/100000:ℝ))≤(1/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_79 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 79)≤(1/10000000:ℝ) := by
  have hr : (1111/125:ℝ)≤Real.sqrt 79 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(267751/12500:ℝ))≤(1/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_91 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 91)≤(1/10000000:ℝ) := by
  have hr : (9539/1000:ℝ)≤Real.sqrt 91 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(2298899/100000:ℝ))≤(1/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_97 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 97)≤(1/10000000:ℝ) := by
  have hr : (1231/125:ℝ)≤Real.sqrt 97 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(296671/12500:ℝ))≤(1/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_100 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 100)≤(1/10000000:ℝ) := by
  have hr : 10≤Real.sqrt 100 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(241/10:ℝ))≤(1/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_103 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 103)≤(1/10000000:ℝ) := by
  have hr : (2537/250:ℝ)≤Real.sqrt 103 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(611417/25000:ℝ))≤(1/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_127 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 127)≤(1/10000000:ℝ) := by
  have hr : (11269/1000:ℝ)≤Real.sqrt 127 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(2715829/100000:ℝ))≤(1/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_133 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 133)≤(1/10000000:ℝ) := by
  have hr : (2883/250:ℝ)≤Real.sqrt 133 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(694803/25000:ℝ))≤(1/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_139 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 139)≤(1/10000000:ℝ) := by
  have hr : (11789/1000:ℝ)≤Real.sqrt 139 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(2841149/100000:ℝ))≤(1/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_148 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 148)≤(1/10000000:ℝ) := by
  have hr : (2433/200:ℝ)≤Real.sqrt 148 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(586353/20000:ℝ))≤(1/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_151 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 151)≤(1/10000000:ℝ) := by
  have hr : (1536/125:ℝ)≤Real.sqrt 151 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(92544/3125:ℝ))≤(1/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_193 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 193)≤(1/10000000:ℝ) := by
  have hr : (3473/250:ℝ)≤Real.sqrt 193 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(836993/25000:ℝ))≤(1/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_196 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 196)≤(1/10000000:ℝ) := by
  have hr : 14≤Real.sqrt 196 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(1687/50:ℝ))≤(1/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_217 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 217)≤(1/10000000:ℝ) := by
  have hr : (1473/100:ℝ)≤Real.sqrt 217 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(354993/10000:ℝ))≤(1/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_271 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 271)≤(1/10000000:ℝ) := by
  have hr : (8231/500:ℝ)≤Real.sqrt 271 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(1983671/50000:ℝ))≤(1/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_ramified_exp_1 :
    Real.exp (-(29/4:ℝ)*Real.sqrt 1)≤(28407/40000000:ℝ) := by
  have hr : 1≤Real.sqrt 1 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(29/4:ℝ))≤(28407/40000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_ramified_exp_3 :
    Real.exp (-(29/4:ℝ)*Real.sqrt 3)≤(3521/1000000000:ℝ) := by
  have hr : (433/250:ℝ)≤Real.sqrt 3 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(12557/1000:ℝ))≤(3521/1000000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_ramified_exp_4 :
    Real.exp (-(29/4:ℝ)*Real.sqrt 4)≤(101/200000000:ℝ) := by
  have hr : 2≤Real.sqrt 4 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(29/2:ℝ))≤(101/200000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_ramified_exp_7 :
    Real.exp (-(29/4:ℝ)*Real.sqrt 7)≤(1/200000000:ℝ) := by
  have hr : (529/200:ℝ)≤Real.sqrt 7 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(15341/800:ℝ))≤(1/200000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_ramified_exp_12 :
    Real.exp (-(29/4:ℝ)*Real.sqrt 12)≤(1/1000000000:ℝ) := by
  have hr : (433/125:ℝ)≤Real.sqrt 12 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(12557/500:ℝ))≤(1/1000000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFiniteCoordinateBox
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal finite coordinate boxes are bounded by rational certificates. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaPrimaryBox_point (p : CubicThetaIntegerPoint)
    (hp : p∈cubicThetaIntegerBox 3) :
    (if p=(0,0) then 0 else cubicThetaPrimaryTailMass p) ≤ cubicThetaPrimaryBoxWeight p := by
  rcases p with ⟨i,j⟩
  have hr := (cubicThetaIntegerBox_mem (i,j) 3).mp hp
  have hi : -3 ≤ i ∧ i ≤ 3 := by unfold cubicThetaIntegerRadius at hr; omega
  have hj : -3 ≤ j ∧ j ≤ 3 := by unfold cubicThetaIntegerRadius at hr; omega
  rcases hi with ⟨hilo,hihi⟩
  rcases hj with ⟨hjlo,hjhi⟩
  interval_cases i <;> interval_cases j
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_73 (by norm_num : (0:ℝ)≤73) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_52 (by norm_num : (0:ℝ)≤52) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_49 (by norm_num : (0:ℝ)≤49) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_64 (by norm_num : (0:ℝ)≤64) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_97 (by norm_num : (0:ℝ)≤97) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_148 (by norm_num : (0:ℝ)≤148) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_217 (by norm_num : (0:ℝ)≤217) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_61 (by norm_num : (0:ℝ)≤61) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_31 (by norm_num : (0:ℝ)≤31) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_19 (by norm_num : (0:ℝ)≤19) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_25 (by norm_num : (0:ℝ)≤25) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_49 (by norm_num : (0:ℝ)≤49) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_91 (by norm_num : (0:ℝ)≤91) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_151 (by norm_num : (0:ℝ)≤151) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_67 (by norm_num : (0:ℝ)≤67) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_28 (by norm_num : (0:ℝ)≤28) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_7 (by norm_num : (0:ℝ)≤7) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_4 (by norm_num : (0:ℝ)≤4) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_19 (by norm_num : (0:ℝ)≤19) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_52 (by norm_num : (0:ℝ)≤52) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_103 (by norm_num : (0:ℝ)≤103) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_91 (by norm_num : (0:ℝ)≤91) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_43 (by norm_num : (0:ℝ)≤43) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_13 (by norm_num : (0:ℝ)≤13) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · norm_num [cubicThetaPrimaryBoxWeight]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_7 (by norm_num : (0:ℝ)≤7) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_31 (by norm_num : (0:ℝ)≤31) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_73 (by norm_num : (0:ℝ)≤73) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_133 (by norm_num : (0:ℝ)≤133) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_76 (by norm_num : (0:ℝ)≤76) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_37 (by norm_num : (0:ℝ)≤37) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_16 (by norm_num : (0:ℝ)≤16) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_13 (by norm_num : (0:ℝ)≤13) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_28 (by norm_num : (0:ℝ)≤28) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_61 (by norm_num : (0:ℝ)≤61) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_193 (by norm_num : (0:ℝ)≤193) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_127 (by norm_num : (0:ℝ)≤127) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_79 (by norm_num : (0:ℝ)≤79) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_49 (by norm_num : (0:ℝ)≤49) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_37 (by norm_num : (0:ℝ)≤37) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_43 (by norm_num : (0:ℝ)≤43) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_67 (by norm_num : (0:ℝ)≤67) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_271 (by norm_num : (0:ℝ)≤271) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_196 (by norm_num : (0:ℝ)≤196) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_139 (by norm_num : (0:ℝ)≤139) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_100 (by norm_num : (0:ℝ)≤100) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_79 (by norm_num : (0:ℝ)≤79) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_76 (by norm_num : (0:ℝ)≤76) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_91 (by norm_num : (0:ℝ)≤91) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]

lemma cubicThetaPrimaryBox_finite :
    cubicThetaIntegerBox 3=({-3, -2, -1, 0, 1, 2, 3}:Finset ℤ).product {-3, -2, -1, 0, 1, 2, 3} := by
  unfold cubicThetaIntegerBox
  have h : Finset.Icc (-(3:ℤ)) 3={-3, -2, -1, 0, 1, 2, 3} := by decide
  simpa only [Nat.cast_ofNat] using congrArg₂ Finset.product h h


lemma cubicThetaPrimaryBox_sum :
    (∑ p∈cubicThetaIntegerBox 3,if p=(0,0) then 0 else cubicThetaPrimaryTailMass p)≤(8/125:ℝ) := by
  apply (Finset.sum_le_sum (fun p hp => cubicThetaPrimaryBox_point p hp)).trans
  rw [cubicThetaPrimaryBox_finite,Finset.product_eq_sprod,Finset.sum_product]
  first | (simp [cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound] <;> norm_num) | norm_num [cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]

lemma cubicThetaRamifiedBox_point (p : CubicThetaIntegerPoint)
    (hp : p∈cubicThetaIntegerBox 2) :
    (if p=(0,0) then 0 else cubicThetaRamifiedTailMass p) ≤ cubicThetaRamifiedBoxWeight p := by
  rcases p with ⟨i,j⟩
  have hr := (cubicThetaIntegerBox_mem (i,j) 2).mp hp
  have hi : -2 ≤ i ∧ i ≤ 2 := by unfold cubicThetaIntegerRadius at hr; omega
  have hj : -2 ≤ j ∧ j ≤ 2 := by unfold cubicThetaIntegerRadius at hr; omega
  rcases hi with ⟨hilo,hihi⟩
  rcases hj with ⟨hjlo,hjhi⟩
  interval_cases i <;> interval_cases j
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_4 (by norm_num : (0:ℝ)≤4) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound] <;> norm_num) | norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_3 (by norm_num : (0:ℝ)≤3) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound] <;> norm_num) | norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_4 (by norm_num : (0:ℝ)≤4) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound] <;> norm_num) | norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_7 (by norm_num : (0:ℝ)≤7) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound] <;> norm_num) | norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_12 (by norm_num : (0:ℝ)≤12) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound] <;> norm_num) | norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_3 (by norm_num : (0:ℝ)≤3) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound] <;> norm_num) | norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_1 (by norm_num : (0:ℝ)≤1) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound] <;> norm_num) | norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_1 (by norm_num : (0:ℝ)≤1) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound] <;> norm_num) | norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_3 (by norm_num : (0:ℝ)≤3) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound] <;> norm_num) | norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_7 (by norm_num : (0:ℝ)≤7) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound] <;> norm_num) | norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_4 (by norm_num : (0:ℝ)≤4) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound] <;> norm_num) | norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_1 (by norm_num : (0:ℝ)≤1) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound] <;> norm_num) | norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · norm_num [cubicThetaRamifiedBoxWeight]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_1 (by norm_num : (0:ℝ)≤1) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound] <;> norm_num) | norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_4 (by norm_num : (0:ℝ)≤4) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound] <;> norm_num) | norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_7 (by norm_num : (0:ℝ)≤7) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound] <;> norm_num) | norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_3 (by norm_num : (0:ℝ)≤3) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound] <;> norm_num) | norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_1 (by norm_num : (0:ℝ)≤1) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound] <;> norm_num) | norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_1 (by norm_num : (0:ℝ)≤1) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound] <;> norm_num) | norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_3 (by norm_num : (0:ℝ)≤3) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound] <;> norm_num) | norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_12 (by norm_num : (0:ℝ)≤12) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound] <;> norm_num) | norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_7 (by norm_num : (0:ℝ)≤7) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound] <;> norm_num) | norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_4 (by norm_num : (0:ℝ)≤4) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound] <;> norm_num) | norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_3 (by norm_num : (0:ℝ)≤3) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound] <;> norm_num) | norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_4 (by norm_num : (0:ℝ)≤4) using 1 <;>
      first | (with_reducible_and_instances rfl) | (simp [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound] <;> norm_num) | norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]

lemma cubicThetaRamifiedBox_finite :
    cubicThetaIntegerBox 2=({-2, -1, 0, 1, 2}:Finset ℤ).product {-2, -1, 0, 1, 2} := by
  unfold cubicThetaIntegerBox
  have h : Finset.Icc (-(2:ℤ)) 2={-2, -1, 0, 1, 2} := by decide
  simpa only [Nat.cast_ofNat] using congrArg₂ Finset.product h h


lemma cubicThetaRamifiedBox_sum :
    (∑ p∈cubicThetaIntegerBox 2,if p=(0,0) then 0 else cubicThetaRamifiedTailMass p)≤(11/2500:ℝ) := by
  apply (Finset.sum_le_sum (fun p hp => cubicThetaRamifiedBox_point p hp)).trans
  rw [cubicThetaRamifiedBox_finite,Finset.product_eq_sprod,Finset.sum_product]
  first | (simp [cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound] <;> norm_num) | norm_num [cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoordinateMass
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite boxes and the geometric tails bound the complete coordinate sums. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubic_finite_complement_sum {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℝ)
    (hc : Summable (fun p => if p∈S then 0 else f p)) :
    Summable f ∧ (∑' p,f p)=(∑ p∈S,f p)+(∑' p,if p∈S then 0 else f p) := by
  classical
  let g := fun p => if p∈S then f p else 0
  have hg : HasSum g (∑ p∈S,f p) := by
    have h : HasSum g (∑ p∈S,g p) := hasSum_sum_of_ne_finset_zero (s:=S) (f:=g) (fun p hp => by simp [g,hp])
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro p hp
    simp [g,hp]
  have h : HasSum f ((∑ p∈S,f p)+(∑' p,if p∈S then 0 else f p)) := by
    convert hg.add hc.hasSum using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    by_cases hp : p∈S <;> simp [g,hp]
  exact ⟨h.summable,h.tsum_eq⟩

lemma cubicThetaPrimary_coordinate_mass :
    Summable (fun p => if p=(0,0) then 0 else cubicThetaPrimaryTailMass p) ∧
    (∑' p,if p=(0,0) then 0 else cubicThetaPrimaryTailMass p)<13/200 := by
  classical
  let f := fun p : CubicThetaIntegerPoint => if p=(0,0) then 0 else cubicThetaPrimaryTailMass p
  have he : (fun p => if p∈cubicThetaIntegerBox 3 then 0 else f p)=
      (fun p => if 3 < cubicThetaIntegerRadius p then cubicThetaPrimaryTailMass p else 0) := by
    funext p
    by_cases hr : 3 < cubicThetaIntegerRadius p
    · have hm : p∉cubicThetaIntegerBox 3 := by
        intro hp; exact (not_lt_of_ge ((cubicThetaIntegerBox_mem p 3).mp hp)) hr
      have hp0 : p≠(0,0) := by intro hp; rw [hp] at hr; norm_num [cubicThetaIntegerRadius] at hr
      simp [hr,hm,f,hp0]
    · have hm := (cubicThetaIntegerBox_mem p 3).mpr (Nat.le_of_not_gt hr)
      simp [hr,hm]
  have hc : Summable (fun p => if p∈cubicThetaIntegerBox 3 then 0 else f p) := by
    rw [he]
    exact cubicThetaPrimary_far_tail.1
  have h := cubic_finite_complement_sum (cubicThetaIntegerBox 3) f hc
  refine ⟨h.1,?_⟩
  rw [h.2,he]
  have hb := cubicThetaPrimaryBox_sum
  have ht := cubicThetaPrimary_far_tail.2
  change (∑ p∈cubicThetaIntegerBox 3,if p=(0,0) then 0 else cubicThetaPrimaryTailMass p)+_<_
  linarith

lemma cubicThetaRamified_coordinate_mass :
    Summable (fun p => if p=(0,0) then 0 else cubicThetaRamifiedTailMass p) ∧
    (∑' p,if p=(0,0) then 0 else cubicThetaRamifiedTailMass p)<9/2000 := by
  classical
  let f := fun p : CubicThetaIntegerPoint => if p=(0,0) then 0 else cubicThetaRamifiedTailMass p
  have he : (fun p => if p∈cubicThetaIntegerBox 2 then 0 else f p)=
      (fun p => if 2 < cubicThetaIntegerRadius p then cubicThetaRamifiedTailMass p else 0) := by
    funext p
    by_cases hr : 2 < cubicThetaIntegerRadius p
    · have hm : p∉cubicThetaIntegerBox 2 := by
        intro hp; exact (not_lt_of_ge ((cubicThetaIntegerBox_mem p 2).mp hp)) hr
      have hp0 : p≠(0,0) := by intro hp; rw [hp] at hr; norm_num [cubicThetaIntegerRadius] at hr
      simp [hr,hm,f,hp0]
    · have hm := (cubicThetaIntegerBox_mem p 2).mpr (Nat.le_of_not_gt hr)
      simp [hr,hm]
  have hc : Summable (fun p => if p∈cubicThetaIntegerBox 2 then 0 else f p) := by
    rw [he]
    exact cubicThetaRamified_far_tail.1
  have h := cubic_finite_complement_sum (cubicThetaIntegerBox 2) f hc
  refine ⟨h.1,?_⟩
  rw [h.2,he]
  have hb := cubicThetaRamifiedBox_sum
  have ht := cubicThetaRamified_far_tail.2
  change (∑ p∈cubicThetaIntegerBox 2,if p=(0,0) then 0 else cubicThetaRamifiedTailMass p)+_<_
  linarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTailCoordinates
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit coordinate parametrizations for the two arithmetic remainder families. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaOrdinaryCoordinate_norm (p : CubicThetaIntegerPoint) :
    norm (cubicThetaOrdinaryCoordinate p)=cubicThetaIntegerQuadratic p := by
  rw [cubicThetaOrdinaryCoordinate,norm,ofCoords_coe,coordinates_norm]
  push_cast
  rfl

lemma cubicThetaPrimaryCoordinate_norm (p : CubicThetaIntegerPoint) :
    norm (cubicThetaPrimaryCoordinate p)=cubicThetaPrimaryQuadratic p := by
  rw [cubicThetaPrimaryCoordinate,norm,ofCoords_coe,coordinates_norm]
  push_cast
  rfl

lemma cubicThetaPrimaryCoordinate_eq (p : CubicThetaIntegerPoint) :
    cubicThetaPrimaryCoordinate p=1+3*cubicThetaOrdinaryCoordinate p := by
  unfold cubicThetaPrimaryCoordinate cubicThetaOrdinaryCoordinate ofCoords
  push_cast
  ring

lemma cubicThetaPrimaryCoordinate_zero : cubicThetaPrimaryCoordinate (0,0)=1 := by
  apply Subtype.ext
  norm_num [cubicThetaPrimaryCoordinate,ofCoords_coe]

lemma cubicThetaOrdinaryCoordinate_zero : cubicThetaOrdinaryCoordinate (0,0)=0 := by
  apply Subtype.ext
  norm_num [cubicThetaOrdinaryCoordinate,ofCoords_coe]

lemma cubicThetaPrimaryCoordinate_exists {m : Eisenstein} (hm : primary m) (hne : m≠1) :
    ∃ p : CubicThetaIntegerPoint,p≠(0,0) ∧ cubicThetaPrimaryCoordinate p=m := by
  obtain ⟨w,hw⟩ := hm
  obtain ⟨p,hp⟩ := ofCoords_surjective w
  change ofCoords p.1 p.2=w at hp
  have he : cubicThetaPrimaryCoordinate p=m := by
    rw [cubicThetaPrimaryCoordinate_eq]
    change 1+3*ofCoords p.1 p.2=m
    rw [hp]
    linear_combination -hw
  refine ⟨p,?_,he⟩
  intro h
  exact hne (by rw [←he,h,cubicThetaPrimaryCoordinate_zero])

lemma cubicThetaOrdinaryCoordinate_exists {m : Eisenstein} (hm : m≠0) :
    ∃ p : CubicThetaIntegerPoint,p≠(0,0) ∧ cubicThetaOrdinaryCoordinate p=m := by
  obtain ⟨p,hp⟩ := ofCoords_surjective m
  refine ⟨p,?_,hp⟩
  intro h
  exact hm (by rw [←hp]; change cubicThetaOrdinaryCoordinate p=0
               rw [h,cubicThetaOrdinaryCoordinate_zero])

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRemainderWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A summable majorant on the actual Fourier lattice, with its full mass bounded. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaPrimaryDerivativeWeight_nonneg (p : CubicThetaIntegerPoint) :
    0 ≤ cubicThetaPrimaryDerivativeWeight p := by
  unfold cubicThetaPrimaryDerivativeWeight
  apply mul_nonneg (by positivity)
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (cubicThetaQuadratic_nonneg _ _) (Real.exp_pos _).le

lemma cubicThetaRamifiedDerivativeWeight_nonneg (p : CubicThetaIntegerPoint) :
    0 ≤ cubicThetaRamifiedDerivativeWeight p := by
  unfold cubicThetaRamifiedDerivativeWeight
  apply mul_nonneg (by positivity)
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (cubicThetaQuadratic_nonneg _ _) (Real.exp_pos _).le

lemma cubicThetaPrimaryDerivativeWeight_mass :
    Summable cubicThetaPrimaryDerivativeWeight ∧
    (∑' p,cubicThetaPrimaryDerivativeWeight p)<((9/2:ℝ)*Real.pi)*(13/200) := by
  have h := cubicThetaPrimary_coordinate_mass
  refine ⟨h.1.mul_left _,?_⟩
  change (∑' p,((9/2:ℝ)*Real.pi)*(if p=(0,0) then 0 else cubicThetaPrimaryTailMass p))<_
  rw [tsum_mul_left]
  exact mul_lt_mul_of_pos_left h.2 (by positivity)

lemma cubicThetaRamifiedDerivativeWeight_mass :
    Summable cubicThetaRamifiedDerivativeWeight ∧
    (∑' p,cubicThetaRamifiedDerivativeWeight p)<(27*Real.pi)*(9/2000) := by
  have h := cubicThetaRamified_coordinate_mass
  refine ⟨h.1.mul_left _,?_⟩
  change (∑' p,(27*Real.pi)*(if p=(0,0) then 0 else cubicThetaRamifiedTailMass p))<_
  rw [tsum_mul_left]
  exact mul_lt_mul_of_pos_left h.2 (by positivity)

lemma cubicThetaRemainderWeight_properties :
    Summable cubicThetaRemainderWeight ∧ (∀ n,0 ≤ cubicThetaRemainderWeight n) ∧
    (∑' n,cubicThetaRemainderWeight n)<5/2 := by
  have hp := cubicThetaMassPushforward_properties
    (fun p => lambdaE*cubicThetaPrimaryCoordinate p) cubicThetaPrimaryDerivativeWeight
    cubicThetaPrimaryDerivativeWeight_nonneg cubicThetaPrimaryDerivativeWeight_mass.1
  have hn := cubicThetaMassPushforward_properties
    (fun p => -lambdaE*cubicThetaPrimaryCoordinate p) cubicThetaPrimaryDerivativeWeight
    cubicThetaPrimaryDerivativeWeight_nonneg cubicThetaPrimaryDerivativeWeight_mass.1
  have hh := cubicThetaMassPushforward_properties
    (fun p => lambdaE^3*cubicThetaOrdinaryCoordinate p) cubicThetaRamifiedDerivativeWeight
    cubicThetaRamifiedDerivativeWeight_nonneg cubicThetaRamifiedDerivativeWeight_mass.1
  refine ⟨(hp.1.add hn.1).add hh.1,fun n => add_nonneg (add_nonneg (hp.2.2.1 n)
    (hn.2.2.1 n)) (hh.2.2.1 n),?_⟩
  change (∑' n : Eisenstein, ((cubicThetaPositiveRemainderWeight n+
    cubicThetaNegativeRemainderWeight n)+cubicThetaHighRemainderWeight n))<5/2
  simp only [cubicThetaPositiveRemainderWeight,cubicThetaNegativeRemainderWeight,cubicThetaHighRemainderWeight]
  rw [(hp.1.add hn.1).tsum_add hh.1,hp.1.tsum_add hn.1,hp.2.1,hn.2.1,hh.2.1]
  have hP := cubicThetaPrimaryDerivativeWeight_mass.2
  have hH := cubicThetaRamifiedDerivativeWeight_mass.2
  have hpi := Real.pi_lt_d2
  linarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaDerivativeTailBounds
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical derivative bounds for the two actual arithmetic frequency scales. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaWhittakerDerivative_simple_tail {r : ℝ} (hr : 0 < r)
    (hx : 4≤4*Real.pi*r) :
    ‖cubicThetaWhittakerDerivative r‖≤3*Real.pi*r*Real.exp (-4*Real.pi*r) := by
  let b := (4*Real.pi*r-1)/2-1/18
  have hb : 0<b := by dsimp [b]; linarith
  have hs : Real.sqrt (Real.pi/b)≤3/2 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num,?_⟩
    apply (div_le_iff₀ hb).mpr
    dsimp [b]
    nlinarith [Real.pi_lt_d2]
  have h := cubicThetaWhittakerDerivative_gaussian hr (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hs
    (show 0≤(4*Real.pi*r/2)*Real.exp (-4*Real.pi*r) by positivity)
  exact h.trans (hmul.trans_eq (by ring))

lemma cubicThetaFrequency_scalar_lower :
    (241/100:ℝ)≤4*Real.pi*Real.sqrt 3/9 ∧
    (29/4:ℝ)≤4*Real.pi*Real.sqrt 3/3 := by
  have hs : (1732/1000:ℝ)≤Real.sqrt 3 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have h := mul_le_mul Real.pi_gt_d4.le hs (by positivity) (by positivity)
  constructor <;> nlinarith

lemma cubicThetaPrimary_derivative_tail {N : ℝ} (hN : 4≤N) :
    (81/2:ℝ)*(Real.sqrt 3*Real.sqrt N/9)*
      ‖cubicThetaWhittakerDerivative (Real.sqrt 3*Real.sqrt N/9)‖≤
      (9/2:ℝ)*Real.pi*(N*Real.exp (-(241/100:ℝ)*Real.sqrt N)) := by
  let r := Real.sqrt 3*Real.sqrt N/9
  have hN0 : 0<N := by linarith
  have hr : 0 < r := by dsimp [r]; positivity
  have hsN : 2≤Real.sqrt N := by
    convert Real.sqrt_le_sqrt hN using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  have hscale := cubicThetaFrequency_scalar_lower.1
  have harg : (241/100:ℝ)*Real.sqrt N≤4*Real.pi*r := by
    have h := mul_le_mul_of_nonneg_right hscale (Real.sqrt_nonneg N)
    dsimp [r]
    nlinarith
  have hx : 4≤4*Real.pi*r := by nlinarith
  have hr2 : r^2=N/27 := by
    dsimp [r]
    rw [div_pow,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤3),Real.sq_sqrt hN0.le]
    ring
  have h := mul_le_mul_of_nonneg_left (cubicThetaWhittakerDerivative_simple_tail hr hx)
    (show 0≤(81/2:ℝ)*r by positivity)
  have he := Real.exp_le_exp.mpr (neg_le_neg harg)
  calc
    _ ≤ (81/2:ℝ)*r*(3*Real.pi*r*Real.exp (-4*Real.pi*r)) := h
    _ = (243/2:ℝ)*Real.pi*r^2*Real.exp (-4*Real.pi*r) := by ring
    _ = (9/2:ℝ)*Real.pi*(N*Real.exp (-4*Real.pi*r)) := by rw [hr2]; ring
    _ = ((9/2:ℝ)*Real.pi*N)*Real.exp (-(4*Real.pi*r)) := by ring_nf
    _ ≤ ((9/2:ℝ)*Real.pi*N)*Real.exp (-((241/100:ℝ)*Real.sqrt N)) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring_nf

lemma cubicThetaRamified_derivative_tail {N : ℝ} (hN : 1≤N) :
    27*(Real.sqrt 3*Real.sqrt N/3)*
      ‖cubicThetaWhittakerDerivative (Real.sqrt 3*Real.sqrt N/3)‖≤
      27*Real.pi*(N*Real.exp (-(29/4:ℝ)*Real.sqrt N)) := by
  let r := Real.sqrt 3*Real.sqrt N/3
  have hN0 : 0<N := by linarith
  have hr : 0 < r := by dsimp [r]; positivity
  have hsN : 1≤Real.sqrt N := by simpa using Real.sqrt_le_sqrt hN
  have hscale := cubicThetaFrequency_scalar_lower.2
  have harg : (29/4:ℝ)*Real.sqrt N≤4*Real.pi*r := by
    have h := mul_le_mul_of_nonneg_right hscale (Real.sqrt_nonneg N)
    dsimp [r]
    nlinarith
  have hx : 4≤4*Real.pi*r := by nlinarith
  have hr2 : r^2=N/3 := by
    dsimp [r]
    rw [div_pow,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤3),Real.sq_sqrt hN0.le]
    ring
  have h := mul_le_mul_of_nonneg_left (cubicThetaWhittakerDerivative_simple_tail hr hx)
    (show 0≤(27:ℝ)*r by positivity)
  have he := Real.exp_le_exp.mpr (neg_le_neg harg)
  calc
    _ ≤ 27*r*(3*Real.pi*r*Real.exp (-4*Real.pi*r)) := h
    _ = 81*Real.pi*r^2*Real.exp (-4*Real.pi*r) := by ring
    _ = 27*Real.pi*(N*Real.exp (-4*Real.pi*r)) := by rw [hr2]; ring
    _ = (27*Real.pi*N)*Real.exp (-(4*Real.pi*r)) := by ring_nf
    _ ≤ (27*Real.pi*N)*Real.exp (-((29/4:ℝ)*Real.sqrt N)) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring_nf

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFirstPair
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first two literal arithmetic Fourier terms have a uniformly
negative contribution at height one. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaFrequency_lambda : ‖cubicThetaFrequency lambdaE‖=Real.sqrt 3/9 := by
  simpa using cubicThetaFrequency_primary_norm (1:Eisenstein) 1

lemma cubicThetaArithmeticCoefficient_lambda : cubicThetaArithmeticCoefficient lambdaE=81 := by
  simpa [gauss_one] using cubicThetaArithmeticCoefficient_primary primary_one primary_one
    (squarefree_one : Squarefree (1:Eisenstein))

lemma cubicThetaFrequency_neg_norm (n : Eisenstein) :
    ‖cubicThetaFrequency (-n)‖=‖cubicThetaFrequency n‖ := by
  simp only [cubicThetaFrequency,Subalgebra.coe_neg,neg_div,norm_neg]

lemma cubicThetaFirstPair_real_bound :
    (cubicThetaSeriesTermVertical cubicThetaArithmeticCoefficient 0 1 lambdaE+
      cubicThetaSeriesTermVertical cubicThetaArithmeticCoefficient 0 1 (-lambdaE)).re≤ -5/2 := by
  let r := Real.sqrt 3/9
  have hr : 0 < r := by dsimp [r]; positivity
  have hs : 173/100≤Real.sqrt 3 ∧ Real.sqrt 3≤7/4 := by
    constructor <;> nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤3),Real.sqrt_nonneg 3]
  have hx : 2≤4*Real.pi*r := by
    dsimp [r]
    have hp := Real.pi_gt_three
    nlinarith [Real.sqrt_nonneg 3]
  have hx' : 4*Real.pi*r≤5/2 := by
    dsimp [r]
    have hp := Real.pi_lt_d2
    nlinarith [Real.pi_pos]
  have hl := cubicWhittakerFirstSlope_lower hr hx hx'
  have hz : (-lambdaE:Eisenstein)≠0 := neg_ne_zero.mpr lambdaE_prime.ne_zero
  simp [cubicThetaSeriesTermVertical,lambdaE_prime.ne_zero,hz,
    cubicThetaArithmeticCoefficient_lambda,cubicThetaArithmeticCoefficient_even,
    cubicThetaFrequency_neg_norm,cubicThetaFrequency_lambda,tracePair,Complex.mul_re]
  change 81*(cubicThetaWhittakerDerivative r).re*r+
    81*(cubicThetaWhittakerDerivative r).re*r≤ -5/2
  have hr' : 173/900 ≤ r := by dsimp [r]; linarith [hs.1]
  have hm := mul_le_mul_of_nonneg_right hl hr.le
  nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTailTerm
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute vertical-term estimates at the two arithmetic lattice scales. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaFrequency_lambda_mul (m : Eisenstein) :
    ‖cubicThetaFrequency (lambdaE*m)‖=Real.sqrt 3*Real.sqrt (norm m)/9 := by
  simpa using cubicThetaFrequency_primary_norm m 1

lemma cubicThetaFrequency_lambda_cube_mul (m : Eisenstein) :
    ‖cubicThetaFrequency (lambdaE^3*m)‖=Real.sqrt 3*Real.sqrt (norm m)/3 := by
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (by positivity)).mp
  rw [cubicThetaFrequency_sq]
  have he : norm (lambdaE^3*m)=27*norm m := by
    change Complex.normSq (((lambdaE^3*m:Eisenstein):ℂ))=_
    simp only [Subalgebra.coe_mul,Subalgebra.coe_pow,Complex.normSq_mul,
      map_pow,lambdaE_coe,traceLambda_normSq]
    unfold norm
    ring
  rw [he,div_pow,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤3),
    Real.sq_sqrt (norm_nonneg m)]
  ring

lemma cubicThetaSeriesTermVertical_axis_norm {a : Eisenstein → ℂ} {n : Eisenstein}
    (hn : n≠0) :
    ‖cubicThetaSeriesTermVertical a 0 1 n‖=
      ‖a n‖*‖cubicThetaFrequency n‖*‖cubicThetaWhittakerDerivative ‖cubicThetaFrequency n‖‖ := by
  simp only [cubicThetaSeriesTermVertical,hn,ite_false, if_false,mul_one,norm_mul,Circle.norm_coe,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (_root_.norm_nonneg _)]
  ring

lemma cubicThetaSeriesTermVertical_primary_bound {n m : Eisenstein}
    (hn : n≠0) (hN : 4≤norm m)
    (he : n=lambdaE*m ∨ n= -lambdaE*m)
    (hc : ‖cubicThetaArithmeticCoefficient n‖≤81/2) :
    ‖cubicThetaSeriesTermVertical cubicThetaArithmeticCoefficient 0 1 n‖≤
      (9/2:ℝ)*Real.pi*(norm m*Real.exp (-(241/100:ℝ)*Real.sqrt (norm m))) := by
  have hf : ‖cubicThetaFrequency n‖=Real.sqrt 3*Real.sqrt (norm m)/9 := by
    rcases he with rfl | rfl
    · exact cubicThetaFrequency_lambda_mul m
    · rw [neg_mul,cubicThetaFrequency_neg_norm,cubicThetaFrequency_lambda_mul]
  rw [cubicThetaSeriesTermVertical_axis_norm hn,hf]
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity))
    (_root_.norm_nonneg _)).trans (cubicThetaPrimary_derivative_tail hN)

lemma cubicThetaSeriesTermVertical_ramified_bound {n m : Eisenstein}
    (hn : n≠0) (hm : m≠0) (he : n=lambdaE^3*m)
    (hc : ‖cubicThetaArithmeticCoefficient n‖≤27) :
    ‖cubicThetaSeriesTermVertical cubicThetaArithmeticCoefficient 0 1 n‖≤
      27*Real.pi*(norm m*Real.exp (-(29/4:ℝ)*Real.sqrt (norm m))) := by
  rw [cubicThetaSeriesTermVertical_axis_norm hn,he,cubicThetaFrequency_lambda_cube_mul]
  rw [he] at hc
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity))
    (_root_.norm_nonneg _)).trans (cubicThetaRamified_derivative_tail (one_le_norm hm))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaDerivativeRemainder
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual arithmetic derivative remainder is dominated by the three
summable coordinate families. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaRemainderWeight_components (n : Eisenstein) :
    cubicThetaPositiveRemainderWeight n ≤ cubicThetaRemainderWeight n ∧
    cubicThetaNegativeRemainderWeight n ≤ cubicThetaRemainderWeight n ∧
    cubicThetaHighRemainderWeight n ≤ cubicThetaRemainderWeight n := by
  have hp : 0 ≤ cubicThetaPositiveRemainderWeight n :=
    (cubicThetaMassPushforward_properties _ _ cubicThetaPrimaryDerivativeWeight_nonneg
      cubicThetaPrimaryDerivativeWeight_mass.1).2.2.1 n
  have hn : 0 ≤ cubicThetaNegativeRemainderWeight n :=
    (cubicThetaMassPushforward_properties _ _ cubicThetaPrimaryDerivativeWeight_nonneg
      cubicThetaPrimaryDerivativeWeight_mass.1).2.2.1 n
  have hh : 0 ≤ cubicThetaHighRemainderWeight n :=
    (cubicThetaMassPushforward_properties _ _ cubicThetaRamifiedDerivativeWeight_nonneg
      cubicThetaRamifiedDerivativeWeight_mass.1).2.2.1 n
  unfold cubicThetaRemainderWeight
  constructor
  · linarith
  constructor <;> linarith

lemma cubicThetaDerivativeRemainder_bound (n : Eisenstein) :
    ‖cubicThetaDerivativeRemainder n‖ ≤ cubicThetaRemainderWeight n := by
  by_cases he : n=lambdaE ∨ n= -lambdaE
  · simpa only [cubicThetaDerivativeRemainder,ite_eq_left he,norm_zero] using
      cubicThetaRemainderWeight_properties.2.1 n
  rw [cubicThetaDerivativeRemainder,ite_eq_right he]
  by_cases hn : n=0
  · simpa only [cubicThetaSeriesTermVertical,hn,ite_true, if_true,norm_zero] using
      cubicThetaRemainderWeight_properties.2.1 0
  by_cases hc : cubicThetaArithmeticCoefficient n=0
  · simpa only [cubicThetaSeriesTermVertical,hn,ite_false, if_false,hc,zero_mul,norm_zero] using
      cubicThetaRemainderWeight_properties.2.1 n
  rcases cubicThetaArithmetic_remainder_support (fun h => he (Or.inl h))
    (fun h => he (Or.inr h)) hc with ⟨m,hm,hm1,heq,hc⟩ | ⟨m,hm,heq,hc⟩
  · obtain ⟨p,hp,hpm⟩ := cubicThetaPrimaryCoordinate_exists hm hm1
    have hb := cubicThetaSeriesTermVertical_primary_bound hn
      (cubic_primary_norm_ge_four hm hm1) heq hc
    have hb' : ‖cubicThetaSeriesTermVertical cubicThetaArithmeticCoefficient 0 1 n‖≤
        cubicThetaPrimaryDerivativeWeight p := by
      rw [←hpm,cubicThetaPrimaryCoordinate_norm] at hb
      simpa only [cubicThetaPrimaryDerivativeWeight,ite_eq_right hp,cubicThetaPrimaryTailMass] using hb
    apply hb'.trans
    rcases heq with heq | heq
    · have ht := (cubicThetaMassPushforward_properties
        (fun p => lambdaE*cubicThetaPrimaryCoordinate p) cubicThetaPrimaryDerivativeWeight
        cubicThetaPrimaryDerivativeWeight_nonneg cubicThetaPrimaryDerivativeWeight_mass.1).2.2.2 p
      have he' : lambdaE*cubicThetaPrimaryCoordinate p=n := by rw [hpm,heq]
      rw [he'] at ht
      exact ht.trans (cubicThetaRemainderWeight_components n).1
    · have ht := (cubicThetaMassPushforward_properties
        (fun p => -lambdaE*cubicThetaPrimaryCoordinate p) cubicThetaPrimaryDerivativeWeight
        cubicThetaPrimaryDerivativeWeight_nonneg cubicThetaPrimaryDerivativeWeight_mass.1).2.2.2 p
      have he' : -lambdaE*cubicThetaPrimaryCoordinate p=n := by rw [hpm,heq]
      rw [he'] at ht
      exact ht.trans (cubicThetaRemainderWeight_components n).2.1
  · obtain ⟨p,hp,hpm⟩ := cubicThetaOrdinaryCoordinate_exists hm
    have hb := cubicThetaSeriesTermVertical_ramified_bound hn hm heq hc
    have hb' : ‖cubicThetaSeriesTermVertical cubicThetaArithmeticCoefficient 0 1 n‖≤
        cubicThetaRamifiedDerivativeWeight p := by
      rw [←hpm,cubicThetaOrdinaryCoordinate_norm] at hb
      simpa only [cubicThetaRamifiedDerivativeWeight,ite_eq_right hp,cubicThetaRamifiedTailMass] using hb
    have ht := (cubicThetaMassPushforward_properties
      (fun p => lambdaE^3*cubicThetaOrdinaryCoordinate p) cubicThetaRamifiedDerivativeWeight
      cubicThetaRamifiedDerivativeWeight_nonneg cubicThetaRamifiedDerivativeWeight_mass.1).2.2.2 p
    have he' : lambdaE^3*cubicThetaOrdinaryCoordinate p=n := by rw [hpm,heq]
    rw [he'] at ht
    exact hb'.trans (ht.trans (cubicThetaRemainderWeight_components n).2.2)

lemma cubicThetaDerivativeRemainder_mass :
    Summable cubicThetaDerivativeRemainder ∧ (∑' n,‖cubicThetaDerivativeRemainder n‖)<5/2 := by
  have hs := Summable.of_nonneg_of_le (fun n => _root_.norm_nonneg (cubicThetaDerivativeRemainder n))
    cubicThetaDerivativeRemainder_bound cubicThetaRemainderWeight_properties.1
  exact ⟨hs.of_norm,(hs.tsum_le_tsum cubicThetaDerivativeRemainder_bound
    cubicThetaRemainderWeight_properties.1).trans_lt cubicThetaRemainderWeight_properties.2.2⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaBaseScalarValue
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two negative leading terms dominate the complete arithmetic tail,
fixing the sign of the actual theta normalization. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaArithmeticAxisDerivative_split :
    cubicThetaArithmeticAxisDerivative 1=
      (cubicThetaSeriesTermVertical cubicThetaArithmeticCoefficient 0 1 lambdaE+
       cubicThetaSeriesTermVertical cubicThetaArithmeticCoefficient 0 1 (-lambdaE))+
      ∑' n,cubicThetaDerivativeRemainder n := by
  let f := cubicThetaSeriesTermVertical cubicThetaArithmeticCoefficient 0 1
  have hne : lambdaE≠ -lambdaE := by
    intro h
    have hz : (2:Eisenstein)*lambdaE=0 := by linear_combination h
    rcases mul_eq_zero.mp hz with hz | hz
    · norm_num at hz
    · exact lambdaE_prime.ne_zero hz
  have hp : HasSum (fun n : Eisenstein => if n=lambdaE then f lambdaE else 0) (f lambdaE) :=
    hasSum_ite_eq lambdaE _
  have hn : HasSum (fun n : Eisenstein => if n= -lambdaE then f (-lambdaE) else 0) (f (-lambdaE)) :=
    hasSum_ite_eq (-lambdaE) _
  have h : HasSum f ((f lambdaE+f (-lambdaE))+∑' n,cubicThetaDerivativeRemainder n) := by
    convert (hp.add hn).add cubicThetaDerivativeRemainder_mass.1.hasSum using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    by_cases h1 : n=lambdaE
    · subst n
      simp only [ite_true, if_true,cubicThetaDerivativeRemainder,true_or,
        add_zero]
      simp [hne]
    · by_cases h2 : n= -lambdaE
      · subst n
        simp [h1,cubicThetaDerivativeRemainder]
      · simp [h1,h2,cubicThetaDerivativeRemainder,f]
  exact h.tsum_eq

lemma cubicThetaArithmeticAxisDerivative_re_neg_oai :
    (cubicThetaArithmeticAxisDerivative 1).re<0 := by
  have ht : ‖∑' n,cubicThetaDerivativeRemainder n‖<5/2 :=
    (tsum_of_norm_bounded cubicThetaRemainderWeight_properties.1.hasSum
      cubicThetaDerivativeRemainder_bound).trans_lt cubicThetaRemainderWeight_properties.2.2
  have hr := Complex.re_le_norm (∑' n,cubicThetaDerivativeRemainder n)
  rw [cubicThetaArithmeticAxisDerivative_split,Complex.add_re]
  linarith [cubicThetaFirstPair_real_bound]

end CubicFirstMoment

end

end OAI
end

theorem solution : type_of% @OAI.CubicFirstMoment.cubicThetaArithmeticAxisDerivative_re_neg_oai := @OAI.CubicFirstMoment.cubicThetaArithmeticAxisDerivative_re_neg_oai
