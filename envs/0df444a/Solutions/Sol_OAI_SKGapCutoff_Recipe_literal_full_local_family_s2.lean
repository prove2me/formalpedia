-- Prove2me | solution 1 for OAI.SKGapCutoff.Recipe.literal_full_local_family_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:17:09.490989+00:00
-- url     : https://prove2.me/submissions/c4f2aea6-8b6b-4dbd-89e0-bfaff0af6059

import Mathlib
import Definitions.Def_OAIQ072A002

section
-- module Solutions.OAIQ074_CM.SKGap_Gaussian_PhiStein
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace SKGap.Stein

lemma hasDerivAt_integral01 {F F' : ℝ→ℝ→ℝ}
    (hF : Continuous (fun p : ℝ×ℝ=>F p.1 p.2))
    (hF' : Continuous (fun p : ℝ×ℝ=>F' p.1 p.2))
    (hd : ∀ z u,HasDerivAt (fun z=>F z u) (F' z u) z) (z : ℝ) :
    HasDerivAt (fun z=>∫u in (0:ℝ)..1,F z u) (∫u in (0:ℝ)..1,F' z u) z := by
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hF'.continuousOn : ContinuousOn (fun p : ℝ×ℝ=>F' p.1 p.2)
      ((Set.Icc (z-1) (z+1))×ˢ(Set.Icc (0:ℝ) 1)))
  have hc (x : ℝ) : Continuous (F x) := hF.comp (continuous_const.prodMk continuous_id)
  have hc' (x : ℝ) : Continuous (F' x) := hF'.comp (continuous_const.prodMk continuous_id)
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F:=F) (F':=F') (bound:=fun _=>C)
    (s:=Set.Icc (z-1) (z+1)) (Icc_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall (fun x=>(hc x).aestronglyMeasurable))
    (hc z|>.intervalIntegrable _ _) (hc' z).aestronglyMeasurable
    (Eventually.of_forall (by
      intro u hu x hx
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ)≤1)] at hu
      exact hC (x,u) ⟨hx,hu.1.le,hu.2⟩))
    intervalIntegrable_const
    (Eventually.of_forall (fun u _ x _=>hd x u))).2

lemma continuous_weight (a : ℝ) : Continuous (weight a) := by unfold weight; fun_prop

lemma phi_eq (z r a : ℝ) : phi z r a=numerator z r a/(Real.cosh z*Real.cosh r) := by
  exact intervalIntegral.integral_div _ _

lemma numerator_hasDerivAt (z r a : ℝ) :
    HasDerivAt (fun z=>numerator z r a) (numeratorZ z r a) z := by
  unfold numerator numeratorZ
  apply hasDerivAt_integral01 (F:=fun z u=>weight a u*Real.cosh (u*(z-r)))
    (F':=fun z u=>weight a u*u*Real.sinh (u*(z-r)))
  · unfold weight; fun_prop
  · unfold weight; fun_prop
  · intro z u
    convert! ((Real.hasDerivAt_cosh (u*(z-r))).comp z
      (((hasDerivAt_id z).sub_const r).const_mul u)).const_mul (weight a u) using 1
    all_goals try with_reducible_and_instances rfl
    ring

lemma phi_hasDerivAt (z r a : ℝ) : HasDerivAt (fun z=>phi z r a) (phiZ z r a) z := by
  have h := (numerator_hasDerivAt z r a).div
    ((Real.hasDerivAt_cosh z).mul_const (Real.cosh r))
    (ne_of_gt (mul_pos (Real.cosh_pos z) (Real.cosh_pos r)))
  convert! h using 1
  · funext x; exact phi_eq x r a
  · rw [phiZ,phi_eq,Real.tanh_eq_sinh_div_cosh]
    field_simp [ne_of_gt (Real.cosh_pos z),ne_of_gt (Real.cosh_pos r)]

lemma weight_hasDerivAt (a u : ℝ) : HasDerivAt (weight a) (-a*u*weight a u) u := by
  unfold weight
  convert! (Real.hasDerivAt_exp _).comp u
    ((((hasDerivAt_id u).pow 2).const_sub 1).const_mul a |>.div_const 2) using 1
  all_goals try with_reducible_and_instances rfl
  dsimp
  ring

lemma boundary_hasDerivAt (z r a u : ℝ) :
    HasDerivAt (fun u=>weight a u*Real.sinh (u*(z-r)))
      (weight a u*((z-r)*Real.cosh (u*(z-r))-a*u*Real.sinh (u*(z-r)))) u := by
  convert! (weight_hasDerivAt a u).mul
    ((Real.hasDerivAt_sinh (u*(z-r))).comp u ((hasDerivAt_id u).mul_const (z-r))) using 1
  all_goals try with_reducible_and_instances rfl
  dsimp
  ring

lemma numerator_boundary (z r a : ℝ) :
    (z-r)*numerator z r a-a*numeratorZ z r a=Real.sinh (z-r) := by
  have hc1 : Continuous (fun u=>weight a u*Real.cosh (u*(z-r))) := by
    exact (continuous_weight a).mul (by fun_prop)
  have hc2 : Continuous (fun u=>weight a u*u*Real.sinh (u*(z-r))) := by
    exact ((continuous_weight a).mul continuous_id).mul (by fun_prop)
  have he : (fun u=>weight a u*((z-r)*Real.cosh (u*(z-r))-a*u*Real.sinh (u*(z-r))))=
      (fun u=>(z-r)*(weight a u*Real.cosh (u*(z-r)))-a*(weight a u*u*Real.sinh (u*(z-r)))) := by
    funext u; ring
  have H:=intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a:=(0:ℝ)) (b:=1) (fun u _=>boundary_hasDerivAt z r a u)
    (show IntervalIntegrable (fun u=>weight a u*((z-r)*Real.cosh (u*(z-r))-a*u*Real.sinh (u*(z-r)))) volume 0 1 from by
      rw [he]; exact ((hc1.const_mul (z-r)).sub (hc2.const_mul a)).intervalIntegrable _ _)
  rw [he,intervalIntegral.integral_sub ((hc1.const_mul (z-r)).intervalIntegrable _ _)
    ((hc2.const_mul a).intervalIntegrable _ _),intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at H
  simpa only [numerator,numeratorZ,weight,one_pow,sub_self,mul_zero,zero_div,
    Real.exp_zero,one_mul,zero_mul,Real.sinh_zero,sub_zero] using H

theorem phi_stein (z r a : ℝ) :
    (z-r-a*Real.tanh z)*phi z r a-a*phiZ z r a=Real.tanh z-Real.tanh r := by
  rw [phiZ,phi_eq]
  have H:=numerator_boundary z r a
  have hId : Real.sinh (z-r)/(Real.cosh z*Real.cosh r)=Real.tanh z-Real.tanh r := by
    rw [Real.sinh_sub,Real.tanh_eq_sinh_div_cosh,Real.tanh_eq_sinh_div_cosh]
    field_simp [ne_of_gt (Real.cosh_pos z),ne_of_gt (Real.cosh_pos r)]
  rw [←hId]
  field_simp [ne_of_gt (Real.cosh_pos z),ne_of_gt (Real.cosh_pos r)]
  nlinarith [H]

lemma phi_pos (z r a : ℝ) : 0<phi z r a := by
  apply intervalIntegral.integral_pos (by norm_num : (0:ℝ)<1)
  · apply Continuous.continuousOn; unfold weight
    exact Continuous.div_const (by fun_prop) _
  · intro u _; exact (div_pos (mul_pos (Real.exp_pos _) (Real.cosh_pos _))
      (mul_pos (Real.cosh_pos _) (Real.cosh_pos _))).le
  · exact ⟨0,by norm_num,div_pos (mul_pos (Real.exp_pos _) (Real.cosh_pos _))
      (mul_pos (Real.cosh_pos _) (Real.cosh_pos _))⟩

end SKGap.Stein

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_ScalarVariance
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
namespace SKGapCutoff

lemma scalarVariance_pos (y : ℝ) : 0 < scalarVariance y :=
  sub_pos.mpr (Real.tanh_sq_lt_one y)

lemma scalarVariance_le_one (y : ℝ) : scalarVariance y ≤ 1 := by
  unfold scalarVariance
  nlinarith [sq_nonneg (Real.tanh y)]

lemma scalarVariance_eq (y : ℝ) : scalarVariance y = 1 / Real.cosh y ^ 2 := by
  have hc := Real.cosh_sq_sub_sinh_sq y
  unfold scalarVariance
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp
  nlinarith

lemma tanh_hasDerivAt (y : ℝ) : HasDerivAt Real.tanh (scalarVariance y) y := by
  have h := (Real.hasDerivAt_sinh y).div (Real.hasDerivAt_cosh y) (Real.cosh_pos y).ne'
  convert! h using 1
  · ext z; exact Real.tanh_eq_sinh_div_cosh z
  · rw [scalarVariance_eq]
    congr 1
    nlinarith [Real.cosh_sq_sub_sinh_sq y]

lemma tanh_lipschitz (x y : ℝ) : |Real.tanh y - Real.tanh x| ≤ |y-x| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ (Set.univ : Set ℝ)) => (tanh_hasDerivAt z).hasDerivWithinAt)
    (fun z _ => (show ‖scalarVariance z‖ ≤ 1 by
      rw [Real.norm_eq_abs, abs_of_pos (scalarVariance_pos z)]
      exact scalarVariance_le_one z)) convex_univ (Set.mem_univ x) (Set.mem_univ y)
  simpa only [one_mul, Real.norm_eq_abs] using h

end SKGapCutoff

open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_PhiBounds
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory
namespace SKGap.Stein

lemma phi_zero_diagonal (r : ℝ) : phi r r 0=1/(Real.cosh r)^2 := by
  simp [phi,weight,pow_two]

lemma phi_zero_le_one (z r : ℝ) : phi z r 0≤1 := by
  by_cases h : z=r
  · subst z
    rw [phi_zero_diagonal,←SKGapCutoff.scalarVariance_eq]
    exact SKGapCutoff.scalarVariance_le_one _
  · have H:=phi_stein z r 0
    simp only [zero_mul,sub_zero] at H
    have H':=congrArg abs H
    rw [abs_mul,abs_of_pos (phi_pos z r 0)] at H'
    have hz : 0 < |z-r| := abs_pos.mpr (sub_ne_zero.mpr h)
    have hl:=SKGapCutoff.tanh_lipschitz r z
    nlinarith

lemma weight_le (a u : ℝ) (hu : u∈Set.Icc (0:ℝ) 1) : weight a u≤Real.exp (|a|/2) := by
  unfold weight
  apply Real.exp_le_exp.mpr
  have hu2 : u^2≤1 := by nlinarith [hu.1,hu.2]
  have hm : a*(1-u^2)≤|a| := by
    calc
      _ ≤ |a| *(1-u^2) := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
      _ ≤ |a| *1 := mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg u]) (abs_nonneg _)
      _ = |a| := mul_one _
  linarith

lemma continuous_integrand (z r a : ℝ) : Continuous (fun u=>
    weight a u*Real.cosh (u*(z-r))/(Real.cosh z*Real.cosh r)) := by
  exact Continuous.div_const ((continuous_weight a).mul (by fun_prop)) _

lemma phi_le_exp (z r a : ℝ) : phi z r a≤Real.exp (|a|/2) := by
  have H:=intervalIntegral.integral_mono_on (μ:=volume) (a:=(0:ℝ)) (b:=1) (by norm_num)
    ((continuous_integrand z r a).intervalIntegrable 0 1)
    (((continuous_integrand z r 0).const_mul (Real.exp (|a|/2))).intervalIntegrable 0 1)
    (by
      intro u hu
      simp only [weight,zero_mul,zero_div,Real.exp_zero,one_mul]
      rw [←mul_div_assoc]
      apply div_le_div_of_nonneg_right _ (le_of_lt (mul_pos (Real.cosh_pos _) (Real.cosh_pos _)))
      exact mul_le_mul_of_nonneg_right (weight_le a u hu) (Real.cosh_pos _).le)
  rw [intervalIntegral.integral_const_mul] at H
  exact H.trans ((mul_le_mul_of_nonneg_left (phi_zero_le_one z r) (Real.exp_pos _).le).trans_eq (mul_one _))

lemma abs_sinh_le_cosh (t : ℝ) : |Real.sinh t|≤Real.cosh t := by
  have h:=Real.cosh_sq_sub_sinh_sq t
  have ha:=sq_abs (Real.sinh t)
  nlinarith [Real.cosh_pos t,abs_nonneg (Real.sinh t)]

end SKGap.Stein

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Gaussian_PhiMoments
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory
namespace SKGap.Stein

lemma continuous_hyper (b : Bool) : Continuous (hyper b) := by unfold hyper; split_ifs <;> fun_prop
lemma hyper_hasDerivAt (b : Bool) (x : ℝ) : HasDerivAt (hyper b) (hyper (!b) x) x := by
  cases b <;> simpa only [hyper,Bool.not_false,Bool.not_true,Bool.false_eq_true,ite_false,ite_true] using
    (show HasDerivAt _ _ x from (by first | exact Real.hasDerivAt_cosh x | exact Real.hasDerivAt_sinh x))

lemma hyper_abs_le (b : Bool) (x : ℝ) : |hyper b x|≤Real.cosh x := by
  cases b
  · simp only [hyper,Bool.false_eq_true,ite_false,abs_of_pos (Real.cosh_pos _),le_refl]
  · exact abs_sinh_le_cosh x

lemma moment_base (z r a : ℝ) : moment 0 0 false z r a=phi z r a := by
  rw [phi_eq]
  simp only [moment,momentNum,numerator,pow_zero,mul_one,hyper,Bool.false_eq_true,ite_false]

lemma momentNum_hasDerivAt_d (p q : ℕ) (b : Bool) (d a : ℝ) :
    HasDerivAt (fun d=>momentNum p q b d a) (momentNum (p+1) q (!b) d a) d := by
  unfold momentNum
  apply hasDerivAt_integral01
    (F:=fun d u=>weight a u*u^p*((1-u^2)/2)^q*hyper b (u*d))
    (F':=fun d u=>weight a u*u^(p+1)*((1-u^2)/2)^q*hyper (!b) (u*d))
  · exact (((continuous_weight a).comp continuous_snd).mul (continuous_snd.pow p)|>.mul
      (((continuous_const.sub (continuous_snd.pow 2)).div_const 2).pow q)).mul
      ((continuous_hyper b).comp (continuous_snd.mul continuous_fst))
  · exact (((continuous_weight a).comp continuous_snd).mul (continuous_snd.pow (p+1))|>.mul
      (((continuous_const.sub (continuous_snd.pow 2)).div_const 2).pow q)).mul
      ((continuous_hyper (!b)).comp (continuous_snd.mul continuous_fst))
  · intro d u
    have H:=((hyper_hasDerivAt b (u*d)).comp d ((hasDerivAt_id d).const_mul u)).const_mul
      (weight a u*u^p*((1-u^2)/2)^q)
    convert! H using 1
    all_goals try with_reducible_and_instances rfl
    simp only [pow_succ]
    ring

lemma momentNum_hasDerivAt_a (p q : ℕ) (b : Bool) (d a : ℝ) :
    HasDerivAt (fun a=>momentNum p q b d a) (momentNum p (q+1) b d a) a := by
  unfold momentNum
  apply hasDerivAt_integral01
    (F:=fun a u=>weight a u*u^p*((1-u^2)/2)^q*hyper b (u*d))
    (F':=fun a u=>weight a u*u^p*((1-u^2)/2)^(q+1)*hyper b (u*d))
  · apply Continuous.mul
    · unfold weight; fun_prop
    · exact (continuous_hyper b).comp (continuous_snd.mul_const d)
  · apply Continuous.mul
    · unfold weight; fun_prop
    · exact (continuous_hyper b).comp (continuous_snd.mul_const d)
  · intro a u
    have H:=((((hasDerivAt_id a).mul_const (1-u^2)).div_const 2).exp).mul_const
      (u^p*((1-u^2)/2)^q*hyper b (u*d))
    convert! H using 1 <;> (try funext x) <;> dsimp [weight] <;> simp only [pow_succ] <;> ring

lemma momentNum_abs_le (p q : ℕ) (b : Bool) (d a : ℝ) :
    |momentNum p q b d a|≤ momentNum 0 0 false d a := by
  unfold momentNum
  apply (intervalIntegral.abs_integral_le_integral_abs (by norm_num : (0:ℝ)≤1)).trans
  apply intervalIntegral.integral_mono_on (by norm_num : (0:ℝ)≤1)
  · apply Continuous.intervalIntegrable
    apply Continuous.abs
    exact (((continuous_weight a).mul (continuous_id.pow p)).mul
      (((continuous_const.sub (continuous_id.pow 2)).div_const 2).pow q)).mul
      ((continuous_hyper b).comp (continuous_id.mul_const d))
  · apply Continuous.intervalIntegrable
    exact (((continuous_weight a).mul (continuous_id.pow 0)).mul
      (((continuous_const.sub (continuous_id.pow 2)).div_const 2).pow 0)).mul
      ((continuous_hyper false).comp (continuous_id.mul_const d))
  · intro u hu
    have hu2 : u^2≤1 := by nlinarith [hu.1,hu.2]
    have hv0 : 0≤(1-u^2)/2 := by linarith
    have hv1 : (1-u^2)/2≤1 := by nlinarith [sq_nonneg u]
    have hp : u^p ≤ 1 := pow_le_one₀ hu.1 hu.2
    have hq : ((1-u^2)/2)^q ≤ 1 := pow_le_one₀ hv0 hv1
    simp only [abs_mul,abs_of_pos (show 0<weight a u from Real.exp_pos _),
      abs_pow,abs_of_nonneg hu.1,abs_of_nonneg hv0,pow_zero,mul_one,
      hyper,Bool.false_eq_true,ite_false]
    have hH:=hyper_abs_le b (u*d)
    change |if b=true then Real.sinh (u*d) else Real.cosh (u*d)|≤Real.cosh (u*d) at hH
    have hprod : u^p*((1-u^2)/2)^q≤1 :=
      (mul_le_mul hp hq (pow_nonneg hv0 q) (by norm_num)).trans_eq (one_mul 1)
    have hh:=mul_le_mul (mul_le_mul_of_nonneg_left hprod (Real.exp_pos (a*(1-u^2)/2)).le)
      hH (abs_nonneg _) (by positivity)
    dsimp [weight] at *
    nlinarith only [hh]

lemma moment_relative_bound (p q : ℕ) (b : Bool) (z r a : ℝ) :
    |moment p q b z r a|≤phi z r a := by
  rw [moment,abs_div,abs_of_pos (mul_pos (Real.cosh_pos _) (Real.cosh_pos _)),←moment_base]
  exact div_le_div_of_nonneg_right (momentNum_abs_le p q b (z-r) a)
    (mul_pos (Real.cosh_pos _) (Real.cosh_pos _)).le

lemma moment_hasDerivAt_z (p q : ℕ) (b : Bool) (z r a : ℝ) :
    HasDerivAt (fun z=>moment p q b z r a)
      (moment (p+1) q (!b) z r a-Real.tanh z*moment p q b z r a) z := by
  have H:=((momentNum_hasDerivAt_d p q b (z-r) a).comp z ((hasDerivAt_id z).sub_const r)).div
    ((Real.hasDerivAt_cosh z).mul_const (Real.cosh r))
    (ne_of_gt (mul_pos (Real.cosh_pos _) (Real.cosh_pos _)))
  convert! H using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [moment]
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp [ne_of_gt (Real.cosh_pos z),ne_of_gt (Real.cosh_pos r)]

lemma moment_hasDerivAt_r (p q : ℕ) (b : Bool) (z r a : ℝ) :
    HasDerivAt (fun r=>moment p q b z r a)
      (-moment (p+1) q (!b) z r a-Real.tanh r*moment p q b z r a) r := by
  have H:=((momentNum_hasDerivAt_d p q b (z-r) a).comp r ((hasDerivAt_id r).const_sub z)).div
    ((Real.hasDerivAt_cosh r).const_mul (Real.cosh z))
    (ne_of_gt (mul_pos (Real.cosh_pos _) (Real.cosh_pos _)))
  convert! H using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [moment]
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp [ne_of_gt (Real.cosh_pos z),ne_of_gt (Real.cosh_pos r)]

lemma moment_hasDerivAt_a (p q : ℕ) (b : Bool) (z r a : ℝ) :
    HasDerivAt (fun a=>moment p q b z r a) (moment p (q+1) b z r a) a := by
  exact (momentNum_hasDerivAt_a p q b (z-r) a).div_const _

end SKGap.Stein

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_PhiAlgebra
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace SKGap.Stein

namespace KernelExpr

lemma mass_nonneg (f : KernelExpr) : 0 ≤ mass f := by
  induction f <;> simp only [mass] <;> positivity

lemma relative_bound (f : KernelExpr) (z r a : ℝ) : |eval f z r a| ≤ mass f*phi z r a := by
  induction f with
  | atom p q b  =>  simpa only [eval,mass,one_mul] using moment_relative_bound p q b z r a
  | add f g hf hg  =>
    exact (abs_add_le _ _).trans (by simpa only [eval,mass,add_mul] using add_le_add hf hg)
  | scale c f hf  =>
    dsimp only [eval,mass]
    rw [abs_mul,mul_assoc]
    exact mul_le_mul_of_nonneg_left hf (abs_nonneg c)
  | tz f hf  =>
    dsimp only [eval,mass]
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right (Real.abs_tanh_lt_one z).le (abs_nonneg _)).trans
      (by simpa only [one_mul] using hf)
  | tr f hf  =>
    dsimp only [eval,mass]
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right (Real.abs_tanh_lt_one r).le (abs_nonneg _)).trans
      (by simpa only [one_mul] using hf)

lemma hasDerivAt_z (f : KernelExpr) (z r a : ℝ) :
    HasDerivAt (fun z => eval f z r a) (eval (dz f) z r a) z := by
  induction f with
  | atom p q b  =>  simpa only [eval,dz,neg_mul,one_mul,←sub_eq_add_neg] using moment_hasDerivAt_z p q b z r a
  | add f g hf hg  =>  exact hf.add hg
  | scale c f hf  =>  exact hf.const_mul c
  | tz f hf  =>
    convert! (SKGapCutoff.tanh_hasDerivAt z).mul hf using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [eval,dz,SKGapCutoff.scalarVariance]
    ring
  | tr f hf  =>  exact hf.const_mul _

lemma hasDerivAt_r (f : KernelExpr) (z r a : ℝ) :
    HasDerivAt (fun r => eval f z r a) (eval (dr f) z r a) r := by
  induction f with
  | atom p q b  =>  simpa only [eval,dr,neg_mul,one_mul,←sub_eq_add_neg] using moment_hasDerivAt_r p q b z r a
  | add f g hf hg  =>  exact hf.add hg
  | scale c f hf  =>  exact hf.const_mul c
  | tz f hf  =>  exact hf.const_mul _
  | tr f hf  =>
    convert! (SKGapCutoff.tanh_hasDerivAt r).mul hf using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [eval,dr,SKGapCutoff.scalarVariance]
    ring

lemma hasDerivAt_a (f : KernelExpr) (z r a : ℝ) :
    HasDerivAt (fun a => eval f z r a) (eval (da f) z r a) a := by
  induction f with
  | atom p q b  =>  exact moment_hasDerivAt_a p q b z r a
  | add f g hf hg  =>  exact hf.add hg
  | scale c f hf  =>  exact hf.const_mul c
  | tz f hf  =>  exact hf.const_mul _
  | tr f hf  =>  exact hf.const_mul _

end KernelExpr

end SKGap.Stein

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_PhiFrechet
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter
open scoped Topology
namespace SKGap.Stein

lemma grad2_eq (a b : ℝ) : grad2 a b=
    a • ContinuousLinearMap.fst ℝ ℝ ℝ+b • ContinuousLinearMap.snd ℝ ℝ ℝ := by
  apply ContinuousLinearMap.ext; intro x; simp [grad2,ContinuousLinearMap.toSpanSingleton_apply,mul_comm]

lemma continuous_grad2 : Continuous (fun x : ℝ×ℝ=>grad2 x.1 x.2) := by
  simp only [grad2_eq]; fun_prop

lemma hasFDerivAt_of_three_partials (F Fz Fr Fa : ℝ→ℝ→ℝ→ℝ)
    (hz : ∀z r a,HasDerivAt (fun z=>F z r a) (Fz z r a) z)
    (hr : ∀z r a,HasDerivAt (fun r=>F z r a) (Fr z r a) r)
    (ha : ∀z r a,HasDerivAt (fun a=>F z r a) (Fa z r a) a)
    (cz : Continuous (eval3 Fz)) (cr : Continuous (eval3 Fr)) (ca : Continuous (eval3 Fa))
    (x : Triple) : HasFDerivAt (eval3 F) (grad3 (eval3 Fz x) (eval3 Fr x) (eval3 Fa x)) x := by
  have hpair (z : ℝ) (y : ℝ×ℝ) : HasFDerivAt (fun v : ℝ×ℝ=>F z v.1 v.2)
      (grad2 (Fr z y.1 y.2) (Fa z y.1 y.2)) y := by
    apply HasStrictFDerivAt.hasFDerivAt
    apply hasStrictFDerivAt_uncurry_coprod
      (f:=fun r a=>F z r a)
      (f₁:=fun r a=>ContinuousLinearMap.toSpanSingleton ℝ (Fr z r a))
      (f₂:=fun r a=>ContinuousLinearMap.toSpanSingleton ℝ (Fa z r a))
    · exact Eventually.of_forall fun v=>(hr z v.1 v.2).hasFDerivAt
    · exact Eventually.of_forall fun v=>(ha z v.1 v.2).hasFDerivAt
    · exact ((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp
        (cr.comp (continuous_const.prodMk continuous_id))).continuousAt
    · exact ((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp
        (ca.comp (continuous_const.prodMk continuous_id))).continuousAt
  apply HasStrictFDerivAt.hasFDerivAt
  apply hasStrictFDerivAt_uncurry_coprod
    (f:=fun (z : ℝ) (v : ℝ×ℝ)=>F z v.1 v.2)
    (f₁:=fun z v=>ContinuousLinearMap.toSpanSingleton ℝ (Fz z v.1 v.2))
    (f₂:=fun z v=>grad2 (Fr z v.1 v.2) (Fa z v.1 v.2))
  · exact Eventually.of_forall fun v=>(hz v.1 v.2.1 v.2.2).hasFDerivAt
  · exact Eventually.of_forall fun v=>hpair v.1 v.2
  · exact ((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp cz).continuousAt
  · exact (continuous_grad2.comp (cr.prodMk ca)).continuousAt

lemma continuous_momentNum (p q : ℕ) (b : Bool) :
    Continuous (fun x : ℝ×ℝ=>momentNum p q b x.1 x.2) := by
  unfold momentNum
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  apply Continuous.mul
  · unfold weight; fun_prop
  · exact (continuous_hyper b).comp (continuous_snd.mul (continuous_fst.fst))

lemma continuous_moment (p q : ℕ) (b : Bool) : Continuous (eval3 (moment p q b)) := by
  change Continuous (fun x : Triple=>momentNum p q b (x.1-x.2.1) x.2.2/(Real.cosh x.1*Real.cosh x.2.1))
  exact ((continuous_momentNum p q b).comp
    ((continuous_fst.sub continuous_snd.fst).prodMk continuous_snd.snd)).div
      ((Real.continuous_cosh.comp continuous_fst).mul (Real.continuous_cosh.comp continuous_snd.fst))
      (fun x=>(mul_pos (Real.cosh_pos _) (Real.cosh_pos _)).ne')

lemma continuous_tanh : Continuous Real.tanh :=
  continuous_iff_continuousAt.mpr fun z=>(SKGapCutoff.tanh_hasDerivAt z).continuousAt

namespace KernelExpr
lemma continuous_eval (f : KernelExpr) : Continuous (eval3 f.eval) := by
  induction f with
  | atom p q b => exact continuous_moment p q b
  | add f g hf hg => exact hf.add hg
  | scale c f hf => exact hf.const_mul c
  | tz f hf => exact (continuous_tanh.comp continuous_fst).mul hf
  | tr f hf => exact (continuous_tanh.comp continuous_snd.fst).mul hf

lemma hasFDerivAt_eval (f : KernelExpr) (x : Triple) :
    HasFDerivAt (eval3 f.eval) (f.gradient x) x :=
  hasFDerivAt_of_three_partials f.eval f.dz.eval f.dr.eval f.da.eval
    f.hasDerivAt_z f.hasDerivAt_r f.hasDerivAt_a
    f.dz.continuous_eval f.dr.continuous_eval f.da.continuous_eval x
end KernelExpr

lemma grad3_norm (a b c : ℝ) : ‖grad3 a b c‖≤|a|+|b|+|c| := by
  apply (grad3 a b c).opNorm_le_bound (by positivity)
  intro x
  have hz := norm_fst_le x
  have hr := (norm_fst_le x.2).trans (norm_snd_le x)
  have ha := (norm_snd_le x.2).trans (norm_snd_le x)
  change |x.1*a+(x.2.1*b+x.2.2*c)|≤(|a|+|b|+|c|)*‖x‖
  calc
    _ ≤ |x.1*a|+(|x.2.1*b|+|x.2.2*c|) := (abs_add_le _ _).trans
      (add_le_add (le_refl _) (abs_add_le _ _))
    _ ≤ ‖x‖*|a|+(‖x‖*|b|+‖x‖*|c|) := by
      simp only [abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_right hz (abs_nonneg _))
        (add_le_add (mul_le_mul_of_nonneg_right hr (abs_nonneg _))
          (mul_le_mul_of_nonneg_right ha (abs_nonneg _)))
    _ = _ := by ring

lemma grad3_sub (a b c d e f : ℝ) :
    grad3 a b c-grad3 d e f=grad3 (a-d) (b-e) (c-f) := by
  apply ContinuousLinearMap.ext; intro x
  simp only [grad3,grad2,sub_apply,ContinuousLinearMap.coprod_apply,
    ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul]
  ring

lemma convex_strip (R : ℝ) : Convex ℝ (strip R) := by
  intro x hx y hy a b ha hb hab
  change |a*x.2.2+b*y.2.2|≤R
  calc
    _ ≤ |a*x.2.2|+|b*y.2.2| := abs_add_le _ _
    _ = a*|x.2.2|+b*|y.2.2| := by rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hb]
    _ ≤ a*R+b*R := add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    _ = R := by rw [←add_mul,hab,one_mul]

namespace KernelExpr
lemma absolute_bound (f : KernelExpr) {R : ℝ} {x : Triple} (hx : x∈strip R) :
    |eval3 f.eval x|≤f.mass*Real.exp (R/2) := by
  exact (f.relative_bound x.1 x.2.1 x.2.2).trans (mul_le_mul_of_nonneg_left
    ((phi_le_exp ..).trans (Real.exp_le_exp.mpr (by dsimp [strip] at hx; linarith))) f.mass_nonneg)

lemma dBudget_nonneg (f : KernelExpr) (R : ℝ) : 0≤f.dBudget R := by
  unfold dBudget
  exact mul_nonneg (add_nonneg (add_nonneg f.dz.mass_nonneg f.dr.mass_nonneg) f.da.mass_nonneg)
    (Real.exp_pos _).le
lemma gradient_bound (f : KernelExpr) {R : ℝ} {x : Triple} (hx : x∈strip R) :
    ‖f.gradient x‖≤f.dBudget R := by
  apply (grad3_norm ..).trans
  exact (add_le_add (add_le_add (f.dz.absolute_bound hx) (f.dr.absolute_bound hx))
    (f.da.absolute_bound hx)).trans_eq (by dsimp [dBudget]; ring)

lemma lipschitz_strip (f : KernelExpr) {R : ℝ} {x y : Triple}
    (hx : x∈strip R) (hy : y∈strip R) :
    |eval3 f.eval y-eval3 f.eval x|≤f.dBudget R*‖y-x‖ := by
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _=>(f.hasFDerivAt_eval z).hasFDerivWithinAt)
    (fun _ hz=>f.gradient_bound hz) (convex_strip R) hx hy

lemma ddBudget_nonneg (f : KernelExpr) (R : ℝ) : 0≤f.ddBudget R :=
  add_nonneg (add_nonneg (f.dz.dBudget_nonneg R) (f.dr.dBudget_nonneg R)) (f.da.dBudget_nonneg R)

lemma gradient_lipschitz (f : KernelExpr) {R : ℝ} {x y : Triple}
    (hx : x∈strip R) (hy : y∈strip R) :
    ‖f.gradient y-f.gradient x‖≤f.ddBudget R*‖y-x‖ := by
  rw [gradient,gradient,grad3_sub]
  apply (grad3_norm ..).trans
  exact (add_le_add (add_le_add (f.dz.lipschitz_strip hx hy) (f.dr.lipschitz_strip hx hy))
    (f.da.lipschitz_strip hx hy)).trans_eq (by dsimp [ddBudget]; ring)
end KernelExpr

end SKGap.Stein

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_Taylor
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set
namespace SKGap.SourceTaylor
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma segment_lipschitz (F : E→ℝ) (F' : E→E→L[ℝ]ℝ) (x y : E) {C : ℝ}
    (hC : 0≤C)
    (hF : ∀t∈Icc (0:ℝ) 1,HasFDerivAt F (F' (x+t • (y-x))) (x+t • (y-x)))
    (hBound : ∀t∈Icc (0:ℝ) 1,‖F' (x+t • (y-x))‖≤C) :
    |F y-F x|≤C*‖y-x‖ := by
  let g : ℝ→ℝ:=fun t=>F (x+t • (y-x))
  let g' : ℝ→ℝ:=fun t=>F' (x+t • (y-x)) (y-x)
  have hg (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : HasDerivAt g (g' t) t := by
    convert! (hF t ht).comp_hasDerivAt t (((hasDerivAt_id t).smul_const (y-x)).const_add x) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [g',one_smul]
  have hb (t : ℝ) (ht : t∈Ico (0:ℝ) 1) : ‖g' t‖≤C*‖y-x‖ :=
    ((F' (x+t • (y-x))).le_opNorm _).trans
      (mul_le_mul (hBound t ⟨ht.1,ht.2.le⟩) le_rfl (norm_nonneg _) hC)
  have H:=norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t ht=>(hg t ht).hasDerivWithinAt) hb
  simpa only [g,one_smul,zero_smul,add_sub_cancel,add_zero,Real.norm_eq_abs] using H

end SKGap.SourceTaylor

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_Operation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix
variable {n : ℕ}

lemma vectorNorm_sq (u : Fin n→ℝ) : vectorNorm u^2=∑i,(u i)^2 := by
  exact EuclideanSpace.real_norm_sq_eq _

lemma vectorNorm_nonneg (u : Fin n→ℝ) : 0 ≤ vectorNorm u := norm_nonneg _

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix
variable {n : ℕ}

lemma vectorNorm_smul (c : ℝ) (u : Fin n→ℝ) :
    vectorNorm (c • u)=|c| *vectorNorm u := by
  exact norm_smul c (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))

lemma vectorNorm_mono {u v : Fin n→ℝ} (h : ∀i,|u i|≤|v i|) : vectorNorm u ≤ vectorNorm v := by
  apply nonneg_le_nonneg_of_sq_le_sq (vectorNorm_nonneg _)
  simp only [←sq,vectorNorm_sq]
  exact Finset.sum_le_sum fun i _=>by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (u i)) (h i) 2

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_PhiRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein
variable {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype ι] [Fintype κ] in
lemma affine_segment (L : Args (ι:=ι) (κ:=κ)→L[ℝ]Triple) (s : Triple)
    (u v : Args (ι:=ι) (κ:=κ)) (t : ℝ) :
    L (u+t • (v-u))+s=(L u+s)+t • ((L v+s)-(L u+s)) := by
  simp only [map_add,map_smul,map_sub]
  module

lemma affine_segmentRegular (H : ι→VectorFields n) (θ : κ→Spin n→ℝ) (x : Spin n)
    (F : Triple→ℝ) (F' : Triple→Triple→L[ℝ]ℝ)
    (L : Args (ι:=ι) (κ:=κ)→L[ℝ]Triple) (s : Fin n→Triple)
    (S : Set Triple) (hS : Convex ℝ S) {B D : ℝ} (hB : 0≤B) (hD : 0≤D)
    (hderiv : ∀u∈S,HasFDerivAt F (F' u) u)
    (hbound : ∀u∈S,‖F' u‖≤B)
    (hlip : ∀u∈S,∀v∈S,‖F' v-F' u‖≤D*‖v-u‖)
    (hbase : ∀i,L (localArgs H θ x i)+s i∈S)
    (hflip : ∀i k,L (localArgs H θ (flip x k) i)+s i∈S) :
    SegmentRegular H θ (fun i u=>F (L u+s i))
      (fun i u=>(F' (L u+s i)).comp L) x (B*‖L‖+D*‖L‖^2) := by
  have hc : 0≤B*‖L‖+D*‖L‖^2 := by positivity
  have hm (i : Fin n) (k : Fin n) (t : ℝ) (ht : t∈Set.Icc (0:ℝ) 1) :
      L (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i))+s i∈S := by
    rw [affine_segment]
    exact hS.add_smul_sub_mem (hbase i) (hflip i k) ht
  refine ⟨hc,?_,?_,?_⟩
  · intro i k t ht
    exact (hderiv _ (hm i k t ht)).comp
      (f:=fun u : Args (ι:=ι) (κ:=κ)=>L u+s i)
      (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i))
      (L.hasFDerivAt.add_const (s i))
  · intro i k t ht
    exact ((F' _).opNorm_comp_le L).trans ((mul_le_mul_of_nonneg_right
      (hbound _ (hm i k t ht)) (norm_nonneg L)).trans (le_add_of_nonneg_right (by positivity)))
  · intro i k t ht
    rw [←ContinuousLinearMap.sub_comp]
    apply (ContinuousLinearMap.opNorm_comp_le _ L).trans
    have hd := hlip _ (hbase i) _ (hm i k t ht)
    have hid : L (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i))+s i-
        (L (localArgs H θ x i)+s i)=L (t • (localArgs H θ (flip x k) i-localArgs H θ x i)) := by
      simp only [map_add]; abel
    rw [hid] at hd
    have hb := L.le_opNorm (t • (localArgs H θ (flip x k) i-localArgs H θ x i))
    have h₁ := (mul_le_mul_of_nonneg_left hb hD)
    have h₂ := mul_le_mul_of_nonneg_right (hd.trans h₁) (norm_nonneg L)
    apply h₂.trans
    nlinarith only [mul_nonneg (mul_nonneg hB (norm_nonneg L))
      (norm_nonneg (t • (localArgs H θ (flip x k) i-localArgs H θ x i)))]

lemma phi_kernel_segmentRegular (f : KernelExpr) (H : ι→VectorFields n)
    (θ : κ→Spin n→ℝ) (x : Spin n)
    (L : Args (ι:=ι) (κ:=κ)→L[ℝ]Triple) (s : Fin n→Triple) (R : ℝ)
    (hbase : ∀i,L (localArgs H θ x i)+s i∈strip R)
    (hflip : ∀i k,L (localArgs H θ (flip x k) i)+s i∈strip R) :
    SegmentRegular H θ (fun i u=>eval3 f.eval (L u+s i))
      (fun i u=>(f.gradient (L u+s i)).comp L) x
      (f.dBudget R*‖L‖+f.ddBudget R*‖L‖^2) :=
  affine_segmentRegular H θ x (eval3 f.eval) f.gradient L s (strip R) (convex_strip R)
    (f.dBudget_nonneg R) (f.ddBudget_nonneg R)
    (fun u _=>f.hasFDerivAt_eval u) (fun _ hu=>f.gradient_bound hu)
    (fun _ hu _ hv=>f.gradient_lipschitz hu hv) hbase hflip

omit [Fintype ι] [Fintype κ] in
lemma phiSelect_apply (l : ι) (α : κ) (u : Args (ι:=ι) (κ:=κ)) :
    phiSelect l α u=(u (.inl l),(0,u (.inr α))) := rfl
lemma phiSelect_norm (l : ι) (α : κ) : ‖phiSelect l α‖≤1 := by
  apply (phiSelect l α).opNorm_le_bound (by norm_num)
  intro u
  rw [one_mul,phiSelect_apply,Prod.norm_def,Prod.norm_def]
  exact max_le (norm_le_pi_norm u _) (max_le (by simp) (norm_le_pi_norm u _))

end SKGapCutoff.Recipe

namespace SKGapCutoff.Recipe
open SKGap.Stein
variable {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
lemma SegmentRegular.mono {H : ι→VectorFields n} {θ : κ→Spin n→ℝ}
    {F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ}
    {F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ}
    {x : Spin n} {C D : ℝ} (h : SegmentRegular H θ F F' x C) (hCD : C≤D) :
    SegmentRegular H θ F F' x D :=
  ⟨h.nonneg.trans hCD,h.deriv,(fun i k t ht=>(h.bound i k t ht).trans hCD),
    (fun i k t ht=>(h.lip i k t ht).trans (mul_le_mul_of_nonneg_right hCD (norm_nonneg _)))⟩

lemma fixed_root_kernel_regular (f : KernelExpr) (H : ι→VectorFields n)
    (θ : κ→Spin n→ℝ) (x : Spin n) (l : ι) (α : κ) (r : Fin n→ℝ) (R : ℝ)
    (hx : |θ α x|≤R) (hf : ∀k,|θ α (flip x k)|≤R) :
    SegmentRegular H θ (fun i u=>eval3 f.eval (phiSelect l α u+(0,(r i,0))))
      (fun i u=>(f.gradient (phiSelect l α u+(0,(r i,0)))).comp (phiSelect l α)) x
      (f.dBudget R+f.ddBudget R) := by
  have h:=phi_kernel_segmentRegular f H θ x (phiSelect l α) (fun i=>(0,(r i,0))) R
    (fun _=>by simpa [strip,phiSelect,localArgs] using hx)
    (fun _ k=>by simpa [strip,phiSelect,localArgs] using hf k)
  apply h.mono
  have h1:=phiSelect_norm l α
  have h2:=pow_le_pow_left₀ (norm_nonneg (phiSelect l α)) h1 2
  simpa only [mul_one,one_pow] using add_le_add
    (mul_le_mul_of_nonneg_left h1 (f.dBudget_nonneg R))
    (mul_le_mul_of_nonneg_left h2 (f.ddBudget_nonneg R))

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_LiteralInitialRecipe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary
variable {n : ℕ}

lemma initialKernel_phi (r : ℝ) (u : InitialArgs) :
    initialKernel phiExpr r u=phi (u (.inl ())) r (u (.inr false)) := moment_base _ _ _
lemma phiExpr_dz (z r a : ℝ) : phiExpr.dz.eval z r a=phiZ z r a := by
  have H:=phiExpr.hasDerivAt_z z r a
  have He : phiExpr.eval=phi := funext fun _=>funext fun _=>funext fun _=>moment_base _ _ _
  rw [He] at H
  exact H.unique (phi_hasDerivAt z r a)

lemma initialGradient_primary (f : KernelExpr) (r : ℝ) (u : InitialArgs) :
    partialAt (initialGradient f r u) (.inl ())=f.dz.eval (u (.inl ())) r (u (.inr false)) := by
  simp [partialAt,initialGradient,phiSelect,KernelExpr.gradient,grad3,grad2,
    ContinuousLinearMap.toSpanSingleton_apply,eval3]

lemma literalInitial_coefficient (J : Interaction n) (j d : ℝ) (f : KernelExpr)
    (z m : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (x : Spin n) (i : Fin n) :
    (literalInitial J j d f z m a c r e).implicitCoefficient x i=phi (z x i) (r i) (a x) := by
  simp [OrdinaryData.implicitCoefficient,OrdinaryData.auxCoefficient,literalInitial,
    coefficient,initialKernel_phi,localArgs]

lemma literalInitial_source (J : Interaction n) (j d : ℝ) (f : KernelExpr)
    (z m y : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (hd : d≠0) (x : Spin n) (i : Fin n) :
    (literalInitial J j d f z m a c r e).sourceOf 1 (fun _=>y) x i=
      f.eval (z x i) (r i) (a x)*e i+
        phi (z x i) (r i) (a x)*(y x i-j*c x*Real.tanh (r i)) := by
  simp [OrdinaryData.sourceOf,OrdinaryData.seedCoefficient,OrdinaryData.auxCoefficient,
    literalInitial,coefficient,initialKernel,phiExpr,KernelExpr.eval,moment_base,localArgs]
  field_simp
  ring

lemma literalInitial_partial (J : Interaction n) (j d : ℝ) (f : KernelExpr)
    (z m y : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (hd : d≠0) (x : Spin n) (i : Fin n) :
    (literalInitial J j d f z m a c r e).implicitPartial y x i=
      f.dz.eval (z x i) (r i) (a x)*e i+
        phiZ (z x i) (r i) (a x)*(y x i-j*c x*Real.tanh (r i)) := by
  simp only [OrdinaryData.implicitPartial,OrdinaryData.partialOf,OrdinaryData.seedPartial,
    OrdinaryData.auxPartial,localPartial,literalInitial,Fintype.sum_bool,Fin.sum_univ_one]
  simp only [Bool.false_eq_true,↓reduceIte,initialGradient_primary]
  simp [partialAt,initialGradient,phiSelect,KernelExpr.gradient,grad3,grad2,
    ContinuousLinearMap.toSpanSingleton_apply,eval3,localArgs,phiExpr_dz]
  field_simp
  ring

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_ResidualAdmissibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
variable {n : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

namespace SegmentRegular
variable {H : ι→VectorFields n} {θ : κ→Spin n→ℝ}
variable {F G : Fin n→Args (ι:=ι) (κ:=κ)→ℝ}
variable {F' G' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ}
variable {x : Spin n} {C D : ℝ}

omit [DecidableEq ι] [DecidableEq κ] in
lemma value_difference (h : SegmentRegular H θ F F' x C) (i k : Fin n)
    (t : ℝ) (ht : t∈Set.Icc (0:ℝ) 1) :
    |F i (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i))-
      F i (localArgs H θ x i)|≤C*‖t • (localArgs H θ (flip x k) i-localArgs H θ x i)‖ := by
  let u:=localArgs H θ x i
  let v:=localArgs H θ (flip x k) i
  have hm (s : ℝ) (hs : s∈Set.Icc (0:ℝ) 1) : s*t∈Set.Icc (0:ℝ) 1 :=
    ⟨mul_nonneg hs.1 ht.1,(mul_le_mul hs.2 ht.2 ht.1 (by norm_num)).trans_eq (by norm_num)⟩
  have he (s : ℝ) : u+s • (u+t • (v-u)-u)=u+(s*t) • (v-u) := by module
  have hb:=SKGap.SourceTaylor.segment_lipschitz (F i) (F' i) u (u+t • (v-u)) h.nonneg
    (fun s hs=>by rw [he]; exact h.deriv i k (s*t) (hm s hs))
    (fun s hs=>by rw [he]; exact h.bound i k (s*t) (hm s hs))
  simpa only [add_sub_cancel_left] using hb

omit [DecidableEq ι] [DecidableEq κ] in
lemma mul (hF : SegmentRegular H θ F F' x C) (hG : SegmentRegular H θ G G' x D)
    {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hvF : ∀i k t, t∈Set.Icc (0:ℝ) 1→
      |F i (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i))|≤A)
    (hvG : ∀i k t, t∈Set.Icc (0:ℝ) 1→
      |G i (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i))|≤B) :
    SegmentRegular H θ (fun i u=>F i u*G i u)
      (fun i u=>F i u • G' i u+G i u • F' i u) x (A*D+B*C+2*C*D) := by
  refine ⟨by positivity [hF.nonneg,hG.nonneg],?_,?_,?_⟩
  · intro i k t ht
    exact (hF.deriv i k t ht).mul (hG.deriv i k t ht)
  · intro i k t ht
    let u:=localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i)
    have h₁ : ‖F i u • G' i u‖≤A*D := by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul (hvF i k t ht) (hG.bound i k t ht) (norm_nonneg _) hA
    have h₂ : ‖G i u • F' i u‖≤B*C := by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul (hvG i k t ht) (hF.bound i k t ht) (norm_nonneg _) hB
    have hh := (norm_add_le _ _).trans (add_le_add h₁ h₂)
    exact hh.trans (le_add_of_nonneg_right (by positivity [hF.nonneg,hG.nonneg]))
  · intro i k t ht
    let u:=localArgs H θ x i
    let v:=u+t • (localArgs H θ (flip x k) i-u)
    let d:=‖t • (localArgs H θ (flip x k) i-u)‖
    have hf : |F i v-F i u|≤C*d := hF.value_difference i k t ht
    have hg : |G i v-G i u|≤D*d := hG.value_difference i k t ht
    have hf' : ‖F' i v-F' i u‖≤C*d := hF.lip i k t ht
    have hg' : ‖G' i v-G' i u‖≤D*d := hG.lip i k t ht
    have hfu : ‖F' i u‖≤C := by simpa [u] using hF.bound i k 0 (by constructor <;> norm_num)
    have hgu : ‖G' i u‖≤D := by simpa [u] using hG.bound i k 0 (by constructor <;> norm_num)
    have he : (F i v • G' i v+G i v • F' i v)-(F i u • G' i u+G i u • F' i u)=
        (F i v • (G' i v-G' i u)+(F i v-F i u) • G' i u)+
        (G i v • (F' i v-F' i u)+(G i v-G i u) • F' i u) := by module
    change ‖(F i v • G' i v+G i v • F' i v)-(F i u • G' i u+G i u • F' i u)‖≤_
    rw [he]
    have h₁ : ‖F i v • (G' i v-G' i u)‖≤A*(D*d) := by
      rw [norm_smul,Real.norm_eq_abs]; exact mul_le_mul (hvF i k t ht) hg' (norm_nonneg _) hA
    have h₂ : ‖(F i v-F i u) • G' i u‖≤(C*d)*D := by
      rw [norm_smul,Real.norm_eq_abs]; exact mul_le_mul hf hgu (norm_nonneg _) (by positivity [hF.nonneg])
    have h₃ : ‖G i v • (F' i v-F' i u)‖≤B*(C*d) := by
      rw [norm_smul,Real.norm_eq_abs]; exact mul_le_mul (hvG i k t ht) hf' (norm_nonneg _) hB
    have h₄ : ‖(G i v-G i u) • F' i u‖≤(D*d)*C := by
      rw [norm_smul,Real.norm_eq_abs]; exact mul_le_mul hg hfu (norm_nonneg _) (by positivity [hG.nonneg])
    have hh := (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add h₁ h₂))
      ((norm_add_le _ _).trans (add_le_add h₃ h₄)))
    exact hh.trans_eq (by dsimp only [d]; ring)

end SegmentRegular
end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Stability_ImplicitCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary
variable {n : ℕ}

lemma vectorNorm_const (c : ℝ) : vectorNorm (fun _ : Fin n=>c)=|c| *Real.sqrt n := by
  apply (sq_eq_sq₀ (vectorNorm_nonneg _) (by positivity)).mp
  rw [vectorNorm_sq,mul_pow,sq_abs,Real.sq_sqrt (Nat.cast_nonneg n)]
  simp [mul_comm]

lemma vectorNorm_tanh (z : Fin n→ℝ) : vectorNorm (fun i=>Real.tanh (z i))≤Real.sqrt n := by
  simpa only [vectorNorm_const,abs_one,one_mul] using
    (vectorNorm_mono (u:=fun i=>Real.tanh (z i)) (v:=fun _=>1)
      (fun i=>by simpa using (Real.abs_tanh_lt_one (z i)).le))

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_LiteralInitialSystem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary SKGap.ImplicitSystem Matrix
variable {n : ℕ}

lemma literalInitial_partial_source (J : Interaction n) (j d : ℝ) (f : KernelExpr)
    (z m w y : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (hd : d≠0) (x : Spin n)
    (hw : w x=(literalInitial J j d f z m a c r e).sourceOf 1 (fun _=>y) x) :
    (literalInitial J j d f z m a c r e).implicitPartial y x=
      fun i=>logSlope (z x i) (r i) (a x)*w x i+initialP f z a r e x i := by
  ext i
  rw [literalInitial_partial _ _ _ _ _ _ _ _ _ _ _ hd,hw,literalInitial_source _ _ _ _ _ _ _ _ _ _ _ hd]
  dsimp only [initialP,logSlope]
  field_simp [(phi_pos (z x i) (r i) (a x)).ne']
  ring

lemma literalInitial_field (J : Interaction n) (j d : ℝ) (f : KernelExpr)
    (z m w y : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (x : Spin n)
    (hw : w x=(literalInitial J j d f z m a c r e).sourceOf 1 (fun _=>y) x)
    (hc : c x=siteMean ((literalInitial J j d f z m a c r e).implicitPartial y) x) :
    (literalInitial J j d f z m a c r e).fieldOf 1 (fun _=>w) (fun _=>y) x=
      fun i=>J.mulVec (w x) i-j*siteMean (fun x i=>phi (z x i) (r i) (a x)) x*w x i-j*c x*m x i := by
  ext i
  simp only [OrdinaryData.fieldOf,←hw,Fintype.sum_unique]
  change J.mulVec (w x) i-j*(siteMean ((literalInitial J j d f z m a c r e).implicitPartial y) x*m x i)-
    j*(siteMean ((literalInitial J j d f z m a c r e).implicitCoefficient) x*w x i)=_
  have he : (literalInitial J j d f z m a c r e).implicitCoefficient=fun x i=>phi (z x i) (r i) (a x) := by
    ext v k; exact literalInitial_coefficient ..
  rw [he,←hc]
  ring

lemma initial_scalar_equation (f : KernelExpr) (z w : VectorFields n)
    (a c : Spin n→ℝ) (r e : Fin n→ℝ) (x : Spin n) :
    c x=(n:ℝ)⁻¹*inner ℝ (WithLp.toLp 2 (fun i=>logSlope (z x i) (r i) (a x)) : Euclid n)
        (WithLp.toLp 2 (w x))+siteMean (initialP f z a r e) x ↔
      c x=siteMean (fun x i=>logSlope (z x i) (r i) (a x)*w x i+initialP f z a r e x i) x := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial,dotProduct,siteMean,
    Finset.sum_add_distrib,div_eq_mul_inv]
  simp [mul_comm,add_comm,mul_add]

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_LiteralSystemBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary SKGap.ImplicitSystem Matrix
variable {n : ℕ}

lemma phiDiagonal_apply (z r : Fin n→ℝ) (a : ℝ) (v : Euclid n) (i : Fin n) :
    phiDiagonal z r a v i=phi (z i) (r i) a*v i := by
  change (toEuclideanCLM (𝕜:=ℝ) (diagonal (fun k=>phi (z k) (r k) a)) (WithLp.toLp 2 v.ofLp)) i=_
  simp only [toEuclideanCLM_toLp,WithLp.ofLp_toLp,mulVec_diagonal]

lemma literal_first_equation (J : Interaction n) (j d : ℝ) (f : KernelExpr)
    (z m w y : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (hd : d≠0) (x : Spin n) :
    ((WithLp.toLp 2 (w x) : Euclid n)=phiDiagonal (z x) r (a x)
      (WithLp.toLp 2 (initialU f z a r e x)+WithLp.toLp 2 (y x)-
        (j*c x) • WithLp.toLp 2 (fun i=>Real.tanh (r i)))) ↔
      w x=(literalInitial J j d f z m a c r e).sourceOf 1 (fun _=>y) x := by
  have he : (phiDiagonal (z x) r (a x)
      (WithLp.toLp 2 (initialU f z a r e x)+WithLp.toLp 2 (y x)-
        (j*c x) • WithLp.toLp 2 (fun i=>Real.tanh (r i)))).ofLp=
      (literalInitial J j d f z m a c r e).sourceOf 1 (fun _=>y) x := by
    ext i
    rw [literalInitial_source _ _ _ _ _ _ _ _ _ _ _ hd]
    change phiDiagonal _ _ _ _ i=_
    rw [phiDiagonal_apply]
    change phi (z x i) (r i) (a x)*
      (f.eval (z x i) (r i) (a x)/phi (z x i) (r i) (a x)*e i+y x i-j*c x*Real.tanh (r i))=_
    field_simp [(phi_pos (z x i) (r i) (a x)).ne']
    ring
  constructor
  · intro h; exact (congrArg WithLp.ofLp h).trans he
  · intro h; exact WithLp.ofLp_injective 2 (h.trans he.symm)

lemma literalEquations_recipe (J : Interaction n) (j d : ℝ) (f : KernelExpr)
    (z m w y : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (hd : d≠0) (x : Spin n) :
    LiteralEquations J j f z m w y a c r e x ↔
      w x=(literalInitial J j d f z m a c r e).sourceOf 1 (fun _=>y) x ∧
      y x=(literalInitial J j d f z m a c r e).fieldOf 1 (fun _=>w) (fun _=>y) x ∧
      c x=siteMean ((literalInitial J j d f z m a c r e).implicitPartial y) x := by
  have hc (hw : w x=(literalInitial J j d f z m a c r e).sourceOf 1 (fun _=>y) x) :
      c x=(n:ℝ)⁻¹*inner ℝ (WithLp.toLp 2 (fun i=>logSlope (z x i) (r i) (a x)) : Euclid n)
          (WithLp.toLp 2 (w x))+siteMean (initialP f z a r e) x ↔
        c x=siteMean ((literalInitial J j d f z m a c r e).implicitPartial y) x := by
    rw [initial_scalar_equation]
    change c x=(∑i,(logSlope (z x i) (r i) (a x)*w x i+initialP f z a r e x i))/(n:ℝ) ↔ _
    rw [siteMean,literalInitial_partial_source _ _ _ _ _ _ _ _ _ _ _ _ hd x hw]
  have hy (hw : w x=(literalInitial J j d f z m a c r e).sourceOf 1 (fun _=>y) x)
      (hc : c x=siteMean ((literalInitial J j d f z m a c r e).implicitPartial y) x) :
      (WithLp.toLp 2 (y x) : Euclid n)=toEuclideanCLM (𝕜:=ℝ) J (WithLp.toLp 2 (w x))-
        (j*siteMean (fun v i=>phi (z v i) (r i) (a v)) x) • WithLp.toLp 2 (w x)-
        (j*c x) • WithLp.toLp 2 (m x) ↔
      y x=(literalInitial J j d f z m a c r e).fieldOf 1 (fun _=>w) (fun _=>y) x := by
    rw [literalInitial_field _ _ _ _ _ _ _ _ _ _ _ _ x hw hc]
    constructor
    · intro h; exact congrArg WithLp.ofLp h
    · intro h; exact WithLp.ofLp_injective 2 h
  constructor
  · intro h
    have hw:=(literal_first_equation J j d f z m w y a c r e hd x).mp h.1
    have hs:=(hc hw).mp h.2.2
    exact ⟨hw,(hy hw hs).mp h.2.1,hs⟩
  · rintro ⟨hw,hy',hc'⟩
    exact ⟨(literal_first_equation J j d f z m w y a c r e hd x).mpr hw,
      (hy hw hc').mpr hy',(hc hw).mpr hc'⟩
end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_LiteralRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary
variable {n : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
lemma SegmentRegular.const_mul {H : ι→VectorFields n} {θ : κ→Spin n→ℝ}
    {F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ}
    {F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ}
    {x : Spin n} {C : ℝ} (h : SegmentRegular H θ F F' x C) (b : ℝ) :
    SegmentRegular H θ (fun i u=>b*F i u) (fun i u=>b • F' i u) x (|b| *C) := by
  refine ⟨mul_nonneg (abs_nonneg _) h.nonneg,?_,?_,?_⟩
  · intro i k t ht; exact (h.deriv i k t ht).const_mul b
  · intro i k t ht
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (h.bound i k t ht) (abs_nonneg _)
  · intro i k t ht
    rw [←smul_sub b (F' i _) (F' i _),norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (h.lip i k t ht) (abs_nonneg _)).trans_eq (by ring)

omit [DecidableEq ι] [DecidableEq κ] in
lemma parameter_regular (H : ι→VectorFields n) (θ : κ→Spin n→ℝ) (x : Spin n) (α : κ) :
    SegmentRegular H θ (fun _ u=>u (.inr α))
      (fun _ _=>ContinuousLinearMap.proj (.inr α)) x 1 := by
  refine ⟨by norm_num,?_,?_,?_⟩
  · intro i k t ht; exact (ContinuousLinearMap.proj (Sum.inr α : ι ⊕ κ) : Args (ι:=ι) (κ:=κ) →L[ℝ] ℝ).hasFDerivAt
  · intro i k t ht
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro u
    simpa using norm_le_pi_norm u (.inr α)
  · intro i k t ht; simp

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
lemma parameter_segment_value (H : ι→VectorFields n) (θ : κ→Spin n→ℝ) (x : Spin n)
    (α : κ) {B : ℝ} (hx : |θ α x|≤B) (hf : ∀k,|θ α (flip x k)|≤B)
    (i k : Fin n) (t : ℝ) (ht : t∈Set.Icc (0:ℝ) 1) :
    |(localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i)) (.inr α)|≤B := by
  change |θ α x+t*(θ α (flip x k)-θ α x)|≤B
  have hx' := abs_le.mp hx
  have hf' := abs_le.mp (hf k)
  apply abs_le.mpr
  constructor
  · nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hf'.1),
      mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hx'.1)]
  · nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hf'.2),
      mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hx'.2)]

lemma initialKernel_regular (f : KernelExpr) (H : Unit→VectorFields n)
    (θ : Bool→Spin n→ℝ) (x : Spin n) (r : Fin n→ℝ) (R : ℝ)
    (hx : |θ false x|≤R) (hf : ∀k,|θ false (flip x k)|≤R) :
    SegmentRegular H θ (fun i=>initialKernel f (r i))
      (fun i=>initialGradient f (r i)) x (f.dBudget R+f.ddBudget R) := by
  convert fixed_root_kernel_regular f H θ x () false r R hx hf using 1
  · ext i u; simp [initialKernel,phiSelect_apply,eval3]
  · rfl

lemma initialKernel_segment_value (f : KernelExpr) (H : Unit→VectorFields n)
    (θ : Bool→Spin n→ℝ) (x : Spin n) (r : Fin n→ℝ) (R : ℝ)
    (hx : |θ false x|≤R) (hf : ∀k,|θ false (flip x k)|≤R)
    (i k : Fin n) (t : ℝ) (ht : t∈Set.Icc (0:ℝ) 1) :
    |initialKernel f (r i) (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i))|≤
      f.mass*Real.exp (R/2) := by
  change |eval3 f.eval (_, r i, _)| ≤ _
  apply f.absolute_bound
  exact parameter_segment_value H θ x false hx hf i k t ht

lemma literalInitial_regular (J : Interaction n) (j d : ℝ) (f : KernelExpr)
    (z m : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (x : Spin n)
    {R B : ℝ} (hB : 0≤B) (ha : |a x|≤R) (haf : ∀k,|a (flip x k)|≤R)
    (hc : |d*c x|≤B) (hcf : ∀k,|d*c (flip x k)|≤B) :
    let D:=literalInitial J j d f z m a c r e
    (∀s,SegmentRegular D.H D.θ (D.seedFunction 1 s) (D.seedDerivative 1 s) x
      (initialRegularBudget f j R B)) ∧
    SegmentRegular D.H D.θ (D.auxFunction 1 0) (D.auxDerivative 1 0) x
      (initialRegularBudget f j R B) := by
  let D:=literalInitial J j d f z m a c r e
  have hp:=initialKernel_regular phiExpr D.H D.θ x r R ha haf
  have hF:=initialKernel_regular f D.H D.θ x r R ha haf
  have hT:=parameter_regular D.H D.θ x true
  have hm:=hT.mul hp hB (mul_nonneg phiExpr.mass_nonneg (Real.exp_pos _).le)
    (parameter_segment_value D.H D.θ x true hc hcf)
    (initialKernel_segment_value phiExpr D.H D.θ x r R ha haf)
  have hm':=hm.const_mul (-j)
  simp only [abs_neg,mul_one] at hm'
  have hphi : 0≤phiExpr.dBudget R+phiExpr.ddBudget R:=add_nonneg (phiExpr.dBudget_nonneg _) (phiExpr.ddBudget_nonneg _)
  have hf0 : 0≤f.dBudget R+f.ddBudget R:=add_nonneg (f.dBudget_nonneg _) (f.ddBudget_nonneg _)
  have he : 0≤|j| *(B*(phiExpr.dBudget R+phiExpr.ddBudget R)+phiExpr.mass*Real.exp (R/2)+
      2*(phiExpr.dBudget R+phiExpr.ddBudget R)):=by positivity [phiExpr.mass_nonneg]
  constructor
  · intro s
    cases s
    · exact hF.mono (by dsimp [initialRegularBudget]; linarith)
    · convert hm'.mono (show |j| *(B*(phiExpr.dBudget R+phiExpr.ddBudget R)+phiExpr.mass*Real.exp (R/2)+
          2*(phiExpr.dBudget R+phiExpr.ddBudget R))≤ initialRegularBudget f j R B by
          dsimp [initialRegularBudget]; linarith) using 1
      · ext i u
        dsimp [D,literalInitial]
        ring
      · rfl
  · exact hp.mono (by dsimp [initialRegularBudget]; linarith)
end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_StartedRecipe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe.OrdinaryData
open Primary Matrix SKGap.Noncrossing.Primary
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]
variable (D : OrdinaryData n ι κ σ)

lemma startedSource_eq (w y : VectorFields n) {a : ℕ} (ha : 0<a) :
    D.startedSource w y a=D.sourceOf a (fun b=>D.startedAuxiliary w y b) := by
  obtain ⟨a,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : a≠0)
  rw [startedSource,startedEvaluate];rfl
lemma startedAuxiliary_eq (w y : VectorFields n) {a : ℕ} (ha : 0<a) :
    D.startedAuxiliary w y a=D.fieldOf a (fun b=>D.startedSource w y b) (fun b=>D.startedAuxiliary w y b) := by
  obtain ⟨a,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : a≠0)
  rw [startedAuxiliary,startedEvaluate];rfl

lemma startedSource_one (w y : VectorFields n) :
    D.startedSource w y 1=D.sourceOf 1 (fun _=>y) := by
  rw [D.startedSource_eq w y (by omega)]
  congr 1;funext index
  simp
lemma startedAuxiliary_one (w y : VectorFields n) :
    D.startedAuxiliary w y 1=D.fieldOf 1 (fun _=>w) (fun _=>y) := by
  rw [D.startedAuxiliary_eq w y (by omega)]
  congr 1 <;> funext index
  all_goals simp

end SKGapCutoff.Recipe.OrdinaryData

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_BufferedSelectionDiagnostics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary
variable {n : ℕ}

lemma literalInitial_coefficientClass (J : Interaction n) (j d : ℝ) (f : KernelExpr)
    (z m : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (x : Spin n)
    {R B : ℝ} (hB : 0≤B) (ha : |a x|≤R) (haf : ∀k,|a (flip x k)|≤R)
    (hc : |d*c x|≤B) (hcf : ∀k,|d*c (flip x k)|≤B) (N : ℕ) :
    (literalInitial J j d f z m a c r e).CoefficientClass N x
      (literalCoefficientBudget f j R B) := by
  let D:=literalInitial J j d f z m a c r e
  let K:=literalCoefficientBudget f j R B
  have hreg:=literalInitial_regular J j d f z m a c r e x hB ha haf hc hcf
  have h1 : 1≤K := by
    have h2 : 0≤f.mass*Real.exp (R/2):=mul_nonneg f.mass_nonneg (Real.exp_pos _).le
    have h3 : 0≤(1+|j| *|B|)*phiExpr.mass*Real.exp (R/2):=by positivity [phiExpr.mass_nonneg]
    dsimp [K,literalCoefficientBudget];linarith [abs_nonneg (initialRegularBudget f j R B)]
  have hR : initialRegularBudget f j R B≤K := by
    have h0:=le_abs_self (initialRegularBudget f j R B)
    have h2 : 0≤f.mass*Real.exp (R/2):=mul_nonneg f.mass_nonneg (Real.exp_pos _).le
    have h3 : 0≤(1+|j| *|B|)*phiExpr.mass*Real.exp (R/2):=by positivity [phiExpr.mass_nonneg]
    dsimp [K,literalCoefficientBudget];linarith
  have hF : f.mass*Real.exp (R/2)≤K := by
    have h3 : 0≤(1+|j| *|B|)*phiExpr.mass*Real.exp (R/2):=by positivity [phiExpr.mass_nonneg]
    dsimp [K,literalCoefficientBudget];linarith [abs_nonneg (initialRegularBudget f j R B)]
  have hP : phiExpr.mass*Real.exp (R/2)≤K := by
    have h2 : 0≤f.mass*Real.exp (R/2):=mul_nonneg f.mass_nonneg (Real.exp_pos _).le
    have h3 : 0≤|j| *|B| *(phiExpr.mass*Real.exp (R/2)):=by positivity [phiExpr.mass_nonneg]
    dsimp [K,literalCoefficientBudget];nlinarith [abs_nonneg (initialRegularBudget f j R B)]
  have hJP : |j| *B*(phiExpr.mass*Real.exp (R/2))≤K := by
    have h2 : 0≤f.mass*Real.exp (R/2):=mul_nonneg f.mass_nonneg (Real.exp_pos _).le
    have h3 : 0≤phiExpr.mass*Real.exp (R/2):=by positivity [phiExpr.mass_nonneg]
    dsimp [K,literalCoefficientBudget];rw [abs_of_nonneg hB]
    nlinarith [abs_nonneg (initialRegularBudget f j R B)]
  refine ⟨h1,?_,?_,?_,?_⟩
  · intro q hq b
    simpa only [D,literalInitial] using (hreg.1 b).mono hR
  · intro q hq b
    simpa only [D,literalInitial] using hreg.2.mono hR
  · intro q hq b i k t ht
    cases b
    · exact (initialKernel_segment_value f D.H D.θ x r R ha haf i k t ht).trans hF
    · change |(-j)*(_)*initialKernel phiExpr (r i) _|≤K
      rw [abs_mul,abs_mul,abs_neg]
      exact (mul_le_mul (mul_le_mul_of_nonneg_left
        (parameter_segment_value D.H D.θ x true hc hcf i k t ht) (abs_nonneg _))
        (initialKernel_segment_value phiExpr D.H D.θ x r R ha haf i k t ht)
        (abs_nonneg _) (mul_nonneg (abs_nonneg _) hB)).trans hJP
  · intro q hq b i k t ht
    exact (initialKernel_segment_value phiExpr D.H D.θ x r R ha haf i k t ht).trans hP

lemma literalInitial_seed_bound (J : Interaction n) (j : ℝ) (f : KernelExpr)
    (z m : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ)
    (hn : 0<n) (he : vectorNorm e≤1) :
    (∑b,vectorNorm ((literalInitial J j (Real.sqrt (n:ℝ)) f z m a c r e).seed b))≤2 := by
  have hd : 0<Real.sqrt (n:ℝ):=Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hb : vectorNorm (fun i=>Real.tanh (r i)/Real.sqrt (n:ℝ))≤1 := by
    have hv:=vectorNorm_tanh r
    have hscale : (fun i=>Real.tanh (r i)/Real.sqrt (n:ℝ))=
        (Real.sqrt (n:ℝ))⁻¹ • (fun i=>Real.tanh (r i)):=by ext i;simp [div_eq_mul_inv,mul_comm]
    rw [hscale,vectorNorm_smul,abs_of_nonneg (inv_nonneg.mpr hd.le)]
    calc
      _ ≤ (Real.sqrt (n:ℝ))⁻¹*Real.sqrt (n:ℝ) := mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr hd.le)
      _ = 1 := inv_mul_cancel₀ hd.ne'
  simp only [Fintype.sum_bool,literalInitial,Bool.false_eq_true,↓reduceIte]
  change vectorNorm (fun i=>Real.tanh (r i)/Real.sqrt (n:ℝ))+vectorNorm e≤2
  linarith
end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_RecipeArgumentPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary
variable {n : ℕ} {ι κ ι₀ κ₀ : Type*}
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Fintype ι₀] [DecidableEq ι₀] [Fintype κ₀] [DecidableEq κ₀]

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq ι₀] [DecidableEq κ₀] in
lemma argumentSelect_norm (l : ι₀→ι) (p : κ₀→κ) : ‖argumentSelect l p‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr
  intro q
  exact norm_le_pi_norm u (Sum.map l p q)

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype ι₀] [DecidableEq ι₀] [Fintype κ₀] [DecidableEq κ₀] in
lemma argumentSelect_local (l : ι₀→ι) (p : κ₀→κ)
    (H : ι→VectorFields n) (θ : κ→Spin n→ℝ) (x : Spin n) (i : Fin n) :
    argumentSelect l p (localArgs H θ x i)=localArgs (H∘l) (θ∘p) x i := by
  ext q;cases q <;> rfl

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq ι₀] [DecidableEq κ₀] in
lemma SegmentRegular.argumentPullback (l : ι₀→ι) (p : κ₀→κ)
    {H : ι→VectorFields n} {θ : κ→Spin n→ℝ}
    {F : Fin n→Args (ι:=ι₀) (κ:=κ₀)→ℝ}
    {F' : Fin n→Args (ι:=ι₀) (κ:=κ₀)→Args (ι:=ι₀) (κ:=κ₀)→L[ℝ]ℝ}
    {x : Spin n} {C : ℝ} (h : SegmentRegular (H∘l) (θ∘p) F F' x C) :
    SegmentRegular H θ (fun i u=>F i (argumentSelect l p u))
      (fun i u=>(F' i (argumentSelect l p u)).comp (argumentSelect l p)) x C := by
  let P:=argumentSelect l p
  have hp : ‖P‖≤1:=argumentSelect_norm l p
  have hn (G : Args (ι:=ι₀) (κ:=κ₀)→L[ℝ]ℝ) : ‖G.comp P‖≤‖G‖ :=
    (G.opNorm_comp_le P).trans (by simpa using mul_le_mul_of_nonneg_left hp (norm_nonneg G))
  have hs (i k : Fin n) (t : ℝ) :
      P (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i))=
        localArgs (H∘l) (θ∘p) x i+t •
          (localArgs (H∘l) (θ∘p) (flip x k) i-localArgs (H∘l) (θ∘p) x i) := by
    simp [P,map_add,map_smul,map_sub,argumentSelect_local]
  refine ⟨h.nonneg,?_,?_,?_⟩
  · intro i k t ht
    have hh:=h.deriv i k t ht
    rw [←hs] at hh
    exact hh.comp
      (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i)) P.hasFDerivAt
  · intro i k t ht
    exact (hn _).trans (by rw [hs];exact h.bound i k t ht)
  · intro i k t ht
    rw [←ContinuousLinearMap.sub_comp]
    apply (hn _).trans
    rw [hs,show P (localArgs H θ x i)=localArgs (H∘l) (θ∘p) x i from argumentSelect_local l p H θ x i]
    apply (h.lip i k t ht).trans
    apply mul_le_mul_of_nonneg_left _ h.nonneg
    have hh:=P.le_opNorm (t • (localArgs H θ (flip x k) i-localArgs H θ x i))
    have hh':=hh.trans (mul_le_mul_of_nonneg_right hp (norm_nonneg _))
    simpa only [P,map_smul,map_sub,argumentSelect_local,one_mul] using hh'

namespace OrdinaryData
variable {σ : Type*} [Fintype σ]

omit [Fintype σ] in
lemma CoefficientClass.argumentPullback {D : OrdinaryData n ι₀ κ₀ σ} {N : ℕ}
    {x : Spin n} {K : ℝ} (h : D.CoefficientClass N x K)
    (l : ι₀→ι) (p : κ₀→κ) (H U : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (hH : H∘l=D.H) (hθ : θ∘p=D.θ) :
    (D.argumentPullback l p H U θ).CoefficientClass N x K := by
  refine ⟨h.one_le,?_,?_,?_,?_⟩
  · intro a ha b
    dsimp only [OrdinaryData.argumentPullback]
    apply SegmentRegular.argumentPullback l p
    simpa only [hH,hθ] using h.seedRegular a ha b
  · intro a ha b
    dsimp only [OrdinaryData.argumentPullback]
    apply SegmentRegular.argumentPullback l p
    simpa only [hH,hθ] using h.auxRegular a ha b
  · intro a ha b i k t ht
    dsimp only [OrdinaryData.argumentPullback]
    simpa only [map_add,map_smul,map_sub,argumentSelect_local,hH,hθ] using
      h.seedValue a ha b i k t ht
  · intro a ha b i k t ht
    dsimp only [OrdinaryData.argumentPullback]
    simpa only [map_add,map_smul,map_sub,argumentSelect_local,hH,hθ] using
      h.auxValue a ha b i k t ht
end OrdinaryData
end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary
variable {n : ℕ} {ι κ κ₀ σ : Type*}
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Fintype κ₀] [DecidableEq κ₀] [Fintype σ]

omit [Fintype ι] [Fintype κ] [Fintype κ₀] in
lemma argumentSelect_single_primary (l : ι) (p : κ₀→κ) (q : ι) :
    argumentSelect (fun _ : Unit=>l) p (Pi.single (.inl q) 1)=
      if q=l then (Pi.single (.inl ()) 1 : Args (ι:=Unit) (κ:=κ₀)) else 0 := by
  by_cases hq : q=l
  · subst q; ext s; cases s with
    | inl s=>cases s;simp [argumentSelect_apply]
    | inr s=>simp [argumentSelect_apply]
  · ext s; cases s with
    | inl s=>cases s;simp [argumentSelect_apply,hq,Ne.symm hq]
    | inr s=>simp [argumentSelect_apply,hq]

namespace OrdinaryData
variable (D : OrdinaryData n Unit κ₀ σ) (l : ι) (p : κ₀→κ)
variable (H U : ι→VectorFields n) (θ : κ→Spin n→ℝ)
variable (hH : H∘(fun _:Unit=>l)=D.H) (hθ : θ∘p=D.θ)
include hH hθ

omit [Fintype σ] in
lemma unitPullback_seedCoefficient (a : ℕ) (s : σ) :
    (D.argumentPullback (fun _:Unit=>l) p H U θ).seedCoefficient a s=D.seedCoefficient a s := by
  ext x i
  simp only [seedCoefficient,coefficient,argumentPullback,argumentSelect_local,hH,hθ]

omit [Fintype σ] in
lemma unitPullback_auxCoefficient (a : ℕ) (b : Fin a) :
    (D.argumentPullback (fun _:Unit=>l) p H U θ).auxCoefficient a b=D.auxCoefficient a b := by
  ext x i
  simp only [auxCoefficient,coefficient,argumentPullback,argumentSelect_local,hH,hθ]

lemma unitPullback_sourceOf (a : ℕ) (Y : Fin a→VectorFields n) :
    (D.argumentPullback (fun _:Unit=>l) p H U θ).sourceOf a Y=D.sourceOf a Y := by
  ext x i
  simp only [sourceOf,unitPullback_seedCoefficient D l p H U θ hH hθ,
    unitPullback_auxCoefficient D l p H U θ hH hθ]
  rfl

omit [Fintype σ] in
lemma unitPullback_seedPartial (a : ℕ) (q : ι) (s : σ) :
    (D.argumentPullback (fun _:Unit=>l) p H U θ).seedPartial a q s=
      if q=l then D.seedPartial a () s else 0 := by
  by_cases hq : q=l <;> ext x i <;>
    simp [seedPartial,localPartial,argumentPullback,partialAt,
      ContinuousLinearMap.comp_apply,argumentSelect_local,hH,hθ,argumentSelect_single_primary,hq]

omit [Fintype σ] in
lemma unitPullback_auxPartial (a : ℕ) (q : ι) (b : Fin a) :
    (D.argumentPullback (fun _:Unit=>l) p H U θ).auxPartial a q b=
      if q=l then D.auxPartial a () b else 0 := by
  by_cases hq : q=l <;> ext x i <;>
    simp [auxPartial,localPartial,argumentPullback,partialAt,
      ContinuousLinearMap.comp_apply,argumentSelect_local,hH,hθ,argumentSelect_single_primary,hq]

lemma unitPullback_partialOf (a : ℕ) (q : ι) (Y : Fin a→VectorFields n) :
    (D.argumentPullback (fun _:Unit=>l) p H U θ).partialOf a q Y=
      if q=l then D.partialOf a () Y else 0 := by
  ext x i
  simp only [partialOf,unitPullback_seedPartial D l p H U θ hH hθ,
    unitPullback_auxPartial D l p H U θ hH hθ]
  by_cases hq : q=l <;> simp [hq,argumentPullback,partialOf]

lemma unitPullback_fieldOf (hU : U l=D.predecessor ()) (a : ℕ) (W Y : Fin a→VectorFields n) :
    (D.argumentPullback (fun _:Unit=>l) p H U θ).fieldOf a W Y=D.fieldOf a W Y := by
  ext x i
  simp only [fieldOf,unitPullback_sourceOf D l p H U θ hH hθ,
    unitPullback_partialOf D l p H U θ hH hθ,
    unitPullback_auxCoefficient D l p H U θ hH hθ]
  have hm (q : ι) : siteMean (if q=l then D.partialOf a () Y else 0) x*U q x i=
      if q=l then siteMean (D.partialOf a () Y) x*U l x i else 0 := by
    split_ifs with hq
    · subst q;rfl
    · simp [siteMean]
  simp only [argumentPullback,hm,Finset.sum_ite_eq',Finset.mem_univ,ite_true,hU,Fintype.sum_unique]

lemma unitPullback_started_duplicate (hU : U l=D.predecessor ()) (w y : VectorFields n)
    (x : Spin n) (hw : w x=D.sourceOf 1 (fun _=>y) x)
    (hy : y x=D.fieldOf 1 (fun _=>w) (fun _=>y) x) :
    (D.argumentPullback (fun _:Unit=>l) p H U θ).startedSource w y 1 x=w x ∧
      (D.argumentPullback (fun _:Unit=>l) p H U θ).startedAuxiliary w y 1 x=y x := by
  rw [startedSource_one,startedAuxiliary_one,unitPullback_sourceOf D l p H U θ hH hθ,
    unitPullback_fieldOf D l p H U θ hH hθ hU]
  exact ⟨hw.symm,hy.symm⟩
end OrdinaryData
end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_FiniteStartedControlGeneral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary SKGap.Stein Static

variable {n M : ℕ}

lemma literalFullData_admissible (j : ℝ) (J : Interaction n) (h : Fin n→ℝ)
    (l : Fin M) (f : KernelExpr) (a c : Spin n→ℝ) (r e : Fin n→ℝ)
    (N p : ℕ) (hp : p≤l.val) : (literalFullData j J h l f a c r e).Admissible N p := by
  intro b hb q hq
  have hne : q≠l := by intro he;subst q;omega
  dsimp only [literalFullData]
  constructor
  · intro s
    rw [OrdinaryData.unitPullback_seedPartial
      (literalInitial J j (Real.sqrt (n:ℝ)) f (fld j J h l.val) (mag j J h l.val) a c r e)
      l Sum.inr (fun q : Fin M=>fld j J h q.val) (fun q : Fin M=>mag j J h q.val)
      (literalFullParameters j J h a c) rfl rfl]
    simp only [ite_eq_right hne]
  · intro s
    rw [OrdinaryData.unitPullback_auxPartial
      (literalInitial J j (Real.sqrt (n:ℝ)) f (fld j J h l.val) (mag j J h l.val) a c r e)
      l Sum.inr (fun q : Fin M=>fld j J h q.val) (fun q : Fin M=>mag j J h q.val)
      (literalFullParameters j J h a c) rfl rfl]
    simp only [ite_eq_right hne]

lemma literalFullData_coefficientClass (j : ℝ) (J : Interaction n) (h : Fin n→ℝ)
    (l : Fin M) (f : KernelExpr) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (x : Spin n)
    {R B : ℝ} (hB : 0≤B) (ha : |a x|≤R) (haf : ∀k,|a (flip x k)|≤R)
    (hc : |Real.sqrt (n:ℝ)*c x|≤B) (hcf : ∀k,|Real.sqrt (n:ℝ)*c (flip x k)|≤B) (N : ℕ) :
    (literalFullData j J h l f a c r e).CoefficientClass N x (literalCoefficientBudget f j R B) := by
  exact (literalInitial_coefficientClass J j (Real.sqrt (n:ℝ)) f
    (fld j J h l.val) (mag j J h l.val) a c r e x hB ha haf hc hcf N).argumentPullback (fun _:Unit=>l) Sum.inr _ _ _ rfl rfl

lemma literalFullData_initial (j : ℝ) (J : Interaction n) (h : Fin n→ℝ)
    (l : Fin M) (f : KernelExpr) (a c : Spin n→ℝ) (r e : Fin n→ℝ)
    (w y : VectorFields n) (hn : 0<n) (x : Spin n)
    (heq : LiteralEquations J j f (fld j J h l.val) (mag j J h l.val) w y a c r e x) :
    (literalFullData j J h l f a c r e).startedSource w y 1 x=w x ∧
      (literalFullData j J h l f a c r e).startedAuxiliary w y 1 x=y x := by
  have hd : Real.sqrt (n:ℝ)≠0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  have hh:=(literalEquations_recipe J j (Real.sqrt (n:ℝ)) f (fld j J h l.val)
    (mag j J h l.val) w y a c r e hd x).mp heq
  exact OrdinaryData.unitPullback_started_duplicate _ l Sum.inr _ _ _ rfl rfl rfl w y x hh.1 hh.2.1

universe u
variable {Ω : Type u} {n : Ω→ℕ}

theorem literal_full_local_family_s2_oai (j : ℝ) (J : ∀b,Interaction (n b))
    (h : ∀b,Fin (n b)→ℝ) (l : Fin M) (f : KernelExpr)
    (a c : ∀b,Spin (n b)→ℝ) (r e : ∀b,Fin (n b)→ℝ)
    (w y : ∀b,VectorFields (n b)) (E : ∀b,Set (Spin (n b)))
    (hn : ∀b,0<n b) (he : ∀b,vectorNorm (e b)≤1)
    {R B : ℝ} (hB : 0≤B)
    (ha : ∀b x,x∈flipNeighborhood (flipNeighborhood (E b))→|a b x|≤R)
    (hc : ∀b x,x∈flipNeighborhood (flipNeighborhood (E b))→|Real.sqrt (n b:ℝ)*c b x|≤B)
    (heq : ∀b x,x∈E b→LiteralEquations (J b) j f (fld j (J b) (h b) l.val)
      (mag j (J b) (h b) l.val) (w b) (y b) (a b) (c b) (r b) (e b) x) :
    LocalFamilyRecipe E j J h (fun b=>literalFullParameters j (J b) (h b) (a b) (c b)) w y
      (fun b=>literalFullData j (J b) (h b) l f (a b) (c b) (r b) (e b)) 1 l.val
      (literalCoefficientBudget f j R B) := by
  refine ⟨le_rfl,fun _=>rfl,fun _=>rfl,fun _ _=>rfl,fun _ _=>rfl,fun _=>rfl,?_,?_,?_,?_⟩
  · refine ⟨2,by norm_num,fun b=>?_⟩
    exact literalInitial_seed_bound (J b) j f (fld j (J b) (h b) l.val)
      (mag j (J b) (h b) l.val) (a b) (c b) (r b) (e b) (hn b) (he b)
  · intro b x hx
    apply literalFullData_coefficientClass j (J b) (h b) l f (a b) (c b) (r b) (e b) x hB
    · exact ha b x (Or.inl hx)
    · intro k;exact ha b (flip x k) (Or.inr ⟨k,by simpa only [flip_flip] using hx⟩)
    · exact hc b x (Or.inl hx)
    · intro k;exact hc b (flip x k) (Or.inr ⟨k,by simpa only [flip_flip] using hx⟩)
  · intro b;exact literalFullData_admissible j (J b) (h b) l f (a b) (c b) (r b) (e b) 1 l.val le_rfl
  · intro b x hx;exact literalFullData_initial j (J b) (h b) l f (a b) (c b) (r b) (e b)
      (w b) (y b) (hn b) x (heq b x hx)

end SKGapCutoff.Recipe

end
end

end OAI
end

theorem solution.{u} : type_of% @OAI.SKGapCutoff.Recipe.literal_full_local_family_s2_oai.{u} := @OAI.SKGapCutoff.Recipe.literal_full_local_family_s2_oai.{u}
