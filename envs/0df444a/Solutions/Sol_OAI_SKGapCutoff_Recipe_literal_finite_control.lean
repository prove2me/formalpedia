-- Prove2me | solution 1 for OAI.SKGapCutoff.Recipe.literal_finite_control
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:07:42.465778+00:00
-- url     : https://prove2.me/submissions/70fbcd46-a5da-4012-b900-0d537f6cd11e

import Mathlib
import Definitions.Def_OAIQ072A002
import Theorems.Thm_OAI_SKGapCutoff_Recipe_finite_started_control_seeds

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_PhiStein
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
-- module Solutions.OAIQ072_SK.SKGap_Terminal_Spin
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped BigOperators

namespace SKGapCutoff

theorem halfDiff_mul {n : ℕ} (i : Fin n) (f g : Spin n → ℝ) (x : Spin n) :
    halfDiff i (fun y => f y * g y) x =
      f x * halfDiff i g x + g x * halfDiff i f x -
        2 * spin x i * halfDiff i f x * halfDiff i g x := by
  have hx : replace x i (x i) = x := replace_self x i
  cases h : x i <;> simp only [h] at hx
  · simp only [halfDiff, spin, h, Bool.false_eq_true, ↓reduceIte]
    rw [hx]
    ring
  · simp only [halfDiff, spin, h, ↓reduceIte]
    rw [hx]
    ring

theorem halfDiff_sub {n : ℕ} (i : Fin n) (f g : Spin n → ℝ) (x : Spin n) :
    halfDiff i (fun y => f y - g y) x = halfDiff i f x - halfDiff i g x := by
  simp only [halfDiff]
  ring

end SKGapCutoff
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_GibbsExpectation
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
namespace SKGapCutoff
open Filter Topology

lemma flip_sub {n : ℕ} (i : Fin n) (f : Observables n) (x : Spin n) :
    f (flip x i) - f x = -2 * spin x i * halfDiff i f x := by
  have hx := replace_self x i
  cases hi : x i <;> simp only [hi] at hx
  · simp only [flip, hi, Bool.not_false, spin, Bool.false_eq_true, ↓reduceIte, halfDiff]
    rw [hx]; ring
  · simp only [flip, hi, Bool.not_true, spin, ↓reduceIte, halfDiff]
    rw [hx]; ring

end SKGapCutoff

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ScalarVariance
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

lemma scalarVariance_lipschitz (x y : ℝ) : |scalarVariance y - scalarVariance x| ≤ 2*|y-x| := by
  have h1 := tanh_lipschitz x y
  have h2 : |Real.tanh y + Real.tanh x| ≤ 2 :=
    (abs_add_le _ _).trans (by linarith [Real.abs_tanh_lt_one x, Real.abs_tanh_lt_one y])
  have he : scalarVariance y - scalarVariance x =
      -(Real.tanh y - Real.tanh x) * (Real.tanh y + Real.tanh x) := by
    unfold scalarVariance
    ring
  rw [he, abs_mul, abs_neg]
  nlinarith [mul_le_mul h1 h2 (abs_nonneg _) (abs_nonneg _)]

lemma tanh_linear_remainder (x y : ℝ) :
    |Real.tanh y - Real.tanh x - scalarVariance x * (y-x)| ≤ 2 * |y-x| ^ 2 := by
  let f (z : ℝ) := Real.tanh z - Real.tanh x - scalarVariance x * (z-x)
  have hd (z : ℝ) : HasDerivAt f (scalarVariance z - scalarVariance x) z := by
    convert! ((tanh_hasDerivAt z).sub_const (Real.tanh x)).sub
      (((hasDerivAt_id z).sub_const x).const_mul (scalarVariance x)) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [mul_one]
  have hb (z : ℝ) (hz : z ∈ segment ℝ x y) : ‖scalarVariance z - scalarVariance x‖ ≤
      2 * |y-x| := by
    have hh : |z-x| ≤ |y-x| := by simpa only [Real.norm_eq_abs] using norm_sub_le_of_mem_segment hz
    simpa only [Real.norm_eq_abs] using (scalarVariance_lipschitz x z).trans
      (mul_le_mul_of_nonneg_left hh (by norm_num))
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ segment ℝ x y) => (hd z).hasDerivWithinAt) hb
    (convex_segment x y) (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa only [f, sub_self, mul_zero, sub_zero, Real.norm_eq_abs, pow_two, mul_assoc] using h

lemma halfDiff_as_flip {n : ℕ} (f : Observables n) (x : Spin n) (i : Fin n) :
    halfDiff i f x = spin x i * (f x - f (flip x i)) / 2 := by
  have hx := replace_self x i
  cases hi : x i <;> simp only [hi] at hx
  · simp only [spin, hi, Bool.false_eq_true, ↓reduceIte, flip, Bool.not_false, halfDiff]
    rw [hx]; ring
  · simp only [spin, hi, ↓reduceIte, flip, Bool.not_true, halfDiff]
    rw [hx]; ring

lemma abs_spin_eq_one {n : ℕ} (x : Spin n) (i : Fin n) : |spin x i| = 1 := by
  cases hi : x i <;> simp [spin, hi]

end SKGapCutoff

open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_PhiBounds
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
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_PhiMoments
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
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_SquaredGaussianFourth
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
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
namespace SKGapCutoff.RandomMatrix

lemma matrix_opNorm_sq_le_frobenius {n : ℕ} (A : Interaction n) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖^2 ≤ ∑ i, ∑ j, A i j^2 := by
  let S := ∑ i, ∑ j, A i j^2
  have hS : 0 ≤ S := by unfold S; positivity
  have hN : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖ ≤ Real.sqrt S := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro x
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ Real.sqrt S * ‖x‖)).mp
    rw [mul_pow, Real.sq_sqrt hS]
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    change ∑ i, (∑ j, A i j*x j)^2 ≤ S * ∑ j, x j^2
    calc
      _ ≤ ∑ i, (∑ j, A i j^2)*(∑ j, x j^2) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (A i) x)
      _ = _ := by rw [← Finset.sum_mul]
  exact (pow_le_pow_left₀ (norm_nonneg _) hN 2).trans_eq (Real.sq_sqrt hS)

end SKGapCutoff.RandomMatrix

open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_PhiAlgebra
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
-- module Solutions.OAIQ072_SK.SKGap_Localization_PhiFrechet
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
-- module Solutions.OAIQ072_SK.SKGap_Localization_Taylor
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
-- module Solutions.OAIQ072_SK.SKGap_Localization_PreparationGrowth
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
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise NNReal ENNReal
open scoped BigOperators
open Filter Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory ContinuousLinearMap
open scoped Topology NNReal ENNReal
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter
open scoped BigOperators Topology
open Filter Set Metric
open scoped Topology RealInnerProductSpace
open scoped BigOperators
open ContinuousLinearMap
open scoped BigOperators
open ContinuousLinearMap
namespace SKGapCutoff

lemma refreshField_flip {n : ℕ} (H : VectorFields n) (x : Spin n) (i j : Fin n) :
    H (flip x i) j = H x j - 2*spin x i*halfDiff i (fun y => H y j) x := by
  have h := flip_sub i (fun y => H y j) x
  linarith

lemma refreshField_abs_change {n : ℕ} (H : VectorFields n) (x : Spin n) (i j : Fin n) :
    |H x j-H (flip x i) j| = 2*|halfDiff i (fun y => H y j) x| := by
  rw [refreshField_flip H x i j]
  ring_nf
  simp [abs_mul, abs_spin_eq_one, mul_comm]

lemma refreshInfluence_error_le {n : ℕ} (H : VectorFields n) (x : Spin n) (i j : Fin n) :
    |refreshInfluence (fun y k => Real.tanh (H y k)) x i j -
      halfDiff i (fun y => H y j) x*scalarVariance (H x j)| ≤
        4*(halfDiff i (fun y => H y j) x)^2 := by
  have hr := tanh_linear_remainder (H x j) (H (flip x i) j)
  have he : refreshInfluence (fun y k => Real.tanh (H y k)) x i j -
      halfDiff i (fun y => H y j) x*scalarVariance (H x j) =
      -(spin x i/2)*(Real.tanh (H (flip x i) j)-Real.tanh (H x j)-
        scalarVariance (H x j)*(H (flip x i) j-H x j)) := by
    simp only [refreshInfluence, halfDiff_as_flip]
    ring
  rw [he, abs_mul, abs_neg, abs_div, abs_spin_eq_one]
  norm_num only [abs_of_pos (show (0:ℝ)<2 by norm_num)]
  have ha : |H (flip x i) j-H x j| = 2*|halfDiff i (fun y => H y j) x| := by
    rw [abs_sub_comm, refreshField_abs_change]
  rw [ha] at hr
  nlinarith [sq_abs (halfDiff i (fun y => H y j) x)]

open RandomMatrix

end SKGapCutoff
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_OpNorm
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma opNorm_mul (M N : Matrix ι ι ℝ) : opNorm (M*N) ≤ opNorm M*opNorm N := by
  have he : (M*N).toEuclideanLin.toContinuousLinearMap =
      M.toEuclideanLin.toContinuousLinearMap * N.toEuclideanLin.toContinuousLinearMap := by
    ext x i
    exact congrFun (congrArg (fun T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι => (T x).ofLp)
      (Matrix.toLpLin_mul 2 2 2 M N)) i
  exact (congrArg norm he).le.trans (norm_mul_le _ _)

end SKGap

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_FrobeniusSq
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
namespace SKGap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma frobenius_col_sq (M : Matrix ι ι ℝ) : ‖M‖^2 = ∑ k, ‖colVec M k‖^2 := by
  rw [frobenius_sq,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [EuclideanSpace.norm_sq_eq]
  simp [colVec,Real.norm_eq_abs,sq_abs]

lemma colVec_mul (M N : Matrix ι ι ℝ) (k : ι) :
    colVec (M*N) k = M.toEuclideanLin.toContinuousLinearMap (colVec N k) := by
  ext i
  rfl

lemma frobenius_mul_le_opNorm (M N : Matrix ι ι ℝ) : ‖M*N‖ ≤ opNorm M * ‖N‖ := by
  have hp : 0 ≤ opNorm M := norm_nonneg _
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hp (norm_nonneg N))
  simp only [← sq]
  rw [frobenius_col_sq,mul_pow,frobenius_col_sq,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  rw [colVec_mul]
  have hh := M.toEuclideanLin.toContinuousLinearMap.le_opNorm (colVec N k)
  change ‖M.toEuclideanLin.toContinuousLinearMap (colVec N k)‖ ≤ opNorm M * ‖colVec N k‖ at hh
  nlinarith only [hh, norm_nonneg (M.toEuclideanLin.toContinuousLinearMap (colVec N k)),
    mul_nonneg hp (norm_nonneg (colVec N k))]

lemma opNorm_transpose (M : Matrix ι ι ℝ) : opNorm Mᵀ = opNorm M := by
  change ‖Mᵀ.toEuclideanLin.toContinuousLinearMap‖ = ‖M.toEuclideanLin.toContinuousLinearMap‖
  have he : Mᵀ.toEuclideanLin.toContinuousLinearMap =
      ContinuousLinearMap.adjoint M.toEuclideanLin.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℝ
    intro y
    rw [ContinuousLinearMap.adjoint_inner_right]
    change (∑ i, (∑ k, M k i*x k)*y i) = ∑ i, x i * (∑ k, M i k*y k)
    simp only [Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he,ContinuousLinearMap.adjoint.norm_map]

end SKGap

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_MatrixSeminorm
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance instFactLeENNRealOfNat_solutions : Fact (1≤(4:ENNReal)) := ⟨by norm_num⟩

omit [DecidableEq ι] in
lemma diagonalSeminorm_sq (M : Matrix ι ι ℝ) : diagonalSeminorm M^2=∑ i,(M i i)^2 := by
  simp only [diagonalSeminorm,EuclideanSpace.norm_sq_eq,diagonalVector,Real.norm_eq_abs,sq_abs]

lemma offDiagonalSeminorm_fourth (M : Matrix ι ι ℝ) :
    offDiagonalSeminorm M^4=∑ p : ι×ι,if p.1=p.2 then 0 else (M p.1 p.2)^4 := by
  rw [offDiagonalSeminorm,PiLp.norm_eq_of_nat (p:=4) 4 (by norm_num)]
  rw [←Real.rpow_natCast,←Real.rpow_mul (Finset.sum_nonneg (fun _ _=>pow_nonneg (norm_nonneg _) _))]
  norm_num only [Nat.cast_ofNat,one_div,mul_inv_cancel₀ (by norm_num : (4:ℝ)≠0),Real.rpow_one]
  apply Finset.sum_congr rfl
  intro p _
  simp only [offDiagonalVector,WithLp.ofLp_toLp]
  split_ifs
  · simp
  · rw [Real.norm_eq_abs]
    calc
      |M p.1 p.2|^4=(|M p.1 p.2|^2)^2 := by ring
      _ = ((M p.1 p.2)^2)^2 := by rw [sq_abs]
      _ = (M p.1 p.2)^4 := by ring

lemma diagonalSeminorm_le (M : Matrix ι ι ℝ) : diagonalSeminorm M≤‖M‖ := by
  apply le_of_pow_le_pow_left₀ (by decide : 2≠0) (norm_nonneg _)
  rw [diagonalSeminorm_sq,frobenius_sq]
  exact Finset.sum_le_sum (fun i _=>Finset.single_le_sum (fun k _=>sq_nonneg (M i k)) (Finset.mem_univ i))

lemma offDiagonalSeminorm_le (M : Matrix ι ι ℝ) : offDiagonalSeminorm M≤‖M‖ := by
  let a : ι×ι→ℝ := fun p=>if p.1=p.2 then 0 else (M p.1 p.2)^2
  have ha : ∀ p,0≤a p := by intro p;dsimp [a];split_ifs <;> positivity
  have hs : (∑ p,a p)≤‖M‖^2 := by
    rw [frobenius_sq]
    rw [show (∑ i,∑ k,(M i k)^2) = ∑ p : ι×ι,(M p.1 p.2)^2 from (Fintype.sum_prod_type fun p : ι×ι=>(M p.1 p.2)^2).symm]
    apply Finset.sum_le_sum
    intro p _
    dsimp [a]
    split_ifs
    · exact sq_nonneg _
    · exact le_rfl
  apply le_of_pow_le_pow_left₀ (by decide : 4≠0) (norm_nonneg _)
  rw [offDiagonalSeminorm_fourth]
  calc
    _ = ∑ p,a p^2 := by
      apply Finset.sum_congr rfl
      intro p _
      dsimp [a]
      split_ifs <;> ring
    _ ≤ (∑ p,a p)^2 := Finset.sum_sq_le_sq_sum_of_nonneg (fun p _=>ha p)
    _ ≤ (‖M‖^2)^2 := pow_le_pow_left₀ (Finset.sum_nonneg (fun p _=>ha p)) hs 2
    _ = ‖M‖^4 := by ring

omit [DecidableEq ι] in
lemma diagonalSeminorm_add (M N : Matrix ι ι ℝ) :
    diagonalSeminorm (M+N)≤diagonalSeminorm M+diagonalSeminorm N := by
  simpa only [diagonalSeminorm,diagonalVector_add] using norm_add_le (diagonalVector M) (diagonalVector N)
lemma offDiagonalSeminorm_add (M N : Matrix ι ι ℝ) :
    offDiagonalSeminorm (M+N)≤offDiagonalSeminorm M+offDiagonalSeminorm N := by
  simpa only [offDiagonalSeminorm,offDiagonalVector_add] using norm_add_le (offDiagonalVector M) (offDiagonalVector N)
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_OpNormDiagonal
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open Real
noncomputable section
open scoped BigOperators Topology
open Filter Real
namespace SKGap
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma opNorm_diagonal_eq (d : ι → ℝ) : opNorm (diagonal d) = ‖d‖ :=
  Matrix.l2_opNorm_diagonal d

lemma opNorm_diagonal_le {d : ι → ℝ} {C : ℝ} (hC : 0 ≤ C) (hd : ∀ i, |d i| ≤ C) :
    opNorm (diagonal d) ≤ C := by
  rw [opNorm_diagonal_eq]
  exact (pi_norm_le_iff_of_nonneg hC).mpr (fun i => by simpa only [Real.norm_eq_abs] using hd i)

lemma opNorm_one_le : opNorm (1 : Matrix ι ι ℝ) ≤ 1 := by
  change ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (1 : Matrix ι ι ℝ)‖ ≤ _
  rw [map_one]
  exact ContinuousLinearMap.norm_id_le

end SKGap

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_DiscreteMatrixCalculus
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Primary
open SKGap Matrix
variable {n : ℕ}
local instance instFactLeENNRealOfNat_solutions : Fact (1≤(4:ENNReal)) := ⟨by norm_num⟩

lemma opNorm_eq (M : Interaction n) :
    SKGap.opNorm M = ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M‖ := rfl

lemma opNorm_le_frobenius (M : Interaction n) : SKGap.opNorm M ≤ ‖M‖ := by
  apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg M)
  simp only [← sq]
  rw [SKGap.frobenius_sq,opNorm_eq]
  exact RandomMatrix.matrix_opNorm_sq_le_frobenius M

lemma opNorm_add (M N : Interaction n) : SKGap.opNorm (M+N) ≤ SKGap.opNorm M+SKGap.opNorm N := by
  simp only [opNorm_eq,map_add]
  exact norm_add_le _ _

lemma opNorm_smul (c : ℝ) (M : Interaction n) : SKGap.opNorm (c • M) = |c| * SKGap.opNorm M := by
  simp only [opNorm_eq,map_smul,norm_smul,Real.norm_eq_abs]

lemma ShapeBound.mono {M : Interaction n} {C D : ℝ} (h : ShapeBound M C) (hCD : C≤D) :
    ShapeBound M D := ⟨h.1.trans hCD,h.2.1.trans hCD,h.2.2.trans hCD⟩

lemma ShapeBound.add {M N : Interaction n} {C D : ℝ}
    (hM : ShapeBound M C) (hN : ShapeBound N D) : ShapeBound (M+N) (C+D) := by
  exact ⟨(opNorm_add M N).trans (add_le_add hM.1 hN.1),
    (SKGap.diagonalSeminorm_add M N).trans (add_le_add hM.2.1 hN.2.1),
    (SKGap.offDiagonalSeminorm_add M N).trans (add_le_add hM.2.2 hN.2.2)⟩

lemma shapeBound_of_frobenius {M : Interaction n} {C : ℝ} (h : ‖M‖≤C) : ShapeBound M C :=
  ⟨(opNorm_le_frobenius M).trans h,(SKGap.diagonalSeminorm_le M).trans h,
    (SKGap.offDiagonalSeminorm_le M).trans h⟩

lemma ShapeBound.perturb {M H : Interaction n} {C E : ℝ}
    (hH : ShapeBound H C) (hE : ‖M-H‖≤E) : ShapeBound M (C+E) := by
  simpa only [add_sub_cancel] using hH.add (shapeBound_of_frobenius hE)

lemma fourth_sum (M : Interaction n) :
    (∑ i,∑ k,(M i k)^4) = (∑ i,(M i i)^4)+SKGap.offDiagonalSeminorm M^4 := by
  rw [SKGap.offDiagonalSeminorm_fourth,Fintype.sum_prod_type,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hs : (M i i)^4 = ∑ k : Fin n, if i=k then (M i k)^4 else 0 := by simp
  rw [hs,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : i=k <;> simp [h]

lemma fourth_sum_le {M : Interaction n} {C : ℝ} (hC : 0≤C) (hM : ShapeBound M C) :
    (∑ i,∑ k,(M i k)^4) ≤ 2*C^4 := by
  rw [fourth_sum]
  have hd : (∑ i,(M i i)^4) ≤ SKGap.diagonalSeminorm M^4 := by
    rw [show (4:ℕ)=2*2 by rfl,pow_mul,SKGap.diagonalSeminorm_sq]
    simpa only [pow_mul] using
      (Finset.sum_sq_le_sq_sum_of_nonneg (s:=Finset.univ) (f:=fun i => (M i i)^2)
        (fun i _ => sq_nonneg _))
  have hdC := (pow_le_pow_iff_left₀ (norm_nonneg (SKGap.diagonalVector M)) hC
    (by decide : 4 ≠ 0)).2 hM.2.1
  have hoC := pow_le_pow_left₀ (norm_nonneg (SKGap.offDiagonalVector M)) hM.2.2 4
  dsimp only [SKGap.diagonalSeminorm,SKGap.offDiagonalSeminorm] at hd ⊢
  nlinarith

lemma quadratic_entry_error {D R : Interaction n} {C A : ℝ} (hC : 0≤C) (hA : 0≤A)
    (hD : ShapeBound D C) (he : ∀ i k, |R i k|≤A*(D i k)^2) :
    ‖R‖ ≤ 2*A*C^2 := by
  have hs : ‖R‖^2 ≤ A^2*(2*C^4) := by
    rw [SKGap.frobenius_sq]
    calc
      _ ≤ ∑ i,∑ k,A^2*(D i k)^4 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro k _
        have h := pow_le_pow_left₀ (abs_nonneg (R i k)) (he i k) 2
        nlinarith only [h,sq_abs (R i k)]
      _ = A^2*(∑ i,∑ k,(D i k)^4) := by simp_rw [← Finset.mul_sum]
      _ ≤ A^2*(2*C^4) := mul_le_mul_of_nonneg_left (fourth_sum_le hC hD) (sq_nonneg _)
  have hp : 0≤2*A*C^2 := by positivity
  nlinarith [sq_nonneg (A*C^2)]

lemma diagonal_mul_shape {M : Interaction n} {C : ℝ} {a : Fin n→ℝ}
    (ha : ∀ i,|a i|≤1) (hM : ShapeBound M C) :
    ShapeBound (Matrix.diagonal a*M) C := by
  have haN : SKGap.opNorm (Matrix.diagonal a)≤1 := SKGap.opNorm_diagonal_le (by norm_num) ha
  refine ⟨(SKGap.opNorm_mul _ _).trans ?_,?_,?_⟩
  · calc
      _ ≤ 1*SKGap.opNorm M := mul_le_mul_of_nonneg_right haN (norm_nonneg _)
      _ = SKGap.opNorm M := one_mul _
      _ ≤ C := hM.1
  · apply le_trans ?_ hM.2.1
    apply le_of_pow_le_pow_left₀ (by decide : 2≠0) (norm_nonneg _)
    change SKGap.diagonalSeminorm _ ^2 ≤ SKGap.diagonalSeminorm M ^2
    simp only [SKGap.diagonalSeminorm_sq,Matrix.diagonal_mul]
    apply Finset.sum_le_sum
    intro i _
    have hi := pow_le_pow_left₀ (abs_nonneg (a i)) (ha i) 2
    simp only [sq_abs,one_pow] at hi
    simpa only [mul_pow,one_mul] using mul_le_mul_of_nonneg_right hi (sq_nonneg (M i i))
  · apply le_trans ?_ hM.2.2
    apply le_of_pow_le_pow_left₀ (by decide : 4≠0) (norm_nonneg _)
    change SKGap.offDiagonalSeminorm _ ^4 ≤ SKGap.offDiagonalSeminorm M ^4
    simp only [SKGap.offDiagonalSeminorm_fourth]
    apply Finset.sum_le_sum
    intro p _
    split_ifs
    · exact le_rfl
    · simp only [Matrix.diagonal_mul,mul_pow]
      have hi := pow_le_pow_left₀ (abs_nonneg (a p.1)) (ha p.1) 4
      rw [← abs_pow,abs_of_nonneg (by positivity : 0≤a p.1^4)] at hi
      simpa only [one_pow,one_mul] using mul_le_mul_of_nonneg_right hi
        (by positivity : 0≤(M p.1 p.2)^4)

lemma tanh_derivative_error {F : VectorFields n} {x : Spin n} {C : ℝ}
    (hC : 0≤C) (hD : ShapeBound (derivativeMatrix F x) C) :
    ‖derivativeMatrix (fun y i => Real.tanh (F y i)) x-
      Matrix.diagonal (fun i => scalarVariance (F x i))*derivativeMatrix F x‖ ≤ 8*C^2 := by
  convert quadratic_entry_error hC (by norm_num : (0:ℝ)≤4) hD ?_ using 1 <;> try norm_num
  intro i k
  simpa only [derivativeMatrix,Matrix.sub_apply,Matrix.diagonal_mul,mul_comm,
    refreshInfluence] using refreshInfluence_error_le F x k i

lemma tanh_derivative_shape {F : VectorFields n} {x : Spin n} {C : ℝ}
    (hC : 0≤C) (hD : ShapeBound (derivativeMatrix F x) C) :
    ShapeBound (derivativeMatrix (fun y i => Real.tanh (F y i)) x) (C+8*C^2) := by
  apply ShapeBound.perturb _ (tanh_derivative_error hC hD)
  apply diagonal_mul_shape ?_ hD
  intro i
  rw [abs_of_pos (scalarVariance_pos _)]
  exact scalarVariance_le_one _

lemma siteMean_derivative (F : VectorFields n) (x : Spin n) :
    derivativeVector (siteMean F) x = (n:ℝ)⁻¹ •
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) ((derivativeMatrix F x)ᵀ))
        (WithLp.toLp 2 (fun _ => 1)) := by
  ext k
  change halfDiff k (siteMean F) x = (n:ℝ)⁻¹*(∑ i,halfDiff k (fun y => F y i) x*1)
  simp only [mul_one,halfDiff,siteMean]
  rw [← Finset.sum_div,Finset.sum_sub_distrib]
  ring

lemma euclidean_ones_norm_sq :
    ‖(WithLp.toLp 2 (fun _ : Fin n => (1:ℝ)) : EuclideanSpace ℝ (Fin n))‖^2 = n := by
  simp [EuclideanSpace.real_norm_sq_eq]

lemma siteMean_derivative_square (F : VectorFields n) (x : Spin n) (hn : 0<n) :
    (n:ℝ)*‖derivativeVector (siteMean F) x‖^2 ≤ SKGap.opNorm (derivativeMatrix F x)^2 := by
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have h := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) ((derivativeMatrix F x)ᵀ)).le_opNorm
    (WithLp.toLp 2 (fun _ : Fin n => (1:ℝ)))
  change ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) ((derivativeMatrix F x)ᵀ))
    (WithLp.toLp 2 (fun _ : Fin n => (1:ℝ)))‖ ≤
    SKGap.opNorm ((derivativeMatrix F x)ᵀ) * ‖(WithLp.toLp 2 (fun _ : Fin n => (1:ℝ)) : EuclideanSpace ℝ (Fin n))‖ at h
  rw [SKGap.opNorm_transpose] at h
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow,euclidean_ones_norm_sq] at hs
  rw [siteMean_derivative,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hnR,mul_pow]
  field_simp
  nlinarith

lemma siteMean_derivative_square_bound {F : VectorFields n} {x : Spin n} {B : ℝ}
    (hn : 0<n) (hB : SKGap.opNorm (derivativeMatrix F x)≤B) :
    (n:ℝ)*‖derivativeVector (siteMean F) x‖^2 ≤ B^2 :=
  (siteMean_derivative_square F x hn).trans
    (pow_le_pow_left₀ (norm_nonneg _) hB 2)

lemma derivative_norm_of_mean_square {f : Spin n→ℝ} {x : Spin n} {B : ℝ}
    (hn : 0<n) (hB : 0≤B) (h : (n:ℝ)*‖derivativeVector f x‖^2≤B^2) :
    ‖derivativeVector f x‖≤B := by
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  nlinarith [sq_nonneg ‖derivativeVector f x‖,norm_nonneg (derivativeVector f x)]

lemma outer_frobenius_bound {v : Fin n→ℝ} {f : Spin n→ℝ} {x : Spin n} {B : ℝ}
    (hv : ∀ i,|v i|≤1) (hB : 0≤B)
    (h : (n:ℝ)*‖derivativeVector f x‖^2≤B^2) :
    ‖Matrix.of (fun i k => v i*halfDiff k f x)‖≤B := by
  apply nonneg_le_nonneg_of_sq_le_sq hB
  simp only [← sq]
  rw [SKGap.frobenius_sq]
  calc
    _ ≤ ∑ _i : Fin n,∑ k,(halfDiff k f x)^2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro k _
      have hi := pow_le_pow_left₀ (abs_nonneg (v i)) (hv i) 2
      simp only [sq_abs,one_pow] at hi
      change (v i*halfDiff k f x)^2 ≤ _
      rw [mul_pow]
      nlinarith [sq_nonneg (halfDiff k f x)]
    _ = (n:ℝ)*‖derivativeVector f x‖^2 := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        EuclideanSpace.real_norm_sq_eq,derivativeVector]
    _ ≤ B^2 := h

lemma spin_diagonal_frobenius (f : Spin n→ℝ) (x : Spin n) :
    ‖Matrix.diagonal (fun k => spin x k*halfDiff k f x)‖ = ‖derivativeVector f x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [SKGap.frobenius_sq,EuclideanSpace.real_norm_sq_eq]
  simp [Matrix.diagonal_apply,derivativeVector,mul_pow,spin_sq]

lemma derivativeMatrix_product (f : Spin n→ℝ) (F : VectorFields n) (x : Spin n) :
    derivativeMatrix (fun y i => f y*F y i) x = f x • derivativeMatrix F x +
      Matrix.of (fun i k => F x i*halfDiff k f x) -
      (2:ℝ) • (derivativeMatrix F x*Matrix.diagonal (fun k => spin x k*halfDiff k f x)) := by
  ext i k
  simp only [derivativeMatrix,Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,
    smul_eq_mul,Matrix.mul_diagonal,halfDiff_mul,Matrix.of_apply]
  ring

lemma product_derivative_error {f : Spin n→ℝ} {F : VectorFields n} {x : Spin n} {B C : ℝ}
    (hn : 0<n) (hB : 0≤B) (hC : SKGap.opNorm (derivativeMatrix F x)≤C)
    (hF : ∀ i,|F x i|≤1) (hf : (n:ℝ)*‖derivativeVector f x‖^2≤B^2) :
    ‖derivativeMatrix (fun y i => f y*F y i) x-f x • derivativeMatrix F x‖ ≤ B+2*C*B := by
  have hdb := derivative_norm_of_mean_square hn hB hf
  have hC0 : 0≤C := (norm_nonneg _).trans hC
  rw [derivativeMatrix_product]
  have he (A R T : Interaction n) : A+R-T-A=R-T := by abel
  rw [he]
  calc
    _ ≤ ‖Matrix.of (fun i k => F x i*halfDiff k f x)‖+
        ‖(2:ℝ) • (derivativeMatrix F x*Matrix.diagonal (fun k => spin x k*halfDiff k f x))‖ := norm_sub_le _ _
    _ ≤ B+2*C*B := by
      apply add_le_add (outer_frobenius_bound hF hB hf)
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2)]
      calc
        _ ≤ 2*(SKGap.opNorm (derivativeMatrix F x)*‖Matrix.diagonal (fun k => spin x k*halfDiff k f x)‖) :=
          mul_le_mul_of_nonneg_left (SKGap.frobenius_mul_le_opNorm _ _) (by norm_num)
        _ ≤ 2*(C*B) := by
          rw [spin_diagonal_frobenius]
          exact mul_le_mul_of_nonneg_left (mul_le_mul hC hdb (norm_nonneg _) hC0) (by norm_num)
        _ = _ := by ring

lemma derivativeMatrix_linear (J : Interaction n) (F : VectorFields n) (h : Fin n→ℝ)
    (x : Spin n) :
    derivativeMatrix (fun y i => h i+∑ k,J i k*F y k) x = J*derivativeMatrix F x := by
  ext i l
  simp only [derivativeMatrix,Matrix.mul_apply,halfDiff]
  simp_rw [← mul_div_assoc,mul_sub]
  rw [← Finset.sum_div,Finset.sum_sub_distrib]
  ring

lemma derivativeMatrix_sub (F G : VectorFields n) (x : Spin n) :
    derivativeMatrix (fun y i => F y i-G y i) x=derivativeMatrix F x-derivativeMatrix G x := by
  ext i k
  exact halfDiff_sub k (fun y => F y i) (fun y => G y i) x

lemma derivativeMatrix_smul (c : ℝ) (F : VectorFields n) (x : Spin n) :
    derivativeMatrix (fun y i => c*F y i) x=c • derivativeMatrix F x := by
  ext i k
  simp only [derivativeMatrix,halfDiff,Matrix.smul_apply,smul_eq_mul]
  ring

lemma derivativeMatrix_spin (x : Spin n) : derivativeMatrix spin x=1 := by
  ext i k
  simp [derivativeMatrix,Matrix.one_apply,eq_comm]

lemma variance_derivative_error {F : VectorFields n} {x : Spin n} {C : ℝ}
    (hC : 0≤C) (hD : ShapeBound (derivativeMatrix F x) C) :
    ‖derivativeMatrix (fun y i => 1-(F y i)^2) x-
      (-2:ℝ) • (Matrix.diagonal (F x)*derivativeMatrix F x)‖ ≤ 4*C^2 := by
  convert quadratic_entry_error hC (by norm_num : (0:ℝ)≤2) hD ?_ using 1 <;> try norm_num
  intro i k
  have hs : halfDiff k (fun y => 1-(F y i)^2) x =
      -2*F x i*halfDiff k (fun y => F y i) x+
        2*spin x k*(halfDiff k (fun y => F y i) x)^2 := by
    have hh := halfDiff_mul k (fun y => F y i) (fun y => F y i) x
    rw [halfDiff_sub,halfDiff_const]
    simpa only [pow_two,zero_sub] using (show -(halfDiff k (fun y => F y i*F y i) x) =
      -2*F x i*halfDiff k (fun y => F y i) x+
        2*spin x k*(halfDiff k (fun y => F y i) x)^2 by rw [hh]; ring)
  simp only [derivativeMatrix,hs]
  have he (a b c : ℝ) : -2*a*b+2*c*b^2+2*(a*b)=2*c*b^2 := by ring
  rw [he,abs_mul,abs_mul,abs_spin_eq_one,mul_one]
  norm_num [abs_of_nonneg (sq_nonneg (halfDiff k (fun y => F y i) x))]

lemma variance_derivative_opNorm {F : VectorFields n} {x : Spin n} {C : ℝ}
    (hC : 0≤C) (hF : ∀ i,|F x i|≤1) (hD : ShapeBound (derivativeMatrix F x) C) :
    SKGap.opNorm (derivativeMatrix (fun y i => 1-(F y i)^2) x) ≤ 2*C+4*C^2 := by
  let A := (-2:ℝ) • (Matrix.diagonal (F x)*derivativeMatrix F x)
  have hA : SKGap.opNorm A≤2*C := by
    dsimp only [A]
    rw [opNorm_smul]
    norm_num only [abs_neg,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
    exact mul_le_mul_of_nonneg_left (diagonal_mul_shape hF hD).1 (by norm_num)
  have hE := (opNorm_le_frobenius
    (derivativeMatrix (fun y i => 1-(F y i)^2) x-A)).trans (variance_derivative_error hC hD)
  have he : derivativeMatrix (fun y i => 1-(F y i)^2) x =
      A+(derivativeMatrix (fun y i => 1-(F y i)^2) x-A) := by abel
  rw [he]
  exact (opNorm_add _ _).trans (add_le_add hA hE)

lemma tanh_derivative_formal_error {F : VectorFields n} {x : Spin n}
    {H : Interaction n} {C E : ℝ} (hC : 0≤C) (hD : ShapeBound (derivativeMatrix F x) C)
    (hE : ‖derivativeMatrix F x-H‖≤E) :
    ‖derivativeMatrix (fun y i => Real.tanh (F y i)) x-
      Matrix.diagonal (fun i => scalarVariance (F x i))*H‖ ≤ 8*C^2+E := by
  let V := Matrix.diagonal (fun i => scalarVariance (F x i))
  have hV : SKGap.opNorm V≤1 := by
    apply SKGap.opNorm_diagonal_le (by norm_num)
    intro i
    rw [abs_of_pos (scalarVariance_pos _)]
    exact scalarVariance_le_one _
  have he : derivativeMatrix (fun y i => Real.tanh (F y i)) x-V*H =
      (derivativeMatrix (fun y i => Real.tanh (F y i)) x-V*derivativeMatrix F x)+
        V*(derivativeMatrix F x-H) := by noncomm_ring
  change ‖derivativeMatrix (fun y i => Real.tanh (F y i)) x-V*H‖≤_
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add (tanh_derivative_error hC hD)
  exact (SKGap.frobenius_mul_le_opNorm _ _).trans
    ((mul_le_mul_of_nonneg_right hV (norm_nonneg _)).trans (by simpa using hE))

end SKGapCutoff.Primary
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_Operation
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
-- module Solutions.OAIQ072_SK.SKGap_Localization_PhiRegularity
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
-- module Solutions.OAIQ072_SK.SKGap_Matrix_PrimaryMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary
open WordSeries
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrixWord_append (J : Matrix ι ι ℝ) (F G : List (Letter (ι→ℝ))) :
    matrixWord J (F++G)=matrixWord J F*matrixWord J G := by simp [matrixWord]
lemma matrixPolynomial_append (J : Matrix ι ι ℝ) (P Q : WordPolynomial (ι:=ι)) :
    matrixPolynomial J (P++Q)=matrixPolynomial J P+matrixPolynomial J Q := by
  simp [matrixPolynomial]
lemma matrixPolynomial_prefix (J : Matrix ι ι ℝ) (F : List (Letter (ι→ℝ)))
    (P : WordPolynomial (ι:=ι)) :
    matrixPolynomial J (prependWords F P)=matrixWord J F*matrixPolynomial J P := by
  induction P with
  | nil => simp [prependWords,matrixPolynomial]
  | cons p P ih =>
    simp only [prependWords,List.map_cons,matrixPolynomial,List.sum_cons] at *
    rw [matrixWord_append,ih,mul_add,mul_smul_comm]
lemma matrixPolynomial_scale (J : Matrix ι ι ℝ) (c : ℝ) (P : WordPolynomial (ι:=ι)) :
    matrixPolynomial J (scale c P)=c • matrixPolynomial J P := by
  induction P with
  | nil => simp [scale,matrixPolynomial]
  | cons p P ih =>
    simp only [scale,List.map_cons,matrixPolynomial,List.sum_cons] at *
    rw [ih,smul_add,mul_smul]

omit [DecidableEq ι]

lemma mean_abs_le_one [Nonempty ι] {a : ι→ℝ} (ha : ∀ i,|a i|≤1) :
    |Diagram.mean a|≤1 := by
  have hn : (0:ℝ)<Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  calc
    |Diagram.mean a| = |∑ i,a i|/(Fintype.card ι:ℝ) := by
      rw [Diagram.mean,abs_div,abs_of_pos hn]
    _ ≤ (∑ i,|a i|)/(Fintype.card ι:ℝ) :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hn.le
    _ ≤ 1 := by
      rw [div_le_one hn]
      simpa using Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => ha i)

end SKGap.Noncrossing.Primary
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_PrimaryDifferentiation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Primary
open SKGap Matrix
variable {n : ℕ}

lemma primaryDiagonal_bounded (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) :
    ∀ k i, |primaryDiagonal j J h x k i|≤1 := by
  intro k i
  rw [primaryDiagonal,abs_of_pos (scalarVariance_pos _)]
  exact scalarVariance_le_one _

lemma primaryState_mag_bounded (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ)
    (x : Spin n) (i : Fin n) : |(primaryState j J h k).1 x i|≤1 := by
  cases k with
  | zero => simp [primaryState,abs_spin_eq_one]
  | succ k => exact (Real.abs_tanh_lt_one _).le

lemma formalMag_previous (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) (k : ℕ) :
    formalMag j J h x k =
      Matrix.diagonal (SKGap.Noncrossing.Primary.previousDiagonal (primaryDiagonal j J h x) k)*
        SKGap.Noncrossing.Primary.primaryMatrix j J (primaryDiagonal j J h x) k := by
  cases k <;> simp [formalMag,formalField,SKGap.Noncrossing.Primary.previousDiagonal,
    SKGap.Noncrossing.Primary.primaryMatrix]

lemma formalField_succ (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) (k : ℕ) :
    formalField j J h x (k+1) = J*formalMag j J h x (k+1)-
      (j*SKGap.Noncrossing.Diagram.mean (primaryDiagonal j J h x k)) • formalMag j J h x k := by
  change SKGap.Noncrossing.Primary.primaryMatrix j J (primaryDiagonal j J h x) (k+2) =
    J*(Matrix.diagonal (primaryDiagonal j J h x k)*
      SKGap.Noncrossing.Primary.primaryMatrix j J (primaryDiagonal j J h x) (k+1))-
      (j*SKGap.Noncrossing.Diagram.mean (primaryDiagonal j J h x k)) • formalMag j J h x k
  rw [formalMag_previous,SKGap.Noncrossing.Primary.primaryMatrix,Matrix.mul_assoc]

lemma onsager_derivative_error {F G : VectorFields n} {x : Spin n} {H P : Interaction n}
    (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) {C R : ℝ} (hn : 0<n)
    (hC : 0≤C) (hR : 0≤R) (hJ : SKGap.opNorm J≤R)
    (hF : ShapeBound (derivativeMatrix F x) C) (hFE : ‖derivativeMatrix F x-H‖≤C)
    (hGE : ‖derivativeMatrix G x-P‖≤C) (hG : SKGap.opNorm (derivativeMatrix G x)≤C)
    (hGb : ∀ i,|G x i|≤1) :
    let m : VectorFields n := fun y i => Real.tanh (F y i)
    let b : Spin n→ℝ := siteMean (fun y i => 1-(m y i)^2)
    let T := C+8*C^2
    let Q := 2*T+4*T^2
    ‖derivativeMatrix (fun y i => h i+∑ a,J i a*m y a-j*b y*G y i) x-
      (J*(Matrix.diagonal (fun i => scalarVariance (F x i))*H)-(j*b x) • P)‖ ≤
      R*T+|j| *(C+Q+2*C*Q) := by
  let m : VectorFields n := fun y i => Real.tanh (F y i)
  let b : Spin n→ℝ := siteMean (fun y i => 1-(m y i)^2)
  let T := C+8*C^2
  let Q := 2*T+4*T^2
  change ‖derivativeMatrix (fun y i => h i+∑ a,J i a*m y a-j*b y*G y i) x-
    (J*(Matrix.diagonal (fun i => scalarVariance (F x i))*H)-(j*b x) • P)‖≤_
  have hT : 0≤T := by dsimp [T]; positivity
  have hQ : 0≤Q := by dsimp [Q]; positivity
  have hm : ShapeBound (derivativeMatrix m x) T := tanh_derivative_shape hC hF
  have hmE : ‖derivativeMatrix m x-Matrix.diagonal (fun i => scalarVariance (F x i))*H‖≤T := by
    convert tanh_derivative_formal_error hC hF hFE using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [T]
    ring
  have hbQ : (n:ℝ)*‖derivativeVector b x‖^2≤Q^2 :=
    siteMean_derivative_square_bound hn (variance_derivative_opNorm hT
      (fun i => (Real.abs_tanh_lt_one _).le) hm)
  have hp : ‖derivativeMatrix (fun y i => b y*G y i) x-b x • derivativeMatrix G x‖≤Q+2*C*Q :=
    product_derivative_error hn hQ hG hGb hbQ
  have hb : |b x|≤1 := by
    let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
    have hv (i : Fin n) : |1-(m x i)^2|≤1 := by
      change |scalarVariance (F x i)|≤1
      rw [abs_of_pos (scalarVariance_pos _)]
      exact scalarVariance_le_one _
    simpa only [b,siteMean,SKGap.Noncrossing.Diagram.mean,Fintype.card_fin] using
      SKGap.Noncrossing.Primary.mean_abs_le_one hv
  have hpE : ‖derivativeMatrix (fun y i => b y*G y i) x-b x • P‖≤C+Q+2*C*Q := by
    have he : derivativeMatrix (fun y i => b y*G y i) x-b x • P =
        (derivativeMatrix (fun y i => b y*G y i) x-b x • derivativeMatrix G x)+
          b x • (derivativeMatrix G x-P) := by module
    rw [he]
    apply (norm_add_le _ _).trans
    have hs : ‖b x • (derivativeMatrix G x-P)‖≤C := by
      rw [norm_smul,Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_right hb (norm_nonneg _)).trans (by simpa using hGE)
    have hh := add_le_add hp hs
    linarith
  have hd : derivativeMatrix (fun y i => h i+∑ a,J i a*m y a-j*b y*G y i) x =
      J*derivativeMatrix m x-j • derivativeMatrix (fun y i => b y*G y i) x := by
    rw [derivativeMatrix_sub,derivativeMatrix_linear]
    congr 1
    convert derivativeMatrix_smul j (fun y i => b y*G y i) x using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext y i
    ring
  rw [hd]
  have he : J*derivativeMatrix m x-j • derivativeMatrix (fun y i => b y*G y i) x-
      (J*(Matrix.diagonal (fun i => scalarVariance (F x i))*H)-(j*b x) • P) =
      J*(derivativeMatrix m x-Matrix.diagonal (fun i => scalarVariance (F x i))*H)-
        j • (derivativeMatrix (fun y i => b y*G y i) x-b x • P) := by
    simp only [mul_sub,smul_sub,mul_smul]
    abel
  rw [he]
  apply (norm_sub_le _ _).trans
  apply add_le_add
  · exact (SKGap.frobenius_mul_le_opNorm _ _).trans (mul_le_mul hJ hmE (norm_nonneg _) hR)
  · rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hpE (abs_nonneg _)

theorem primary_differentiation {j R B : ℝ} (J : Interaction n) (h : Fin n→ℝ)
    (x : Spin n) (hn : 0<n) (hR : 0≤R) (hB : 0≤B) (hJ : SKGap.opNorm J≤R) (k : ℕ)
    (hformal : ∀ l≤k, ShapeBound (formalField j J h x l) B) :
    let C := differentiationBound j R B k
    ‖derivativeMatrix (primaryState j J h k).2 x-formalField j J h x k‖≤C ∧
    ‖derivativeMatrix (primaryState j J h k).1 x-formalMag j J h x k‖≤C ∧
    SKGap.opNorm (derivativeMatrix (primaryState j J h k).1 x)≤C ∧
    ShapeBound (derivativeMatrix (primaryState j J h k).2 x) C := by
  induction k with
  | zero =>
    have hd : derivativeMatrix (primaryState j J h 0).2 x=J := by
      change derivativeMatrix (fun y i => h i+∑ a,J i a*spin y a) x=J
      rw [derivativeMatrix_linear,derivativeMatrix_spin,mul_one]
    have hm : derivativeMatrix (primaryState j J h 0).1 x=1 := derivativeMatrix_spin x
    have hf : formalField j J h x 0=J := rfl
    change _≤B+1 ∧ _≤B+1 ∧ _≤B+1 ∧ ShapeBound _ (B+1)
    rw [hd,hm,hf,formalMag,sub_self,norm_zero,sub_self,norm_zero]
    refine ⟨by positivity,by positivity,(SKGap.opNorm_one_le).trans ?_,?_⟩
    · linarith
    · exact (show ShapeBound J B by simpa only [hf] using hformal 0 le_rfl).mono (by linarith)
  | succ k ih =>
    obtain ⟨hFE,hGE,hG,hF⟩ := ih (fun l hl => hformal l (hl.trans (Nat.le_succ _)))
    let C := differentiationBound j R B k
    let T := C+8*C^2
    let Q := 2*T+4*T^2
    let E := R*T+|j| *(C+Q+2*C*Q)
    have hC : 0≤C := differentiationBound_nonneg hR hB k
    have hT : 0≤T := by dsimp [T]; positivity
    have hQ : 0≤Q := by dsimp [Q]; positivity
    have hE : 0≤E := by dsimp [E]; positivity
    have hnext : differentiationBound j R B (k+1)=B+1+E+T := rfl
    have hFE' : ‖derivativeMatrix (primaryState j J h (k+1)).2 x-formalField j J h x (k+1)‖≤E := by
      have hh := onsager_derivative_error (F := (primaryState j J h k).2)
        (G := (primaryState j J h k).1) j J h hn hC hR hJ hF hFE hGE hG
        (primaryState_mag_bounded j J h k x)
      have hb : siteMean (fun y i => 1-(Real.tanh ((primaryState j J h k).2 y i))^2) x =
          SKGap.Noncrossing.Diagram.mean (primaryDiagonal j J h x k) := by
        simp only [siteMean,SKGap.Noncrossing.Diagram.mean,primaryDiagonal,scalarVariance,Fintype.card_fin]
      dsimp only at hh
      rw [hb] at hh
      rw [formalField_succ]
      exact hh
    have hGE' : ‖derivativeMatrix (primaryState j J h (k+1)).1 x-formalMag j J h x (k+1)‖≤T := by
      have hh := tanh_derivative_formal_error hC hF hFE
      change ‖derivativeMatrix (fun y i => Real.tanh ((primaryState j J h k).2 y i)) x-
        Matrix.diagonal (fun i => scalarVariance ((primaryState j J h k).2 x i))*formalField j J h x k‖≤T
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      dsimp [T]
      ring
    have hG' : SKGap.opNorm (derivativeMatrix (primaryState j J h (k+1)).1 x)≤T :=
      (tanh_derivative_shape hC hF).1
    have hF' : ShapeBound (derivativeMatrix (primaryState j J h (k+1)).2 x) (B+E) :=
      (hformal (k+1) le_rfl).perturb hFE'
    rw [hnext]
    exact ⟨hFE'.trans (by linarith),hGE'.trans (by linarith),hG'.trans (by linarith),
      hF'.mono (by linarith)⟩

theorem primary_average_differentiation {j R B : ℝ} (J : Interaction n) (h : Fin n→ℝ)
    (x : Spin n) (hn : 0<n) (hR : 0≤R) (hB : 0≤B) (hJ : SKGap.opNorm J≤R) (k : ℕ)
    (hformal : ∀ l≤k, ShapeBound (formalField j J h x l) B) :
    let C := differentiationBound j R B k
    let T := C+8*C^2
    (n:ℝ)*‖derivativeVector (siteMean (fun y i =>
        scalarVariance ((primaryState j J h k).2 y i))) x‖^2≤(2*T+4*T^2)^2 := by
  have hC := differentiationBound_nonneg (j:=j) hR hB k
  have hF := (primary_differentiation J h x hn hR hB hJ k hformal).2.2.2
  apply siteMean_derivative_square_bound hn
  exact variance_derivative_opNorm (by positivity)
    (fun i => (Real.abs_tanh_lt_one _).le) (tanh_derivative_shape hC hF)

end SKGapCutoff.Primary

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_OrdinaryGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary
open Diagram
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace SourceTree
variable {D : Type*}

lemma sourceMatrix_leaf (j c : ℝ) (J : Matrix ι ι ℝ) :
    sourceMatrix j J (.leaf c)=c • 1 := by simp [sourceMatrix,words,matrixPolynomial,matrixWord]
lemma fieldMatrix_leaf (j c : ℝ) (J : Matrix ι ι ℝ) :
    fieldMatrix j J (.leaf c)=c • J := by
  simp [fieldMatrix,words,matrixPolynomial,matrixWord,matrixLetter]
lemma sourceMatrix_branch (j : ℝ) (J : Matrix ι ι ℝ) (p : ι→ℝ) (a b : SourceTree (ι→ℝ)) :
    sourceMatrix j J (.branch p a b)=Matrix.diagonal p*fieldMatrix j J a+sourceMatrix j J b := by
  simp [sourceMatrix,fieldMatrix,words,matrixPolynomial_append,matrixPolynomial_prefix,
    matrixWord,matrixLetter]
lemma fieldMatrix_branch (j : ℝ) (J : Matrix ι ι ℝ) (p : ι→ℝ) (a b : SourceTree (ι→ℝ)) :
    fieldMatrix j J (.branch p a b)=J*(Matrix.diagonal p*fieldMatrix j J a)-
      (j*Diagram.mean p) • sourceMatrix j J a+fieldMatrix j J b := by
  simp [sourceMatrix,fieldMatrix,words,matrixPolynomial_append,matrixPolynomial_prefix,
    matrixPolynomial_scale,matrixWord,matrixLetter,mul_assoc,sub_eq_add_neg,add_assoc]
end SourceTree
end SKGap.Noncrossing.Primary

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_RecipeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Primary
open SKGap.Noncrossing.Primary
variable {n : ℕ}

lemma primaryTree_matrices (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) (k : ℕ) :
    SourceTree.sourceMatrix j J (primaryTree j J h x k)=formalMag j J h x k ∧
    SourceTree.fieldMatrix j J (primaryTree j J h x k)=formalField j J h x k := by
  induction k with
  | zero => simp [primaryTree,SourceTree.sourceMatrix_leaf,SourceTree.fieldMatrix_leaf,
      formalMag,formalField,primaryMatrix]
  | succ k ih =>
    constructor
    · simp [primaryTree,SourceTree.sourceMatrix_branch,SourceTree.sourceMatrix_leaf,ih.2,formalMag]
    · simp only [primaryTree,SourceTree.fieldMatrix_branch,SourceTree.fieldMatrix_leaf,zero_smul,
        add_zero,ih.1,ih.2]
      rw [formalField_succ,formalMag]

end SKGapCutoff.Primary

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_ClosedErrorTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Matrix SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary SKGap.Noncrossing.Diagram
variable {n : ℕ}

lemma closedWordBounded_lift {A : ℝ} {w : OrdinaryWord n} (hw : wordBounded A w) :
    closedWordBounded A (liftWord w) := by
  intro l hl
  obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hl
  cases q with
  | diag p=>exact hw _ hq
  | noise=>trivial

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LiteralInitialRecipe
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
-- module Solutions.OAIQ072_SK.SKGap_Localization_ResidualInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Primary
open Matrix SKGap.Stein
variable {n : ℕ}

lemma mag_zero (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) : mag j J h 0=spin := rfl
lemma onsager_zero (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) :
    onsager j J h 0 x=0 := by simp [onsager,siteMean,mag_zero,spin_sq]

end SKGapCutoff.Primary

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ResidualAdmissibility
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
variable {n M : ℕ} {κ σ : Type*} [Fintype κ] [DecidableEq κ] [Fintype σ]
namespace OrdinaryData

omit [Fintype σ] in
lemma Admissible.mono {D : OrdinaryData n (Fin M) κ σ} {N p r : ℕ}
    (h : D.Admissible N p) (hr : r≤p) : D.Admissible N r :=
  fun a ha q hq=>h a ha q (hq.trans_le hr)

omit [Fintype σ] in
lemma Admissible.prefix {D : OrdinaryData n (Fin M) κ σ} {N p A : ℕ}
    (h : D.Admissible N p) (hr : A≤N) : D.Admissible A p :=
  fun a ha=>h a (ha.trans hr)

end OrdinaryData
end SKGapCutoff.Recipe

end
end

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
-- module Solutions.OAIQ072_SK.SKGap_Localization_RecipeCoefficientClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
lemma SegmentValue.at {H : ι→VectorFields n} {θ : κ→Spin n→ℝ}
    {F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ} {x : Spin n} {K : ℝ}
    (h : SegmentValue H θ F x K) (i : Fin n) : |coefficient H θ F x i|≤K := by
  simpa [coefficient] using h i i 0 (by constructor <;> norm_num)

omit [DecidableEq ι] [DecidableEq κ] in
lemma segmentRegular_const (H : ι→VectorFields n) (θ : κ→Spin n→ℝ) (x : Spin n) (c : ℝ) :
    SegmentRegular H θ (fun _ _=>c) (fun _ _=>0) x 0 := by
  refine ⟨le_rfl,fun _ _ _ _=>hasFDerivAt_const _ _,?_,?_⟩
  · intros; simp
  · intros; simp

namespace OrdinaryData

omit [Fintype σ] in
lemma CoefficientClass.prefix {D : OrdinaryData n ι κ σ} {N A : ℕ} {x : Spin n} {K : ℝ}
    (h : D.CoefficientClass N x K) (ha : A≤N) : D.CoefficientClass A x K :=
  ⟨h.one_le,fun a hh=>h.seedRegular a (hh.trans ha),fun a hh=>h.auxRegular a (hh.trans ha),
    fun a hh=>h.seedValue a (hh.trans ha),fun a hh=>h.auxValue a (hh.trans ha)⟩

end OrdinaryData
end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_ImplicitCoefficient
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
-- module Solutions.OAIQ072_SK.SKGap_Localization_LiteralInitialSystem
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
-- module Solutions.OAIQ072_SK.SKGap_Localization_LiteralSystemBridge
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
-- module Solutions.OAIQ072_SK.SKGap_Matrix_RecipeTraceBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary.MarkedPolynomial
open Diagram
variable {n : ℕ}

lemma mass_nonneg (P : WordPolynomial (ι:=Fin n)) : 0 ≤ mass P := by
  unfold mass
  exact List.sum_nonneg (by intro r hr; obtain ⟨t,_,rfl⟩:=List.mem_map.mp hr; exact abs_nonneg _)

end SKGap.Noncrossing.Primary.MarkedPolynomial

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LiteralRegularity
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
-- module Solutions.OAIQ072_SK.SKGap_Localization_UniformRecipeClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static
universe u
variable {Ω : Type u} {n : Ω→ℕ} {M : ℕ}
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

namespace OrdinaryData
lemma CoefficientClass.mono {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Fintype σ] {D : OrdinaryData n ι κ σ} {N : ℕ} {x : Spin n}
    {K L : ℝ} (h : D.CoefficientClass N x K) (hKL : K≤L) : D.CoefficientClass N x L := by
  refine ⟨h.one_le.trans hKL,fun a ha s=>(h.seedRegular a ha s).mono hKL,
    fun a ha b=>(h.auxRegular a ha b).mono hKL,?_,?_⟩
  · intro a ha s i k t ht; exact (h.seedValue a ha s i k t ht).trans hKL
  · intro a ha b i k t ht; exact (h.auxValue a ha b i k t ht).trans hKL
end OrdinaryData

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_MarkedDiagnostic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Noncrossing SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.MarkedPolynomial
variable {n : ℕ}
lemma wordBounded_append {A : ℝ} {u v : OrdinaryWord n}
    (hu : wordBounded A u) (hv : wordBounded A v) : wordBounded A (u++v) := by
  intro l hl; rcases List.mem_append.mp hl with hl|hl
  · exact hu l hl
  · exact hv l hl

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_PrimaryWordControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Noncrossing SKGap.Noncrossing.Primary
variable {n : ℕ}
lemma PolynomialControl.mono {A : ℝ} {L K : ℕ} {P : WordPolynomial (ι:=Fin n)}
    (h : PolynomialControl A L P) (hLK : L≤K) : PolynomialControl A K P :=
  fun t ht=>⟨(h t ht).1,(h t ht).2.trans hLK⟩
lemma PolynomialControl.append {A : ℝ} {L : ℕ} {P Q : WordPolynomial (ι:=Fin n)}
    (h : PolynomialControl A L P) (hQ : PolynomialControl A L Q) : PolynomialControl A L (P++Q) := by
  intro t ht; rcases List.mem_append.mp ht with ht|ht
  · exact h t ht
  · exact hQ t ht
lemma PolynomialControl.prepend {A : ℝ} {L : ℕ} {P : WordPolynomial (ι:=Fin n)}
    (h : PolynomialControl A L P) (w : OrdinaryWord n) (hw : wordBounded A w) :
    PolynomialControl A (w.length+L) (prependWords w P) := by
  intro t ht
  obtain ⟨r,hr,he⟩:=List.mem_map.mp ht
  subst t
  exact ⟨wordBounded_append hw (h r hr).1,by simpa only [List.length_append] using Nat.add_le_add_left (h r hr).2 w.length⟩
lemma PolynomialControl.scale {A : ℝ} {L : ℕ} {P : WordPolynomial (ι:=Fin n)}
    (h : PolynomialControl A L P) (c : ℝ) : PolynomialControl A L (SKGap.Noncrossing.Primary.scale c P) := by
  intro t ht
  obtain ⟨r,hr,he⟩:=List.mem_map.mp ht
  subst t
  exact h r hr
lemma polynomialControl_nil (c : ℝ) (A : ℝ) (L : ℕ) :
    PolynomialControl (n:=n) A L [(c,[])] := by
  intro t ht
  have he:=List.mem_singleton.mp ht; subst t
  exact ⟨by intro l hl; simp at hl,Nat.zero_le _⟩
lemma polynomialControl_noise (c : ℝ) (A : ℝ) (L : ℕ) (hL : 1≤L) :
    PolynomialControl (n:=n) A L [(c,[.noise])] := by
  intro t ht
  have he:=List.mem_singleton.mp ht; subst t
  constructor
  · intro l hl
    have he:=List.mem_singleton.mp hl; subst l; trivial
  · exact hL
end SKGapCutoff.Recipe
namespace SKGapCutoff.Primary
open Recipe SKGap.Noncrossing SKGap.Noncrossing.Primary
variable {n : ℕ}
theorem primaryTree_control (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) (k : ℕ)
    {A : ℝ} (hA : 1≤A) :
    PolynomialControl A (2*k+1) ((primaryTree j J h x k).words j).1 ∧
    PolynomialControl A (2*k+1) ((primaryTree j J h x k).words j).2 := by
  induction k with
  | zero=>exact ⟨polynomialControl_nil _ _ _,polynomialControl_noise _ _ _ (by omega)⟩
  | succ k ih=>
    have hd : wordBounded A [.diag (primaryDiagonal j J h x k)] := by
      intro l hl
      have he:=List.mem_singleton.mp hl; subst l
      exact fun i=>(primaryDiagonal_bounded j J h x k i).trans hA
    have hv : PolynomialControl A (2*(k+1)+1) (prependWords [.diag (primaryDiagonal j J h x k)]
        ((primaryTree j J h x k).words j).2) :=
      (ih.2.prepend _ hd).mono (by simp only [List.length_singleton]; omega)
    have hn : wordBounded (n:=n) A [.noise] := by
      intro l hl; have he:=List.mem_singleton.mp hl; subst l; trivial
    have hh : PolynomialControl A (2*(k+1)+1) (prependWords [.noise,.diag (primaryDiagonal j J h x k)]
        ((primaryTree j J h x k).words j).2) := by
      exact (ih.2.prepend _ (wordBounded_append hn hd)).mono (by simp only [List.length_append,List.length_cons,List.length_nil]; omega)
    simp only [primaryTree,SourceTree.words]
    exact ⟨hv.append (polynomialControl_nil _ _ _),
      (hh.append ((ih.1.scale _).mono (by omega))).append (polynomialControl_noise _ _ _ (by omega))⟩
end SKGapCutoff.Primary

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_FiniteRecipeControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Static
variable {n M : ℕ}

lemma emptyRecipe_local (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (M : ℕ)
    (T : Fin M→SKGap.Noncrossing.Primary.SourceTree (Fin n→ℝ)) (x : Spin n)
    {P L E V : ℝ} (hP : 0≤P) (hL : 0≤L) (hE : 0≤E) (hV : 0≤V) (hn : 0<n)
    (hJ : SKGap.opNorm J≤L)
    (hshape : ∀q:Fin M,ShapeBound (derivativeMatrix (fld j J h q.val) x) P)
    (hfield : ∀q:Fin M,‖derivativeMatrix (fld j J h q.val) x-
      SKGap.Noncrossing.Primary.SourceTree.fieldMatrix j J (T q)‖≤E)
    (hsource : ∀q:Fin M,‖derivativeMatrix (mag j J h q.val) x-
      SKGap.Noncrossing.Primary.SourceTree.sourceMatrix j J (T q)‖≤E)
    (hderiv : ∀q:Fin M,SKGap.opNorm (derivativeMatrix (mag j J h q.val) x)≤P)
    (hparam : (∑q:Fin M,‖derivativeVector (fun y=>j*(onsager j J h (q.val+1) y-onsager j J h q.val y)) x‖)≤V) :
    LocalOrdinaryInput (emptyRecipe j J h M) T x 0
      ⟨1,1,P,L,E,V,0,le_rfl,zero_le_one,le_rfl,hP,hL,hE,hV,le_rfl⟩ := by
  refine ⟨hn,hJ,hshape,hfield,hsource,?_,hderiv,?_,hparam,?_,?_,?_,?_⟩
  · intro q i; exact primaryState_mag_bounded j J h q.val x i
  · simp [emptyRecipe,vectorNorm]
  · intro a ha s; exact (segmentRegular_const _ _ x 0).mono zero_le_one
  · intro a ha b; exact (segmentRegular_const _ _ x 0).mono zero_le_one
  · intros; norm_num [OrdinaryData.seedCoefficient,coefficient,emptyRecipe]
  · intros; norm_num [OrdinaryData.auxCoefficient,coefficient,emptyRecipe]

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_StartedRecipe
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
-- module Solutions.OAIQ072_SK.SKGap_Localization_PrimaryLocalInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Primary
open Recipe SKGap.Noncrossing.Primary
variable {n : ℕ}

lemma localPrimaryBudget_bounds {j R B : ℝ} (hR : 0≤R) (hB : 0≤B) (M : ℕ) (q : Fin M) :
    differentiationBound j R B q.val≤localPrimaryBudget j R B M ∧
    averageBudget j R B q.val≤localPrimaryBudget j R B M := by
  have hh:=Finset.single_le_sum (s:=Finset.univ)
    (fun r (_:r∈Finset.univ)=>add_nonneg (differentiationBound_nonneg (j:=j) hR hB r.val)
      (averageBudget_nonneg (j:=j) hR hB r.val)) (Finset.mem_univ q)
  have h1:=differentiationBound_nonneg (j:=j) hR hB q.val
  have h2:=averageBudget_nonneg (j:=j) hR hB q.val
  exact ⟨(le_add_of_nonneg_right h2).trans hh,(le_add_of_nonneg_left h1).trans hh⟩

lemma onsager_derivative_bound {j R B : ℝ} (J : Interaction n) (h : Fin n→ℝ) (x : Spin n)
    (hn : 0<n) (hR : 0≤R) (hB : 0≤B) (hJ : SKGap.opNorm J≤R) (M : ℕ)
    (hformal : ∀l<M,ShapeBound (formalField j J h x l) B) {q : ℕ} (hq : q≤M) :
    ‖derivativeVector (onsager j J h q) x‖≤localPrimaryBudget j R B M := by
  cases q with
  | zero=>
    have he : onsager j J h 0=0:=funext (onsager_zero j J h)
    rw [he]
    have hz : derivativeVector (0 : Spin n→ℝ) x=0 := by
      ext i; simp [derivativeVector,halfDiff]
    rw [hz,norm_zero]
    exact localPrimaryBudget_nonneg (j:=j) hR hB M
  | succ k=>
    have hh:=primary_average_differentiation J h x hn hR hB hJ k (fun l hl=>hformal l (by omega))
    have hh':(n:ℝ)*‖derivativeVector (onsager j J h (k+1)) x‖^2≤(averageBudget j R B k)^2 := by
      simpa only [onsager,mag,primaryState,scalarVariance,averageBudget] using hh
    exact (derivative_norm_of_mean_square hn (averageBudget_nonneg hR hB k) hh').trans
      (localPrimaryBudget_bounds hR hB M ⟨k,by omega⟩).2

lemma derivativeVector_mul_sub (c : ℝ) (f g : Spin n→ℝ) (x : Spin n) :
    derivativeVector (fun y=>c*(f y-g y)) x=c • (derivativeVector f x-derivativeVector g x) := by
  ext i
  simp only [derivativeVector,WithLp.ofLp_toLp,PiLp.smul_apply,PiLp.sub_apply]
  simp only [halfDiff]
  ring

theorem primary_local_input {j R B : ℝ} (J : Interaction n) (h : Fin n→ℝ) (x : Spin n)
    (hn : 0<n) (hR : 0≤R) (hB : 0≤B) (hJ : SKGap.opNorm J≤R) (M : ℕ)
    (hformal : ∀l<M,ShapeBound (formalField j J h x l) B) :
    let C:=localPrimaryBudget j R B M
    LocalOrdinaryInput (emptyRecipe j J h M) (fun q=>primaryTree j J h x q.val) x 0
      ⟨1,1,C,R,C,(M:ℝ)*(|j| *(C+C)),0,le_rfl,zero_le_one,le_rfl,
        localPrimaryBudget_nonneg hR hB M,hR,localPrimaryBudget_nonneg hR hB M,
        by positivity [localPrimaryBudget_nonneg (j:=j) hR hB M],le_rfl⟩ := by
  dsimp only
  have hC:=localPrimaryBudget_nonneg (j:=j) hR hB M
  have hb:=localPrimaryBudget_bounds (j:=j) hR hB M
  have hd (q : Fin M):=primary_differentiation J h x hn hR hB hJ q.val
    (fun l hl=>hformal l (by omega))
  apply emptyRecipe_local j J h M _ x hC hR hC _ hn hJ
  · intro q; exact (hd q).2.2.2.mono (hb q).1
  · intro q; rw [(primaryTree_matrices j J h x q.val).2]
    exact (hd q).1.trans (hb q).1
  · intro q; rw [(primaryTree_matrices j J h x q.val).1]
    exact (hd q).2.1.trans (hb q).1
  · intro q; exact (hd q).2.2.1.trans (hb q).1
  · calc
      _ ≤ ∑q:Fin M,|j| *(localPrimaryBudget j R B M+localPrimaryBudget j R B M) := by
        apply Finset.sum_le_sum; intro q _
        rw [derivativeVector_mul_sub,norm_smul,Real.norm_eq_abs]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact (norm_sub_le _ _).trans (add_le_add
          (onsager_derivative_bound J h x hn hR hB hJ M hformal (by omega))
          (onsager_derivative_bound J h x hn hR hB hJ M hformal (by omega)))
      _ = _ := by simp

end SKGapCutoff.Primary

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_RecipePrimaryMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary.MarkedPolynomial
variable {n : ℕ}
lemma mass_append (P Q : WordPolynomial (ι:=Fin n)) : mass (P++Q)=mass P+mass Q := by
  simp [mass]
lemma mass_prefix (F : List (Letter (Fin n→ℝ))) (P : WordPolynomial (ι:=Fin n)) :
    mass (prependWords F P)=mass P := by simp [mass,prependWords,List.map_map,Function.comp_def]
lemma mass_scale (c : ℝ) (P : WordPolynomial (ι:=Fin n)) : mass (Primary.scale c P)=|c| *mass P := by
  induction P with
  | nil => simp [mass,Primary.scale]
  | cons t P ih =>
    simp only [Primary.scale,List.map_cons,mass,List.sum_cons,abs_mul] at *
    rw [ih]; ring
end SKGap.Noncrossing.Primary.MarkedPolynomial
namespace SKGapCutoff.Primary
open SKGap.Noncrossing.Primary MarkedPolynomial
variable {n : ℕ}

lemma primaryTree_mass (hn : 0<n) (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) (k : ℕ) :
    mass ((primaryTree j J h x k).words j).1≤(2+|j|)^k ∧
    mass ((primaryTree j J h x k).words j).2≤(2+|j|)^k := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  induction k with
  | zero => simp [primaryTree,SourceTree.words,mass]
  | succ k ih =>
    have hm := mean_abs_le_one (primaryDiagonal_bounded j J h x k)
    have hc : 0≤(2+|j|)^k := by positivity
    have hj : 0≤|j| := abs_nonneg _
    have ht : |j*SKGap.Noncrossing.Diagram.mean (primaryDiagonal j J h x k)|≤|j| := by
      rw [abs_mul]; simpa using mul_le_mul_of_nonneg_left hm hj
    simp only [primaryTree,SourceTree.words,mass_append,mass_prefix,mass_scale]
    have hz₁ : mass ([(0,[])] : WordPolynomial (ι:=Fin n))=0 := by simp [mass]
    have hz₂ : mass ([(0,[.noise])] : WordPolynomial (ι:=Fin n))=0 := by simp [mass]
    simp only [hz₁,hz₂,add_zero,abs_neg]
    constructor
    · rw [pow_succ]; nlinarith [ih.2,mul_nonneg hj hc]
    · have ht' := mul_le_mul ht ih.1 (mass_nonneg _) hj
      rw [pow_succ]
      nlinarith [ih.2]

end SKGapCutoff.Primary

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_BufferedSelectionDiagnostics
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
-- module Solutions.OAIQ072_SK.SKGap_Localization_RecipeArgumentPullback
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
-- module Solutions.OAIQ072_SK.SKGap_Localization_LocalRecipeClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static
universe u
variable {Ω : Type u} {n : Ω→ℕ} {M : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]
variable {σ τ : Type} [Fintype σ] [Fintype τ]

namespace LocalFamilyRecipe
variable {E : ∀a,Set (Spin (n a))} {j : ℝ} {J : ∀a,Interaction (n a)} {h : ∀a,Fin (n a)→ℝ}
variable {Θ : ∀a,κ→Observables (n a)} {w y : ∀a,VectorFields (n a)}
variable {D : ∀a,OrdinaryData (n a) (Fin M) κ σ} {N p : ℕ} {K : ℝ}

lemma mono (H : LocalFamilyRecipe E j J h Θ w y D N p K) {r A : ℕ} {L : ℝ}
    (hr : r≤p) (hA : A≤N) (hpos : 1≤A) (hK : K≤L) : LocalFamilyRecipe E j J h Θ w y D A r L :=
  ⟨hpos,H.interaction,H.coupling,H.primary,H.predecessor,H.parameter,H.seed,
    fun a x hx=>((H.coefficients a x hx).prefix hA).mono hK,
    fun a=>(H.admissible a).prefix hA |>.mono hr,H.initial⟩

end LocalFamilyRecipe
end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_FiniteStartedControlGeneral
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

theorem literal_full_local_family (j : ℝ) (J : ∀b,Interaction (n b))
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

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_ClosedOrdinaryBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.ClosedMarked
open SKGapCutoff.Recipe Primary Primary.Tensor.Series
variable {n : ℕ}

lemma ordinary_mass_bridge (j : ℝ) (t : SourceTree (Fin n→ℝ)) :
    Marked.mass (GradedWords.ordinaryWords j t).1=MarkedPolynomial.mass (t.words j).1 ∧
    Marked.mass (GradedWords.ordinaryWords j t).2=MarkedPolynomial.mass (t.words j).2 := by
  have happend (p q : GradedWords (Fin n)) : Marked.mass (p++q)=Marked.mass p+Marked.mass q := by simp [Marked.mass]
  have hprepend (l : WordLetter (Fin n)) (p : GradedWords (Fin n)) : Marked.mass (GradedWords.prepend l p)=Marked.mass p := by
    simp [Marked.mass,GradedWords.prepend,List.map_map,Function.comp_def]
  have hbump (p : GradedWords (Fin n)) : Marked.mass (GradedWords.bump p)=Marked.mass p := by
    simp [Marked.mass,GradedWords.bump,List.map_map,Function.comp_def]
  have hscale (c : ℝ) (p : GradedWords (Fin n)) : Marked.mass (GradedWords.scale c p)=|c| *Marked.mass p := by
    induction p with
    | nil=>simp [Marked.mass,GradedWords.scale]
    | cons t p ih=>simpa [Marked.mass,GradedWords.scale,mul_add,abs_mul] using congrArg (fun r=>|c*t.1|+r) ih
  have hprefix (w : OrdinaryWord n) (p : WordPolynomial (ι:=Fin n)) : MarkedPolynomial.mass (prependWords w p)=MarkedPolynomial.mass p := by
    simp [MarkedPolynomial.mass,prependWords,List.map_map,Function.comp_def]
  have hscale' (c : ℝ) (p : WordPolynomial (ι:=Fin n)) : MarkedPolynomial.mass (scale c p)=|c| *MarkedPolynomial.mass p := by
    induction p with
    | nil=>simp [MarkedPolynomial.mass,scale]
    | cons t p ih=>simpa [MarkedPolynomial.mass,scale,mul_add,abs_mul] using congrArg (fun r=>|c*t.1|+r) ih
  have happend' (p q : WordPolynomial (ι:=Fin n)) : MarkedPolynomial.mass (p++q)=MarkedPolynomial.mass p+MarkedPolynomial.mass q := by simp [MarkedPolynomial.mass]
  induction t with
  | leaf c=>simp [GradedWords.ordinaryWords,GradedWords.scalar,SourceTree.words,Marked.mass,MarkedPolynomial.mass,GradedWords.bump,GradedWords.prepend]
  | branch p t u ih1 ih2=>
    simp only [GradedWords.ordinaryWords,SourceTree.words,GradedWords.branch,happend,hprepend,hbump,hscale,happend',hprefix,hscale',ih1.1,ih1.2,ih2.1,ih2.2,and_self]
end SKGap.Noncrossing.ClosedMarked

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.ClosedMarked
open SKGapCutoff.Recipe Primary Primary.Tensor.Series
variable {n : ℕ}

lemma ordinary_word_bridge (j : ℝ) (t : SourceTree (Fin n→ℝ)) :
    ((GradedWords.ordinaryWords j t).1.map (fun s=>s.2.2))=((t.words j).1.map (fun s=>liftWord s.2)) ∧
    ((GradedWords.ordinaryWords j t).2.map (fun s=>s.2.2))=((t.words j).2.map (fun s=>liftWord s.2)) := by
  have hprefix (l : WordLetter (Fin n)) (P : GradedWords (Fin n)) :
      (GradedWords.prepend l P).map (fun s=>s.2.2)=(P.map (fun s=>s.2.2)).map (fun w=>l::w) := by
    simp [GradedWords.prepend,List.map_map,Function.comp_def]
  have hprefix' (l : Letter (Fin n→ℝ)) (P : WordPolynomial (ι:=Fin n)) :
      (prependWords [l] P).map (fun s=>liftWord s.2)=(P.map (fun s=>liftWord s.2)).map (fun w=>l.toWord::w) := by
    simp [prependWords,liftWord,List.map_map,Function.comp_def]
  have hprefix'' (l m : Letter (Fin n→ℝ)) (P : WordPolynomial (ι:=Fin n)) :
      (prependWords [l,m] P).map (fun s=>liftWord s.2)=(P.map (fun s=>liftWord s.2)).map (fun w=>l.toWord::m.toWord::w) := by
    simp [prependWords,liftWord,List.map_map,Function.comp_def]
  induction t with
  | leaf c=>simp [GradedWords.ordinaryWords,GradedWords.scalar,GradedWords.bump,GradedWords.prepend,SourceTree.words,liftWord,Letter.toWord]
  | branch p t u ih1 ih2=>
    simp only [GradedWords.ordinaryWords,GradedWords.branch,SourceTree.words,List.map_append]
    simp only [GradedWords.bump,GradedWords.scale,List.map_map,Function.comp_def]
    change ((GradedWords.prepend (.diag p) (GradedWords.ordinaryWords j t).2).map (fun s=>s.2.2)++
      (GradedWords.ordinaryWords j u).1.map (fun s=>s.2.2)=_) ∧ _
    constructor
    · rw [hprefix,ih1.2,ih2.1,hprefix'];rfl
    · simp only [hprefix,ih1.1,ih1.2,ih2.2,hprefix'',scale,List.map_map,Function.comp_def]
      rfl

lemma ordinary_control_bridge (j : ℝ) (t : SourceTree (Fin n→ℝ)) {A : ℝ} {L : ℕ}
    (h : PolynomialControl A L (t.words j).1 ∧ PolynomialControl A L (t.words j).2) :
    GradedControl A L (GradedWords.ordinaryWords j t).1 ∧ GradedControl A L (GradedWords.ordinaryWords j t).2 := by
  have hb:=ordinary_word_bridge j t
  constructor
  · intro s hs
    have hh : s.2.2∈((GradedWords.ordinaryWords j t).1.map (fun s=>s.2.2)):=List.mem_map.mpr ⟨s,hs,rfl⟩
    rw [hb.1] at hh
    obtain ⟨v,hv,he⟩:=List.mem_map.mp hh
    rw [←he]
    exact ⟨closedWordBounded_lift (h.1 v hv).1,by simpa [liftWord] using (h.1 v hv).2⟩
  · intro s hs
    have hh : s.2.2∈((GradedWords.ordinaryWords j t).2.map (fun s=>s.2.2)):=List.mem_map.mpr ⟨s,hs,rfl⟩
    rw [hb.2] at hh
    obtain ⟨v,hv,he⟩:=List.mem_map.mp hh
    rw [←he]
    exact ⟨closedWordBounded_lift (h.2 v hv).1,by simpa [liftWord] using (h.2 v hv).2⟩
end SKGap.Noncrossing.ClosedMarked

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LiteralLocalInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary SKGap.Stein SKGap.Noncrossing.Primary
variable {n M : ℕ}

theorem literal_full_local_input (j : ℝ) (J : Interaction n) (h : Fin n→ℝ)
    (l : Fin M) (f : KernelExpr) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (x : Spin n)
    (N : ℕ) (hn : 0<n) (he : vectorNorm e≤1)
    {K B A Va Vc : ℝ} (hK : 0≤K) (hB : 0≤B) (hA : 1≤A) (hVa : 0≤Va) (hVc : 0≤Vc)
    (hop : SKGap.opNorm J≤K) (hformal : ∀q<M,ShapeBound (formalField j J h x q) B)
    (ha : ‖derivativeVector a x‖≤Va) (hc : ‖derivativeVector (fun v=>Real.sqrt (n:ℝ)*c v) x‖≤Vc)
    (hcoeff : (literalFullData j J h l f a c r e).CoefficientClass N x A) :
    LocalOrdinaryInput (literalFullData j J h l f a c r e)
      (fun q=>primaryTree j J h x q.val) x N
      (literalEnvironmentConstants j K B A Va Vc M hK hB hA hVa hVc) := by
  have hp:=primary_local_input J h x hn hK hB hop M hformal
  refine ⟨hn,hop,hp.primaryShape,hp.primaryFieldError,hp.primarySourceError,
    hp.primaryValue,hp.primaryDerivative,?_,?_,hcoeff.seedRegular,hcoeff.auxRegular,?_,?_⟩
  · exact literalInitial_seed_bound J j f (fld j J h l.val) (mag j J h l.val) a c r e hn he
  · change (∑q : Fin M⊕Bool,‖derivativeVector (literalFullParameters j J h a c q) x‖)≤_
    rw [Fintype.sum_sum_type,Fintype.sum_bool]
    have hh:=hp.parameter
    change (∑q : Fin M,‖derivativeVector (fun v=>j*(onsager j J h (q.val+1) v-onsager j J h q.val v)) x‖)≤_ at hh
    change (∑q : Fin M,‖derivativeVector (fun v=>j*(onsager j J h (q.val+1) v-onsager j J h q.val v)) x‖)+
      (‖derivativeVector (fun v=>Real.sqrt (n:ℝ)*c v) x‖+‖derivativeVector a x‖)≤_
    dsimp only [literalEnvironmentConstants]
    linarith
  · intro b hb s i;exact (hcoeff.seedValue b hb s).at i
  · intro b hb s i;exact (hcoeff.auxValue b hb s).at i

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Static SKGap.Stein SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.Tensor.Series SKGap.Noncrossing.ClosedMarked
universe u
variable {Ω : Type u} {n : Ω→ℕ} {M : ℕ}

theorem literal_finite_control_oai (j : ℝ) (J : ∀b,Interaction (n b))
    (h : ∀b,Fin (n b)→ℝ) (l : Fin M) (f : KernelExpr)
    (a c : ∀b,Spin (n b)→ℝ) (r e : ∀b,Fin (n b)→ℝ)
    (w y : ∀b,VectorFields (n b)) (E : ∀b,Set (Spin (n b)))
    (hn : ∀b,0<n b) (he : ∀b,vectorNorm (e b)≤1)
    {K B R Bc Va Vc A V S F W C : ℝ}
    (hK : 0≤K) (hB : 0≤B) (hBc : 0≤Bc) (hVa : 0≤Va) (hVc : 0≤Vc)
    (hA : 1≤A) (hV : 0≤V) (hS : 0≤S) (hF : 0≤F) (hW : 0≤W) (hC : 0≤C)
    (hop : ∀b,SKGap.opNorm (J b)≤K)
    (hformal : ∀b x,∀q<M,ShapeBound (formalField j (J b) (h b) x q) B)
    (ha : ∀b x,x∈flipNeighborhood (flipNeighborhood (E b))→|a b x|≤R)
    (hc : ∀b x,x∈flipNeighborhood (flipNeighborhood (E b))→|Real.sqrt (n b:ℝ)*c b x|≤Bc)
    (hDa : ∀b x,x∈flipNeighborhood (E b)→‖derivativeVector (a b) x‖≤Va)
    (hDc : ∀b x,x∈flipNeighborhood (E b)→‖derivativeVector (fun v=>Real.sqrt (n b:ℝ)*c b v) x‖≤Vc)
    (heq : ∀b x,x∈E b→LiteralEquations (J b) j f (fld j (J b) (h b) l.val)
      (mag j (J b) (h b) l.val) (w b) (y b) (a b) (c b) (r b) (e b) x)
    (hdiag : ∀b x,x∈flipNeighborhood (E b)→LiteralInitialDiagnostics
      (literalInitial (J b) j (Real.sqrt (n b:ℝ)) f (fld j (J b) (h b) l.val)
        (mag j (J b) (h b) l.val) (a b) (c b) (r b) (e b))
      (w b) (y b) (primaryTree j (J b) (h b) x l.val) x V S F A)
    (Nmax : ℕ)
    (hw : ∀b x,x∈flipNeighborhood (E b)→ClosedWordTestBound j
      (fun i=>phi (fld j (J b) (h b) l.val x i) (r b i) (a b x)) (J b) A W (2*Nmax+5))
    (hd : ∀b x,x∈flipNeighborhood (E b)→ClosedWordDiagramBound j
      (fun i=>phi (fld j (J b) (h b) l.val x i) (r b i) (a b x)) (J b) A C (2*M+2*Nmax+4)) :
    FiniteLocalRecipeControl E j J h (fun b=>literalFullParameters (M:=M) j (J b) (h b) (a b) (c b))
      w y M Nmax A := by
  let D:=fun b=>literalFullData j (J b) (h b) l f (a b) (c b) (r b) (e b)
  let I:=fun b=>literalInitial (J b) j (Real.sqrt (n b:ℝ)) f (fld j (J b) (h b) l.val)
    (mag j (J b) (h b) l.val) (a b) (c b) (r b) (e b)
  let K₀:=literalCoefficientBudget f j R Bc
  have hK₀ : 1≤K₀ := by
    have h2 : 0≤f.mass*Real.exp (R/2):=mul_nonneg f.mass_nonneg (Real.exp_pos _).le
    have h3 : 0≤(1+|j| *|Bc|)*phiExpr.mass*Real.exp (R/2):=by positivity [phiExpr.mass_nonneg]
    dsimp [K₀,literalCoefficientBudget];linarith [abs_nonneg (initialRegularBudget f j R Bc)]
  have H:=literal_full_local_family j J h l f a c r e w y E hn he hBc ha hc heq
  have H₀:=H.mono (Nat.zero_le l.val) le_rfl le_rfl (le_refl K₀)
  have hi : ∀b x,x∈flipNeighborhood (E b)→LocalOrdinaryInput (D b)
      (fun q=>primaryTree j (J b) (h b) x q.val) x 1
      (literalEnvironmentConstants j K B K₀ Va Vc M hK hB hK₀ hVa hVc) := by
    intro b x hx
    exact literal_full_local_input j (J b) (h b) l f (a b) (c b) (r b) (e b) x 1
      (hn b) (he b) hK hB hK₀ hVa hVc (hop b) (hformal b x) (hDa b x hx) (hDc b x hx)
      (H.coefficients b x hx)
  have hm (b : Ω) (x : Spin (n b)) (q : Fin M) :
      Marked.mass (GradedWords.ordinaryWords j (primaryTree j (J b) (h b) x q.val)).1≤(2+|j|)^M ∧
      Marked.mass (GradedWords.ordinaryWords j (primaryTree j (J b) (h b) x q.val)).2≤(2+|j|)^M := by
    have hb:=ordinary_mass_bridge j (primaryTree j (J b) (h b) x q.val)
    rw [hb.1,hb.2]
    have hm:=primaryTree_mass (hn b) j (J b) (h b) x q.val
    have hp : (2+|j|)^q.val≤(2+|j|)^M:=pow_le_pow_right₀ (by linarith [abs_nonneg j]) q.isLt.le
    exact ⟨hm.1.trans hp,hm.2.trans hp⟩
  have ht (b : Ω) (x : Spin (n b)) (q : Fin M) :
      GradedControl A (2*M+1) (GradedWords.ordinaryWords j (primaryTree j (J b) (h b) x q.val)).1 ∧
      GradedControl A (2*M+1) (GradedWords.ordinaryWords j (primaryTree j (J b) (h b) x q.val)).2 := by
    apply ordinary_control_bridge
    have hv:=primaryTree_control j (J b) (h b) x q.val hA
    exact ⟨hv.1.mono (by omega),hv.2.mono (by omega)⟩
  apply finite_started_control_seeds D K₀ H₀ I (fun _=>rfl) (fun _=>rfl)
    (fun b x q=>primaryTree j (J b) (h b) x q.val) (fun b x=>primaryTree j (J b) (h b) x l.val)
    (literalEnvironmentConstants j K B K₀ Va Vc M hK hB hK₀ hVa hVc) A hi Sum.inl
    (fun _ _=>rfl) Nmax (2*M+1) S F V W C ((2+|j|)^M) hA hS hF hV hW hC (by positivity)
  · exact fun b x hx=>(hdiag b x hx).source
  · exact fun b x hx=>(hdiag b x hx).source_flip
  · exact fun b x hx=>(hdiag b x hx).field
  · exact fun b x hx=>(hdiag b x hx).field_flip
  · exact fun b x hx=>(hdiag b x hx).coefficient_nonneg
  · exact fun b x hx=>(hdiag b x hx).inverse_pos
  · exact fun b x hx=>(hdiag b x hx).source_bound
  · exact fun b x hx=>(hdiag b x hx).field_bound
  · exact fun b x hx=>(hdiag b x hx).partial_bound.size
  · exact fun b x hx=>(hdiag b x hx).source_trace
  · exact fun b x hx=>(hdiag b x hx).field_trace
  · exact fun b x hx=>(hdiag b x hx).coefficient_bound
  · exact fun b x _ q=>hm b x q
  · exact fun b x _=>hm b x l
  · exact fun b x _ q=>ht b x q
  · exact fun b x _=>ht b x l
  · intro b x hx
    have hcoef : (I b).implicitCoefficient x=fun i=>phi (fld j (J b) (h b) l.val x i) (r b i) (a b x) :=
      funext fun i=>literalInitial_coefficient _ _ _ _ _ _ _ _ _ _ _ _
    rw [hcoef];exact hw b x hx
  · intro b x hx
    have hcoef : (I b).implicitCoefficient x=fun i=>phi (fld j (J b) (h b) l.val x i) (r b i) (a b x) :=
      funext fun i=>literalInitial_coefficient _ _ _ _ _ _ _ _ _ _ _ _
    rw [hcoef]
    convert hd b x hx using 1
    all_goals try with_reducible_and_instances rfl
    omega

end SKGapCutoff.Recipe

end
end

end OAI
end

theorem solution.{u} : type_of% @OAI.SKGapCutoff.Recipe.literal_finite_control_oai.{u} := @OAI.SKGapCutoff.Recipe.literal_finite_control_oai.{u}
