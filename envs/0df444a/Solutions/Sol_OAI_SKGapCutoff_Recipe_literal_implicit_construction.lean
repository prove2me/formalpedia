-- Prove2me | solution 1 for OAI.SKGapCutoff.Recipe.literal_implicit_construction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:08:05.51597+00:00
-- url     : https://prove2.me/submissions/606217a7-ea94-4565-b407-c318ce4fb227

import Mathlib
import Definitions.Def_OAIQ072A002

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

lemma phiZ_at_diagonal (r a : ℝ) : phiZ r r a= -Real.tanh r*phi r r a := by
  simp [phiZ,numeratorZ]

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

lemma numerator_pos (z r a : ℝ) : 0<numerator z r a := by
  have h:=phi_pos z r a
  rw [phi_eq] at h
  exact (div_pos_iff_of_pos_right (mul_pos (Real.cosh_pos z) (Real.cosh_pos r))).mp h

lemma abs_numeratorZ_le (z r a : ℝ) : |numeratorZ z r a|≤numerator z r a := by
  unfold numeratorZ numerator
  apply (intervalIntegral.abs_integral_le_integral_abs (by norm_num : (0:ℝ)≤1)).trans
  apply intervalIntegral.integral_mono_on (by norm_num : (0:ℝ)≤1)
  · exact ((continuous_weight a|>.mul continuous_id).mul (by fun_prop) |>.abs).intervalIntegrable _ _
  · exact ((continuous_weight a).mul (by fun_prop)).intervalIntegrable _ _
  · intro u hu
    rw [abs_mul,abs_mul,abs_of_pos (show 0<weight a u from Real.exp_pos _),abs_of_nonneg hu.1]
    calc
      _ ≤ weight a u*u*Real.cosh (u*(z-r)) :=
        mul_le_mul_of_nonneg_left (abs_sinh_le_cosh _) (mul_nonneg (Real.exp_pos _).le hu.1)
      _ ≤ weight a u*Real.cosh (u*(z-r)) := by
        have H:=mul_le_mul_of_nonneg_left hu.2 (mul_pos (Real.exp_pos (a*(1-u^2)/2)) (Real.cosh_pos (u*(z-r)))).le
        dsimp [weight] at *
        nlinarith only [H]

lemma phiZ_relative_bound (z r a : ℝ) : |phiZ z r a|≤2*phi z r a := by
  unfold phiZ
  apply (abs_sub _ _).trans
  have hd : 0<Real.cosh z*Real.cosh r := mul_pos (Real.cosh_pos _) (Real.cosh_pos _)
  rw [abs_div,abs_of_pos hd,abs_mul,abs_of_pos (phi_pos z r a)]
  have h1:=div_le_div_of_nonneg_right (abs_numeratorZ_le z r a) hd.le
  have h2:=mul_le_mul_of_nonneg_right (Real.abs_tanh_lt_one z).le (phi_pos z r a).le
  rw [←phi_eq] at h1
  nlinarith

lemma numeratorZ_hasDerivAt (z r a : ℝ) :
    HasDerivAt (fun z=>numeratorZ z r a) (numeratorZZ z r a) z := by
  unfold numeratorZ numeratorZZ
  apply hasDerivAt_integral01 (F:=fun z u=>weight a u*u*Real.sinh (u*(z-r)))
    (F':=fun z u=>weight a u*u^2*Real.cosh (u*(z-r)))
  · unfold weight; fun_prop
  · unfold weight; fun_prop
  · intro z u
    convert! ((Real.hasDerivAt_sinh (u*(z-r))).comp z
      (((hasDerivAt_id z).sub_const r).const_mul u)).const_mul (weight a u*u) using 1
    all_goals try with_reducible_and_instances rfl
    ring

lemma numeratorZZ_nonneg (z r a : ℝ) : 0≤numeratorZZ z r a := by
  apply intervalIntegral.integral_nonneg (by norm_num : (0:ℝ)≤1)
  intro u _; exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _)) (Real.cosh_pos _).le

lemma numeratorZZ_le (z r a : ℝ) : numeratorZZ z r a≤numerator z r a := by
  apply intervalIntegral.integral_mono_on (by norm_num : (0:ℝ)≤1)
  · apply Continuous.intervalIntegrable; unfold weight; fun_prop
  · exact ((continuous_weight a).mul (by fun_prop)).intervalIntegrable _ _
  · intro u hu
    have hu2 : u^2≤1 := by nlinarith [hu.1,hu.2]
    have H:=mul_le_mul_of_nonneg_left hu2
      (mul_pos (Real.exp_pos (a*(1-u^2)/2)) (Real.cosh_pos (u*(z-r)))).le
    dsimp [weight] at *
    nlinarith only [H]

lemma logSlope_eq (z r a : ℝ) : logSlope z r a=
    numeratorZ z r a/numerator z r a-Real.tanh z := by
  rw [logSlope,phiZ,phi_eq]
  field_simp [ne_of_gt (numerator_pos z r a),ne_of_gt (Real.cosh_pos z),ne_of_gt (Real.cosh_pos r)]

lemma logSlope_hasDerivAt (z r a : ℝ) :
    HasDerivAt (fun z=>logSlope z r a) (logSlopeZ z r a) z := by
  have H:=((numeratorZ_hasDerivAt z r a).div (numerator_hasDerivAt z r a)
    (ne_of_gt (numerator_pos z r a))).sub (SKGapCutoff.tanh_hasDerivAt z)
  convert! H using 1
  · funext x; exact logSlope_eq x r a
  · unfold logSlopeZ
    field_simp [ne_of_gt (numerator_pos z r a)]

lemma logSlopeZ_bound (z r a : ℝ) : |logSlopeZ z r a|≤3 := by
  have hN : 0<numerator z r a := numerator_pos z r a
  have h0 : 0≤numeratorZZ z r a/numerator z r a := div_nonneg (numeratorZZ_nonneg z r a) hN.le
  have h1 : numeratorZZ z r a/numerator z r a≤1 := (div_le_one hN).mpr (numeratorZZ_le z r a)
  have h2 : |numeratorZ z r a/numerator z r a|≤1 := by
    rw [abs_div,abs_of_pos hN]; exact (div_le_one hN).mpr (abs_numeratorZ_le z r a)
  have h3:=pow_le_pow_left₀ (abs_nonneg (numeratorZ z r a/numerator z r a)) h2 2
  rw [sq_abs,one_pow] at h3
  rw [logSlopeZ,abs_le]
  constructor <;> nlinarith [SKGapCutoff.scalarVariance_pos z,SKGapCutoff.scalarVariance_le_one z,
    sq_nonneg (numeratorZ z r a/numerator z r a)]

lemma logSlope_lipschitz (z z' r a : ℝ) : |logSlope z' r a-logSlope z r a|≤3*|z'-z| := by
  have H:=Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun q (_ : q∈(Set.univ : Set ℝ))=>(logSlope_hasDerivAt q r a).hasDerivWithinAt)
    (fun q _=>show ‖logSlopeZ q r a‖≤3 by simpa only [Real.norm_eq_abs] using logSlopeZ_bound q r a)
    convex_univ (Set.mem_univ z) (Set.mem_univ z')
  simpa only [Real.norm_eq_abs] using H

lemma logSlope_diagonal (r a : ℝ) : logSlope r r a= -Real.tanh r := by
  rw [logSlope,phiZ_at_diagonal]
  exact mul_div_cancel_right₀ _ (ne_of_gt (phi_pos r r a))

theorem logSlope_near_diagonal (z r a : ℝ) : |logSlope z r a+Real.tanh r|≤3*|z-r| := by
  simpa only [logSlope_diagonal,sub_neg_eq_add] using logSlope_lipschitz r z r a

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
-- module Solutions.OAIQ072_SK.SKGap_Localization_CoefficientFlip
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set
namespace SKGapCutoff.Recipe
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma flipHalfDiff_norm (i : Fin n) (P : Spin n→E) (x : Spin n) :
    ‖flipHalfDiff i P x‖=‖P (flip x i)-P x‖/2 := by
  simp only [flipHalfDiff,norm_smul,Real.norm_eq_abs,abs_div,abs_spin_eq_one,abs_of_pos (by norm_num : (0:ℝ)<2)]
  rw [norm_sub_rev]
  ring

lemma coefficient_lipschitz (i : Fin n) (P : Spin n→E) (x : Spin n)
    (F : E→ℝ) (F' : E→E→L[ℝ]ℝ) {C : ℝ} (hC : 0≤C)
    (hF : ∀t∈Icc (0:ℝ) 1,HasFDerivAt F
      (F' (P x+t • (P (flip x i)-P x))) (P x+t • (P (flip x i)-P x)))
    (hBound : ∀t∈Icc (0:ℝ) 1,‖F' (P x+t • (P (flip x i)-P x))‖≤C) :
    |halfDiff i (fun y=>F (P y)) x|≤C*‖flipHalfDiff i P x‖ := by
  have H:=SKGap.SourceTaylor.segment_lipschitz F F' (P x) (P (flip x i)) hC hF hBound
  rw [halfDiff_as_flip,abs_div,abs_mul,abs_spin_eq_one,one_mul,
    abs_of_pos (by norm_num : (0:ℝ)<2),flipHalfDiff_norm,abs_sub_comm]
  simpa only [mul_div_assoc] using div_le_div_of_nonneg_right H (show (0:ℝ)≤2 by norm_num)

end SKGapCutoff.Recipe

end
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

lemma colVec_eq (M : Matrix ι ι ℝ) (k : ι) :
    colVec M k = M.toEuclideanLin.toContinuousLinearMap (EuclideanSpace.single k (1:ℝ)) := by
  ext i
  simp [colVec,Matrix.toLpLin_apply]

lemma colVec_norm_le (M : Matrix ι ι ℝ) (k : ι) : ‖colVec M k‖ ≤ opNorm M := by
  rw [colVec_eq]
  simpa only [PiLp.norm_single,norm_one,mul_one,opNorm] using!
    M.toEuclideanLin.toContinuousLinearMap.le_opNorm (EuclideanSpace.single k (1:ℝ))

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

local instance instFactLeENNRealOfNat_solutions_r50209d_1 : Fact (1≤(4:ENNReal)) := ⟨by norm_num⟩
lemma opNorm_eq (M : Interaction n) :
    SKGap.opNorm M = ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M‖ := rfl

lemma opNorm_le_frobenius (M : Interaction n) : SKGap.opNorm M ≤ ‖M‖ := by
  apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg M)
  simp only [← sq]
  rw [SKGap.frobenius_sq,opNorm_eq]
  exact RandomMatrix.matrix_opNorm_sq_le_frobenius M

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

end SKGapCutoff.Primary
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LocalCoefficient
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
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
variable {n : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma flipHalfDiff_coordinate {α : Type*} [Fintype α] (P : Spin n→α→ℝ)
    (k : Fin n) (x : Spin n) (l : α) :
    flipHalfDiff k P x l=halfDiff k (fun y=>P y l) x := by
  rw [halfDiff_as_flip]
  dsimp only [flipHalfDiff,Pi.smul_apply,Pi.sub_apply,smul_eq_mul]
  ring

omit [DecidableEq ι] [DecidableEq κ] in
lemma local_argument_bound (H : ι→VectorFields n) (θ : κ→Spin n→ℝ) (x : Spin n) (i k : Fin n) :
    ‖flipHalfDiff k (fun y=>localArgs H θ y i) x‖ ≤
      (∑l,|derivativeMatrix (H l) x i k|)+(∑α,|halfDiff k (θ α) x|) := by
  apply (pi_norm_le_iff_of_nonneg (add_nonneg
    (Finset.sum_nonneg fun l _=>abs_nonneg _) (Finset.sum_nonneg fun α _=>abs_nonneg _))).mpr
  intro l
  rw [Real.norm_eq_abs,flipHalfDiff_coordinate]
  cases l with
  | inl l =>
    dsimp only [localArgs,Sum.elim_inl]
    exact (Finset.single_le_sum (fun l _=>abs_nonneg (derivativeMatrix (H l) x i k)) (Finset.mem_univ l)).trans
      (le_add_of_nonneg_right (Finset.sum_nonneg fun α _=>abs_nonneg _))
  | inr α =>
    dsimp only [localArgs,Sum.elim_inr]
    exact (Finset.single_le_sum (fun α _=>abs_nonneg (halfDiff k (θ α) x)) (Finset.mem_univ α)).trans
      (le_add_of_nonneg_left (Finset.sum_nonneg fun l _=>abs_nonneg _))

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_Error
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.SourceError
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance instFactLeENNRealOfNat_solutions_r50209d_2 : Fact (1≤(4:ENNReal)) := ⟨by norm_num⟩
lemma matrix_column_square_le (P : Matrix ι ι ℝ) (i : ι) :
    (∑k,(P k i)^2)≤(opNorm P)^2 := by
  have H:=pow_le_pow_left₀ (norm_nonneg (colVec P i)) (colVec_norm_le P i) 2
  simpa only [colVec,EuclideanSpace.real_norm_sq_eq] using H

lemma matrix_row_square_le (P : Matrix ι ι ℝ) (i : ι) :
    (∑k,(P i k)^2)≤(opNorm P)^2 := by
  simpa only [Matrix.transpose_apply,opNorm_transpose] using matrix_column_square_le Pᵀ i

end SKGap.SourceError

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

lemma vectorNorm_mul (a s : Fin n→ℝ) {A : ℝ} (hA : 0 ≤ A) (ha : ∀i,|a i| ≤ A) :
    vectorNorm (fun i=>a i*s i) ≤ A*vectorNorm s := by
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hA (vectorNorm_nonneg _))
  simp only [←sq,vectorNorm_sq,mul_pow]
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _=>mul_le_mul_of_nonneg_right
    (by nlinarith [sq_abs (a i),ha i,abs_nonneg (a i)]) (sq_nonneg _)

lemma row_scaled_frobenius (D : Interaction n) (s : Fin n→ℝ) {R : ℝ}
    (hR : 0 ≤ R) (hD : ∀i,∑k,(D i k)^2 ≤ R^2) :
    ‖Matrix.of (fun i k=>s i*D i k)‖ ≤ R*vectorNorm s := by
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hR (vectorNorm_nonneg _))
  simp only [←sq]
  rw [SKGap.frobenius_sq,mul_pow,vectorNorm_sq]
  simp only [Matrix.of_apply,mul_pow,←Finset.mul_sum]
  calc
    _  ≤  ∑i,(s i)^2*R^2 := Finset.sum_le_sum fun i _=>mul_le_mul_of_nonneg_left (hD i) (sq_nonneg _)
    _ = _ := by rw [←Finset.sum_mul]; ring

lemma row_entry_bound (D : Interaction n) {R : ℝ} (hR : 0 ≤ R)
    (hD : ∀i,∑k,(D i k)^2 ≤ R^2) (i k : Fin n) : |D i k| ≤ R := by
  have H: (D i k)^2 ≤ R^2 :=
    (Finset.single_le_sum (fun l _=>sq_nonneg (D i l)) (Finset.mem_univ k)).trans (hD i)
  nlinarith [sq_abs (D i k),abs_nonneg (D i k)]

lemma multiplier_frobenius (a : Fin n→ℝ) (D : Interaction n) {A : ℝ}
    (hA : 0 ≤ A) (ha : ∀i,|a i| ≤ A) : ‖Matrix.of (fun i k=>a i*D i k)‖ ≤ A*‖D‖ := by
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hA (norm_nonneg _))
  simp only [←sq]
  rw [SKGap.frobenius_sq,mul_pow,SKGap.frobenius_sq]
  simp only [Matrix.of_apply,mul_pow,Finset.mul_sum]
  apply Finset.sum_le_sum; intro i _
  apply Finset.sum_le_sum; intro k _
  exact mul_le_mul_of_nonneg_right (by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (a i)) (ha i) 2) (sq_nonneg _)

lemma product_remainder_frobenius (A D : Interaction n) (x : Spin n) {R : ℝ}
    (hR : 0 ≤ R) (hA : ∀i,∑k,(A i k)^2 ≤ R^2) :
    ‖Matrix.of (fun i k=>2*spin x k*A i k*D i k)‖ ≤ 2*R*‖D‖ := by
  apply nonneg_le_nonneg_of_sq_le_sq (by positivity)
  simp only [←sq]
  rw [SKGap.frobenius_sq,mul_pow,mul_pow,SKGap.frobenius_sq]
  simp only [Matrix.of_apply,mul_pow,spin_sq,mul_one,Finset.mul_sum]
  apply Finset.sum_le_sum; intro i _
  apply Finset.sum_le_sum; intro k _
  have H:=row_entry_bound A hR hA i k
  have HH : (A i k)^2 ≤ R^2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (A i k)) H 2
  nlinarith [mul_nonneg (sq_nonneg (D i k)) (sub_nonneg.mpr HH)]

lemma source_derivative_product (a s : VectorFields n) (x : Spin n) :
    derivativeMatrix (fun x i=>a x i*s x i) x=
      (fun i k=>a x i*derivativeMatrix s x i k)+
      (fun i k=>s x i*derivativeMatrix a x i k)-
      (fun i k=>2*spin x k*derivativeMatrix a x i k*derivativeMatrix s x i k) := by
  ext i k
  exact halfDiff_mul k (fun x=>a x i) (fun x=>s x i) x

lemma source_frobenius (a s : VectorFields n) (x : Spin n) {A R : ℝ}
    (hA : 0 ≤ A) (hR : 0 ≤ R) (ha : ∀i,|a x i| ≤ A)
    (hda : ∀i,∑k,(derivativeMatrix a x i k)^2 ≤ R^2) :
    ‖derivativeMatrix (fun x i=>a x i*s x i) x‖ ≤
      A*‖derivativeMatrix s x‖+R*vectorNorm (s x)+2*R*‖derivativeMatrix s x‖ := by
  rw [source_derivative_product]
  exact (norm_sub_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add (multiplier_frobenius _ _ hA ha)
      (row_scaled_frobenius _ _ hR hda))) (product_remainder_frobenius _ _ x hR hda))

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix
variable {n : ℕ}

lemma vectorNorm_add (u v : Fin n→ℝ) :
    vectorNorm (u+v) ≤ vectorNorm u+vectorNorm v := by
  exact norm_add_le (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 v)

lemma vectorNorm_smul (c : ℝ) (u : Fin n→ℝ) :
    vectorNorm (c • u)=|c| *vectorNorm u := by
  exact norm_smul c (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))

lemma vectorNorm_sum {ι : Type*} [Fintype ι] (u : ι→Fin n→ℝ) :
    vectorNorm (∑l,u l) ≤ ∑l,vectorNorm (u l) := by
  change ‖(WithLp.toLp 2 (∑l,u l) : EuclideanSpace ℝ (Fin n))‖≤_
  have he : (WithLp.toLp 2 (∑l,u l) : EuclideanSpace ℝ (Fin n))=∑l,WithLp.toLp 2 (u l) := by
    ext i; simp [Finset.sum_apply]
  rw [he]
  exact norm_sum_le _ _

lemma vectorNorm_mono {u v : Fin n→ℝ} (h : ∀i,|u i|≤|v i|) : vectorNorm u ≤ vectorNorm v := by
  apply nonneg_le_nonneg_of_sq_le_sq (vectorNorm_nonneg _)
  simp only [←sq,vectorNorm_sq]
  exact Finset.sum_le_sum fun i _=>by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (u i)) (h i) 2

lemma vectorNorm_abs (u : Fin n→ℝ) : vectorNorm (fun i=>|u i|)=vectorNorm u := by
  apply (sq_eq_sq₀ (vectorNorm_nonneg _) (vectorNorm_nonneg _)).mp
  simp [vectorNorm_sq]

lemma siteMean_square (U : VectorFields n) (x : Spin n) (hn : 0<n) :
    (n:ℝ)*(siteMean U x)^2 ≤ (vectorNorm (U x))^2 := by
  have H:=sq_sum_le_card_mul_sum_sq (s:=Finset.univ) (f:=U x)
  simp only [Finset.card_univ,Fintype.card_fin] at H
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn
  dsimp only [siteMean]
  rw [div_pow,vectorNorm_sq]
  apply (mul_le_mul_iff_left₀ hnR).mp
  field_simp
  nlinarith

lemma coefficient_mean_value (a : VectorFields n) (x : Spin n) {A : ℝ}
    (hA : 0≤A) (ha : ∀i,|a x i|≤A) : |siteMean a x|≤A := by
  by_cases hn : n=0
  · subst n; simp [siteMean,hA]
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [siteMean,abs_div,abs_of_pos hnR]
  apply (div_le_iff₀ hnR).mpr
  calc
    _ ≤ ∑i,|a x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑_i:Fin n,A := Finset.sum_le_sum fun i _=>ha i
    _ = _ := by simp [mul_comm]

lemma coefficient_mean_difference (a : VectorFields n) (x : Spin n) {R : ℝ}
    (hR : 0≤R) (hda : ∀i,∑k,(derivativeMatrix a x i k)^2≤R^2) :
    ‖derivativeVector (siteMean a) x‖≤R := by
  have he : derivativeVector (siteMean a) x = (n:ℝ)⁻¹ •
      ∑i,WithLp.toLp 2 (fun k=>derivativeMatrix a x i k) := by
    ext k
    simp only [derivativeVector,WithLp.ofLp_toLp,PiLp.smul_apply,smul_eq_mul,WithLp.ofLp_sum,Finset.sum_apply,WithLp.ofLp_toLp]
    simp only [halfDiff,siteMean,derivativeMatrix]
    rw [←Finset.sum_div,Finset.sum_sub_distrib]
    ring
  rw [he,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (Nat.cast_nonneg n)]
  by_cases hn : n=0
  · subst n; simp [hR]
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  calc
    _ ≤ (n:ℝ)⁻¹*(∑_i:Fin n,R) := mul_le_mul_of_nonneg_left
      ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _=>by
        apply nonneg_le_nonneg_of_sq_le_sq hR
        simpa only [←sq,EuclideanSpace.real_norm_sq_eq,WithLp.ofLp_toLp] using hda i)) (inv_nonneg.mpr hnR.le)
    _ = R := by simp [hnR.ne']

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_CoefficientRow
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
variable {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma row_vectorNorm_le_opNorm (D : Interaction n) (i : Fin n) :
    vectorNorm (D i) ≤ SKGap.opNorm D := by
  have h0 : 0≤SKGap.opNorm D := norm_nonneg _
  apply nonneg_le_nonneg_of_sq_le_sq h0
  simp only [←sq,vectorNorm_sq]
  exact SKGap.SourceError.matrix_row_square_le D i

lemma local_argument_row_bound (H : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (x : Spin n) (i : Fin n) :
    vectorNorm (fun k=>‖flipHalfDiff k (fun y=>localArgs H θ y i) x‖) ≤
      (∑l,SKGap.opNorm (derivativeMatrix (H l) x))+(∑α,‖derivativeVector (θ α) x‖) := by
  have hQ (l : ι) : vectorNorm (fun k=>|derivativeMatrix (H l) x i k|)≤SKGap.opNorm (derivativeMatrix (H l) x) := by
    rw [vectorNorm_abs]; exact row_vectorNorm_le_opNorm _ _
  have hT (α : κ) : vectorNorm (fun k=>|halfDiff k (θ α) x|)=‖derivativeVector (θ α) x‖ := by
    rw [vectorNorm_abs]; rfl
  calc
    _ ≤ vectorNorm (fun k=>(∑l,|derivativeMatrix (H l) x i k|)+(∑α,|halfDiff k (θ α) x|)) :=
      vectorNorm_mono fun k=>by
        have hp : 0≤(∑l,|derivativeMatrix (H l) x i k|)+(∑α,|halfDiff k (θ α) x|) :=
          add_nonneg (Finset.sum_nonneg fun _ _=>abs_nonneg _) (Finset.sum_nonneg fun _ _=>abs_nonneg _)
        simpa only [abs_of_nonneg (norm_nonneg _),abs_of_nonneg hp] using local_argument_bound H θ x i k
    _ ≤ vectorNorm (fun k=>∑l,|derivativeMatrix (H l) x i k|)+
        vectorNorm (fun k=>∑α,|halfDiff k (θ α) x|) := vectorNorm_add _ _
    _ ≤ (∑l,vectorNorm (fun k=>|derivativeMatrix (H l) x i k|))+
        ∑α,vectorNorm (fun k=>|halfDiff k (θ α) x|) := by
      apply add_le_add
      · convert! vectorNorm_sum (fun l k=>|derivativeMatrix (H l) x i k|) using 1
        all_goals try with_reducible_and_instances rfl
        congr 1; ext k; simp
      · convert! vectorNorm_sum (fun α k=>|halfDiff k (θ α) x|) using 1
        all_goals try with_reducible_and_instances rfl
        congr 1; ext k; simp
    _ ≤ _ := add_le_add (Finset.sum_le_sum fun l _=>hQ l) (by simp only [hT]; rfl)

lemma coefficient_row_bound (H : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ)
    (F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ)
    (x : Spin n) (i : Fin n) {L : ℝ} (hL : 0≤L)
    (hF : ∀k t, t∈Set.Icc (0:ℝ) 1→HasFDerivAt (F i)
      (F' i (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i)))
      (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i)))
    (hBound : ∀k t, t∈Set.Icc (0:ℝ) 1→
      ‖F' i (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i))‖≤L) :
    vectorNorm (derivativeMatrix (coefficient H θ F) x i) ≤
      L*((∑l,SKGap.opNorm (derivativeMatrix (H l) x))+(∑α,‖derivativeVector (θ α) x‖)) := by
  calc
    _ ≤ vectorNorm (fun k=>L*‖flipHalfDiff k (fun y=>localArgs H θ y i) x‖) :=
      vectorNorm_mono fun k=>by
        rw [abs_of_nonneg (mul_nonneg hL (norm_nonneg _))]
        exact coefficient_lipschitz k (fun y=>localArgs H θ y i) x (F i) (F' i) hL (hF k) (hBound k)
    _ = L*vectorNorm (fun k=>‖flipHalfDiff k (fun y=>localArgs H θ y i) x‖) := by
      convert! vectorNorm_smul L (fun k=>‖flipHalfDiff k (fun y=>localArgs H θ y i) x‖) using 1
      all_goals try with_reducible_and_instances rfl
      rw [abs_of_nonneg hL]
    _ ≤ _ := mul_le_mul_of_nonneg_left (local_argument_row_bound H θ x i) hL

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix
variable {n : ℕ}

lemma SmallBound.mono {U : VectorFields n} {x : Spin n} {C D : ℝ}
    (h : SmallBound U x C) (hCD : C≤D) : SmallBound U x D :=
  ⟨h.nonneg.trans hCD,h.size.trans hCD,h.derivative.trans hCD⟩

lemma SmallBound.seed (s : Fin n→ℝ) (x : Spin n) :
    SmallBound (fun _=>s) x (vectorNorm s) := by
  refine ⟨vectorNorm_nonneg _,le_rfl,?_⟩
  have he : derivativeMatrix (fun _=>s) x=0 := by ext i k; simp [derivativeMatrix,halfDiff]
  rw [he,norm_zero]; exact vectorNorm_nonneg _

lemma SmallBound.coefficient {U : VectorFields n} {x : Spin n} {C : ℝ}
    (hU : SmallBound U x C) (a : VectorFields n) {A R : ℝ}
    (hA : 0≤A) (hR : 0≤R) (ha : ∀i,|a x i|≤A)
    (hda : ∀i,∑k,(derivativeMatrix a x i k)^2≤R^2) :
    SmallBound (fun x i=>a x i*U x i) x (C*(A+3*R)) := by
  refine ⟨mul_nonneg hU.nonneg (by positivity),?_,?_⟩
  · exact ((vectorNorm_mul _ _ hA ha).trans (mul_le_mul_of_nonneg_left hU.size hA)).trans
      (by nlinarith [mul_nonneg hU.nonneg hR])
  · calc
      _ ≤ A*‖derivativeMatrix U x‖+R*vectorNorm (U x)+2*R*‖derivativeMatrix U x‖ :=
        source_frobenius a U x hA hR ha hda
      _ ≤ A*C+R*C+2*R*C := add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left hU.derivative hA) (mul_le_mul_of_nonneg_left hU.size hR))
        (mul_le_mul_of_nonneg_left hU.derivative (by positivity))
      _ = _ := by ring

end SKGapCutoff.Recipe

end
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
-- module Solutions.OAIQ072_SK.SKGap_Localization_PhiRatio
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace SKGap.Stein

namespace RatioExpr

lemma mass_nonneg (f : RatioExpr) : 0 ≤ mass f := by
  induction f with
  | constant c  =>  exact abs_nonneg c
  | kernel f  =>  exact f.mass_nonneg
  | add f g hf hg  =>  exact add_nonneg hf hg
  | mul f g hf hg  =>  exact mul_nonneg hf hg

lemma bounded (f : RatioExpr) (z r a : ℝ) : |eval f z r a| ≤ mass f := by
  induction f with
  | constant c  =>  exact le_refl _
  | kernel f  =>
    dsimp only [eval,mass]
    rw [abs_div,abs_of_pos (phi_pos z r a),div_le_iff₀ (phi_pos z r a)]
    exact f.relative_bound z r a
  | add f g hf hg  =>  exact (abs_add_le _ _).trans (add_le_add hf hg)
  | mul f g hf hg  =>
    dsimp only [eval,mass]
    rw [abs_mul]
    exact mul_le_mul hf hg (abs_nonneg _) f.mass_nonneg

lemma kernel_deriv_z (f : KernelExpr) (z r a : ℝ) :
    HasDerivAt (fun z => eval (kernel f) z r a) (eval (d .z (kernel f)) z r a) z := by
  have hphi : HasDerivAt (fun z => phi z r a)
      ((KernelExpr.atom 0 0 false).dz.eval z r a) z := by
    simpa only [KernelExpr.eval,moment_base] using (KernelExpr.atom 0 0 false).hasDerivAt_z z r a
  convert! (f.hasDerivAt_z z r a).div hphi (phi_pos z r a).ne' using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [eval,d,KernelExpr.d]
  field_simp
  ring

lemma kernel_deriv_r (f : KernelExpr) (z r a : ℝ) :
    HasDerivAt (fun r => eval (kernel f) z r a) (eval (d .r (kernel f)) z r a) r := by
  have hphi : HasDerivAt (fun r => phi z r a)
      ((KernelExpr.atom 0 0 false).dr.eval z r a) r := by
    simpa only [KernelExpr.eval,moment_base] using (KernelExpr.atom 0 0 false).hasDerivAt_r z r a
  convert! (f.hasDerivAt_r z r a).div hphi (phi_pos z r a).ne' using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [eval,d,KernelExpr.d]
  field_simp
  ring

lemma kernel_deriv_a (f : KernelExpr) (z r a : ℝ) :
    HasDerivAt (fun a => eval (kernel f) z r a) (eval (d .a (kernel f)) z r a) a := by
  have hphi : HasDerivAt (fun a => phi z r a)
      ((KernelExpr.atom 0 0 false).da.eval z r a) a := by
    simpa only [KernelExpr.eval,moment_base] using (KernelExpr.atom 0 0 false).hasDerivAt_a z r a
  convert! (f.hasDerivAt_a z r a).div hphi (phi_pos z r a).ne' using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [eval,d,KernelExpr.d]
  field_simp
  ring

lemma hasDerivAt_z (f : RatioExpr) (z r a : ℝ) :
    HasDerivAt (fun z => eval f z r a) (eval (d .z f) z r a) z := by
  induction f with
  | constant c  =>  exact hasDerivAt_const z c
  | kernel f  =>  exact kernel_deriv_z f z r a
  | add f g hf hg  =>  exact hf.add hg
  | mul f g hf hg  =>  exact hf.mul hg

lemma hasDerivAt_r (f : RatioExpr) (z r a : ℝ) :
    HasDerivAt (fun r => eval f z r a) (eval (d .r f) z r a) r := by
  induction f with
  | constant c  =>  exact hasDerivAt_const r c
  | kernel f  =>  exact kernel_deriv_r f z r a
  | add f g hf hg  =>  exact hf.add hg
  | mul f g hf hg  =>  exact hf.mul hg

lemma hasDerivAt_a (f : RatioExpr) (z r a : ℝ) :
    HasDerivAt (fun a => eval f z r a) (eval (d .a f) z r a) a := by
  induction f with
  | constant c  =>  exact hasDerivAt_const a c
  | kernel f  =>  exact kernel_deriv_a f z r a
  | add f g hf hg  =>  exact hf.add hg
  | mul f g hf hg  =>  exact hf.mul hg

end RatioExpr
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

namespace RatioExpr
lemma continuous_eval (f : RatioExpr) : Continuous (eval3 f.eval) := by
  induction f with
  | constant c => exact continuous_const
  | kernel f =>
    have hp : Continuous (eval3 phi) := by simpa only [KernelExpr.eval,moment_base] using
      (KernelExpr.atom 0 0 false).continuous_eval
    exact f.continuous_eval.div hp (fun x=>(phi_pos x.1 x.2.1 x.2.2).ne')
  | add f g hf hg => exact hf.add hg
  | mul f g hf hg => exact hf.mul hg

lemma hasFDerivAt_eval (f : RatioExpr) (x : Triple) :
    HasFDerivAt (eval3 f.eval) (f.gradient x) x :=
  hasFDerivAt_of_three_partials f.eval (f.d .z).eval (f.d .r).eval (f.d .a).eval
    f.hasDerivAt_z f.hasDerivAt_r f.hasDerivAt_a
    (f.d .z).continuous_eval (f.d .r).continuous_eval (f.d .a).continuous_eval x

lemma gradient_bound (f : RatioExpr) (x : Triple) : ‖f.gradient x‖≤f.dBudget := by
  exact (grad3_norm ..).trans (add_le_add
    (add_le_add ((f.d .z).bounded ..) ((f.d .r).bounded ..)) ((f.d .a).bounded ..))
lemma lipschitz_global (f : RatioExpr) (x y : Triple) :
    |eval3 f.eval y-eval3 f.eval x|≤f.dBudget*‖y-x‖ := by
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z (_ : z∈(Set.univ:Set Triple))=>(f.hasFDerivAt_eval z).hasFDerivWithinAt)
    (fun z _=>f.gradient_bound z) convex_univ (Set.mem_univ x) (Set.mem_univ y)
lemma gradient_lipschitz (f : RatioExpr) (x y : Triple) :
    ‖f.gradient y-f.gradient x‖≤f.ddBudget*‖y-x‖ := by
  rw [gradient,gradient,grad3_sub]
  apply (grad3_norm ..).trans
  exact (add_le_add (add_le_add ((f.d .z).lipschitz_global x y) ((f.d .r).lipschitz_global x y))
    ((f.d .a).lipschitz_global x y)).trans_eq (by dsimp [ddBudget]; ring)
end RatioExpr
end SKGap.Stein

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

lemma _root_.OAI.SKGap.Stein.RatioExpr.dBudget_nonneg (f : RatioExpr) : 0≤f.dBudget := by
  exact add_nonneg (add_nonneg (f.d .z).mass_nonneg (f.d .r).mass_nonneg) (f.d .a).mass_nonneg
lemma _root_.OAI.SKGap.Stein.RatioExpr.ddBudget_nonneg (f : RatioExpr) : 0≤f.ddBudget :=
  add_nonneg (add_nonneg (f.d .z).dBudget_nonneg (f.d .r).dBudget_nonneg) (f.d .a).dBudget_nonneg

lemma phi_ratio_segmentRegular (f : RatioExpr) (H : ι→VectorFields n)
    (θ : κ→Spin n→ℝ) (x : Spin n)
    (L : Args (ι:=ι) (κ:=κ)→L[ℝ]Triple) (s : Fin n→Triple) :
    SegmentRegular H θ (fun i u=>eval3 f.eval (L u+s i))
      (fun i u=>(f.gradient (L u+s i)).comp L) x
      (f.dBudget*‖L‖+f.ddBudget*‖L‖^2) :=
  affine_segmentRegular H θ x (eval3 f.eval) f.gradient L s Set.univ convex_univ
    f.dBudget_nonneg f.ddBudget_nonneg
    (fun u _=>f.hasFDerivAt_eval u) (fun u _=>f.gradient_bound u)
    (fun u _ v _=>f.gradient_lipschitz u v) (fun _=>Set.mem_univ _) (fun _ _=>Set.mem_univ _)

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
-- module Solutions.OAIQ072_SK.SKGap_Stability_OrdinaryRecipe
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
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

lemma CoefficientBound.small_product {a U : VectorFields n} {x : Spin n} {A R C : ℝ}
    (ha : CoefficientBound a x A R) (hU : SmallBound U x C) :
    SmallBound (fun x i=>a x i*U x i) x (C*(A+3*R)) :=
  hU.coefficient a ha.size_nonneg ha.row_nonneg ha.value ha.difference

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

lemma phiExpr_dz (z r a : ℝ) : phiExpr.dz.eval z r a=phiZ z r a := by
  have H:=phiExpr.hasDerivAt_z z r a
  have He : phiExpr.eval=phi := funext fun _=>funext fun _=>funext fun _=>moment_base _ _ _
  rw [He] at H
  exact H.unique (phi_hasDerivAt z r a)

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_NormalizedPrimaryRecipe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary
variable {n M : ℕ} {κ σ : Type*} [Fintype κ] [DecidableEq κ]

lemma scaledMean_size (hn : 0<n) (U : VectorFields n) (x : Spin n) {C : ℝ}
    (hC : 0≤C) (hU : vectorNorm (U x)≤C) :
    |Real.sqrt (n:ℝ)*siteMean U x|≤C := by
  apply (sq_le_sq₀ (abs_nonneg _) hC).mp
  rw [sq_abs,mul_pow,Real.sq_sqrt (Nat.cast_nonneg n)]
  exact (siteMean_square U x hn).trans (pow_le_pow_left₀ (vectorNorm_nonneg _) hU 2)

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_PhiCoefficient
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

lemma phi_hasDerivAt_a (z r a : ℝ) : HasDerivAt (fun a=>phi z r a) (phiA z r a) a := by
  unfold phi phiA
  apply hasDerivAt_integral01
    (F:=fun a u=>weight a u*Real.cosh (u*(z-r))/(Real.cosh z*Real.cosh r))
    (F':=fun a u=>((1-u^2)/2)*(weight a u*Real.cosh (u*(z-r))/(Real.cosh z*Real.cosh r)))
  · unfold weight; fun_prop
  · unfold weight; fun_prop
  · intro a u
    have h:=((((hasDerivAt_id a).mul_const (1-u^2)).div_const 2).exp.mul_const
      (Real.cosh (u*(z-r)))).div_const (Real.cosh z*Real.cosh r)
    convert! h using 1
    all_goals try with_reducible_and_instances rfl
    try dsimp [weight]
    ring

lemma phiA_nonneg (z r a : ℝ) : 0≤phiA z r a := by
  apply intervalIntegral.integral_nonneg (by norm_num : (0:ℝ)≤1)
  intro u hu
  have hu2 : u^2≤1 := by nlinarith [hu.1,hu.2]
  apply mul_nonneg (by linarith)
  exact div_nonneg (mul_pos (Real.exp_pos _) (Real.cosh_pos _)).le
    (mul_pos (Real.cosh_pos _) (Real.cosh_pos _)).le

lemma phiA_relative_bound (z r a : ℝ) : phiA z r a≤phi z r a/2 := by
  have H:=intervalIntegral.integral_mono_on (μ:=volume) (a:=(0:ℝ)) (b:=1) (by norm_num)
    (f:=fun u=>((1-u^2)/2)*(weight a u*Real.cosh (u*(z-r))/(Real.cosh z*Real.cosh r)))
    (g:=fun u=>(weight a u*Real.cosh (u*(z-r))/(Real.cosh z*Real.cosh r))/2)
    (by apply Continuous.intervalIntegrable; unfold weight; fun_prop)
    (((continuous_integrand z r a).div_const 2).intervalIntegrable _ _)
    (by
      intro u hu
      have hp : 0≤weight a u*Real.cosh (u*(z-r))/(Real.cosh z*Real.cosh r) := by
        apply div_nonneg (mul_pos (Real.exp_pos _) (Real.cosh_pos _)).le
        exact (mul_pos (Real.cosh_pos _) (Real.cosh_pos _)).le
      nlinarith [mul_nonneg (sq_nonneg u) hp])
  simpa only [intervalIntegral.integral_div,phiA,phi] using H

lemma phi_lipschitz_z (z z' r a : ℝ) :
    |phi z' r a-phi z r a|≤(2*Real.exp (|a|/2))*|z'-z| := by
  have H:=Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun q (_ : q∈(Set.univ : Set ℝ))=>(phi_hasDerivAt q r a).hasDerivWithinAt)
    (fun q _=>show ‖phiZ q r a‖≤2*Real.exp (|a|/2) by
      rw [Real.norm_eq_abs]
      exact (phiZ_relative_bound q r a).trans (by nlinarith [phi_le_exp q r a]))
    convex_univ (Set.mem_univ z) (Set.mem_univ z')
  simpa only [Real.norm_eq_abs] using H

lemma phi_lipschitz_a (z r a : ℝ) :
    |phi z r a-phi z r 0|≤(Real.exp (|a|/2)/2)*|a| := by
  have H:=Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun q (_ : q∈Set.Icc (-|a|) |a|)=>(phi_hasDerivAt_a z r q).hasDerivWithinAt)
    (fun q hq=>show ‖phiA z r q‖≤Real.exp (|a|/2)/2 by
      rw [Real.norm_eq_abs,abs_of_nonneg (phiA_nonneg _ _ _)]
      have hq' : |q|≤|a| := abs_le.mpr hq
      have he : Real.exp (|q|/2)≤Real.exp (|a|/2) := Real.exp_le_exp.mpr (by linarith)
      exact (phiA_relative_bound z r q).trans (by linarith [phi_le_exp z r q]))
    (convex_Icc (-|a|) |a|)
    (show (0:ℝ)∈Set.Icc (-|a|) |a| by constructor <;> linarith [abs_nonneg a])
    (show a∈Set.Icc (-|a|) |a| from ⟨neg_abs_le a,le_abs_self a⟩)
  simpa only [Real.norm_eq_abs,sub_zero] using H

theorem phi_near_root (z r a : ℝ) :
    |phi z r a-SKGapCutoff.scalarVariance r|≤
      Real.exp (|a|/2)*(2*|z-r|+|a|/2) := by
  have he : phi r r 0=SKGapCutoff.scalarVariance r := by
    rw [phi_zero_diagonal,SKGapCutoff.scalarVariance_eq]
  have h1:=phi_lipschitz_z r z r a
  have h2:=phi_lipschitz_a r r a
  have h3:=abs_add_le (phi z r a-phi r r a) (phi r r a-phi r r 0)
  rw [he] at h2 h3
  have hh : phi z r a-phi r r a+(phi r r a-SKGapCutoff.scalarVariance r)=
      phi z r a-SKGapCutoff.scalarVariance r := by ring
  rw [hh] at h3
  nlinarith only [h1,h2,h3]

end SKGap.Stein

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_ImplicitLinear
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace SKGap.ImplicitLinear
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma lower_norm_of_quadratic (M : E →L[ℝ] E) {c : ℝ}
    (h : ∀v,c*‖v‖^2 ≤ ⟪v, M v⟫) (v : E) : c*‖v‖≤‖M v‖ := by
  by_cases hv : ‖v‖=0
  · simp [hv]
  have hn : 0<‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
  have H:=(h v).trans (real_inner_le_norm v (M v))
  nlinarith

lemma quadratic_perturbation (M S : E →L[ℝ] E) {c e : ℝ}
    (hS : ∀v,c*‖v‖^2 ≤ ⟪v, S v⟫) (hMS : ‖M-S‖≤e) (v : E) :
    (c-e)*‖v‖^2 ≤ ⟪v, M v⟫ := by
  have hI:=abs_real_inner_le_norm v ((M-S) v)
  have hO:=(M-S).le_opNorm v
  have hm:=mul_le_mul_of_nonneg_right hMS (norm_nonneg v)
  have hh:=mul_le_mul_of_nonneg_left (hO.trans hm) (norm_nonneg v)
  have he : ⟪v, (M-S) v⟫=⟪v, M v⟫-⟪v, S v⟫ := by simp only [sub_apply,inner_sub_right]
  rw [he] at hI
  have H := (neg_abs_le (⟪v, M v⟫-⟪v, S v⟫)).trans (le_refl _)
  nlinarith [hS v]

lemma injective_of_lower_norm (M : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (h : ∀v,c*‖v‖≤‖M v‖) : Function.Injective M := by
  intro x y hxy
  have H:=h (x-y)
  have he : M (x-y)=0 := by simp [hxy]
  rw [he,norm_zero] at H
  have hz : ‖x-y‖=0 := by nlinarith [norm_nonneg (x-y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

variable [FiniteDimensional ℝ E]

theorem exists_bounded_inverse (M S : E →L[ℝ] E) {c e : ℝ}
    (hce : e < c) (hS : ∀v,c*‖v‖^2 ≤ ⟪v, S v⟫) (hMS : ‖M-S‖≤e) :
    ∃ N : E →L[ℝ] E,M*N=1 ∧ N*M=1 ∧ ‖N‖≤(c-e)⁻¹ := by
  have hc : 0 < c-e := sub_pos.mpr hce
  have hlow : ∀v,(c-e)*‖v‖≤‖M v‖ :=
    lower_norm_of_quadratic M (quadratic_perturbation M S hS hMS)
  have hinj := injective_of_lower_norm M hc hlow
  let L : E ≃ₗ[ℝ] E := LinearEquiv.ofBijective M.toLinearMap
    ⟨hinj,LinearMap.injective_iff_surjective.mp hinj⟩
  let N : E →L[ℝ] E := L.symm.toLinearMap.toContinuousLinearMap
  have hMN : M*N=1 := by
    ext x; exact L.apply_symm_apply x
  have hNM : N*M=1 := by
    ext x; exact L.symm_apply_apply x
  refine ⟨N,hMN,hNM,N.opNorm_le_bound (inv_nonneg.mpr hc.le) ?_⟩
  intro x
  have H:=hlow (N x)
  have hx : M (N x)=x := by change (M*N) x=x; rw [hMN]; rfl
  rw [hx] at H
  exact (le_div_iff₀ hc).2 (by nlinarith) |>.trans_eq (by ring)

end SKGap.ImplicitLinear

namespace SKGap.ImplicitLinear
variable {R : Type*} [Ring R]

lemma jacobson_left (X Y N : R) (hN : (1+Y*X)*N=1) :
    (1+X*Y)*(1-X*N*Y)=1 := by
  calc
    _ = 1+X*(1-(1+Y*X)*N)*Y := by noncomm_ring
    _ = 1 := by rw [hN]; simp

lemma jacobson_right (X Y N : R) (hN : N*(1+Y*X)=1) :
    (1-X*N*Y)*(1+X*Y)=1 := by
  calc
    _ = 1+X*(1-N*(1+Y*X))*Y := by noncomm_ring
    _ = 1 := by rw [hN]; simp

end SKGap.ImplicitLinear

namespace SKGap.ImplicitLinear
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem unnormalized_inverse (X L S : E →L[ℝ] E) {c e : ℝ}
    (hce : e < c) (hS : ∀v,c*‖v‖^2 ≤ ⟪v, S v⟫)
    (hMS : ‖(1+X*L*X)-S‖≤e) :
    ∃ B : E →L[ℝ] E,(1+X*X*L)*B=1 ∧ B*(1+X*X*L)=1 ∧
      ‖B‖≤1+‖X‖^2*(c-e)⁻¹*‖L‖ := by
  obtain ⟨N,hN,hN',hNb⟩ := exists_bounded_inverse (1+X*L*X) S hce hS hMS
  let B:=1-X*N*(X*L)
  refine ⟨B,?_,?_,?_⟩
  · simpa only [B,mul_assoc] using jacobson_left X (X*L) N hN
  · simpa only [B,mul_assoc] using jacobson_right X (X*L) N hN'
  · calc
      ‖B‖ ≤ ‖(1 : E →L[ℝ] E)‖+‖X*N*(X*L)‖ := norm_sub_le _ _
      _ ≤ 1+‖X‖*‖N‖*(‖X‖*‖L‖) := by
        apply add_le_add (ContinuousLinearMap.norm_id_le)
        exact (norm_mul_le _ _).trans (mul_le_mul (norm_mul_le _ _) (norm_mul_le _ _)
          (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
      _ ≤ 1+‖X‖*(c-e)⁻¹*(‖X‖*‖L‖) := by
        gcongr
      _ = _ := by ring

omit [FiniteDimensional ℝ E] in
lemma unique_solution_of_inverse (M B : E →L[ℝ] E) (hMB : M*B=1) (hBM : B*M=1)
    (b : E) : ∃!w,M w=b := by
  refine ⟨B b,?_,?_⟩
  · change (M*B) b=b; rw [hMB]; rfl
  · intro w hw
    have := congrArg (fun f : E →L[ℝ] E=>f w) hBM
    simpa only [mul_apply_eq_comp,hw,one_apply_eq_self] using this.symm

end SKGap.ImplicitLinear

end
end

section

noncomputable section
namespace SKGap.ImplicitSystem
open SKGap.ImplicitLinear
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma rank_add_right (u v w : E) : rank u (v+w)=rank u v+rank u w := by
  ext x; simp only [rank_apply,inner_add_left,add_smul,add_apply]

lemma rank_sub_left (u v w : E) : rank (u-v) w=rank u w-rank v w := by
  ext x; simp only [rank_apply,smul_sub,sub_apply]

lemma rank_smul_left (a : ℝ) (u v : E) : rank (a • u) v=a • rank u v := by
  ext x; simp only [rank_apply,smul_apply]; module

lemma rank_norm_le (u v : E) : ‖rank u v‖≤‖u‖*‖v‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro x
  simp only [rank_apply,norm_smul,Real.norm_eq_abs]
  calc
    _ ≤ (‖v‖*‖x‖)*‖u‖ := mul_le_mul_of_nonneg_right (abs_real_inner_le_norm v x) (norm_nonneg _)
    _ = _ := by ring

lemma rank_perturbation (v ell m : E) :
    rank v ell+(2:ℝ) • rank m m=rank (v-(2:ℝ) • m) ell+(2:ℝ) • rank m (ell+m) := by
  rw [rank_sub_left,rank_smul_left,rank_add_right,smul_add]
  module

lemma rank_perturbation_bound (v ell m : E) :
    ‖rank v ell+(2:ℝ) • rank m m‖≤‖v-(2:ℝ) • m‖*‖ell‖+2*‖m‖*‖ell+m‖ := by
  rw [rank_perturbation]
  calc
    _ ≤ ‖rank (v-(2:ℝ) • m) ell‖+‖(2:ℝ) • rank m (ell+m)‖ := norm_add_le _ _
    _ ≤ ‖v-(2:ℝ) • m‖*‖ell‖+2*(‖m‖*‖ell+m‖) := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2)]
      exact add_le_add (rank_norm_le _ _) (mul_le_mul_of_nonneg_left (rank_norm_le _ _) (by norm_num))
    _ = _ := by ring

lemma normalized_difference (j χ b r : ℝ) (X J : E →L[ℝ] E) (v ell m : E) :
    (1+X*L₂ j χ r J v ell*X)-stableMatrix j b r X J m=
      (j*(χ-b)) • (X*X)+(j*r) • (X*(rank v ell+(2:ℝ) • rank m m)*X) := by
  simp only [L₂,stableMatrix,mul_add,add_mul,mul_neg,neg_mul,mul_smul_comm,
    smul_mul_assoc,mul_one,smul_add,smul_smul]
  module

lemma normalized_difference_bound (j χ b r : ℝ) (X J : E →L[ℝ] E) (v ell m : E) :
    ‖(1+X*L₂ j χ r J v ell*X)-stableMatrix j b r X J m‖≤
      |j| * |χ-b| * ‖X‖^2+|j*r| * ‖X‖^2*(‖v-(2:ℝ) • m‖*‖ell‖+2*‖m‖*‖ell+m‖) := by
  rw [normalized_difference]
  calc
    _ ≤ ‖(j*(χ-b)) • (X*X)‖+‖(j*r) • (X*(rank v ell+(2:ℝ) • rank m m)*X)‖ := norm_add_le _ _
    _ ≤ |j| * |χ-b| * (‖X‖*‖X‖)+|j*r| * (‖X‖*(‖v-(2:ℝ) • m‖*‖ell‖+2*‖m‖*‖ell+m‖)*‖X‖) := by
      simp only [norm_smul,Real.norm_eq_abs,abs_mul]
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (norm_mul_le X X) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      · apply mul_le_mul_of_nonneg_left _ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
          ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (rank_perturbation_bound v ell m) (norm_nonneg _)))
          (norm_nonneg _))
    _ = _ := by ring

lemma eliminated_equation (j χ r p : ℝ) (A J : E →L[ℝ] E) (u m t ell w : E) :
    Equations j χ r p A J u m t ell w
      (J w-(j*χ) • w-(j*(r*inner ℝ ell w+p)) • m) (r*inner ℝ ell w+p) ↔
      (1+A*L₂ j χ r J (m+t) ell) w=A (u-(j*p) • (m+t)) := by
  simp only [Equations,and_true,L₂,add_apply,smul_apply,neg_apply,one_apply_eq_self,
    mul_apply_eq_comp,rank_apply,map_add,map_sub,map_smul,map_neg]
  constructor <;> intro h <;> linear_combination (norm := module) h

variable [FiniteDimensional ℝ E]

theorem unique_implicit_solution (j χ b r p : ℝ) (X J : E →L[ℝ] E)
    (u m t ell q : E) {δ : ℝ} (hδ : 0<δ)
    (hStable : ∀v,δ*‖v‖^2 ≤ inner ℝ v (stableMatrix j b r X J q v))
    (hSmall : |j| * |χ-b| * ‖X‖^2+|j*r| * ‖X‖^2*
      (‖m+t-(2:ℝ) • q‖*‖ell‖+2*‖q‖*‖ell+q‖)≤δ/2) :
    ∃! z : E×E×ℝ,Equations j χ r p (X*X) J u m t ell z.1 z.2.1 z.2.2 := by
  have hPert := (normalized_difference_bound j χ b r X J (m+t) ell q).trans hSmall
  obtain ⟨B,hMB,hBM,hB⟩ := unnormalized_inverse X (L₂ j χ r J (m+t) ell)
    (stableMatrix j b r X J q) (by linarith : δ/2<δ) hStable hPert
  obtain ⟨w,hw,huniq⟩:=unique_solution_of_inverse (1+X*X*L₂ j χ r J (m+t) ell) B hMB hBM
    ((X*X) (u-(j*p) • (m+t)))
  let c:=r*inner ℝ ell w+p
  let y:=J w-(j*χ) • w-(j*c) • m
  have hEq : Equations j χ r p (X*X) J u m t ell w y c := by
    apply (eliminated_equation j χ r p (X*X) J u m t ell w).mpr
    simpa only [mul_assoc] using hw
  refine ⟨(w,y,c),hEq,?_⟩
  rintro ⟨w',y',c'⟩ h'
  rcases h' with ⟨hw',hy',hc'⟩
  have hwe : (1+(X*X)*L₂ j χ r J (m+t) ell) w'=(X*X) (u-(j*p) • (m+t)) := by
    apply (eliminated_equation j χ r p (X*X) J u m t ell w').mp
    refine ⟨?_,rfl,rfl⟩
    simpa only [←hc',←hy'] using hw'
  have hww : w'=w := huniq w' (by simpa only [mul_assoc] using hwe)
  have hcc : c'=c := by simpa only [hww] using hc'
  have hyy : y'=y := by simpa only [hww,hcc] using hy'
  simp only [hww,hyy,hcc]

end SKGap.ImplicitSystem

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

lemma vectorNorm_neg (v : Fin n→ℝ) : vectorNorm (-v)=vectorNorm v := by
  exact norm_neg (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))
lemma vectorNorm_tanh (z : Fin n→ℝ) : vectorNorm (fun i=>Real.tanh (z i))≤Real.sqrt n := by
  simpa only [vectorNorm_const,abs_one,one_mul] using
    (vectorNorm_mono (u:=fun i=>Real.tanh (z i)) (v:=fun _=>1)
      (fun i=>by simpa using (Real.abs_tanh_lt_one (z i)).le))
lemma vectorNorm_tanh_diff (z r : Fin n→ℝ) :
    vectorNorm (fun i=>Real.tanh (z i)-Real.tanh (r i))≤vectorNorm (z-r) :=
  vectorNorm_mono fun i=>tanh_lipschitz (r i) (z i)

lemma abs_logSlope_le_two (z r a : ℝ) : |logSlope z r a|≤2 := by
  rw [logSlope,abs_div,abs_of_pos (phi_pos z r a),div_le_iff₀ (phi_pos z r a)]
  exact phiZ_relative_bound z r a

lemma vectorNorm_logSlope (z r : Fin n→ℝ) (a : ℝ) :
    vectorNorm (fun i=>logSlope (z i) (r i) a)≤2*Real.sqrt n := by
  simpa only [vectorNorm_const,abs_of_pos (by norm_num : (0:ℝ)<2)] using
    (vectorNorm_mono (u:=fun i=>logSlope (z i) (r i) a) (v:=fun _=>2)
      (fun i=>by simpa using abs_logSlope_le_two (z i) (r i) a))

lemma vectorNorm_logSlope_near (z r : Fin n→ℝ) (a : ℝ) :
    vectorNorm (fun i=>logSlope (z i) (r i) a+Real.tanh (r i))≤3*vectorNorm (z-r) := by
  have h:=vectorNorm_mono (u:=fun i=>logSlope (z i) (r i) a+Real.tanh (r i))
    (v:=fun i=>3*(z i-r i)) (fun i=>by simpa only [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<3)] using
      (logSlope_near_diagonal (z i) (r i) a))
  apply h.trans_eq
  convert! vectorNorm_smul 3 (z-r) using 1
  all_goals try with_reducible_and_instances rfl
  norm_num

lemma phi_near_current (z r a : ℝ) {R : ℝ} (ha : |a|≤R) :
    |phi z r a-scalarVariance z|≤
      (2*Real.exp (R/2)+2)*|z-r|+(Real.exp (R/2)/2)*|a| := by
  have he:=Real.exp_le_exp.mpr (show |a|/2≤R/2 by linarith)
  have h₁:=(phi_near_root z r a).trans (mul_le_mul_of_nonneg_right he (by positivity))
  have h₂:=scalarVariance_lipschitz r z
  have h₃:=abs_sub_le (phi z r a) (scalarVariance r) (scalarVariance z)
  rw [abs_sub_comm (scalarVariance r)] at h₃
  linarith

lemma vectorNorm_phi_near_current (z r : Fin n→ℝ) (a : ℝ) {R : ℝ} (ha : |a|≤R) :
    vectorNorm (fun i=>phi (z i) (r i) a-scalarVariance (z i))≤
      (2*Real.exp (R/2)+2)*vectorNorm (z-r)+(Real.exp (R/2)/2)*|a| *Real.sqrt n := by
  let E:=Real.exp (R/2)
  have he:0≤E := (Real.exp_pos _).le
  have hmono:=vectorNorm_mono (u:=fun i=>phi (z i) (r i) a-scalarVariance (z i))
    (v:=fun i=>(2*E+2)*|z i-r i|+(E/2)*|a|) (fun i=>by
      rw [abs_of_nonneg (show 0≤(2*E+2)*|z i-r i|+(E/2)*|a| from by positivity)]
      exact phi_near_current _ _ _ ha)
  apply hmono.trans
  have ht:=vectorNorm_add ((2*E+2) • (fun i=>|z i-r i|)) (fun _=>(E/2)*|a|)
  rw [vectorNorm_smul,abs_of_nonneg (by positivity : 0≤2*E+2),
    vectorNorm_abs,vectorNorm_const,abs_of_nonneg (by positivity : 0≤(E/2)*|a|)] at ht
  exact ht

lemma normalized_mean_bound (u : Fin n→ℝ) (hn : 0<n) :
    |(∑i,u i)/(n:ℝ)|≤vectorNorm u/Real.sqrt n := by
  have hnR : (0:ℝ)<n:=Nat.cast_pos.mpr hn
  have hs : 0<Real.sqrt n:=Real.sqrt_pos.mpr hnR
  have hh:=siteMean_square (fun _=>u) (fun _=>false) hn
  change (n:ℝ)*((∑i,u i)/(n:ℝ))^2≤(vectorNorm u)^2 at hh
  apply (sq_le_sq₀ (abs_nonneg _) (div_nonneg (vectorNorm_nonneg _) hs.le)).mp
  rw [sq_abs, div_pow, div_pow, Real.sq_sqrt hnR.le]
  exact (le_div_iff₀ hnR).mpr (by simpa only [div_pow, mul_comm] using hh)

theorem implicit_coefficient_bounds (z r : Fin n→ℝ) (a : ℝ) (hn : 0<n)
    {R ρ : ℝ} (hρ : 0≤ρ) (ha : |a|≤R) (haρ : |a|≤ρ)
    (hz : vectorNorm (z-r)≤ρ*Real.sqrt n) :
    let E:=Real.exp (R/2)
    let A:=fun i=>phi (z i) (r i) a
    let ell:=fun i=>logSlope (z i) (r i) a
    let q:=fun i=>Real.tanh (z i)
    (∀i,0<A i ∧ A i≤E) ∧
    vectorNorm (A-(fun i=>scalarVariance (z i)))≤(3*E+2)*ρ*Real.sqrt n ∧
    |(∑i,A i)/(n:ℝ)-(∑i,scalarVariance (z i))/(n:ℝ)|≤(3*E+2)*ρ ∧
    vectorNorm (ell+q)≤4*ρ*Real.sqrt n ∧
    vectorNorm ell≤2*Real.sqrt n ∧ vectorNorm q≤Real.sqrt n := by
  dsimp only
  have hnR : (0:ℝ)<n:=Nat.cast_pos.mpr hn
  have hs : 0<Real.sqrt n:=Real.sqrt_pos.mpr hnR
  have he:0<Real.exp (R/2):=Real.exp_pos _
  have hA : vectorNorm (fun i=>phi (z i) (r i) a-scalarVariance (z i))≤
      (3*Real.exp (R/2)+2)*ρ*Real.sqrt n := by
    apply (vectorNorm_phi_near_current z r a ha).trans
    have h₁:=mul_le_mul_of_nonneg_left hz (by positivity : 0≤2*Real.exp (R/2)+2)
    have h₂:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left haρ
      (by positivity : 0≤Real.exp (R/2)/2)) hs.le
    nlinarith only [h₁,h₂,mul_nonneg he.le (mul_nonneg hρ hs.le)]
  refine ⟨fun i=>⟨phi_pos _ _ _,(phi_le_exp ..).trans (Real.exp_le_exp.mpr (by linarith))⟩,hA,?_,?_,
    vectorNorm_logSlope z r a,vectorNorm_tanh z⟩
  · rw [←sub_div,←Finset.sum_sub_distrib]
    exact (normalized_mean_bound _ hn).trans ((div_le_div_of_nonneg_right hA hs.le).trans_eq (by field_simp))
  · have h₁:=vectorNorm_logSlope_near z r a
    have h₂:=vectorNorm_tanh_diff z r
    have h₃:=vectorNorm_add (fun i=>logSlope (z i) (r i) a+Real.tanh (r i))
      (fun i=>Real.tanh (z i)-Real.tanh (r i))
    have heq : (fun i=>logSlope (z i) (r i) a+Real.tanh (r i))+
        (fun i=>Real.tanh (z i)-Real.tanh (r i))=
        (fun i=>logSlope (z i) (r i) a)+(fun i=>Real.tanh (z i)) := by ext i; dsimp; ring
    rw [heq] at h₃
    nlinarith only [h₁,h₂,h₃,hz]

end SKGapCutoff.Recipe

end
end

section

noncomputable section
namespace SKGap.ImplicitSystem
open SKGap.ImplicitLinear
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma eliminated_rhs_bound (A : E →L[ℝ] E) (j p : ℝ) (u m t : E) :
    ‖A (u-(j*p) • (m+t))‖≤‖A‖*(‖u‖+|j| *|p| *(‖m‖+‖t‖)) := by
  calc
    _ ≤ ‖A‖*‖u-(j*p) • (m+t)‖ := A.le_opNorm _
    _ ≤ ‖A‖*(‖u‖+‖(j*p) • (m+t)‖) := mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
    _ ≤ _ := by
      simp only [norm_smul,Real.norm_eq_abs,abs_mul]
      exact mul_le_mul_of_nonneg_left (add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left (norm_add_le m t) (mul_nonneg (abs_nonneg _) (abs_nonneg _)))) (norm_nonneg _)

lemma implicit_scalar_size (r p : ℝ) (ell w : E) :
    |r*inner ℝ ell w+p|≤|r| *‖ell‖*‖w‖+|p| := by
  calc
    _ ≤ |r*inner ℝ ell w|+|p| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul]
      nlinarith only [mul_le_mul_of_nonneg_left (abs_real_inner_le_norm ell w) (abs_nonneg r)]

lemma implicit_field_size (J : E →L[ℝ] E) (j χ c : ℝ) (w m : E) :
    ‖J w-(j*χ) • w-(j*c) • m‖≤(‖J‖+|j*χ|)*‖w‖+|j| *|c| *‖m‖ := by
  calc
    _ ≤ ‖J w-(j*χ) • w‖+‖(j*c) • m‖ := norm_sub_le _ _
    _ ≤ ‖J w‖+‖(j*χ) • w‖+‖(j*c) • m‖ := add_le_add (norm_sub_le _ _) (le_refl _)
    _ ≤ _ := by
      simp only [norm_smul,Real.norm_eq_abs,abs_mul]
      nlinarith only [J.le_opNorm w]

variable [FiniteDimensional ℝ E]

theorem implicit_size_bounds (j χ b r p : ℝ) (X J : E →L[ℝ] E)
    (u m t ell q w y : E) (c : ℝ) {δ : ℝ} (hδ : 0<δ)
    (hStable : ∀v,δ*‖v‖^2 ≤ inner ℝ v (stableMatrix j b r X J q v))
    (hSmall : |j| *|χ-b| *‖X‖^2+|j*r| *‖X‖^2*
      (‖m+t-(2:ℝ) • q‖*‖ell‖+2*‖q‖*‖ell+q‖)≤δ/2)
    (hEq : Equations j χ r p (X*X) J u m t ell w y c) :
    let W := (1+‖X‖^2*(δ/2)⁻¹*‖L₂ j χ r J (m+t) ell‖)*
      ‖X‖^2*(‖u‖+|j| *|p| *(‖m‖+‖t‖))
    ‖w‖≤W ∧ |c|≤|r| *‖ell‖*W+|p| ∧
      ‖y‖≤(‖J‖+|j*χ|)*W+|j| *(|r| *‖ell‖*W+|p|)*‖m‖ := by
  dsimp only
  let W := (1+‖X‖^2*(δ/2)⁻¹*‖L₂ j χ r J (m+t) ell‖)*
      ‖X‖^2*(‖u‖+|j| *|p| *(‖m‖+‖t‖))
  have hPert := (normalized_difference_bound j χ b r X J (m+t) ell q).trans hSmall
  obtain ⟨B,hMB,hBM,hB⟩ := unnormalized_inverse X (L₂ j χ r J (m+t) ell)
    (stableMatrix j b r X J q) (by linarith : δ/2<δ) hStable hPert
  have hw : (1+X*X*L₂ j χ r J (m+t) ell) w=(X*X) (u-(j*p) • (m+t)) := by
    apply (eliminated_equation j χ r p (X*X) J u m t ell w).mp
    rcases hEq with ⟨hw,hy,hc⟩
    refine ⟨?_,rfl,rfl⟩
    simpa only [←hc,←hy] using hw
  have hform : w=B ((X*X) (u-(j*p) • (m+t))) := by
    rw [←hw]
    change w=(B*(1+X*X*L₂ j χ r J (m+t) ell)) w
    rw [hBM]; rfl
  have hBB : ‖B‖≤1+‖X‖^2*(δ/2)⁻¹*‖L₂ j χ r J (m+t) ell‖ := by
    convert hB using 2
    all_goals try with_reducible_and_instances rfl
    congr 2
    ring
  have hwB : ‖w‖≤W := by
    calc
      ‖w‖=‖B ((X*X) (u-(j*p) • (m+t)))‖ := congrArg norm hform
      _ ≤ ‖B‖*‖(X*X) (u-(j*p) • (m+t))‖ := B.le_opNorm _
      _ ≤ ‖B‖*(‖X*X‖*(‖u‖+|j| *|p| *(‖m‖+‖t‖))) :=
        mul_le_mul_of_nonneg_left (eliminated_rhs_bound (X*X) j p u m t) (norm_nonneg _)
      _ ≤ W := by
        dsimp [W]
        have hX : ‖X*X‖≤‖X‖^2 := by simpa only [pow_two] using norm_mul_le X X
        have h0 : 0≤‖u‖+|j| *|p| *(‖m‖+‖t‖) := by positivity
        have hK : 0≤1+‖X‖^2*(δ/2)⁻¹*‖L₂ j χ r J (m+t) ell‖ := by positivity
        calc
          _ ≤ (1+‖X‖^2*(δ/2)⁻¹*‖L₂ j χ r J (m+t) ell‖)*
              (‖X‖^2*(‖u‖+|j| *|p| *(‖m‖+‖t‖))) :=
            mul_le_mul hBB (mul_le_mul_of_nonneg_right hX h0) (by positivity) hK
          _ = _ := by ring
  have hcB : |c|≤|r| *‖ell‖*W+|p| := by
    rw [hEq.2.2]
    exact (implicit_scalar_size r p ell w).trans
      (add_le_add (mul_le_mul_of_nonneg_left hwB (mul_nonneg (abs_nonneg _) (norm_nonneg _))) (le_refl _))
  refine ⟨hwB,hcB,?_⟩
  rw [hEq.2.1]
  apply (implicit_field_size J j χ c w m).trans
  exact add_le_add (mul_le_mul_of_nonneg_left hwB (by positivity))
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcB (abs_nonneg j)) (norm_nonneg m))

end SKGap.ImplicitSystem

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_ImplicitPerturb
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary SKGap.ImplicitSystem
variable {n : ℕ}

lemma vectorNorm_implicit_rank (z r m : Fin n→ℝ) {ρ : ℝ}
    (hz : vectorNorm (z-r)≤ρ*Real.sqrt n)
    (hm : vectorNorm (m-(fun i=>Real.tanh (r i)))≤ρ*Real.sqrt n) :
    vectorNorm (m+(fun i=>Real.tanh (r i))-(2:ℝ) • (fun i=>Real.tanh (z i)))≤
      3*ρ*Real.sqrt n := by
  let q:=fun i=>Real.tanh (z i)
  let t:=fun i=>Real.tanh (r i)
  have ht:=vectorNorm_tanh_diff z r
  have ht' : vectorNorm (t-q)≤ρ*Real.sqrt n := by
    have he : t-q= -(q-t) := by ext i; dsimp; ring
    rw [he,vectorNorm_neg]
    exact ht.trans hz
  have hh:=vectorNorm_add (m-t) ((2:ℝ) • (t-q))
  rw [vectorNorm_smul,abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
  have he : (m-t)+(2:ℝ) • (t-q)=m+t-(2:ℝ) • q := by ext i; dsimp; ring
  rw [he] at hh
  exact hh.trans (by nlinarith only [hm,ht'])

theorem implicit_normalized_perturbation (z r m : Fin n→ℝ) (a j : ℝ)
    (X : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hn : 0<n) {R ρ : ℝ} (hρ : 0≤ρ) (ha : |a|≤R) (haρ : |a|≤ρ)
    (hz : vectorNorm (z-r)≤ρ*Real.sqrt n)
    (hm : vectorNorm (m-(fun i=>Real.tanh (r i)))≤ρ*Real.sqrt n)
    (hX : ‖X‖^2≤Real.exp (R/2)) :
    let χ:=(∑i,phi (z i) (r i) a)/(n:ℝ)
    let b:=(∑i,scalarVariance (z i))/(n:ℝ)
    let ell:EuclideanSpace ℝ (Fin n):=WithLp.toLp 2 (fun i=>logSlope (z i) (r i) a)
    let q:EuclideanSpace ℝ (Fin n):=WithLp.toLp 2 (fun i=>Real.tanh (z i))
    let t:EuclideanSpace ℝ (Fin n):=WithLp.toLp 2 (fun i=>Real.tanh (r i))
    let M:EuclideanSpace ℝ (Fin n):=WithLp.toLp 2 m
    |j| *|χ-b| *‖X‖^2+|j*(n:ℝ)⁻¹| *‖X‖^2*
      (‖M+t-(2:ℝ) • q‖*‖ell‖+2*‖q‖*‖ell+q‖)≤
        |j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)*ρ := by
  dsimp only
  obtain ⟨hA,hAv,hχ,hEllq,hEll,hq⟩:=implicit_coefficient_bounds z r a hn hρ ha haρ hz
  have hnR : (0:ℝ)<n:=Nat.cast_pos.mpr hn
  have hs : 0≤Real.sqrt n:=Real.sqrt_nonneg _
  have he:0≤Real.exp (R/2):=(Real.exp_pos _).le
  have hv:=vectorNorm_implicit_rank z r m hz hm
  have hbr : vectorNorm (m+(fun i=>Real.tanh (r i))-(2:ℝ) • (fun i=>Real.tanh (z i)))*
      vectorNorm (fun i=>logSlope (z i) (r i) a)+
      2*vectorNorm (fun i=>Real.tanh (z i))*
      vectorNorm ((fun i=>logSlope (z i) (r i) a)+(fun i=>Real.tanh (z i)))≤14*ρ*(n:ℝ) := by
    have h₁:=mul_le_mul hv hEll (vectorNorm_nonneg _) (by positivity : 0≤3*ρ*Real.sqrt n)
    have h₂:=mul_le_mul (mul_le_mul_of_nonneg_left hq (by norm_num : (0:ℝ)≤2)) hEllq
      (vectorNorm_nonneg _) (by positivity : 0≤2*Real.sqrt n)
    apply (add_le_add h₁ h₂).trans_eq
    calc
      _ = 14*ρ*(Real.sqrt n)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt hnR.le]
  change |j| *|_| *‖X‖^2+|j*(n:ℝ)⁻¹| *‖X‖^2*
    (vectorNorm _*vectorNorm _+2*vectorNorm _*vectorNorm _)≤_
  calc
    _ ≤ |j| *((3*Real.exp (R/2)+2)*ρ)*Real.exp (R/2)+
        |j*(n:ℝ)⁻¹| *Real.exp (R/2)*(14*ρ*(n:ℝ)) := by
      apply add_le_add
      · exact mul_le_mul (mul_le_mul_of_nonneg_left hχ (abs_nonneg _)) hX (sq_nonneg _) (by positivity)
      · exact mul_le_mul (mul_le_mul_of_nonneg_left hX (abs_nonneg _)) hbr
          (add_nonneg (mul_nonneg (vectorNorm_nonneg _) (vectorNorm_nonneg _))
            (mul_nonneg (mul_nonneg (by norm_num) (vectorNorm_nonneg _)) (vectorNorm_nonneg _))) (by positivity)
    _ = _ := by
      rw [abs_mul,abs_inv,abs_of_pos hnR]
      field_simp
      ring

lemma implicit_rho_threshold (j R δ ρ : ℝ) (hδ : 0<δ)
    (hρ : ρ≤δ/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1))) :
    |j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)*ρ≤δ/2 := by
  let K:=|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)
  have hK : 0≤K := by dsimp [K]; positivity
  have hp : 0<2*(K+1) := by positivity
  apply (mul_le_mul_of_nonneg_left hρ hK).trans
  change K*(δ/(2*(K+1)))≤δ/2
  apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  rw [mul_assoc,div_mul_eq_mul_div,←mul_div_assoc]
  apply (div_le_iff₀ hp).mpr
  nlinarith

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary SKGap.ImplicitSystem Matrix
variable {n : ℕ}

lemma phiSqrt_square (z r : Fin n→ℝ) (a : ℝ) :
    phiSqrt z r a*phiSqrt z r a=phiDiagonal z r a := by
  rw [phiSqrt,phiDiagonal,←map_mul,diagonal_mul_diagonal]
  congr 2
  ext i
  exact Real.mul_self_sqrt (phi_pos _ _ _).le

lemma phiSqrt_bound (z r : Fin n→ℝ) (a : ℝ) {R : ℝ} (ha : |a|≤R) :
    ‖phiSqrt z r a‖^2≤Real.exp (R/2) := by
  have he : 0≤Real.exp (R/2):=(Real.exp_pos _).le
  have hh : ‖phiSqrt z r a‖≤Real.sqrt (Real.exp (R/2)) := by
    apply SKGap.opNorm_diagonal_le (Real.sqrt_nonneg _)
    intro i
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt ((phi_le_exp ..).trans (Real.exp_le_exp.mpr (by linarith)))
  exact (pow_le_pow_left₀ (norm_nonneg _) hh 2).trans_eq (Real.sq_sqrt he)

theorem literal_implicit_exists_unique (z r m : Fin n→ℝ) (a j p : ℝ)
    (J : Euclid n→L[ℝ]Euclid n) (u : Euclid n) (hn : 0<n)
    {R ρ δ : ℝ} (hδ : 0<δ) (hρ : 0≤ρ) (ha : |a|≤R) (haρ : |a|≤ρ)
    (hz : vectorNorm (z-r)≤ρ*Real.sqrt n)
    (hm : vectorNorm (m-(fun i=>Real.tanh (r i)))≤ρ*Real.sqrt n)
    (hρsmall : ρ≤δ/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1)))
    (hStable : ∀v,δ*‖v‖^2 ≤ inner ℝ v
      (stableMatrix j ((∑i,scalarVariance (z i))/(n:ℝ)) (n:ℝ)⁻¹
        (phiSqrt z r a) J (WithLp.toLp 2 (fun i=>Real.tanh (z i))) v)) :
    ∃! sol : Euclid n×Euclid n×ℝ,
      Equations j ((∑i,phi (z i) (r i) a)/(n:ℝ)) (n:ℝ)⁻¹ p
        (phiDiagonal z r a) J u (WithLp.toLp 2 m)
        (WithLp.toLp 2 (fun i=>Real.tanh (r i)))
        (WithLp.toLp 2 (fun i=>logSlope (z i) (r i) a)) sol.1 sol.2.1 sol.2.2 := by
  have hSmall:=(implicit_normalized_perturbation z r m a j (phiSqrt z r a) hn hρ ha haρ hz hm
    (phiSqrt_bound z r a ha)).trans (implicit_rho_threshold j R δ ρ hδ hρsmall)
  have H:=unique_implicit_solution j ((∑i,phi (z i) (r i) a)/(n:ℝ))
    ((∑i,scalarVariance (z i))/(n:ℝ)) (n:ℝ)⁻¹ p (phiSqrt z r a) J u
    (WithLp.toLp 2 m) (WithLp.toLp 2 (fun i=>Real.tanh (r i)))
    (WithLp.toLp 2 (fun i=>logSlope (z i) (r i) a))
    (WithLp.toLp 2 (fun i=>Real.tanh (z i))) hδ hStable hSmall
  simpa only [phiSqrt_square] using H

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

lemma ratio_dz_phi (f : KernelExpr) (z r a : ℝ) :
    phi z r a*((RatioExpr.kernel f).d .z).eval z r a=
      f.dz.eval z r a-logSlope z r a*f.eval z r a := by
  change phi z r a*(f.dz.eval z r a/phi z r a+
    -1*(f.eval z r a/phi z r a*(phiExpr.dz.eval z r a/phi z r a)))=_
  rw [phiExpr_dz,logSlope]
  field_simp [(phi_pos z r a).ne']
  ring

lemma initialP_ratio (f : KernelExpr) (z : VectorFields n) (a : Spin n→ℝ) (r e : Fin n→ℝ) :
    initialP f z a r e=fun x i=>phi (z x i) (r i) (a x)*
      (((RatioExpr.kernel f).d .z).eval (z x i) (r i) (a x)*e i) := by
  ext x i
  rw [←mul_assoc,ratio_dz_phi]
  rfl

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary
variable {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma fixed_root_ratio_regular (f : RatioExpr) (H : ι→VectorFields n)
    (θ : κ→Spin n→ℝ) (x : Spin n) (l : ι) (α : κ) (r : Fin n→ℝ) :
    SegmentRegular H θ (fun i u=>eval3 f.eval (phiSelect l α u+(0,(r i,0))))
      (fun i u=>(f.gradient (phiSelect l α u+(0,(r i,0)))).comp (phiSelect l α)) x
      (f.dBudget+f.ddBudget) := by
  have h:=phi_ratio_segmentRegular f H θ x (phiSelect l α) (fun i=>(0,(r i,0)))
  apply h.mono
  have h1:=phiSelect_norm l α
  have h2:=pow_le_pow_left₀ (norm_nonneg (phiSelect l α)) h1 2
  simpa only [mul_one,one_pow] using add_le_add
    (mul_le_mul_of_nonneg_left h1 f.dBudget_nonneg)
    (mul_le_mul_of_nonneg_left h2 f.ddBudget_nonneg)

lemma SegmentRegular.coefficientBound {H : ι→VectorFields n} {θ : κ→Spin n→ℝ}
    {F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ}
    {F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ}
    {x : Spin n} {L A T : ℝ} (h : SegmentRegular H θ F F' x L)
    (hA : 0≤A) (hT : 0≤T) (ha : ∀i,|F i (localArgs H θ x i)|≤A)
    (hD : (∑l,SKGap.opNorm (derivativeMatrix (H l) x))+(∑α,‖derivativeVector (θ α) x‖)≤T) :
    CoefficientBound (coefficient H θ F) x A (L*T) := by
  refine ⟨hA,mul_nonneg h.nonneg hT,ha,?_⟩
  intro i
  have hr:=(coefficient_row_bound H θ F F' x i h.nonneg (h.deriv i) (h.bound i)).trans
    (mul_le_mul_of_nonneg_left hD h.nonneg)
  simpa only [vectorNorm_sq] using pow_le_pow_left₀ (vectorNorm_nonneg _) hr 2

lemma fixed_root_kernel_coefficientBound (f : KernelExpr) (H : ι→VectorFields n)
    (θ : κ→Spin n→ℝ) (x : Spin n) (l : ι) (α : κ) (r : Fin n→ℝ)
    {R T : ℝ} (hT : 0≤T) (hx : |θ α x|≤R) (hf : ∀k,|θ α (flip x k)|≤R)
    (hD : (∑l,SKGap.opNorm (derivativeMatrix (H l) x))+(∑α,‖derivativeVector (θ α) x‖)≤T) :
    CoefficientBound (fun y i=>f.eval (H l y i) (r i) (θ α y)) x
      (f.mass*Real.exp (R/2)) ((f.dBudget R+f.ddBudget R)*T) := by
  have h:=fixed_root_kernel_regular f H θ x l α r R hx hf
  have hb:=h.coefficientBound (mul_nonneg f.mass_nonneg (Real.exp_pos _).le) hT
    (fun i=>f.absolute_bound (R:=R) (x:=phiSelect l α (localArgs H θ x i)+(0,(r i,0)))
      (by simpa [strip,phiSelect,localArgs] using hx)) hD
  simp only [eval3,phiSelect_apply,Prod.fst_add,Prod.snd_add,zero_add,add_zero] at hb
  exact hb

lemma fixed_root_ratio_coefficientBound (f : RatioExpr) (H : ι→VectorFields n)
    (θ : κ→Spin n→ℝ) (x : Spin n) (l : ι) (α : κ) (r : Fin n→ℝ)
    {T : ℝ} (hT : 0≤T)
    (hD : (∑l,SKGap.opNorm (derivativeMatrix (H l) x))+(∑α,‖derivativeVector (θ α) x‖)≤T) :
    CoefficientBound (fun y i=>f.eval (H l y i) (r i) (θ α y)) x
      f.mass ((f.dBudget+f.ddBudget)*T) := by
  have h:=fixed_root_ratio_regular f H θ x l α r
  have hb:=h.coefficientBound f.mass_nonneg hT (fun i=>f.bounded _ _ _) hD
  simp only [eval3,phiSelect_apply,Prod.fst_add,Prod.snd_add,zero_add,add_zero] at hb
  exact hb
end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary SKGap.ImplicitSystem
variable {n : ℕ}

lemma kernelSmallBudget_nonneg (f : KernelExpr) (R T : ℝ) (hT : 0≤T) :
    0≤kernelSmallBudget f R T := by
  exact add_nonneg (mul_nonneg f.mass_nonneg (Real.exp_pos _).le)
    (mul_nonneg (by norm_num) (mul_nonneg (add_nonneg (f.dBudget_nonneg _) (f.ddBudget_nonneg _)) hT))
lemma ratioSmallBudget_nonneg (f : RatioExpr) (T : ℝ) (hT : 0≤T) :
    0 ≤ ratioSmallBudget f T := by
  exact add_nonneg f.mass_nonneg
    (mul_nonneg (by norm_num) (mul_nonneg (add_nonneg f.dBudget_nonneg f.ddBudget_nonneg) hT))

lemma initial_kernel_bound (f : KernelExpr) (z : VectorFields n) (a : Spin n→ℝ)
    (r : Fin n→ℝ) (x : Spin n) {R T : ℝ} (hT : 0≤T)
    (ha : |a x|≤R) (haf : ∀k,|a (flip x k)|≤R)
    (hD : SKGap.opNorm (derivativeMatrix z x)+‖derivativeVector a x‖≤T) :
    CoefficientBound (fun v i=>f.eval (z v i) (r i) (a v)) x
      (f.mass*Real.exp (R/2)) ((f.dBudget R+f.ddBudget R)*T) := by
  apply fixed_root_kernel_coefficientBound f (fun _ : Unit=>z) (fun _ : Unit=>a) x () () r hT ha haf
  simpa only [Fintype.sum_unique] using hD

lemma initial_ratio_bound (f : RatioExpr) (z : VectorFields n) (a : Spin n→ℝ)
    (r : Fin n→ℝ) (x : Spin n) {T : ℝ} (hT : 0≤T)
    (hD : SKGap.opNorm (derivativeMatrix z x)+‖derivativeVector a x‖≤T) :
    CoefficientBound (fun v i=>f.eval (z v i) (r i) (a v)) x
      f.mass ((f.dBudget+f.ddBudget)*T) := by
  apply fixed_root_ratio_coefficientBound f (fun _ : Unit=>z) (fun _ : Unit=>a) x () () r hT
  simpa only [Fintype.sum_unique] using hD

lemma initialU_small (f : KernelExpr) (z : VectorFields n) (a : Spin n→ℝ)
    (r e : Fin n→ℝ) (x : Spin n) {T : ℝ} (hT : 0≤T) (he : vectorNorm e≤1)
    (hD : SKGap.opNorm (derivativeMatrix z x)+‖derivativeVector a x‖≤T) :
    SmallBound (initialU f z a r e) x (ratioSmallBudget (.kernel f) T) := by
  have H:=(initial_ratio_bound (.kernel f) z a r x hT hD).small_product ((SmallBound.seed e x).mono he)
  simp only [one_mul] at H
  convert! H using 1
  all_goals try with_reducible_and_instances rfl

lemma initialP_small (f : KernelExpr) (z : VectorFields n) (a : Spin n→ℝ)
    (r e : Fin n→ℝ) (x : Spin n) {R T : ℝ} (hT : 0≤T) (he : vectorNorm e≤1)
    (ha : |a x|≤R) (haf : ∀k,|a (flip x k)|≤R)
    (hD : SKGap.opNorm (derivativeMatrix z x)+‖derivativeVector a x‖≤T) :
    SmallBound (initialP f z a r e) x
      (ratioSmallBudget ((RatioExpr.kernel f).d .z) T*kernelSmallBudget phiExpr R T) := by
  have hu:=(initial_ratio_bound ((RatioExpr.kernel f).d .z) z a r x hT hD).small_product ((SmallBound.seed e x).mono he)
  simp only [one_mul] at hu
  have hp:=(initial_kernel_bound phiExpr z a r x hT ha haf hD).small_product hu
  rw [initialP_ratio]
  convert! hp using 1
  all_goals try with_reducible_and_instances rfl
  ext v i
  rw [phiExpr,KernelExpr.eval,moment_base]

lemma scaledMean_norm (hn : 0<n) (U : VectorFields n) (x : Spin n) {C : ℝ}
    (hU : SmallBound U x C) :
    Real.sqrt (n:ℝ)*|siteMean U x|≤C ∧
      Real.sqrt (n:ℝ)*‖derivativeVector (siteMean U) x‖≤C := by
  constructor
  · have H:=scaledMean_size hn U x hU.nonneg hU.size
    simpa only [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)] using H
  · apply nonneg_le_nonneg_of_sq_le_sq hU.nonneg
    simp only [←sq]
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg n)]
    exact siteMean_derivative_square_bound hn ((Primary.opNorm_le_frobenius _).trans hU.derivative)

lemma logSlope_ratio (z r a : ℝ) :
    logSlope z r a=(RatioExpr.kernel phiExpr.dz).eval z r a := by
  rw [RatioExpr.eval,phiExpr_dz,logSlope]

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_ImplicitFlip
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace SKGap.ImplicitSystem
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma equations_balance (j χ r p : ℝ) (A J : E →L[ℝ] E) (u m t ell w y : E) (c : ℝ)
    (h : Equations j χ r p A J u m t ell w y c) :
    w=A (u+J w-(j*χ) • w-(j*c) • (m+t)) := by
  rcases h with ⟨hw,hy,hc⟩
  calc
    w=A (u+y-(j*c) • t) := hw
    _=A (u+J w-(j*χ) • w-(j*c) • (m+t)) := by
      rw [hy]
      congr 1
      module

theorem implicit_difference_equation (j χ χ' r p p' : ℝ)
    (A A' J : E →L[ℝ] E) (u u' m m' t ell ell' w w' y y' : E) (c c' : ℝ)
    (h : Equations j χ r p A J u m t ell w y c)
    (h' : Equations j χ' r p' A' J u' m' t ell' w' y' c') :
    (1+A'*L₂ j χ' r J (m'+t) ell') (w-w')=
      (A-A') (u+J w-(j*χ) • w-(j*c) • (m+t))+
      A' (u-u')-(j*(χ-χ')) • A' w-(j*c) • A' (m-m')-
      (j*(r*inner ℝ (ell-ell') w+(p-p'))) • A' (m'+t) := by
  have hw:=equations_balance j χ r p A J u m t ell w y c h
  have hw':=equations_balance j χ' r p' A' J u' m' t ell' w' y' c' h'
  have hc:=h.2.2
  have hc':=h'.2.2
  simp only [L₂,add_apply,sub_apply,smul_apply,neg_apply,one_apply_eq_self,
    mul_apply_eq_comp,rank_apply,map_add,map_sub,map_smul,map_neg,inner_sub_left] at hw hw' ⊢
  rw [hc] at hw ⊢
  rw [hc'] at hw'
  linear_combination (norm := module) hw-hw'

theorem implicit_scaled_difference (s j χ χ' r p p' : ℝ)
    (A A' J : E →L[ℝ] E) (u u' m m' t ell ell' w w' y y' : E) (c c' : ℝ)
    (h : Equations j χ r p A J u m t ell w y c)
    (h' : Equations j χ' r p' A' J u' m' t ell' w' y' c') :
    (1+A'*L₂ j χ' r J (m'+t) ell') (s • (w-w'))=
      (s • (A-A')) (u+J w-(j*χ) • w-(j*c) • (m+t))+
      A' (s • (u-u'))-(j*(s*(χ-χ'))) • A' w-(j*c) • A' (s • (m-m'))-
      (j*(r*inner ℝ (s • (ell-ell')) w+s*(p-p'))) • A' (m'+t) := by
  have H:=congrArg (fun x:E=>s • x)
    (implicit_difference_equation j χ χ' r p p' A A' J u u' m m' t ell ell' w w' y y' c c' h h')
  simp only [map_smul,smul_apply,real_inner_smul_left] at H ⊢
  linear_combination (norm := module) H

lemma implicit_scalar_difference (s r p p' : ℝ) (ell ell' w w' : E) :
    s*(r*inner ℝ ell w+p-(r*inner ℝ ell' w'+p'))=
      r*inner ℝ (s • (ell-ell')) w+s*(p-p')+
        r*inner ℝ ell' (s • (w-w')) := by
  simp only [real_inner_smul_left,real_inner_smul_right,inner_sub_left,inner_sub_right]
  ring

end SKGap.ImplicitSystem

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.ImplicitSystem
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι]

omit [InnerProductSpace ℝ E] in
lemma columnNorm_nonneg (V : ι→E) : 0 ≤ columnNorm V := norm_nonneg _
omit [InnerProductSpace ℝ E] in
lemma columnNorm_sq (V : ι→E) : columnNorm V^2=∑i,‖V i‖^2 := by
  exact PiLp.norm_sq_eq_of_L2 (fun _ : ι=>E) (WithLp.toLp 2 V : PiLp 2 (fun _ : ι=>E))
omit [InnerProductSpace ℝ E] in
lemma columnNorm_add (U V : ι→E) : columnNorm (U+V) ≤ columnNorm U+columnNorm V :=
  norm_add_le (WithLp.toLp 2 U : PiLp 2 (fun _ : ι=>E)) (WithLp.toLp 2 V)
omit [InnerProductSpace ℝ E] in
lemma columnNorm_neg (V : ι→E) : columnNorm (-V)=columnNorm V := norm_neg _
omit [InnerProductSpace ℝ E] in
lemma columnNorm_sub (U V : ι→E) : columnNorm (U-V) ≤ columnNorm U+columnNorm V := by
  simpa only [sub_eq_add_neg,columnNorm_neg] using columnNorm_add U (-V)
lemma columnNorm_smul (a : ℝ) (V : ι→E) : columnNorm (a • V)=|a| *columnNorm V :=
  norm_smul a (WithLp.toLp 2 V : PiLp 2 (fun _ : ι=>E))
omit [InnerProductSpace ℝ E] in
lemma columnNorm_bound {U V : ι→E} {C : ℝ} (hC : 0≤C)
    (h : ∀i,‖U i‖≤C*‖V i‖) : columnNorm U≤C*columnNorm V := by
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hC (columnNorm_nonneg _))
  simp only [←sq,columnNorm_sq,mul_pow,Finset.mul_sum]
  exact Finset.sum_le_sum fun i _=>by simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg (U i)) (h i) 2
lemma columnNorm_operator (A : ι→E→L[ℝ]E) (V : ι→E) {C : ℝ}
    (hC : 0≤C) (hA : ∀i,‖A i‖≤C) :
    columnNorm (fun i=>A i (V i))≤C*columnNorm V := by
  apply columnNorm_bound hC
  intro i; exact ((A i).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hA i) (norm_nonneg _))
lemma columnNorm_vector_scalar (V : ι→E) (a : ι→ℝ) {C : ℝ}
    (hC : 0≤C) (hV : ∀i,‖V i‖≤C) :
    columnNorm (fun i=>a i • V i)≤C*columnNorm a := by
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hC (columnNorm_nonneg _))
  simp only [←sq,columnNorm_sq,norm_smul,Real.norm_eq_abs,mul_pow,Finset.mul_sum]
  exact Finset.sum_le_sum fun i _=>by
    have h:=pow_le_pow_left₀ (norm_nonneg (V i)) (hV i) 2
    nlinarith only [mul_le_mul_of_nonneg_left h (sq_nonneg |a i|)]

omit [InnerProductSpace ℝ E] in
lemma columnNorm_add_sub_sub_sub (a b c d e : ι→E) :
    columnNorm (a+b-c-d-e) ≤ columnNorm a+columnNorm b+columnNorm c+columnNorm d+columnNorm e := by
  have h₁:=columnNorm_add a b
  have h₂:=columnNorm_sub (a+b) c
  have h₃:=columnNorm_sub (a+b-c) d
  have h₄:=columnNorm_sub (a+b-c-d) e
  linarith

variable [FiniteDimensional ℝ E]

lemma column_inverse_estimate (X L S : ι→E→L[ℝ]E) (U V : ι→E)
    {δ X₀ L₀ : ℝ} (hδ : 0<δ) (hX₀ : 0≤X₀) (hL₀ : 0≤L₀)
    (hX : ∀i,‖X i‖≤X₀) (hL : ∀i,‖L i‖≤L₀)
    (hS : ∀i v,δ*‖v‖^2≤ inner ℝ v (S i v))
    (hPert : ∀i,‖(1+X i*L i*X i)-S i‖≤δ/2)
    (hEq : ∀i,(1+X i*X i*L i) (U i)=V i) :
    columnNorm U≤(1+X₀^2*(δ/2)⁻¹*L₀)*columnNorm V := by
  apply columnNorm_bound (by positivity)
  intro i
  obtain ⟨B,hMB,hBM,hB⟩:=SKGap.ImplicitLinear.unnormalized_inverse (X i) (L i) (S i)
    (by linarith : δ/2<δ) (hS i) (hPert i)
  have he : U i=B (V i) := by
    rw [←hEq i]
    change U i=(B*(1+X i*X i*L i)) (U i)
    rw [hBM]; rfl
  rw [he]
  apply (B.le_opNorm _).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply hB.trans
  have hX2 : ‖X i‖^2≤X₀^2 := (sq_le_sq₀ (norm_nonneg _) hX₀).mpr (hX i)
  have hinv : 0≤(δ-δ/2)⁻¹ := inv_nonneg.mpr (by linarith)
  calc
    _ ≤ 1+X₀^2*(δ-δ/2)⁻¹*L₀ := add_le_add le_rfl
      (mul_le_mul (mul_le_mul_of_nonneg_right hX2 hinv) (hL i) (norm_nonneg _) (by positivity))
    _ = _ := by congr 2; ring

theorem implicit_columns_bound (j χ r p : ℝ) (X J : E→L[ℝ]E)
    (u m t ell w y : E) (c : ℝ)
    (s χ' p' c' : ι→ℝ) (X' : ι→E→L[ℝ]E) (u' m' ell' w' y' q' : ι→E) (b' : ι→ℝ)
    (h : Equations j χ r p (X*X) J u m t ell w y c)
    (h' : ∀i,Equations j (χ' i) r (p' i) (X' i*X' i) J (u' i) (m' i) t (ell' i) (w' i) (y' i) (c' i))
    {δ X₀ L₀ : ℝ} (hδ : 0<δ) (hX₀ : 0≤X₀) (hL₀ : 0≤L₀)
    (hX : ∀i,‖X' i‖≤X₀) (hL : ∀i,‖L₂ j (χ' i) r J (m' i+t) (ell' i)‖≤L₀)
    (hS : ∀i v,δ*‖v‖^2≤ inner ℝ v (stableMatrix j (b' i) r (X' i) J (q' i) v))
    (hSmall : ∀i,|j| *|χ' i-b' i| *‖X' i‖^2+|j*r| *‖X' i‖^2*
      (‖m' i+t-(2:ℝ) • q' i‖*‖ell' i‖+2*‖q' i‖*‖ell' i+q' i‖)≤δ/2) :
    let A:=X*X
    let A':=fun i=>X' i*X' i
    let B:=u+J w-(j*χ) • w-(j*c) • (m+t)
    let z:=fun i=>r*inner ℝ (s i • (ell-ell' i)) w+s i*(p-p' i)
    columnNorm (fun i=>s i • (w-w' i))≤(1+X₀^2*(δ/2)⁻¹*L₀)*
      (columnNorm (fun i=>(s i • (A-A' i)) B)+
        columnNorm (fun i=>A' i (s i • (u-u' i)))+
        columnNorm (fun i=>(j*(s i*(χ-χ' i))) • A' i w)+
        columnNorm (fun i=>(j*c) • A' i (s i • (m-m' i)))+
        columnNorm (fun i=>(j*z i) • A' i (m' i+t))) := by
  dsimp only
  let V:=fun i=>(s i • (X*X-X' i*X' i)) (u+J w-(j*χ) • w-(j*c) • (m+t))+
    (X' i*X' i) (s i • (u-u' i))-(j*(s i*(χ-χ' i))) • (X' i*X' i) w-
    (j*c) • (X' i*X' i) (s i • (m-m' i))-
    (j*(r*inner ℝ (s i • (ell-ell' i)) w+s i*(p-p' i))) • (X' i*X' i) (m' i+t)
  have hlow:=column_inverse_estimate X' (fun i=>L₂ j (χ' i) r J (m' i+t) (ell' i))
    (fun i=>stableMatrix j (b' i) r (X' i) J (q' i)) (fun i=>s i • (w-w' i)) V
    hδ hX₀ hL₀ hX hL hS
    (fun i=>(normalized_difference_bound j (χ' i) (b' i) r (X' i) J (m' i+t) (ell' i) (q' i)).trans (hSmall i))
    (fun i=>implicit_scaled_difference (s i) j χ (χ' i) r p (p' i) (X*X) (X' i*X' i) J
      u (u' i) m (m' i) t ell (ell' i) w (w' i) y (y' i) c (c' i) h (h' i))
  apply hlow.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact columnNorm_add_sub_sub_sub _ _ _ _ _

end SKGap.ImplicitSystem
namespace SKGapCutoff.Recipe
lemma columnNorm_matrix {dimension : ℕ} (D : Interaction dimension) :
    SKGap.ImplicitSystem.columnNorm (fun k=>(WithLp.toLp 2 (fun i=>D i k) : EuclideanSpace ℝ (Fin dimension)))=‖D‖ := by
  apply (sq_eq_sq₀ (SKGap.ImplicitSystem.columnNorm_nonneg _) (norm_nonneg _)).mp
  rw [SKGap.ImplicitSystem.columnNorm_sq,SKGap.frobenius_sq]
  simp only [EuclideanSpace.real_norm_sq_eq]
  exact Finset.sum_comm
end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_ImplicitFrobenius
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.ImplicitSystem
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {ι : Type*} [Fintype ι]

omit [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] in
lemma columnNorm_compare (U : ι→E) (V : ι→F) {C : ℝ} (hC : 0≤C)
    (h : ∀i,‖U i‖≤C*‖V i‖) : columnNorm U≤C*columnNorm V := by
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hC (columnNorm_nonneg _))
  simp only [←sq,columnNorm_sq,mul_pow,Finset.mul_sum]
  exact Finset.sum_le_sum fun i _=>by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg (U i)) (h i) 2

lemma columnNorm_inner_common (V : ι→E) (w : E) :
    columnNorm (fun i=>inner ℝ (V i) w)≤‖w‖*columnNorm V := by
  apply columnNorm_compare _ _ (norm_nonneg w)
  intro i
  simpa only [Real.norm_eq_abs,mul_comm] using abs_real_inner_le_norm (V i) w

lemma columnNorm_inner_variable (V W : ι→E) {C : ℝ}
    (hC : 0≤C) (hV : ∀i,‖V i‖≤C) :
    columnNorm (fun i=>inner ℝ (V i) (W i))≤C*columnNorm W := by
  apply columnNorm_compare _ _ hC
  intro i
  exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hV i) (norm_nonneg _))

lemma normalized_coefficient_difference (D : ι→E) (dp : ι→ℝ) (w : E)
    {r d R P : ℝ} (hr : 0 ≤ r) (hd : 0<d) (hscale : r*d^2=1)
    (_hR : 0≤R) (hD : columnNorm D≤R*d) (hP : d*columnNorm dp≤P) :
    d*columnNorm (fun i=>r*inner ℝ (D i) w+dp i)≤R*‖w‖+P := by
  have he : (fun i=>r*inner ℝ (D i) w+dp i)=r • (fun i=>inner ℝ (D i) w)+dp := rfl
  rw [he]
  have hc:=columnNorm_add (r • (fun i=>inner ℝ (D i) w)) dp
  rw [columnNorm_smul,abs_of_nonneg hr] at hc
  have hi:=(columnNorm_inner_common D w).trans
    (mul_le_mul_of_nonneg_left hD (norm_nonneg w))
  calc
    _ ≤ d*(r*(‖w‖*(R*d))+columnNorm dp) := mul_le_mul_of_nonneg_left
      (hc.trans (add_le_add (mul_le_mul_of_nonneg_left hi hr) le_rfl)) hd.le
    _ = R*‖w‖*(r*d^2)+d*columnNorm dp := by ring
    _ = R*‖w‖+d*columnNorm dp := by rw [hscale]; ring
    _ ≤ _ := add_le_add le_rfl hP

lemma normalized_scalar_difference (D W L : ι→E) (dp : ι→ℝ) (w : E)
    {r d R P Q : ℝ} (hr : 0 ≤ r) (hd : 0<d) (hscale : r*d^2=1)
    (hR : 0≤R) (hD : columnNorm D≤R*d) (hP : d*columnNorm dp≤P)
    (hQ : 0≤Q) (hL : ∀i,‖L i‖≤Q*d) :
    d*columnNorm (fun i=>r*inner ℝ (D i) w+dp i+r*inner ℝ (L i) (W i))≤
      R*‖w‖+P+Q*columnNorm W := by
  have h₁:=normalized_coefficient_difference D dp w hr hd hscale hR hD hP
  have h₂:=columnNorm_inner_variable L W (mul_nonneg hQ hd.le) hL
  have he : (fun i=>r*inner ℝ (D i) w+dp i+r*inner ℝ (L i) (W i))=
      (fun i=>r*inner ℝ (D i) w+dp i)+r • (fun i=>inner ℝ (L i) (W i)) := rfl
  rw [he]
  have hh:=columnNorm_add (fun i=>r*inner ℝ (D i) w+dp i) (r • (fun i=>inner ℝ (L i) (W i)))
  rw [columnNorm_smul,abs_of_nonneg hr] at hh
  calc
    _ ≤ d*columnNorm (fun i=>r*inner ℝ (D i) w+dp i)+d*r*((Q*d)*columnNorm W) := by
      nlinarith only [mul_le_mul_of_nonneg_left hh hd.le,
        mul_le_mul_of_nonneg_left h₂ (mul_nonneg hd.le hr)]
    _ = d*columnNorm (fun i=>r*inner ℝ (D i) w+dp i)+Q*columnNorm W*(r*d^2) := by ring
    _ = d*columnNorm (fun i=>r*inner ℝ (D i) w+dp i)+Q*columnNorm W := by rw [hscale]; ring
    _ ≤ _ := add_le_add h₁ le_rfl

variable [FiniteDimensional ℝ E]

theorem implicit_frobenius_estimate (j χ r p : ℝ) (X J : E→L[ℝ]E)
    (u m t ell w y : E) (c : ℝ)
    (s χ' p' c' : ι→ℝ) (X' : ι→E→L[ℝ]E) (u' m' ell' w' y' q' : ι→E) (b' : ι→ℝ)
    (h : Equations j χ r p (X*X) J u m t ell w y c)
    (h' : ∀i,Equations j (χ' i) r (p' i) (X' i*X' i) J (u' i) (m' i) t (ell' i) (w' i) (y' i) (c' i))
    {δ X₀ L₀ d RA U Rχ Rm Rell P C V : ℝ}
    (hδ : 0<δ) (hX₀ : 0≤X₀) (hL₀ : 0≤L₀) (hd : 0<d) (hr : 0 ≤ r) (hscale : r*d^2=1)
    (_hRA : 0≤RA) (_hU : 0≤U) (_hRχ : 0≤Rχ) (hRm : 0≤Rm) (hRell : 0≤Rell)
    (_hP : 0≤P) (_hC : 0≤C) (hV : 0≤V)
    (hX : ∀i,‖X' i‖≤X₀) (hL : ∀i,‖L₂ j (χ' i) r J (m' i+t) (ell' i)‖≤L₀)
    (hS : ∀i v,δ*‖v‖^2≤ inner ℝ v (stableMatrix j (b' i) r (X' i) J (q' i) v))
    (hSmall : ∀i,|j| *|χ' i-b' i| *‖X' i‖^2+|j*r| *‖X' i‖^2*
      (‖m' i+t-(2:ℝ) • q' i‖*‖ell' i‖+2*‖q' i‖*‖ell' i+q' i‖)≤δ/2)
    (hDA : ∀B, columnNorm (fun i=>(s i • (X*X-X' i*X' i)) B)≤RA*‖B‖)
    (hDu : columnNorm (fun i=>s i • (u-u' i))≤U)
    (hDχ : columnNorm (fun i=>s i*(χ-χ' i))≤Rχ)
    (hDm : columnNorm (fun i=>s i • (m-m' i))≤Rm*d)
    (hDell : columnNorm (fun i=>s i • (ell-ell' i))≤Rell*d)
    (hDp : d*columnNorm (fun i=>s i*(p-p' i))≤P)
    (hc : d*|c|≤C) (hv : ∀i,‖m' i+t‖≤V*d) :
    columnNorm (fun i=>s i • (w-w' i))≤(1+X₀^2*(δ/2)⁻¹*L₀)*
      (RA*‖u+J w-(j*χ) • w-(j*c) • (m+t)‖+X₀^2*U+
        |j| *X₀^2*‖w‖*Rχ+|j| *X₀^2*C*Rm+
        |j| *X₀^2*V*(Rell*‖w‖+P)) := by
  let A':=fun i=>X' i*X' i
  have hA : ∀i,‖A' i‖≤X₀^2 := fun i=>(norm_mul_le _ _).trans
    (by simpa only [pow_two] using mul_le_mul (hX i) (hX i) (norm_nonneg _) hX₀)
  let z:=fun i=>r*inner ℝ (s i • (ell-ell' i)) w+s i*(p-p' i)
  have hz : d*columnNorm z≤Rell*‖w‖+P :=
    normalized_coefficient_difference _ _ w hr hd hscale hRell hDell hDp
  have h₂ : columnNorm (fun i=>A' i (s i • (u-u' i)))≤X₀^2*U :=
    (columnNorm_operator A' _ (sq_nonneg _) hA).trans (mul_le_mul_of_nonneg_left hDu (sq_nonneg _))
  have h₃ : columnNorm (fun i=>(j*(s i*(χ-χ' i))) • A' i w)≤|j| *X₀^2*‖w‖*Rχ := by
    have he : (fun i=>(j*(s i*(χ-χ' i))) • A' i w)=
        j • (fun i=>(s i*(χ-χ' i)) • A' i w) := by ext i; simp [mul_smul]
    rw [he,columnNorm_smul]
    have hb : ∀i,‖A' i w‖≤X₀^2*‖w‖ := fun i=>((A' i).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hA i) (norm_nonneg _))
    have hh:=(columnNorm_vector_scalar _ _ (by positivity : 0≤X₀^2*‖w‖) hb).trans
      (mul_le_mul_of_nonneg_left hDχ (by positivity))
    nlinarith only [mul_le_mul_of_nonneg_left hh (abs_nonneg j)]
  have h₄ : columnNorm (fun i=>(j*c) • A' i (s i • (m-m' i)))≤|j| *X₀^2*C*Rm := by
    change columnNorm ((j*c) • (fun i=>A' i (s i • (m-m' i))))≤_
    rw [columnNorm_smul,abs_mul]
    have hh:=(columnNorm_operator A' _ (sq_nonneg _) hA).trans
      (mul_le_mul_of_nonneg_left hDm (sq_nonneg _))
    calc
      _ ≤ |j| *|c| *(X₀^2*(Rm*d)) := mul_le_mul_of_nonneg_left hh (by positivity)
      _ = (|j| *X₀^2*Rm)*(d*|c|) := by ring
      _ ≤ (|j| *X₀^2*Rm)*C := mul_le_mul_of_nonneg_left hc (by positivity)
      _ = _ := by ring
  have h₅ : columnNorm (fun i=>(j*z i) • A' i (m' i+t))≤|j| *X₀^2*V*(Rell*‖w‖+P) := by
    have he : (fun i=>(j*z i) • A' i (m' i+t))=j • (fun i=>z i • A' i (m' i+t)) := by
      ext i; simp [mul_smul]
    rw [he,columnNorm_smul]
    have hb : ∀i,‖A' i (m' i+t)‖≤X₀^2*(V*d) := fun i=>((A' i).le_opNorm _).trans
      (mul_le_mul (hA i) (hv i) (norm_nonneg _) (sq_nonneg _))
    have hh:=columnNorm_vector_scalar (fun i=>A' i (m' i+t)) z (by positivity : 0≤X₀^2*(V*d)) hb
    calc
      _ ≤ |j| *((X₀^2*(V*d))*columnNorm z) := mul_le_mul_of_nonneg_left hh (abs_nonneg _)
      _ = (|j| *X₀^2*V)*(d*columnNorm z) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hz (by positivity)
  have H:=implicit_columns_bound j χ r p X J u m t ell w y c s χ' p' c' X' u' m' ell' w' y' q' b'
    h h' hδ hX₀ hL₀ hX hL hS hSmall
  apply H.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add (add_le_add (add_le_add (add_le_add (hDA _) h₂) h₃) h₄) h₅

end SKGap.ImplicitSystem
namespace SKGapCutoff.Recipe
open Matrix
variable {n : ℕ}
lemma frobenius_by_rows (D : Interaction n) {R : ℝ} (hR : 0≤R)
    (hD : ∀i,∑k,(D i k)^2≤R^2) : ‖D‖≤R*Real.sqrt n := by
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hR (Real.sqrt_nonneg _))
  simp only [←sq,SKGap.frobenius_sq,mul_pow,Real.sq_sqrt (Nat.cast_nonneg n)]
  calc
    _ ≤ ∑_i:Fin n,R^2 := Finset.sum_le_sum fun i _=>hD i
    _ = _ := by simp [mul_comm]

lemma coefficient_diagonal_columns (a a' : Fin n→Fin n→ℝ) (s : Fin n→ℝ)
    {R : ℝ} (hR : 0≤R) (ha : ∀i,∑k,(s k*(a k i-a' k i))^2≤R^2)
    (B : EuclideanSpace ℝ (Fin n)) :
    SKGap.ImplicitSystem.columnNorm (fun k=>(s k •
      (toEuclideanCLM (𝕜:=ℝ) (diagonal (a k))-toEuclideanCLM (𝕜:=ℝ) (diagonal (a' k)))) B)≤R*‖B‖ := by
  let D : Interaction n:=fun i k=>B i*(s k*(a k i-a' k i))
  have he : (fun k=>(s k •
      (toEuclideanCLM (𝕜:=ℝ) (diagonal (a k))-toEuclideanCLM (𝕜:=ℝ) (diagonal (a' k)))) B)=
      (fun k=>(WithLp.toLp 2 (fun i=>D i k) : EuclideanSpace ℝ (Fin n))) := by
    ext k i
    change s k*((toEuclideanCLM (𝕜:=ℝ) (diagonal (a k)) (WithLp.toLp 2 B.ofLp)) i-
      (toEuclideanCLM (𝕜:=ℝ) (diagonal (a' k)) (WithLp.toLp 2 B.ofLp)) i)=D i k
    simp only [toEuclideanCLM_toLp,WithLp.ofLp_toLp,mulVec_diagonal,D]
    ring
  rw [he,columnNorm_matrix]
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hR (norm_nonneg _))
  simp only [←sq,SKGap.frobenius_sq,mul_pow,EuclideanSpace.real_norm_sq_eq]
  calc
    _ = ∑i,(B i)^2*(∑k,(s k*(a k i-a' k i))^2) := by
      simp only [D,mul_pow,Finset.mul_sum]
    _ ≤ ∑i,(B i)^2*R^2 := Finset.sum_le_sum fun i _=>mul_le_mul_of_nonneg_left (ha i) (sq_nonneg _)
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_ImplicitUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace SKGap.ImplicitSystem
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma L₂_norm_le (j χ r : ℝ) (J : E→L[ℝ]E) (v ell : E) :
    ‖L₂ j χ r J v ell‖≤‖J‖+|j| *|χ|+|j| *|r| *‖v‖*‖ell‖ := by
  unfold L₂
  calc
    _ ≤ ‖-J+(j*χ) • (1:E→L[ℝ]E)‖+‖(j*r) • rank v ell‖ := norm_add_le _ _
    _ ≤ (‖J‖+|j| *|χ|)+|j| *|r| *(‖v‖*‖ell‖) := by
      apply add_le_add
      · apply (norm_add_le _ _).trans
        simp only [norm_neg,norm_smul,Real.norm_eq_abs,abs_mul]
        exact add_le_add le_rfl (mul_le_of_le_one_right (by positivity) ContinuousLinearMap.norm_id_le)
      · rw [norm_smul,Real.norm_eq_abs,abs_mul]
        exact mul_le_mul_of_nonneg_left (rank_norm_le v ell) (by positivity)
    _ = _ := by ring

lemma L₂_normalized_bound (j χ r : ℝ) (J : E→L[ℝ]E) (v ell : E)
    {d V Q A L : ℝ} (hr : 0 ≤ r) (hd : 0≤d) (hscale : r*d^2=1)
    (hV : 0≤V) (hQ : 0≤Q) (hv : ‖v‖≤V*d) (hell : ‖ell‖≤Q*d)
    (hχ : |χ|≤A) (hJ : ‖J‖≤L) :
    ‖L₂ j χ r J v ell‖≤L+|j| *A+|j| *V*Q := by
  apply (L₂_norm_le j χ r J v ell).trans
  rw [abs_of_nonneg hr]
  have hmul:=mul_le_mul hv hell (norm_nonneg ell) (mul_nonneg hV hd)
  calc
    _ ≤ L+|j| *A+|j| *r*((V*d)*(Q*d)) := by
      rw [mul_assoc (|j| *r)]
      exact add_le_add (add_le_add hJ (mul_le_mul_of_nonneg_left hχ (abs_nonneg _)))
        (mul_le_mul_of_nonneg_left hmul (by positivity))
    _ = L+|j| *A+|j| *V*Q*(r*d^2) := by ring
    _ ≤ _ := by
      simpa only [mul_one] using add_le_add (le_refl (L+|j| *A))
        (mul_le_mul_of_nonneg_left hscale.le (mul_nonneg (mul_nonneg (abs_nonneg j) hV) hQ))

variable [FiniteDimensional ℝ E]

theorem implicit_uniform_size (j χ b r p : ℝ) (X J : E→L[ℝ]E)
    (u m t ell q w y : E) (c : ℝ)
    {δ d A L Q U P : ℝ} (hδ : 0<δ) (hd : 0<d) (hr : 0 ≤ r) (hscale : r*d^2=1)
    (hA : 0≤A) (hL : 0≤L) (hQ : 0≤Q) (hU : 0≤U) (hP : 0≤P)
    (hX : ‖X‖^2≤A) (hJ : ‖J‖≤L) (hχ : |χ|≤A)
    (hu : ‖u‖≤U) (hm : ‖m‖≤d) (ht : ‖t‖≤d) (hell : ‖ell‖≤Q*d) (hp : d*|p|≤P)
    (hStable : ∀v,δ*‖v‖^2≤ inner ℝ v (stableMatrix j b r X J q v))
    (hSmall : |j| *|χ-b| *‖X‖^2+|j*r| *‖X‖^2*
      (‖m+t-(2:ℝ) • q‖*‖ell‖+2*‖q‖*‖ell+q‖)≤δ/2)
    (hEq : Equations j χ r p (X*X) J u m t ell w y c) :
    let W:=(1+A*(δ/2)⁻¹*(L+|j| *A+2*|j| *Q))*A*(U+2*|j| *P)
    ‖w‖≤W ∧ d*|c|≤Q*W+P ∧ ‖y‖≤(L+|j| *A)*W+|j| *(Q*W+P) := by
  dsimp only
  let W:=(1+A*(δ/2)⁻¹*(L+|j| *A+2*|j| *Q))*A*(U+2*|j| *P)
  have hv : ‖m+t‖≤2*d := (norm_add_le _ _).trans (by linarith)
  have hL₂ : ‖L₂ j χ r J (m+t) ell‖≤L+|j| *A+2*|j| *Q := by
    convert L₂_normalized_bound j χ r J (m+t) ell hr hd.le hscale (by norm_num : (0:ℝ)≤2) hQ hv hell hχ hJ using 1 <;> first | rfl | ring
  have hRHS : ‖u‖+|j| *|p| *(‖m‖+‖t‖)≤U+2*|j| *P := by
    calc
      _ ≤ U+|j| *|p| *(2*d) := add_le_add hu (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
      _ = U+2*|j| *(d*|p|) := by ring
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hp (by positivity))
  have hinv : 0≤(δ/2)⁻¹ := by positivity
  have hK : 0≤1+A*(δ/2)⁻¹*(L+|j| *A+2*|j| *Q) := by positivity
  have hKK : 1+‖X‖^2*(δ/2)⁻¹*‖L₂ j χ r J (m+t) ell‖≤
      1+A*(δ/2)⁻¹*(L+|j| *A+2*|j| *Q) := by
    exact add_le_add le_rfl (mul_le_mul (mul_le_mul_of_nonneg_right hX hinv) hL₂ (norm_nonneg _) (by positivity))
  obtain ⟨hw,hc,hy⟩:=implicit_size_bounds j χ b r p X J u m t ell q w y c hδ hStable hSmall hEq
  have hw' : ‖w‖≤W := hw.trans (by
    simpa only [W,mul_comm] using mul_le_mul hRHS
      (mul_le_mul_of_nonneg_right hKK (sq_nonneg _) |>.trans (mul_le_mul_of_nonneg_left hX hK))
      (by positivity)
      (add_nonneg hU (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) (abs_nonneg j)) hP)))
  have hc' : d*|c|≤Q*W+P := by
    have hh:=implicit_scalar_size r p ell w
    rw [←hEq.2.2,abs_of_nonneg hr] at hh
    have hb:=mul_le_mul hell hw' (norm_nonneg w) (mul_nonneg hQ hd.le)
    calc
      _ ≤ d*(r*((Q*d)*W)+|p|) := mul_le_mul_of_nonneg_left
        (hh.trans (add_le_add (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hb hr) le_rfl)) hd.le
      _ = Q*W*(r*d^2)+d*|p| := by ring
      _ = Q*W+d*|p| := by rw [hscale]; ring
      _ ≤ _ := add_le_add le_rfl hp
  refine ⟨hw',hc',?_⟩
  rw [hEq.2.1]
  apply (implicit_field_size J j χ c w m).trans
  rw [abs_mul]
  have h₁:=mul_le_mul (add_le_add hJ (mul_le_mul_of_nonneg_left hχ (abs_nonneg _))) hw'
    (norm_nonneg w) (by positivity : 0≤L+|j| *A)
  have h₂ : |j| *|c| *‖m‖≤|j| *(Q*W+P) := by
    calc
      _ ≤ |j| *|c| *d := mul_le_mul_of_nonneg_left hm (by positivity)
      _ = |j| *(d*|c|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hc' (abs_nonneg _)
  exact add_le_add h₁ h₂
end SKGap.ImplicitSystem

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGap.ImplicitSystem
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι]

lemma implicit_field_difference (s j χ χ' r p p' : ℝ) (A A' J : E→L[ℝ]E)
    (u u' m m' t ell ell' w w' y y' : E) (c c' : ℝ)
    (h : Equations j χ r p A J u m t ell w y c)
    (h' : Equations j χ' r p' A' J u' m' t ell' w' y' c') :
    s • (y-y')=J (s • (w-w'))-(j*χ') • (s • (w-w'))-
      (j*(s*(χ-χ'))) • w-(j*c) • (s • (m-m'))-(j*(s*(c-c'))) • m' := by
  rw [h.2.1,h'.2.1]
  simp only [map_sub,map_smul]
  module

theorem implicit_scalar_columns (s : ι→ℝ) (r p : ℝ) (ell w : E) (c : ℝ)
    (p' c' : ι→ℝ) (ell' w' : ι→E)
    (hc : c=r*inner ℝ ell w+p) (hc' : ∀i,c' i=r*inner ℝ (ell' i) (w' i)+p' i)
    {d R P Q : ℝ} (hr : 0 ≤ r) (hd : 0<d) (hscale : r*d^2=1)
    (hR : 0≤R) (hD : columnNorm (fun i=>s i • (ell-ell' i))≤R*d)
    (hP : d*columnNorm (fun i=>s i*(p-p' i))≤P)
    (hQ : 0≤Q) (hL : ∀i,‖ell' i‖≤Q*d) :
    d*columnNorm (fun i=>s i*(c-c' i))≤R*‖w‖+P+Q*columnNorm (fun i=>s i • (w-w' i)) := by
  have he : (fun i=>s i*(c-c' i))=(fun i=>r*inner ℝ (s i • (ell-ell' i)) w+s i*(p-p' i)+
      r*inner ℝ (ell' i) (s i • (w-w' i))) := by
    funext i
    rw [hc,hc' i]
    exact implicit_scalar_difference (s i) r p (p' i) ell (ell' i) w (w' i)
  rw [he]
  exact normalized_scalar_difference _ _ _ _ w hr hd hscale hR hD hP hQ hL

theorem implicit_field_columns (s : ι→ℝ) (j χ r p : ℝ) (A J : E→L[ℝ]E)
    (u m t ell w y : E) (c : ℝ) (χ' p' c' : ι→ℝ)
    (A' : ι→E→L[ℝ]E) (u' m' ell' w' y' : ι→E)
    (h : Equations j χ r p A J u m t ell w y c)
    (h' : ∀i,Equations j (χ' i) r (p' i) (A' i) J (u' i) (m' i) t (ell' i) (w' i) (y' i) (c' i))
    {L H d Rχ Rm C M Dc : ℝ} (hL : 0≤L) (hH : 0≤H) (hd : 0<d)
    (hRχ : 0≤Rχ) (hRm : 0≤Rm) (hC : 0≤C) (hM : 0≤M)
    (hJ : ‖J‖≤L) (hχ : ∀i,|χ' i|≤H)
    (hDχ : columnNorm (fun i=>s i*(χ-χ' i))≤Rχ)
    (hDm : columnNorm (fun i=>s i • (m-m' i))≤Rm*d)
    (hc : d*|c|≤C) (hm : ∀i,‖m' i‖≤M*d)
    (hdc : d*columnNorm (fun i=>s i*(c-c' i))≤Dc) :
    columnNorm (fun i=>s i • (y-y' i))≤
      (L+|j| *H)*columnNorm (fun i=>s i • (w-w' i))+|j| *‖w‖*Rχ+|j| *C*Rm+|j| *M*Dc := by
  let Dw:=fun i=>s i • (w-w' i)
  let Dχ:=fun i=>s i*(χ-χ' i)
  let Dm:=fun i=>s i • (m-m' i)
  let Dc':=fun i=>s i*(c-c' i)
  have ha : columnNorm (fun i=>J (Dw i))≤L*columnNorm Dw :=
    columnNorm_operator (fun _=>J) Dw hL (fun _=>hJ)
  have hb : columnNorm (fun i=>(j*χ' i) • Dw i)≤(|j| *H)*columnNorm Dw := by
    apply columnNorm_compare _ _ (by positivity)
    intro i
    rw [norm_smul,Real.norm_eq_abs,abs_mul]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hχ i) (abs_nonneg j)) (norm_nonneg _)
  have he : columnNorm (fun i=>(j*Dχ i) • w)≤|j| *‖w‖*Rχ := by
    have eq : (fun i=>(j*Dχ i) • w)=j • (fun i=>Dχ i • w) := by ext i; simp [mul_smul]
    rw [eq,columnNorm_smul]
    exact (mul_le_mul_of_nonneg_left (columnNorm_vector_scalar (fun _=>w) Dχ (norm_nonneg w) (fun _=>le_rfl)) (abs_nonneg j)).trans
      (by
        simpa only [mul_assoc,mul_comm,mul_left_comm] using mul_le_mul hDχ
          (le_refl (|j| *‖w‖)) (mul_nonneg (abs_nonneg j) (norm_nonneg w)) hRχ)
  have hf : columnNorm (fun i=>(j*c) • Dm i)≤|j| *C*Rm := by
    change columnNorm ((j*c) • Dm)≤_
    rw [columnNorm_smul,abs_mul]
    calc
      _ ≤ |j| *|c| *(Rm*d) := mul_le_mul_of_nonneg_left hDm (by positivity)
      _ = (|j| *Rm)*(d*|c|) := by ring
      _ ≤ (|j| *Rm)*C := by
        simpa only [mul_comm] using mul_le_mul hc (le_refl (|j| *Rm))
          (mul_nonneg (abs_nonneg j) hRm) hC
      _ = _ := by ring
  have hg : columnNorm (fun i=>(j*Dc' i) • m' i)≤|j| *M*Dc := by
    have eq : (fun i=>(j*Dc' i) • m' i)=j • (fun i=>Dc' i • m' i) := by ext i; simp [mul_smul]
    rw [eq,columnNorm_smul]
    calc
      _ ≤ |j| *((M*d)*columnNorm Dc') := mul_le_mul_of_nonneg_left
        (columnNorm_vector_scalar m' Dc' (by positivity) hm) (abs_nonneg j)
      _ = (|j| *M)*(d*columnNorm Dc') := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hdc (by positivity)
  have eq : (fun i=>s i • (y-y' i))=(fun i=>J (Dw i))+(fun i=>-((j*χ' i) • Dw i))-
      (fun i=>(j*Dχ i) • w)-(fun i=>(j*c) • Dm i)-(fun i=>(j*Dc' i) • m' i) := by
    funext i
    simpa only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Dw,Dχ,Dm,Dc',sub_eq_add_neg] using
      implicit_field_difference (s i) j χ (χ' i) r p (p' i) A (A' i) J u (u' i) m (m' i) t ell (ell' i) w (w' i) y (y' i) c (c' i) h (h' i)
  rw [eq]
  have ht:=columnNorm_add_sub_sub_sub (fun i=>J (Dw i)) (fun i=>-((j*χ' i) • Dw i))
    (fun i=>(j*Dχ i) • w) (fun i=>(j*c) • Dm i) (fun i=>(j*Dc' i) • m' i)
  change columnNorm _≤_ at ht
  have hn : columnNorm (fun i=>-((j*χ' i) • Dw i))=columnNorm (fun i=>(j*χ' i) • Dw i) := columnNorm_neg _
  rw [hn] at ht
  exact ht.trans (by nlinarith only [ha,hb,he,hf,hg])
end SKGap.ImplicitSystem

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_ImplicitUniformControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace SKGap.ImplicitSystem
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]

lemma uniformControlBudget_nonneg {j δ B : ℝ} (hδ : 0<δ) (hB : 0≤B) :
    0≤uniformControlBudget j δ B := by unfold uniformControlBudget; positivity

theorem implicit_uniform_control (j χ b r p : ℝ) (X J : E→L[ℝ]E)
    (u m t ell q w y : E) (c : ℝ)
    (s χ' p' c' b' : ι→ℝ) (X' : ι→E→L[ℝ]E) (u' m' ell' w' y' q' : ι→E)
    {δ d B : ℝ} (hδ : 0<δ) (hd : 0<d) (hr : 0 ≤ r) (hscale : r*d^2=1) (hB : 0≤B)
    (hX : ‖X‖≤B) (hX' : ∀i,‖X' i‖≤B) (hJ : ‖J‖≤B)
    (hχ : |χ|≤B^2) (hχ' : ∀i,|χ' i|≤B^2)
    (hu : ‖u‖≤B) (hm : ‖m‖≤d) (hm' : ∀i,‖m' i‖≤d) (ht : ‖t‖≤d)
    (hell : ‖ell‖≤B*d) (hell' : ∀i,‖ell' i‖≤B*d) (hp : d*|p|≤B)
    (hS : ∀v,δ*‖v‖^2≤ inner ℝ v (stableMatrix j b r X J q v))
    (hS' : ∀i v,δ*‖v‖^2≤ inner ℝ v (stableMatrix j (b' i) r (X' i) J (q' i) v))
    (hSmall : |j| *|χ-b| *‖X‖^2+|j*r| *‖X‖^2*
      (‖m+t-(2:ℝ) • q‖*‖ell‖+2*‖q‖*‖ell+q‖)≤δ/2)
    (hSmall' : ∀i,|j| *|χ' i-b' i| *‖X' i‖^2+|j*r| *‖X' i‖^2*
      (‖m' i+t-(2:ℝ) • q' i‖*‖ell' i‖+2*‖q' i‖*‖ell' i+q' i‖)≤δ/2)
    (h : Equations j χ r p (X*X) J u m t ell w y c)
    (h' : ∀i,Equations j (χ' i) r (p' i) (X' i*X' i) J (u' i) (m' i) t (ell' i) (w' i) (y' i) (c' i))
    (hDA : ∀V,columnNorm (fun i=>(s i • (X*X-X' i*X' i)) V)≤B*‖V‖)
    (hDu : columnNorm (fun i=>s i • (u-u' i))≤B)
    (hDχ : columnNorm (fun i=>s i*(χ-χ' i))≤B)
    (hDm : columnNorm (fun i=>s i • (m-m' i))≤B*d)
    (hDell : columnNorm (fun i=>s i • (ell-ell' i))≤B*d)
    (hDp : d*columnNorm (fun i=>s i*(p-p' i))≤B) :
    ‖w‖+d*|c|+‖y‖+columnNorm (fun i=>s i • (w-w' i))+
      d*columnNorm (fun i=>s i*(c-c' i))+columnNorm (fun i=>s i • (y-y' i))≤
        uniformControlBudget j δ B := by
  let L:=B+|j| *B^2+2*|j| *B
  let W:=(1+B^2*(δ/2)⁻¹*L)*B^2*(B+2*|j| *B)
  let C:=B*W+B
  let Y:=(B+|j| *B^2)*W+|j| *C
  let F:=(1+B^2*(δ/2)⁻¹*L)*(B*(B+Y+|j| *C)+B^2*B+
        |j| *B^2*W*B+|j| *B^2*C*B+|j| *B^2*2*(B*W+B))
  let G:=B*W+B+B*F
  let H:=(B+|j| *B^2)*F+|j| *W*B+|j| *C*B+|j| *G
  have hW0 : 0≤W := by dsimp [W,L]; positivity
  have hC0 : 0≤C := by dsimp [C]; positivity
  have hY0 : 0≤Y := by dsimp [Y]; positivity
  have hL0 : 0≤L := by dsimp [L]; positivity
  have hF0 : 0≤F := by dsimp [F]; positivity
  obtain ⟨hw,hc,hy⟩:=implicit_uniform_size j χ b r p X J u m t ell q w y c
    hδ hd hr hscale (sq_nonneg B) hB hB hB hB
    (pow_le_pow_left₀ (norm_nonneg X) hX 2) hJ hχ hu hm ht hell hp hS hSmall h
  change ‖w‖≤W at hw
  change d*|c|≤C at hc
  change ‖y‖≤Y at hy
  have hl : ∀i,‖L₂ j (χ' i) r J (m' i+t) (ell' i)‖≤L := by
    intro i
    have hv : ‖m' i+t‖≤2*d := (norm_add_le _ _).trans (by linarith [hm' i])
    convert L₂_normalized_bound j (χ' i) r J (m' i+t) (ell' i) hr hd.le hscale
      (by norm_num : (0:ℝ)≤2) hB hv (hell' i) (hχ' i) hJ using 1; dsimp [L]; ring
  have hb : ‖u+J w-(j*χ) • w-(j*c) • (m+t)‖≤B+Y+|j| *C := by
    have he : u+J w-(j*χ) • w-(j*c) • (m+t)=u+y-(j*c) • t := by
      rw [h.2.1]; module
    rw [he]
    apply (norm_sub_le _ _).trans
    have hct : ‖(j*c) • t‖≤|j| *C := by
      rw [norm_smul,Real.norm_eq_abs,abs_mul]
      calc
        _ ≤ |j| *|c| *d := mul_le_mul_of_nonneg_left ht (by positivity)
        _ = |j| *(d*|c|) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hc (abs_nonneg j)
    exact add_le_add ((norm_add_le _ _).trans (add_le_add hu hy)) hct
  have hf:=implicit_frobenius_estimate j χ r p X J u m t ell w y c
    s χ' p' c' X' u' m' ell' w' y' q' b' h h' hδ hB hL0 hd hr hscale
    hB hB hB hB hB hB hC0 (by norm_num : (0:ℝ)≤2) hX' hl hS' hSmall'
    hDA hDu hDχ hDm hDell hDp hc (fun i=>(norm_add_le _ _).trans (by linarith [hm' i]))
  have hf' : columnNorm (fun i=>s i • (w-w' i))≤F := by
    apply hf.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact add_le_add (add_le_add (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left hb hB) le_rfl)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw (by positivity)) hB)) le_rfl)
      (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hw hB) le_rfl) (by positivity))
  have hg : d*columnNorm (fun i=>s i*(c-c' i))≤G := by
    exact (implicit_scalar_columns s r p ell w c p' c' ell' w' h.2.2 (fun i=>(h' i).2.2)
      hr hd hscale hB hDell hDp hB hell').trans (add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left hw hB) le_rfl) (mul_le_mul_of_nonneg_left hf' hB))
  have hh : columnNorm (fun i=>s i • (y-y' i))≤H := by
    have hh:=implicit_field_columns s j χ r p (X*X) J u m t ell w y c χ' p' c'
      (fun i=>X' i*X' i) u' m' ell' w' y' h h' hB (sq_nonneg B) hd hB hB hC0
      (by norm_num : (0:ℝ)≤1) hJ hχ' hDχ hDm hc (by simpa only [one_mul] using hm') hg
    apply hh.trans
    simp only [mul_one]
    exact add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hf' (by positivity))
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw (abs_nonneg j)) hB)) le_rfl) le_rfl
  change _≤W+C+Y+F+G+H
  exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hw hc) hy) hf') hg) hh
end SKGap.ImplicitSystem

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary SKGap.ImplicitSystem
variable {n : ℕ}

lemma halfDiff_column (U : VectorFields n) (x : Spin n) (k : Fin n) :
    ((spin x k/2) • ((WithLp.toLp 2 (U x) : Euclid n)-WithLp.toLp 2 (U (flip x k))))=
      WithLp.toLp 2 (fun i=>derivativeMatrix U x i k) := by
  ext i
  change (spin x k/2)*(U x i-U (flip x k) i)=halfDiff k (fun y=>U y i) x
  rw [halfDiff_as_flip]; ring

lemma columnNorm_halfDiff (U : VectorFields n) (x : Spin n) :
    columnNorm (fun k=>(spin x k/2) •
      ((WithLp.toLp 2 (U x) : Euclid n)-WithLp.toLp 2 (U (flip x k))))=‖derivativeMatrix U x‖ := by
  simp only [halfDiff_column]
  exact columnNorm_matrix _

lemma columnNorm_scalar_halfDiff (f : Spin n→ℝ) (x : Spin n) :
    columnNorm (fun k=>(spin x k/2)*(f x-f (flip x k)))=‖derivativeVector f x‖ := by
  have he : (fun k=>(spin x k/2)*(f x-f (flip x k)))=fun k=>halfDiff k f x := by
    ext k; rw [halfDiff_as_flip]; ring
  rw [he]
  rfl

lemma diagonal_halfDiff_columns (a : VectorFields n) (x : Spin n) {R : ℝ}
    (hR : 0≤R) (ha : ∀i,∑k,(derivativeMatrix a x i k)^2≤R^2)
    (V : Euclid n) :
    columnNorm (fun k=>((spin x k/2) •
      (Matrix.toEuclideanCLM (𝕜:=ℝ) (Matrix.diagonal (a x))-
       Matrix.toEuclideanCLM (𝕜:=ℝ) (Matrix.diagonal (a (flip x k))))) V)≤R*‖V‖ := by
  apply coefficient_diagonal_columns (fun _=>a x) (fun k=>a (flip x k)) (fun k=>spin x k/2) hR
  intro i
  convert ha i using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  rw [derivativeMatrix,halfDiff_as_flip]
  ring

lemma implicit_tuple_small (w y : VectorFields n) (c : Spin n→ℝ) (x : Spin n)
    {d C : ℝ} (hd : 0≤d) (hC : 0≤C)
    (h : vectorNorm (w x)+d*|c x|+vectorNorm (y x)+‖derivativeMatrix w x‖+
      d*‖derivativeVector c x‖+‖derivativeMatrix y x‖≤C) :
    SmallBound w x C ∧ SmallBound y x C ∧
      |d*c x|≤C ∧ ‖derivativeVector (fun z=>d*c z) x‖≤C := by
  have hw0:=vectorNorm_nonneg (w x)
  have hy0:=vectorNorm_nonneg (y x)
  have hc0:=mul_nonneg hd (abs_nonneg (c x))
  have hw1:=norm_nonneg (derivativeMatrix w x)
  have hy1:=norm_nonneg (derivativeMatrix y x)
  have hc1:=mul_nonneg hd (norm_nonneg (derivativeVector c x))
  refine ⟨⟨hC,by linarith,by linarith⟩,⟨hC,by linarith,by linarith⟩,?_,?_⟩
  · rw [abs_mul,abs_of_nonneg hd]; linarith
  · have he : derivativeVector (fun z=>d*c z) x=d • derivativeVector c x := by
      ext k
      change halfDiff k (fun z=>d*c z) x=d*halfDiff k c x
      simp [halfDiff]; ring
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg hd]
    linarith
end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_LiteralStableControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary SKGap.ImplicitSystem Matrix
variable {n : ℕ}

lemma LiteralStableAt.perturbation {J : Interaction n} {j : ℝ}
    {z m : VectorFields n} {a : Spin n→ℝ} {r : Fin n→ℝ}
    {R ρ δ : ℝ} {x : Spin n} (H : LiteralStableAt J j z m a r R ρ δ x)
    (hn : 0<n) (hδ : 0<δ) (hρ : 0≤ρ)
    (hsmall : ρ≤δ/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1))) :
    |j| *|siteMean (fun v i=>phi (z v i) (r i) (a v)) x-
      (∑i,scalarVariance (z x i))/(n:ℝ)| *‖phiSqrt (z x) r (a x)‖^2+
      |j*(n:ℝ)⁻¹| *‖phiSqrt (z x) r (a x)‖^2*
      (‖(WithLp.toLp 2 (m x) : Euclid n)+WithLp.toLp 2 (fun i=>Real.tanh (r i))-
        (2:ℝ) • WithLp.toLp 2 (fun i=>Real.tanh (z x i))‖*
          ‖(WithLp.toLp 2 (fun i=>logSlope (z x i) (r i) (a x)) : Euclid n)‖+
       2*‖(WithLp.toLp 2 (fun i=>Real.tanh (z x i)) : Euclid n)‖*
        ‖(WithLp.toLp 2 (fun i=>logSlope (z x i) (r i) (a x)) : Euclid n)+
          WithLp.toLp 2 (fun i=>Real.tanh (z x i))‖)≤δ/2 :=
  (implicit_normalized_perturbation (z x) r (m x) (a x) j (phiSqrt (z x) r (a x))
    hn hρ H.a_bound H.a_small H.z_near H.m_near (phiSqrt_bound _ _ _ H.a_bound)).trans
      (implicit_rho_threshold j R δ ρ hδ hsmall)

lemma LiteralStableAt.m_size {J : Interaction n} {j : ℝ}
    {z m : VectorFields n} {a : Spin n→ℝ} {r : Fin n→ℝ}
    {R ρ δ : ℝ} {x : Spin n} (H : LiteralStableAt J j z m a r R ρ δ x) :
    vectorNorm (m x)≤Real.sqrt n := by
  have h:=vectorNorm_mono (u:=m x) (v:=fun _=>1) (fun i=>by simpa using H.m_bound i)
  simpa only [vectorNorm_const,abs_one,one_mul] using h

lemma frobenius_le_opNorm_sqrt (D : Interaction n) : ‖D‖≤SKGap.opNorm D*Real.sqrt n :=
  frobenius_by_rows D (norm_nonneg _) (fun i=>SKGap.SourceError.matrix_row_square_le D i)

lemma literal_initial_control (J : Interaction n) (j : ℝ) (f : KernelExpr)
    (z m w y : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (x : Spin n)
    (hn : 0<n) {R ρ δ T L B : ℝ} (hδ : 0<δ) (hρ : 0≤ρ) (hT : 0≤T)
    (hsmall : ρ≤δ/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1)))
    (hB : LiteralBudget f R T L B) (hJ : SKGap.opNorm J≤L) (he : vectorNorm e≤1)
    (H : LiteralStableAt J j z m a r R ρ δ x)
    (Hf : ∀k,LiteralStableAt J j z m a r R ρ δ (flip x k))
    (hD : SKGap.opNorm (derivativeMatrix z x)+‖derivativeVector a x‖≤T)
    (hDm : SKGap.opNorm (derivativeMatrix m x)≤T)
    (h : LiteralEquations J j f z m w y a c r e x)
    (hf : ∀k,LiteralEquations J j f z m w y a c r e (flip x k)) :
    SmallBound w x (uniformControlBudget j δ B) ∧
    SmallBound y x (uniformControlBudget j δ B) ∧
    |Real.sqrt n*c x|≤uniformControlBudget j δ B ∧
    ‖derivativeVector (fun v=>Real.sqrt n*c v) x‖≤uniformControlBudget j δ B := by
  let A : VectorFields n:=fun v i=>phi (z v i) (r i) (a v)
  let ell : VectorFields n:=fun v i=>logSlope (z v i) (r i) (a v)
  have hnR : (0:ℝ)<n:=Nat.cast_pos.mpr hn
  have hd : 0<Real.sqrt (n:ℝ):=Real.sqrt_pos.mpr hnR
  have hscale : (n:ℝ)⁻¹*(Real.sqrt (n:ℝ))^2=1 := by rw [Real.sq_sqrt hnR.le,inv_mul_cancel₀ hnR.ne']
  have ha:=initial_kernel_bound phiExpr z a r x hT H.a_bound (fun k=>(Hf k).a_bound) hD
  have ha' : CoefficientBound A x (Real.exp (R/2)) ((phiExpr.dBudget R+phiExpr.ddBudget R)*T) := by
    convert! ha using 1
    · ext v i; exact (moment_base _ _ _).symm
    · simp [phiExpr,KernelExpr.mass]
  have hel:=initial_ratio_bound (.kernel phiExpr.dz) z a r x hT hD
  have hel' : CoefficientBound ell x (RatioExpr.kernel phiExpr.dz).mass
      (((RatioExpr.kernel phiExpr.dz).dBudget+(RatioExpr.kernel phiExpr.dz).ddBudget)*T) := by
    convert! hel using 1
    all_goals try with_reducible_and_instances rfl
    ext v i; exact logSlope_ratio _ _ _
  have hu:=(initialU_small f z a r e x hT he hD).mono hB.source
  have hp:=(initialP_small f z a r e x hT he H.a_bound (fun k=>(Hf k).a_bound) hD).mono hB.scalar
  have hp':=scaledMean_norm hn _ x hp
  have hX {v : Spin n} (HV : LiteralStableAt J j z m a r R ρ δ v) : ‖phiSqrt (z v) r (a v)‖≤B := by
    apply (Real.le_sqrt (norm_nonneg _) (Real.exp_pos _).le).mpr (phiSqrt_bound _ _ _ HV.a_bound) |>.trans hB.root
  have hχ {v : Spin n} (HV : LiteralStableAt J j z m a r R ρ δ v) : |siteMean A v|≤B^2 := by
    apply (coefficient_mean_value A v (Real.exp_pos _).le (fun i=>?_) ).trans hB.square
    rw [abs_of_pos (phi_pos _ _ _)]
    exact (phi_le_exp ..).trans (Real.exp_le_exp.mpr (by linarith [HV.a_bound]))
  have hell {v : Spin n} : ‖(WithLp.toLp 2 (ell v) : Euclid n)‖≤B*Real.sqrt n :=
    (vectorNorm_logSlope (z v) r (a v)).trans (mul_le_mul_of_nonneg_right hB.two hd.le)
  have hDA (V : Euclid n) : columnNorm (fun k=>((spin x k/2) •
      (phiSqrt (z x) r (a x)*phiSqrt (z x) r (a x)-
        phiSqrt (z (flip x k)) r (a (flip x k))*phiSqrt (z (flip x k)) r (a (flip x k)))) V)≤B*‖V‖ := by
    simp only [phiSqrt_square]
    exact (diagonal_halfDiff_columns A x ha'.row_nonneg ha'.difference V).trans
      (mul_le_mul_of_nonneg_right hB.phi_row (norm_nonneg _))
  have hDu : columnNorm (fun k=>(spin x k/2) •
      ((WithLp.toLp 2 (initialU f z a r e x) : Euclid n)-WithLp.toLp 2 (initialU f z a r e (flip x k))))≤B := by
    rw [columnNorm_halfDiff]; exact hu.derivative
  have hDχ : columnNorm (fun k=>(spin x k/2)*(siteMean A x-siteMean A (flip x k)))≤B := by
    rw [columnNorm_scalar_halfDiff]
    exact (coefficient_mean_difference A x ha'.row_nonneg ha'.difference).trans hB.phi_row
  have hDm' : columnNorm (fun k=>(spin x k/2) •
      ((WithLp.toLp 2 (m x) : Euclid n)-WithLp.toLp 2 (m (flip x k))))≤B*Real.sqrt n := by
    rw [columnNorm_halfDiff]
    exact (frobenius_le_opNorm_sqrt _).trans (mul_le_mul_of_nonneg_right (hDm.trans hB.primary) hd.le)
  have hDell : columnNorm (fun k=>(spin x k/2) •
      ((WithLp.toLp 2 (ell x) : Euclid n)-WithLp.toLp 2 (ell (flip x k))))≤B*Real.sqrt n := by
    rw [columnNorm_halfDiff]
    exact (frobenius_by_rows _ hel'.row_nonneg hel'.difference).trans
      (mul_le_mul_of_nonneg_right hB.slope_row hd.le)
  have hDp : Real.sqrt n*columnNorm (fun k=>(spin x k/2)*
      (siteMean (initialP f z a r e) x-siteMean (initialP f z a r e) (flip x k)))≤B := by
    rw [columnNorm_scalar_halfDiff]; exact hp'.2
  have hEq : Equations j (siteMean A x) (n:ℝ)⁻¹ (siteMean (initialP f z a r e) x)
      (phiSqrt (z x) r (a x)*phiSqrt (z x) r (a x)) (toEuclideanCLM (𝕜:=ℝ) J)
      (WithLp.toLp 2 (initialU f z a r e x)) (WithLp.toLp 2 (m x))
      (WithLp.toLp 2 (fun i=>Real.tanh (r i))) (WithLp.toLp 2 (ell x))
      (WithLp.toLp 2 (w x)) (WithLp.toLp 2 (y x)) (c x) := by
    rw [phiSqrt_square]; exact h
  have hEqf k : Equations j (siteMean A (flip x k)) (n:ℝ)⁻¹ (siteMean (initialP f z a r e) (flip x k))
      (phiSqrt (z (flip x k)) r (a (flip x k))*phiSqrt (z (flip x k)) r (a (flip x k))) (toEuclideanCLM (𝕜:=ℝ) J)
      (WithLp.toLp 2 (initialU f z a r e (flip x k))) (WithLp.toLp 2 (m (flip x k)))
      (WithLp.toLp 2 (fun i=>Real.tanh (r i))) (WithLp.toLp 2 (ell (flip x k)))
      (WithLp.toLp 2 (w (flip x k))) (WithLp.toLp 2 (y (flip x k))) (c (flip x k)) := by
    rw [phiSqrt_square]; exact hf k
  have ht:=implicit_uniform_control j (siteMean A x) ((∑i,scalarVariance (z x i))/(n:ℝ)) (n:ℝ)⁻¹
    (siteMean (initialP f z a r e) x) (phiSqrt (z x) r (a x)) (toEuclideanCLM (𝕜:=ℝ) J)
    (WithLp.toLp 2 (initialU f z a r e x)) (WithLp.toLp 2 (m x))
    (WithLp.toLp 2 (fun i=>Real.tanh (r i))) (WithLp.toLp 2 (ell x))
    (WithLp.toLp 2 (fun i=>Real.tanh (z x i))) (WithLp.toLp 2 (w x)) (WithLp.toLp 2 (y x)) (c x)
    (fun k=>spin x k/2) (fun k=>siteMean A (flip x k)) (fun k=>siteMean (initialP f z a r e) (flip x k))
    (fun k=>c (flip x k)) (fun k=>(∑i,scalarVariance (z (flip x k) i))/(n:ℝ))
    (fun k=>phiSqrt (z (flip x k)) r (a (flip x k)))
    (fun k=>WithLp.toLp 2 (initialU f z a r e (flip x k))) (fun k=>WithLp.toLp 2 (m (flip x k)))
    (fun k=>WithLp.toLp 2 (ell (flip x k))) (fun k=>WithLp.toLp 2 (w (flip x k)))
    (fun k=>WithLp.toLp 2 (y (flip x k))) (fun k=>WithLp.toLp 2 (fun i=>Real.tanh (z (flip x k) i)))
    hδ hd (inv_nonneg.mpr hnR.le) hscale hB.nonneg (hX H) (fun k=>hX (Hf k)) (hJ.trans hB.matrix)
    (hχ H) (fun k=>hχ (Hf k)) hu.size H.m_size (fun k=>(Hf k).m_size) (vectorNorm_tanh r)
    hell (fun _=>hell) hp'.1 H.stable (fun k=>(Hf k).stable)
    (H.perturbation hn hδ hρ hsmall) (fun k=>(Hf k).perturbation hn hδ hρ hsmall)
    hEq hEqf hDA hDu hDχ hDm' hDell hDp
  rw [columnNorm_halfDiff,columnNorm_halfDiff,columnNorm_scalar_halfDiff] at ht
  exact implicit_tuple_small w y c x hd.le (uniformControlBudget_nonneg hδ hB.nonneg) ht
end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LiteralConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary SKGap.ImplicitSystem Matrix
variable {n : ℕ}

lemma literalBudget_exists (f : KernelExpr) (R T L : ℝ) (hT : 0≤T) :
    ∃B,LiteralBudget f R T L B := by
  let U:=ratioSmallBudget (.kernel f) T
  let P:=ratioSmallBudget ((RatioExpr.kernel f).d .z) T*kernelSmallBudget phiExpr R T
  let V:=(phiExpr.dBudget R+phiExpr.ddBudget R)*T
  let E:=((RatioExpr.kernel phiExpr.dz).dBudget+(RatioExpr.kernel phiExpr.dz).ddBudget)*T
  let B:=2+Real.sqrt (Real.exp (R/2))+|L|+T+U+P+V+E
  have hs:=Real.sqrt_nonneg (Real.exp (R/2))
  have hU:0≤U:=ratioSmallBudget_nonneg _ _ hT
  have hP:0≤P:=mul_nonneg (ratioSmallBudget_nonneg _ _ hT) (kernelSmallBudget_nonneg _ _ _ hT)
  have hV:0≤V:=mul_nonneg (add_nonneg (phiExpr.dBudget_nonneg _) (phiExpr.ddBudget_nonneg _)) hT
  have hE:0≤E:=mul_nonneg (add_nonneg (RatioExpr.dBudget_nonneg _) (RatioExpr.ddBudget_nonneg _)) hT
  have hB:0≤B:=by dsimp [B]; positivity
  have hsB : Real.sqrt (Real.exp (R/2))≤B:=by dsimp [B]; linarith [abs_nonneg L]
  refine ⟨B,⟨hB,?_,hsB,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · dsimp [B]; linarith [abs_nonneg L]
  · have h:=pow_le_pow_left₀ hs hsB 2
    rwa [Real.sq_sqrt (Real.exp_pos _).le] at h
  · dsimp [B]; linarith [le_abs_self L]
  all_goals dsimp [B]; linarith [abs_nonneg L]

lemma literal_system_extension (J : Interaction n) (j : ℝ) (f : KernelExpr)
    (z m : VectorFields n) (a : Spin n→ℝ) (r e : Fin n→ℝ)
    (hn : 0<n) {R ρ δ : ℝ} (hδ : 0<δ) (hρ : 0≤ρ)
    (hsmall : ρ≤δ/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1))) :
    ∃w y : VectorFields n,∃c : Spin n→ℝ,
      ∀x,LiteralStableAt J j z m a r R ρ δ x→LiteralEquations J j f z m w y a c r e x := by
  classical
  let P:=fun x (v : Euclid n×Euclid n×ℝ)=>
    LiteralStableAt J j z m a r R ρ δ x→
      Equations j ((∑i,phi (z x i) (r i) (a x))/(n:ℝ)) (n:ℝ)⁻¹
        (siteMean (initialP f z a r e) x) (phiDiagonal (z x) r (a x))
        (toEuclideanCLM (𝕜:=ℝ) J) (WithLp.toLp 2 (initialU f z a r e x)) (WithLp.toLp 2 (m x))
        (WithLp.toLp 2 (fun i=>Real.tanh (r i))) (WithLp.toLp 2 (fun i=>logSlope (z x i) (r i) (a x)))
        v.1 v.2.1 v.2.2
  have hex : ∀x,∃v,P x v := by
    intro x
    by_cases H:LiteralStableAt J j z m a r R ρ δ x
    · obtain ⟨v,hv,-⟩:=literal_implicit_exists_unique (z x) r (m x) (a x) j
        (siteMean (initialP f z a r e) x) (toEuclideanCLM (𝕜:=ℝ) J)
        (WithLp.toLp 2 (initialU f z a r e x)) hn hδ hρ H.a_bound H.a_small H.z_near H.m_near hsmall H.stable
      exact ⟨v,fun _=>hv⟩
    · exact ⟨0,fun H'=>False.elim (H H')⟩
  choose v hv using hex
  exact ⟨fun x=>(v x).1.ofLp,fun x=>(v x).2.1.ofLp,fun x=>(v x).2.2,hv⟩

theorem literal_implicit_construction_oai (j R ρ δ T L : ℝ) (f : KernelExpr)
    (hδ : 0<δ) (hρ : 0≤ρ) (hT : 0≤T)
    (hsmall : ρ≤δ/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1))) :
    ∃C≥0,∀n : ℕ,0<n→∀(J : Interaction n) (z m : VectorFields n)
      (a : Spin n→ℝ) (r e : Fin n→ℝ),SKGap.opNorm J≤L→vectorNorm e≤1→
      ∃w y : VectorFields n,∃c : Spin n→ℝ,
        (∀x,LiteralStableAt J j z m a r R ρ δ x→LiteralEquations J j f z m w y a c r e x) ∧
        (∀x,LiteralStableAt J j z m a r R ρ δ x→
          (∀k,LiteralStableAt J j z m a r R ρ δ (flip x k))→
          SKGap.opNorm (derivativeMatrix z x)+‖derivativeVector a x‖≤T→
          SKGap.opNorm (derivativeMatrix m x)≤T→
          SmallBound w x C ∧ SmallBound y x C ∧ |Real.sqrt n*c x|≤C ∧
            ‖derivativeVector (fun v=>Real.sqrt n*c v) x‖≤C) := by
  obtain ⟨B,hB⟩:=literalBudget_exists f R T L hT
  refine ⟨uniformControlBudget j δ B,uniformControlBudget_nonneg hδ hB.nonneg,?_⟩
  intro n hn J z m a r e hJ he
  obtain ⟨w,y,c,h⟩:=literal_system_extension J j f z m a r e hn hδ hρ hsmall
  refine ⟨w,y,c,h,?_⟩
  intro x H Hf hD hDm
  exact literal_initial_control J j f z m w y a c r e x hn hδ hρ hT hsmall hB hJ he
    H Hf hD hDm (h x H) (fun k=>h (flip x k) (Hf k))
end SKGapCutoff.Recipe

end
end

end OAI
end

theorem solution : type_of% @OAI.SKGapCutoff.Recipe.literal_implicit_construction_oai := @OAI.SKGapCutoff.Recipe.literal_implicit_construction_oai
