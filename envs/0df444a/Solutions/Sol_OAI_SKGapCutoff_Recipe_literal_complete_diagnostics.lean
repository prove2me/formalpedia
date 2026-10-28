-- Prove2me | solution 1 for OAI.SKGapCutoff.Recipe.literal_complete_diagnostics
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:07:19.761921+00:00
-- url     : https://prove2.me/submissions/68f6e030-b6b7-4f01-a215-5c4694a1d0eb

import Mathlib
import Definitions.Def_OAIQ072A002
import Theorems.Thm_OAI_SKGapCutoff_Recipe_literal_implicit_construction

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

lemma segment_taylor (F : E→ℝ) (F' : E→E→L[ℝ]ℝ) (x y : E) {L : ℝ}
    (hL : 0≤L)
    (hF : ∀t∈Icc (0:ℝ) 1,HasFDerivAt F (F' (x+t • (y-x))) (x+t • (y-x)))
    (hLip : ∀t∈Icc (0:ℝ) 1,‖F' (x+t • (y-x))-F' x‖≤L*‖t • (y-x)‖) :
    |F y-F x-F' x (y-x)|≤L*‖y-x‖^2 := by
  let g : ℝ→ℝ:=fun t=>F (x+t • (y-x))-F x-t*(F' x (y-x))
  let g' : ℝ→ℝ:=fun t=>(F' (x+t • (y-x))-F' x) (y-x)
  have hg (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : HasDerivAt g (g' t) t := by
    have H:=(((hF t ht).comp_hasDerivAt t
      (((hasDerivAt_id t).smul_const (y-x)).const_add x)).sub_const (F x)).sub
      ((hasDerivAt_id t).mul_const (F' x (y-x)))
    convert! H using 1
    all_goals try with_reducible_and_instances rfl
    simp only [g',sub_apply,one_smul,one_mul]
  have hb (t : ℝ) (ht : t∈Ico (0:ℝ) 1) : ‖g' t‖≤L*‖y-x‖^2 := by
    calc
      _ ≤ ‖F' (x+t • (y-x))-F' x‖*‖y-x‖ := (F' (x+t • (y-x))-F' x).le_opNorm _
      _ ≤ (L*‖t • (y-x)‖)*‖y-x‖ := mul_le_mul_of_nonneg_right (hLip t ⟨ht.1,ht.2.le⟩) (norm_nonneg _)
      _ ≤ (L*‖y-x‖)*‖y-x‖ := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
        gcongr
        exact mul_le_of_le_one_left (norm_nonneg _) ht.2.le
      _ = _ := by ring
  have H:=norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t ht=>(hg t ht).hasDerivWithinAt) hb
  simpa only [g,one_smul,zero_smul,add_sub_cancel,add_zero,one_mul,zero_mul,sub_self,sub_zero,
    Real.norm_eq_abs] using H

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

lemma coefficient_linearization (i : Fin n) (P : Spin n→E) (x : Spin n)
    (F : E→ℝ) (T : E→L[ℝ]ℝ) :
    halfDiff i (fun y=>F (P y)) x-T (flipHalfDiff i P x)=
      (-spin x i/2)*(F (P (flip x i))-F (P x)-T (P (flip x i)-P x)) := by
  rw [halfDiff_as_flip]
  simp only [flipHalfDiff,map_smul,map_sub,smul_eq_mul]
  ring

lemma coefficient_taylor (i : Fin n) (P : Spin n→E) (x : Spin n)
    (F : E→ℝ) (F' : E→E→L[ℝ]ℝ) {L : ℝ} (hL : 0≤L)
    (hF : ∀t∈Icc (0:ℝ) 1,HasFDerivAt F
      (F' (P x+t • (P (flip x i)-P x))) (P x+t • (P (flip x i)-P x)))
    (hLip : ∀t∈Icc (0:ℝ) 1,
      ‖F' (P x+t • (P (flip x i)-P x))-F' (P x)‖≤L*‖t • (P (flip x i)-P x)‖) :
    |halfDiff i (fun y=>F (P y)) x-F' (P x) (flipHalfDiff i P x)|≤
      2*L*‖flipHalfDiff i P x‖^2 := by
  have H:=SKGap.SourceTaylor.segment_taylor F F' (P x) (P (flip x i)) hL hF hLip
  rw [coefficient_linearization,abs_mul,abs_div,abs_neg,abs_spin_eq_one,
    abs_of_pos (by norm_num : (0:ℝ)<2),flipHalfDiff_norm]
  calc
    _ ≤ (1/2:ℝ)*(L*‖P (flip x i)-P x‖^2) := mul_le_mul_of_nonneg_left H (by norm_num)
    _ = _ := by ring

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

lemma matrix_entry_le_opNorm (M : Matrix ι ι ℝ) (i k : ι) : |M i k| ≤ opNorm M := by
  have h : |M i k| ≤ ‖colVec M k‖ := by
    simpa only [colVec,Real.norm_eq_abs] using (PiLp.norm_apply_le (colVec M k) i)
  exact h.trans (colVec_norm_le M k)

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

local instance instFactLeENNRealOfNat_solutions_r8ba2f4_1 : Fact (1≤(4:ENNReal)) := ⟨by norm_num⟩
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

lemma linear_apply_coordinates {α : Type*} [Fintype α] [DecidableEq α]
    (T : (α→ℝ)→L[ℝ]ℝ) (v : α→ℝ) : T v=∑l,v l*T (Pi.single l 1) := by
  have he : v=∑l,v l • Pi.single l (1:ℝ) := by
    funext i
    simp [Finset.sum_apply,Pi.single_apply]
  conv_lhs => rw [he]
  simp only [map_sum,map_smul,smul_eq_mul]

lemma flipHalfDiff_coordinate {α : Type*} [Fintype α] (P : Spin n→α→ℝ)
    (k : Fin n) (x : Spin n) (l : α) :
    flipHalfDiff k P x l=halfDiff k (fun y=>P y l) x := by
  rw [halfDiff_as_flip]
  dsimp only [flipHalfDiff,Pi.smul_apply,Pi.sub_apply,smul_eq_mul]
  ring

lemma coefficient_chain (H : ι→VectorFields n) (θ : κ→Spin n→ℝ) (x : Spin n) (i k : Fin n)
    (T : Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ) :
    T (flipHalfDiff k (fun y=>localArgs H θ y i) x)=
      (∑l,partialAt T (.inl l)*derivativeMatrix (H l) x i k)+
      ∑α,partialAt T (.inr α)*halfDiff k (θ α) x := by
  rw [linear_apply_coordinates,Fintype.sum_sum_type]
  simp only [flipHalfDiff_coordinate,partialAt,localArgs,Sum.elim_inl,Sum.elim_inr,derivativeMatrix,mul_comm]

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

lemma source_derivative_exact (H : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ)
    (F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ)
    (s : VectorFields n) (x : Spin n) (i k : Fin n) :
    derivativeMatrix (fun x i=>coefficient H θ F x i*s x i) x i k=
      coefficient H θ F x i*derivativeMatrix s x i k+
      (∑l,s x i*localPartial H θ F' (.inl l) x i*derivativeMatrix (H l) x i k)+
      (∑α,s x i*localPartial H θ F' (.inr α) x i*halfDiff k (θ α) x)+
      s x i*taylorError H θ F F' x i k-
      2*spin x k*derivativeMatrix (coefficient H θ F) x i k*derivativeMatrix s x i k := by
  dsimp only [taylorError,localPartial]
  rw [coefficient_chain]
  simp only [←Finset.mul_sum,mul_assoc]
  rw [derivativeMatrix,halfDiff_mul]
  dsimp only [derivativeMatrix]
  ring

omit [DecidableEq ι] [DecidableEq κ] in
lemma taylor_error_bound (H : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ)
    (F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ)
    (x : Spin n) (i k : Fin n) {L Q T : ℝ} (hL : 0≤L) (hQ : 0≤Q) (hT : 0≤T)
    (hargs : ‖flipHalfDiff k (fun y=>localArgs H θ y i) x‖≤Q+T)
    (hF : ∀t∈Set.Icc (0:ℝ) 1,HasFDerivAt (F i)
      (F' i (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i)))
      (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i)))
    (hLip : ∀t∈Set.Icc (0:ℝ) 1,
      ‖F' i (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i))-
        F' i (localArgs H θ x i)‖≤L*‖t • (localArgs H θ (flip x k) i-localArgs H θ x i)‖) :
    |taylorError H θ F F' x i k|≤4*L*(Q^2+Q*T+T^2) := by
  have h:=coefficient_taylor k (fun y=>localArgs H θ y i) x (F i) (F' i) hL hF hLip
  have hs:=(pow_le_pow_iff_left₀ (norm_nonneg _) (add_nonneg hQ hT)
    (by decide : 2 ≠ 0)).2 hargs
  have hh:=mul_le_mul_of_nonneg_left hs (mul_nonneg (by norm_num : (0:ℝ)≤2) hL)
  change |taylorError H θ F F' x i k|≤_ at h
  refine h.trans (hh.trans ?_)
  nlinarith [sq_nonneg Q,sq_nonneg T,mul_nonneg hL (sq_nonneg Q),mul_nonneg hL (sq_nonneg T)]

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

local instance instFactLeENNRealOfNat_solutions_r8ba2f4_2 : Fact (1≤(4:ENNReal)) := ⟨by norm_num⟩
lemma real_op_norm_nonneg (P : Matrix ι ι ℝ) : 0≤opNorm P := norm_nonneg _

lemma cauchy_bound {α : Type*} [Fintype α] (f g : α→ℝ) {A B : ℝ}
    (hA : 0≤A) (hB : 0≤B) (hf : (∑i,(f i)^2)≤A^2) (hg : (∑i,(g i)^2)≤B^2) :
    |∑i,f i*g i|≤A*B := by
  have H:=Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  have hh:=mul_le_mul hf hg (Finset.sum_nonneg (fun i _=>sq_nonneg _)) (sq_nonneg _)
  nlinarith [sq_abs (∑i,f i*g i),mul_nonneg hA hB,abs_nonneg (∑i,f i*g i)]

omit [DecidableEq ι] in
lemma double_cauchy (f g : ι→ι→ℝ) {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hf : (∑i,∑k,(f i k)^2)≤A^2) (hg : (∑i,∑k,(g i k)^2)≤B^2) :
    |∑i,∑k,f i k*g i k|≤A*B := by
  have H:=cauchy_bound (fun a : ι×ι=>f a.1 a.2) (fun a=>g a.1 a.2) hA hB
    (by simpa only [Fintype.sum_prod_type] using hf) (by simpa only [Fintype.sum_prod_type] using hg)
  simpa only [Fintype.sum_prod_type] using H

omit [DecidableEq ι] in
lemma trace_le_traceAbsolute (P E : Matrix ι ι ℝ) : |trace (P*E)|≤traceAbsolute P E := by
  rw [trace_mul_comm]
  simp only [trace,diag,Matrix.mul_apply]
  apply (Finset.abs_sum_le_sum_abs ..).trans
  apply Finset.sum_le_sum; intro i _
  exact (Finset.abs_sum_le_sum_abs ..).trans_eq (by simp only [abs_mul,mul_comm])

lemma matrix_column_square_le (P : Matrix ι ι ℝ) (i : ι) :
    (∑k,(P k i)^2)≤(opNorm P)^2 := by
  have H:=pow_le_pow_left₀ (norm_nonneg (colVec P i)) (colVec_norm_le P i) 2
  simpa only [colVec,EuclideanSpace.real_norm_sq_eq] using H

lemma matrix_row_square_le (P : Matrix ι ι ℝ) (i : ι) :
    (∑k,(P i k)^2)≤(opNorm P)^2 := by
  simpa only [Matrix.transpose_apply,opNorm_transpose] using matrix_column_square_le Pᵀ i

lemma small_column_square (P : Matrix ι ι ℝ) (s : ι→ℝ) :
    (∑i,∑k,(|P k i| * |s i|)^2)≤(opNorm P)^2*(∑i,(s i)^2) := by
  simp only [mul_pow,sq_abs]
  calc
    _ ≤ ∑i,(opNorm P)^2*(s i)^2 := by
      apply Finset.sum_le_sum; intro i _
      rw [←Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (matrix_column_square_le P i) (sq_nonneg _)
    _ = _ := by rw [←Finset.mul_sum]

lemma small_row_square (P : Matrix ι ι ℝ) (t : ι→ℝ) :
    (∑i,∑k,(|P k i| * |t k|)^2)≤(opNorm P)^2*(∑k,(t k)^2) := by
  rw [Finset.sum_comm]
  simpa only [Matrix.transpose_apply,opNorm_transpose] using small_column_square Pᵀ t

lemma quadratic_trace_bound (P Q : Matrix ι ι ℝ) (s : ι→ℝ) {S B : ℝ}
    (hS : 0≤S) (hB : 0≤B) (hs : (∑i,(s i)^2)≤S^2)
    (hQ : (∑i,∑k,(Q i k)^4)≤B^4) :
    (∑i,∑k,|P k i| * |s i| *(Q i k)^2)≤opNorm P*S*B^2 := by
  have H:=double_cauchy (fun i k=>|P k i| * |s i|) (fun i k=>(Q i k)^2)
    (mul_nonneg (real_op_norm_nonneg P) hS) (pow_nonneg hB 2)
    ((small_column_square P s).trans (by
      simpa only [mul_pow] using mul_le_mul_of_nonneg_left hs (sq_nonneg (opNorm P))))
    (by simpa only [←pow_mul] using hQ)
  exact (le_abs_self _).trans H

lemma mixed_trace_bound (P Q : Matrix ι ι ℝ) (s t : ι→ℝ) {S T B : ℝ}
    (hS : 0≤S) (hT : 0≤T) (hB : 0≤B)
    (hs : (∑i,(s i)^2)≤S^2) (ht : (∑k,(t k)^2)≤T^2)
    (hQ : ∀i,(∑k,(Q i k)^2)≤B^2) :
    (∑i,∑k,|P k i| * |s i| * |Q i k| * |t k|)≤opNorm P*T*(S*B) := by
  have hf : (∑i,∑k,(|P k i| * |t k|)^2)≤(opNorm P*T)^2 :=
    (small_row_square P t).trans (by simpa only [mul_pow] using (mul_le_mul_of_nonneg_left ht (sq_nonneg (opNorm P))))
  have hg : (∑i,∑k,(|s i| * |Q i k|)^2)≤(S*B)^2 := by
    simp only [mul_pow,sq_abs,←Finset.mul_sum]
    calc
      _ ≤ ∑i,(s i)^2*B^2 := Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_left (hQ i) (sq_nonneg _))
      _ = (∑i,(s i)^2)*B^2 := (Finset.sum_mul ..).symm
      _ ≤ S^2*B^2 := mul_le_mul_of_nonneg_right hs (sq_nonneg _)
  have H:=double_cauchy (fun i k=>|P k i| * |t k|) (fun i k=>|s i| * |Q i k|)
    (mul_nonneg (real_op_norm_nonneg P) hT) (mul_nonneg hS hB) hf hg
  apply (le_abs_self _).trans
  have he : (∑i,∑k,|P k i| * |s i| * |Q i k| * |t k|) =
      ∑i,∑k,|P k i| * |t k| * (|s i| * |Q i k|) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro k _; ring
  rw [he]
  exact H

lemma parameter_square_trace_bound (P : Matrix ι ι ℝ) (s t : ι→ℝ) {S T : ℝ}
    (hS : 0≤S) (hT : 0≤T) (hs : (∑i,(s i)^2)≤S^2) (ht : (∑k,(t k)^2)≤T^2) :
    (∑i,∑k,|P k i| * |s i| *(t k)^2)≤opNorm P*T*(S*T) := by
  have hf : (∑i,∑k,(|P k i| * |t k|)^2)≤(opNorm P*T)^2 :=
    (small_row_square P t).trans (by simpa only [mul_pow] using (mul_le_mul_of_nonneg_left ht (sq_nonneg (opNorm P))))
  have hg : (∑i,∑k,(|s i| * |t k|)^2)≤(S*T)^2 := by
    simp only [mul_pow,sq_abs,←Finset.mul_sum,←Finset.sum_mul]
    exact mul_le_mul hs ht (Finset.sum_nonneg (fun k _=>sq_nonneg _)) (sq_nonneg _)
  have H:=double_cauchy (fun i k=>|P k i| * |t k|) (fun i k=>|s i| * |t k|)
    (mul_nonneg (real_op_norm_nonneg P) hT) (mul_nonneg hS hT) hf hg
  apply (le_abs_self _).trans
  have he : (∑i,∑k,|P k i| * |s i| * (t k)^2) =
      ∑i,∑k,|P k i| * |t k| * (|s i| * |t k|) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro k _
    rw [← sq_abs (t k)]; ring
  rw [he]
  exact H

theorem source_taylor_trace_bound (P E Q : Matrix ι ι ℝ) (s t : ι→ℝ) {C S T B R : ℝ}
    (hC : 0≤C) (hS : 0≤S) (hT : 0≤T) (hB : 0≤B) (hR : 0≤R)
    (hs : (∑i,(s i)^2)≤S^2) (ht : (∑k,(t k)^2)≤T^2)
    (hQ4 : (∑i,∑k,(Q i k)^4)≤B^4) (hQr : ∀i,(∑k,(Q i k)^2)≤R^2)
    (hE : ∀i k,|E i k|≤C*|s i| *((Q i k)^2+|Q i k| * |t k|+(t k)^2)) :
    |trace (P*E)|≤C*opNorm P*S*(B^2+R*T+T^2) := by
  apply (trace_le_traceAbsolute P E).trans
  calc
    _ ≤ ∑i,∑k,|P k i| *(C*|s i| *((Q i k)^2+|Q i k| * |t k|+(t k)^2)) := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro k _
      exact mul_le_mul_of_nonneg_left (hE i k) (abs_nonneg _)
    _ = C*((∑i,∑k,|P k i| * |s i| *(Q i k)^2)+
      (∑i,∑k,|P k i| * |s i| * |Q i k| * |t k|)+
      (∑i,∑k,|P k i| * |s i| *(t k)^2)) := by
      simp only [Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro k _; ring
    _ ≤ C*(opNorm P*S*B^2+opNorm P*T*(S*R)+opNorm P*T*(S*T)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add
        (quadratic_trace_bound P Q s hS hB hs hQ4)
        (mixed_trace_bound P Q s t hS hT hR hs ht hQr))
        (parameter_square_trace_bound P s t hS hT hs ht)) hC
    _ = _ := by ring

omit [DecidableEq ι] in
lemma fourth_holder (P D Q : Matrix ι ι ℝ) {B S R : ℝ}
    (hB : 0≤B) (hS : 0≤S) (hR : 0≤R)
    (hP : (∑i,∑k,(P i k)^4)≤B^4) (hD : (∑i,∑k,(D i k)^2)≤S^2)
    (hQ : (∑i,∑k,(Q i k)^4)≤R^4) :
    (∑i,∑k,|P i k| * |D i k| * |Q i k|)≤S*(B*R) := by
  have H₁:=double_cauchy (fun i k=>(P i k)^2) (fun i k=>(Q i k)^2)
    (sq_nonneg B) (sq_nonneg R) (by simpa only [←pow_mul] using hP)
    (by simpa only [←pow_mul] using hQ)
  have H₂ : (∑i,∑k,(|P i k| * |Q i k|)^2)≤(B*R)^2 := by
    simp only [mul_pow,sq_abs]
    exact (le_abs_self _).trans H₁
  have H₃:=double_cauchy (fun i k=>|D i k|) (fun i k=>|P i k| * |Q i k|)
    hS (mul_nonneg hB hR) (by simpa only [sq_abs] using hD) H₂
  apply (le_abs_self _).trans
  have he : (∑i,∑k,|P i k| * |D i k| * |Q i k|) =
      ∑i,∑k,|D i k| * (|P i k| * |Q i k|) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro k _; ring
  rw [he]; exact H₃

lemma sum_split_diagonal (f : ι→ι→ℝ) :
    (∑i,∑k,f i k)=(∑i,f i i)+(∑i,∑k,if i=k then 0 else f i k) := by
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  have he : f i i=∑k,if i=k then f i k else 0 := by simp
  rw [he,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro k _
  split_ifs <;> simp

lemma diagonal_product_trace_bound (P D Q : Matrix ι ι ℝ) {S R : ℝ}
    (hS : 0≤S) (hR : 0≤R) (hD : (∑i,(D i i)^2)≤S^2)
    (hQ : (∑i,(Q i i)^2)≤R^2) :
    (∑i,|P i i| * |D i i| * |Q i i|)≤opNorm P*(S*R) := by
  calc
    _ ≤ ∑i,opNorm P*(|D i i| * |Q i i|) := by
      apply Finset.sum_le_sum; intro i _
      nlinarith [mul_le_mul_of_nonneg_right (matrix_entry_le_opNorm P i i)
        (mul_nonneg (abs_nonneg (D i i)) (abs_nonneg (Q i i)))]
    _ = opNorm P*(∑i,|D i i| * |Q i i|) := by rw [Finset.mul_sum]
    _ ≤ opNorm P*(S*R) := by
      apply mul_le_mul_of_nonneg_left _ (real_op_norm_nonneg P)
      exact (le_abs_self _).trans (cauchy_bound (fun i=>|D i i|) (fun i=>|Q i i|)
        hS hR (by simpa only [sq_abs] using hD) (by simpa only [sq_abs] using hQ))

lemma parameter_product_trace_bound (P D : Matrix ι ι ℝ) (t : ι→ℝ) {S T : ℝ}
    (hS : 0≤S) (hT : 0≤T) (hD : (∑i,∑k,(D i k)^2)≤S^2)
    (ht : (∑k,(t k)^2)≤T^2) :
    (∑i,∑k,|P k i| * |D i k| * |t k|)≤S*(opNorm P*T) := by
  have hf : (∑i,∑k,(|P k i| * |t k|)^2)≤(opNorm P*T)^2 :=
    (small_row_square P t).trans (by simpa only [mul_pow] using
      (mul_le_mul_of_nonneg_left ht (sq_nonneg (opNorm P))))
  have H:=double_cauchy (fun i k=>|D i k|) (fun i k=>|P k i| * |t k|)
    hS (mul_nonneg (real_op_norm_nonneg P) hT) (by simpa only [sq_abs] using hD) hf
  apply (le_abs_self _).trans
  have he : (∑i,∑k,|P k i| * |D i k| * |t k|) =
      ∑i,∑k,|D i k| * (|P k i| * |t k|) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro k _; ring
  rw [he]; exact H

theorem source_product_trace_bound (P E D Q : Matrix ι ι ℝ) (t : ι→ℝ) {C S T B R L : ℝ}
    (hC : 0≤C) (hS : 0≤S) (hT : 0≤T) (hB : 0≤B) (hR : 0≤R) (hL : 0≤L)
    (hD : (∑i,∑k,(D i k)^2)≤S^2) (ht : (∑k,(t k)^2)≤T^2)
    (hP : (∑i,∑k,if i=k then 0 else (P k i)^4)≤B^4)
    (hQ : (∑i,∑k,(Q i k)^4)≤R^4) (hQd : (∑i,(Q i i)^2)≤L^2)
    (hE : ∀i k,|E i k|≤C*|D i k| *(|Q i k|+|t k|)) :
    |trace (P*E)|≤C*S*(B*R+opNorm P*(L+T)) := by
  have hDd : (∑i,(D i i)^2)≤S^2 := by
    apply le_trans _ hD
    exact Finset.sum_le_sum (fun i _=>Finset.single_le_sum (fun k _=>sq_nonneg (D i k))
      (Finset.mem_univ i))
  let O : Matrix ι ι ℝ := fun i k=>if i=k then 0 else P k i
  have hO : (∑i,∑k,(O i k)^4)≤B^4 := by
    simpa only [O,ite_pow,zero_pow (by decide : 4≠0)] using hP
  have hOff := fourth_holder O D Q hB hS hR hO hD hQ
  have heOff : (∑i,∑k,if i=k then 0 else |P k i| * |D i k| * |Q i k|) =
      ∑i,∑k,|O i k| * |D i k| * |Q i k| := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro k _
    dsimp only [O]; split_ifs <;> simp
  have hProd : (∑i,∑k,|P k i| * |D i k| * |Q i k|)≤opNorm P*(S*L)+S*(B*R) := by
    rw [sum_split_diagonal,heOff]
    exact add_le_add (diagonal_product_trace_bound P D Q hS hL hDd hQd) hOff
  apply (trace_le_traceAbsolute P E).trans
  calc
    _ ≤ ∑i,∑k,|P k i| *(C*|D i k| *(|Q i k|+|t k|)) := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro k _
      exact mul_le_mul_of_nonneg_left (hE i k) (abs_nonneg _)
    _ = C*((∑i,∑k,|P k i| * |D i k| * |Q i k|)+
        (∑i,∑k,|P k i| * |D i k| * |t k|)) := by
      simp only [Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro k _; ring
    _ ≤ C*(opNorm P*(S*L)+S*(B*R)+S*(opNorm P*T)) :=
      mul_le_mul_of_nonneg_left (add_le_add hProd
        (parameter_product_trace_bound P D t hS hT hD ht)) hC
    _ = _ := by ring

lemma rank_one_trace_bound (P : Matrix ι ι ℝ) (u v : EuclideanSpace ℝ ι) :
    |trace (P*Matrix.of (fun i k=>u i*v k))|≤opNorm P*‖u‖*‖v‖ := by
  have H:=abs_real_inner_le_norm v (P.toEuclideanLin.toContinuousLinearMap u)
  have he : trace (P*Matrix.of (fun i k=>u i*v k))=
      inner ℝ v (P.toEuclideanLin.toContinuousLinearMap u) := by
    change (∑i,∑k,P i k*(u k*v i))=∑i,(∑k,P i k*u k)*v i
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro k _; ring
  rw [he]
  apply H.trans
  have h:=mul_le_mul_of_nonneg_left
    (P.toEuclideanLin.toContinuousLinearMap.le_opNorm u) (norm_nonneg v)
  change ‖v‖*‖P.toEuclideanLin.toContinuousLinearMap u‖≤opNorm P*‖u‖*‖v‖
  change ‖v‖*‖P.toEuclideanLin.toContinuousLinearMap u‖≤‖v‖*(opNorm P*‖u‖) at h
  nlinarith only [h]

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

lemma scaled_frobenius_by_rows (D : Interaction n) (a : ℝ) {C P : ℝ}
    (hC : 0≤C) (hP : 0≤P) (ha : (n:ℝ)*a^2≤C^2)
    (hD : ∀i,∑k,(D i k)^2≤P^2) : ‖a • D‖≤C*P := by
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hC hP)
  simp only [←sq]
  rw [SKGap.frobenius_sq,mul_pow]
  simp only [Matrix.smul_apply,smul_eq_mul,mul_pow]
  calc
    _ ≤ ∑_i:Fin n,a^2*P^2 := Finset.sum_le_sum fun i _=>by
      rw [←Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hD i) (sq_nonneg _)
    _ = ((n:ℝ)*a^2)*P^2 := by simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right ha (sq_nonneg _)

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

lemma derivativeMatrix_add (U V : VectorFields n) (x : Spin n) :
    derivativeMatrix (fun x i=>U x i+V x i) x=derivativeMatrix U x+derivativeMatrix V x := by
  ext i k; simp only [derivativeMatrix,halfDiff,Matrix.add_apply]; ring

lemma SmallBound.mono {U : VectorFields n} {x : Spin n} {C D : ℝ}
    (h : SmallBound U x C) (hCD : C≤D) : SmallBound U x D :=
  ⟨h.nonneg.trans hCD,h.size.trans hCD,h.derivative.trans hCD⟩

lemma SmallBound.seed (s : Fin n→ℝ) (x : Spin n) :
    SmallBound (fun _=>s) x (vectorNorm s) := by
  refine ⟨vectorNorm_nonneg _,le_rfl,?_⟩
  have he : derivativeMatrix (fun _=>s) x=0 := by ext i k; simp [derivativeMatrix,halfDiff]
  rw [he,norm_zero]; exact vectorNorm_nonneg _

lemma SmallBound.add {U V : VectorFields n} {x : Spin n} {C D : ℝ}
    (hU : SmallBound U x C) (hV : SmallBound V x D) :
    SmallBound (fun x i=>U x i+V x i) x (C+D) := by
  refine ⟨add_nonneg hU.nonneg hV.nonneg,(vectorNorm_add _ _).trans (add_le_add hU.size hV.size),?_⟩
  rw [derivativeMatrix_add]
  exact (norm_add_le _ _).trans (add_le_add hU.derivative hV.derivative)

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
-- module Solutions.OAIQ072_SK.SKGap_Matrix_Trace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix SKGap.SourceError
variable {n : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma SegmentRegular.partial_bound {H : ι→VectorFields n} {θ : κ→Spin n→ℝ}
    {F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ}
    {F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ}
    {x : Spin n} {C : ℝ} (h : SegmentRegular H θ F F' x C) (i : Fin n) (l : ι⊕κ) :
    |localPartial H θ F' l x i|≤C := by
  have hb : ‖F' i (localArgs H θ x i)‖≤C := by simpa using h.bound i i 0 (by constructor <;> norm_num)
  have hs : ‖(Pi.single l (1:ℝ) : Args (ι:=ι) (κ:=κ))‖≤1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
    intro a; simp only [Pi.single_apply]; split_ifs <;> norm_num
  have h₁ := (F' i (localArgs H θ x i)).le_opNorm (Pi.single l 1)
  exact h₁.trans ((mul_le_mul hb hs (norm_nonneg _) h.nonneg).trans_eq (mul_one C))

lemma sourceError_eq (H : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ)
    (F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ)
    (s : VectorFields n) (x : Spin n) :
    sourceError H θ F F' s x=
      (∑α,Matrix.of (fun i k=>(s x i*localPartial H θ F' (.inr α) x i)*halfDiff k (θ α) x))+
      Matrix.of (fun i k=>s x i*taylorError H θ F F' x i k)-
      Matrix.of (fun i k=>2*spin x k*derivativeMatrix (coefficient H θ F) x i k*derivativeMatrix s x i k) := by
  ext i k
  simp only [sourceError,Matrix.sub_apply,Matrix.diagonal_mul,Matrix.sum_apply,Matrix.add_apply,Matrix.of_apply]
  rw [source_derivative_exact]
  ring

lemma sourceError_trace (H : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ)
    (F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ)
    (s : VectorFields n) (x : Spin n) (P : Interaction n) {C S T B R L O : ℝ}
    (h : SegmentRegular H θ F F' x C) (hS : 0≤S) (hT : 0≤T) (hB : 0≤B)
    (hR : 0≤R) (hL : 0≤L) (hO : 0≤O)
    (hs : vectorNorm (s x)≤S) (hds : ‖derivativeMatrix s x‖≤S)
    (ht : vectorNorm (parameterIncrement θ x)≤T)
    (hQ4 : (∑i,∑k,(primaryIncrement H x i k)^4)≤B^4)
    (hQr : ∀i,(∑k,(primaryIncrement H x i k)^2)≤R^2)
    (hQd : (∑i,(primaryIncrement H x i i)^2)≤L^2)
    (hP : (∑i,∑k,if i=k then 0 else (P k i)^4)≤O^4) :
    |trace (P*sourceError H θ F F' s x)|≤
      SKGap.opNorm P*C*S*(∑α,‖derivativeVector (θ α) x‖)+
      4*C*SKGap.opNorm P*S*(B^2+R*T+T^2)+
      2*C*S*(O*B+SKGap.opNorm P*(L+T)) := by
  let Q := primaryIncrement H x
  let t := parameterIncrement θ x
  have hQ : ∀i k,0≤Q i k := fun i k=>Finset.sum_nonneg fun _ _=>abs_nonneg _
  have htt : ∀k,0≤t k := fun k=>Finset.sum_nonneg fun _ _=>abs_nonneg _
  have hs2 : (∑i,(s x i)^2)≤S^2 := by rw [←vectorNorm_sq]; exact pow_le_pow_left₀ (vectorNorm_nonneg _) hs 2
  have ht2 : (∑k,(t k)^2)≤T^2 := by rw [←vectorNorm_sq]; exact pow_le_pow_left₀ (vectorNorm_nonneg _) ht 2
  have hds2 : (∑i,∑k,(derivativeMatrix s x i k)^2)≤S^2 := by
    rw [←SKGap.frobenius_sq]; exact pow_le_pow_left₀ (norm_nonneg _) hds 2
  have htaylor := source_taylor_trace_bound P (Matrix.of (fun i k=>s x i*taylorError H θ F F' x i k)) Q (s x) t
    (mul_nonneg (by norm_num : (0:ℝ)≤4) h.nonneg) hS hT hB hR hs2 ht2 hQ4 hQr (by
      intro i k
      simp only [Matrix.of_apply,abs_mul,abs_of_nonneg (hQ i k),abs_of_nonneg (htt k)]
      have hh := taylor_error_bound H θ F F' x i k h.nonneg (hQ i k) (htt k)
        (local_argument_bound H θ x i k) (h.deriv i k) (h.lip i k)
      nlinarith [mul_le_mul_of_nonneg_left hh (abs_nonneg (s x i))])
  have hproduct := source_product_trace_bound P
    (Matrix.of (fun i k=>2*spin x k*derivativeMatrix (coefficient H θ F) x i k*derivativeMatrix s x i k))
    (derivativeMatrix s x) Q t (mul_nonneg (by norm_num : (0:ℝ)≤2) h.nonneg)
    hS hT hO hB hL hds2 ht2 hP hQ4 hQd (by
      intro i k
      simp only [Matrix.of_apply,abs_mul,abs_spin_eq_one,mul_one,abs_of_nonneg (hQ i k),abs_of_nonneg (htt k)]
      norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)]
      have hh := (coefficient_lipschitz k (fun y=>localArgs H θ y i) x (F i) (F' i)
        h.nonneg (h.deriv i k) (h.bound i k)).trans
          (mul_le_mul_of_nonneg_left (local_argument_bound H θ x i k) h.nonneg)
      change |derivativeMatrix (coefficient H θ F) x i k|≤C*(Q i k+t k) at hh
      nlinarith [mul_le_mul_of_nonneg_right hh (abs_nonneg (derivativeMatrix s x i k))])
  have hrank (α : κ) :
      |trace (P*Matrix.of (fun i k=>(s x i*localPartial H θ F' (.inr α) x i)*halfDiff k (θ α) x))|≤
        SKGap.opNorm P*C*S*‖derivativeVector (θ α) x‖ := by
    have hu : vectorNorm (fun i=>s x i*localPartial H θ F' (.inr α) x i)≤C*S := by
      have H₁ := (vectorNorm_mul (fun i=>localPartial H θ F' (.inr α) x i) (s x) h.nonneg
        (fun i=>h.partial_bound i (.inr α))).trans (mul_le_mul_of_nonneg_left hs h.nonneg)
      simpa only [mul_comm] using H₁
    have HH:=rank_one_trace_bound P
      (WithLp.toLp 2 (fun i=>s x i*localPartial H θ F' (.inr α) x i)) (derivativeVector (θ α) x)
    apply HH.trans
    change SKGap.opNorm P*vectorNorm _*‖derivativeVector (θ α) x‖≤_
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu (real_op_norm_nonneg P))
      (norm_nonneg (derivativeVector (θ α) x))]
  have hranks : |trace (P*(∑α,Matrix.of (fun i k=>(s x i*localPartial H θ F' (.inr α) x i)*halfDiff k (θ α) x)))|≤
      SKGap.opNorm P*C*S*(∑α,‖derivativeVector (θ α) x‖) := by
    rw [Matrix.mul_sum,trace_sum]
    exact (Finset.abs_sum_le_sum_abs ..).trans ((Finset.sum_le_sum fun α _=>hrank α).trans_eq (by rw [Finset.mul_sum]))
  rw [sourceError_eq,mul_sub,mul_add,trace_sub,trace_add]
  exact (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add hranks htaylor)) hproduct)

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
-- module Solutions.OAIQ072_SK.SKGap_Matrix_CorrectionTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix SKGap.SourceError
variable {n : ℕ}

lemma trace_frobenius (P E : Interaction n) : |trace (P*E)|≤‖P‖*‖E‖ := by
  have H := double_cauchy (fun i k=>P k i) (fun i k=>E i k)
    (norm_nonneg P) (norm_nonneg E)
    (by rw [Finset.sum_comm]; exact le_of_eq (SKGap.frobenius_sq P).symm)
    (le_of_eq (SKGap.frobenius_sq E).symm)
  rw [Matrix.trace_mul_comm]
  simpa only [trace,diag,Matrix.mul_apply,mul_comm] using H

lemma trace_small_diagonal (P E : Interaction n) (u : Fin n→ℝ) :
    |trace (P*(Matrix.diagonal u*E))|≤SKGap.opNorm P*vectorNorm u*‖E‖ := by
  apply (trace_le_traceAbsolute P (Matrix.diagonal u*E)).trans
  have H := double_cauchy (fun i k=>|P k i| *|u i|) (fun i k=>|E i k|)
    (mul_nonneg (real_op_norm_nonneg P) (vectorNorm_nonneg u)) (norm_nonneg E)
    (by simpa only [mul_pow,vectorNorm_sq] using small_column_square P u)
    (by simpa only [sq_abs] using le_of_eq (SKGap.frobenius_sq E).symm)
  have HH := (le_abs_self (∑i,∑k,(|P k i| * |u i|)*|E i k|)).trans H
  simpa only [traceAbsolute,Matrix.diagonal_mul,abs_mul,mul_assoc] using HH

lemma trace_small_mean (P E : Interaction n) (U : VectorFields n) (x : Spin n) (hn : 0<n) :
    |trace (P*(siteMean U x • E))|≤SKGap.opNorm P*vectorNorm (U x)*‖E‖ := by
  have hscaled := scaled_frobenius_by_rows P (siteMean U x) (vectorNorm_nonneg _) (real_op_norm_nonneg P)
    (siteMean_square U x hn) (matrix_row_square_le P)
  rw [Matrix.mul_smul,←Matrix.smul_mul]
  exact (trace_frobenius _ E).trans ((mul_le_mul_of_nonneg_right hscaled (norm_nonneg E)).trans_eq (by ring))

lemma averageError_eq (a : Spin n→ℝ) (U : VectorFields n) (x : Spin n) :
    averageError a U x=Matrix.of (fun i k=>U x i*halfDiff k a x)-
      Matrix.of (fun i k=>2*spin x k*derivativeMatrix U x i k*halfDiff k a x) := by
  ext i k
  simp only [averageError,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Matrix.of_apply,derivativeMatrix]
  rw [halfDiff_mul]
  ring

lemma trace_column_scaled (P D : Interaction n) (t : Fin n→ℝ) (x : Spin n) :
    |trace (P*Matrix.of (fun i k=>2*spin x k*D i k*t k))|≤
      2*‖D‖*(SKGap.opNorm P*vectorNorm t) := by
  apply (trace_le_traceAbsolute P _).trans
  have H:=parameter_product_trace_bound P D t (norm_nonneg D) (vectorNorm_nonneg t)
    (le_of_eq (SKGap.frobenius_sq D).symm) (le_of_eq (vectorNorm_sq t).symm)
  have he : traceAbsolute P (Matrix.of (fun i k=>2*spin x k*D i k*t k))=
      2*(∑i,∑k,|P k i| *|D i k| *|t k|) := by
    simp only [traceAbsolute,Matrix.of_apply,abs_mul,abs_spin_eq_one,mul_one,
      abs_of_pos (by norm_num : (0:ℝ)<2),Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro k _; ring
  rw [he]
  exact (mul_le_mul_of_nonneg_left H (by norm_num)).trans_eq (by ring)

lemma averageError_trace (P : Interaction n) (a : Spin n→ℝ) (U : VectorFields n) (x : Spin n) :
    |trace (P*averageError a U x)|≤
      SKGap.opNorm P*(vectorNorm (U x)+2*‖derivativeMatrix U x‖)*‖derivativeVector a x‖ := by
  rw [averageError_eq,mul_sub,trace_sub]
  have h₁:=rank_one_trace_bound P (WithLp.toLp 2 (U x)) (derivativeVector a x)
  have h₂:=trace_column_scaled P (derivativeMatrix U x) (fun k=>halfDiff k a x) x
  apply ((abs_sub _ _).trans (add_le_add h₁ h₂)).trans_eq
  change SKGap.opNorm P*vectorNorm (U x)*‖derivativeVector a x‖+
    2*‖derivativeMatrix U x‖*(SKGap.opNorm P*‖derivativeVector a x‖)=_
  ring

lemma primary_averageError_trace (P : Interaction n) (U m : VectorFields n) (x : Spin n) (hn : 0<n)
    {C R : ℝ} (hC : 0≤C) (hR : 0≤R) (hU : ‖derivativeMatrix U x‖≤C)
    (hm : ∀i,|m x i|≤1) (hdm : SKGap.opNorm (derivativeMatrix m x)≤R) :
    |trace (P*averageError (siteMean U) m x)|≤SKGap.opNorm P*C*(1+2*R) := by
  have hd : (n:ℝ)*‖derivativeVector (siteMean U) x‖^2≤C^2 :=
    siteMean_derivative_square_bound hn ((opNorm_le_frobenius _).trans hU)
  have hm2 : vectorNorm (m x)^2≤(n:ℝ) := by
    rw [vectorNorm_sq]
    calc
      _ ≤ ∑_i:Fin n,(1:ℝ) := Finset.sum_le_sum fun i _=>by nlinarith [hm i,sq_abs (m x i),abs_nonneg (m x i)]
      _ = _ := by simp
  have hdm2 : ‖derivativeMatrix m x‖^2≤(n:ℝ)*R^2 := by
    rw [SKGap.frobenius_sq]
    calc
      _ ≤ ∑_i:Fin n,R^2 := Finset.sum_le_sum fun i _=>
        (matrix_row_square_le _ i).trans (pow_le_pow_left₀ (real_op_norm_nonneg _) hdm 2)
      _ = _ := by simp
  have h₁ : vectorNorm (m x)*‖derivativeVector (siteMean U) x‖≤C := by
    apply nonneg_le_nonneg_of_sq_le_sq hC
    simp only [←sq,mul_pow]
    exact (mul_le_mul_of_nonneg_right hm2 (sq_nonneg _)).trans hd
  have h₂ : ‖derivativeMatrix m x‖*‖derivativeVector (siteMean U) x‖≤C*R := by
    apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hC hR)
    simp only [←sq,mul_pow]
    have H := (mul_le_mul_of_nonneg_right hdm2 (sq_nonneg ‖derivativeVector (siteMean U) x‖)).trans
      (show (n:ℝ)*R^2*‖derivativeVector (siteMean U) x‖^2≤C^2*R^2 by
        nlinarith [mul_le_mul_of_nonneg_right hd (sq_nonneg R)])
    exact H
  apply (averageError_trace P (siteMean U) m x).trans
  have H := mul_le_mul_of_nonneg_left (add_le_add h₁ (mul_le_mul_of_nonneg_left h₂ (by norm_num : (0:ℝ)≤2)))
    (real_op_norm_nonneg P)
  nlinarith only [H]

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_PrimitiveTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix SKGap.SourceError
variable {n : ℕ}
local instance instFactLeENNRealOfNat_solutions : Fact (1≤(4:ENNReal)) := ⟨by norm_num⟩

lemma testSize_nonneg (P : Interaction n) : 0≤testSize P := add_nonneg (norm_nonneg _) (norm_nonneg _)
lemma opNorm_le_testSize (P : Interaction n) : SKGap.opNorm P≤testSize P := le_add_of_nonneg_right (norm_nonneg _)

lemma TraceControl.mono {E : Interaction n} {C D : ℝ} (h : TraceControl E C) (hCD : C≤D) : TraceControl E D :=
  ⟨h.nonneg.trans hCD,fun P=>(h.bound P).trans (mul_le_mul_of_nonneg_right hCD (testSize_nonneg P))⟩
lemma TraceControl.add {E F : Interaction n} {C D : ℝ} (hE : TraceControl E C) (hF : TraceControl F D) :
    TraceControl (E+F) (C+D) := by
  refine ⟨add_nonneg hE.nonneg hF.nonneg,?_⟩
  intro P; rw [mul_add,trace_add,add_mul]
  exact (abs_add_le _ _).trans (add_le_add (hE.bound P) (hF.bound P))
lemma TraceControl.smul {E : Interaction n} {C : ℝ} (hE : TraceControl E C) (a : ℝ) :
    TraceControl (a • E) (|a| *C) := by
  refine ⟨mul_nonneg (abs_nonneg _) hE.nonneg,?_⟩
  intro P; rw [Matrix.mul_smul,trace_smul,smul_eq_mul,abs_mul]
  exact (mul_le_mul_of_nonneg_left (hE.bound P) (abs_nonneg a)).trans_eq (by ring)
lemma TraceControl.neg {E : Interaction n} {C : ℝ} (hE : TraceControl E C) : TraceControl (-E) C := by
  simpa using hE.smul (-1)
lemma TraceControl.sub {E F : Interaction n} {C D : ℝ} (hE : TraceControl E C) (hF : TraceControl F D) :
    TraceControl (E-F) (C+D) := by simpa only [sub_eq_add_neg] using hE.add hF.neg
lemma TraceControl.sum {α : Type*} [Fintype α] {E : α→Interaction n} {C : α→ℝ}
    (h : ∀a,TraceControl (E a) (C a)) : TraceControl (∑a,E a) (∑a,C a) := by
  refine ⟨Finset.sum_nonneg (fun a _=>(h a).nonneg),?_⟩
  intro P; rw [Matrix.mul_sum,trace_sum,Finset.sum_mul]
  exact (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun a _=>(h a).bound P)

lemma control_of_operator {E : Interaction n} {C : ℝ} (hC : 0≤C)
    (h : ∀P,|trace (P*E)|≤C*SKGap.opNorm P) : TraceControl E C :=
  ⟨hC,fun P=>(h P).trans (mul_le_mul_of_nonneg_left (opNorm_le_testSize P) hC)⟩

lemma small_diagonal_control (E : Interaction n) (u : Fin n→ℝ) :
    TraceControl (Matrix.diagonal u*E) (vectorNorm u*‖E‖) := by
  apply control_of_operator (mul_nonneg (vectorNorm_nonneg _) (norm_nonneg _))
  intro P; exact (trace_small_diagonal P E u).trans_eq (by ring)
lemma small_mean_control (E : Interaction n) (U : VectorFields n) (x : Spin n) (hn : 0<n) :
    TraceControl (siteMean U x • E) (vectorNorm (U x)*‖E‖) := by
  apply control_of_operator (mul_nonneg (vectorNorm_nonneg _) (norm_nonneg _))
  intro P; exact (trace_small_mean P E U x hn).trans_eq (by ring)
lemma averageError_control (a : Spin n→ℝ) (U : VectorFields n) (x : Spin n) :
    TraceControl (averageError a U x) ((vectorNorm (U x)+2*‖derivativeMatrix U x‖)*‖derivativeVector a x‖) := by
  apply control_of_operator (by positivity [vectorNorm_nonneg (U x)])
  intro P; exact (averageError_trace P a U x).trans_eq (by ring)
lemma primary_averageError_control (U m : VectorFields n) (x : Spin n) (hn : 0<n)
    {C R : ℝ} (hC : 0≤C) (hR : 0≤R) (hU : ‖derivativeMatrix U x‖≤C)
    (hm : ∀i,|m x i|≤1) (hdm : SKGap.opNorm (derivativeMatrix m x)≤R) :
    TraceControl (averageError (siteMean U) m x) (C*(1+2*R)) := by
  apply control_of_operator (by positivity)
  intro P; exact (primary_averageError_trace P U m x hn hC hR hU hm hdm).trans_eq (by ring)

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
lemma sourceError_control (H : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ)
    (F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ)
    (s : VectorFields n) (x : Spin n) {C S T B R L : ℝ}
    (h : SegmentRegular H θ F F' x C) (hS : 0≤S) (hT : 0≤T) (hB : 0≤B) (hR : 0≤R) (hL : 0≤L)
    (hs : vectorNorm (s x)≤S) (hds : ‖derivativeMatrix s x‖≤S)
    (ht : vectorNorm (parameterIncrement θ x)≤T)
    (hQ4 : (∑i,∑k,(primaryIncrement H x i k)^4)≤B^4)
    (hQr : ∀i,(∑k,(primaryIncrement H x i k)^2)≤R^2)
    (hQd : (∑i,(primaryIncrement H x i i)^2)≤L^2) :
    TraceControl (sourceError H θ F F' s x)
      (C*S*((∑α,‖derivativeVector (θ α) x‖)+4*(B^2+R*T+T^2)+2*(B+L+T))) := by
  have hC := h.nonneg
  have hsum : 0≤∑α,‖derivativeVector (θ α) x‖ := Finset.sum_nonneg fun α _=>norm_nonneg _
  refine ⟨by positivity,?_⟩
  intro P
  have hO : 0≤SKGap.offDiagonalSeminorm P := norm_nonneg _
  have hP : (∑i,∑k,if i=k then 0 else (P k i)^4)≤SKGap.offDiagonalSeminorm P^4 := by
    rw [SKGap.offDiagonalSeminorm_fourth,Fintype.sum_prod_type,Finset.sum_comm]
    simp only [eq_comm]; rfl
  apply (sourceError_trace H θ F F' s x P h hS hT hB hR hL hO hs hds ht hQ4 hQr hQd hP).trans
  have h₁ : 0≤C*S*((∑α,‖derivativeVector (θ α) x‖)+4*(B^2+R*T+T^2)+2*(L+T)) := by positivity
  have h₂ : 0≤2*C*S*B := by positivity
  have H₁ := mul_nonneg (real_op_norm_nonneg P) h₂
  have H₂ := mul_nonneg hO h₁
  unfold testSize
  nlinarith only [H₁,H₂]

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

lemma logSlope_ratio (z r a : ℝ) :
    logSlope z r a=(RatioExpr.kernel phiExpr.dz).eval z r a := by
  rw [RatioExpr.eval,phiExpr_dz,logSlope]

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

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_RecipeIncrement
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

lemma parameterIncrement_bound (θ : κ→Spin n→ℝ) (x : Spin n) :
    vectorNorm (parameterIncrement θ x)≤∑α,‖derivativeVector (θ α) x‖ := by
  calc
    _ ≤ ∑α,vectorNorm (fun k=>|halfDiff k (θ α) x|) := by
      convert! vectorNorm_sum (fun α k=>|halfDiff k (θ α) x|) using 1
      all_goals try with_reducible_and_instances rfl
      congr 1; ext k; simp [parameterIncrement]
    _ = _ := by apply Finset.sum_congr rfl; intro α _; rw [vectorNorm_abs]; rfl

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
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary SKGap.ImplicitSystem Matrix
variable {n : ℕ}

lemma initialU_size (f : KernelExpr) (z : VectorFields n) (a : Spin n→ℝ)
    (r e : Fin n→ℝ) (x : Spin n) (he : vectorNorm e≤1) :
    vectorNorm (initialU f z a r e x)≤f.mass := by
  exact (vectorNorm_mul _ e f.mass_nonneg (fun i=>(RatioExpr.kernel f).bounded _ _ _)).trans
    (mul_le_of_le_one_right f.mass_nonneg he)

lemma initialP_size (f : KernelExpr) (z : VectorFields n) (a : Spin n→ℝ)
    (r e : Fin n→ℝ) (x : Spin n) {R : ℝ} (ha : |a x|≤R) (he : vectorNorm e≤1) :
    vectorNorm (initialP f z a r e x)≤
      Real.exp (R/2)*((RatioExpr.kernel f).d .z).mass := by
  rw [initialP_ratio]
  apply (vectorNorm_mul _ _ (Real.exp_pos _).le (fun i=>?_)).trans
    (mul_le_mul_of_nonneg_left ((vectorNorm_mul _ e (RatioExpr.mass_nonneg _)
      (fun i=>RatioExpr.bounded _ _ _ _)).trans
        (mul_le_of_le_one_right (RatioExpr.mass_nonneg _) he)) (Real.exp_pos _).le)
  rw [abs_of_pos (phi_pos _ _ _)]
  exact (phi_le_exp ..).trans (Real.exp_le_exp.mpr (by linarith))

lemma literal_initial_size (J : Interaction n) (j : ℝ) (f : KernelExpr)
    (z m w y : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (x : Spin n)
    (hn : 0<n) {R ρ δ L : ℝ} (hδ : 0<δ) (hρ : 0≤ρ)
    (hsmall : ρ≤δ/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1)))
    (hJ : SKGap.opNorm J≤L) (he : vectorNorm e≤1)
    (H : LiteralStableAt J j z m a r R ρ δ x)
    (h : LiteralEquations J j f z m w y a c r e x) :
    vectorNorm (w x)+vectorNorm (y x)+Real.sqrt n*|c x|≤literalSizeBudget j δ R L f := by
  have hnR : (0:ℝ)<n:=Nat.cast_pos.mpr hn
  have hd : 0<Real.sqrt (n:ℝ):=Real.sqrt_pos.mpr hnR
  have hL : 0≤L:=(norm_nonneg _).trans hJ
  have hscale : (n:ℝ)⁻¹*(Real.sqrt (n:ℝ))^2=1 := by
    rw [Real.sq_sqrt hnR.le,inv_mul_cancel₀ hnR.ne']
  have hχ : |siteMean (fun v i=>phi (z v i) (r i) (a v)) x|≤Real.exp (R/2) := by
    apply coefficient_mean_value _ _ (Real.exp_pos _).le
    intro i
    rw [abs_of_pos (phi_pos _ _ _)]
    exact (phi_le_exp ..).trans (Real.exp_le_exp.mpr (by linarith [H.a_bound]))
  have hP:=initialP_size f z a r e x H.a_bound he
  have hp:=scaledMean_size hn (initialP f z a r e) x
    (mul_nonneg (Real.exp_pos _).le (RatioExpr.mass_nonneg _)) hP
  rw [abs_mul,abs_of_nonneg hd.le] at hp
  have heq:=h
  unfold LiteralEquations at heq
  rw [←phiSqrt_square] at heq
  obtain ⟨hw,hc,hy⟩:=implicit_uniform_size j _ _ _ _ (phiSqrt (z x) r (a x))
    (toEuclideanCLM (𝕜:=ℝ) J) (WithLp.toLp 2 (initialU f z a r e x))
    (WithLp.toLp 2 (m x)) (WithLp.toLp 2 (fun i=>Real.tanh (r i)))
    (WithLp.toLp 2 (fun i=>logSlope (z x i) (r i) (a x)))
    (WithLp.toLp 2 (fun i=>Real.tanh (z x i))) (WithLp.toLp 2 (w x))
    (WithLp.toLp 2 (y x)) (c x) hδ hd (by positivity) hscale
    (Real.exp_pos _).le hL (by norm_num : (0:ℝ)≤2) f.mass_nonneg
    (mul_nonneg (Real.exp_pos _).le (RatioExpr.mass_nonneg _))
    (phiSqrt_bound _ _ _ H.a_bound) hJ hχ (initialU_size f z a r e x he)
    H.m_size (vectorNorm_tanh r) (vectorNorm_logSlope (z x) r (a x)) hp
    H.stable (H.perturbation hn hδ hρ hsmall) heq
  dsimp only [literalSizeBudget]
  change vectorNorm (w x)≤_ at hw
  change vectorNorm (y x)≤_ at hy
  linarith

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_LocalImplicitNode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Primary
variable {n : ℕ}
lemma derivativeMatrix_congr_on_flips (F G : VectorFields n) (x : Spin n)
    (hx : F x=G x) (hf : ∀i,F (flip x i)=G (flip x i)) :
    derivativeMatrix F x=derivativeMatrix G x := by
  ext i k
  simp only [derivativeMatrix,halfDiff_as_flip,hx,hf]
end SKGapCutoff.Primary

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LiteralPartial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary
variable {n : ℕ}
lemma SmallBound.of_local_eq {U V : VectorFields n} {x : Spin n} {C : ℝ}
    (h : SmallBound V x C) (hx : U x=V x) (hf : ∀k,U (flip x k)=V (flip x k)) :
    SmallBound U x C := by
  refine ⟨h.nonneg,?_,?_⟩
  · simpa only [hx] using h.size
  · rw [derivativeMatrix_congr_on_flips U V x hx hf]
    exact h.derivative

lemma literalInitial_partial_small (J : Interaction n) (j d : ℝ) (f : KernelExpr)
    (z m w y : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (x : Spin n)
    (hd : d≠0) {R T B : ℝ} (hT : 0≤T) (he : vectorNorm e≤1)
    (ha : |a x|≤R) (haf : ∀k,|a (flip x k)|≤R)
    (hD : SKGap.opNorm (derivativeMatrix z x)+‖derivativeVector a x‖≤T)
    (hW : SmallBound w x B)
    (hw : w x=(literalInitial J j d f z m a c r e).sourceOf 1 (fun _=>y) x)
    (hwf : ∀k,w (flip x k)=(literalInitial J j d f z m a c r e).sourceOf 1 (fun _=>y) (flip x k)) :
    SmallBound ((literalInitial J j d f z m a c r e).implicitPartial y) x
      (B*ratioSmallBudget (.kernel phiExpr.dz) T+
        ratioSmallBudget ((RatioExpr.kernel f).d .z) T*kernelSmallBudget phiExpr R T) := by
  have hel:=initial_ratio_bound (.kernel phiExpr.dz) z a r x hT hD
  have hs:=(hel.small_product hW).add (initialP_small f z a r e x hT he ha haf hD)
  have H : SmallBound (fun v i=>logSlope (z v i) (r i) (a v)*w v i+initialP f z a r e v i) x
      (B*ratioSmallBudget (.kernel phiExpr.dz) T+
        ratioSmallBudget ((RatioExpr.kernel f).d .z) T*kernelSmallBudget phiExpr R T) := by
    convert! hs using 1
    all_goals try with_reducible_and_instances rfl
    ext v i
    rw [logSlope_ratio]
  exact H.of_local_eq (literalInitial_partial_source _ _ _ _ _ _ _ _ _ _ _ _ hd x hw)
    (fun k=>literalInitial_partial_source _ _ _ _ _ _ _ _ _ _ _ _ hd _ (hwf k))
end SKGapCutoff.Recipe

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
-- module Solutions.OAIQ072_SK.SKGap_Stability_ImplicitTraceControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe.OrdinaryData
open Primary Matrix SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary
variable {n : ℕ} {κ σ : Type*} [Fintype κ] [DecidableEq κ] [Fintype σ]
variable (D : OrdinaryData n Unit κ σ)

lemma implicitSource_control (t : SourceTree (Fin n→ℝ)) (y : VectorFields n) (x : Spin n)
    {C Q R L V Z B Cp E : ℝ}
    (hC : 0≤C) (hQ : 0≤Q) (hR : 0≤R) (hL : 0≤L) (hV : 0≤V)
    (hY : SmallBound y x B) (hp : SmallBound (D.implicitPartial y) x Cp)
    (hE : ‖derivativeMatrix (D.H ()) x-t.fieldMatrix D.j D.J‖≤E)
    (hs : ∀s,SegmentRegular D.H D.θ (D.seedFunction 1 s) (D.seedDerivative 1 s) x C)
    (ha : SegmentRegular D.H D.θ (D.auxFunction 1 0) (D.auxDerivative 1 0) x C)
    (ht : vectorNorm (parameterIncrement D.θ x)≤V)
    (hQ4 : (∑i,∑k,(primaryIncrement D.H x i k)^4)≤Q^4)
    (hQr : ∀i,(∑k,(primaryIncrement D.H x i k)^2)≤R^2)
    (hQd : (∑i,(primaryIncrement D.H x i i)^2)≤L^2)
    (hZ : (∑α,‖derivativeVector (D.θ α) x‖)+4*(Q^2+R*V+V^2)+2*(Q+L+V)≤Z) :
    TraceControl (D.implicitSourcePrimitive t y x)
      (((∑s,C*vectorNorm (D.seed s)*Z)+C*B*Z)+Cp*E) := by
  have hc (s : VectorFields n) {S : ℝ} (hS : SmallBound s x S)
      (F : Fin n→Args (ι:=Unit) (κ:=κ)→ℝ)
      (F' : Fin n→Args (ι:=Unit) (κ:=κ)→Args (ι:=Unit) (κ:=κ)→L[ℝ]ℝ)
      (hF : SegmentRegular D.H D.θ F F' x C) : TraceControl (sourceError D.H D.θ F F' s x) (C*S*Z) :=
    (sourceError_control D.H D.θ F F' s x hF hS.nonneg hV hQ hR hL hS.size hS.derivative ht hQ4 hQr hQd).mono
      (mul_le_mul_of_nonneg_left hZ (mul_nonneg hC hS.nonneg))
  have hs' := TraceControl.sum (fun s=>hc (fun _=>D.seed s) (SmallBound.seed _ x) _ _ (hs s))
  have ha' := hc y hY _ _ ha
  have hp' := (small_diagonal_control
    (derivativeMatrix (D.H ()) x-t.fieldMatrix D.j D.J) (D.implicitPartial y x)).mono
      (mul_le_mul hp.size hE (norm_nonneg _) hp.nonneg)
  have H:=(hs'.add ha').add hp'
  simpa only [implicitSourcePrimitive,sourceAtoms,Fin.sum_univ_one] using H

lemma implicitField_control (t : SourceTree (Fin n→ℝ)) (w y : VectorFields n) (x : Spin n) (hn : 0<n)
    {P R B Cp E : ℝ} (hP : 0≤P) (hR : 0≤R)
    (hW : SmallBound w x B) (hp : SmallBound (D.implicitPartial y) x Cp)
    (hE : ‖derivativeMatrix (D.predecessor ()) x-t.sourceMatrix D.j D.J‖≤E)
    (hm : ∀i,|D.predecessor () x i|≤1)
    (hdm : SKGap.opNorm (derivativeMatrix (D.predecessor ()) x)≤P)
    (hda : ∀i,∑k,(derivativeMatrix D.implicitCoefficient x i k)^2≤R^2) :
    TraceControl (D.implicitFieldPrimitive t w y x)
      (|D.j| *(Cp*E)+|D.j| *(Cp*(1+2*P)+3*B*R)) := by
  have hmE : TraceControl
      ((D.j*siteMean (D.implicitPartial y) x) •
        (derivativeMatrix (D.predecessor ()) x-t.sourceMatrix D.j D.J)) (|D.j| *(Cp*E)) := by
    simpa only [smul_smul] using ((small_mean_control
      (derivativeMatrix (D.predecessor ()) x-t.sourceMatrix D.j D.J)
      (D.implicitPartial y) x hn).mono
        (mul_le_mul hp.size hE (norm_nonneg _) hp.nonneg)).smul D.j
  have hpE := primary_averageError_control (D.implicitPartial y) (D.predecessor ()) x hn
    hp.nonneg hP hp.derivative hm hdm
  have haE : TraceControl (averageError (siteMean D.implicitCoefficient) w x) (3*B*R) := by
    apply (averageError_control (siteMean D.implicitCoefficient) w x).mono
    have H:=coefficient_mean_difference D.implicitCoefficient x hR hda
    have h1 := add_le_add hW.size (mul_le_mul_of_nonneg_left hW.derivative (by norm_num : (0:ℝ)≤2))
    exact (mul_le_mul h1 H (norm_nonneg _) (by linarith [hW.nonneg])).trans_eq (by ring)
  simpa only [implicitFieldPrimitive,neg_smul] using hmE.neg.sub ((hpE.add haE).smul D.j)

end SKGapCutoff.Recipe.OrdinaryData

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_LiteralTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary
variable {n : ℕ}

lemma literalInitial_parameter (J : Interaction n) (j d : ℝ) (f : KernelExpr)
    (z m : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (x : Spin n) :
    (∑α,‖derivativeVector ((literalInitial J j d f z m a c r e).θ α) x‖)=
      ‖derivativeVector a x‖+‖derivativeVector (fun v=>d*c v) x‖ := by
  simp only [Fintype.sum_bool,literalInitial,Bool.false_eq_true,ite_false,ite_true]
  ring

lemma literalInitial_traces (J : Interaction n) (j : ℝ) (f : KernelExpr)
    (z m w y : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (x : Spin n)
    (t : SKGap.Noncrossing.Primary.SourceTree (Fin n→ℝ)) (hn : 0<n)
    {R T B Bs Q E : ℝ} (hT : 0≤T) (hQ : 0≤Q) (hBs : 0≤Bs)
    (he : vectorNorm e≤1) (ha : |a x|≤R) (haf : ∀k,|a (flip x k)|≤R)
    (hc : |Real.sqrt n*c x|≤Bs) (hcf : ∀k,|Real.sqrt n*c (flip x k)|≤Bs)
    (hD : SKGap.opNorm (derivativeMatrix z x)+‖derivativeVector a x‖≤T)
    (hDm : SKGap.opNorm (derivativeMatrix m x)≤T) (hm : ∀i,|m x i|≤1)
    (hW : SmallBound w x B) (hY : SmallBound y x B)
    (hDc : ‖derivativeVector (fun v=>Real.sqrt n*c v) x‖≤B)
    (hw : w x=(literalInitial J j (Real.sqrt n) f z m a c r e).sourceOf 1 (fun _=>y) x)
    (hwf : ∀k,w (flip x k)=(literalInitial J j (Real.sqrt n) f z m a c r e).sourceOf 1 (fun _=>y) (flip x k))
    (hEz : ‖derivativeMatrix z x-t.fieldMatrix j J‖≤E)
    (hEm : ‖derivativeMatrix m x-t.sourceMatrix j J‖≤E)
    (hQ4 : (∑i,∑k,(derivativeMatrix z x i k)^4)≤Q^4)
    (hdiag : (∑i,(derivativeMatrix z x i i)^2)≤T^2) :
    let D:=literalInitial J j (Real.sqrt n) f z m a c r e
    let C:=initialRegularBudget f j R Bs
    let Cp:=initialPartialBudget f R T B
    TraceControl (D.implicitSourcePrimitive t y x)
      ((2*C+C*B)*initialTraceFactor Q T B+Cp*E) ∧
    TraceControl (D.implicitFieldPrimitive t w y x)
      (|j| *(Cp*E)+|j| *(Cp*(1+2*T)+3*B*((phiExpr.dBudget R+phiExpr.ddBudget R)*T))) := by
  let D:=literalInitial J j (Real.sqrt n) f z m a c r e
  let C:=initialRegularBudget f j R Bs
  have hd : Real.sqrt (n:ℝ)≠0:=(Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  have hp:=literalInitial_partial_small J j (Real.sqrt n) f z m w y a c r e x hd hT he ha haf hD hW hw hwf
  obtain ⟨hreg,har⟩:=literalInitial_regular J j (Real.sqrt n) f z m a c r e x hBs ha haf hc hcf
  have hC : 0≤ initialRegularBudget f j R Bs:=(hreg false).nonneg
  have hparam : (∑α,‖derivativeVector (D.θ α) x‖)≤T+B := by
    rw [literalInitial_parameter]
    exact add_le_add (by linarith [show 0≤SKGap.opNorm (derivativeMatrix z x) from norm_nonneg _]) hDc
  have hrow (i : Fin n) : (∑k,(primaryIncrement D.H x i k)^2)≤T^2 := by
    simpa only [primaryIncrement,D,literalInitial,Fintype.sum_unique,sq_abs] using
      (SKGap.SourceError.matrix_row_square_le (derivativeMatrix z x) i).trans
        (pow_le_pow_left₀ (norm_nonneg _) (le_trans (le_add_of_nonneg_right (norm_nonneg _)) hD) 2)
  have h4 : (∑i,∑k,(primaryIncrement D.H x i k)^4)≤Q^4 := by
    simpa only [primaryIncrement,D,literalInitial,Fintype.sum_unique,show (4:ℕ)=2*2 from rfl,pow_mul,sq_abs] using hQ4
  have hdi : (∑i,(primaryIncrement D.H x i i)^2)≤T^2 := by
    simpa only [primaryIncrement,D,literalInitial,Fintype.sum_unique,sq_abs] using hdiag
  have hseed (s : Bool) : vectorNorm (D.seed s)≤1 := by
    cases s
    · exact he
    · change vectorNorm (fun i=>Real.tanh (r i)/Real.sqrt n)≤1
      have H:=(vectorNorm_tanh r)
      rw [show (fun i=>Real.tanh (r i)/Real.sqrt n)=((Real.sqrt n)⁻¹ • (fun i=>Real.tanh (r i))) by ext i; simp only [Pi.smul_apply,smul_eq_mul];ring,
        vectorNorm_smul,abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
      exact (mul_le_mul_of_nonneg_left H (inv_nonneg.mpr (Real.sqrt_nonneg _))).trans_eq (inv_mul_cancel₀ hd)
  have hZ : (∑α,‖derivativeVector (D.θ α) x‖)+4*(Q^2+T*(T+B)+(T+B)^2)+2*(Q+T+(T+B))≤ initialTraceFactor Q T B := by
    dsimp only [initialTraceFactor]; linarith
  have Hs:=D.implicitSource_control t y x hC hQ hT hT (add_nonneg hT hW.nonneg) hY hp hEz hreg har
    ((parameterIncrement_bound D.θ x).trans hparam) h4 hrow hdi
    hZ
  have Hb : (∑s,C*vectorNorm (D.seed s))≤2*C := by
    simpa only [Fintype.sum_bool,mul_one,two_mul] using add_le_add
      (mul_le_mul_of_nonneg_left (hseed true) hC) (mul_le_mul_of_nonneg_left (hseed false) hC)
  have hcoef:=initial_kernel_bound phiExpr z a r x hT ha haf hD
  have hcoef' : D.implicitCoefficient=fun v i=>phiExpr.eval (z v i) (r i) (a v) := by
    ext v i; rw [literalInitial_coefficient,phiExpr,KernelExpr.eval,moment_base]
  constructor
  · apply Hs.mono
    dsimp only [initialPartialBudget,initialTraceFactor] at *
    rw [←Finset.sum_mul]
    nlinarith [mul_nonneg (sub_nonneg.mpr Hb)
      (show 0≤T+B+4*(Q^2+T*(T+B)+(T+B)^2)+2*(Q+T+(T+B)) by positivity [hW.nonneg])]
  · apply D.implicitField_control t w y x hn hT hcoef.row_nonneg hW hp hEm hm hDm
    simpa only [hcoef'] using hcoef.difference
end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGap.ImplicitSystem
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma ordinary_matrix_margin (j χ b r δ : ℝ) (X J : E→L[ℝ]E) (q : E)
    (hj : 0≤j) (hr : 0 ≤ r)
    (hself : ∀u v,inner ℝ u (X v)=inner ℝ (X u) v)
    (hStable : ∀v,δ*‖v‖^2≤ inner ℝ v (stableMatrix j b r X J q v))
    (hSmall : |j| *|χ-b| *‖X‖^2≤δ/2) (v : E) :
    (δ/2)*‖v‖^2≤ inner ℝ v ((1-X*(J-(j*χ) • 1)*X) v) := by
  let S:=1+(j*b) • (X*X)-X*J*X
  have hS : ∀u,δ*‖u‖^2≤ inner ℝ u (S u) := by
    intro u
    have hh : inner ℝ u ((X*rank q q*X) u)=(inner ℝ q (X u))^2 := by
      simp only [mul_apply_eq_comp,rank_apply,map_smul,inner_smul_right]
      rw [hself u q,real_inner_comm (X u) q]
      ring
    have hs:=hStable u
    change δ*‖u‖^2≤ inner ℝ u ((S-(2*j*r) • (X*rank q q*X)) u) at hs
    simp only [sub_apply,smul_apply,inner_sub_right,
      inner_smul_right,hh] at hs
    nlinarith [mul_nonneg (by positivity : 0≤2*j*r) (sq_nonneg (inner ℝ q (X u)))]
  have hd : (1-X*(J-(j*χ) • 1)*X)-S=(j*(χ-b)) • (X*X) := by
    dsimp only [S]
    simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,mul_one,sub_smul]
    module
  have hnorm : ‖(1-X*(J-(j*χ) • 1)*X)-S‖≤δ/2 := by
    rw [hd,norm_smul,Real.norm_eq_abs,abs_mul]
    exact ((mul_le_mul_of_nonneg_left (norm_mul_le X X) (by positivity)).trans_eq
      (by ring)).trans hSmall
  have hp:=SKGap.ImplicitLinear.quadratic_perturbation (1-X*(J-(j*χ) • 1)*X) S hS hnorm v
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  ring
end SKGap.ImplicitSystem

namespace SKGapCutoff.Recipe
open SKGap.Stein Primary SKGap.ImplicitSystem Matrix
variable {n : ℕ}
lemma phiSqrt_inner (z r : Fin n→ℝ) (a : ℝ) (u v : Euclid n) :
    inner ℝ u (phiSqrt z r a v)=inner ℝ (phiSqrt z r a u) v := by
  simp only [phiSqrt,EuclideanSpace.inner_eq_star_dotProduct,
    star_trivial,ofLp_toEuclideanCLM,dotProduct,mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma literal_inverse_stability (J : Interaction n) (j : ℝ)
    (z m : VectorFields n) (a : Spin n→ℝ) (r : Fin n→ℝ) (x : Spin n)
    (hn : 0<n) (hj : 0≤j) (hJ : J.IsSymm) {R ρ δ : ℝ} (hδ : 0<δ) (hρ : 0≤ρ)
    (hsmall : ρ≤δ/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1)))
    (H : LiteralStableAt J j z m a r R ρ δ x) :
    (1-SKGap.pathDiagonal (fun i=>phi (z x i) (r i) (a x)) 1*
      (J-(j*siteMean (fun v i=>phi (z v i) (r i) (a v)) x) • 1)*
      SKGap.pathDiagonal (fun i=>phi (z x i) (r i) (a x)) 1).PosDef := by
  let D:=SKGap.pathDiagonal (fun i=>phi (z x i) (r i) (a x)) 1
  let χ:=siteMean (fun v i=>phi (z v i) (r i) (a v)) x
  have hD : D.IsHermitian := by simp [D,SKGap.pathDiagonal]
  have hM : (J-(j*χ) • 1).IsHermitian :=
    (isHermitian_iff_isSymm.mpr hJ).sub (isHermitian_one.smul (IsSelfAdjoint.all (j*χ)))
  have hHerm : (1-D*(J-(j*χ) • 1)*D).IsHermitian := by
    apply isHermitian_one.sub
    simpa only [hD.eq] using isHermitian_conjTranspose_mul_mul D hM
  apply PosDef.of_dotProduct_mulVec_pos hHerm
  intro v hv
  have hpert:=H.perturbation hn hδ hρ hsmall
  have hsmall' : |j| *|χ-(∑i,scalarVariance (z x i))/(n:ℝ)| *‖phiSqrt (z x) r (a x)‖^2≤δ/2 :=
    (le_add_of_nonneg_right (by positivity)).trans hpert
  have hp:=ordinary_matrix_margin j χ _ (n:ℝ)⁻¹ δ (phiSqrt (z x) r (a x))
    (toEuclideanCLM (𝕜:=ℝ) J) (WithLp.toLp 2 (fun i=>Real.tanh (z x i)))
    hj (by positivity) (phiSqrt_inner _ _ _) H.stable hsmall' (WithLp.toLp 2 v)
  have hrep : toEuclideanCLM (𝕜:=ℝ) (1-D*(J-(j*χ) • 1)*D)=
      1-phiSqrt (z x) r (a x)*(toEuclideanCLM (𝕜:=ℝ) J-(j*χ) • 1)*phiSqrt (z x) r (a x) := by
    simp only [map_sub,map_mul,map_one,map_smul,D,SKGap.pathDiagonal,Real.sqrt_one,one_mul,phiSqrt]
  rw [←hrep,inner_toEuclideanCLM] at hp
  have hnorm : 0<‖(WithLp.toLp 2 v : Euclid n)‖^2 := by
    exact sq_pos_of_pos (norm_pos_iff.mpr (by simpa using hv))
  simpa only [star_trivial] using lt_of_lt_of_le (mul_pos (half_pos hδ) hnorm) hp
end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LiteralLocalWeak
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary
variable {n : ℕ}

theorem literal_complete_diagnostics_oai (j R ρ δ T L Q E : ℝ) (f : KernelExpr)
    (hj : 0≤j) (hδ : 0<δ) (hρ : 0≤ρ) (hT : 0≤T) (hQ : 0≤Q)
    (hsmall : ρ≤δ/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1))) :
    ∃B≥0,∃S≥0,∃F≥0,∃Bc≥0,∃Vc≥0,∀n : ℕ,0<n→∀(J : Interaction n) (z m : VectorFields n)
      (a : Spin n→ℝ) (r e : Fin n→ℝ),J.IsSymm→SKGap.opNorm J≤L→vectorNorm e≤1→
      ∃w y : VectorFields n,∃c : Spin n→ℝ,
        (∀x,LiteralStableAt J j z m a r R ρ δ x→LiteralEquations J j f z m w y a c r e x) ∧
        (∀x,LiteralStableAt J j z m a r R ρ δ x→|Real.sqrt n*c x|≤Bc) ∧
        (∀x,LiteralStableAt J j z m a r R ρ δ x→
          (∀k,LiteralStableAt J j z m a r R ρ δ (flip x k))→
          SKGap.opNorm (derivativeMatrix z x)+‖derivativeVector a x‖≤T→
          SKGap.opNorm (derivativeMatrix m x)≤T→
          ‖derivativeVector (fun v=>Real.sqrt n*c v) x‖≤Vc) ∧
        (∀x (t : SKGap.Noncrossing.Primary.SourceTree (Fin n→ℝ)),
          LiteralStableAt J j z m a r R ρ δ x→
          (∀k,LiteralStableAt J j z m a r R ρ δ (flip x k))→
          SKGap.opNorm (derivativeMatrix z x)+‖derivativeVector a x‖≤T→
          SKGap.opNorm (derivativeMatrix m x)≤T→(∀i,|m x i|≤1)→
          ‖derivativeMatrix z x-t.fieldMatrix j J‖≤E→
          ‖derivativeMatrix m x-t.sourceMatrix j J‖≤E→
          (∑i,∑k,(derivativeMatrix z x i k)^4)≤Q^4→
          (∑i,(derivativeMatrix z x i i)^2)≤T^2→
          LiteralInitialDiagnostics (literalInitial J j (Real.sqrt n) f z m a c r e)
            w y t x B S F (Real.exp (R/2))) := by
  obtain ⟨C,hC,hsol⟩:=literal_implicit_construction j R ρ δ T L f hδ hρ hT hsmall
  let Cp:=initialPartialBudget f R T C
  have hCp : 0≤Cp := by
    dsimp only [Cp,initialPartialBudget]
    exact add_nonneg (mul_nonneg hC (ratioSmallBudget_nonneg _ _ hT))
      (mul_nonneg (ratioSmallBudget_nonneg _ _ hT) (kernelSmallBudget_nonneg _ _ _ hT))
  let Bs:=|literalSizeBudget j δ R L f|
  let Cr:=initialRegularBudget f j R Bs
  let S:=(2*Cr+Cr*C)*initialTraceFactor Q T C+Cp*E
  let F:=|j| *(Cp*E)+|j| *(Cp*(1+2*T)+3*C*((phiExpr.dBudget R+phiExpr.ddBudget R)*T))
  refine ⟨C+Cp,add_nonneg hC hCp,|S|,abs_nonneg _,|F|,abs_nonneg _,Bs,abs_nonneg _,C,hC,?_⟩
  intro n hn J z m a r e hJ hJL he
  obtain ⟨w,y,c,heq,hb⟩:=hsol n hn J z m a r e hJL he
  have hcs {v : Spin n} (HV : LiteralStableAt J j z m a r R ρ δ v) :
      |Real.sqrt n*c v|≤Bs := by
    have hh:=literal_initial_size J j f z m w y a c r e v hn hδ hρ hsmall hJL he HV (heq v HV)
    rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
    dsimp only [Bs]
    exact le_trans (by linarith [vectorNorm_nonneg (w v),vectorNorm_nonneg (y v)]) (le_abs_self _)
  refine ⟨w,y,c,heq,fun x H=>hcs H,fun x H Hf hD hDm=>(hb x H Hf hD hDm).2.2.2,?_⟩
  intro x t H Hf hD hDm hm hEz hEm hQ4 hdi
  have hd : Real.sqrt (n:ℝ)≠0:=(Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  have heqr {v : Spin n} (HV : LiteralStableAt J j z m a r R ρ δ v) :=
    (literalEquations_recipe J j (Real.sqrt n) f z m w y a c r e hd v).mp (heq v HV)
  have hsize {v : Spin n} (HV : LiteralStableAt J j z m a r R ρ δ v) :
      |Real.sqrt n*c v|≤Bs := by
    have hh:=literal_initial_size J j f z m w y a c r e v hn hδ hρ hsmall hJL he HV (heq v HV)
    rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
    dsimp only [Bs]
    exact le_trans (by linarith [vectorNorm_nonneg (w v),vectorNorm_nonneg (y v)]) (le_abs_self _)
  obtain ⟨hw,hy,hc,hDc⟩:=hb x H Hf hD hDm
  have hp:=literalInitial_partial_small J j (Real.sqrt n) f z m w y a c r e x hd hT he
    H.a_bound (fun k=>(Hf k).a_bound) hD hw (heqr H).1 (fun k=>(heqr (Hf k)).1)
  obtain ⟨hS,hF⟩:=literalInitial_traces J j f z m w y a c r e x t hn hT hQ
    (abs_nonneg _) he H.a_bound (fun k=>(Hf k).a_bound) (hsize H) (fun k=>hsize (Hf k))
    hD hDm hm hw hy hDc (heqr H).1 (fun k=>(heqr (Hf k)).1) hEz hEm hQ4 hdi
  refine ⟨(heqr H).1,(fun k=>(heqr (Hf k)).1),(heqr H).2.1,
    (fun k=>(heqr (Hf k)).2.1),?_,?_,?_,hw.mono (le_add_of_nonneg_right hCp),
      hy.mono (le_add_of_nonneg_right hCp),hp.mono (le_add_of_nonneg_left hC),
      hS.mono (le_abs_self _),hF.mono (le_abs_self _)⟩
  · intro i
    rw [literalInitial_coefficient]
    exact (phi_pos ..).le
  · intro i
    rw [literalInitial_coefficient,abs_of_pos (phi_pos ..)]
    exact (phi_le_exp ..).trans (Real.exp_le_exp.mpr (by linarith [H.a_bound]))
  · have hcoef : (literalInitial J j (Real.sqrt n) f z m a c r e).implicitCoefficient=
        fun v i=>phi (z v i) (r i) (a v) := by
      ext v i
      exact literalInitial_coefficient ..
    rw [hcoef]
    exact literal_inverse_stability J j z m a r x hn hj hJ hδ hρ hsmall H
end SKGapCutoff.Recipe

end
end

end OAI
end

theorem solution : type_of% @OAI.SKGapCutoff.Recipe.literal_complete_diagnostics_oai := @OAI.SKGapCutoff.Recipe.literal_complete_diagnostics_oai
