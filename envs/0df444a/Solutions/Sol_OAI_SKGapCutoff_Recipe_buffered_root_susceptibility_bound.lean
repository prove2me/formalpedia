-- Prove2me | solution 1 for OAI.SKGapCutoff.Recipe.buffered_root_susceptibility_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:01:41.114761+00:00
-- url     : https://prove2.me/submissions/d518a91e-495c-4047-8062-628a39d8eac0

import Mathlib
import Definitions.Def_OAIQ072A002
import Theorems.Thm_OAI_SKGapCutoff_Recipe_buffered_root_source_weak

section
-- module Solutions.OAIQ072_SK.Compat
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

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

end RatioExpr
end SKGap.Stein

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_StableFields
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Real Matrix
namespace SKGap

theorem overlap_nonneg {n : ℕ} (y : Field n) : 0 ≤ overlap y :=
  div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg _)

theorem overlap_lt_one {n : ℕ} (hn : 0 < n) (y : Field n) : overlap y < 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  apply (div_lt_iff₀ hn').mpr
  simp only [one_mul]
  calc
    (∑ i, magnetization y i ^ 2) < ∑ _ : Fin n, (1 : ℝ) := by
      apply Finset.sum_lt_sum_of_nonempty
      · exact Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
      · intro i _
        exact tanh_sq_lt_one (y i)
    _ = n := by simp

theorem spinVariance_pos {n : ℕ} (y : Field n) (i : Fin n) :
    0 < spinVariance y i := sub_pos.mpr (tanh_sq_lt_one _)

theorem spinVariance_le_one {n : ℕ} (y : Field n) (i : Fin n) :
    spinVariance y i ≤ 1 := sub_le_self _ (sq_nonneg _)

theorem magnetization_hasFDerivAt {n : ℕ} (y : Field n) (i : Fin n) :
    HasFDerivAt (fun z : Field n => magnetization z i)
      (spinVariance y i • (ContinuousLinearMap.proj i : Field n →L[ℝ] ℝ)) y :=
  (hasDerivAt_tanh (y i)).comp_hasFDerivAt y (hasFDerivAt_apply i y)

theorem overlap_hasFDerivAt {n : ℕ} (y : Field n) :
    HasFDerivAt overlap (overlapDerivative y) y := by
  have hd := (HasFDerivAt.sum (u := Finset.univ)
    (fun k _ => (magnetization_hasFDerivAt y k).pow 2)).const_mul (n : ℝ)⁻¹
  convert! hd using 1
  · ext z
    simp only [overlap, Finset.sum_apply, div_eq_mul_inv]
    ring
  · ext v
    simp only [overlapDerivative, _root_.smul_apply,
      _root_.sum_apply, ContinuousLinearMap.proj_apply,
      smul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
      nsmul_eq_mul]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    ring

theorem onsager_hasFDerivAt {n : ℕ} (j : ℝ) (y : Field n) :
    HasFDerivAt (onsager j) (-j • overlapDerivative y) y := by
  convert! ((overlap_hasFDerivAt y).const_sub 1).const_mul j using 1
  all_goals try with_reducible_and_instances rfl
  ext v
  simp only [_root_.smul_apply, smul_eq_mul, _root_.neg_apply]
  ring

theorem tapField_hasFDerivAt {n : ℕ} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (h y : Field n) :
    HasFDerivAt (tapField j J h)
      ((fieldJacobian j J y).mulVecLin.toContinuousLinearMap) y := by
  rw [hasFDerivAt_pi']
  intro i
  have hfirst := ((hasFDerivAt_apply i y).sub_const (h i)).add
    ((onsager_hasFDerivAt j y).mul (magnetization_hasFDerivAt y i))
  have hlast := HasFDerivAt.sum (u := Finset.univ)
    (fun k _ => (magnetization_hasFDerivAt y k).const_mul (J i k))
  convert! hfirst.sub hlast using 1
  · ext z
    simp only [tapField, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Finset.sum_apply]
  · ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      LinearMap.coe_toContinuousLinearMap', Matrix.mulVecLin_apply, Matrix.mulVec,
      dotProduct, fieldJacobian, hessianCore, _root_.sub_apply,
      _root_.add_apply, _root_.smul_apply,
      _root_.sum_apply, smul_eq_mul, overlapDerivative]
    have hdelta : (∑ k : Fin n, (if i = k then 1 else (0 : ℝ)) * v k) = v i := by
      simp
    have hdeltaV : (∑ k : Fin n, (if i = k then 1 else (0 : ℝ)) *
        spinVariance y k * v k) = spinVariance y i * v i := by simp
    calc
      _ = (∑ k : Fin n, (if i = k then 1 else (0 : ℝ)) * v k) +
          onsager j y * (∑ k : Fin n, (if i = k then 1 else (0 : ℝ)) *
            spinVariance y k * v k) -
          (∑ k, J i k * (spinVariance y k * v k)) -
          (2 * j / n) * magnetization y i *
            (∑ k, (magnetization y k * spinVariance y k) * v k) := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := by
        rw [hdelta, hdeltaV]
        ring

theorem fieldHessian_variance_intertwine {n : ℕ} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (y : Field n) (i k : Fin n) :
    fieldHessian j J y (spinVariance y) i k * sqrt (spinVariance y k) =
      sqrt (spinVariance y i) * fieldJacobian j J y i k := by
  have hk := sq_sqrt (spinVariance_pos y k).le
  by_cases hik : i = k
  · subst k
    simp only [fieldHessian, fieldJacobian, ↓reduceIte]
    nlinarith only [congrArg (fun z => sqrt (spinVariance y i) * hessianCore j J y i i * z) hk]
  · simp only [fieldHessian, fieldJacobian, ite_eq_right hik, zero_add]
    nlinarith only [congrArg (fun z => sqrt (spinVariance y i) * hessianCore j J y i k * z) hk]

theorem fieldHessian_variance_mulVec {n : ℕ} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (y v : Field n) :
    (fieldHessian j J y (spinVariance y)).mulVec
      (fun k => sqrt (spinVariance y k) * v k) =
    fun i => sqrt (spinVariance y i) * (fieldJacobian j J y).mulVec v i := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← mul_assoc, fieldHessian_variance_intertwine]
  ring

theorem quadraticForm_eq_dot_mulVec {n : ℕ}
    (J : Matrix (Fin n) (Fin n) ℝ) (x : Field n) :
    quadraticForm J x = ∑ i, x i * J.mulVec x i := by
  simp only [quadraticForm, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem vectorNorm_nonneg {n : ℕ} (x : Field n) : 0 ≤ vectorNorm x := norm_nonneg _

theorem vectorNorm_sq {n : ℕ} (x : Field n) : vectorNorm x ^ 2 = vectorSqNorm x := by
  exact EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 x)

theorem vectorNorm_add_le {n : ℕ} (x z : Field n) :
    vectorNorm (x + z) ≤ vectorNorm x + vectorNorm z := by
  exact norm_add_le (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 z)

theorem vectorNorm_sub_le {n : ℕ} (x z : Field n) :
    vectorNorm (x - z) ≤ vectorNorm x + vectorNorm z := by
  exact norm_sub_le (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 z)

theorem vectorNorm_smul {n : ℕ} (a : ℝ) (x : Field n) :
    vectorNorm (fun i => a * x i) = |a| * vectorNorm x := by
  exact norm_smul a (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))

theorem vector_dot_abs_le {n : ℕ} (x z : Field n) :
    |∑ i, x i * z i| ≤ vectorNorm x * vectorNorm z := by
  simpa only [vectorNorm, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    PiLp.toLp_apply, mul_comm] using
    abs_real_inner_le_norm (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 z)

theorem vectorNorm_diag_le {n : ℕ} {a : Field n} {M : ℝ} (hM : 0 ≤ M)
    (ha : ∀ i, |a i| ≤ M) (x : Field n) :
    vectorNorm (fun i => a i * x i) ≤ M * vectorNorm x := by
  apply (sq_le_sq₀ (vectorNorm_nonneg _) (mul_nonneg hM (vectorNorm_nonneg _))).mp
  rw [mul_pow, vectorNorm_sq, vectorNorm_sq]
  unfold vectorSqNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [mul_pow]
  have hi : a i ^ 2 ≤ M ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (a i)) hM).mpr (ha i)
  exact mul_le_mul_of_nonneg_right hi (sq_nonneg (x i))

theorem sqrtVarianceMul_norm_le {n : ℕ} (y v : Field n) :
    vectorNorm (sqrtVarianceMul y v) ≤ vectorNorm v := by
  change vectorNorm (fun i => sqrt (spinVariance y i) * v i) ≤ vectorNorm v
  calc
    _ ≤ 1 * vectorNorm v := vectorNorm_diag_le zero_le_one (fun i => by
      rw [abs_of_nonneg (sqrt_nonneg _)]
      exact sqrt_le_one.mpr (spinVariance_le_one y i)) v
    _ = _ := one_mul _

theorem sqrtVarianceMul_twice {n : ℕ} (y v : Field n) :
    sqrtVarianceMul y (sqrtVarianceMul y v) = fun i => spinVariance y i * v i := by
  ext i
  dsimp [sqrtVarianceMul]
  rw [← mul_assoc, mul_self_sqrt (spinVariance_pos y i).le]

theorem weighted_inverse_bound {n : ℕ} {c j : ℝ} (_hc : 0 < c)
    (J : Matrix (Fin n) (Fin n) ℝ) (y v : Field n)
    (hH : ∀ x : Field n, c * vectorSqNorm x ≤
      quadraticForm (fieldHessian j J y (spinVariance y)) x) :
    c * vectorNorm (sqrtVarianceMul y v) ≤
      vectorNorm ((fieldJacobian j J y).mulVec v) := by
  let w := sqrtVarianceMul y v
  let z := (fieldJacobian j J y).mulVec v
  have hi : (fieldHessian j J y (spinVariance y)).mulVec w = sqrtVarianceMul y z :=
    fieldHessian_variance_mulVec j J y v
  have hq := hH w
  rw [quadraticForm_eq_dot_mulVec, hi] at hq
  have hdot := (le_abs_self (∑ i, w i * sqrtVarianceMul y z i)).trans
    (vector_dot_abs_le w (sqrtVarianceMul y z))
  have hz := mul_le_mul_of_nonneg_left (sqrtVarianceMul_norm_le y z) (vectorNorm_nonneg w)
  rw [← vectorNorm_sq] at hq
  change c * vectorNorm w ≤ vectorNorm z
  by_cases hw : vectorNorm w = 0
  · rw [hw, mul_zero]
    exact vectorNorm_nonneg z
  · have hw' : 0 < vectorNorm w := lt_of_le_of_ne (vectorNorm_nonneg w) (Ne.symm hw)
    nlinarith [hq.trans (hdot.trans hz)]

theorem hessianCore_mulVec {n : ℕ} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (y v : Field n) :
    (hessianCore j J y).mulVec v =
      (fun i => onsager j y * v i) - J.mulVec v -
      (fun i => ((2 * j / n) * (∑ k, magnetization y k * v k)) * magnetization y i) := by
  ext i
  change (∑ k, hessianCore j J y i k * v k) =
    onsager j y * v i - (∑ k, J i k * v k) -
      ((2 * j / n) * (∑ k, magnetization y k * v k)) * magnetization y i
  calc
    _ = ∑ k, (onsager j y * ((if i = k then 1 else 0) * v k) - J i k * v k -
        ((2 * j / n) * magnetization y i) * (magnetization y k * v k)) := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [hessianCore]
      ring
    _ = _ := by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp
      ring

attribute [local irreducible] vectorNorm

theorem hessianCore_norm_le {n : ℕ} (hn : 0 < n) {j K : ℝ} (hj : 0 ≤ j)
    (J : Matrix (Fin n) (Fin n) ℝ) (y v : Field n)
    (hJ : ∀ z : Field n, vectorNorm (J.mulVec z) ≤ K * vectorNorm z) :
    vectorNorm ((hessianCore j J y).mulVec v) ≤ (K + 3 * j) * vectorNorm v := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hq0 := overlap_nonneg y
  have hq1 := (overlap_lt_one hn y).le
  have hB0 : 0 ≤ onsager j y := mul_nonneg hj (sub_nonneg.mpr hq1)
  have hB : onsager j y ≤ j := by
    dsimp [onsager]
    nlinarith
  have hfirst : vectorNorm (fun i => onsager j y * v i) ≤ j * vectorNorm v := by
    rw [vectorNorm_smul, abs_of_nonneg hB0]
    exact mul_le_mul_of_nonneg_right hB (vectorNorm_nonneg v)
  have hm : vectorNorm (magnetization y) ^ 2 = (n : ℝ) * overlap y := by
    rw [vectorNorm_sq]
    dsimp [vectorSqNorm, overlap]
    field_simp
  have hm_bound : vectorNorm (magnetization y) ^ 2 ≤ n := by nlinarith
  have hs : 0 ≤ 2 * j / (n : ℝ) := by positivity
  have hcs := vector_dot_abs_le (magnetization y) v
  have hrank : vectorNorm (fun i => ((2 * j / n) *
      (∑ k, magnetization y k * v k)) * magnetization y i) ≤ 2 * j * vectorNorm v := by
    rw [vectorNorm_smul, abs_mul, abs_of_nonneg hs]
    calc
      _ ≤ ((2 * j / n) * (vectorNorm (magnetization y) * vectorNorm v)) *
          vectorNorm (magnetization y) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcs hs)
          (vectorNorm_nonneg _)
      _ = (2 * j / n) * vectorNorm (magnetization y) ^ 2 * vectorNorm v := by ring
      _ ≤ (2 * j / n) * n * vectorNorm v :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm_bound hs)
          (vectorNorm_nonneg _)
      _ = _ := by field_simp
  rw [hessianCore_mulVec]
  calc
    _ ≤ vectorNorm ((fun i => onsager j y * v i) - J.mulVec v) +
        vectorNorm (fun i => ((2 * j / n) * (∑ k, magnetization y k * v k)) *
          magnetization y i) := vectorNorm_sub_le _ _
    _ ≤ (vectorNorm (fun i => onsager j y * v i) + vectorNorm (J.mulVec v)) +
        vectorNorm (fun i => ((2 * j / n) * (∑ k, magnetization y k * v k)) *
          magnetization y i) := add_le_add (vectorNorm_sub_le _ _) le_rfl
    _ ≤ (j * vectorNorm v + K * vectorNorm v) + 2 * j * vectorNorm v :=
      add_le_add (add_le_add hfirst (hJ v)) hrank
    _ = _ := by ring

theorem fieldJacobian_mulVec {n : ℕ} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (y v : Field n) :
    (fieldJacobian j J y).mulVec v = v +
      (hessianCore j J y).mulVec (fun i => spinVariance y i * v i) := by
  ext i
  simp only [Matrix.mulVec, dotProduct, fieldJacobian, add_mul,
    Finset.sum_add_distrib, Pi.add_apply, mul_assoc]
  simp

theorem fieldJacobian_inverse_bound {n : ℕ} (hn : 0 < n) {c j K : ℝ}
    (hc : 0 < c) (hj : 0 ≤ j) (hK : 0 ≤ K)
    (J : Matrix (Fin n) (Fin n) ℝ) (y v : Field n)
    (hJ : ∀ z : Field n, vectorNorm (J.mulVec z) ≤ K * vectorNorm z)
    (hH : ∀ x : Field n, c * vectorSqNorm x ≤
      quadraticForm (fieldHessian j J y (spinVariance y)) x) :
    vectorNorm v ≤ (1 + (K + 3 * j) / c) *
      vectorNorm ((fieldJacobian j J y).mulVec v) := by
  let z := (fieldJacobian j J y).mulVec v
  let w : Field n := fun i => spinVariance y i * v i
  have hw : vectorNorm w ≤ vectorNorm (sqrtVarianceMul y v) := by
    simpa only [sqrtVarianceMul_twice] using sqrtVarianceMul_norm_le y (sqrtVarianceMul y v)
  have hcv : c * vectorNorm w ≤ vectorNorm z :=
    (mul_le_mul_of_nonneg_left hw hc.le).trans (weighted_inverse_bound hc J y v hH)
  have hv : vectorNorm w ≤ vectorNorm z / c := (le_div_iff₀ hc).mpr (by
    simpa only [mul_comm] using hcv)
  have he : v = z - (hessianCore j J y).mulVec w := by
    have hid := fieldJacobian_mulVec j J y v
    change z = v + (hessianCore j J y).mulVec w at hid
    rw [hid, add_sub_cancel_right]
  have hL := hessianCore_norm_le hn hj J y w hJ
  have hD : 0 ≤ K + 3 * j := by positivity
  calc
    vectorNorm v ≤ vectorNorm z + vectorNorm ((hessianCore j J y).mulVec w) := by
      conv_lhs => rw [he]
      exact vectorNorm_sub_le _ _
    _ ≤ vectorNorm z + (K + 3 * j) * vectorNorm w := add_le_add le_rfl hL
    _ ≤ vectorNorm z + (K + 3 * j) * (vectorNorm z / c) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hv hD)
    _ = (1 + (K + 3 * j) / c) * vectorNorm z := by ring

end SKGap
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

end SKGapCutoff.Recipe

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
-- module Solutions.OAIQ072_SK.SKGap_Localization_BilinearCoefficient
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
namespace SKGapCutoff.RandomMatrix

lemma matrix_column_sq_le {n : ℕ} (J : Interaction n) (j : Fin n) :
    ∑ i, J i j^2 ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) J‖^2 := by
  let A := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) J
  let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single j 1
  have he : ‖e‖ = 1 := by simp [e]
  have hh : ‖A e‖ ≤ ‖A‖ := by simpa only [he, mul_one] using A.le_opNorm e
  have hv : ‖A e‖^2 = ∑ i, J i j^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    have hi : A e i = J i j := by
      change (∑ k, J i k * ((Pi.single j (1:ℝ) : Fin n → ℝ) k)) = J i j
      simp [Pi.single_apply]
    rw [hi]
  rw [← hv]
  exact pow_le_pow_left₀ (norm_nonneg _) hh 2

end SKGapCutoff.RandomMatrix

open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set

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

lemma vectorNorm_mono {u v : Fin n→ℝ} (h : ∀i,|u i|≤|v i|) : vectorNorm u ≤ vectorNorm v := by
  apply nonneg_le_nonneg_of_sq_le_sq (vectorNorm_nonneg _)
  simp only [←sq,vectorNorm_sq]
  exact Finset.sum_le_sum fun i _=>by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (u i)) (h i) 2

lemma vectorNorm_abs (u : Fin n→ℝ) : vectorNorm (fun i=>|u i|)=vectorNorm u := by
  apply (sq_eq_sq₀ (vectorNorm_nonneg _) (vectorNorm_nonneg _)).mp
  simp [vectorNorm_sq]

lemma vectorNorm_matrix_mul (J : Interaction n) (u : Fin n→ℝ) :
    vectorNorm (J.mulVec u) ≤ SKGap.opNorm J*vectorNorm u := by
  exact (Matrix.toEuclideanCLM (𝕜:=ℝ) J).le_opNorm (WithLp.toLp 2 u)

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

end SKGapCutoff.Recipe

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
-- module Solutions.OAIQ072_SK.SKGap_Matrix_MatrixQuad
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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma matrixQuad_smul (M : Matrix ι ι ℝ) (p : EuclideanSpace ℝ ι) (c : ℝ) :
    matrixQuad M (c • p) = c^2 * matrixQuad M p := by
  simp only [matrixQuad, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

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
lemma mag_succ (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) (i : Fin n) :
    mag j J h (k+1) x i=Real.tanh (fld j J h k x i) := rfl
lemma onsager_zero (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) :
    onsager j J h 0 x=0 := by simp [onsager,siteMean,mag_zero,spin_sq]

lemma fld_eq (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) (i : Fin n) :
    fld j J h k x i=h i+∑a,J i a*mag j J h k x a-
      j*onsager j J h k x*mag j J h (k-1) x i := by
  cases k with
  | zero => simp [fld,primaryState,mag,onsager_zero]
  | succ k => rfl

end SKGapCutoff.Primary

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_WeakResidual
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
variable {n : ℕ}

lemma conditionalVariance_le_one (P : Spin n→ℝ) (x : Spin n) (i : Fin n) :
    conditionalVariance P x i≤1 := by dsimp [conditionalVariance]; nlinarith [sq_nonneg (conditionalMean P x i)]

end SKGapCutoff.Static

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
-- module Solutions.OAIQ072_SK.SKGap_Localization_ResidualMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
variable {n : ℕ}

lemma halfDiff_mul_flipped (i : Fin n) (θ G : Observables n) (x : Spin n) :
    halfDiff i (fun y=>θ y*G y) x=θ (flip x i)*halfDiff i G x+G x*halfDiff i θ x := by
  rw [halfDiff_mul]
  have h:=flip_sub i θ x
  rw [show θ (flip x i)=θ x-2*spin x i*halfDiff i θ x by linarith]
  ring

end SKGapCutoff.Static

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
namespace SKGapCutoff.Primary
variable {n : ℕ}
lemma onsager_bounds (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) :
    0≤onsager j J h k x ∧ onsager j J h k x≤1 := by
  have hm (i : Fin n) : (mag j J h k x i)^2≤1 := by
    have H:=primaryState_mag_bounded j J h k x i
    have H':=sq_le_sq₀ (abs_nonneg (mag j J h k x i)) (by norm_num : (0:ℝ)≤1)
    simpa only [sq_abs,one_pow] using H'.mpr H
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun i _=>sub_nonneg.mpr (hm i))) (Nat.cast_nonneg n)
  · by_cases hn : n=0
    · simp [onsager,siteMean,hn]
    · apply (div_le_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).mpr
      calc
        (∑i:Fin n,(1-(mag j J h k x i)^2)) ≤ ∑i:Fin n,(1:ℝ) :=
          Finset.sum_le_sum fun i _=>sub_le_self _ (sq_nonneg _)
        _ = _ := by simp
end SKGapCutoff.Primary

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

end SKGapCutoff.Primary

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_UniformResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
open Primary Recipe
universe u
variable {Ω : Type u} {n : Ω→ℕ}

lemma scalar_product_bounds {n : ℕ} (θ η : Observables n) {B L D K : ℝ}
    (hB : 0≤B) (_ : 0≤L) (_ : 0≤D) (_ : 0≤K)
    (ht : ∀x,|θ x|≤B) (hdt : ∀x,∑i,(halfDiff i θ x)^2≤L^2)
    (he : ∀x,|η x|≤D) (hde : ∀x,∑i,(halfDiff i η x)^2≤K^2) :
    (∀x,|θ x*η x|≤B*D) ∧
    (∀x,∑i,(halfDiff i (fun y=>θ y*η y) x)^2≤(Real.sqrt (2*B^2*K^2+2*D^2*L^2))^2) := by
  constructor
  · intro x; rw [abs_mul]; exact mul_le_mul (ht x) (he x) (abs_nonneg _) hB
  · intro x
    rw [Real.sq_sqrt (by positivity)]
    calc
      _ ≤ ∑i,(2*B^2*(halfDiff i η x)^2+2*D^2*(halfDiff i θ x)^2) := by
        apply Finset.sum_le_sum; intro i _
        rw [halfDiff_mul_flipped]
        have h1 : (θ (flip x i))^2≤B^2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (ht (flip x i)) 2
        have h2 : (η x)^2≤D^2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (he x) 2
        have h1':=mul_le_mul_of_nonneg_right h1 (sq_nonneg (halfDiff i η x))
        have h2':=mul_le_mul_of_nonneg_right h2 (sq_nonneg (halfDiff i θ x))
        nlinarith only [h1',h2',sq_nonneg (θ (flip x i)*halfDiff i η x-η x*halfDiff i θ x)]
      _ = 2*B^2*(∑i,(halfDiff i η x)^2)+2*D^2*(∑i,(halfDiff i θ x)^2) := by
        simp only [Finset.sum_add_distrib,Finset.mul_sum]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hde x) (by positivity))
        (mul_le_mul_of_nonneg_left (hdt x) (by positivity))

end SKGapCutoff.Static

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_FieldGibbs
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

lemma vectorPair_derivative (U V : VectorFields n) (x : Spin n) :
    derivativeVector (vectorPair U V) x =
      (Matrix.toEuclideanCLM (n:=Fin n) (𝕜:=ℝ) (derivativeMatrix U x)ᵀ) (WithLp.toLp 2 (V x))+
      (Matrix.toEuclideanCLM (n:=Fin n) (𝕜:=ℝ) (derivativeMatrix V x)ᵀ) (WithLp.toLp 2 (U x))-
      WithLp.toLp 2 (fun k=>2*spin x k*∑i,derivativeMatrix U x i k*derivativeMatrix V x i k) := by
  ext k
  change halfDiff k (vectorPair U V) x =
    (∑i,halfDiff k (fun y=>U y i) x*V x i)+
    (∑i,halfDiff k (fun y=>V y i) x*U x i)-
    2*spin x k*∑i,halfDiff k (fun y=>U y i) x*halfDiff k (fun y=>V y i) x
  have hh : halfDiff k (vectorPair U V) x=∑i,halfDiff k (fun y=>U y i*V y i) x := by
    simp only [halfDiff,vectorPair]
    rw [← Finset.sum_sub_distrib,Finset.sum_div]
  rw [hh,← Finset.sum_add_distrib,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [halfDiff_mul]
  ring

lemma vectorPair_abs (U V : VectorFields n) (x : Spin n) :
    |vectorPair U V x| ≤ vectorNorm (U x)*vectorNorm (V x) := by
  simpa [vectorPair,vectorNorm,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,mul_comm] using
    abs_real_inner_le_norm (WithLp.toLp 2 (U x) : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 (V x))

lemma vectorPair_cross_bound (U V : VectorFields n) (x : Spin n)
    {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hu : SKGap.opNorm (derivativeMatrix U x)≤A) (hv : SKGap.opNorm (derivativeMatrix V x)≤B) :
    vectorNorm (fun k=>2*spin x k*∑i,derivativeMatrix U x i k*derivativeMatrix V x i k) ≤
      2*A*B*Real.sqrt (n:ℝ) := by
  have hcol (M : Interaction n) {C : ℝ} (hC : 0≤C) (hM : SKGap.opNorm M≤C) (k : Fin n) :
      vectorNorm (fun i=>M i k)≤C := by
    apply nonneg_le_nonneg_of_sq_le_sq hC
    simp only [← sq,vectorNorm_sq]
    exact (RandomMatrix.matrix_column_sq_le M k).trans (pow_le_pow_left₀ (norm_nonneg _) hM 2)
  have hdot (k : Fin n) : |∑i,derivativeMatrix U x i k*derivativeMatrix V x i k|≤A*B := by
    exact (vectorPair_abs (fun _ i=>derivativeMatrix U x i k)
      (fun _ i=>derivativeMatrix V x i k) x).trans
      (mul_le_mul (hcol _ hA hu k) (hcol _ hB hv k) (vectorNorm_nonneg _) hA)
  apply nonneg_le_nonneg_of_sq_le_sq (by positivity)
  simp only [← sq,vectorNorm_sq]
  calc
    _ ≤ ∑ _k : Fin n,(2*A*B)^2 := by
      apply Finset.sum_le_sum
      intro k _
      have hb : |2*spin x k*∑i,derivativeMatrix U x i k*derivativeMatrix V x i k|≤2*A*B := by
        simpa only [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2),abs_spin_eq_one,mul_one,one_mul,mul_assoc] using
          mul_le_mul_of_nonneg_left (hdot k) (by norm_num : (0:ℝ)≤2)
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hb 2
    _ = _ := by simp [mul_pow,Real.sq_sqrt (Nat.cast_nonneg n)]; ring

lemma vectorPair_derivative_bound (U V : VectorFields n) (x : Spin n)
    {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hu : SKGap.opNorm (derivativeMatrix U x)≤A) (hv : SKGap.opNorm (derivativeMatrix V x)≤B) :
    ‖derivativeVector (vectorPair U V) x‖ ≤
      A*vectorNorm (V x)+B*vectorNorm (U x)+2*A*B*Real.sqrt (n:ℝ) := by
  have hop (M : Interaction n) (u : Fin n→ℝ) {C : ℝ} (hM : SKGap.opNorm M≤C) :
      ‖(Matrix.toEuclideanCLM (n:=Fin n) (𝕜:=ℝ) Mᵀ) (WithLp.toLp 2 u)‖≤C*vectorNorm u := by
    apply (ContinuousLinearMap.le_opNorm _ _).trans
    change SKGap.opNorm Mᵀ*vectorNorm u≤_
    rw [SKGap.opNorm_transpose]
    exact mul_le_mul_of_nonneg_right hM (vectorNorm_nonneg u)
  rw [vectorPair_derivative]
  exact (norm_sub_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add (hop _ _ hu) (hop _ _ hv)))
    (vectorPair_cross_bound U V x hA hB hu hv))

lemma normalizedPair_derivative (U V : VectorFields n) (x : Spin n) :
    derivativeVector (normalizedPair U V) x =
      (Real.sqrt (n:ℝ))⁻¹ • derivativeVector (vectorPair U V) x := by
  ext k
  simp only [derivativeVector,WithLp.ofLp_toLp,PiLp.smul_apply,smul_eq_mul,normalizedPair,halfDiff]
  ring

lemma normalizedPair_derivative_bound (hn : 0<n) (U V : VectorFields n) (x : Spin n)
    {A B Cu Cv : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hu : SKGap.opNorm (derivativeMatrix U x)≤A) (hv : SKGap.opNorm (derivativeMatrix V x)≤B)
    (hU : vectorNorm (U x)≤Cu*Real.sqrt (n:ℝ))
    (hV : vectorNorm (V x)≤Cv*Real.sqrt (n:ℝ)) :
    ‖derivativeVector (normalizedPair U V) x‖≤A*Cv+B*Cu+2*A*B := by
  have hs : 0<Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  rw [normalizedPair_derivative,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs)]
  calc
    _ ≤ (Real.sqrt (n:ℝ))⁻¹*(A*vectorNorm (V x)+B*vectorNorm (U x)+2*A*B*Real.sqrt (n:ℝ)) :=
      mul_le_mul_of_nonneg_left (vectorPair_derivative_bound U V x hA hB hu hv) (inv_nonneg.mpr hs.le)
    _ ≤ (Real.sqrt (n:ℝ))⁻¹*(A*(Cv*Real.sqrt (n:ℝ))+B*(Cu*Real.sqrt (n:ℝ))+2*A*B*Real.sqrt (n:ℝ)) := by
      gcongr
    _ = _ := by field_simp

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_ResidualPairMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Static
open Primary Recipe
variable {n : ℕ}

lemma varianceEnergy_gradient_bound (P : Observables n) (hP : ∀x,0≤P x)
    (hp : ∑x,P x=1) (f : Observables n) {L : ℝ}
    (hd : ∀x,∑i,(halfDiff i f x)^2≤L^2) : varianceEnergy P f≤L^2 := by
  calc
    _ ≤ ∑x,P x*L^2 := by
      apply Finset.sum_le_sum; intro x _
      apply mul_le_mul_of_nonneg_left _ (hP x)
      exact (Finset.sum_le_sum (fun i _=>mul_le_of_le_one_left (sq_nonneg _) (conditionalVariance_le_one P x i))).trans (hd x)
    _ = _ := by rw [←Finset.sum_mul,hp,one_mul]

end SKGapCutoff.Static
namespace SKGapCutoff.Recipe
open Primary Static
variable {n : ℕ}

lemma mag_vectorNorm (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) :
    vectorNorm (mag j J h k x)≤Real.sqrt (n:ℝ) := by
  apply nonneg_le_nonneg_of_sq_le_sq (Real.sqrt_nonneg _)
  simp only [←sq,vectorNorm_sq,Real.sq_sqrt (Nat.cast_nonneg n)]
  calc
    _ ≤ ∑_i:Fin n,(1:ℝ)^2 := Finset.sum_le_sum (fun i _=>by
      simpa only [sq_abs,mag] using pow_le_pow_left₀ (abs_nonneg _) (primaryState_mag_bounded j J h k x i) 2)
    _ = _ := by simp

lemma residual_vectorNorm (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) :
    vectorNorm (residual j J h k x)≤2*Real.sqrt (n:ℝ) := by
  have he : vectorNorm (residual j J h k x)≤vectorNorm (mag j J h k x)+vectorNorm (mag j J h (k+1) x) :=
    norm_sub_le (WithLp.toLp 2 (mag j J h k x) : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 (mag j J h (k+1) x))
  exact he.trans ((add_le_add (mag_vectorNorm j J h k x) (mag_vectorNorm j J h (k+1) x)).trans_eq (by ring))

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_SmoothSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal ContDiff
namespace SKGapCutoff.Recipe
open Primary Static
variable {n : ℕ}

lemma residualScalarCutoff_bounds (u : ℝ) :
    0 ≤ residualScalarCutoff u ∧ residualScalarCutoff u≤1 := by
  refine ⟨mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _),?_⟩
  exact (mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
    (Real.smoothTransition.nonneg _) (by norm_num)).trans_eq (by simp)

lemma residualScalarCutoff_zero {u : ℝ} (hu : 1≤u) : residualScalarCutoff u=0 := by
  simp [residualScalarCutoff,Real.smoothTransition.zero_of_nonpos (by linarith : (1-u)*4/3≤0)]

lemma residualScalarCutoff_smooth : ContDiff ℝ ∞ residualScalarCutoff := by
  unfold residualScalarCutoff
  fun_prop

lemma residualScalarCutoff_lipschitz : ∃K,LipschitzWith K residualScalarCutoff := by
  have hc : HasCompactSupport residualScalarCutoff := by
    apply HasCompactSupport.intro' (K:=Set.Icc (-1:ℝ) 1) isCompact_Icc isClosed_Icc
    intro x hx
    simp only [Set.mem_Icc,not_and_or,not_le] at hx
    rcases hx with hx|hx
    · simp [residualScalarCutoff,Real.smoothTransition.zero_of_nonpos (by linarith : (1+x)*4/3≤0)]
    · exact residualScalarCutoff_zero hx.le
  exact ContDiff.lipschitzWith_of_hasCompactSupport hc residualScalarCutoff_smooth (by simp)

lemma norm_derivativeVector_sq (f : Spin n→ℝ) (x : Spin n) :
    ‖derivativeVector f x‖^2=∑i,(halfDiff i f x)^2 := by
  exact vectorNorm_sq (fun i=>halfDiff i f x)

lemma derivativeVector_norm_mono (f g : Spin n→ℝ) (x : Spin n) {C : ℝ} (hC : 0≤C)
    (h : ∀i,|halfDiff i f x|≤C*|halfDiff i g x|) :
    ‖derivativeVector f x‖≤C*‖derivativeVector g x‖ := by
  apply nonneg_le_nonneg_of_sq_le_sq (by positivity)
  simp only [←sq,mul_pow,norm_derivativeVector_sq,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  simpa only [sq_abs,mul_pow] using pow_le_pow_left₀ (abs_nonneg _) (h i) 2

lemma derivativeVector_comp_lipschitz {φ : ℝ→ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ)
    (f : Spin n→ℝ) (x : Spin n) :
    ‖derivativeVector (fun x=>φ (f x)) x‖≤(K:ℝ)*‖derivativeVector f x‖ := by
  apply derivativeVector_norm_mono _ _ _ K.coe_nonneg
  intro i
  have h:=hφ.dist_le_mul (f (replace x i true)) (f (replace x i false))
  simpa only [halfDiff,abs_div,Real.dist_eq,abs_of_pos (by norm_num : (0:ℝ)<2),mul_div_assoc] using
    div_le_div_of_nonneg_right h (by norm_num : (0:ℝ)≤2)

lemma derivativeVector_scale (c : ℝ) (f : Spin n→ℝ) (x : Spin n) :
    derivativeVector (fun y=>c*f y) x=c • derivativeVector f x := by
  ext i
  simp only [derivativeVector,WithLp.ofLp_toLp,PiLp.smul_apply,smul_eq_mul,halfDiff]
  ring

lemma residualEnergy_as_pair (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) :
    residualEnergy j J h k x =
      (Real.sqrt (n:ℝ))⁻¹*normalizedPair (residual j J h k) (residual j J h k) x := by
  simp only [residualEnergy,vectorNorm_sq,normalizedPair,vectorPair]
  simp only [inv_mul_eq_div,div_div,Real.mul_self_sqrt (Nat.cast_nonneg n),sq]

lemma residualEnergy_gradient (hn : 0<n) (j : ℝ) (J : Interaction n) (h : Fin n→ℝ)
    (k : ℕ) (x : Spin n) {A : ℝ} (hA : 0≤A)
    (hd : SKGap.opNorm (derivativeMatrix (residual j J h k) x)≤A) :
    ‖derivativeVector (residualEnergy j J h k) x‖≤(4*A+2*A^2)/Real.sqrt (n:ℝ) := by
  have he : residualEnergy j J h k=fun y=>(Real.sqrt (n:ℝ))⁻¹*
      normalizedPair (residual j J h k) (residual j J h k) y := funext (residualEnergy_as_pair j J h k)
  rw [he,derivativeVector_scale,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  have hb:=normalizedPair_derivative_bound hn (residual j J h k) (residual j J h k) x hA hA hd hd
    (residual_vectorNorm j J h k x) (residual_vectorNorm j J h k x)
  exact (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (Real.sqrt_nonneg _))).trans_eq (by ring)

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators NNReal
namespace SKGapCutoff.Recipe
open Primary Static
variable {n : ℕ}

lemma residualStepCutoff_bounds (ρ j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) :
    0 ≤ residualStepCutoff ρ j J h k x ∧ residualStepCutoff ρ j J h k x≤1 := residualScalarCutoff_bounds _
lemma residualCutoff_bounds (ρ j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) :
    0 ≤ residualCutoff ρ j J h k x ∧ residualCutoff ρ j J h k x≤1 := by
  have h0:=residualStepCutoff_bounds ρ j J h k x
  have h1:=residualStepCutoff_bounds ρ j J h (k+1) x
  exact ⟨mul_nonneg h0.1 h1.1,(mul_le_mul h0.2 h1.2 h1.1 (by norm_num)).trans_eq (by simp)⟩

lemma residualStepCutoff_support (hn : 0<n) {ρ j : ℝ} (hρ : 0<ρ)
    (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n)
    (hc : residualStepCutoff ρ j J h k x≠0) :
    vectorNorm (residual j J h k x)≤ρ*Real.sqrt (n:ℝ) := by
  have hr : residualEnergy j J h k x/ρ^2<1 :=
    lt_of_not_ge (fun hh=>hc (residualScalarCutoff_zero hh))
  have he : residualEnergy j J h k x≤ρ^2 := by
    exact ((div_lt_one (sq_pos_of_pos hρ)).mp hr).le
  apply nonneg_le_nonneg_of_sq_le_sq (by positivity)
  simp only [←sq,mul_pow,Real.sq_sqrt (Nat.cast_nonneg n)]
  exact (div_le_iff₀ (Nat.cast_pos.mpr hn)).mp he

lemma residualCutoff_support (hn : 0<n) {ρ j : ℝ} (hρ : 0<ρ)
    (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n)
    (hc : residualCutoff ρ j J h k x≠0) :
    vectorNorm (residual j J h k x)≤ρ*Real.sqrt (n:ℝ) ∧
    vectorNorm (residual j J h (k+1) x)≤ρ*Real.sqrt (n:ℝ) := by
  have H:=mul_ne_zero_iff.mp hc
  exact ⟨residualStepCutoff_support hn hρ J h k x H.1,residualStepCutoff_support hn hρ J h (k+1) x H.2⟩

lemma derivativeVector_mul_bound (f g : Spin n→ℝ) (x : Spin n)
    (hf : ∀x,|f x|≤1) (hg : ∀x,|g x|≤1) {A B : ℝ}
    (hA : 0≤A) (hB : 0≤B)
    (hdF : ‖derivativeVector f x‖≤A) (hdG : ‖derivativeVector g x‖≤B) :
    ‖derivativeVector (fun y=>f y*g y) x‖≤2*(A+B) := by
  have ht (i : Fin n) : (halfDiff i (fun y=>f y*g y) x)^2≤
      2*(halfDiff i f x)^2+2*(halfDiff i g x)^2 := by
    have hf' : (f (flip x i))^2≤1 := by simpa only [sq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg _) (hf (flip x i)) 2
    have hg' : (g x)^2≤1 := by simpa only [sq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg _) (hg x) 2
    rw [halfDiff_mul_flipped]
    nlinarith [mul_le_mul_of_nonneg_right hf' (sq_nonneg (halfDiff i g x)),
      mul_le_mul_of_nonneg_right hg' (sq_nonneg (halfDiff i f x)),
      sq_nonneg (f (flip x i)*halfDiff i g x-g x*halfDiff i f x)]
  have hb : ‖derivativeVector (fun y=>f y*g y) x‖^2≤2*A^2+2*B^2 := by
    calc
      _ ≤ ∑i,(2*(halfDiff i f x)^2+2*(halfDiff i g x)^2) := by
        rw [norm_derivativeVector_sq]; exact Finset.sum_le_sum (fun i _=>ht i)
      _ = 2*‖derivativeVector f x‖^2+2*‖derivativeVector g x‖^2 := by
        simp only [norm_derivativeVector_sq,Finset.sum_add_distrib,Finset.mul_sum]
      _ ≤ _ := by nlinarith [pow_le_pow_left₀ (norm_nonneg _) hdF 2,pow_le_pow_left₀ (norm_nonneg _) hdG 2]
  apply nonneg_le_nonneg_of_sq_le_sq (by positivity)
  simp only [←sq]
  nlinarith [mul_nonneg hA hB,sq_nonneg A,sq_nonneg B]

lemma residualStepCutoff_gradient (hn : 0<n) {j ρ : ℝ} (_ : 0<ρ)
    {K : ℝ≥0} (hK : LipschitzWith K residualScalarCutoff)
    (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) {A : ℝ} (hA : 0≤A)
    (hd : SKGap.opNorm (derivativeMatrix (residual j J h k) x)≤A) :
    ‖derivativeVector (residualStepCutoff ρ j J h k) x‖≤
      (K:ℝ)/ρ^2*(4*A+2*A^2)/Real.sqrt (n:ℝ) := by
  apply (derivativeVector_comp_lipschitz hK (fun y=>residualEnergy j J h k y/ρ^2) x).trans
  have he : (fun y=>residualEnergy j J h k y/ρ^2)=fun y=>(ρ^2)⁻¹*residualEnergy j J h k y := by
    funext y; ring
  rw [he,derivativeVector_scale,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
  exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (residualEnergy_gradient hn j J h k x hA hd) (inv_nonneg.mpr (sq_nonneg _))) K.coe_nonneg).trans_eq (by ring)

lemma residualCutoff_gradient (hn : 0<n) {j ρ : ℝ} (hρ : 0<ρ)
    {K : ℝ≥0} (hK : LipschitzWith K residualScalarCutoff)
    (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (h0 : SKGap.opNorm (derivativeMatrix (residual j J h k) x)≤A)
    (h1 : SKGap.opNorm (derivativeMatrix (residual j J h (k+1)) x)≤B) :
    ‖derivativeVector (residualCutoff ρ j J h k) x‖≤
      (2*(K:ℝ)/ρ^2*((4*A+2*A^2)+(4*B+2*B^2)))/Real.sqrt (n:ℝ) := by
  apply (derivativeVector_mul_bound _ _ x
    (fun y=>by rw [abs_of_nonneg (residualStepCutoff_bounds ρ j J h k y).1];exact (residualStepCutoff_bounds ρ j J h k y).2)
    (fun y=>by rw [abs_of_nonneg (residualStepCutoff_bounds ρ j J h (k+1) y).1];exact (residualStepCutoff_bounds ρ j J h (k+1) y).2)
    (by positivity) (by positivity)
    (residualStepCutoff_gradient hn hρ hK J h k x hA h0)
    (residualStepCutoff_gradient hn hρ hK J h (k+1) x hB h1)).trans_eq
  ring

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ConstantRecipe
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
variable {n : ℕ}

lemma residualDerivativeBudget_nonneg {j R B : ℝ} (hR : 0≤R) (hB : 0≤B) (k : ℕ) :
    0 ≤ residualDerivativeBudget j R B k :=
  add_nonneg (differentiationBound_nonneg hR hB k) (differentiationBound_nonneg hR hB (k+1))

lemma residual_derivative_bound (hn : 0<n) {j R B : ℝ} (hR : 0≤R) (hB : 0≤B)
    (J : Interaction n) (h : Fin n→ℝ) (hJ : SKGap.opNorm J≤R) (k : ℕ)
    (hformal : ∀x l,l≤k+1→ShapeBound (formalField j J h x l) B) (x : Spin n) :
    SKGap.opNorm (derivativeMatrix (residual j J h k) x) ≤ residualDerivativeBudget j R B k := by
  have hm (l : ℕ) (hl : l≤k+1) :
      SKGap.opNorm (derivativeMatrix (mag j J h l) x)≤differentiationBound j R B l :=
    (primary_differentiation J h x hn hR hB hJ l (fun t ht=>hformal x t (ht.trans hl))).2.2.1
  rw [show derivativeMatrix (residual j J h k) x=
    derivativeMatrix (mag j J h k) x-derivativeMatrix (mag j J h (k+1)) x from derivativeMatrix_sub _ _ x]
  simp only [opNorm_eq,map_sub]
  exact (norm_sub_le _ _).trans (add_le_add (hm _ (by omega)) (hm _ le_rfl))

universe u

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_TapPotential
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Real Matrix Set Filter Function
open scoped Topology
namespace SKGap

lemma quadraticForm_derivative_algebra {n : ℕ} {J : Matrix (Fin n) (Fin n) ℝ}
    (hJ : J.IsSymm) (m w : Field n) :
    (∑ i, ∑ k, (w i * J i k * m k + m i * J i k * w k)) =
      2 * ∑ i, w i * (∑ k, J i k * m k) := by
  simp only [Finset.sum_add_distrib]
  have he : (∑ i, ∑ k, m i * J i k * w k) = ∑ i, ∑ k, w i * J i k * m k := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    rw [hJ.apply k i]
    ring
  rw [he]
  simp only [← Finset.mul_sum, mul_assoc]
  ring

lemma quadratic_magnetization_hasFDerivAt {n : ℕ} {J : Matrix (Fin n) (Fin n) ℝ}
    (hJ : J.IsSymm) (y : Field n) :
    HasFDerivAt (fun z => quadraticForm J (magnetization z))
      (2 • ∑ i, (spinVariance y i * (∑ k, J i k * magnetization y k)) •
        (ContinuousLinearMap.proj i : Field n →L[ℝ] ℝ)) y := by
  have hd := HasFDerivAt.sum (u := Finset.univ) (fun i _ =>
    HasFDerivAt.sum (u := Finset.univ) (fun k _ =>
      ((magnetization_hasFDerivAt y i).mul_const (J i k)).mul
        (magnetization_hasFDerivAt y k)))
  convert! hd using 1
  · ext z
    simp only [quadraticForm, Finset.sum_apply, Pi.mul_apply]
  ext v
  simp only [_root_.smul_apply, _root_.sum_apply, _root_.add_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, nsmul_eq_mul]
  have he := quadraticForm_derivative_algebra hJ (magnetization y)
    (fun i => spinVariance y i * v i)
  calc
    _ = 2 * ∑ i, (spinVariance y i * v i) * (∑ k, J i k * magnetization y k) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ i, ∑ k, ((spinVariance y i * v i) * J i k * magnetization y k +
        magnetization y i * J i k * (spinVariance y k * v k)) := he.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      ring

lemma squared_magnetization_hasFDerivAt {n : ℕ} (y : Field n) :
    HasFDerivAt (fun z => vectorSqNorm (magnetization z))
      (∑ i, (2*magnetization y i*spinVariance y i) •
        (ContinuousLinearMap.proj i : Field n →L[ℝ] ℝ)) y := by
  convert! (HasFDerivAt.sum (u := Finset.univ)
    (fun i _ => (magnetization_hasFDerivAt y i).pow 2)) using 1
  · ext z
    simp only [vectorSqNorm, Finset.sum_apply]
  ext v
  simp only [_root_.sum_apply, _root_.smul_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, Nat.reduceSub, pow_one]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma tapPotential_hasFDerivAt {n : ℕ} (j : ℝ)
    {J : Matrix (Fin n) (Fin n) ℝ} (hJ : J.IsSymm) (h y : Field n) :
    HasFDerivAt (tapPotential j J h)
      (∑ i, weightedTap j J h y i •
        (ContinuousLinearMap.proj i : Field n →L[ℝ] ℝ)) y := by
  have hsinglei (i : Fin n) :
      HasFDerivAt (fun z : Field n => z i * tanh (z i) - log (cosh (z i)))
        ((y i*(1-tanh (y i)^2)) • (ContinuousLinearMap.proj i : Field n →L[ℝ] ℝ)) y := by
    have hd := ((hasFDerivAt_apply (𝕜 := ℝ) i y).mul
      (magnetization_hasFDerivAt y i)).sub
      (((hasFDerivAt_apply (𝕜 := ℝ) i y).cosh).log (cosh_pos (y i)).ne')
    convert! hd using 1
    all_goals try with_reducible_and_instances rfl
    ext v
    simp only [_root_.smul_apply, _root_.sub_apply, _root_.add_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul, spinVariance, magnetization,
      tanh_eq_sinh_div_cosh]
    ring
  have hsingle := HasFDerivAt.sum (u := Finset.univ) (fun i _ => hsinglei i)
  have hext := HasFDerivAt.sum (u := Finset.univ) (fun i _ =>
    (magnetization_hasFDerivAt y i).const_mul (h i))
  have hquad := (quadratic_magnetization_hasFDerivAt hJ y).const_mul (1/2:ℝ)
  have hsq := (squared_magnetization_hasFDerivAt y).const_mul (j/2)
  have hfour := ((squared_magnetization_hasFDerivAt y).pow 2).const_mul (j/(4*n))
  convert! (((hsingle.sub hext).sub hquad).add hsq).sub hfour using 1
  · ext z
    simp only [tapPotential, Finset.sum_apply, Pi.sub_apply, Pi.add_apply, magnetization]
  ext v
  simp only [_root_.sum_apply, _root_.smul_apply, _root_.sub_apply, _root_.add_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, nsmul_eq_mul,
    Nat.cast_ofNat, Nat.reduceSub, pow_one]
  simp only [weightedTap, tapField, onsager, overlap, vectorSqNorm, spinVariance,
    magnetization]
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  ring

lemma contDiff_tanh_SK {m : WithTop ℕ∞} : ContDiff ℝ m tanh := by
  have he : tanh = sinh / cosh := funext tanh_eq_sinh_div_cosh
  rw [he]
  exact contDiff_sinh.div contDiff_cosh (fun x => (cosh_pos x).ne')

lemma magnetization_contDiff {n : ℕ} {m : WithTop ℕ∞} (i : Fin n) :
    ContDiff ℝ m (fun y : Field n => magnetization y i) :=
  contDiff_tanh_SK.comp (contDiff_apply ℝ ℝ i)

lemma spinVariance_contDiff {n : ℕ} {m : WithTop ℕ∞} (i : Fin n) :
    ContDiff ℝ m (fun y : Field n => spinVariance y i) :=
  contDiff_const.sub ((magnetization_contDiff i).pow 2)

lemma overlap_contDiff {n : ℕ} {m : WithTop ℕ∞} :
    ContDiff ℝ m (overlap (n := n)) :=
  (ContDiff.sum (fun i _ => (magnetization_contDiff i).pow 2)).div_const _

lemma tapField_contDiff {n : ℕ} {m : WithTop ℕ∞} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) : ContDiff ℝ m (tapField j J h) := by
  apply contDiff_pi.mpr
  intro i
  exact ((contDiff_apply ℝ ℝ i).sub contDiff_const).add
    ((contDiff_const.mul (contDiff_const.sub overlap_contDiff)).mul
      (magnetization_contDiff i)) |>.sub
        (ContDiff.sum (fun k _ => contDiff_const.mul (magnetization_contDiff k)))

lemma weightedTap_contDiff {n : ℕ} {m : WithTop ℕ∞} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) : ContDiff ℝ m (weightedTap j J h) := by
  apply contDiff_pi.mpr
  intro i
  exact (spinVariance_contDiff i).mul (contDiff_pi.mp (tapField_contDiff j J h) i)

lemma weightedTapE_contDiff {n : ℕ} {m : WithTop ℕ∞} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) : ContDiff ℝ m (weightedTapE j J h) :=
  (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm.contDiff.comp
    ((weightedTap_contDiff j J h).comp
      (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).contDiff)

lemma tapPotentialE_hasFDerivAt {n : ℕ} (j : ℝ)
    {J : Matrix (Fin n) (Fin n) ℝ} (hJ : J.IsSymm) (h : Field n) (y : EField n) :
    HasFDerivAt (tapPotentialE j J h) (innerSL ℝ (weightedTapE j J h y)) y := by
  have hd := (tapPotential_hasFDerivAt j hJ h (WithLp.ofLp y)).comp y
    (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).hasFDerivAt
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  ext v
  simp only [innerSL_apply_apply, weightedTapE, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial, ContinuousLinearMap.comp_apply,
    _root_.sum_apply, _root_.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  change v i * weightedTap j J h (WithLp.ofLp y) i =
    weightedTap j J h (WithLp.ofLp y) i * v i
  ring

lemma weightedTap_hasFDerivAt_zero {n : ℕ} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (h y : Field n)
    (hz : tapField j J h y = 0) :
    HasFDerivAt (weightedTap j J h) (weightedJacobianMap j J y) y := by
  rw [hasFDerivAt_pi']
  intro i
  have hV := ((spinVariance_contDiff i (m := 1)).differentiable (by norm_num) y).hasFDerivAt
  have hF := hasFDerivAt_pi'.mp (tapField_hasFDerivAt j J h y) i
  have hzi : tapField j J h y i = 0 := congrFun hz i
  have hd := hV.mul hF
  simp only [hzi, zero_smul, add_zero] at hd
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl

lemma weightedTapE_fderiv_zero {n : ℕ} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) (y v : EField n)
    (hz : tapField j J h (WithLp.ofLp y) = 0) (i : Fin n) :
    (fderiv ℝ (weightedTapE j J h) y v) i =
      spinVariance (WithLp.ofLp y) i *
        ((fieldJacobian j J (WithLp.ofLp y)).mulVec (WithLp.ofLp v)) i := by
  let e := EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)
  have hd := e.symm.hasFDerivAt.comp y
    ((weightedTap_hasFDerivAt_zero j J h (WithLp.ofLp y) hz).comp y e.hasFDerivAt)
  have he : fderiv ℝ (weightedTapE j J h) y =
      e.symm.toContinuousLinearMap.comp ((weightedJacobianMap j J (WithLp.ofLp y)).comp
        e.toContinuousLinearMap) := hd.fderiv
  rw [he]
  rfl

lemma weighted_jacobian_quadratic_form {n : ℕ} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (y v : Field n) :
    (∑ i, v i * (spinVariance y i * ((fieldJacobian j J y).mulVec v) i)) =
      quadraticForm (fieldHessian j J y (spinVariance y)) (sqrtVarianceMul y v) := by
  simp only [Matrix.mulVec, dotProduct, quadraticForm, sqrtVarianceMul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  have hi := sq_sqrt (spinVariance_pos y i).le
  calc
    _ = (sqrt (spinVariance y i) * v i) *
        (sqrt (spinVariance y i)*fieldJacobian j J y i k) * v k := by
      conv_lhs => rw [← hi]
      ring
    _ = _ := by rw [← fieldHessian_variance_intertwine]; ring

lemma weightedTapE_derivative_energy {n : ℕ} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) (y v : EField n)
    (hz : tapField j J h (WithLp.ofLp y) = 0) :
    inner ℝ v (fderiv ℝ (weightedTapE j J h) y v) =
      quadraticForm (fieldHessian j J (WithLp.ofLp y) (spinVariance (WithLp.ofLp y)))
        (sqrtVarianceMul (WithLp.ofLp y) (WithLp.ofLp v)) := by
  rw [← weighted_jacobian_quadratic_form]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro i _
  rw [weightedTapE_fderiv_zero j J h y v hz i]
  ring

lemma spinVariance_eq_inv_cosh_sq {n : ℕ} (y : Field n) (i : Fin n) :
    spinVariance y i = 1 / cosh (y i)^2 := by
  simp only [spinVariance, magnetization, tanh_eq_sinh_div_cosh]
  field_simp
  exact cosh_sq_sub_sinh_sq _

lemma spinVariance_bound_on_box {n : ℕ} (y : Field n) {R : ℝ} (hR : 0 ≤ R)
    (hy : ∀ i, |y i| ≤ R) (i : Fin n) :
    1 / cosh R^2 ≤ spinVariance y i := by
  rw [spinVariance_eq_inv_cosh_sq]
  apply one_div_le_one_div_of_le (sq_pos_of_pos (cosh_pos (y i)))
  have h : cosh (y i) ≤ cosh R := cosh_le_cosh.mpr
    (by simpa only [abs_of_nonneg hR] using hy i)
  exact pow_le_pow_left₀ (cosh_pos (y i)).le h 2

lemma tapField_shift_bound {n : ℕ} (hn : 0 < n) {j : ℝ} (hj : 0 ≤ j)
    (J : Matrix (Fin n) (Fin n) ℝ) (h y : Field n) (i : Fin n) :
    |y i - tapField j J h y i| ≤ |h i| + j + ∑ k, |J i k| := by
  have hm (k : Fin n) : |magnetization y k| ≤ 1 := by
    exact (abs_lt.mpr ⟨neg_one_lt_tanh _, tanh_lt_one _⟩).le
  have hB0 : 0 ≤ onsager j y := mul_nonneg hj (sub_nonneg.mpr (overlap_lt_one hn y).le)
  have hBj : onsager j y ≤ j := by
    dsimp [onsager]
    nlinarith [overlap_nonneg y]
  have hBm : |onsager j y * magnetization y i| ≤ j := by
    rw [abs_mul, abs_of_nonneg hB0]
    exact (mul_le_of_le_one_right hB0 (hm i)).trans hBj
  have hJm : |∑ k, J i k * magnetization y k| ≤ ∑ k, |J i k| := by
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hm k))
  have he : y i-tapField j J h y i = h i-onsager j y*magnetization y i +
      ∑ k, J i k*magnetization y k := by simp only [tapField]; ring
  rw [he]
  have hs : |h i-onsager j y*magnetization y i| ≤ |h i|+j := by
    calc
      _ ≤ |h i|+|onsager j y*magnetization y i| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le (h i) (-(onsager j y*magnetization y i))
      _ ≤ _ := add_le_add_right hBm _
  exact (abs_add_le _ _).trans (add_le_add hs hJm)

lemma exists_tapBox_radius {n : ℕ} (hn : 0 < n) {j : ℝ} (hj : 0 ≤ j)
    (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) :
    ∃ R : ℝ, 0 < R ∧ ∀ y : Field n, ∀ i, |y i-tapField j J h y i| ≤ R := by
  let b := fun i => |h i| + j + ∑ k, |J i k|
  have hb (i : Fin n) : 0 ≤ b i := by dsimp [b]; positivity
  refine ⟨1+∑ i, b i, by positivity, fun y i => ?_⟩
  exact (tapField_shift_bound hn hj J h y i).trans
    ((Finset.single_le_sum (fun k _ => hb k) (Finset.mem_univ i)).trans (by linarith))

lemma weightedTap_step_box {n : ℕ} (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h y : Field n) {R ε : ℝ} (hε : ε ∈ Set.Icc (0:ℝ) 1)
    (hbound : ∀ i, |y i-tapField j J h y i| ≤ R) (hy : ∀ i, |y i| ≤ R) :
    ∀ i, |(y-ε • weightedTap j J h y) i| ≤ R := by
  intro i
  let a := ε*spinVariance y i
  have ha0 : 0 ≤ a := mul_nonneg hε.1 (spinVariance_pos y i).le
  have ha1 : a ≤ 1 := (mul_le_mul_of_nonneg_left (spinVariance_le_one y i) hε.1).trans
    (by simpa using hε.2)
  have he : (y-ε • weightedTap j J h y) i =
      (1-a)*y i + a*(y i-tapField j J h y i) := by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, weightedTap, a]
    ring
  rw [he]
  calc
    _ ≤ |(1-a)*y i| + |a*(y i-tapField j J h y i)| := abs_add_le _ _
    _ = (1-a)*|y i| + a*|y i-tapField j J h y i| := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha0, abs_of_nonneg (sub_nonneg.mpr ha1)]
    _ ≤ (1-a)*R+a*R := add_le_add
      (mul_le_mul_of_nonneg_left (hy i) (sub_nonneg.mpr ha1))
      (mul_le_mul_of_nonneg_left (hbound i) ha0)
    _ = R := by ring

lemma mem_fieldBoxE {n : ℕ} {R : ℝ} (hR : 0 ≤ R) (y : EField n) :
    y ∈ fieldBoxE n R ↔ ∀ i, |y i| ≤ R := by
  simp only [fieldBoxE, Set.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hn : ‖x‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    change ∀ i, |x i| ≤ R
    simpa only [Real.norm_eq_abs] using (pi_norm_le_iff_of_nonneg hR).mp hn
  · intro hy
    refine ⟨WithLp.ofLp y, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hR]
    exact hy

lemma isCompact_fieldBoxE (n : ℕ) (R : ℝ) : IsCompact (fieldBoxE n R) :=
  (isCompact_closedBall (0:Field n) R).image
    (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm.continuous

lemma convex_fieldBoxE (n : ℕ) (R : ℝ) : Convex ℝ (fieldBoxE n R) :=
  (convex_closedBall (0:Field n) R).linear_image
    (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm.toLinearMap

lemma nonempty_fieldBoxE (n : ℕ) {R : ℝ} (hR : 0 ≤ R) : (fieldBoxE n R).Nonempty :=
  ⟨0, (mem_fieldBoxE hR 0).mpr (fun _ => by simpa using hR)⟩

theorem lyapunov_eventually_hits {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (T : X → X) (hT : Continuous T) (φ : X → ℝ) (hφ : Continuous φ)
    (hstrict : ∀ x, T x ≠ x → φ (T x) < φ x)
    {U : Set X} (hU : IsOpen U) (hfix : ∀ x, T x = x → x ∈ U) (x : X) :
    ∃ n : ℕ, T^[n] x ∈ U := by
  by_contra! hnever
  have hK : IsCompact Uᶜ := hU.isClosed_compl.isCompact
  have hne : Uᶜ.Nonempty := ⟨x, by simpa using hnever 0⟩
  obtain ⟨y, hy, hmin⟩ := hK.exists_isMinOn hne (hφ.sub (hφ.comp hT)).continuousOn
  let δ := φ y - φ (T y)
  have hd : 0 < δ := sub_pos.mpr (hstrict y (fun h => hy (hfix y h)))
  have hdec (n : ℕ) : δ ≤ φ (T^[n] x) - φ (T (T^[n] x)) :=
    hmin (hnever n)
  obtain ⟨m, hm⟩ := isCompact_univ.bddBelow_image hφ.continuousOn
  have hlower (z : X) : m ≤ φ z := hm ⟨z, mem_univ _, rfl⟩
  have hbound (n : ℕ) : φ (T^[n] x) ≤ φ x - (n:ℝ)*δ := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [iterate_succ_apply']
      have h := hdec n
      push_cast
      nlinarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((φ x - m)/δ)
  have hn' : φ x - m < (n:ℝ)*δ := (div_lt_iff₀ hd).mp hn
  have hb := hbound n
  have hl := hlower (T^[n] x)
  linarith

theorem lyapunov_fixed_point {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [Nonempty X] (T : X → X) (φ : X → ℝ) (hφ : Continuous φ)
    (hstrict : ∀ x, T x ≠ x → φ (T x) < φ x) : ∃ x, T x = x := by
  obtain ⟨x, _, hx⟩ := isCompact_univ.exists_isMinOn univ_nonempty hφ.continuousOn
  refine ⟨x, by_contra fun h => ?_⟩
  exact (not_lt_of_ge (hx (mem_univ (T x)))) (hstrict x h)

section Basins
variable {X : Type*} [TopologicalSpace X] (T : X → X)

lemma mem_attractionBasin_iterate_iff (p x : X) (k : ℕ) :
    T^[k] x ∈ attractionBasin T p ↔ x ∈ attractionBasin T p := by
  simpa only [attractionBasin, mem_ofPred_eq, iterate_add_apply] using
    (tendsto_add_atTop_iff_nat (f := fun n : ℕ => T^[n] x) (l := 𝓝 p) k)

lemma fixed_mem_attractionBasin {p : X} (hp : T p = p) : p ∈ attractionBasin T p := by
  simp only [attractionBasin, mem_ofPred_eq, iterate_fixed hp]
  exact tendsto_const_nhds

end Basins
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_AttractionBasinIUnion
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Real Matrix Set Filter Function
open scoped Topology
namespace SKGap
section Basins
variable {X : Type*} [TopologicalSpace X] (T : X → X)

lemma attractionBasin_eq_iUnion {p : X} {U : Set X} (hU : IsOpen U) (hp : p ∈ U)
    (hatt : U ⊆ attractionBasin T p) :
    attractionBasin T p = ⋃ k : ℕ, (T^[k]) ⁻¹' U := by
  ext x
  constructor
  · intro hx
    have h := hx.eventually (hU.mem_nhds hp)
    obtain ⟨k, hk⟩ := h.exists
    exact mem_iUnion.mpr ⟨k, hk⟩
  · intro hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    exact (mem_attractionBasin_iterate_iff T p x k).mp (hatt hk)

lemma isOpen_attractionBasin (hT : Continuous T) {p : X} {U : Set X}
    (hU : IsOpen U) (hp : p ∈ U) (hatt : U ⊆ attractionBasin T p) :
    IsOpen (attractionBasin T p) := by
  rw [attractionBasin_eq_iUnion T hU hp hatt]
  exact isOpen_iUnion (fun k => hU.preimage (hT.iterate k))

lemma disjoint_attractionBasins [T2Space X] {p q : X} (hpq : p ≠ q) :
    Disjoint (attractionBasin T p) (attractionBasin T q) := by
  rw [disjoint_left]
  intro x hx hy
  exact hpq (tendsto_nhds_unique hx hy)

end Basins

theorem lyapunov_unique_fixed_point {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [ConnectedSpace X] [T2Space X]
    (T : X → X) (hT : Continuous T) (φ : X → ℝ) (hφ : Continuous φ)
    (hstrict : ∀ x, T x ≠ x → φ (T x) < φ x)
    (hattract : ∀ p, T p = p → ∃ U : Set X, IsOpen U ∧ p ∈ U ∧
      U ⊆ attractionBasin T p) : ∃! p, T p = p := by
  have hopen (p) (hp : T p = p) : IsOpen (attractionBasin T p) := by
    obtain ⟨U, hU, hpU, hatt⟩ := hattract p hp
    exact isOpen_attractionBasin T hT hU hpU hatt
  have hcover (x : X) : ∃ p, T p = p ∧ x ∈ attractionBasin T p := by
    let U := ⋃ p : {p // T p = p}, attractionBasin T p.val
    have hU : IsOpen U := isOpen_iUnion (fun p => hopen p.val p.property)
    have hfixed (p) (hp : T p = p) : p ∈ U :=
      mem_iUnion.mpr ⟨⟨p, hp⟩, fixed_mem_attractionBasin T hp⟩
    obtain ⟨k, hk⟩ := lyapunov_eventually_hits T hT φ hφ hstrict hU hfixed x
    obtain ⟨p, hp⟩ := mem_iUnion.mp hk
    exact ⟨p.val, p.property, (mem_attractionBasin_iterate_iff T p.val x k).mp hp⟩
  obtain ⟨p, hp⟩ := lyapunov_fixed_point T φ hφ hstrict
  refine ⟨p, hp, fun q hq => ?_⟩
  by_contra hqp
  let V := ⋃ q : {q // T q = q ∧ q ≠ p}, attractionBasin T q.val
  have hV : IsOpen V := isOpen_iUnion (fun q => hopen q.val q.property.1)
  have hdisj : Disjoint (attractionBasin T p) V := by
    rw [disjoint_iUnion_right]
    intro q
    exact disjoint_attractionBasins T q.property.2.symm
  have hcov : (univ : Set X) ⊆ attractionBasin T p ∪ V := by
    intro x _
    obtain ⟨r, hr, hx⟩ := hcover x
    by_cases he : r = p
    · subst r
      exact Or.inl hx
    · exact Or.inr (mem_iUnion.mpr ⟨⟨r, hr, he⟩, hx⟩)
  have hconn := IsPreconnected.subset_or_subset (hopen p hp) hV hdisj hcov
    isPreconnected_univ
  rcases hconn with hconn | hconn
  · have hqp' := tendsto_nhds_unique (hconn (mem_univ q))
      (fixed_mem_attractionBasin T hq)
    exact hqp hqp'.symm
  · exact disjoint_left.mp hdisj (fixed_mem_attractionBasin T hp) (hconn (mem_univ p))

theorem local_contraction_attracts {X : Type*} [MetricSpace X]
    {T : X → X} {p : X} (hp : T p = p) {K : NNReal} (hK : K < 1)
    {U : Set X} (hU : U ∈ 𝓝 p) (hlip : LipschitzOnWith K T U) :
    ∃ V : Set X, IsOpen V ∧ p ∈ V ∧ V ⊆ attractionBasin T p := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  have hpU : p ∈ U := hball (Metric.mem_ball_self hε)
  have hmaps : MapsTo T (Metric.ball p ε) (Metric.ball p ε) := by
    intro x hx
    have h := hlip.dist_le_mul x (hball hx) p hpU
    rw [hp] at h
    exact h.trans_lt ((mul_le_of_le_one_left (dist_nonneg : 0 ≤ dist x p)
      (show (K:ℝ) ≤ 1 by exact_mod_cast hK.le)).trans_lt hx)
  refine ⟨Metric.ball p ε, Metric.isOpen_ball, Metric.mem_ball_self hε, ?_⟩
  intro x hx
  have hbd (n : ℕ) : dist (T^[n] x) p ≤ (K:ℝ)^n * dist x p := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [iterate_succ_apply']
      have h := hlip.dist_le_mul (T^[n] x) (hball (hmaps.iterate n hx)) p hpU
      rw [hp] at h
      exact h.trans (by simpa only [pow_succ', mul_assoc] using
        mul_le_mul_of_nonneg_left ih K.coe_nonneg)
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one K.coe_nonneg
    (show (K:ℝ) < 1 by exact_mod_cast hK)).mul_const (dist x p)
  rw [zero_mul] at ht
  exact Metric.tendsto_atTop.mpr (fun δ hδ => by
    obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hδ))
    exact ⟨N, fun n hn => (hbd n).trans_lt (hN n hn)⟩)

end SKGap

noncomputable section
open Set Function Real
open scoped Topology NNReal
namespace SKGap
section GradientDescent
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem lipschitz_gradient_remainder {φ : E → ℝ} {G : E → E} {s : Set E}
    (hs : Convex ℝ s) (hgrad : ∀ x ∈ s, HasFDerivAt φ (innerSL ℝ (G x)) x)
    {L : ℝ≥0} (hG : LipschitzOnWith L G s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    |φ y - φ x - inner ℝ (G x) (y-x)| ≤ (L:ℝ)*‖y-x‖^2 := by
  let d := y-x
  let ℓ : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y
  let f := fun t : ℝ => φ (ℓ t) - t * inner ℝ (G x) d
  let f' := fun t : ℝ => inner ℝ (G (ℓ t) - G x) d
  have hℓ (t : ℝ) : ℓ t = x + t • d := by
    simp only [ℓ, d, AffineMap.lineMap_apply_module]
    module
  have hmem (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : ℓ t ∈ s :=
    hs.mapsTo_lineMap hx hy ht
  have hf (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      HasDerivWithinAt f (f' t) (Icc (0:ℝ) 1) t := by
    have hd := ((hgrad (ℓ t) (hmem t ht)).comp_hasDerivAt t
      AffineMap.hasDerivAt_lineMap).sub
      ((hasDerivAt_id t).mul_const (inner ℝ (G x) d))
    convert! (hd.hasDerivWithinAt (s := Icc (0:ℝ) 1)) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [f', innerSL_apply_apply, inner_sub_left, d, one_mul]
  have hb (t : ℝ) (ht : t ∈ Ico (0:ℝ) 1) :
      ‖f' t‖ ≤ (L:ℝ)*‖d‖^2 := by
    have hdiff : ‖ℓ t-x‖ ≤ ‖d‖ := by
      rw [hℓ, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg _) ht.2.le
    have h := (hG.norm_sub_le (hmem t ⟨ht.1, ht.2.le⟩) hx).trans
      (mul_le_mul_of_nonneg_left hdiff L.coe_nonneg)
    calc
      ‖f' t‖ ≤ ‖G (ℓ t)-G x‖*‖d‖ := norm_inner_le_norm _ _
      _ ≤ ((L:ℝ)*‖d‖)*‖d‖ := mul_le_mul_of_nonneg_right h (norm_nonneg d)
      _ = _ := by ring
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01' hf hb
  simpa only [f, ℓ, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one,
    zero_mul, sub_zero, one_mul, Real.norm_eq_abs, d, sub_right_comm] using h

theorem gradient_step_strict_descent {φ : E → ℝ} {G : E → E} {s : Set E}
    (hs : Convex ℝ s) (hgrad : ∀ x ∈ s, HasFDerivAt φ (innerSL ℝ (G x)) x)
    {L : ℝ≥0} (hG : LipschitzOnWith L G s) {ε : ℝ} (hε : 0 < ε)
    (hsmall : (L:ℝ)*ε < 1) {x : E} (hx : x ∈ s) (hstep : x-ε • G x ∈ s)
    (hGx : G x ≠ 0) : φ (x-ε • G x) < φ x := by
  have h := (le_abs_self _).trans (lipschitz_gradient_remainder hs hgrad hG hx hstep)
  have he : x-ε • G x-x = -ε • G x := by module
  rw [he, inner_smul_right, real_inner_self_eq_norm_sq,
    norm_smul, Real.norm_eq_abs, abs_of_neg (neg_neg_of_pos hε)] at h
  have hn : 0 < ‖G x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hGx)
  have hc : 0 < ε*(1-(L:ℝ)*ε)*‖G x‖^2 := by positivity
  nlinarith only [h, hc]

theorem gradient_step_derivative_sq_bound {D : E →L[ℝ] E} {c M ε : ℝ}
    (_hc : 0 ≤ c) (_hM : 0 ≤ M) (hε : 0 ≤ ε)
    (hcoercive : ∀ v, c*‖v‖^2 ≤ inner ℝ v (D v)) (hbound : ‖D‖ ≤ M)
    (v : E) :
    ‖v-ε • D v‖^2 ≤ (1-2*ε*c+ε^2*M^2)*‖v‖^2 := by
  have hD : ‖D v‖ ≤ M*‖v‖ := D.le_of_opNorm_le hbound v
  have hD2 : ‖D v‖^2 ≤ M^2*‖v‖^2 := by
    nlinarith [norm_nonneg (D v), mul_nonneg _hM (norm_nonneg v)]
  have h := mul_le_mul_of_nonneg_left (hcoercive v) (show 0 ≤ 2*ε by positivity)
  have h' := mul_le_mul_of_nonneg_left hD2 (sq_nonneg ε)
  rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hε]
  nlinarith only [h, h']

end GradientDescent
end SKGap

end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_TapFieldE
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Real Matrix Set Filter Function
open scoped Topology
noncomputable section
open Set Function Real
open scoped Topology NNReal
namespace SKGap
section GradientRoots
open Set Function Filter Real
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma exists_small_gradient_step {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ M*ε < 1 ∧ 2*ε*c ≤ 1 ∧ ε*M^2 < c := by
  have h1 : 0 < 1/(M+1) := by positivity
  have h2 : 0 < 1/(2*c+1) := by positivity
  have h3 : 0 < c/(M^2+1) := by positivity
  obtain ⟨ε, hε, he⟩ := exists_between
    (lt_min (by norm_num : (0:ℝ) < 1) (lt_min h1 (lt_min h2 h3)))
  have he1 := (lt_min_iff.mp he).1
  have he2 := (lt_min_iff.mp (lt_min_iff.mp he).2).1
  have he3 := (lt_min_iff.mp (lt_min_iff.mp (lt_min_iff.mp he).2).2).1
  have he4 := (lt_min_iff.mp (lt_min_iff.mp (lt_min_iff.mp he).2).2).2
  have hp2 := (lt_div_iff₀ (show 0 < M+1 by positivity)).mp he2
  have hp3 := (lt_div_iff₀ (show 0 < 2*c+1 by positivity)).mp he3
  have hp4 := (lt_div_iff₀ (show 0 < M^2+1 by positivity)).mp he4
  exact ⟨ε, hε, he1.le, by nlinarith, by nlinarith, by nlinarith⟩

lemma gradient_step_derivative_norm_lt {D : E →L[ℝ] E} {c M ε : ℝ}
    (hc : 0 < c) (hM : 0 ≤ M) (hε : 0 < ε)
    (hsmall0 : 2*ε*c ≤ 1) (hsmall1 : ε*M^2 < c)
    (hcoercive : ∀ v, c*‖v‖^2 ≤ inner ℝ v (D v)) (hbound : ‖D‖ ≤ M) :
    ‖ContinuousLinearMap.id ℝ E - ε • D‖ < 1 := by
  let k := 1-2*ε*c+ε^2*M^2
  have hk0 : 0 ≤ k := by dsimp [k]; nlinarith [sq_nonneg (ε*M)]
  have hk1 : k < 1 := by
    dsimp [k]
    have h := mul_lt_mul_of_pos_left hsmall1 hε
    nlinarith
  have hb : ‖ContinuousLinearMap.id ℝ E - ε • D‖ ≤ sqrt k := by
    refine (ContinuousLinearMap.id ℝ E - ε • D).opNorm_le_bound (sqrt_nonneg k) ?_
    intro v
    change ‖v-ε • D v‖ ≤ sqrt k * ‖v‖
    have h := gradient_step_derivative_sq_bound hc.le hM hε.le hcoercive hbound v
    have hp : 0 ≤ sqrt k*‖v‖ := by positivity
    apply (sq_le_sq₀ (norm_nonneg _) hp).mp
    calc
      ‖v-ε • D v‖^2 ≤ k*‖v‖^2 := h
      _ = (sqrt k*‖v‖)^2 := by rw [mul_pow, sq_sqrt hk0]
  exact hb.trans_lt (by simpa using sqrt_lt_sqrt hk0 hk1)

theorem gradient_unique_zero_on_compact
    {φ : E → ℝ} {G : E → E} {s : Set E}
    (hcompact : IsCompact s) (hne : s.Nonempty) (hconv : Convex ℝ s)
    (hgrad : ∀ x, HasFDerivAt φ (innerSL ℝ (G x)) x)
    (hG : ContDiff ℝ 1 G)
    {c : ℝ} (hc : 0 < c)
    (hcoercive : ∀ x ∈ s, G x = 0 → ∀ v, c*‖v‖^2 ≤ inner ℝ v (fderiv ℝ G x v))
    (hinvariant : ∀ ε ∈ Icc (0:ℝ) 1, MapsTo (fun x => x-ε • G x) s s) :
    ∃! x : s, G x = 0 := by
  let : CompactSpace s := isCompact_iff_compactSpace.mp hcompact
  let : Nonempty s := hne.to_subtype
  let : ConnectedSpace s := isConnected_iff_connectedSpace.mp (hconv.isConnected hne)
  have hbound : ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ s, ‖fderiv ℝ G x‖ ≤ M := by
    obtain ⟨M, hM⟩ := hcompact.bddAbove_image
      (hG.continuous_fderiv (by norm_num)).norm.continuousOn
    refine ⟨max M 0, le_max_right _ _, fun x hx => ?_⟩
    exact (hM ⟨x, hx, rfl⟩).trans (le_max_left _ _)
  obtain ⟨M, hM, hbound⟩ := hbound
  obtain ⟨ε, hε, hε1, hεM, hεc, hεM2⟩ := exists_small_gradient_step hc hM
  let L : ℝ≥0 := ⟨M, hM⟩
  have hLip : LipschitzOnWith L G s :=
    hconv.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (fun x _ => (hG.differentiable (by norm_num) x).hasFDerivAt.hasFDerivWithinAt)
      (fun x hx => by exact_mod_cast hbound x hx)
  let T : s → s := fun x => ⟨x.val-ε • G x.val, hinvariant ε ⟨hε.le,hε1⟩ x.property⟩
  have hT : Continuous T := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.sub
      (continuous_const.smul (hG.continuous.comp continuous_subtype_val))
  let ψ : s → ℝ := fun x => φ x.val
  have hψ : Continuous ψ :=
    (continuous_iff_continuousAt.mpr fun x => (hgrad x).continuousAt).comp continuous_subtype_val
  have hzero (x : s) : T x = x ↔ G x.val = 0 := by
    rw [Subtype.ext_iff]
    change x.val-ε • G x.val = x.val ↔ G x.val = 0
    simp only [sub_eq_self, smul_eq_zero, hε.ne', false_or]
  have hstrict (x : s) (hx : T x ≠ x) : ψ (T x) < ψ x := by
    exact gradient_step_strict_descent hconv (fun x _ => hgrad x) hLip hε hεM
      x.property (T x).property (fun h => hx ((hzero x).mpr h))
  have hattract (p : s) (hp : T p = p) :
      ∃ U : Set s, IsOpen U ∧ p ∈ U ∧ U ⊆ attractionBasin T p := by
    let D := ContinuousLinearMap.id ℝ E - ε • fderiv ℝ G p.val
    have hD : HasStrictFDerivAt (fun x : E => x-ε • G x) D p.val :=
      (hasStrictFDerivAt_id p.val).sub
        ((hG.contDiffAt.hasStrictFDerivAt (by norm_num)).const_smul ε)
    have hDn : ‖D‖ < 1 := gradient_step_derivative_norm_lt hc hM hε hεc hεM2
      (hcoercive p.val p.property ((hzero p).mp hp)) (hbound p.val p.property)
    have hDnn : ‖D‖₊ < 1 := by exact_mod_cast hDn
    obtain ⟨K, hDK, hK⟩ := exists_between hDnn
    obtain ⟨U, hU, hULip⟩ := hD.exists_lipschitzOnWith_of_nnnorm_lt K hDK
    have hpre : Subtype.val ⁻¹' U ∈ 𝓝 p := continuous_subtype_val.continuousAt.preimage_mem_nhds hU
    have hpreLip : LipschitzOnWith K T (Subtype.val ⁻¹' U) := by
      rw [lipschitzOnWith_iff_dist_le_mul]
      intro x hx y hy
      exact hULip.dist_le_mul x.val hx y.val hy
    exact local_contraction_attracts hp hK hpre hpreLip
  obtain ⟨p, hp, huniq⟩ := lyapunov_unique_fixed_point T hT ψ hψ hstrict hattract
  exact ⟨p, (hzero p).mp hp, fun q hq => huniq q ((hzero q).mpr hq)⟩

end GradientRoots

lemma weightedTapE_eq_zero_iff {n : ℕ} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) (y : EField n) :
    weightedTapE j J h y = 0 ↔ tapField j J h (WithLp.ofLp y) = 0 := by
  constructor
  · intro hz
    ext i
    have he := congrArg (fun z : EField n => z i) hz
    change spinVariance (WithLp.ofLp y) i * tapField j J h (WithLp.ofLp y) i = 0 at he
    exact (mul_eq_zero.mp he).resolve_left (spinVariance_pos (WithLp.ofLp y) i).ne'
  · intro hz
    ext i
    change spinVariance (WithLp.ofLp y) i * tapField j J h (WithLp.ofLp y) i = 0
    rw [hz, Pi.zero_apply, mul_zero]

lemma weightedTapE_coercive_on_box {n : ℕ} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) {R c : ℝ}
    (hR : 0 ≤ R) (hc : 0 ≤ c) (y : EField n) (hy : y ∈ fieldBoxE n R)
    (hz : tapField j J h (WithLp.ofLp y) = 0)
    (hH : ∀ x : Field n, c*vectorSqNorm x ≤
      quadraticForm (fieldHessian j J (WithLp.ofLp y) (spinVariance (WithLp.ofLp y))) x)
    (v : EField n) :
    (c / cosh R^2)*‖v‖^2 ≤ inner ℝ v (fderiv ℝ (weightedTapE j J h) y v) := by
  rw [weightedTapE_derivative_energy j J h y v hz]
  have hV := spinVariance_bound_on_box (WithLp.ofLp y) hR ((mem_fieldBoxE hR y).mp hy)
  have hb : (1 / cosh R^2)*‖v‖^2 ≤ vectorSqNorm (sqrtVarianceMul (WithLp.ofLp y) (WithLp.ofLp v)) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [vectorSqNorm, sqrtVarianceMul, Finset.mul_sum, mul_pow,
      sq_sqrt (spinVariance_pos _ _).le]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (hV i) (sq_nonneg _)
  have h := (mul_le_mul_of_nonneg_left hb hc).trans (hH _)
  simpa only [mul_assoc, div_eq_mul_inv, one_mul] using h

theorem tap_unique_zero {n : ℕ} (hn : 0 < n) {j c : ℝ} (hj : 0 ≤ j) (hc : 0 < c)
    {J : Matrix (Fin n) (Fin n) ℝ} (hJ : J.IsSymm) (h : Field n)
    (hH : ∀ y : Field n, tapField j J h y = 0 → ∀ x : Field n,
      c*vectorSqNorm x ≤ quadraticForm (fieldHessian j J y (spinVariance y)) x) :
    ∃! r : Field n, tapField j J h r = 0 := by
  obtain ⟨R, hR, hbound⟩ := exists_tapBox_radius hn hj J h
  have hco : ∀ y ∈ fieldBoxE n R, weightedTapE j J h y = 0 → ∀ v,
      (c / cosh R^2)*‖v‖^2 ≤ inner ℝ v (fderiv ℝ (weightedTapE j J h) y v) := by
    intro y hy hz v
    have hz' := (weightedTapE_eq_zero_iff j J h y).mp hz
    exact weightedTapE_coercive_on_box j J h hR.le hc.le y hy hz' (hH _ hz') v
  have hmaps : ∀ ε ∈ Set.Icc (0:ℝ) 1,
      Set.MapsTo (fun y => y-ε • weightedTapE j J h y) (fieldBoxE n R) (fieldBoxE n R) := by
    intro ε hε y hy
    rw [mem_fieldBoxE hR.le] at hy ⊢
    exact weightedTap_step_box j J h (WithLp.ofLp y) hε (hbound _) hy
  obtain ⟨r, hr, huniq⟩ := gradient_unique_zero_on_compact
    (isCompact_fieldBoxE n R) (nonempty_fieldBoxE n hR.le) (convex_fieldBoxE n R)
    (tapPotentialE_hasFDerivAt j hJ h) (weightedTapE_contDiff j J h)
    (show 0 < c / cosh R^2 by positivity) hco hmaps
  refine ⟨WithLp.ofLp r.val, (weightedTapE_eq_zero_iff j J h r.val).mp hr, ?_⟩
  intro y hy
  have hys : WithLp.toLp 2 y ∈ fieldBoxE n R := by
    rw [mem_fieldBoxE hR.le]
    intro i
    have hb := hbound y i
    simpa only [hy, Pi.zero_apply, sub_zero] using hb
  have hye : weightedTapE j J h (WithLp.toLp 2 y) = 0 :=
    (weightedTapE_eq_zero_iff j J h (WithLp.toLp 2 y)).mpr hy
  have he := congrArg (fun z : fieldBoxE n R => WithLp.ofLp z.val)
    (huniq ⟨WithLp.toLp 2 y, hys⟩ hye)
  exact he

theorem inverseOnConvex_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] {f : E → E} {U : Set E}
    (hU : IsOpen U) (hconv : Convex ℝ U) (hf : ContDiff ℝ 1 f)
    (hunique : ∀ z ∈ U, ∃! y, f y = z) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ y, f y ∈ U → ∀ v, ‖v‖ ≤ C * ‖fderiv ℝ f y v‖)
    {x y : E} (hx : f x ∈ U) (hy : f y ∈ U) :
    ‖y-x‖ ≤ C * ‖f y-f x‖ := by
  classical
  let g : E → E := fun z => if hz : z ∈ U then (hunique z hz).choose else 0
  have hg (z : E) (hz : z ∈ U) : f (g z) = z := by
    simp only [g, dite_eq_left hz]
    exact (hunique z hz).choose_spec.1
  have hgf (z : E) (hz : f z ∈ U) : g (f z) = z := by
    simp only [g, dite_eq_left hz]
    exact ((hunique (f z) hz).choose_spec.2 z rfl).symm
  have hinj (z : E) (hz : f z ∈ U) : Function.Injective (fderiv ℝ f z) := by
    intro a b hab
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    have hh := hbound z hz (a-b)
    rw [map_sub, hab, sub_self, norm_zero, mul_zero] at hh
    exact le_antisymm hh (norm_nonneg _)
  let D (z : E) : E →L[ℝ] E := fderiv ℝ f z
  let e (z : E) (hz : f z ∈ U) : E ≃L[ℝ] E :=
    (LinearEquiv.ofInjectiveEndo (D z).toLinearMap (hinj z hz)).toContinuousLinearEquiv
  have he (z : E) (hz : f z ∈ U) : (e z hz : E →L[ℝ] E) = D z := by
    ext v
    rfl
  have hgder (z : E) (hz : z ∈ U) :
      HasFDerivAt g ((e (g z) (by rw [hg z hz]; exact hz)).symm : E →L[ℝ] E) z := by
    let p := g z
    have hp : f p = z := hg z hz
    have hpU : f p ∈ U := hp ▸ hz
    have hder : HasStrictFDerivAt f (e p hpU : E →L[ℝ] E) p := by
      rw [he p hpU]
      exact hf.contDiffAt.hasStrictFDerivAt (by norm_num)
    have hleft : ∀ᶠ w in 𝓝 p, g (f w) = w := by
      filter_upwards [hf.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds hpU)] with w hw
      exact hgf w hw
    have H := (hder.to_local_left_inverse hleft).hasFDerivAt
    simpa only [hp] using H
  have hnorm (z : E) (hz : z ∈ U) :
      ‖((e (g z) (by rw [hg z hz]; exact hz)).symm : E →L[ℝ] E)‖ ≤ C := by
    apply ContinuousLinearMap.opNorm_le_bound _ hC
    intro v
    have hh := hbound (g z) (by rw [hg z hz]; exact hz)
      ((e (g z) (by rw [hg z hz]; exact hz)).symm v)
    change ‖_‖ ≤ C*‖D (g z) _‖ at hh
    rw [← he (g z) (by rw [hg z hz]; exact hz)] at hh
    simpa using hh
  have hd : DifferentiableOn ℝ g U := fun z hz => (hgder z hz).differentiableAt.differentiableWithinAt
  have hn : ∀ z ∈ U, ‖fderivWithin ℝ g U z‖ ≤ C := by
    intro z hz
    rw [(hgder z hz).hasFDerivWithinAt.fderivWithin (hU.uniqueDiffWithinAt hz)]
    exact hnorm z hz
  have H := hconv.norm_image_sub_le_of_norm_fderivWithin_le hd hn hx hy
  simpa only [hgf x hx, hgf y hy] using H

lemma tapFieldE_contDiff {n : ℕ} {m : WithTop ℕ∞} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) : ContDiff ℝ m (tapFieldE j J h) :=
  (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm.contDiff.comp
    ((tapField_contDiff j J h).comp
      (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).contDiff)

lemma norm_EField_eq {n : ℕ} (v : EField n) : ‖v‖ = vectorNorm (WithLp.ofLp v) := by
  simp only [EuclideanSpace.norm_eq, vectorNorm, Real.norm_eq_abs, sq_abs]

lemma tapFieldE_fderiv {n : ℕ} (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h : Field n) (y v : EField n) :
    fderiv ℝ (tapFieldE j J h) y v =
      WithLp.toLp 2 ((fieldJacobian j J (WithLp.ofLp y)).mulVec (WithLp.ofLp v)) := by
  let e := EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)
  have hd := e.symm.hasFDerivAt.comp y
    ((tapField_hasFDerivAt j J h (WithLp.ofLp y)).comp y e.hasFDerivAt)
  change HasFDerivAt (tapFieldE j J h) _ y at hd
  rw [hd.fderiv]
  rfl

lemma vectorNorm_zero (n : ℕ) : vectorNorm (0 : Field n) = 0 := by
  simp [vectorNorm]

lemma tapField_shift {n : ℕ} (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h z y : Field n) : tapField j J (h+z) y = tapField j J h y-z := by
  ext i
  simp only [tapField, Pi.add_apply, Pi.sub_apply]
  ring

theorem tap_root_and_distance {n : ℕ} (hn : 0 < n) {j K c R : ℝ}
    (hj : 0 ≤ j) (hK : 0 ≤ K) (hc : 0 < c) (hR : 0 < R)
    {J : Matrix (Fin n) (Fin n) ℝ} (hJsymm : J.IsSymm) (h : Field n)
    (hJ : ∀ z : Field n, vectorNorm (J.mulVec z) ≤ K*vectorNorm z)
    (hH : ∀ y : Field n, vectorNorm (tapField j J h y) ≤ R → ∀ x : Field n,
      c*vectorSqNorm x ≤ quadraticForm (fieldHessian j J y (spinVariance y)) x) :
    ∃ r : Field n, tapField j J h r = 0 ∧
      (∀ y, tapField j J h y = 0 → y = r) ∧
      ∀ y, vectorNorm (tapField j J h y) < R →
        vectorNorm (y-r) ≤ (1+(K+3*j)/c)*vectorNorm (tapField j J h y) := by
  have hH0 : ∀ y : Field n, tapField j J h y = 0 → ∀ x : Field n,
      c*vectorSqNorm x ≤ quadraticForm (fieldHessian j J y (spinVariance y)) x := by
    intro y hy
    apply hH y
    simpa only [hy, vectorNorm_zero] using hR.le
  obtain ⟨r, hr, huniq⟩ := tap_unique_zero hn hj hc hJsymm h hH0
  refine ⟨r, hr, huniq, ?_⟩
  intro y hy
  let F := tapFieldE j J h
  let U := Metric.ball (0 : EField n) R
  have hmem (v : EField n) : F v ∈ U ↔ vectorNorm (tapField j J h (WithLp.ofLp v)) < R := by
    simp only [U, Metric.mem_ball, dist_zero_right, F, norm_EField_eq, tapFieldE]
  have hsurj : ∀ z ∈ U, ∃! v, F v = z := by
    intro z hz
    have hzn : vectorNorm (WithLp.ofLp z) < R := by
      simpa only [U, Metric.mem_ball, dist_zero_right, norm_EField_eq] using hz
    have hHz : ∀ v : Field n, tapField j J (h+WithLp.ofLp z) v = 0 → ∀ x : Field n,
        c*vectorSqNorm x ≤ quadraticForm (fieldHessian j J v (spinVariance v)) x := by
      intro v hv
      rw [tapField_shift, sub_eq_zero] at hv
      exact hH v (by rw [hv]; exact hzn.le)
    obtain ⟨v, hv, huv⟩ := tap_unique_zero hn hj hc hJsymm (h+WithLp.ofLp z) hHz
    have hv' : tapField j J h v = WithLp.ofLp z := by
      simpa only [tapField_shift, sub_eq_zero] using hv
    refine ⟨WithLp.toLp 2 v, ?_, ?_⟩
    · change WithLp.toLp 2 (tapField j J h v) = z
      rw [hv', WithLp.toLp_ofLp]
    · intro w hw
      apply (WithLp.ofLp_injective 2)
      apply huv
      rw [tapField_shift, sub_eq_zero]
      exact congrArg WithLp.ofLp hw
  have hbound : ∀ v, F v ∈ U → ∀ w, ‖w‖ ≤ (1+(K+3*j)/c)*‖fderiv ℝ F v w‖ := by
    intro v hv w
    rw [tapFieldE_fderiv, norm_EField_eq, norm_EField_eq]
    exact fieldJacobian_inverse_bound hn hc hj hK J (WithLp.ofLp v) (WithLp.ofLp w)
      hJ (hH _ ((hmem v).mp hv).le)
  have hrmem : F (WithLp.toLp 2 r) ∈ U := by
    rw [hmem]
    simpa only [WithLp.ofLp_toLp, hr, vectorNorm_zero] using hR
  have hymem : F (WithLp.toLp 2 y) ∈ U := (hmem _).mpr hy
  have H := inverseOnConvex_bound Metric.isOpen_ball (convex_ball _ _) (tapFieldE_contDiff j J h)
    hsurj (show 0 ≤ 1+(K+3*j)/c by positivity) hbound hrmem hymem
  simpa only [norm_EField_eq, WithLp.ofLp_sub, WithLp.ofLp_toLp, F, tapFieldE, hr,
    sub_zero, WithLp.toLp_zero] using H

end SKGap

end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_ResidualRoot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static Matrix
variable {n : ℕ}

lemma primary_onsager_tap (hn : 0<n) (j : ℝ) (J : Interaction n) (h : Fin n→ℝ)
    (k : ℕ) (x : Spin n) :
    SKGap.onsager j (fld j J h k x)=j*onsager j J h (k+1) x := by
  have hnR : (n:ℝ)≠0:=ne_of_gt (Nat.cast_pos.mpr hn)
  simp only [SKGap.onsager,SKGap.overlap,SKGap.magnetization,onsager,siteMean,mag_succ,
    Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,sub_div,div_self hnR]

lemma primary_tap_residual (hn : 0<n) (j : ℝ) (J : Interaction n) (h : Fin n→ℝ)
    (k : ℕ) (x : Spin n) :
    SKGap.tapField j J h (fld j J h (k+1) x)=
      J.mulVec (Primary.residual j J h (k+1) x)-
      (fun i=>j*onsager j J h (k+1) x*(Primary.residual j J h k x i+Primary.residual j J h (k+1) x i))+
      (fun i=>j*(onsager j J h (k+2) x-onsager j J h (k+1) x)*mag j J h (k+2) x i) := by
  ext i
  simp only [SKGap.tapField,primary_onsager_tap hn,SKGap.magnetization,←mag_succ,
    Pi.add_apply,Pi.sub_apply,Matrix.mulVec,dotProduct]
  rw [fld_eq]
  simp only [Nat.add_sub_cancel,Primary.residual,mul_sub,Finset.sum_sub_distrib]
  ring

lemma onsager_residual_difference (hn : 0<n) (j : ℝ) (J : Interaction n)
    (h : Fin n→ℝ) (k : ℕ) (x : Spin n) :
    |onsager j J h (k+1) x-onsager j J h k x| *Real.sqrt (n:ℝ) ≤
      2*vectorNorm (Primary.residual j J h k x) := by
  have hnR : (0:ℝ)<n:=Nat.cast_pos.mpr hn
  have hs : 0<Real.sqrt (n:ℝ):=Real.sqrt_pos.mpr hnR
  have hd : onsager j J h (k+1) x-onsager j J h k x=
      (∑i,Primary.residual j J h k x i*(mag j J h k x i+mag j J h (k+1) x i))/(n:ℝ) := by
    simp only [onsager,siteMean,←sub_div,←Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl; intro i _; dsimp [Primary.residual]; ring
  have hv : vectorNorm (fun i=>mag j J h k x i+mag j J h (k+1) x i)≤2*Real.sqrt (n:ℝ) := by
    exact (SKGap.vectorNorm_add_le _ _).trans
      ((add_le_add (mag_vectorNorm j J h k x) (mag_vectorNorm j J h (k+1) x)).trans_eq (by ring))
  have hp := (SKGap.vector_dot_abs_le (Primary.residual j J h k x)
    (fun i=>mag j J h k x i+mag j J h (k+1) x i)).trans
      (mul_le_mul_of_nonneg_left hv (vectorNorm_nonneg _))
  rw [hd,abs_div,abs_of_pos hnR]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hnR).mpr
  convert mul_le_mul_of_nonneg_right hp (Real.sqrt_nonneg (n:ℝ)) using 1
  all_goals try with_reducible_and_instances rfl
  simp only [SKGap.vectorNorm,vectorNorm]
  ring_nf
  rw [Real.sq_sqrt hnR.le]

lemma primary_tap_norm (hn : 0<n) {j K : ℝ} (hj : 0≤j) (hK : 0≤K)
    (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n)
    (hop : ∀v,vectorNorm (J.mulVec v)≤K*vectorNorm v) :
    vectorNorm (SKGap.tapField j J h (fld j J h (k+1) x)) ≤
      j*vectorNorm (Primary.residual j J h k x)+(K+3*j)*vectorNorm (Primary.residual j J h (k+1) x) := by
  have hb:=onsager_bounds j J h (k+1) x
  have hJ : SKGap.opNorm J≤K := by
    apply ContinuousLinearMap.opNorm_le_bound _ hK
    intro value
    exact hop (WithLp.ofLp value)
  have hterm : vectorNorm (fun i=>j*onsager j J h (k+1) x*
      (Primary.residual j J h k x i+Primary.residual j J h (k+1) x i))≤
      j*(vectorNorm (Primary.residual j J h k x)+vectorNorm (Primary.residual j J h (k+1) x)) := by
    rw [show vectorNorm (fun i=>j*onsager j J h (k+1) x*
      (Primary.residual j J h k x i+Primary.residual j J h (k+1) x i))=
      |j*onsager j J h (k+1) x| *vectorNorm (Primary.residual j J h k x+Primary.residual j J h (k+1) x) from SKGap.vectorNorm_smul ..,
      abs_of_nonneg (mul_nonneg hj hb.1)]
    exact mul_le_mul (mul_le_of_le_one_right hj hb.2) (SKGap.vectorNorm_add_le _ _) (vectorNorm_nonneg _) hj
  have hlast : vectorNorm (fun i=>j*(onsager j J h (k+2) x-onsager j J h (k+1) x)*mag j J h (k+2) x i)≤
      2*j*vectorNorm (Primary.residual j J h (k+1) x) := by
    rw [show vectorNorm (fun i=>j*(onsager j J h (k+2) x-onsager j J h (k+1) x)*mag j J h (k+2) x i)=
      |j*(onsager j J h (k+2) x-onsager j J h (k+1) x)| *vectorNorm (mag j J h (k+2) x) from SKGap.vectorNorm_smul ..,
      abs_mul,abs_of_nonneg hj]
    calc
      _ ≤ j*|onsager j J h (k+2) x-onsager j J h (k+1) x| *Real.sqrt (n:ℝ) :=
        mul_le_mul_of_nonneg_left (mag_vectorNorm j J h (k+2) x) (by positivity)
      _ ≤ j*(2*vectorNorm (Primary.residual j J h (k+1) x)) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (onsager_residual_difference hn j J h (k+1) x) hj
      _ = _ := by ring
  rw [primary_tap_residual hn]
  exact (SKGap.vectorNorm_add_le _ _).trans ((add_le_add
    ((SKGap.vectorNorm_sub_le _ _).trans (add_le_add
      ((vectorNorm_matrix_mul _ _).trans (mul_le_mul_of_nonneg_right hJ (vectorNorm_nonneg _)))
      hterm)) hlast).trans_eq (by ring))

lemma magnetization_vector_lipschitz (y r : Fin n→ℝ) :
    vectorNorm (SKGap.magnetization y-SKGap.magnetization r)≤vectorNorm (y-r) := by
  apply (sq_le_sq₀ (vectorNorm_nonneg _) (vectorNorm_nonneg _)).mp
  simp only [vectorNorm_sq,Pi.sub_apply,SKGap.magnetization]
  exact Finset.sum_le_sum fun i _=>by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (tanh_lipschitz (r i) (y i)) 2

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Entropy_WeightedMean
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
variable {Ω : Type u} {N : Ω→ℕ} {j R B W C ρ : ℝ}
variable {J : ∀a,Interaction (N a)} {h e : ∀a,Fin (N a)→ℝ}

lemma magnetization_norm {n : ℕ} (r : Fin n→ℝ) :
    vectorNorm (SKGap.magnetization r)≤Real.sqrt (n:ℝ) := by
  apply nonneg_le_nonneg_of_sq_le_sq (Real.sqrt_nonneg _)
  simp only [←sq,vectorNorm_sq,Real.sq_sqrt (Nat.cast_nonneg n)]
  calc
    _ ≤ ∑_i:Fin n,(1:ℝ) := Finset.sum_le_sum (fun i _=>(Real.tanh_sq_lt_one (r i)).le)
    _ = _ := by simp

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
-- module Solutions.OAIQ072_SK.SKGap_Localization_PhiHessianBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary SKGap.ImplicitSystem Matrix
variable {n : ℕ}

lemma rank_toEuclideanCLM (m : Fin n→ℝ) :
    toEuclideanCLM (𝕜:=ℝ) (vecMulVec m m)=rank (WithLp.toLp 2 m) (WithLp.toLp 2 m) := by
  ext v i
  change ((vecMulVec m m).mulVec v.ofLp) i=(inner ℝ (WithLp.toLp 2 m) v)*m i
  simp only [mulVec, dotProduct, vecMulVec]
  change (∑k,m i*m k*v k)=(∑k,v k*m k)*m i
  rw [Finset.sum_mul]
  congr 1
  ext k
  ring

lemma fieldHessian_matrix (j : ℝ) (J : Interaction n) (z A : Fin n→ℝ) :
    SKGap.fieldHessian j J z A=
      1+(SKGap.onsager j z) • ((diagonal (fun i=>Real.sqrt (A i)))*(diagonal (fun i=>Real.sqrt (A i))))-
        diagonal (fun i=>Real.sqrt (A i))*J*diagonal (fun i=>Real.sqrt (A i))-
        (2*j/(n:ℝ)) • (diagonal (fun i=>Real.sqrt (A i))*
          vecMulVec (SKGap.magnetization z) (SKGap.magnetization z)*diagonal (fun i=>Real.sqrt (A i))) := by
  ext i k
  simp only [SKGap.fieldHessian,SKGap.hessianCore,Matrix.add_apply,Matrix.sub_apply,
    Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Matrix.diagonal_mul,Matrix.mul_diagonal,
    Matrix.diagonal_apply,vecMulVec,Matrix.of_apply]
  by_cases h:i=k
  · subst k; simp only [ite_true];ring
  · simp only [h,ite_false];ring

lemma onsager_scalarVariance (hn : 0<n) (j : ℝ) (z : Fin n→ℝ) :
    SKGap.onsager j z=j*((∑i,scalarVariance (z i))/(n:ℝ)) := by
  have hn0 : (n:ℝ)≠0:=ne_of_gt (Nat.cast_pos.mpr hn)
  simp only [SKGap.onsager,SKGap.overlap,SKGap.magnetization,scalarVariance]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  field_simp

lemma literal_stableMatrix_eq_hessian (hn : 0<n) (j : ℝ) (J : Interaction n)
    (z r : Fin n→ℝ) (a : ℝ) :
    stableMatrix j ((∑i,scalarVariance (z i))/(n:ℝ)) (n:ℝ)⁻¹
      (phiSqrt z r a) (toEuclideanCLM (𝕜:=ℝ) J)
      (WithLp.toLp 2 (fun i=>Real.tanh (z i)))=
      toEuclideanCLM (𝕜:=ℝ) (SKGap.fieldHessian j J z (fun i=>phi (z i) (r i) a)) := by
  rw [fieldHessian_matrix]
  simp only [map_sub,map_add,map_one,map_smul,map_mul,rank_toEuclideanCLM]
  rw [onsager_scalarVariance hn]
  simp only [stableMatrix,phiSqrt,div_eq_mul_inv]
  rfl

lemma literal_stableMatrix_quadratic (hn : 0<n) (j : ℝ) (J : Interaction n)
    (z r : Fin n→ℝ) (a : ℝ) (v : Euclid n) :
    inner ℝ v (stableMatrix j ((∑i,scalarVariance (z i))/(n:ℝ)) (n:ℝ)⁻¹
      (phiSqrt z r a) (toEuclideanCLM (𝕜:=ℝ) J)
      (WithLp.toLp 2 (fun i=>Real.tanh (z i))) v)=
      SKGap.quadraticForm (SKGap.fieldHessian j J z (fun i=>phi (z i) (r i) a)) v.ofLp := by
  rw [literal_stableMatrix_eq_hessian hn,Matrix.inner_toEuclideanCLM]
  simp only [dotProduct,mulVec,SKGap.quadraticForm,Finset.mul_sum]
  congr 1
  ext i
  congr 1
  ext k
  ring

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_StableRootInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace SKGap.ObservationBridge
open Matrix Real Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

lemma stable_hessian_coercive {n : ℕ} {j A ε c ρ : ℝ}
    {J : Matrix (Fin n) (Fin n) ℝ} {h y a : Field n}
    (hbad : ¬rootBad j A ε c ρ J h)
    (hy : vectorNorm (tapField j J h y) ≤ ρ*sqrt (n:ℝ))
    (ha : ∀ i,a i∈Icc 0 A) (hd : (∑ i,(a i-spinVariance y i)^2)≤ε^2*(n:ℝ)) :
    ∀ v : Field n,c*vectorSqNorm v ≤ quadraticForm (fieldHessian j J y a) v := by
  intro v
  let x : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 v
  let H := fieldHessian j J y a
  have hunit : ∀ z : EuclideanSpace ℝ (Fin n),‖z‖=1 → c < matrixQuad H z := by
    intro z hz
    exact lt_of_not_ge (fun hh=>hbad ⟨y,hy,a,ha,hd,z,hz,hh⟩)
  by_cases hx : x=0
  · have hv : v=0 := congrArg WithLp.ofLp hx
    simp [hv,vectorSqNorm,quadraticForm]
  · have hx0 : 0<‖x‖ := norm_pos_iff.mpr hx
    have hu : ‖(‖x‖⁻¹:ℝ) • x‖=1 := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hx0),inv_mul_cancel₀ hx0.ne']
    have hh := (hunit (‖x‖⁻¹ • x) hu).le
    rw [matrixQuad_smul] at hh
    have hmul := mul_le_mul_of_nonneg_left hh (sq_nonneg ‖x‖)
    have he : ‖x‖^2*((‖x‖⁻¹)^2*matrixQuad H x)=matrixQuad H x := by
      field_simp
    rw [he] at hmul
    have hn : ‖x‖^2=vectorSqNorm v := vectorNorm_sq v
    rw [hn,mul_comm] at hmul
    exact hmul

end SKGap.ObservationBridge

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_LiteralStableEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
namespace SKGapCutoff.Recipe
open SKGap SKGap.Stein Primary SKGap.ImplicitSystem Matrix SKGap.ObservationBridge
variable {n : ℕ}

lemma phi_hessian_stable (hn : 0<n) {j A ε c r₀ R ρ : ℝ}
    (hρ : 0≤ρ) (_ : 0≤ε) (hAR : Real.exp (R/2)≤A)
    (hsmall : (3*Real.exp (R/2)+2)*ρ≤ε)
    (J : Interaction n) (h z r : Fin n→ℝ) (a : ℝ)
    (hbad : ¬rootBad j A ε c r₀ J h)
    (htap : vectorNorm (SKGap.tapField j J h z) ≤ r₀*Real.sqrt (n:ℝ))
    (ha : |a|≤R) (haρ : |a|≤ρ)
    (hz : vectorNorm (z-r)≤ρ*Real.sqrt (n:ℝ)) :
    ∀v : Euclid n,c*‖v‖^2≤ inner ℝ v
      (stableMatrix j ((∑i,scalarVariance (z i))/(n:ℝ)) (n:ℝ)⁻¹
        (phiSqrt z r a) (toEuclideanCLM (𝕜:=ℝ) J)
        (WithLp.toLp 2 (fun i=>Real.tanh (z i))) v) := by
  obtain ⟨hb,hvar,hrest⟩:=implicit_coefficient_bounds z r a hn hρ ha haρ hz
  have hdiag : (∑i,(phi (z i) (r i) a-SKGap.spinVariance z i)^2)≤ε^2*(n:ℝ) := by
    have hv : vectorNorm (fun i=>phi (z i) (r i) a-SKGap.spinVariance z i)≤ε*Real.sqrt (n:ℝ) := by
      apply (show vectorNorm (fun i=>phi (z i) (r i) a-SKGap.spinVariance z i)≤
          (3*Real.exp (R/2)+2)*ρ*Real.sqrt (n:ℝ) by
        change SKGapCutoff.Recipe.vectorNorm ((fun i=>phi (z i) (r i) a)-(fun i=>scalarVariance (z i))) ≤ _ at hvar
        exact hvar).trans
      exact mul_le_mul_of_nonneg_right hsmall (Real.sqrt_nonneg _)
    have hs:=pow_le_pow_left₀ (vectorNorm_nonneg _) hv 2
    simpa only [vectorNorm_sq,mul_pow,Real.sq_sqrt (Nat.cast_nonneg n)] using hs
  have H:=stable_hessian_coercive hbad htap
    (fun i=>⟨(hb i).1.le,(hb i).2.trans hAR⟩) hdiag
  intro v
  rw [literal_stableMatrix_quadratic hn]
  have hvnorm : SKGap.vectorSqNorm v.ofLp=‖v‖^2 := by
    simpa only [SKGap.vectorNorm,WithLp.toLp_ofLp] using (SKGap.vectorNorm_sq v.ofLp).symm
  simpa only [hvnorm] using H v.ofLp

lemma literalStableAt_of_stableField (hn : 0<n) {j A ε c r₀ R ρ : ℝ}
    (hρ : 0≤ρ) (hε : 0≤ε) (hAR : Real.exp (R/2)≤A)
    (hsmall : (3*Real.exp (R/2)+2)*ρ≤ε)
    (J : Interaction n) (h r : Fin n→ℝ) (z m : VectorFields n) (a : Spin n→ℝ)
    (x : Spin n) (hbad : ¬rootBad j A ε c r₀ J h)
    (htap : vectorNorm (SKGap.tapField j J h (z x)) ≤ r₀*Real.sqrt (n:ℝ))
    (ha : |a x|≤R) (haρ : |a x|≤ρ)
    (hz : vectorNorm (z x-r)≤ρ*Real.sqrt (n:ℝ))
    (hm : vectorNorm (m x-(fun i=>Real.tanh (r i)))≤ρ*Real.sqrt (n:ℝ))
    (hmb : ∀i,|m x i|≤1) :
    LiteralStableAt J j z m a r R ρ c x :=
  ⟨ha,haρ,hz,hm,hmb,phi_hessian_stable hn hρ hε hAR hsmall J h (z x) r (a x)
    hbad htap ha haρ hz⟩

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix
namespace SKGapCutoff.Recipe
open SKGap Primary Static SKGap.ObservationBridge SKGap.Stein
variable {n : ℕ}

lemma square_average_difference (hn : 0<n) (v t : Fin n→ℝ)
    (hv : vectorNorm v≤Real.sqrt (n:ℝ)) (ht : vectorNorm t≤Real.sqrt (n:ℝ)) :
    |(∑i,(v i)^2)/(n:ℝ)-(∑i,(t i)^2)/(n:ℝ)| *Real.sqrt (n:ℝ)≤
      2*vectorNorm (v-t) := by
  have hnR : (0:ℝ)<n:=Nat.cast_pos.mpr hn
  have hd : (∑i,(v i)^2)-(∑i,(t i)^2)=∑i,(v i-t i)*(v i+t i) := by
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl;intros;ring
  have hp:=(SKGap.vector_dot_abs_le (v-t) (v+t)).trans
    (mul_le_mul_of_nonneg_left ((SKGap.vectorNorm_add_le v t).trans
      ((add_le_add hv ht).trans_eq (show Real.sqrt (n:ℝ)+Real.sqrt (n:ℝ)=2*Real.sqrt (n:ℝ) by ring))) (vectorNorm_nonneg _))
  rw [←sub_div,hd,abs_div,abs_of_pos hnR,div_mul_eq_mul_div]
  apply (div_le_iff₀ hnR).mpr
  have H:=mul_le_mul_of_nonneg_right hp (Real.sqrt_nonneg (n:ℝ))
  have he : (SKGap.vectorNorm (v-t)*(2*Real.sqrt (n:ℝ)))*Real.sqrt (n:ℝ)=2*SKGap.vectorNorm (v-t)*(n:ℝ) := by
    calc
      _ = 2*SKGap.vectorNorm (v-t)*(Real.sqrt (n:ℝ))^2 := by ring
      _ = _ := by rw [Real.sq_sqrt hnR.le]
  simpa only [Pi.add_apply,Pi.sub_apply,SKGap.vectorNorm,vectorNorm] using H.trans_eq he

lemma primary_auxiliary_small (hn : 0<n) {j D ρ : ℝ} (hj : 0≤j)
    (J : Interaction n) (h r : Fin n→ℝ) (k : ℕ) (x : Spin n)
    (hnear : vectorNorm (mag j J h k x-SKGap.magnetization r)≤D*ρ*Real.sqrt (n:ℝ)) :
    |j*(1-onsager j J h k x-SKGap.overlap r)|≤2*j*D*ρ := by
  have hs : 0<Real.sqrt (n:ℝ):=Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hv : vectorNorm (SKGap.magnetization r)≤Real.sqrt (n:ℝ) := by
    exact magnetization_norm r
  have havg : 1-onsager j J h k x-SKGap.overlap r=
      (∑i,(mag j J h k x i)^2)/(n:ℝ)-(∑i,(SKGap.magnetization r i)^2)/(n:ℝ) := by
    have hn0 : (n:ℝ)≠0:=ne_of_gt (Nat.cast_pos.mpr hn)
    simp only [Primary.onsager,siteMean,SKGap.overlap,Finset.sum_sub_distrib,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,
      sub_div,div_self hn0]
    ring
  have H:=(square_average_difference hn (mag j J h k x) (SKGap.magnetization r)
    (mag_vectorNorm j J h k x) hv).trans (mul_le_mul_of_nonneg_left hnear (by norm_num))
  rw [abs_mul,abs_of_nonneg hj,havg]
  apply (mul_le_mul_iff_left₀ hs).mp
  calc
    _ = j*(|((∑i,(mag j J h k x i)^2)/(n:ℝ))-(∑i,(SKGap.magnetization r i)^2)/(n:ℝ)| *Real.sqrt (n:ℝ)) := by ring
    _ ≤ j*(2*(D*ρ*Real.sqrt (n:ℝ))) := mul_le_mul_of_nonneg_left H hj
    _ = _ := by ring

theorem stable_primary_buffer (hn : 0<n) {j K A ε c r₀ R ρ : ℝ}
    (hj : 0≤j) (hK : 0≤K) (hA : 1≤A) (hc : 0 < c) (hr₀ : 0 < r₀) (hρ : 0≤ρ)
    (hε : 0≤ε) (hAR : Real.exp (R/2)≤A)
    (hbuffer : (K+4*j)*ρ < r₀)
    (hR : (1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*ρ≤R)
    (hsmall : (3*Real.exp (R/2)+2)*((1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*ρ)≤ε)
    (J : Interaction n) (hJ : J.IsSymm) (h : Fin n→ℝ)
    (hop : ∀v,vectorNorm (J.mulVec v)≤K*vectorNorm v)
    (hbad : ¬rootBad j A ε c r₀ J h) :
    ∃r:Fin n→ℝ,SKGap.tapField j J h r=0 ∧ (∀y,SKGap.tapField j J h y=0→y=r) ∧
      ∀k x,
      vectorNorm (Primary.residual j J h k x)≤ρ*Real.sqrt (n:ℝ)→
      vectorNorm (Primary.residual j J h (k+1) x)≤ρ*Real.sqrt (n:ℝ)→
      LiteralStableAt J j (fld j J h (k+1)) (mag j J h (k+1))
        (fun v=>j*(1-onsager j J h (k+1) v-SKGap.overlap r)) r R
        ((1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*ρ) c x := by
  let C:=(1+(K+3*j)/c)*(K+4*j)
  let D:=(1+2*j)*(1+C)
  have hC : 0≤C:=by dsimp [C];positivity
  have hD : 0≤D:=by dsimp [D];positivity
  have hCD : C≤D:=by dsimp [D];nlinarith
  have h1CD : 1+C≤D:=by dsimp [D];nlinarith
  have h2CD : 2*j*(1+C)≤D:=by dsimp [D];nlinarith
  have hs : 0<Real.sqrt (n:ℝ):=Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hH : ∀y,vectorNorm (SKGap.tapField j J h y) ≤ r₀*Real.sqrt (n:ℝ)→∀v,
      c*SKGap.vectorSqNorm v≤SKGap.quadraticForm (SKGap.fieldHessian j J y (SKGap.spinVariance y)) v := by
    intro y hy
    apply stable_hessian_coercive hbad hy
    · intro i
      exact ⟨(SKGap.spinVariance_pos y i).le,(SKGap.spinVariance_le_one y i).trans hA⟩
    · simp only [sub_self,zero_pow (by decide : 2≠0),Finset.sum_const_zero]
      positivity
  obtain ⟨r,hr,hu,hd⟩:=SKGap.tap_root_and_distance hn hj hK hc (mul_pos hr₀ hs) hJ h hop hH
  refine ⟨r,hr,hu,?_⟩
  intro k x h0 h1
  have htap : vectorNorm (SKGap.tapField j J h (fld j J h (k+1) x))≤(K+4*j)*ρ*Real.sqrt (n:ℝ) :=
    (primary_tap_norm hn hj hK J h k x hop).trans
      ((add_le_add (mul_le_mul_of_nonneg_left h0 hj)
        (mul_le_mul_of_nonneg_left h1 (by positivity))).trans_eq (by ring))
  have htap' := htap.trans_lt (mul_lt_mul_of_pos_right hbuffer hs)
  have hz : vectorNorm (fld j J h (k+1) x-r)≤C*ρ*Real.sqrt (n:ℝ) :=
    (hd _ htap').trans ((mul_le_mul_of_nonneg_left htap (by positivity)).trans_eq (by dsimp [C];ring))
  have ht : vectorNorm (mag j J h (k+2) x-SKGap.magnetization r)≤C*ρ*Real.sqrt (n:ℝ) :=
    (magnetization_vector_lipschitz (fld j J h (k+1) x) r).trans hz
  have hm : vectorNorm (mag j J h (k+1) x-SKGap.magnetization r)≤(1+C)*ρ*Real.sqrt (n:ℝ) := by
    have he : mag j J h (k+1) x-SKGap.magnetization r=
        Primary.residual j J h (k+1) x+(mag j J h (k+2) x-SKGap.magnetization r) := by
      ext i;simp only [Primary.residual,Pi.sub_apply,Pi.add_apply];ring
    rw [he]
    exact (SKGap.vectorNorm_add_le _ _).trans ((add_le_add h1 ht).trans_eq (by ring))
  have ha := (primary_auxiliary_small hn hj J h r (k+1) x hm).trans
    (mul_le_mul_of_nonneg_right h2CD hρ)
  apply literalStableAt_of_stableField hn (mul_nonneg hD hρ) hε hAR hsmall J h r _ _ _ x hbad
    htap'.le (ha.trans hR) ha
  · exact hz.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCD hρ) hs.le)
  · exact hm.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1CD hρ) hs.le)
  · intro i
    exact primaryState_mag_bounded j J h (k+1) x i

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_BufferedFlip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary SKGap.Stein
variable {n : ℕ}

lemma auxiliary_derivative (j q : ℝ) (b : Spin n→ℝ) (x : Spin n) :
    derivativeVector (fun y=>j*(1-b y-q)) x= -j • derivativeVector b x := by
  ext i
  simp only [derivativeVector,WithLp.ofLp_toLp,PiLp.smul_apply,halfDiff]
  ring

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_PhiResponse
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace SKGap.Stein
open KernelExpr

lemma phiR_hasDerivAt (z r a : ℝ) : HasDerivAt (fun r=>phi z r a) (phiR z r a) r := by
  simpa only [eval,moment_base,phiR] using hasDerivAt_r (atom 0 0 false) z r a
lemma phiZR_commute (z r a : ℝ) :
    eval (dr (dz (atom 0 0 false))) z r a=phiRZ z r a := by
  simp only [phiRZ,dz,dr,eval]
  ring
lemma phiZ_kernel (z r a : ℝ) : phiZ z r a=eval (dz (atom 0 0 false)) z r a := by
  exact (phi_hasDerivAt z r a).unique (by simpa only [eval,moment_base] using hasDerivAt_z (atom 0 0 false) z r a)
lemma phiZ_hasDerivAt_r (z r a : ℝ) : HasDerivAt (fun r=>phiZ z r a) (phiRZ z r a) r := by
  simpa only [phiZ_kernel,phiZR_commute] using hasDerivAt_r (dz (atom 0 0 false)) z r a

theorem phiR_stein (z r a : ℝ) :
    (z-r-a*Real.tanh z)*phiR z r a-a*phiRZ z r a=phi z r a-SKGapCutoff.scalarVariance r := by
  have hc : HasDerivAt (fun r=>z-r-a*Real.tanh z) (-1) r := by
    convert! ((hasDerivAt_const r z).sub (hasDerivAt_id r)).sub_const (a*Real.tanh z) using 1
    all_goals try with_reducible_and_instances rfl
    simp
  have hleft := (hc.mul (phiR_hasDerivAt z r a)).sub ((phiZ_hasDerivAt_r z r a).const_mul a)
  have hright : HasDerivAt (fun r=>Real.tanh z-Real.tanh r) (-SKGapCutoff.scalarVariance r) r := by
    convert! (hasDerivAt_const r (Real.tanh z)).sub (SKGapCutoff.tanh_hasDerivAt r) using 1
    all_goals try with_reducible_and_instances rfl
    simp
  have hh : (fun r=>(z-r-a*Real.tanh z)*phi z r a-a*phiZ z r a)=
      (fun r=>Real.tanh z-Real.tanh r) := funext fun r=>phi_stein z r a
  change HasDerivAt (fun r=>(z-r-a*Real.tanh z)*phi z r a-a*phiZ z r a) _ r at hleft
  rw [hh] at hleft
  have he:=hleft.unique hright
  linarith

end SKGap.Stein

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_ImplicitComparison
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
open Matrix SKGap.Stein
variable {n : ℕ}

lemma implicit_phiR_source (z r : Fin n→ℝ) (a : ℝ) :
    (∑i,((z i-r i-a*Real.tanh (z i))*(phiR (z i) (r i) a/Real.sqrt (n:ℝ))-
      a*(phiRZ (z i) (r i) a/Real.sqrt (n:ℝ))))=
      (∑i,(phi (z i) (r i) a-scalarVariance (r i)))/Real.sqrt (n:ℝ) := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl;intro i _
  linear_combination (phiR_stein (z i) (r i) a)/Real.sqrt (n:ℝ)

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LocalUniformWeak
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
open Primary Recipe
universe u
variable {Ω : Type u} {n : Ω→ℕ}

variable {E : ∀a,Set (Spin (n a))}

lemma LocalUniformWeak.congr {P F F' : ∀a,Observables (n a)} (h : LocalUniformWeak E P F)
    (he : ∀a x,F a x=F' a x) : LocalUniformWeak E P F' := by
  have : F=F' := funext fun a=>funext (he a)
  rwa [←this]

end SKGapCutoff.Static

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LiteralWeak
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
open Primary Recipe
variable {n : ℕ}

lemma tested_susceptibility_absorption (P C L M : Observables n)
    (hP : ∀x,0≤P x) {K D : ℝ} (hK : 0≤K) (hD : 0≤D)
    (hM : ∀x,C x≠0→|M x|≤|L x|/2)
    (hweak : |∑x,P x*((C x)^2*L x)*(L x+M x)|≤K*starNorm P (fun x=>(C x)^2*L x))
    (hstar : starSquared P (fun x=>(C x)^2*L x)≤(∑x,P x*(C x*L x)^2)+D) :
    (∑x,P x*(C x*L x)^2)≤4*K^2+D := by
  let S:=∑x,P x*(C x*L x)^2
  have hS : 0≤S := Finset.sum_nonneg fun x _=>mul_nonneg (hP x) (sq_nonneg _)
  have hsum : S/2≤∑x,P x*((C x)^2*L x)*(L x+M x) := by
    rw [show S/2=∑x,P x*(C x*L x)^2/2 by simp only [S,Finset.sum_div]]
    apply Finset.sum_le_sum
    intro x _
    by_cases hx:C x=0
    · simp [hx]
    have habs : |L x*M x|≤(L x)^2/2 := by
      rw [abs_mul]
      have H:=mul_le_mul_of_nonneg_left (hM x hx) (abs_nonneg (L x))
      simpa only [←mul_div_assoc,←sq,sq_abs] using H
    have hh := (neg_abs_le (L x*M x)).trans' (neg_le_neg habs)
    have hh' := mul_le_mul_of_nonneg_left hh (mul_nonneg (hP x) (sq_nonneg (C x)))
    nlinarith only [hh']
  have htest : S/2≤K*Real.sqrt (S+D) :=
    (hsum.trans (le_abs_self _)).trans (hweak.trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hstar) hK))
  have hsqrt : (Real.sqrt (S+D))^2=S+D := Real.sq_sqrt (add_nonneg hS hD)
  have H:=sq_nonneg (Real.sqrt (S+D)-2*K)
  change S≤4*K^2+D
  nlinarith only [htest,H,hsqrt]

end SKGapCutoff.Static

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_SusceptibilityMiddle
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

lemma literal_middle_error (J : Interaction n) (j : ℝ) (f : KernelExpr)
    (z m w y : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (x : Spin n)
    (hn : 0<n) {R ρ δ L : ℝ} (hδ : 0<δ) (hρ : 0≤ρ)
    (hsmall : ρ≤δ/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1)))
    (hJ : SKGap.opNorm J≤L) (he : vectorNorm e≤1)
    (H : LiteralStableAt J j z m a r R ρ δ x)
    (h : LiteralEquations J j f z m w y a c r e x) :
    |j*(1-SKGap.overlap r-siteMean (fun v i=>phi (z v i) (r i) (a v)) x)*
      (∑i,(Real.tanh (z x i)-Real.tanh (r i))*w x i)|≤
      (|j| *|literalSizeBudget j δ R L f|)*ρ*|literalSusceptibility z a r x| := by
  have hh:=literal_initial_size J j f z m w y a c r e x hn hδ hρ hsmall hJ he H h
  have hw : vectorNorm (w x)≤|literalSizeBudget j δ R L f| := by
    have hrest : 0 ≤ vectorNorm (y x) + Real.sqrt (n:ℝ)*|c x| := by
      exact add_nonneg (vectorNorm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
    exact (le_trans (by linarith) hh).trans (le_abs_self _)
  have hp : vectorNorm (fun i=>Real.tanh (z x i)-Real.tanh (r i))≤ρ*Real.sqrt (n:ℝ) :=
    (magnetization_vector_lipschitz (z x) r).trans H.z_near
  have hd : |∑i,(Real.tanh (z x i)-Real.tanh (r i))*w x i|≤
      (ρ*Real.sqrt (n:ℝ))*|literalSizeBudget j δ R L f| :=
    (SKGap.vector_dot_abs_le _ _).trans (mul_le_mul hp hw (vectorNorm_nonneg _) (by positivity))
  rw [abs_mul,abs_mul]
  apply (mul_le_mul_of_nonneg_left hd (mul_nonneg (abs_nonneg _) (abs_nonneg _))).trans_eq
  rw [literalSusceptibility,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _),abs_sub_comm]
  ring

lemma primary_auxiliary_global (hn : 0<n) (j : ℝ) (J : Interaction n) (h r : Fin n→ℝ)
    (k : ℕ) (x : Spin n) :
    |j*(1-Primary.onsager j J h k x-SKGap.overlap r)|≤|j| := by
  have hb:=onsager_bounds j J h k x
  have hq:=SKGap.overlap_nonneg r
  have hq1:=(SKGap.overlap_lt_one hn r).le
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_le.mpr ⟨by linarith,by linarith⟩)

lemma literalSusceptibility_global_size (hn : 0<n) (j : ℝ) (J : Interaction n)
    (h r : Fin n→ℝ) (k : ℕ) (x : Spin n) :
    |literalSusceptibility (fld j J h k)
      (fun v=>j*(1-Primary.onsager j J h k v-SKGap.overlap r)) r x|≤
      (Real.exp (|j|/2)+1)*Real.sqrt (n:ℝ) := by
  have ha:=primary_auxiliary_global hn j J h r k x
  have hphi : |siteMean (fun v i=>phi (fld j J h k v i) (r i)
      (j*(1-Primary.onsager j J h k v-SKGap.overlap r))) x|≤Real.exp (|j|/2) := by
    apply coefficient_mean_value _ _ (Real.exp_pos _).le
    intro i
    rw [abs_of_pos (phi_pos ..)]
    exact (phi_le_exp ..).trans (Real.exp_le_exp.mpr (by linarith))
  have hq : |1-SKGap.overlap r|≤1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (SKGap.overlap_lt_one hn r).le)]
    linarith [SKGap.overlap_nonneg r]
  have H:=(abs_sub _ _).trans (add_le_add hphi hq)
  rw [literalSusceptibility,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (mul_le_mul_of_nonneg_left H (Real.sqrt_nonneg _)).trans_eq (by ring)

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary SKGap.Stein
variable {n : ℕ}

lemma parameter_fourth_bound (hn : 0<n) (a : Spin n→ℝ) (x : Spin n) {D : ℝ}
    (hD : (n:ℝ)*‖derivativeVector a x‖^2≤D^2) :
    (∑_:Fin n,∑k:Fin n,(halfDiff k a x)^4)≤D^4 := by
  have hn1 : (1:ℝ)≤n:=by exact_mod_cast hn
  have hh:=Finset.sum_sq_le_sq_sum_of_nonneg (s:=Finset.univ)
    (f:=fun k:Fin n=>(halfDiff k a x)^2) (fun _ _=>sq_nonneg _)
  have he : (∑k:Fin n,(halfDiff k a x)^2)=‖derivativeVector a x‖^2 := by
    simp only [EuclideanSpace.real_norm_sq_eq,derivativeVector]
  rw [he] at hh
  have hp:=mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg n : (0:ℝ)≤n)
  have hq:=pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg _)) hD 2
  have hs:=mul_nonneg (sub_nonneg.mpr hn1) (sq_nonneg ((n:ℝ)*‖derivativeVector a x‖^2))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,←pow_mul] at hp ⊢
  have ht:=mul_le_mul_of_nonneg_left hn1 (pow_nonneg (norm_nonneg (derivativeVector a x)) 4)
  have ht':=mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg n : (0:ℝ)≤n)
  norm_num only at hp
  nlinarith

lemma one_coefficient_derivative_bound (hn : 0<n) (z : VectorFields n)
    (a : Spin n→ℝ) (x : Spin n) (F : Fin n→Args (ι:=Unit) (κ:=Unit)→ℝ)
    (F' : Fin n→Args (ι:=Unit) (κ:=Unit)→Args (ι:=Unit) (κ:=Unit)→L[ℝ]ℝ)
    {L C D : ℝ} (hC : 0≤C) (hD : 0≤D)
    (H : SegmentRegular (fun _:Unit=>z) (fun _:Unit=>a) F F' x L)
    (hz : ShapeBound (derivativeMatrix z x) C)
    (ha : (n:ℝ)*‖derivativeVector a x‖^2≤D^2) :
    SKGap.opNorm (derivativeMatrix (coefficient (fun _:Unit=>z) (fun _:Unit=>a) F) x)≤
      L*C+L*D+12*L*(C^2+D^2) := by
  have hL:=H.nonneg
  let T:Fin n→ℝ:=localPartial (fun _:Unit=>z) (fun _:Unit=>a) F' (.inl ()) x
  let U:Fin n→ℝ:=localPartial (fun _:Unit=>z) (fun _:Unit=>a) F' (.inr ()) x
  let V:Interaction n:=Matrix.of (fun i k=>(1:ℝ)*halfDiff k a x)
  let R:Interaction n:=Matrix.of (taylorError (fun _:Unit=>z) (fun _:Unit=>a) F F' x)
  have hT : SKGap.opNorm (Matrix.diagonal T)≤L :=
    SKGap.opNorm_diagonal_le H.nonneg (fun i=>H.partial_bound i (.inl ()))
  have hU : SKGap.opNorm (Matrix.diagonal U)≤L :=
    SKGap.opNorm_diagonal_le H.nonneg (fun i=>H.partial_bound i (.inr ()))
  have hV : ‖V‖≤D := outer_frobenius_bound (fun _=>by norm_num) hD ha
  have hRpoint (i k:Fin n) : |R i k|≤6*L*((derivativeMatrix z x i k)^2+(halfDiff k a x)^2) := by
    have hh:=taylor_error_bound (fun _:Unit=>z) (fun _:Unit=>a) F F' x i k H.nonneg
      (abs_nonneg (derivativeMatrix z x i k)) (abs_nonneg (halfDiff k a x))
      (by simpa only [Fintype.sum_unique] using local_argument_bound (fun _:Unit=>z) (fun _:Unit=>a) x i k)
      (H.deriv i k) (H.lip i k)
    change |R i k|≤_ at hh
    simp only [sq_abs] at hh
    have hs:=mul_nonneg H.nonneg (sq_nonneg (|derivativeMatrix z x i k|-|halfDiff k a x|))
    simp only [sub_sq,sq_abs] at hs
    nlinarith
  have hR : ‖R‖≤12*L*(C^2+D^2) := by
    have hs : ‖R‖^2≤72*L^2*(2*C^4+D^4) := by
      rw [SKGap.frobenius_sq]
      calc
        _≤∑i,∑k,72*L^2*((derivativeMatrix z x i k)^4+(halfDiff k a x)^4) := by
          apply Finset.sum_le_sum;intro i _
          apply Finset.sum_le_sum;intro k _
          have h:=pow_le_pow_left₀ (abs_nonneg (R i k)) (hRpoint i k) 2
          have ht:=mul_nonneg (sq_nonneg L) (sq_nonneg ((derivativeMatrix z x i k)^2-(halfDiff k a x)^2))
          nlinarith [sq_abs (R i k)]
        _=72*L^2*((∑i,∑k,(derivativeMatrix z x i k)^4)+(∑i,∑k,(halfDiff k a x)^4)) := by
          simp only [mul_add,Finset.mul_sum,Finset.sum_add_distrib]
        _≤72*L^2*(2*C^4+D^4) := mul_le_mul_of_nonneg_left
          (add_le_add (fourth_sum_le hC hz) (parameter_fourth_bound hn a x ha)) (by positivity)
    apply nonneg_le_nonneg_of_sq_le_sq (by positivity)
    simp only [←sq]
    apply hs.trans
    nlinarith [mul_nonneg (sq_nonneg L) (mul_nonneg (sq_nonneg C) (sq_nonneg D)),
      mul_nonneg (sq_nonneg L) (pow_nonneg hD 4)]
  have he : derivativeMatrix (coefficient (fun _:Unit=>z) (fun _:Unit=>a) F) x=
      Matrix.diagonal T*derivativeMatrix z x+Matrix.diagonal U*V+R := by
    ext i k
    simp only [Matrix.add_apply,Matrix.diagonal_mul,R,V,Matrix.of_apply,T,U,taylorError,localPartial]
    rw [coefficient_chain]
    simp only [Fintype.sum_unique]
    ring
  rw [he]
  have hmain : SKGap.opNorm (Matrix.diagonal T*derivativeMatrix z x)≤L*C :=
    (SKGap.opNorm_mul _ _).trans (mul_le_mul hT hz.1 (norm_nonneg _) H.nonneg)
  have hparam : SKGap.opNorm (Matrix.diagonal U*V)≤L*D :=
    (opNorm_le_frobenius _).trans ((SKGap.frobenius_mul_le_opNorm _ _).trans
      (mul_le_mul hU hV (norm_nonneg _) H.nonneg))
  exact (opNorm_add _ _).trans (add_le_add
    ((opNorm_add _ _).trans (add_le_add hmain hparam)) ((opNorm_le_frobenius _).trans hR))

end SKGapCutoff.Recipe

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary SKGap.Stein

theorem literalSusceptibility_global_derivative (j K B : ℝ) (hK : 0≤K) (hB : 0≤B) (k : ℕ) :
    ∃S≥0,∀n:ℕ,0<n→∀(J:Interaction n) (h r:Fin n→ℝ),SKGap.opNorm J≤K→
      (∀x l,l<k+3→ShapeBound (formalField j J h x l) B)→∀x:Spin n,
      ‖derivativeVector (literalSusceptibility (fld j J h (k+1))
        (fun v=>j*(1-onsager j J h (k+1) v-SKGap.overlap r)) r) x‖≤S := by
  let f:=KernelExpr.atom 0 0 false
  let L:=f.dBudget |j|+f.ddBudget |j|
  let C:=localPrimaryBudget j K B (k+3)
  let D := |j| * averageBudget j K B k
  have hL : 0≤L:=add_nonneg (f.dBudget_nonneg _) (f.ddBudget_nonneg _)
  have hC : 0≤C:=localPrimaryBudget_nonneg hK hB _
  have hD : 0≤D:=mul_nonneg (abs_nonneg _) (averageBudget_nonneg hK hB _)
  refine ⟨L*C+L*D+12*L*(C^2+D^2),by positivity,?_⟩
  intro n hn J h r hop hformal x
  let z:=fld j J h (k+1)
  let a:=fun v:Spin n=>j*(1-onsager j J h (k+1) v-SKGap.overlap r)
  let F:=fun i:Fin n=>fun u:Args (ι:=Unit) (κ:=Unit)=>eval3 f.eval (phiSelect () () u+(0,(r i,0)))
  let F':=fun i:Fin n=>fun u:Args (ι:=Unit) (κ:=Unit)=>
    (f.gradient (phiSelect () () u+(0,(r i,0)))).comp (phiSelect () ())
  have hreg : SegmentRegular (fun _:Unit=>z) (fun _:Unit=>a) F F' x L :=
    fixed_root_kernel_regular f (fun _:Unit=>z) (fun _:Unit=>a) x () () r |j|
      (primary_auxiliary_global hn j J h r (k+1) x)
      (fun v=>primary_auxiliary_global hn j J h r (k+1) (flip x v))
  have hz : ShapeBound (derivativeMatrix z x) C :=
    ((primary_differentiation J h x hn hK hB hop (k+1)
      (fun l hl=>hformal x l (by omega))).2.2.2).mono
      (localPrimaryBudget_bounds hK hB (k+3) ⟨k+1,by omega⟩).1
  have hm : (n:ℝ)*‖derivativeVector (onsager j J h (k+1)) x‖^2≤(averageBudget j K B k)^2 := by
    simpa only [onsager,mag,primaryState,scalarVariance,averageBudget] using
      primary_average_differentiation J h x hn hK hB hop k (fun l hl=>hformal x l (by omega))
  have ha : (n:ℝ)*‖derivativeVector a x‖^2≤D^2 := by
    dsimp only [a]
    rw [auxiliary_derivative,norm_smul,Real.norm_eq_abs,abs_neg,mul_pow]
    calc
      _=|j|^2*((n:ℝ)*‖derivativeVector (onsager j J h (k+1)) x‖^2) := by ring
      _≤|j|^2*(averageBudget j K B k)^2 := mul_le_mul_of_nonneg_left hm (sq_nonneg _)
      _=D^2 := by dsimp [D];ring
  have he : coefficient (fun _:Unit=>z) (fun _:Unit=>a) F=(fun v i=>phi (z v i) (r i) (a v)) := by
    funext v i
    simp only [coefficient,F,eval3,phiSelect_apply,Prod.fst_add,Prod.snd_add,
      localArgs,Sum.elim_inl,Sum.elim_inr,zero_add,add_zero,f,KernelExpr.eval,moment_base]
  have hmat:=one_coefficient_derivative_bound hn z a x F F' hC hD hreg hz ha
  rw [he] at hmat
  have hav:=siteMean_derivative_square_bound hn hmat
  have hed : derivativeVector (literalSusceptibility z a r) x=
      Real.sqrt (n:ℝ) • derivativeVector (siteMean (fun v i=>phi (z v i) (r i) (a v))) x := by
    ext i
    simp only [derivativeVector,WithLp.ofLp_toLp,PiLp.smul_apply,literalSusceptibility,halfDiff]
    ring
  change ‖derivativeVector (literalSusceptibility z a r) x‖≤_
  rw [hed,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  apply nonneg_le_nonneg_of_sq_le_sq (by positivity)
  simpa only [←sq,mul_pow,Real.sq_sqrt (Nat.cast_nonneg n)] using hav

end SKGapCutoff.Recipe

end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_SusceptibilityTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
open Primary Recipe
variable {n : ℕ}

lemma cutoff_square_derivative (C : Observables n) {s A : ℝ} (hs : 0 < s) (hA : 0≤A)
    (hc : ∀x,|C x|≤1) (hd : ∀x,‖derivativeVector C x‖≤A/s) :
    ∀x,∑i,(halfDiff i (fun y=>(C y)^2) x)^2≤(4*A/s)^2 := by
  intro x
  have H:=derivativeVector_mul_bound C C x hc hc (div_nonneg hA hs.le) (div_nonneg hA hs.le) (hd x) (hd x)
  have H' : ‖derivativeVector (fun y=>(C y)^2) x‖≤4*A/s := by
    simpa only [←sq] using H.trans_eq (show 2*(A/s+A/s)=4*A/s by ring)
  simpa only [norm_derivativeVector_sq] using pow_le_pow_left₀ (norm_nonneg _) H' 2

lemma cutoff_susceptibility_star (P C L : Observables n) (hP : ∀x,0≤P x)
    (hp : ∑x,P x=1) {s A B D : ℝ} (hs : 0 < s) (hA : 0≤A) (hB : 0≤B) (hD : 0≤D)
    (hc : ∀x,|C x|≤1) (hdC : ∀x,‖derivativeVector C x‖≤A/s)
    (hL : ∀x,|L x|≤B*s) (hdL : ∀x,‖derivativeVector L x‖≤D) :
    starSquared P (fun x=>(C x)^2*L x)≤
      (∑x,P x*(C x*L x)^2)+(32*A^2*B^2+2*D^2) := by
  have hc2 : ∀x,|(C x)^2|≤1 := by
    intro x
    simpa only [sq_abs,abs_sq,one_pow] using pow_le_pow_left₀ (abs_nonneg _) (hc x) 2
  have hdC2:=cutoff_square_derivative C hs hA hc hdC
  have hdL2 : ∀x,∑i,(halfDiff i L x)^2≤D^2 := by
    intro x
    simpa only [norm_derivativeVector_sq] using pow_le_pow_left₀ (norm_nonneg _) (hdL x) 2
  have hg:= (scalar_product_bounds (fun x=>(C x)^2) L (by norm_num) (by positivity)
    (mul_nonneg hB hs.le) hD hc2 hdC2 hL hdL2).2
  have he : varianceEnergy P (fun x=>(C x)^2*L x)≤32*A^2*B^2+2*D^2 := by
    have H:=varianceEnergy_gradient_bound P hP hp (fun x=>(C x)^2*L x) hg
    rw [Real.sq_sqrt (by positivity)] at H
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
    ring
  have hv : (∑x,P x*((C x)^2*L x)^2)≤∑x,P x*(C x*L x)^2 := by
    apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_left _ (hP x)
    have H : (C x)^2≤1 := by
      simpa only [sq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg _) (hc x) 2
    have H':=mul_le_mul_of_nonneg_right H (sq_nonneg (C x*L x))
    nlinarith only [H']
  exact add_le_add hv he

end SKGapCutoff.Static

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static

theorem literalSusceptibility_cutoff_test (j K B ρ : ℝ) (hK : 0≤K) (hB : 0≤B)
    (hρ : 0<ρ) (k : ℕ) :
    ∃D≥0,∀n:ℕ,0<n→∀(J:Interaction n) (h r:Fin n→ℝ) (P:Observables n),
      (∀x,0≤P x)→(∑x,P x=1)→SKGap.opNorm J≤K→
      (∀x l,l<k+3→ShapeBound (formalField j J h x l) B)→
      let C:=residualCutoff ρ j J h k
      let L:=literalSusceptibility (fld j J h (k+1))
        (fun v=>j*(1-onsager j J h (k+1) v-SKGap.overlap r)) r
      starSquared P (fun x=>(C x)^2*L x)≤(∑x,P x*(C x*L x)^2)+D := by
  obtain ⟨S,hS,hdL⟩:=literalSusceptibility_global_derivative j K B hK hB k
  obtain ⟨Q,hQ⟩:=residualScalarCutoff_lipschitz
  let U:=residualDerivativeBudget j K B k
  let V:=residualDerivativeBudget j K B (k+1)
  let A:=2*(Q:ℝ)/ρ^2*((4*U+2*U^2)+(4*V+2*V^2))
  have hU : 0≤U:=residualDerivativeBudget_nonneg hK hB _
  have hV : 0≤V:=residualDerivativeBudget_nonneg hK hB _
  have hA : 0≤A:=by dsimp [A];positivity
  refine ⟨32*A^2*(Real.exp (|j|/2)+1)^2+2*S^2,by positivity,?_⟩
  intro n hn J h r P hP hp hop hformal
  dsimp only
  apply cutoff_susceptibility_star P _ _ hP hp (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))
    hA (by positivity) hS
  · intro x
    rw [abs_of_nonneg (residualCutoff_bounds ρ j J h k x).1]
    exact (residualCutoff_bounds ρ j J h k x).2
  · intro x
    exact residualCutoff_gradient hn hρ hQ J h k x hU hV
      (residual_derivative_bound hn hK hB J h hop k (fun v l hl=>hformal v l (by omega)) x)
      (residual_derivative_bound hn hK hB J h hop (k+1) (fun v l hl=>hformal v l (by omega)) x)
  · exact literalSusceptibility_global_size hn j J h r (k+1)
  · exact hdL n hn J h r hop hformal

end SKGapCutoff.Recipe

end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LiteralValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary SKGap.Stein
variable {n : ℕ}

lemma literal_source_phiR (hn : 0<n) (j : ℝ) (J : Interaction n) (h r : Fin n→ℝ)
    (k : ℕ) (x : Spin n) :
    literalSourceBracket j J h r (fun _=>1/Real.sqrt (n:ℝ)) k
      (KernelExpr.dr (KernelExpr.atom 0 0 false)) x =
    literalSusceptibility (fld j J h (k+1))
      (fun v=>j*(1-onsager j J h (k+1) v-SKGap.overlap r)) r x := by
  have hh:=implicit_phiR_source (fld j J h (k+1) x) r
    (j*(1-onsager j J h (k+1) x-SKGap.overlap r))
  have hh' : literalSourceBracket j J h r (fun _=>1/Real.sqrt (n:ℝ)) k
      (KernelExpr.dr (KernelExpr.atom 0 0 false)) x=
      (∑i,(phi (fld j J h (k+1) x i) (r i)
        (j*(1-onsager j J h (k+1) x-SKGap.overlap r))-SKGapCutoff.scalarVariance (r i)))/Real.sqrt (n:ℝ) := by
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [literalSourceBracket,phiR,phiRZ]
    ring
  rw [hh']
  have hn0 : (n:ℝ)≠0:=ne_of_gt (Nat.cast_pos.mpr hn)
  have hs0 : Real.sqrt (n:ℝ)≠0:=ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))
  have hs : (Real.sqrt (n:ℝ))^2=(n:ℝ):=Real.sq_sqrt (Nat.cast_nonneg _)
  simp only [literalSusceptibility,siteMean,SKGap.overlap,SKGap.magnetization,
    SKGapCutoff.scalarVariance,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,mul_one]
  field_simp
  rw [hs]
  ring

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary Static
universe u

theorem buffered_root_susceptibility_bound_oai {j K B Aroot ε c r₀ R ρ : ℝ}
    (hj : 0≤j) (hK : 0≤K) (hB : 0≤B) (hA : 1≤Aroot) (hc : 0 < c)
    (hr₀ : 0 < r₀) (hρ : 0<ρ) (hε : 0≤ε) (hAR : Real.exp (R/2)≤Aroot)
    (hbuffer : (K+4*j)*(2*ρ) < r₀)
    (hR : (1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ)≤R)
    (hsmall : (3*Real.exp (R/2)+2)*((1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ))≤ε)
    (himplicit : (1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ)≤
      c/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1)))
    (habsorb : (|j| *|literalSizeBudget j c R K
        (KernelExpr.dr (KernelExpr.atom 0 0 false))|)*
      ((1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ))≤(1:ℝ)/2)
    (k : ℕ) :
    ∃A≥1,∀W C : ℝ,0≤W→0≤C→∀(Ω : Type u) (n : Ω→ℕ)
      (J : ∀b,Interaction (n b)) (h : ∀b,Fin (n b)→ℝ) (P : ∀b,Observables (n b)),
      (∀b,0<n b)→(∀b,(J b).IsSymm)→
      (∀b,StartedMatrixEvent j K (Real.exp (R/2)) A (c/2) B W C (k+3) (2+2*(k+1)) (J b))→
      (∀b,¬SKGap.rootBad j Aroot ε c r₀ (J b) (h b))→
      (∀b,4*(residualDerivativeBudget j K B k+residualDerivativeBudget j K B (k+1))≤ρ*Real.sqrt (n b:ℝ))→
      (∀b x,0≤P b x)→(∀b,∑x,P b x=1)→
      (∀b x i,conditionalMean (P b) x i=mag j (J b) (h b) 1 x i)→
      ∃r : ∀b,Fin (n b)→ℝ,(∀b,SKGap.tapField j (J b) (h b) (r b)=0 ∧
          ∀v,SKGap.tapField j (J b) (h b) v=0→v=r b) ∧
      ∃D≥0,∀b,
        ∑x,P b x*(residualCutoff ρ j (J b) (h b) k x*
          literalSusceptibility (fld j (J b) (h b) (k+1))
            (fun v=>j*(1-onsager j (J b) (h b) (k+1) v-SKGap.overlap (r b))) (r b) x)^2≤D := by
  let f:=KernelExpr.dr (KernelExpr.atom 0 0 false)
  let η:=(1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ)
  have hη : 0≤η:=by dsimp [η];positivity
  obtain ⟨A,hA',hh⟩:=buffered_root_source_weak hj hK hB hA hc hr₀ hρ hε
    hAR hbuffer hR hsmall himplicit k f
  refine ⟨A,hA',?_⟩
  intro W C hW hC Ω n J h P hn hJ hevent hbad hdim hP hp hm
  let e:=fun b=>fun _ : Fin (n b)=>1/Real.sqrt (n b:ℝ)
  have he : ∀b,vectorNorm (e b)≤1 := by
    intro b
    dsimp [e]
    rw [vectorNorm_const,abs_of_nonneg (by positivity)]
    have hs : Real.sqrt (n b:ℝ)≠0:=ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (hn b)))
    exact le_of_eq (by field_simp)
  obtain ⟨r,hr,w,y,c₀,heq,hweak⟩:=hh W C hW hC Ω n J h e P hn hJ he hevent hbad hdim hP hp hm
  let E:=fun b=>{x | residualCutoff ρ j (J b) (h b) k x≠0}
  let L:=fun b=>literalSusceptibility (fld j (J b) (h b) (k+1))
    (fun v=>j*(1-onsager j (J b) (h b) (k+1) v-SKGap.overlap (r b))) (r b)
  let M:=fun b=>literalMiddle j (J b) (h b) (r b) k (w b)
  have hstable : ∀b x,x∈E b→
      LiteralStableAt (J b) j (fld j (J b) (h b) (k+1)) (mag j (J b) (h b) (k+1))
        (fun v=>j*(1-onsager j (J b) (h b) (k+1) v-SKGap.overlap (r b))) (r b) R η c x := by
    intro b x hx
    have hact (v : Fin (n b)→ℝ) : vectorNorm ((J b).mulVec v)≤K*vectorNorm v :=
      (vectorNorm_matrix_mul _ v).trans (mul_le_mul_of_nonneg_right (hevent b).1 (vectorNorm_nonneg v))
    obtain ⟨r',hr',hu',hs⟩:=stable_primary_buffer (hn b) hj hK hA hc hr₀
      (mul_nonneg (by norm_num) hρ.le) hε hAR hbuffer hR hsmall (J b) (hJ b) (h b) hact (hbad b)
    have heqroot : r'=r b:=(hr b).2 r' hr'
    rw [heqroot] at hs
    obtain ⟨h0,h1⟩:=residualCutoff_support (hn b) hρ (J b) (h b) k x hx
    have hρ2 : ρ*Real.sqrt (n b:ℝ)≤(2*ρ)*Real.sqrt (n b:ℝ) := by nlinarith [mul_nonneg hρ.le (Real.sqrt_nonneg (n b:ℝ))]
    exact hs k x (h0.trans hρ2) (h1.trans hρ2)
  have hmiddle : ∀b x,x∈E b→|M b x|≤|L b x|/2 := by
    intro b x hx
    have H:=literal_middle_error (J b) j f (fld j (J b) (h b) (k+1))
      (mag j (J b) (h b) (k+1)) (w b) (y b)
      (fun v=>j*(1-onsager j (J b) (h b) (k+1) v-SKGap.overlap (r b))) (c₀ b) (r b) (e b) x
      (hn b) hc hη himplicit (hevent b).1 (he b) (hstable b x hx) (heq b x hx)
    change |M b x|≤(|j| *|literalSizeBudget j c R K f|)*η*|L b x| at H
    have H':=(mul_le_mul_of_nonneg_right habsorb (abs_nonneg (L b x)))
    exact H.trans (H'.trans_eq (by ring))
  have hweakL : LocalUniformWeak E P (fun b x=>L b x+M b x) := by
    apply hweak.congr
    intro b x
    rw [literal_source_phiR (hn b)]
  obtain ⟨D,hD,hstar⟩:=literalSusceptibility_cutoff_test j K B ρ hK hB hρ k
  obtain ⟨Q,hQ,hQbound⟩:=hweakL
  refine ⟨r,hr,4*Q^2+D,by positivity,?_⟩
  intro b
  apply tested_susceptibility_absorption (P b) (residualCutoff ρ j (J b) (h b) k) (L b) (M b)
    (hP b) hQ hD (hmiddle b)
  · apply hQbound b
    intro x hx
    have hc0 : residualCutoff ρ j (J b) (h b) k x=0 := by simpa only [E,Set.mem_ofPred_eq,not_not] using hx
    simp [hc0]
  · exact hstar (n b) (hn b) (J b) (h b) (r b) (P b) (hP b) (hp b)
      (hevent b).1 (fun x l hl=>(hevent b).2.1 (h b) x l hl)

end SKGapCutoff.Recipe

end
end

end OAI
end

theorem solution.{u} : type_of% @OAI.SKGapCutoff.Recipe.buffered_root_susceptibility_bound_oai.{u} := @OAI.SKGapCutoff.Recipe.buffered_root_susceptibility_bound_oai.{u}
