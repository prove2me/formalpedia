-- Prove2me | solution 1 for OAI.SKGapCutoff.Recipe.buffered_posterior_covariance
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:57:52.353897+00:00
-- url     : https://prove2.me/submissions/ca4ae681-cf03-4ec8-a629-cd8717f9aabe

import Mathlib
import Definitions.Def_OAIQ072A002
import Theorems.Thm_OAI_SKGapCutoff_Recipe_buffered_root_direction_weak
import Theorems.Thm_OAI_SKGapCutoff_Recipe_gibbs_residual_selection_deficit
import Theorems.Thm_OAI_SKGapCutoff_Recipe_primary_finite_control

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
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
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
-- module Solutions.OAIQ072_SK.SKGap_Localization_Character
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
namespace SKGapCutoff

lemma spin_replace_of_ne {n : ℕ} (x : Spin n) {i j : Fin n} (h : j ≠ i) (b : Bool) :
    spin (replace x i b) j = spin x j := by
  simp [spin, replace, Function.update_of_ne h]

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

lemma spin_flip {n : ℕ} (x : Spin n) (i j : Fin n) :
    spin (flip x i) j = spin x j - if j = i then 2 * spin x i else 0 := by
  by_cases h : j = i
  · subst j; simp; ring
  · simp [flip, spin_replace_of_ne x h, h]

lemma energy_flip {n : ℕ} (J : Interaction n) (hJ : ∀ i j, J i j = J j i)
    (hdiag : ∀ i, J i i = 0) (x : Spin n) (i : Fin n) :
    energy J (flip x i) = energy J x - 2 * spin x i * field J x i := by
  have hr : ∑ j, spin x j * J j i = field J x i := by
    simp only [field, hJ, mul_comm]
  unfold energy
  simp only [spin_flip, sub_mul, mul_sub, Finset.sum_sub_distrib]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte, hdiag]
  simp only [← Finset.sum_mul, hr]
  simp only [mul_assoc, ← Finset.mul_sum, field]
  ring

lemma exp_two_mul_one_sub_tanh (a : ℝ) :
    Real.exp (2 * a) * (1 - Real.tanh a) = 1 + Real.tanh a := by
  rw [Real.tanh_eq, show 2 * a = a + a by ring, Real.exp_add, Real.exp_neg]
  have he := Real.exp_pos a
  field_simp
  nlinarith

lemma sum_flip {n : ℕ} (i : Fin n) (f : Observables n) :
    ∑ x, f (flip x i) = ∑ x, f x := (flipEquiv n i).sum_comp f

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

theorem vectorNorm_smul {n : ℕ} (a : ℝ) (x : Field n) :
    vectorNorm (fun i => a * x i) = |a| * vectorNorm x := by
  exact norm_smul a (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))

attribute [local irreducible] vectorNorm

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

lemma phiPairSelect_norm (l m : ι) (α : κ) : ‖phiPairSelect l m α‖≤1 := by
  apply (phiPairSelect l m α).opNorm_le_bound (by norm_num)
  intro u
  change ‖(u (.inl l),(u (.inl m),u (.inr α)))‖≤1*‖u‖
  rw [one_mul,Prod.norm_def,Prod.norm_def]
  exact max_le (norm_le_pi_norm u _) (max_le (norm_le_pi_norm u _) (norm_le_pi_norm u _))

lemma two_field_kernel_regular (f : KernelExpr) (H : ι→VectorFields n)
    (θ : κ→Spin n→ℝ) (x : Spin n) (l m : ι) (α : κ) (R : ℝ)
    (hx : |θ α x|≤R) (hf : ∀k,|θ α (flip x k)|≤R) :
    SegmentRegular H θ (fun _ u=>eval3 f.eval (phiPairSelect l m α u))
      (fun _ u=>(f.gradient (phiPairSelect l m α u)).comp (phiPairSelect l m α)) x
      (f.dBudget R+f.ddBudget R) := by
  have h:=phi_kernel_segmentRegular f H θ x (phiPairSelect l m α) (fun _=>0) R
    (fun _=>by simpa [strip,phiPairSelect,localArgs] using hx)
    (fun _ k=>by simpa [strip,phiPairSelect,localArgs] using hf k)
  simp only [add_zero] at h
  apply h.mono
  have h1:=phiPairSelect_norm l m α
  have h2:=pow_le_pow_left₀ (norm_nonneg (phiPairSelect l m α)) h1 2
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

lemma primary_residual_field (j : ℝ) (J : Interaction n) (h : Fin n→ℝ)
    (k : ℕ) (x : Spin n) (i : Fin n) :
    let a:=j*(onsager j J h (k+1) x-onsager j J h k x)
    fld j J h k x i-fld j J h (k+1) x i-a*mag j J h (k+1) x i=
      (∑l,J i l*residual j J h k x l)+a*residual j J h k x i-
        j*onsager j J h k x*previousResidual j J h k x i := by
  dsimp only
  rw [fld_eq,fld_eq]
  simp only [Nat.add_sub_cancel,residual,previousResidual,mul_sub,Finset.sum_sub_distrib]
  ring

lemma residual_inner_product (hn : 0<n) (j : ℝ) (J : Interaction n) (h : Fin n→ℝ)
    (k : ℕ) (x : Spin n) :
    (∑i,residual j J h k x i*mag j J h k x i)=
      (n:ℝ)*(onsager j J h (k+1) x-onsager j J h k x)-
      ∑i,residual j J h k x i*mag j J h (k+1) x i := by
  have hnR : (n:ℝ)≠0 := ne_of_gt (Nat.cast_pos.mpr hn)
  simp only [onsager,siteMean,mul_sub,mul_div_cancel₀ _ hnR]
  rw [←Finset.sum_sub_distrib,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [residual]
  ring

lemma mulVec_pair_symmetric (J : Interaction n) (hJ : J.IsSymm) (u v : Fin n→ℝ) :
    (∑i,(∑l,J i l*u l)*v i)=∑l,u l*(∑i,J l i*v i) := by
  simp only [Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro l _
  apply Finset.sum_congr rfl; intro i _
  rw [hJ.apply i l]
  ring

lemma stein_residual_pointwise (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ)
    (U : VectorFields n) (x : Spin n) (i : Fin n) :
    residual j J h (k+1) x i*U x i=
      (fld j J h k x i-fld j J h (k+1) x i-
        j*(onsager j J h (k+1) x-onsager j J h k x)*mag j J h (k+1) x i)*
      steinSource j J h k U x i-
      j*(onsager j J h (k+1) x-onsager j J h k x)*steinPartial j J h k U x i := by
  dsimp only [steinSource,steinPartial,residual]
  simp only [mag_succ]
  rw [←phi_stein (fld j J h k x i) (fld j J h (k+1) x i)
    (j*(onsager j J h (k+1) x-onsager j J h k x))]
  ring

theorem residual_induction_identity {ι κ : Type*} [Fintype ι] [Fintype κ]
    (hn : 0<n) (j : ℝ) (J : Interaction n) (hJ : J.IsSymm) (h : Fin n→ℝ) (k : ℕ)
    (U : VectorFields n) (L : ι→ℕ) (α : ι→Spin n→ℝ)
    (W : κ→VectorFields n) (γ : κ→Spin n→ℝ) (x : Spin n) :
    (∑i,residual j J h (k+1) x i*U x i)=
      (∑i,residual j J h k x i*nextField j J h k U L α W γ x i)+
      j*(onsager j J h (k+1) x-onsager j J h k x)*
        (∑i,residual j J h k x i*steinSource j J h k U x i)-
      j*onsager j J h k x*(∑i,previousResidual j J h k x i*steinSource j J h k U x i)+
      j*(∑b,γ b x*∑i,residual j J h k x i*W b x i)+
      j*(∑l,α l x*∑i,residual j J h k x i*mag j J h (L l) x i)-
      j*siteMean (steinPartial j J h k U) x*
        (∑i,residual j J h k x i*mag j J h (k+1) x i) := by
  have hnR : (n:ℝ)≠0 := ne_of_gt (Nat.cast_pos.mpr hn)
  have hsum : (∑i,steinPartial j J h k U x i)=
      (n:ℝ)*siteMean (steinPartial j J h k U) x := by
    dsimp [siteMean]; field_simp
  have he:=residual_inner_product hn j J h k x
  have hs:=mulVec_pair_symmetric J hJ (residual j J h k x) (steinSource j J h k U x)
  have hon := primary_residual_field j J h k x
  have hfirst : (∑i,residual j J h (k+1) x i*U x i)=
      (∑i,(∑l,J i l*residual j J h k x l)*steinSource j J h k U x i)+
       j*(onsager j J h (k+1) x-onsager j J h k x)*
         (∑i,residual j J h k x i*steinSource j J h k U x i)-
       j*onsager j J h k x*(∑i,previousResidual j J h k x i*steinSource j J h k U x i)-
       j*(onsager j J h (k+1) x-onsager j J h k x)*
         (n:ℝ)*siteMean (steinPartial j J h k U) x := by
    simp_rw [stein_residual_pointwise j J h k U x,primary_residual_field]
    simp only [add_mul,sub_mul,Finset.sum_sub_distrib,Finset.sum_add_distrib,
      ←Finset.mul_sum,mul_assoc]
    rw [hsum]
  rw [hs] at hfirst
  have hy : (∑i,residual j J h k x i*nextField j J h k U L α W γ x i)=
      (∑i,residual j J h k x i*(∑l,J i l*steinSource j J h k U x l))-
      j*siteMean (steinPartial j J h k U) x*(∑i,residual j J h k x i*mag j J h k x i)-
      j*(∑l,α l x*∑i,residual j J h k x i*mag j J h (L l) x i)-
      j*(∑b,γ b x*∑i,residual j J h k x i*W b x i) := by
    dsimp [nextField]
    simp only [mul_sub,Finset.sum_sub_distrib]
    congr 2
    · congr 1
      simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    · simp only [Finset.mul_sum]; rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro l _
      apply Finset.sum_congr rfl; intro i _; ring
    · simp only [Finset.mul_sum]; rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro b _
      apply Finset.sum_congr rfl; intro i _; ring
  rw [hy,he,hfirst]
  ring

end SKGapCutoff.Primary

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

namespace OrdinaryData
variable (D : OrdinaryData n ι κ σ)

lemma source_eq (a : ℕ) : D.source a=D.sourceOf a (fun b=>D.auxiliary b) := by
  rw [source,evaluate]; rfl
lemma auxiliary_eq (a : ℕ) : D.auxiliary a=D.fieldOf a (fun b=>D.source b) (fun b=>D.auxiliary b) := by
  rw [auxiliary,evaluate]; rfl

end OrdinaryData

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ResidualRecipe2
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
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]
namespace OrdinaryData

lemma evaluation_prefix_eq (D E : OrdinaryData n ι κ σ) (N : ℕ)
    (hJ : E.J=D.J) (hj : E.j=D.j) (hp : E.predecessor=D.predecessor) (hs : E.seed=D.seed)
    (hseed : ∀a≤N,∀s,E.seedCoefficient a s=D.seedCoefficient a s)
    (haux : ∀a≤N,∀b,E.auxCoefficient a b=D.auxCoefficient a b)
    (hseedp : ∀a≤N,∀l s,E.seedPartial a l s=D.seedPartial a l s)
    (hauxp : ∀a≤N,∀l b,E.auxPartial a l b=D.auxPartial a l b) :
    ∀a≤N,E.source a=D.source a ∧ E.auxiliary a=D.auxiliary a := by
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih =>
    intro ha
    have hy : ∀ b:Fin a, E.auxiliary b=D.auxiliary b := by
      intro b; exact (ih b b.isLt (b.isLt.le.trans ha)).2
    have hw : ∀ b:Fin a, E.source b=D.source b := by
      intro b; exact (ih b b.isLt (b.isLt.le.trans ha)).1
    have hsrc : E.sourceOf a (fun b=>E.auxiliary b)=D.sourceOf a (fun b=>D.auxiliary b) := by
      funext x i
      unfold sourceOf
      simp only [hseed a ha,haux a ha,hs,hy]
    have hpart : ∀l,E.partialOf a l (fun b=>E.auxiliary b)=D.partialOf a l (fun b=>D.auxiliary b) := by
      intro l
      funext x i
      unfold partialOf
      simp only [hseedp a ha,hauxp a ha,hs,hy]
    constructor
    · simpa only [source_eq] using hsrc
    · rw [auxiliary_eq,auxiliary_eq]
      funext x i
      simp only [fieldOf,hJ,hj,hp,hsrc,hpart,hw,haux a ha]

lemma appendProduct_prefix (D : OrdinaryData n ι κ σ) (N : ℕ) (F F') :
    ∀a≤N,(D.appendProduct N F F').source a=D.source a ∧
      (D.appendProduct N F F').auxiliary a=D.auxiliary a := by
  apply evaluation_prefix_eq
  · rfl
  · rfl
  · rfl
  · rfl
  all_goals
    intro a ha
    have hn : a≠N+1 := by omega
  · intro s; ext x i; simp [seedCoefficient,coefficient,appendProduct,hn]
  · intro b; ext x i; simp [auxCoefficient,coefficient,appendProduct,hn]
  · intro l s; ext x i; simp [seedPartial,localPartial,appendProduct,hn]
  · intro l b; ext x i; simp [auxPartial,localPartial,appendProduct,hn]

lemma appendProduct_source (D : OrdinaryData n ι κ σ) (N : ℕ) (F F') :
    (D.appendProduct N F F').source (N+1)=
      fun x i=>coefficient D.H D.θ F x i*D.source N x i := by
  have hprev:=D.appendProduct_prefix N F F'
  ext x i
  rw [source_eq]
  dsimp only [sourceOf]
  rw [Fin.sum_univ_castSucc]
  simp only [auxCoefficient,seedCoefficient,coefficient,appendProduct,ite_true,Fin.val_castSucc,
    Fin.val_last,Fin.isLt,dite_true,lt_self_iff_false,dite_false,zero_mul,add_zero]
  have hy : ∀b:Fin N,(D.appendProduct N F F').auxiliary b=D.auxiliary b :=
    fun b=>(hprev b (by omega)).2
  dsimp only [appendProduct] at hy
  simp only [hy,Fin.eta]
  rw [D.source_eq]
  simp only [sourceOf,seedCoefficient,coefficient,auxCoefficient,mul_add,Finset.mul_sum,mul_assoc]

lemma appendProduct_partial (D : OrdinaryData n ι κ σ) (N : ℕ) (F F') (l : ι) :
    (D.appendProduct N F F').sourcePartial (N+1) l=
      fun x i=>coefficient D.H D.θ F x i*D.sourcePartial N l x i+
        localPartial D.H D.θ F' (.inl l) x i*D.source N x i := by
  have hprev:=D.appendProduct_prefix N F F'
  ext x i
  dsimp only [sourcePartial,partialOf]
  rw [Fin.sum_univ_castSucc]
  simp only [auxPartial,seedPartial,localPartial,appendProduct,ite_true,Fin.val_castSucc,
    Fin.val_last,Fin.isLt,dite_true,lt_self_iff_false,dite_false]
  have hy : ∀b:Fin N,(D.appendProduct N F F').auxiliary b=D.auxiliary b :=
    fun b=>(hprev b (by omega)).2
  dsimp only [appendProduct] at hy
  simp only [hy,Fin.eta]
  rw [D.source_eq]
  simp only [sourceOf,seedCoefficient,coefficient,auxCoefficient,partialAt,add_apply,
    smul_apply,smul_eq_mul,add_mul,mul_add,Finset.sum_add_distrib,Finset.mul_sum,
    zero_apply,zero_mul,add_zero,mul_assoc]
  simp only [mul_assoc,mul_comm,mul_left_comm]
  ring

lemma appendProduct_new_partial (D : OrdinaryData n ι κ σ) (N : ℕ) (F F') (l : ι)
    (hzero : D.sourcePartial N l=0) :
    (D.appendProduct N F F').sourcePartial (N+1) l=
      fun x i=>localPartial D.H D.θ F' (.inl l) x i*D.source N x i := by
  rw [appendProduct_partial,hzero]
  ext x i; simp

end OrdinaryData
end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary Matrix
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
lemma phiCoefficient_eq (l m : ι) (α : κ) (i : Fin n) (u : Args (ι:=ι) (κ:=κ)) :
    phiCoefficient l m α i u=phi (u (.inl l)) (u (.inl m)) (u (.inr α)) := by
  simp [phiCoefficient,eval3,phiPairSelect,KernelExpr.eval,moment_base]

lemma base_dz (z r a : ℝ) : (KernelExpr.atom 0 0 false).dz.eval z r a=phiZ z r a := by
  have H:=(KernelExpr.atom 0 0 false).hasDerivAt_z z r a
  simp only [KernelExpr.eval,moment_base] at H
  exact H.unique (phi_hasDerivAt z r a)

omit [Fintype ι] [Fintype κ] in
lemma phiDerivative_first (l m : ι) (α : κ) (hlm : l≠m) (i : Fin n) (u : Args (ι:=ι) (κ:=κ)) :
    partialAt (phiDerivative l m α i u) (.inl l)=phiZ (u (.inl l)) (u (.inl m)) (u (.inr α)) := by
  simp [partialAt,phiDerivative,phiPairSelect,KernelExpr.gradient,grad3,grad2,
    ContinuousLinearMap.toSpanSingleton_apply,hlm.symm,eval3,base_dz]

omit [Fintype ι] [Fintype κ] in
lemma phiDerivative_other (l m q : ι) (α : κ) (hql : q≠l) (hqm : q≠m)
    (i : Fin n) (u : Args (ι:=ι) (κ:=κ)) :
    partialAt (phiDerivative l m α i u) (.inl q)=0 := by
  simp [partialAt,phiDerivative,phiPairSelect,KernelExpr.gradient,grad3,grad2,
    ContinuousLinearMap.toSpanSingleton_apply,hql.symm,hqm.symm]

namespace OrdinaryData

lemma appendStein_source (D : OrdinaryData n ι κ σ) (N : ℕ) (l m : ι) (α : κ)
    (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ)
    (hl : D.H l=fld j J h k) (hm : D.H m=fld j J h (k+1))
    (ha : D.θ α=fun x=>j*(onsager j J h (k+1) x-onsager j J h k x)) :
    (D.appendStein N l m α).source (N+1)=steinSource j J h k (D.source N) := by
  rw [appendStein,appendProduct_source]
  ext x i
  simp [coefficient,phiCoefficient_eq,localArgs,hl,hm,ha,steinSource]

lemma appendStein_partial (D : OrdinaryData n ι κ σ) (N : ℕ) (l m : ι) (α : κ)
    (hlm : l≠m) (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ)
    (hl : D.H l=fld j J h k) (hm : D.H m=fld j J h (k+1))
    (ha : D.θ α=fun x=>j*(onsager j J h (k+1) x-onsager j J h k x))
    (hzero : D.sourcePartial N l=0) :
    (D.appendStein N l m α).sourcePartial (N+1) l=steinPartial j J h k (D.source N) := by
  rw [appendStein,appendProduct_new_partial _ _ _ _ _ hzero]
  ext x i
  simp [localPartial,phiDerivative_first l m α hlm,localArgs,hl,hm,ha,steinPartial]

lemma sum_split (f : ι→ℝ) (l : ι) : (∑q,f q)=f l+∑q:{q:ι//q≠l},f q := by
  rw [←Finset.sum_erase_add _ _ (Finset.mem_univ l),add_comm]
  congr 1
  exact Finset.sum_subtype (Finset.univ.erase l) (fun q=>show q∈Finset.univ.erase l ↔ q≠l by simp) f

lemma auxiliary_split (D : OrdinaryData n ι κ σ) (a : ℕ) (l : ι) (x : Spin n) (i : Fin n) :
    D.auxiliary a x i=(∑b,D.J i b*D.source a x b)-
      D.j*siteMean (D.sourcePartial a l) x*D.predecessor l x i-
      D.j*(∑q:{q:ι//q≠l},siteMean (D.sourcePartial a q) x*D.predecessor q x i)-
      D.j*∑b:Fin a,siteMean (D.auxCoefficient a b) x*D.source b x i := by
  rw [auxiliary_eq]
  simp only [fieldOf,←D.source_eq,sourcePartial,Matrix.mulVec,dotProduct]
  rw [sum_split _ l]
  ring

lemma appendStein_auxiliary (D : OrdinaryData n ι κ σ) (N : ℕ) (l m : ι) (α : κ)
    (hlm : l≠m) (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ)
    (L : ι→ℕ) (hj : D.j=j) (hJ : D.J=J)
    (hp : ∀q,D.predecessor q=mag j J h (L q)) (hL : L l=k)
    (hl : D.H l=fld j J h k) (hm : D.H m=fld j J h (k+1))
    (ha : D.θ α=fun x=>j*(onsager j J h (k+1) x-onsager j J h k x))
    (hzero : D.sourcePartial N l=0) :
    let E:=D.appendStein N l m α
    E.auxiliary (N+1)=nextField j J h k (D.source N)
      (fun q:{q:ι//q≠l}=>L q) (fun q=>siteMean (E.sourcePartial (N+1) q))
      (fun b:Fin (N+1)=>E.source b) (fun b=>siteMean (E.auxCoefficient (N+1) b)) := by
  dsimp only
  funext x i
  rw [auxiliary_split _ _ l,appendStein_source D N l m α j J h k hl hm ha,
    appendStein_partial D N l m α hlm j J h k hl hm ha hzero]
  simp only [appendStein,appendProduct,hJ,hj,hp,hL,nextField]

theorem residual_step (D : OrdinaryData n ι κ σ) (N : ℕ) (l m : ι) (α : κ)
    (hlm : l≠m) (hn : 0<n) (j : ℝ) (J : Interaction n) (hJs : J.IsSymm)
    (h : Fin n→ℝ) (k : ℕ) (L : ι→ℕ) (hj : D.j=j) (hJ : D.J=J)
    (hp : ∀q,D.predecessor q=mag j J h (L q)) (hL : L l=k)
    (hl : D.H l=fld j J h k) (hm : D.H m=fld j J h (k+1))
    (ha : D.θ α=fun x=>j*(onsager j J h (k+1) x-onsager j J h k x))
    (hzero : D.sourcePartial N l=0) (x : Spin n) :
    let E:=D.appendStein N l m α
    (∑i,residual j J h (k+1) x i*D.source N x i)=
      (∑i,residual j J h k x i*E.auxiliary (N+1) x i)+
      j*(onsager j J h (k+1) x-onsager j J h k x)*(∑i,residual j J h k x i*E.source (N+1) x i)-
      j*onsager j J h k x*(∑i,previousResidual j J h k x i*E.source (N+1) x i)+
      j*(∑b:Fin (N+1),siteMean (E.auxCoefficient (N+1) b) x*∑i,residual j J h k x i*E.source b x i)+
      j*(∑q:{q:ι//q≠l},siteMean (E.sourcePartial (N+1) q) x*∑i,residual j J h k x i*mag j J h (L q) x i)-
      j*siteMean (E.sourcePartial (N+1) l) x*(∑i,residual j J h k x i*mag j J h (k+1) x i) := by
  dsimp only
  rw [appendStein_auxiliary D N l m α hlm j J h k L hj hJ hp hL hl hm ha hzero,
    appendStein_source D N l m α j J h k hl hm ha,
    appendStein_partial D N l m α hlm j J h k hl hm ha hzero]
  exact residual_induction_identity hn j J hJs h k (D.source N)
    (fun q:{q:ι//q≠l}=>L q)
    (fun q=>siteMean ((D.appendStein N l m α).sourcePartial (N+1) q))
    (fun b:Fin (N+1)=>(D.appendStein N l m α).source b)
    (fun b=>siteMean ((D.appendStein N l m α).auxCoefficient (N+1) b)) x

end OrdinaryData
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

lemma Admissible.sourcePartial {D : OrdinaryData n (Fin M) κ σ} {N p : ℕ}
    (h : D.Admissible N p) (a : ℕ) (ha : a≤N) (q : Fin M) (hq : q.val<p) :
    D.sourcePartial a q=0 := by
  ext x i
  simp only [OrdinaryData.sourcePartial,partialOf,(h a ha q hq).1,(h a ha q hq).2,
    Pi.zero_apply,zero_mul,Finset.sum_const_zero,add_zero]

omit [Fintype σ] in
lemma appendProduct_Admissible (D : OrdinaryData n (Fin M) κ σ) (N p : ℕ) (F F')
    (h : D.Admissible N p)
    (hf : ∀q:Fin M,q.val<p→ localPartial D.H D.θ F' (.inl q)=0) :
    (D.appendProduct N F F').Admissible (N+1) p := by
  intro a ha q hq
  by_cases he : a=N+1
  · subst a
    have hs:= (h N le_rfl q hq).1
    have hb:= (h N le_rfl q hq).2
    have hfs:=hf q hq
    constructor
    · intro s; ext x i
      have hs':partialAt (D.seedDerivative N s i (localArgs D.H D.θ x i)) (.inl q)=0 := congrFun (congrFun (hs s) x) i
      have hf':partialAt (F' i (localArgs D.H D.θ x i)) (.inl q)=0 := congrFun (congrFun hfs x) i
      simp [seedPartial,localPartial,appendProduct,partialAt] at hs' hf' ⊢
      rw [hs',hf']; ring
    · intro b; ext x i
      by_cases hh : b.val<N
      · have hb':partialAt (D.auxDerivative N ⟨b.val,hh⟩ i (localArgs D.H D.θ x i)) (.inl q)=0 :=
          congrFun (congrFun (hb ⟨b.val,hh⟩) x) i
        have hf':partialAt (F' i (localArgs D.H D.θ x i)) (.inl q)=0 := congrFun (congrFun hfs x) i
        simp [auxPartial,localPartial,appendProduct,partialAt,hh] at hb' hf' ⊢
        rw [hb',hf']; ring
      · simp [auxPartial,localPartial,appendProduct,hh,partialAt]
  · have haN : a≤N := by omega
    simpa only [seedPartial,auxPartial,localPartial,appendProduct,ite_eq_right he] using h a haN q hq

omit [Fintype σ] in
lemma appendStein_Admissible (D : OrdinaryData n (Fin M) κ σ) (N p : ℕ)
    (l m : Fin M) (α : κ) (hl : p≤l.val) (hm : p ≤ m.val)
    (h : D.Admissible N p) : (D.appendStein N l m α).Admissible (N+1) p := by
  apply D.appendProduct_Admissible N p _ _ h
  intro q hq
  ext x i
  exact phiDerivative_other l m q α (by intro he; subst q; omega) (by intro he; subst q; omega) i _

lemma appendAuxiliary_prefix (D : OrdinaryData n (Fin M) κ σ) (N : ℕ) :
    ∀a≤N,(D.appendAuxiliary N).source a=D.source a ∧
      (D.appendAuxiliary N).auxiliary a=D.auxiliary a := by
  apply evaluation_prefix_eq D (D.appendAuxiliary N) N rfl rfl rfl rfl
  all_goals
    intro a ha
    have hh : a≠N+1 := by omega
    simp [seedCoefficient,auxCoefficient,seedPartial,auxPartial,appendAuxiliary,hh]

lemma appendAuxiliary_source (D : OrdinaryData n (Fin M) κ σ) (N : ℕ) :
    (D.appendAuxiliary N).source (N+1)=D.auxiliary N := by
  rw [source_eq]
  ext x i
  dsimp only [sourceOf]
  rw [Fin.sum_univ_castSucc]
  have hy : (D.appendAuxiliary N).auxiliary N=D.auxiliary N := (D.appendAuxiliary_prefix N N le_rfl).2
  dsimp only [appendAuxiliary] at hy
  simp [seedCoefficient,auxCoefficient,coefficient,appendAuxiliary,hy,
    show ∀b:Fin N,b.val≠N from fun b=>Nat.ne_of_lt b.isLt]

omit [Fintype σ] in
lemma appendAuxiliary_Admissible (D : OrdinaryData n (Fin M) κ σ) (N p : ℕ)
    (h : D.Admissible N p) : (D.appendAuxiliary N).Admissible (N+1) p := by
  intro a ha q hq
  by_cases he : a=N+1
  · subst a
    constructor
    · intro s; ext x i; simp [seedPartial,localPartial,appendAuxiliary,partialAt]
    · intro b; ext x i; simp [auxPartial,localPartial,appendAuxiliary,partialAt]
  · have haN : a≤N := by omega
    simpa only [seedPartial,auxPartial,localPartial,appendAuxiliary,ite_eq_right he] using h a haN q hq

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

omit [Fintype σ] in
lemma CoefficientClass.appendProduct {D : OrdinaryData n ι κ σ} {N : ℕ} {x : Spin n} {K B : ℝ}
    (h : D.CoefficientClass N x K) (hB : 0≤B)
    (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ) (F')
    (hr : SegmentRegular D.H D.θ F F' x B) (hv : SegmentValue D.H D.θ F x B) :
    (D.appendProduct N F F').CoefficientClass (N+1) x (K+4*B*K) := by
  have hK : 0≤K := le_trans (by norm_num) h.one_le
  have hk : K≤K+4*B*K := le_add_of_nonneg_right (by positivity)
  have hbk : B*K≤K+4*B*K := by nlinarith [mul_nonneg hB hK]
  have hrk : B*K+K*B+2*B*K≤K+4*B*K := by nlinarith
  have hrold (G G') (hg : SegmentRegular D.H D.θ G G' x K) :
      SegmentRegular D.H D.θ G G' x (K+4*B*K) := hg.mono hk
  have hrnew (G G') (hg : SegmentRegular D.H D.θ G G' x K)
      (hgv : SegmentValue D.H D.θ G x K) :
      SegmentRegular D.H D.θ (fun i u=>F i u*G i u)
        (fun i u=>F i u • G' i u+G i u • F' i u) x (K+4*B*K) :=
    (hr.mul hg hB hK hv hgv).mono hrk
  refine ⟨h.one_le.trans hk,?_,?_,?_,?_⟩
  · intro a ha s
    by_cases he : a=N+1
    · subst a
      simpa only [OrdinaryData.appendProduct,ite_true] using hrnew _ _ (h.seedRegular N le_rfl s) (h.seedValue N le_rfl s)
    · have haN : a≤N := by omega
      simpa only [OrdinaryData.appendProduct,ite_eq_right he] using hrold _ _ (h.seedRegular a haN s)
  · intro a ha b
    by_cases he : a=N+1
    · subst a
      by_cases hb : b.val<N
      · simpa only [OrdinaryData.appendProduct,ite_true,dite_eq_left hb] using hrnew _ _ (h.auxRegular N le_rfl ⟨b.val,hb⟩) (h.auxValue N le_rfl ⟨b.val,hb⟩)
      · simpa only [OrdinaryData.appendProduct,ite_true,dite_eq_right hb] using (segmentRegular_const D.H D.θ x 0).mono (hK.trans hk)
    · have haN : a≤N := by omega
      simpa only [OrdinaryData.appendProduct,ite_eq_right he] using hrold _ _ (h.auxRegular a haN b)
  · intro a ha s i k t ht
    by_cases he : a=N+1
    · subst a
      simp only [OrdinaryData.appendProduct,ite_true,abs_mul]
      exact (mul_le_mul (hv i k t ht) (h.seedValue N le_rfl s i k t ht) (abs_nonneg _) hB).trans hbk
    · have haN : a≤N := by omega
      simpa only [OrdinaryData.appendProduct,ite_eq_right he] using (h.seedValue a haN s i k t ht).trans hk
  · intro a ha b i k t ht
    by_cases he : a=N+1
    · subst a
      by_cases hb : b.val<N
      · simp only [OrdinaryData.appendProduct,ite_true,dite_eq_left hb,abs_mul]
        exact (mul_le_mul (hv i k t ht) (h.auxValue N le_rfl ⟨b.val,hb⟩ i k t ht) (abs_nonneg _) hB).trans hbk
      · simpa only [OrdinaryData.appendProduct,ite_true,dite_eq_right hb,abs_zero] using hK.trans hk
    · have haN : a≤N := by omega
      simpa only [OrdinaryData.appendProduct,ite_eq_right he] using (h.auxValue a haN b i k t ht).trans hk

omit [Fintype σ] in
lemma CoefficientClass.appendAuxiliary {M : ℕ} {D : OrdinaryData n (Fin M) κ σ}
    {N : ℕ} {x : Spin n} {K : ℝ} (h : D.CoefficientClass N x K) :
    (D.appendAuxiliary N).CoefficientClass (N+1) x K := by
  have hK : 0≤K := le_trans (by norm_num) h.one_le
  refine ⟨h.one_le,?_,?_,?_,?_⟩
  · intro a ha s
    by_cases he : a=N+1
    · subst a
      simpa only [OrdinaryData.appendAuxiliary,ite_true] using (segmentRegular_const D.H D.θ x 0).mono hK
    · have haN : a≤N := by omega
      simpa only [OrdinaryData.appendAuxiliary,ite_eq_right he] using h.seedRegular a haN s
  · intro a ha b
    by_cases he : a=N+1
    · subst a
      simp only [OrdinaryData.appendAuxiliary,ite_true]
      exact (segmentRegular_const D.H D.θ x (if b.val=N then 1 else 0)).mono hK
    · have haN : a≤N := by omega
      simpa only [OrdinaryData.appendAuxiliary,ite_eq_right he] using h.auxRegular a haN b
  · intro a ha s i k t ht
    by_cases he : a=N+1
    · simp [OrdinaryData.appendAuxiliary,he,hK]
    · have haN : a≤N := by omega
      simpa only [OrdinaryData.appendAuxiliary,ite_eq_right he] using h.seedValue a haN s i k t ht
  · intro a ha b i k t ht
    by_cases he : a=N+1
    · simp only [OrdinaryData.appendAuxiliary,ite_eq_left he]
      split_ifs
      · simpa using h.one_le
      · simpa using hK
    · have haN : a≤N := by omega
      simpa only [OrdinaryData.appendAuxiliary,ite_eq_right he] using h.auxValue a haN b i k t ht

end OrdinaryData
end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_SteinRecipeRegularity
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
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
lemma two_field_kernel_value (f : KernelExpr) (H : ι→VectorFields n)
    (θ : κ→Spin n→ℝ) (x : Spin n) (l m : ι) (α : κ) (R : ℝ)
    (hx : |θ α x|≤R) (hf : ∀k,|θ α (flip x k)|≤R) :
    SegmentValue H θ (fun _ u=>eval3 f.eval (phiPairSelect l m α u)) x (f.mass*Real.exp (R/2)) := by
  intro i k t ht
  apply f.absolute_bound
  have hb : phiPairSelect l m α (localArgs H θ x i)∈strip R := by
    simpa [strip,phiPairSelect,localArgs] using hx
  have he : phiPairSelect l m α (localArgs H θ (flip x k) i)∈strip R := by
    simpa [strip,phiPairSelect,localArgs] using hf k
  have := (convex_strip R).add_smul_sub_mem hb he ht
  simpa only [map_add,map_smul,map_sub] using this

lemma steinCoefficientBudget_nonneg (R : ℝ) : 0 ≤ steinCoefficientBudget R := by
  have h0:= (KernelExpr.atom 0 0 false).mass_nonneg
  have h1:= (KernelExpr.atom 0 0 false).dBudget_nonneg R
  have h2:= (KernelExpr.atom 0 0 false).ddBudget_nonneg R
  unfold steinCoefficientBudget
  positivity

namespace OrdinaryData
omit [Fintype σ] in
lemma CoefficientClass.appendStein {D : OrdinaryData n ι κ σ} {N : ℕ} {x : Spin n} {K : ℝ}
    (h : D.CoefficientClass N x K) (l m : ι) (α : κ) (R : ℝ)
    (hx : |D.θ α x|≤R) (hf : ∀k,|D.θ α (flip x k)|≤R) :
    (D.appendStein N l m α).CoefficientClass (N+1) x (K+4*steinCoefficientBudget R*K) := by
  apply h.appendProduct (steinCoefficientBudget_nonneg R)
  · apply (two_field_kernel_regular (KernelExpr.atom 0 0 false) D.H D.θ x l m α R hx hf).mono
    exact le_add_of_nonneg_left (mul_nonneg (KernelExpr.atom 0 0 false).mass_nonneg (Real.exp_pos _).le) |>.trans_eq (by unfold steinCoefficientBudget; ring)
  · intro i k t ht
    exact (two_field_kernel_value (KernelExpr.atom 0 0 false) D.H D.θ x l m α R hx hf i k t ht).trans
      (by unfold steinCoefficientBudget; linarith [(KernelExpr.atom 0 0 false).dBudget_nonneg R,(KernelExpr.atom 0 0 false).ddBudget_nonneg R])
end OrdinaryData
end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_ConditionalMean
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
namespace SKGapCutoff.Static

lemma conditionalMean_mul_mass {n : ℕ} (Q : Spin n → ℝ)
    (hQ : ∀ x, 0 ≤ Q x) (x : Spin n) (i : Fin n) :
    (Q x + Q (flip x i)) * conditionalMean Q x i =
      spin x i * (Q x-Q (flip x i)) := by
  unfold conditionalMean
  by_cases h : Q x + Q (flip x i) = 0
  · have ha : Q x=0 := by have := hQ (flip x i); have := hQ x; linarith
    have hb : Q (flip x i)=0 := by have := hQ x; have := hQ (flip x i); linarith
    simp [ha,hb]
  · field_simp

lemma conditionalMean_abs_le {n : ℕ} (Q : Spin n → ℝ)
    (hQ : ∀ x, 0 ≤ Q x) (x : Spin n) (i : Fin n) :
    |conditionalMean Q x i| ≤ 1 := by
  have hs : |spin x i| = 1 := by cases hx : x i <;> simp [spin,hx]
  simp only [conditionalMean, abs_mul, hs, one_mul, abs_div]
  rw [abs_of_nonneg (add_nonneg (hQ x) (hQ _))]
  apply div_le_one_of_le₀ _ (add_nonneg (hQ x) (hQ _))
  exact abs_sub_le_iff.2 ⟨by linarith [hQ (flip x i)], by linarith [hQ x]⟩

lemma law_coordinate_mean {n : ℕ} (Q : Spin n → ℝ) (hQ : ∀ x, 0 ≤ Q x)
    (i : Fin n) (F : Spin n → ℝ) (hF : ∀ x, F (flip x i)=F x) :
    (∑ x, Q x * spin x i * F x) = ∑ x, Q x * conditionalMean Q x i * F x := by
  have ha := sum_flip i (fun x => Q x * spin x i * F x)
  have hb := sum_flip i (fun x => Q x * conditionalMean Q x i * F x)
  simp only [spin_flip_self, conditionalMean_flip, hF] at ha hb
  have he (x : Spin n) :
      Q x * spin x i * F x + Q (flip x i) * -spin x i * F x =
      Q x * conditionalMean Q x i * F x +
        Q (flip x i) * conditionalMean Q x i * F x := by
    have hm := conditionalMean_mul_mass Q hQ x i
    have := congrArg (fun z => z * F x) hm
    nlinarith only [this]
  have hh := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun x _ => he x)
  simp only [Finset.sum_add_distrib, ha, hb] at hh
  linarith only [hh]

lemma law_integration_by_parts {n : ℕ} (Q : Spin n → ℝ) (hQ : ∀ x, 0 ≤ Q x)
    (i : Fin n) (F : Spin n → ℝ) :
    (∑ x, Q x * (spin x i - conditionalMean Q x i) * F x) =
      ∑ x, Q x * (1-spin x i*conditionalMean Q x i) * halfDiff i F x := by
  have hh : ∀ x, (F (flip x i) - spin (flip x i) i * halfDiff i F (flip x i)) =
      F x - spin x i * halfDiff i F x := by
    intro x
    rw [spin_flip_self, halfDiff_flip]
    linarith only [flip_sub i F x]
  have he := law_coordinate_mean Q hQ i
    (fun x => F x-spin x i*halfDiff i F x) hh
  have h1 (x : Spin n) : Q x * spin x i * (F x-spin x i*halfDiff i F x) =
      Q x*spin x i*F x - Q x*halfDiff i F x := by
    have hs := spin_sq x i
    nlinarith only [congrArg (fun z : ℝ => Q x*halfDiff i F x*z) hs]
  simp_rw [h1] at he
  simp only [mul_sub, Finset.sum_sub_distrib] at he
  have h2 (x : Spin n) : Q x * (spin x i - conditionalMean Q x i) * F x =
      Q x * spin x i * F x - Q x * conditionalMean Q x i * F x := by ring
  have h3 (x : Spin n) : Q x * (1-spin x i*conditionalMean Q x i) * halfDiff i F x =
      Q x * halfDiff i F x -
        Q x * conditionalMean Q x i * (spin x i * halfDiff i F x) := by ring
  simp_rw [h2, h3, Finset.sum_sub_distrib]
  linarith only [he]

lemma law_integration_by_parts_variance {n : ℕ} (Q : Spin n → ℝ)
    (hQ : ∀ x, 0 ≤ Q x) (i : Fin n) (F : Spin n → ℝ) :
    (∑ x, Q x * (spin x i-conditionalMean Q x i) * F x) =
      ∑ x, Q x*(1-(conditionalMean Q x i)^2)*halfDiff i F x := by
  rw [law_integration_by_parts Q hQ]
  have hh := law_coordinate_mean Q hQ i
    (fun x => conditionalMean Q x i*halfDiff i F x)
    (by intro x; rw [conditionalMean_flip,halfDiff_flip])
  simp only [mul_sub,sub_mul,mul_one,Finset.sum_sub_distrib,pow_two,← mul_assoc] at hh ⊢
  rw [hh]

lemma weighted_cauchy_sq {α : Type*} [Fintype α] (w f g : α → ℝ)
    (hw : ∀ a, 0 ≤ w a) :
    (∑ a, w a*f a*g a)^2 ≤ (∑ a, w a*f a^2)*(∑ a, w a*g a^2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    Finset.univ (fun a _ => mul_nonneg (hw a) (sq_nonneg _))
      (fun a _ => mul_nonneg (hw a) (sq_nonneg _))
  intro a _
  exact le_of_eq (by ring)

end SKGapCutoff.Static

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise NNReal ENNReal

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

lemma conditionalVariance_nonneg (P : Spin n→ℝ) (hP : ∀ x,0≤P x)
    (x : Spin n) (i : Fin n) : 0 ≤ conditionalVariance P x i := by
  have h:=conditionalMean_abs_le P hP x i
  have hh:=pow_le_pow_left₀ (abs_nonneg (conditionalMean P x i)) h 2
  simpa only [sq_abs,one_pow,conditionalVariance,sub_nonneg] using hh

lemma conditionalVariance_le_one (P : Spin n→ℝ) (x : Spin n) (i : Fin n) :
    conditionalVariance P x i≤1 := by dsimp [conditionalVariance]; nlinarith [sq_nonneg (conditionalMean P x i)]

lemma varianceEnergy_nonneg (P : Spin n→ℝ) (hP : ∀ x,0≤P x) (f : Observables n) :
    0≤varianceEnergy P f := by
  exact Finset.sum_nonneg (fun x _=>mul_nonneg (hP x)
    (Finset.sum_nonneg (fun i _=>mul_nonneg (conditionalVariance_nonneg P hP x i) (sq_nonneg _))))

lemma residual_product_identity (P : Spin n→ℝ) (hP : ∀ x,0≤P x)
    (G : Observables n) (U : VectorFields n) :
    (∑ x,P x*G x*∑ i,(spin x i-conditionalMean P x i)*U x i)=
    (∑ x,P x*G x*∑ i,conditionalVariance P x i*halfDiff i (fun y=>U y i) x)+
    ∑ x,P x*∑ i,conditionalVariance P x i*halfDiff i G x*
      (U x i-2*spin x i*halfDiff i (fun y=>U y i) x) := by
  have H (i : Fin n):=law_integration_by_parts_variance P hP i (fun x=>G x*U x i)
  simp_rw [halfDiff_mul] at H
  simp only [Finset.mul_sum,←Finset.sum_add_distrib]
  rw [Finset.sum_comm,Finset.sum_comm (f:=fun x i=>
    P x*G x*(conditionalVariance P x i*halfDiff i (fun y=>U y i) x)+
    P x*(conditionalVariance P x i*halfDiff i G x*
      (U x i-2*spin x i*halfDiff i (fun y=>U y i) x)))]
  apply Finset.sum_congr rfl
  intro i _
  convert H i using 1
  · apply Finset.sum_congr rfl; intro x _; ring
  · apply Finset.sum_congr rfl; intro x _; dsimp [conditionalVariance]; ring

lemma diagonal_reflected_bound (U : VectorFields n) {A B : ℝ}
    (hA : 0≤A) (hB : 0≤B)
    (hD : ∀ x,∑ i,|halfDiff i (fun y=>U y i) x|≤A)
    (hU : ∀ x,∑ i,(U x i)^2≤B^2) (x : Spin n) :
    (∑ i,(U x i-2*spin x i*halfDiff i (fun y=>U y i) x)^2)≤(2*B+4*A)^2 := by
  have hd : (∑ i,(halfDiff i (fun y=>U y i) x)^2)≤A^2 := by
    have h:=Finset.sum_sq_le_sq_sum_of_nonneg (s:=Finset.univ)
      (f:=fun i=>|halfDiff i (fun y=>U y i) x|) (fun i _=>abs_nonneg _)
    simp only [sq_abs] at h
    exact h.trans (pow_le_pow_left₀ (Finset.sum_nonneg (fun i _=>abs_nonneg _)) (hD x) 2)
  calc
    _ ≤ ∑ i,(2*(U x i)^2+8*(halfDiff i (fun y=>U y i) x)^2) := by
      apply Finset.sum_le_sum
      intro i _
      have hs:=spin_sq x i
      have he : (spin x i*halfDiff i (fun y=>U y i) x)^2=
          (halfDiff i (fun y=>U y i) x)^2 := by rw [mul_pow,hs,one_mul]
      nlinarith only [sq_nonneg (U x i+2*spin x i*halfDiff i (fun y=>U y i) x),he]
    _ = 2*(∑ i,(U x i)^2)+8*(∑ i,(halfDiff i (fun y=>U y i) x)^2) := by
      simp only [Finset.sum_add_distrib,←Finset.mul_sum]
    _ ≤ (2*B+4*A)^2 := by nlinarith [hU x,mul_nonneg hA hB]

lemma weighted_residual_derivative_bound (P : Spin n→ℝ) (hP : ∀ x,0≤P x)
    (G : Observables n) (U : VectorFields n) {A : ℝ}
    (hD : ∀ x,∑ i,|halfDiff i (fun y=>U y i) x|≤A) :
    |∑ x,P x*G x*∑ i,conditionalVariance P x i*halfDiff i (fun y=>U y i) x|≤
      A*(∑ x,P x*|G x|) := by
  calc
    _ ≤ ∑ x,|P x*G x*∑ i,conditionalVariance P x i*halfDiff i (fun y=>U y i) x| :=
      Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ x,P x*|G x| *A := by
      apply Finset.sum_le_sum; intro x _
      rw [abs_mul,abs_mul,abs_of_nonneg (hP x)]
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hP x) (abs_nonneg _))
      calc
        _ ≤ ∑ i,|conditionalVariance P x i*halfDiff i (fun y=>U y i) x| :=
          Finset.abs_sum_le_sum_abs ..
        _ ≤ ∑ i,|halfDiff i (fun y=>U y i) x| := by
          apply Finset.sum_le_sum; intro i _
          rw [abs_mul,abs_of_nonneg (conditionalVariance_nonneg P hP x i)]
          exact mul_le_of_le_one_left (abs_nonneg _) (conditionalVariance_le_one P x i)
        _ ≤ A := hD x
    _ = _ := by rw [←Finset.sum_mul,mul_comm]

lemma energy_pair_bound (P : Spin n→ℝ) (hP : ∀ x,0≤P x)
    (hPsum : ∑ x,P x=1) (f : Observables n) (V : VectorFields n) {C : ℝ}
    (hC : 0≤C) (hV : ∀ x,∑ i,(V x i)^2≤C^2) :
    |∑ x,P x*∑ i,conditionalVariance P x i*halfDiff i f x*V x i|≤
      C*Real.sqrt (varianceEnergy P f) := by
  have H:=weighted_cauchy_sq (fun a : Spin n×Fin n=>P a.1*conditionalVariance P a.1 a.2)
    (fun a=>halfDiff a.2 f a.1) (fun a=>V a.1 a.2)
    (fun a=>mul_nonneg (hP _) (conditionalVariance_nonneg P hP _ _))
  simp only [Fintype.sum_prod_type,mul_assoc,←Finset.mul_sum] at H
  have hv : (∑ x,P x*∑ i,conditionalVariance P x i*(V x i)^2)≤C^2 := by
    calc
      _ ≤ ∑ x,P x*C^2 := by
        apply Finset.sum_le_sum; intro x _
        apply mul_le_mul_of_nonneg_left _ (hP x)
        exact (Finset.sum_le_sum (fun i _=>mul_le_of_le_one_left (sq_nonneg _) (conditionalVariance_le_one P x i))).trans (hV x)
      _ = C^2 := by rw [←Finset.sum_mul,hPsum,one_mul]
  have hn:=varianceEnergy_nonneg P hP f
  have ht:=H.trans (mul_le_mul_of_nonneg_left hv hn)
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hC (Real.sqrt_nonneg _))).1
  rw [sq_abs,mul_pow,Real.sq_sqrt hn]
  simpa only [varianceEnergy,mul_assoc,mul_comm,mul_left_comm] using ht

theorem signed_weak_residual_base (P : Spin n→ℝ) (hP : ∀ x,0≤P x)
    (hPsum : ∑ x,P x=1) (G : Observables n) (U : VectorFields n) {A B : ℝ}
    (hA : 0≤A) (hB : 0≤B)
    (hD : ∀ x,∑ i,|halfDiff i (fun y=>U y i) x|≤A)
    (hU : ∀ x,∑ i,(U x i)^2≤B^2) :
    |∑ x,P x*G x*∑ i,(spin x i-conditionalMean P x i)*U x i|≤
      A*(∑ x,P x*|G x|)+(2*B+4*A)*Real.sqrt (varianceEnergy P G) := by
  rw [residual_product_identity P hP G U]
  exact (abs_add_le _ _).trans (add_le_add (weighted_residual_derivative_bound P hP G U hD)
    (energy_pair_bound P hP hPsum G _ (by positivity) (diagonal_reflected_bound U hA hB hD hU)))

lemma coordinate_abs_le_of_square_sum (V : VectorFields n) {C : ℝ}
    (hC : 0≤C) (hV : ∀ x,∑ i,(V x i)^2≤C^2) (x : Spin n) (i : Fin n) :
    |V x i|≤C := by
  apply (sq_le_sq₀ (abs_nonneg _) hC).1
  rw [sq_abs]
  exact (Finset.single_le_sum (fun k _=>sq_nonneg (V x k)) (Finset.mem_univ i)).trans (hV x)

lemma energy_cross_square_bound (P : Spin n→ℝ) (hP : ∀ x,0≤P x)
    (f : Observables n) (V : VectorFields n) {C : ℝ}
    (hC : 0≤C) (hV : ∀ x,∑ i,(V x i)^2≤C^2) :
    |2*(∑ x,P x*∑ i,conditionalVariance P x i*f x*halfDiff i f x*V x i)|≤
      C*((∑ x,P x*(f x)^2)+varianceEnergy P f) := by
  have H:=weighted_cauchy_sq (fun a : Spin n×Fin n=>P a.1*conditionalVariance P a.1 a.2)
    (fun a=>halfDiff a.2 f a.1) (fun a=>f a.1*V a.1 a.2)
    (fun a=>mul_nonneg (hP _) (conditionalVariance_nonneg P hP _ _))
  simp only [Fintype.sum_prod_type,mul_assoc,←Finset.mul_sum] at H
  have hv : (∑ x,P x*∑ i,conditionalVariance P x i*(f x*V x i)^2)≤
      C^2*(∑ x,P x*(f x)^2) := by
    calc
      _ ≤ ∑ x,P x*((f x)^2*C^2) := by
        apply Finset.sum_le_sum; intro x _
        apply mul_le_mul_of_nonneg_left _ (hP x)
        have he : (∑ i,conditionalVariance P x i*(f x*V x i)^2)=
            (f x)^2*(∑ i,conditionalVariance P x i*(V x i)^2) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
        rw [he]
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact (Finset.sum_le_sum (fun i _=>mul_le_of_le_one_left (sq_nonneg _) (conditionalVariance_le_one P x i))).trans (hV x)
      _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
  have hn:=varianceEnergy_nonneg P hP f
  have hz : 0≤∑ x,P x*(f x)^2 := Finset.sum_nonneg (fun x _=>mul_nonneg (hP x) (sq_nonneg _))
  have he : (∑ x,P x*∑ i,conditionalVariance P x i*(halfDiff i f x*(f x*V x i)))=
      ∑ x,P x*∑ i,conditionalVariance P x i*f x*halfDiff i f x*V x i := by
    apply Finset.sum_congr rfl; intro x _; congr 1
    apply Finset.sum_congr rfl; intro i _; ring
  rw [he] at H
  have ht:=H.trans (mul_le_mul_of_nonneg_left hv hn)
  change _≤varianceEnergy P f*(C^2*(∑ x,P x*(f x)^2)) at ht
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hC (add_nonneg hz hn))).1
  rw [sq_abs]
  nlinarith [mul_nonneg (sq_nonneg C) (sq_nonneg ((∑ x,P x*(f x)^2)-varianceEnergy P f))]

lemma energy_square_coefficient_bound (P : Spin n→ℝ) (hP : ∀ x,0≤P x)
    (f : Observables n) (V : VectorFields n) {C : ℝ}
    (hC : 0≤C) (hV : ∀ x,∑ i,(V x i)^2≤C^2) :
    |∑ x,P x*∑ i,conditionalVariance P x i*spin x i*(halfDiff i f x)^2*V x i|≤
      C*varianceEnergy P f := by
  calc
    _ ≤ ∑ x,|P x*∑ i,conditionalVariance P x i*spin x i*(halfDiff i f x)^2*V x i| :=
      Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ x,P x*∑ i,C*(conditionalVariance P x i*(halfDiff i f x)^2) := by
      apply Finset.sum_le_sum; intro x _
      rw [abs_mul,abs_of_nonneg (hP x)]
      apply mul_le_mul_of_nonneg_left _ (hP x)
      apply (Finset.abs_sum_le_sum_abs ..).trans
      apply Finset.sum_le_sum; intro i _
      simp only [abs_mul,abs_of_nonneg (conditionalVariance_nonneg P hP x i),abs_spin_eq_one,
        mul_one,abs_of_nonneg (sq_nonneg (halfDiff i f x))]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left
        (coordinate_abs_le_of_square_sum V hC hV x i)
        (mul_nonneg (conditionalVariance_nonneg P hP x i) (sq_nonneg (halfDiff i f x)))
    _ = _ := by
      simp only [varianceEnergy,Finset.mul_sum]
      apply Finset.sum_congr rfl; intro x _
      apply Finset.sum_congr rfl; intro i _; ring

lemma halfDiff_square (i : Fin n) (f : Observables n) (x : Spin n) :
    halfDiff i (fun y=>(f y)^2) x=2*f x*halfDiff i f x-2*spin x i*(halfDiff i f x)^2 := by
  simp only [pow_two,halfDiff_mul]; ring

theorem square_weak_residual_base (P : Spin n→ℝ) (hP : ∀ x,0≤P x)
    (f : Observables n) (U : VectorFields n) {A B : ℝ}
    (hA : 0≤A) (hB : 0≤B)
    (hD : ∀ x,∑ i,|halfDiff i (fun y=>U y i) x|≤A)
    (hU : ∀ x,∑ i,(U x i)^2≤B^2) :
    |∑ x,P x*(f x)^2*∑ i,(spin x i-conditionalMean P x i)*U x i|≤
      (13*A+6*B)*((∑ x,P x*(f x)^2)+varianceEnergy P f) := by
  let V : VectorFields n:=fun x i=>U x i-2*spin x i*halfDiff i (fun y=>U y i) x
  let C:=2*B+4*A
  have hC : 0≤C := by dsimp [C]; positivity
  have hV : ∀ x,∑ i,(V x i)^2≤C^2 := diagonal_reflected_bound U hA hB hD hU
  rw [residual_product_identity P hP (fun x=>(f x)^2) U]
  have hd:=weighted_residual_derivative_bound P hP (fun x=>(f x)^2) U hD
  simp only [abs_pow,sq_abs] at hd
  have he : (∑ x,P x*∑ i,conditionalVariance P x i*halfDiff i (fun y=>(f y)^2) x*V x i)=
      2*(∑ x,P x*∑ i,conditionalVariance P x i*f x*halfDiff i f x*V x i)-
      2*(∑ x,P x*∑ i,conditionalVariance P x i*spin x i*(halfDiff i f x)^2*V x i) := by
    simp only [halfDiff_square,Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro i _; ring
  change |_+(∑ x,P x*∑ i,conditionalVariance P x i*halfDiff i (fun y=>(f y)^2) x*V x i)|≤_
  rw [he]
  have ht:=energy_cross_square_bound P hP f V hC hV
  have hs:=energy_square_coefficient_bound P hP f V hC hV
  have hr:=abs_sub
    (2*(∑ x,P x*∑ i,conditionalVariance P x i*f x*halfDiff i f x*V x i))
    (2*(∑ x,P x*∑ i,conditionalVariance P x i*spin x i*(halfDiff i f x)^2*V x i))
  simp only [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at hr ht
  have hu:=abs_add_le
    (∑ x,P x*(f x)^2*∑ i,conditionalVariance P x i*halfDiff i (fun y=>U y i) x)
    (2*(∑ x,P x*∑ i,conditionalVariance P x i*f x*halfDiff i f x*V x i)-
      2*(∑ x,P x*∑ i,conditionalVariance P x i*spin x i*(halfDiff i f x)^2*V x i))
  have hn:=varianceEnergy_nonneg P hP f
  have hz : 0≤∑ x,P x*(f x)^2 := Finset.sum_nonneg (fun x _=>mul_nonneg (hP x) (sq_nonneg _))
  dsimp only [C] at *
  nlinarith [mul_nonneg hA hn,mul_nonneg (add_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hB)
    (mul_nonneg (by norm_num : (0:ℝ)≤4) hA)) hz]

lemma sum_abs_mul_le_of_squares {ι : Type*} [Fintype ι] (u v : ι→ℝ)
    {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hu : ∑ i,(u i)^2≤A^2) (hv : ∑ i,(v i)^2≤B^2) :
    (∑ i,|u i*v i|)≤A*B := by
  have H:=Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i=>|u i|) (fun i=>|v i|)
  simp only [sq_abs,←abs_mul] at H
  apply (sq_le_sq₀ (Finset.sum_nonneg (fun i _=>abs_nonneg _)) (mul_nonneg hA hB)).1
  rw [mul_pow]
  exact H.trans (mul_le_mul hu hv (Finset.sum_nonneg (fun i _=>sq_nonneg _)) (sq_nonneg _))

lemma multiplier_vector_bounds (U : VectorFields n) (θ : Observables n) {A B H L : ℝ}
    (hA : 0≤A) (hB : 0≤B) (hH : 0≤H) (hL : 0≤L)
    (hD : ∀ x,∑ i,|halfDiff i (fun y=>U y i) x|≤A)
    (hU : ∀ x,∑ i,(U x i)^2≤B^2)
    (hθ : ∀ x,|θ x|≤H) (hdθ : ∀ x,∑ i,(halfDiff i θ x)^2≤L^2) :
    (∀ x,∑ i,|halfDiff i (fun y=>θ y*U y i) x|≤H*A+(2*B+4*A)*L) ∧
    (∀ x,∑ i,(θ x*U x i)^2≤(H*B)^2) := by
  constructor
  · intro x
    have hc:=sum_abs_mul_le_of_squares
      (fun i=>U x i-2*spin x i*halfDiff i (fun y=>U y i) x)
      (fun i=>halfDiff i θ x) (show 0≤2*B+4*A by positivity) hL
      (diagonal_reflected_bound U hA hB hD hU x) (hdθ x)
    have ht : (∑ i,|θ x*halfDiff i (fun y=>U y i) x|)≤H*A := by
      simp only [abs_mul,←Finset.mul_sum]
      exact mul_le_mul (hθ x) (hD x) (Finset.sum_nonneg (fun i _=>abs_nonneg _)) hH
    calc
      _ ≤ ∑ i,(|θ x*halfDiff i (fun y=>U y i) x|+
          |(U x i-2*spin x i*halfDiff i (fun y=>U y i) x)*halfDiff i θ x|) := by
        apply Finset.sum_le_sum; intro i _
        rw [halfDiff_mul]
        convert abs_add_le (θ x*halfDiff i (fun y=>U y i) x)
          ((U x i-2*spin x i*halfDiff i (fun y=>U y i) x)*halfDiff i θ x) using 1
        all_goals try with_reducible_and_instances rfl
        ring_nf
      _ ≤ _ := by rw [Finset.sum_add_distrib]; exact add_le_add ht hc
  · intro x
    simp only [mul_pow,←Finset.mul_sum]
    exact mul_le_mul (by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (θ x)) (hθ x) 2)
      (hU x) (Finset.sum_nonneg (fun i _=>sq_nonneg _)) (sq_nonneg _)

theorem square_multiplier_weak_residual_base (P : Spin n→ℝ) (hP : ∀ x,0≤P x)
    (f θ : Observables n) (U : VectorFields n) {A B H L : ℝ}
    (hA : 0≤A) (hB : 0≤B) (hH : 0≤H) (hL : 0≤L)
    (hD : ∀ x,∑ i,|halfDiff i (fun y=>U y i) x|≤A)
    (hU : ∀ x,∑ i,(U x i)^2≤B^2)
    (hθ : ∀ x,|θ x|≤H) (hdθ : ∀ x,∑ i,(halfDiff i θ x)^2≤L^2) :
    |∑ x,P x*(f x)^2*θ x*∑ i,(spin x i-conditionalMean P x i)*U x i|≤
      (13*(H*A+(2*B+4*A)*L)+6*(H*B))*
        ((∑ x,P x*(f x)^2)+varianceEnergy P f) := by
  obtain ⟨hD',hU'⟩:=multiplier_vector_bounds U θ hA hB hH hL hD hU hθ hdθ
  convert square_weak_residual_base P hP f (fun x i=>θ x*U x i)
    (by positivity) (by positivity) hD' hU' using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply Finset.sum_congr rfl; intro x _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _; ring

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
namespace OrdinaryData

lemma normalizedPrimary_source (D : OrdinaryData n (Fin M) κ σ) (q : Fin M) :
    (D.normalizedPrimary q).source 0=fun x i=>Real.tanh (D.H q x i)/Real.sqrt (n:ℝ) := by
  rw [source_eq]
  ext x i
  simp [sourceOf,normalizedPrimary,seedCoefficient,coefficient,localArgs,div_eq_mul_inv]

lemma normalizedPrimary_magnetization (D : OrdinaryData n (Fin M) κ σ) (q : Fin M)
    (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (hh : D.H q=fld j J h k) :
    (D.normalizedPrimary q).source 0=fun x i=>mag j J h (k+1) x i/Real.sqrt (n:ℝ) := by
  rw [normalizedPrimary_source,hh]
  rfl

lemma normalizedPrimary_Admissible (D : OrdinaryData n (Fin M) κ σ) (q : Fin M)
    (p : ℕ) (hp : p≤q.val) (N : ℕ) : (D.normalizedPrimary q).Admissible N p := by
  intro a ha l hl
  have hne : l≠q := by intro he; subst l; omega
  constructor
  · intro s; ext x i
    simp [seedPartial,localPartial,normalizedPrimary,partialAt,hne.symm]
  · intro b; ext x i
    simp [auxPartial,localPartial,normalizedPrimary,partialAt]

lemma normalizedPrimary_seed (D : OrdinaryData n (Fin M) κ σ) (q : Fin M) (hn : 0<n) :
    (∑s,vectorNorm ((D.normalizedPrimary q).seed s))=1 := by
  simp only [normalizedPrimary,Finset.univ_unique,Finset.sum_singleton]
  apply (sq_eq_sq₀ (vectorNorm_nonneg _) (by norm_num : (0:ℝ)≤1)).mp
  rw [vectorNorm_sq]
  have hs : Real.sqrt (n:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,inv_pow,one_pow]
  rw [Real.sq_sqrt (Nat.cast_nonneg n)]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))

end OrdinaryData

lemma normalized_pair_cancel (hn : 0<n) (R U : VectorFields n) (a : Spin n→ℝ) (x : Spin n) :
    (Real.sqrt (n:ℝ)*a x)*(∑i,R x i*(U x i/Real.sqrt (n:ℝ)))=
      a x*(∑i,R x i*U x i) := by
  have hs : Real.sqrt (n:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))
  simp only [div_eq_mul_inv,←mul_assoc,←Finset.sum_mul]
  field_simp

lemma scaledMean_size (hn : 0<n) (U : VectorFields n) (x : Spin n) {C : ℝ}
    (hC : 0≤C) (hU : vectorNorm (U x)≤C) :
    |Real.sqrt (n:ℝ)*siteMean U x|≤C := by
  apply (sq_le_sq₀ (abs_nonneg _) hC).mp
  rw [sq_abs,mul_pow,Real.sq_sqrt (Nat.cast_nonneg n)]
  exact (siteMean_square U x hn).trans (pow_le_pow_left₀ (vectorNorm_nonneg _) hU 2)

lemma scaledMean_difference (hn : 0<n) (U : VectorFields n) (x : Spin n) {C : ℝ}
    (hC : 0≤C) (hU : ‖derivativeMatrix U x‖≤C) :
    (∑i,(halfDiff i (fun y=>Real.sqrt (n:ℝ)*siteMean U y) x)^2)≤C^2 := by
  have H := (siteMean_derivative_square U x hn).trans
    ((sq_le_sq₀ (norm_nonneg _) hC).2 ((Primary.opNorm_le_frobenius _).trans hU))
  have he (i : Fin n) : halfDiff i (fun y=>Real.sqrt (n:ℝ)*siteMean U y) x=
      Real.sqrt (n:ℝ)*halfDiff i (siteMean U) x := by unfold halfDiff; ring
  simp only [he,mul_pow,Real.sq_sqrt (Nat.cast_nonneg n),←Finset.mul_sum]
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
variable {n : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
lemma tanh_segmentRegular (H : ι→VectorFields n) (θ : κ→Spin n→ℝ) (x : Spin n) (q : ι) :
    SegmentRegular H θ (fun _ u=>Real.tanh (u (.inl q)))
      (fun _ u=>(1-(Real.tanh (u (.inl q)))^2) • ContinuousLinearMap.proj (.inl q)) x 2 := by
  let L : Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ:=ContinuousLinearMap.proj (.inl q)
  have hL : ‖L‖≤1 := by
    apply L.opNorm_le_bound (by norm_num)
    intro u
    exact (norm_le_pi_norm u (.inl q)).trans_eq (by rw [one_mul])
  refine ⟨by norm_num,?_,?_,?_⟩
  · intro i k t ht
    exact (tanh_hasDerivAt _).comp_hasFDerivAt _ L.hasFDerivAt
  · intro i k t ht
    rw [norm_smul,Real.norm_eq_abs]
    have hv : |1-(Real.tanh ((localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i)) (.inl q)))^2|≤1 :=
      (abs_of_pos (scalarVariance_pos _)).trans_le (scalarVariance_le_one _)
    exact (mul_le_mul hv hL (norm_nonneg _) (by norm_num)).trans (by norm_num)
  · intro i k t ht
    let u:=localArgs H θ x i
    let v:=localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i)
    change ‖scalarVariance (v (.inl q)) • L-scalarVariance (u (.inl q)) • L‖≤_
    have he : scalarVariance (v (.inl q)) • L-scalarVariance (u (.inl q)) • L=
        (scalarVariance (v (.inl q))-scalarVariance (u (.inl q))) • L := by module
    rw [he,norm_smul,Real.norm_eq_abs]
    have hv:=scalarVariance_lipschitz (u (.inl q)) (v (.inl q))
    have hu : |v (.inl q)-u (.inl q)|≤‖v-u‖ := norm_le_pi_norm (v-u) (.inl q)
    calc
      _ ≤ 2*|v (.inl q)-u (.inl q)| := (mul_le_mul hv hL (norm_nonneg _) (by positivity)).trans_eq (by ring)
      _ ≤ 2*‖v-u‖ := mul_le_mul_of_nonneg_left hu (by norm_num)
      _ = _ := by dsimp only [u,v]; rw [add_sub_cancel_left]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
lemma tanh_segmentValue (H : ι→VectorFields n) (θ : κ→Spin n→ℝ) (x : Spin n) (q : ι) :
    SegmentValue H θ (fun _ u=>Real.tanh (u (.inl q))) x 2 := by
  intro i k t ht
  exact (Real.abs_tanh_lt_one _).le.trans (by norm_num)

namespace OrdinaryData
variable {M : ℕ} {σ : Type*}
lemma normalizedPrimary_coefficientClass (D : OrdinaryData n (Fin M) κ σ)
    (q : Fin M) (N : ℕ) (x : Spin n) : (D.normalizedPrimary q).CoefficientClass N x 2 := by
  refine ⟨by norm_num,?_,?_,?_,?_⟩
  · intros
    exact tanh_segmentRegular D.H D.θ x q
  · intros
    exact (segmentRegular_const D.H D.θ x 0).mono (by norm_num)
  · intros
    exact tanh_segmentValue D.H D.θ x q
  · intro a ha b i k t ht
    norm_num [normalizedPrimary]
end OrdinaryData
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

lemma starSquared_nonneg (P : Spin n→ℝ) (hP : ∀x,0≤P x) (f : Observables n) :
    0≤ starSquared P f := add_nonneg (Finset.sum_nonneg fun x _=>mul_nonneg (hP x) (sq_nonneg _))
      (varianceEnergy_nonneg P hP f)

lemma halfDiff_mul_flipped (i : Fin n) (θ G : Observables n) (x : Spin n) :
    halfDiff i (fun y=>θ y*G y) x=θ (flip x i)*halfDiff i G x+G x*halfDiff i θ x := by
  rw [halfDiff_mul]
  have h:=flip_sub i θ x
  rw [show θ (flip x i)=θ x-2*spin x i*halfDiff i θ x by linarith]
  ring

lemma multiplier_energy (P : Spin n→ℝ) (hP : ∀x,0≤P x)
    (θ G : Observables n) {B L : ℝ}
    (hB : 0≤B) (hL : 0≤L) (hθ : ∀x,|θ x|≤B)
    (hd : ∀x,∑i,(halfDiff i θ x)^2≤L^2) :
    varianceEnergy P (fun x=>θ x*G x)≤
      2*B^2*varianceEnergy P G+2*L^2*(∑x,P x*(G x)^2) := by
  have ht (x : Spin n) (i : Fin n) : (θ (flip x i))^2≤B^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).2 (hθ (flip x i))
  calc
    _ ≤ ∑x,P x*∑i,conditionalVariance P x i*
        (2*B^2*(halfDiff i G x)^2+2*(G x)^2*(halfDiff i θ x)^2) := by
      apply Finset.sum_le_sum; intro x _
      apply mul_le_mul_of_nonneg_left _ (hP x)
      apply Finset.sum_le_sum; intro i _
      apply mul_le_mul_of_nonneg_left _ (conditionalVariance_nonneg P hP x i)
      rw [halfDiff_mul_flipped]
      have hh:=mul_le_mul_of_nonneg_right (ht x i) (sq_nonneg (halfDiff i G x))
      nlinarith only [hh,sq_nonneg (θ (flip x i)*halfDiff i G x-G x*halfDiff i θ x)]
    _ ≤ ∑x,P x*(2*B^2*(∑i,conditionalVariance P x i*(halfDiff i G x)^2)+2*(G x)^2*L^2) := by
      apply Finset.sum_le_sum; intro x _
      apply mul_le_mul_of_nonneg_left _ (hP x)
      simp only [mul_add,Finset.sum_add_distrib]
      have h1 : (∑i,conditionalVariance P x i*(2*B^2*(halfDiff i G x)^2))=
          2*B^2*(∑i,conditionalVariance P x i*(halfDiff i G x)^2) := by
        simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      rw [h1]
      apply add_le_add_right
      calc
        _ ≤ ∑i,2*(G x)^2*(halfDiff i θ x)^2 := by
          apply Finset.sum_le_sum; intro i _
          exact mul_le_of_le_one_left (by positivity) (conditionalVariance_le_one P x i)
        _ = 2*(G x)^2*(∑i,(halfDiff i θ x)^2) := by rw [Finset.mul_sum]
        _ ≤ _ := by
          simpa only [mul_comm (2*(G x)^2)] using
            mul_le_mul (hd x) (le_refl (2*(G x)^2)) (by positivity) (pow_nonneg hL 2)
    _ = _ := by
      simp only [mul_add,Finset.sum_add_distrib,varianceEnergy,Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro x _ <;> ring_nf

lemma multiplier_starSquared (P : Spin n→ℝ) (hP : ∀x,0≤P x)
    (θ G : Observables n) {B L : ℝ}
    (hB : 0≤B) (hL : 0≤L) (hθ : ∀x,|θ x|≤B)
    (hd : ∀x,∑i,(halfDiff i θ x)^2≤L^2) :
    starSquared P (fun x=>θ x*G x)≤(3*B^2+2*L^2)*starSquared P G := by
  have hs : (∑x,P x*(θ x*G x)^2)≤B^2*(∑x,P x*(G x)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro x _
    have ht : (θ x)^2≤B^2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hθ x) 2
    nlinarith only [mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right ht (sq_nonneg (G x))) (hP x)]
  have he:=multiplier_energy P hP θ G hB hL hθ hd
  have hn:=varianceEnergy_nonneg P hP G
  have hn' : 0≤∑x,P x*(G x)^2 := Finset.sum_nonneg fun x _=>mul_nonneg (hP x) (sq_nonneg _)
  dsimp only [starSquared]
  nlinarith [mul_nonneg (sq_nonneg B) hn,mul_nonneg (sq_nonneg L) hn,
    mul_nonneg (sq_nonneg B) hn']

lemma star_multiplier (P : Spin n→ℝ) (hP : ∀x,0≤P x)
    (θ G : Observables n) {B L : ℝ}
    (hB : 0≤B) (hL : 0≤L) (hθ : ∀x,|θ x|≤B)
    (hd : ∀x,∑i,(halfDiff i θ x)^2≤L^2) :
    starNorm P (fun x=>θ x*G x)≤Real.sqrt (3*B^2+2*L^2)*starNorm P G := by
  exact (Real.sqrt_le_sqrt (multiplier_starSquared P hP θ G hB hL hθ hd)).trans_eq
    (Real.sqrt_mul (by positivity) _)

lemma expected_abs_le_star (P : Spin n→ℝ) (hP : ∀x,0≤P x) (hPsum : ∑x,P x=1)
    (G : Observables n) : (∑x,P x*|G x|)≤ starNorm P G := by
  have hc:=weighted_cauchy_sq P (fun x=>|G x|) (fun _=>1) hP
  simp only [mul_one,one_pow,sq_abs,hPsum] at hc
  have hn : 0≤∑x,P x*|G x| := Finset.sum_nonneg fun x _=>mul_nonneg (hP x) (abs_nonneg _)
  apply (sq_le_sq₀ hn (Real.sqrt_nonneg _)).1
  rw [Real.sq_sqrt (starSquared_nonneg P hP G)]
  exact hc.trans (le_add_of_nonneg_right (varianceEnergy_nonneg P hP G))

lemma sqrt_energy_le_star (P : Spin n→ℝ) (hP : ∀x,0≤P x) (G : Observables n) :
    Real.sqrt (varianceEnergy P G)≤ starNorm P G := by
  apply Real.sqrt_le_sqrt
  exact le_add_of_nonneg_left (Finset.sum_nonneg fun x _=>mul_nonneg (hP x) (sq_nonneg _))

theorem signed_base_star (P : Spin n→ℝ) (hP : ∀x,0≤P x) (hPsum : ∑x,P x=1)
    (G : Observables n) (U : VectorFields n) {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hD : ∀x,∑i,|halfDiff i (fun y=>U y i) x|≤A) (hU : ∀x,∑i,(U x i)^2≤B^2) :
    |∑x,P x*G x*∑i,(spin x i-conditionalMean P x i)*U x i|≤(2*B+5*A)*starNorm P G := by
  have H:=signed_weak_residual_base P hP hPsum G U hA hB hD hU
  have h1:=mul_le_mul_of_nonneg_left (expected_abs_le_star P hP hPsum G) hA
  have h2:=mul_le_mul_of_nonneg_left (sqrt_energy_le_star P hP G) (show 0≤2*B+4*A by positivity)
  linarith

end SKGapCutoff.Static

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Static
open Primary Recipe
universe u
variable {Ω : Type u} {n : Ω→ℕ}

lemma UniformWeak.zero (P : ∀a,Observables (n a)) : UniformWeak P (fun _ _=>0) := by
  refine ⟨0,le_rfl,?_⟩
  simp

lemma UniformWeak.congr {P F F' : ∀a,Observables (n a)} (h : UniformWeak P F)
    (he : ∀a x,F a x=F' a x) : UniformWeak P F' := by
  have : F=F' := funext fun a=>funext (he a)
  rwa [←this]

lemma UniformWeak.add {P F H : ∀a,Observables (n a)} (hF : UniformWeak P F)
    (hH : UniformWeak P H) : UniformWeak P (fun a x=>F a x+H a x) := by
  obtain ⟨C,hC,hF⟩:=hF
  obtain ⟨D,hD,hH⟩:=hH
  refine ⟨C+D,add_nonneg hC hD,fun a G=>?_⟩
  simp only [mul_add,Finset.sum_add_distrib]
  exact (abs_add_le _ _).trans ((add_le_add (hF a G) (hH a G)).trans_eq (by ring))

lemma UniformWeak.neg {P F : ∀a,Observables (n a)} (hF : UniformWeak P F) :
    UniformWeak P (fun a x=>-F a x) := by
  obtain ⟨C,hC,hF⟩:=hF
  refine ⟨C,hC,fun a G=>?_⟩
  simpa using hF a G

lemma UniformWeak.sub {P F H : ∀a,Observables (n a)} (hF : UniformWeak P F)
    (hH : UniformWeak P H) : UniformWeak P (fun a x=>F a x-H a x) := by
  simpa only [sub_eq_add_neg] using hF.add hH.neg

lemma UniformWeak.sum {τ : Type*} [Fintype τ] {P : ∀a,Observables (n a)}
    {F : τ→∀a,Observables (n a)} (h : ∀t,UniformWeak P (F t)) :
    UniformWeak P (fun a x=>∑t,F t a x) := by
  classical
  choose C hC hb using h
  refine ⟨∑t,C t,Finset.sum_nonneg (fun t _=>hC t),fun a G=>?_⟩
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact (Finset.abs_sum_le_sum_abs ..).trans
    ((Finset.sum_le_sum fun t _=>hb t a G).trans_eq (Finset.sum_mul ..).symm)

lemma UniformWeak.mul {P F θ : ∀a,Observables (n a)} (hP : ∀a x,0≤P a x)
    (hF : UniformWeak P F) (hθ : UniformMultiplier θ) :
    UniformWeak P (fun a x=>θ a x*F a x) := by
  obtain ⟨C,hC,hF⟩:=hF
  obtain ⟨B,L,hB,hL,hθ,hd⟩:=hθ
  refine ⟨C*Real.sqrt (3*B^2+2*L^2),by positivity,fun a G=>?_⟩
  have hf:=hF a (fun x=>θ a x*G x)
  have hm:=mul_le_mul_of_nonneg_left (star_multiplier (P a) (hP a) (θ a) G hB hL (hθ a) (hd a)) hC
  calc
    _ = |∑x,P a x*(θ a x*G x)*F a x| := by
      congr 1; apply Finset.sum_congr rfl; intro x _; ring
    _ ≤ C*(Real.sqrt (3*B^2+2*L^2)*starNorm (P a) G) := hf.trans hm
    _ = _ := by ring

lemma UniformMultiplier.const (c : ℝ) : UniformMultiplier (n:=n) (fun _ _=>c) := by
  refine ⟨|c|,0,abs_nonneg _,le_rfl,fun _ _=>le_rfl,?_⟩
  intro a x
  simp [halfDiff]

lemma UniformWeak.smul {P F : ∀a,Observables (n a)} (hP : ∀a x,0≤P a x)
    (hF : UniformWeak P F) (c : ℝ) : UniformWeak P (fun a x=>c*F a x) :=
  hF.mul hP (UniformMultiplier.const c)

lemma UniformWeak.base (P : ∀a,Observables (n a)) (hP : ∀a x,0≤P a x)
    (hp : ∀a,∑x,P a x=1) (U : ∀a,VectorFields (n a))
    {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hD : ∀a x,∑i,|halfDiff i (fun y=>U a y i) x|≤A)
    (hU : ∀a x,vectorNorm (U a x)≤B) :
    UniformWeak P (fun a x=>∑i,(spin x i-conditionalMean (P a) x i)*U a x i) := by
  refine ⟨2*B+5*A,by positivity,fun a G=>?_⟩
  apply signed_base_star (P a) (hP a) (hp a) G (U a) hA hB (hD a)
  intro x
  simpa only [vectorNorm_sq] using pow_le_pow_left₀ (vectorNorm_nonneg _) (hU a x) 2

lemma UniformMultiplier.normedMean (hn : ∀a,0<n a) (U : ∀a,VectorFields (n a))
    {B : ℝ} (hB : 0≤B) (hU : ∀a x,SmallBound (U a) x B) :
    UniformMultiplier (fun a x=>Real.sqrt (n a:ℝ)*siteMean (U a) x) := by
  refine ⟨B,B,hB,hB,fun a x=>scaledMean_size (hn a) _ _ hB (hU a x).size,
    fun a x=>scaledMean_difference (hn a) _ _ hB (hU a x).derivative⟩

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

namespace FamilyRecipe
variable {j : ℝ} {J : ∀a,Interaction (n a)} {h : ∀a,Fin (n a)→ℝ}
variable {D : ∀a,OrdinaryData (n a) (Fin M) (Fin M) σ} {N p : ℕ} {K : ℝ}
lemma mono (H : FamilyRecipe j J h D N p K) {r A : ℕ} {L : ℝ}
    (hr : r≤p) (hA : A≤N) (hK : K≤L) : FamilyRecipe j J h D A r L :=
  ⟨H.interaction,H.coupling,H.primary,H.predecessor,H.parameter,H.seed,
    fun a x=>((H.coefficients a x).prefix hA).mono hK,fun a=>(H.admissible a).prefix hA |>.mono hr⟩

lemma appendStein (H : FamilyRecipe j J h D N p K) (l m α : Fin M)
    (hl : p≤l.val) (hm : p ≤ m.val) {R : ℝ}
    (ht : ∀a x,|(D a).θ α x|≤R) :
    FamilyRecipe j J h (fun a=>(D a).appendStein N l m α) (N+1) p (K+4*steinCoefficientBudget R*K) := by
  refine ⟨H.interaction,H.coupling,H.primary,H.predecessor,H.parameter,H.seed,?_,?_⟩
  · intro a x
    exact (H.coefficients a x).appendStein l m α R (ht a x) (fun k=>ht a (flip x k))
  · intro a; exact (D a).appendStein_Admissible N p l m α hl hm (H.admissible a)

lemma appendAuxiliary (H : FamilyRecipe j J h D N p K) :
    FamilyRecipe j J h (fun a=>(D a).appendAuxiliary N) (N+1) p K :=
  ⟨H.interaction,H.coupling,H.primary,H.predecessor,H.parameter,H.seed,
    fun a x=>(H.coefficients a x).appendAuxiliary,
    fun a=>(D a).appendAuxiliary_Admissible N p (H.admissible a)⟩

lemma normalizedPrimary (H : FamilyRecipe j J h D N p K) (hn : ∀a,0<n a)
    (q : Fin M) (r : ℕ) (hr : r≤q.val) :
    FamilyRecipe j J h (fun a=>(D a).normalizedPrimary q) 0 r 2 := by
  refine ⟨H.interaction,H.coupling,H.primary,H.predecessor,H.parameter,
    ⟨1,by norm_num,fun a=>le_of_eq ((D a).normalizedPrimary_seed q (hn a))⟩,
    fun a x=>(D a).normalizedPrimary_coefficientClass q 0 x,
    fun a=>(D a).normalizedPrimary_Admissible q r hr 0⟩

end FamilyRecipe
end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
universe u
variable {Ω : Type u} {n : Ω→ℕ}
lemma UniformMultiplier.congr {F H : ∀a,Observables (n a)} (hF : UniformMultiplier F)
    (he : ∀a x,F a x=H a x) : UniformMultiplier H := by
  have : F=H:=funext fun a=>funext (he a)
  rwa [←this]
lemma UniformMultiplier.add {F H : ∀a,Observables (n a)} (hF : UniformMultiplier F)
    (hH : UniformMultiplier H) : UniformMultiplier (fun a x=>F a x+H a x) := by
  obtain ⟨B,L,hB,hL,hF,hdF⟩:=hF
  obtain ⟨C,K,hC,hK,hH,hdH⟩:=hH
  refine ⟨B+C,Real.sqrt (2*L^2+2*K^2),add_nonneg hB hC,Real.sqrt_nonneg _,
    fun a x=>(abs_add_le _ _).trans (add_le_add (hF a x) (hH a x)),fun a x=>?_⟩
  rw [Real.sq_sqrt (by positivity)]
  have he (i : Fin (n a)) : halfDiff i (fun y=>F a y+H a y) x=halfDiff i (F a) x+halfDiff i (H a) x := by
    unfold halfDiff; ring
  simp only [he]
  calc
    _ ≤ ∑i,(2*(halfDiff i (F a) x)^2+2*(halfDiff i (H a) x)^2) := by
      apply Finset.sum_le_sum; intro i _; nlinarith [sq_nonneg (halfDiff i (F a) x-halfDiff i (H a) x)]
    _ = 2*(∑i,(halfDiff i (F a) x)^2)+2*(∑i,(halfDiff i (H a) x)^2) := by
      simp only [Finset.sum_add_distrib,Finset.mul_sum]
    _ ≤ _ := by linarith [hdF a x,hdH a x]
lemma UniformMultiplier.finset_sum {τ : Type*} {F : τ→∀a,Observables (n a)} (s : Finset τ)
    (h : ∀t∈s,UniformMultiplier (F t)) : UniformMultiplier (fun a x=>∑t∈s,F t a x) := by
  classical
  induction s using Finset.induction_on with
  | empty=>simpa using (UniformMultiplier.const (n:=n) 0)
  | @insert t s ht ih=>
    simpa only [Finset.sum_insert ht] using (h t (Finset.mem_insert_self ..)).add
      (ih (fun r hr=>h r (Finset.mem_insert_of_mem hr)))
end SKGapCutoff.Static
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
lemma onsager_parameter_bound (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) :
    |j*(onsager j J h (k+1) x-onsager j J h k x)|≤|j| := by
  have H:=onsager_bounds j J h k x
  have H':=onsager_bounds j J h (k+1) x
  rw [abs_mul]
  simpa using mul_le_mul_of_nonneg_left (show |onsager j J h (k+1) x-onsager j J h k x|≤1 from
    abs_le.mpr ⟨by linarith,by linarith⟩) (abs_nonneg j)
lemma onsager_telescope (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) :
    (∑q∈Finset.range k,j*(onsager j J h (q+1) x-onsager j J h q x))=j*onsager j J h k x := by
  induction k with
  | zero=>simp [onsager_zero]
  | succ k ih=>rw [Finset.sum_range_succ,ih]; ring
end SKGapCutoff.Primary

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

lemma wordBounded_mono {A B : ℝ} {u : OrdinaryWord n} (h : wordBounded A u) (hab : A≤B) :
    wordBounded B u := by
  intro l hl; cases l with
  | noise=>trivial
  | diag p=>exact fun i=>(h (.diag p) hl i).trans hab

end SKGapCutoff.Recipe

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
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static
universe u
variable {Ω : Type u} {n : Ω→ℕ} {M Nmax : ℕ} {A j : ℝ}
variable {J : ∀a,Interaction (n a)} {h : ∀a,Fin (n a)→ℝ}

lemma FiniteRecipeControl.onsager_multiplier (H : FiniteRecipeControl j J h M Nmax A) (k : ℕ) (hk : k≤M) :
    UniformMultiplier (fun a x=>j*onsager j (J a) (h a) k x) := by
  have hh : UniformMultiplier (fun a x=>∑q∈Finset.range k,
      j*(onsager j (J a) (h a) (q+1) x-onsager j (J a) (h a) q x)) := by
    apply UniformMultiplier.finset_sum
    intro q hq
    exact H.parameter ⟨q,(Finset.mem_range.mp hq).trans_le hk⟩
  exact hh.congr (fun a x=>onsager_telescope j (J a) (h a) k x)

lemma uniform_normalized_pair (P : ∀a,Observables (n a)) (hP : ∀a x,0≤P a x)
    (hn : ∀a,0<n a) (R U V : ∀a,VectorFields (n a))
    (hV : UniformWeak P (fun a x=>∑i,R a x i*(V a x i/Real.sqrt (n a:ℝ))))
    {C : ℝ} (hC : 0≤C) (hU : ∀a x,SmallBound (U a) x C) :
    UniformWeak P (fun a x=>siteMean (U a) x*(∑i,R a x i*V a x i)) := by
  exact (hV.mul hP (UniformMultiplier.normedMean hn U hC hU)).congr
    (fun a x=>normalized_pair_cancel (hn a) (R a) (V a) (siteMean (U a)) x)

lemma uniform_prev_zero (P : ∀a,Observables (n a)) (U : ∀a,VectorFields (n a)) :
    UniformWeak P (fun a x=>∑i,previousResidual j (J a) (h a) 0 x i*U a x i) := by
  convert UniformWeak.zero P using 1
  all_goals try with_reducible_and_instances rfl
  ext a x
  simp [previousResidual]

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static
universe u
variable {Ω : Type u} {n : Ω→ℕ} {M Nmax : ℕ} {A j : ℝ}
variable {J : ∀a,Interaction (n a)} {h : ∀a,Fin (n a)→ℝ}
variable {P : ∀a,Observables (n a)}

lemma residual_rule_base (C : FiniteRecipeControl j J h M Nmax A)
    (hP : ∀a x,0≤P a x) (hp : ∀a,∑x,P a x=1)
    (hm : ∀a x i,conditionalMean (P a) x i=mag j (J a) (h a) 1 x i)
    (B : ℝ) (hB : B≤A) : RecipeResidualRule j J h P M Nmax 0 B := by
  intro σ inst D N H hN
  obtain ⟨K,hK,hbound⟩:=C.small D N 0 B H (by omega) hB
  have hh:=UniformWeak.base P hP hp (fun a=>(D a).source N) hK hK
    (fun a x=>(hbound a x).2.2) (fun a x=>(hbound a x).1.size)
  apply hh.congr
  intro a x
  simp only [Primary.residual,mag_zero,hm]

lemma residual_rule_step (C : FiniteRecipeControl j J h M Nmax A)
    (hP : ∀a x,0≤P a x) (hn : ∀a,0<n a) (hJ : ∀a,(J a).IsSymm)
    (b : ℕ→ℝ) (hmono : Antitone b) (k : ℕ) (hkM : k+1<M)
    (hkA : b k≤A) (hk2 : 2≤b k)
    (hstep : b (k+1)+4*steinCoefficientBudget |j| *b (k+1)≤b k)
    (ih : ∀r<k+1,RecipeResidualRule j J h P M Nmax r (b r)) :
    RecipeResidualRule j J h P M Nmax (k+1) (b (k+1)) := by
  intro σ inst D N H hN
  let l : Fin M:=⟨k,by omega⟩
  let m : Fin M:=⟨k+1,hkM⟩
  have hlm : l≠m := by intro he; have hv:=congrArg Fin.val he; dsimp [l,m] at hv; omega
  let E:=fun a=>(D a).appendStein N l m l
  have HE : FamilyRecipe j J h E (N+1) k (b k) := by
    have HH:=(H.mono (show k≤k+1 by omega) le_rfl le_rfl).appendStein l m l le_rfl
      (show k ≤ m.val by dsimp [m]; omega)
      (R:=|j|) (fun a x=>by rw [H.parameter a l]; exact onsager_parameter_bound j (J a) (h a) k x)
    exact HH.mono le_rfl le_rfl hstep
  have hEN : N+1+2*k≤Nmax := by omega
  have source : UniformWeak P (fun a x=>∑i,residual j (J a) (h a) k x i*(E a).source (N+1) x i) :=
    ih k (by omega) E (N+1) HE hEN
  have aux : UniformWeak P (fun a x=>∑i,residual j (J a) (h a) k x i*(E a).auxiliary (N+1) x i) := by
    have HH:=ih k (by omega) (fun a=>(E a).appendAuxiliary (N+1)) (N+1+1)
      HE.appendAuxiliary (by omega)
    exact HH.congr (fun a x=>by rw [OrdinaryData.appendAuxiliary_source])
  have param := source.mul hP (C.parameter l)
  have prev : UniformWeak P (fun a x=>∑i,previousResidual j (J a) (h a) k x i*(E a).source (N+1) x i) := by
    cases k with
    | zero=>exact uniform_prev_zero P (fun a=>(E a).source (N+1))
    | succ r=>
      have HH:=ih r (by omega) E (N+1) (HE.mono (by omega) le_rfl (hmono (by omega))) (by omega)
      exact HH.congr (fun a x=>by simp only [previousResidual,Primary.residual,Nat.add_sub_cancel])
  have old:=prev.mul hP (C.onsager_multiplier k (by omega))
  have earlier : UniformWeak P (fun a x=>j*(∑t:Fin (N+1),siteMean ((E a).auxCoefficient (N+1) t) x*
      (∑i,residual j (J a) (h a) k x i*(E a).source t.val x i))) := by
    apply UniformWeak.smul hP _ j
    apply UniformWeak.sum
    intro t
    exact (ih k (by omega) E t.val (HE.mono le_rfl t.isLt.le le_rfl) (by omega)).mul hP
      (C.means E (N+1) k (b k) HE (by omega) hkA t)
  obtain ⟨V,hV,hbound⟩:=C.small E (N+1) k (b k) HE (by omega) hkA
  have primary (q : Fin M) (hr : k≤q.val) :
      UniformWeak P (fun a x=>∑i,residual j (J a) (h a) k x i*
        (mag j (J a) (h a) (q.val+1) x i/Real.sqrt (n a:ℝ))) := by
    have HQ:=(HE.normalizedPrimary hn q k hr).mono le_rfl le_rfl hk2
    have HH:=ih k (by omega) (fun a=>(E a).normalizedPrimary q) 0 HQ (by omega)
    exact HH.congr (fun a x=>by rw [OrdinaryData.normalizedPrimary_magnetization _ _ j (J a) (h a) q.val (HE.primary a q)])
  have future : UniformWeak P (fun a x=>j*(∑q:{q:Fin M//q≠l},siteMean ((E a).sourcePartial (N+1) q) x*
      (∑i,residual j (J a) (h a) k x i*mag j (J a) (h a) q.val.val x i))) := by
    apply UniformWeak.smul hP _ j
    apply UniformWeak.sum
    intro q
    by_cases hq : q.val.val<k
    · apply (UniformWeak.zero P).congr
      intro a x
      rw [(HE.admissible a).sourcePartial (N+1) le_rfl q.val hq]
      simp [siteMean]
    · have hne : q.val.val≠k := by
        intro he
        exact q.property (Fin.ext he)
      have hq' : k<q.val.val := by omega
      let r : Fin M:=⟨q.val.val-1,by omega⟩
      have hr : r.val+1=q.val.val := by dsimp [r]; omega
      have HH:=uniform_normalized_pair P hP hn (fun a=>residual j (J a) (h a) k)
        (fun a=>(E a).sourcePartial (N+1) q.val) (fun a=>mag j (J a) (h a) (r.val+1))
        (primary r (by dsimp [r]; omega)) hV (fun a x=>(hbound a x).2.1 q.val)
      simpa only [hr] using HH
  have last : UniformWeak P (fun a x=>j*(siteMean ((E a).sourcePartial (N+1) l) x*
      (∑i,residual j (J a) (h a) k x i*mag j (J a) (h a) (k+1) x i))) := by
    apply UniformWeak.smul hP _ j
    exact uniform_normalized_pair P hP hn (fun a=>residual j (J a) (h a) k)
      (fun a=>(E a).sourcePartial (N+1) l) (fun a=>mag j (J a) (h a) (k+1))
      (primary l le_rfl) hV (fun a x=>(hbound a x).2.1 l)
  apply ((((aux.add param).sub old).add earlier).add future).sub last |>.congr
  intro a x
  have hid:=(D a).residual_step N l m l hlm (hn a) j (J a) (hJ a) (h a) k Fin.val
    (H.coupling a) (H.interaction a) (H.predecessor a) rfl (H.primary a l) (H.primary a m)
    (H.parameter a l) ((H.admissible a).sourcePartial N le_rfl l (by dsimp [l]; omega)) x
  dsimp only at hid
  rw [hid]
  dsimp only [E,l]
  ring

end SKGapCutoff.Recipe

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
namespace SKGapCutoff.Recipe
open Primary Static
universe u
variable {Ω : Type u} {n : Ω→ℕ} {M Nmax : ℕ} {A j : ℝ}
variable {J : ∀a,Interaction (n a)} {h : ∀a,Fin (n a)→ℝ}
variable {P : ∀a,Observables (n a)}

theorem uniform_residual_rule (C : FiniteRecipeControl j J h M Nmax A)
    (hP : ∀a x,0≤P a x) (hp : ∀a,∑x,P a x=1)
    (hm : ∀a x i,conditionalMean (P a) x i=mag j (J a) (h a) 1 x i)
    (hn : ∀a,0<n a) (hJ : ∀a,(J a).IsSymm)
    (b : ℕ→ℝ) (hmono : Antitone b) (pmax : ℕ) (hM : pmax<M)
    (hA : ∀p≤pmax,b p≤A) (h2 : ∀p≤pmax,2≤b p)
    (hstep : ∀k<pmax,b (k+1)+4*steinCoefficientBudget |j| *b (k+1)≤b k) :
    ∀p≤pmax,RecipeResidualRule j J h P M Nmax p (b p) := by
  intro p
  induction p using Nat.strong_induction_on with
  | h p ih=>
    intro hpmax
    cases p with
    | zero=>exact residual_rule_base C hP hp hm (b 0) (hA 0 hpmax)
    | succ k=>
      exact residual_rule_step C hP hn hJ b hmono k (hpmax.trans_lt hM)
        (hA k (by omega)) (h2 k (by omega)) (hstep k (by omega))
        (fun r hr=>ih r hr (by omega))

lemma residualCoefficientBudget_antitone (j : ℝ) {K : ℝ} (hK : 0≤K) (t : ℕ) :
    Antitone (residualCoefficientBudget j K t) := by
  intro p q hpq
  apply mul_le_mul_of_nonneg_left _ hK
  exact pow_le_pow_right₀ (by linarith [steinCoefficientBudget_nonneg |j|]) (Nat.sub_le_sub_left hpq t)
lemma residualCoefficientBudget_ge (j : ℝ) {K : ℝ} (hK : 0≤K) (t p : ℕ) :
    K ≤ residualCoefficientBudget j K t p := by
  simpa only [mul_one,residualCoefficientBudget] using mul_le_mul_of_nonneg_left
    (one_le_pow₀ (by linarith [steinCoefficientBudget_nonneg |j|]) :
      1≤(1+4*steinCoefficientBudget |j|)^(t-p)) hK
lemma residualCoefficientBudget_step (j K : ℝ) {t k : ℕ} (hk : k<t) :
    residualCoefficientBudget j K t (k+1)+4*steinCoefficientBudget |j| *residualCoefficientBudget j K t (k+1)=
      residualCoefficientBudget j K t k := by
  have he : t-k=(t-(k+1))+1 := by omega
  dsimp only [residualCoefficientBudget]
  rw [he,pow_succ]
  ring

theorem uniform_ordinary_weak_residual (p N : ℕ) {K : ℝ} (hK : 2≤K) (hM : p<M)
    (C : FiniteRecipeControl j J h M (N+2*p) (residualCoefficientBudget j K p 0))
    (hP : ∀a x,0≤P a x) (hp : ∀a,∑x,P a x=1)
    (hm : ∀a x i,conditionalMean (P a) x i=mag j (J a) (h a) 1 x i)
    (hn : ∀a,0<n a) (hJ : ∀a,(J a).IsSymm)
    {σ : Type} [Fintype σ] (D : ∀a,OrdinaryData (n a) (Fin M) (Fin M) σ)
    (H : FamilyRecipe j J h D N p K) :
    UniformWeak P (fun a x=>∑i,residual j (J a) (h a) p x i*(D a).source N x i) := by
  have hK0 : 0≤K := by linarith
  have hb:=residualCoefficientBudget_antitone j hK0 p
  have HH:=uniform_residual_rule C hP hp hm hn hJ (residualCoefficientBudget j K p) hb p hM
    (fun r _=>hb (Nat.zero_le r)) (fun r _=>hK.trans (residualCoefficientBudget_ge j hK0 p r))
    (fun k hk=>le_of_eq (residualCoefficientBudget_step j K hk)) p le_rfl D N
  apply HH _ le_rfl
  simpa [residualCoefficientBudget] using H

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
open Primary Recipe
universe u
variable {Ω : Type u} {n : Ω→ℕ}

lemma UniformSquare.zero (P : ∀a,Observables (n a)) : UniformSquare P (fun _ _=>0) := by
  intro B L hB hL
  exact ⟨0,le_rfl,by simp⟩
lemma UniformSquare.congr {P F H : ∀a,Observables (n a)} (hF : UniformSquare P F)
    (he : ∀a x,F a x=H a x) : UniformSquare P H := by
  have : F=H:=funext fun a=>funext (he a)
  rwa [←this]
lemma UniformSquare.add {P F H : ∀a,Observables (n a)} (hF : UniformSquare P F)
    (hH : UniformSquare P H) : UniformSquare P (fun a x=>F a x+H a x) := by
  intro B L hB hL
  obtain ⟨C,hC,hF⟩:=hF B L hB hL
  obtain ⟨D,hD,hH⟩:=hH B L hB hL
  refine ⟨C+D,add_nonneg hC hD,fun a f θ ht hd=>?_⟩
  simp only [mul_add,Finset.sum_add_distrib]
  exact (abs_add_le _ _).trans ((add_le_add (hF a f θ ht hd) (hH a f θ ht hd)).trans_eq (by ring))
lemma UniformSquare.neg {P F : ∀a,Observables (n a)} (hF : UniformSquare P F) :
    UniformSquare P (fun a x=>-F a x) := by
  intro B L hB hL
  obtain ⟨C,hC,hF⟩:=hF B L hB hL
  refine ⟨C,hC,fun a f θ ht hd=>?_⟩
  simpa using hF a f θ ht hd
lemma UniformSquare.sub {P F H : ∀a,Observables (n a)} (hF : UniformSquare P F)
    (hH : UniformSquare P H) : UniformSquare P (fun a x=>F a x-H a x) := by
  simpa only [sub_eq_add_neg] using hF.add hH.neg
lemma UniformSquare.sum {τ : Type*} [Fintype τ] {P : ∀a,Observables (n a)}
    {F : τ→∀a,Observables (n a)} (h : ∀t,UniformSquare P (F t)) :
    UniformSquare P (fun a x=>∑t,F t a x) := by
  classical
  intro B L hB hL
  choose C hC hb using (fun t=>h t B L hB hL)
  refine ⟨∑t,C t,Finset.sum_nonneg (fun t _=>hC t),fun a f θ ht hd=>?_⟩
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact (Finset.abs_sum_le_sum_abs ..).trans
    ((Finset.sum_le_sum fun t _=>hb t a f θ ht hd).trans_eq (Finset.sum_mul ..).symm)

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

lemma UniformSquare.mul {P F η : ∀a,Observables (n a)} (_ : ∀a x,0≤P a x)
    (hF : UniformSquare P F) (hη : UniformMultiplier η) :
    UniformSquare P (fun a x=>η a x*F a x) := by
  obtain ⟨D,K,hD,hK,he,hde⟩:=hη
  intro B L hB hL
  obtain ⟨C,hC,hF⟩:=hF (B*D) (Real.sqrt (2*B^2*K^2+2*D^2*L^2))
    (mul_nonneg hB hD) (Real.sqrt_nonneg _)
  refine ⟨C,hC,fun a f θ ht hd=>?_⟩
  obtain ⟨h1,h2⟩:=scalar_product_bounds θ (η a) hB hL hD hK ht hd (he a) (hde a)
  convert hF a f (fun x=>θ x*η a x) h1 h2 using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply Finset.sum_congr rfl; intro x _; ring
lemma UniformSquare.smul {P F : ∀a,Observables (n a)} (hP : ∀a x,0≤P a x)
    (hF : UniformSquare P F) (c : ℝ) : UniformSquare P (fun a x=>c*F a x) :=
  hF.mul hP (UniformMultiplier.const c)

lemma UniformSquare.base (P : ∀a,Observables (n a)) (hP : ∀a x,0≤P a x)
    (U : ∀a,VectorFields (n a)) {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hD : ∀a x,∑i,|halfDiff i (fun y=>U a y i) x|≤A)
    (hU : ∀a x,vectorNorm (U a x)≤B) :
    UniformSquare P (fun a x=>∑i,(spin x i-conditionalMean (P a) x i)*U a x i) := by
  intro H L hH hL
  refine ⟨13*(H*A+(2*B+4*A)*L)+6*(H*B),by positivity,fun a f θ ht hd=>?_⟩
  apply square_multiplier_weak_residual_base (P a) (hP a) f θ (U a) hA hB hH hL (hD a) _ ht hd
  intro x
  simpa only [vectorNorm_sq] using pow_le_pow_left₀ (vectorNorm_nonneg _) (hU a x) 2

end SKGapCutoff.Static
namespace SKGapCutoff.Recipe
open Primary Static
universe u
variable {Ω : Type u} {n : Ω→ℕ} {j : ℝ} {J : ∀a,Interaction (n a)} {h : ∀a,Fin (n a)→ℝ}
lemma uniform_square_normalized_pair (P : ∀a,Observables (n a)) (hP : ∀a x,0≤P a x)
    (hn : ∀a,0<n a) (R U V : ∀a,VectorFields (n a))
    (hV : UniformSquare P (fun a x=>∑i,R a x i*(V a x i/Real.sqrt (n a:ℝ))))
    {C : ℝ} (hC : 0≤C) (hU : ∀a x,SmallBound (U a) x C) :
    UniformSquare P (fun a x=>siteMean (U a) x*(∑i,R a x i*V a x i)) := by
  exact (hV.mul hP (UniformMultiplier.normedMean hn U hC hU)).congr
    (fun a x=>normalized_pair_cancel (hn a) (R a) (V a) (siteMean (U a)) x)
lemma uniform_square_prev_zero (P : ∀a,Observables (n a)) (U : ∀a,VectorFields (n a)) :
    UniformSquare P (fun a x=>∑i,previousResidual j (J a) (h a) 0 x i*U a x i) := by
  convert UniformSquare.zero P using 1
  all_goals try with_reducible_and_instances rfl
  ext a x
  simp [previousResidual]
end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_UniformSquareInduction
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
variable {Ω : Type u} {n : Ω→ℕ} {M Nmax : ℕ} {A j : ℝ}
variable {J : ∀a,Interaction (n a)} {h : ∀a,Fin (n a)→ℝ}
variable {P : ∀a,Observables (n a)}

lemma residual_square_rule_base (C : FiniteRecipeControl j J h M Nmax A)
    (hP : ∀a x,0≤P a x) (_ : ∀a,∑x,P a x=1)
    (hm : ∀a x i,conditionalMean (P a) x i=mag j (J a) (h a) 1 x i)
    (B : ℝ) (hB : B≤A) : RecipeSquareResidualRule j J h P M Nmax 0 B := by
  intro σ inst D N H hN
  obtain ⟨K,hK,hbound⟩:=C.small D N 0 B H (by omega) hB
  have hh:=UniformSquare.base P hP (fun a=>(D a).source N) hK hK
    (fun a x=>(hbound a x).2.2) (fun a x=>(hbound a x).1.size)
  apply hh.congr
  intro a x
  simp only [Primary.residual,mag_zero,hm]

lemma residual_square_rule_step (C : FiniteRecipeControl j J h M Nmax A)
    (hP : ∀a x,0≤P a x) (hn : ∀a,0<n a) (hJ : ∀a,(J a).IsSymm)
    (b : ℕ→ℝ) (hmono : Antitone b) (k : ℕ) (hkM : k+1<M)
    (hkA : b k≤A) (hk2 : 2≤b k)
    (hstep : b (k+1)+4*steinCoefficientBudget |j| *b (k+1)≤b k)
    (ih : ∀r<k+1,RecipeSquareResidualRule j J h P M Nmax r (b r)) :
    RecipeSquareResidualRule j J h P M Nmax (k+1) (b (k+1)) := by
  intro σ inst D N H hN
  let l : Fin M:=⟨k,by omega⟩
  let m : Fin M:=⟨k+1,hkM⟩
  have hlm : l≠m := by intro he; have hv:=congrArg Fin.val he; dsimp [l,m] at hv; omega
  let E:=fun a=>(D a).appendStein N l m l
  have HE : FamilyRecipe j J h E (N+1) k (b k) := by
    have HH:=(H.mono (show k≤k+1 by omega) le_rfl le_rfl).appendStein l m l le_rfl
      (show k ≤ m.val by dsimp [m]; omega)
      (R:=|j|) (fun a x=>by rw [H.parameter a l]; exact onsager_parameter_bound j (J a) (h a) k x)
    exact HH.mono le_rfl le_rfl hstep
  have hEN : N+1+2*k≤Nmax := by omega
  have source : UniformSquare P (fun a x=>∑i,residual j (J a) (h a) k x i*(E a).source (N+1) x i) :=
    ih k (by omega) E (N+1) HE hEN
  have aux : UniformSquare P (fun a x=>∑i,residual j (J a) (h a) k x i*(E a).auxiliary (N+1) x i) := by
    have HH:=ih k (by omega) (fun a=>(E a).appendAuxiliary (N+1)) (N+1+1)
      HE.appendAuxiliary (by omega)
    exact HH.congr (fun a x=>by rw [OrdinaryData.appendAuxiliary_source])
  have param := source.mul hP (C.parameter l)
  have prev : UniformSquare P (fun a x=>∑i,previousResidual j (J a) (h a) k x i*(E a).source (N+1) x i) := by
    cases k with
    | zero=>exact uniform_square_prev_zero P (fun a=>(E a).source (N+1))
    | succ r=>
      have HH:=ih r (by omega) E (N+1) (HE.mono (by omega) le_rfl (hmono (by omega))) (by omega)
      exact HH.congr (fun a x=>by simp only [previousResidual,Primary.residual,Nat.add_sub_cancel])
  have old:=prev.mul hP (C.onsager_multiplier k (by omega))
  have earlier : UniformSquare P (fun a x=>j*(∑t:Fin (N+1),siteMean ((E a).auxCoefficient (N+1) t) x*
      (∑i,residual j (J a) (h a) k x i*(E a).source t.val x i))) := by
    apply UniformSquare.smul hP _ j
    apply UniformSquare.sum
    intro t
    exact (ih k (by omega) E t.val (HE.mono le_rfl t.isLt.le le_rfl) (by omega)).mul hP
      (C.means E (N+1) k (b k) HE (by omega) hkA t)
  obtain ⟨V,hV,hbound⟩:=C.small E (N+1) k (b k) HE (by omega) hkA
  have primary (q : Fin M) (hr : k≤q.val) :
      UniformSquare P (fun a x=>∑i,residual j (J a) (h a) k x i*
        (mag j (J a) (h a) (q.val+1) x i/Real.sqrt (n a:ℝ))) := by
    have HQ:=(HE.normalizedPrimary hn q k hr).mono le_rfl le_rfl hk2
    have HH:=ih k (by omega) (fun a=>(E a).normalizedPrimary q) 0 HQ (by omega)
    exact HH.congr (fun a x=>by rw [OrdinaryData.normalizedPrimary_magnetization _ _ j (J a) (h a) q.val (HE.primary a q)])
  have future : UniformSquare P (fun a x=>j*(∑q:{q:Fin M//q≠l},siteMean ((E a).sourcePartial (N+1) q) x*
      (∑i,residual j (J a) (h a) k x i*mag j (J a) (h a) q.val.val x i))) := by
    apply UniformSquare.smul hP _ j
    apply UniformSquare.sum
    intro q
    by_cases hq : q.val.val<k
    · apply (UniformSquare.zero P).congr
      intro a x
      rw [(HE.admissible a).sourcePartial (N+1) le_rfl q.val hq]
      simp [siteMean]
    · have hne : q.val.val≠k := by
        intro he
        exact q.property (Fin.ext he)
      have hq' : k<q.val.val := by omega
      let r : Fin M:=⟨q.val.val-1,by omega⟩
      have hr : r.val+1=q.val.val := by dsimp [r]; omega
      have HH:=uniform_square_normalized_pair P hP hn (fun a=>residual j (J a) (h a) k)
        (fun a=>(E a).sourcePartial (N+1) q.val) (fun a=>mag j (J a) (h a) (r.val+1))
        (primary r (by dsimp [r]; omega)) hV (fun a x=>(hbound a x).2.1 q.val)
      simpa only [hr] using HH
  have last : UniformSquare P (fun a x=>j*(siteMean ((E a).sourcePartial (N+1) l) x*
      (∑i,residual j (J a) (h a) k x i*mag j (J a) (h a) (k+1) x i))) := by
    apply UniformSquare.smul hP _ j
    exact uniform_square_normalized_pair P hP hn (fun a=>residual j (J a) (h a) k)
      (fun a=>(E a).sourcePartial (N+1) l) (fun a=>mag j (J a) (h a) (k+1))
      (primary l le_rfl) hV (fun a x=>(hbound a x).2.1 l)
  apply ((((aux.add param).sub old).add earlier).add future).sub last |>.congr
  intro a x
  have hid:=(D a).residual_step N l m l hlm (hn a) j (J a) (hJ a) (h a) k Fin.val
    (H.coupling a) (H.interaction a) (H.predecessor a) rfl (H.primary a l) (H.primary a m)
    (H.parameter a l) ((H.admissible a).sourcePartial N le_rfl l (by dsimp [l]; omega)) x
  dsimp only at hid
  rw [hid]
  dsimp only [E,l]
  ring

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static
universe u
variable {Ω : Type u} {n : Ω→ℕ} {M Nmax : ℕ} {A j : ℝ}
variable {J : ∀a,Interaction (n a)} {h : ∀a,Fin (n a)→ℝ}
variable {P : ∀a,Observables (n a)}

theorem uniform_residual_square_rule (C : FiniteRecipeControl j J h M Nmax A)
    (hP : ∀a x,0≤P a x) (hp : ∀a,∑x,P a x=1)
    (hm : ∀a x i,conditionalMean (P a) x i=mag j (J a) (h a) 1 x i)
    (hn : ∀a,0<n a) (hJ : ∀a,(J a).IsSymm)
    (b : ℕ→ℝ) (hmono : Antitone b) (pmax : ℕ) (hM : pmax<M)
    (hA : ∀p≤pmax,b p≤A) (h2 : ∀p≤pmax,2≤b p)
    (hstep : ∀k<pmax,b (k+1)+4*steinCoefficientBudget |j| *b (k+1)≤b k) :
    ∀p≤pmax,RecipeSquareResidualRule j J h P M Nmax p (b p) := by
  intro p
  induction p using Nat.strong_induction_on with
  | h p ih=>
    intro hpmax
    cases p with
    | zero=>exact residual_square_rule_base C hP hp hm (b 0) (hA 0 hpmax)
    | succ k=>
      exact residual_square_rule_step C hP hn hJ b hmono k (hpmax.trans_lt hM)
        (hA k (by omega)) (h2 k (by omega)) (hstep k (by omega))
        (fun r hr=>ih r hr (by omega))

theorem uniform_ordinary_square_residual (p N : ℕ) {K : ℝ} (hK : 2≤K) (hM : p<M)
    (C : FiniteRecipeControl j J h M (N+2*p) (residualCoefficientBudget j K p 0))
    (hP : ∀a x,0≤P a x) (hp : ∀a,∑x,P a x=1)
    (hm : ∀a x i,conditionalMean (P a) x i=mag j (J a) (h a) 1 x i)
    (hn : ∀a,0<n a) (hJ : ∀a,(J a).IsSymm)
    {σ : Type} [Fintype σ] (D : ∀a,OrdinaryData (n a) (Fin M) (Fin M) σ)
    (H : FamilyRecipe j J h D N p K) :
    UniformSquare P (fun a x=>∑i,residual j (J a) (h a) p x i*(D a).source N x i) := by
  have hK0 : 0≤K := by linarith
  have hb:=residualCoefficientBudget_antitone j hK0 p
  have HH:=uniform_residual_square_rule C hP hp hm hn hJ (residualCoefficientBudget j K p) hb p hM
    (fun r _=>hb (Nat.zero_le r)) (fun r _=>hK.trans (residualCoefficientBudget_ge j hK0 p r))
    (fun k hk=>le_of_eq (residualCoefficientBudget_step j K hk)) p le_rfl D N
  apply HH _ le_rfl
  simpa [residualCoefficientBudget] using H

end SKGapCutoff.Recipe

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
open scoped BigOperators
namespace SKGapCutoff
variable {n : ℕ}

lemma fieldPartition_pos (J : Interaction n) (h : Fin n→ℝ) : 0<fieldPartition J h :=
  Finset.sum_pos (fun _ _=>Real.exp_pos _) Finset.univ_nonempty
lemma fieldGibbs_pos (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) : 0<fieldGibbs J h x :=
  div_pos (Real.exp_pos _) (fieldPartition_pos J h)
lemma sum_fieldGibbs (J : Interaction n) (h : Fin n→ℝ) : ∑x,fieldGibbs J h x=1 := by
  simp only [fieldGibbs,←Finset.sum_div]
  change fieldPartition J h/fieldPartition J h=1
  exact div_self (ne_of_gt (fieldPartition_pos J h))

lemma fieldEnergy_flip (J : Interaction n) (hJ : ∀i k,J i k=J k i)
    (hd : ∀i,J i i=0) (h : Fin n→ℝ) (x : Spin n) (i : Fin n) :
    fieldEnergy J h (flip x i)=fieldEnergy J h x-2*spin x i*(h i+field J x i) := by
  simp only [fieldEnergy,energy_flip J hJ hd,spin_flip,mul_sub,Finset.sum_sub_distrib]
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]
  ring

lemma fieldGibbs_detailed_balance (J : Interaction n) (hJ : ∀i k,J i k=J k i)
    (hd : ∀i,J i i=0) (h : Fin n→ℝ) (x : Spin n) (i : Fin n) :
    fieldGibbs J h (flip x i)*(1+spin x i*Real.tanh (h i+field J x i))=
      fieldGibbs J h x*(1-spin x i*Real.tanh (h i+field J x i)) := by
  simp only [fieldGibbs,fieldEnergy_flip J hJ hd,Real.exp_sub]
  cases hi:x i
  · simp only [spin,hi,Bool.false_eq_true,↓reduceIte,neg_mul,one_mul,mul_neg,Real.exp_neg]
    have ht:=exp_two_mul_one_sub_tanh (h i+field J x i)
    field_simp [ne_of_gt (fieldPartition_pos J h)]
    nlinarith only [ht]
  · simp only [spin,hi,↓reduceIte,one_mul,mul_one]
    have ht:=exp_two_mul_one_sub_tanh (h i+field J x i)
    field_simp [ne_of_gt (fieldPartition_pos J h)]
    nlinarith only [ht]

namespace Static
lemma conditionalMean_fieldGibbs (J : Interaction n) (hJ : ∀i k,J i k=J k i)
    (hd : ∀i,J i i=0) (h : Fin n→ℝ) (x : Spin n) (i : Fin n) :
    conditionalMean (fieldGibbs J h) x i=Real.tanh (h i+field J x i) := by
  have hb:=fieldGibbs_detailed_balance J hJ hd h x i
  have hp:=ne_of_gt (add_pos (fieldGibbs_pos J h x) (fieldGibbs_pos J h (flip x i)))
  rw [conditionalMean,←mul_div_assoc]
  apply (div_eq_iff hp).2
  cases hi:x i <;> simp only [spin,hi,Bool.false_eq_true,↓reduceIte,one_mul,neg_mul] at hb ⊢ <;>
    linarith only [hb]

lemma conditionalMean_primary (j : ℝ) (J : Interaction n) (hJ : J.IsSymm)
    (hd : ∀i,J i i=0) (h : Fin n→ℝ) (x : Spin n) (i : Fin n) :
    conditionalMean (fieldGibbs J h) x i=Primary.mag j J h 1 x i := by
  rw [conditionalMean_fieldGibbs J (fun i k=>hJ.apply k i) hd]
  rfl
end Static
end SKGapCutoff

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static
universe u
variable {Ω : Type u} {n : Ω→ℕ} {M : ℕ} {j R B W C K : ℝ}
variable {J : ∀a,Interaction (n a)} {h : ∀a,Fin (n a)→ℝ}

theorem gibbs_ordinary_residuals (p N : ℕ) (hK : 2≤K) (hM : p<M)
    (hR : 0≤R) (hB : 0≤B) (hW : 0≤W) (hC : 0≤C)
    (hn : ∀a,0<n a) (hJ : ∀a,(J a).IsSymm) (hdiag : ∀a i,J a i i=0)
    (hevent : ∀a,RecipeMatrixEvent j R (residualCoefficientBudget j K p 0) B W C M (N+2*p) (J a))
    {σ : Type} [Fintype σ] (D : ∀a,OrdinaryData (n a) (Fin M) (Fin M) σ)
    (H : FamilyRecipe j J h D N p K) :
    UniformWeak (fun a=>fieldGibbs (J a) (h a))
      (fun a x=>∑i,residual j (J a) (h a) p x i*(D a).source N x i) ∧
    UniformSquare (fun a=>fieldGibbs (J a) (h a))
      (fun a x=>∑i,residual j (J a) (h a) p x i*(D a).source N x i) := by
  have hA : 1 ≤ residualCoefficientBudget j K p 0 :=
    (by linarith : 1≤K).trans (residualCoefficientBudget_ge j (by linarith) p 0)
  have hc:=primary_finite_control j R B hR hB J h M (N+2*p) hn
    (fun a=>(hevent a).1) (fun a x l hl=>(hevent a).2.1 (h a) x l hl)
    _ W C hA hW hC (fun a=>(hevent a).2.2.1) (fun a=>(hevent a).2.2.2)
  have hp : ∀a x,0≤fieldGibbs (J a) (h a) x:=fun a x=>(fieldGibbs_pos _ _ _).le
  have hm:=fun a=>conditionalMean_primary j (J a) (hJ a) (hdiag a) (h a)
  exact ⟨uniform_ordinary_weak_residual p N hK hM hc hp (fun a=>sum_fieldGibbs _ _) hm hn hJ D H,
    uniform_ordinary_square_residual p N hK hM hc hp (fun a=>sum_fieldGibbs _ _) hm hn hJ D H⟩

end SKGapCutoff.Recipe

end
end

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
-- module Solutions.OAIQ072_SK.SKGap_Terminal_FinitePairTail
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
variable {n d : ℕ}

lemma RecipeMatrixEvent.mono {j R A A' B W C : ℝ} {M N N' : ℕ} {J : Interaction n}
    (he : RecipeMatrixEvent j R A B W C M N J) (hA : A'≤A) (hN : N'≤N) :
    RecipeMatrixEvent j R A' B W C M N' J := by
  refine ⟨he.1,he.2.1,?_,?_⟩
  · intro w hl hw; exact he.2.2.1 w (hl.trans (by omega)) (wordBounded_mono hw hA)
  · intro w hl hw; exact he.2.2.2 w (hl.trans (by omega)) (wordBounded_mono hw hA)

lemma residualCoefficientBudget_depth_mono (j : ℝ) {k d : ℕ} (hk : k≤d) :
    residualCoefficientBudget j 2 k 0 ≤ residualCoefficientBudget j 2 d 0 := by
  simp only [residualCoefficientBudget,Nat.sub_zero]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact pow_le_pow_right₀ (by linarith [steinCoefficientBudget_nonneg |j|]) hk

universe u

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
namespace SKGapCutoff.Static
universe u
variable {Ω : Type u} {n : Ω→ℕ}
lemma UniformWeak.finset_sum {τ : Type*} {P : ∀a,Observables (n a)}
    {F : τ→∀a,Observables (n a)} (s : Finset τ) (h : ∀t∈s,UniformWeak P (F t)) :
    UniformWeak P (fun a x=>∑t∈s,F t a x) := by
  classical
  induction s using Finset.induction_on with
  | empty=>simpa using UniformWeak.zero P
  | @insert t s ht ih=>
    simpa only [Finset.sum_insert ht] using (h t (Finset.mem_insert_self ..)).add
      (ih (fun r hr=>h r (Finset.mem_insert_of_mem hr)))
lemma UniformSquare.finset_sum {τ : Type*} {P : ∀a,Observables (n a)}
    {F : τ→∀a,Observables (n a)} (s : Finset τ) (h : ∀t∈s,UniformSquare P (F t)) :
    UniformSquare P (fun a x=>∑t∈s,F t a x) := by
  classical
  induction s using Finset.induction_on with
  | empty=>simpa using UniformSquare.zero P
  | @insert t s ht ih=>
    simpa only [Finset.sum_insert ht] using (h t (Finset.mem_insert_self ..)).add
      (ih (fun r hr=>h r (Finset.mem_insert_of_mem hr)))
end SKGapCutoff.Static
namespace SKGapCutoff.Recipe
open Primary Static
variable {n M : ℕ}

lemma constantRecipe_source (j : ℝ) (J : Interaction n) (h e : Fin n→ℝ) (M : ℕ) :
    (constantRecipe j J h e M).source 0=fun _=>e := by
  rw [OrdinaryData.source_eq]
  ext x i
  simp [OrdinaryData.sourceOf,constantRecipe,OrdinaryData.seedCoefficient,OrdinaryData.auxCoefficient,coefficient]

lemma constantRecipe_coefficients (j : ℝ) (J : Interaction n) (h e : Fin n→ℝ) (M N : ℕ) (x : Spin n) :
    (constantRecipe j J h e M).CoefficientClass N x 1 := by
  refine ⟨le_rfl,?_,?_,?_,?_⟩
  · intro a ha s; exact (segmentRegular_const _ _ x 1).mono zero_le_one
  · intro a ha b; exact (segmentRegular_const _ _ x 0).mono zero_le_one
  · intros; norm_num [SegmentValue,constantRecipe]
  · intros; norm_num [SegmentValue,constantRecipe]

lemma constantRecipe_admissible (j : ℝ) (J : Interaction n) (h e : Fin n→ℝ) (M N p : ℕ) :
    (constantRecipe j J h e M).Admissible N p := by
  intro a ha q hq
  constructor <;> intro s <;> ext x i <;>
    simp [OrdinaryData.seedPartial,OrdinaryData.auxPartial,localPartial,constantRecipe,partialAt]

universe u
variable {Ω : Type u} {N : Ω→ℕ} {j R B W C : ℝ}
variable {J : ∀a,Interaction (N a)} {h e : ∀a,Fin (N a)→ℝ}

lemma constantRecipe_family (he : ∀a,vectorNorm (e a)≤1) (M p : ℕ) :
    FamilyRecipe j J h (fun a=>constantRecipe j (J a) (h a) (e a) M) 0 p 2 := by
  refine ⟨fun _=>rfl,fun _=>rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl,
    ⟨1,zero_le_one,?_⟩,fun a x=>(constantRecipe_coefficients j (J a) (h a) (e a) M 0 x).mono (by norm_num),
    fun a=>constantRecipe_admissible j (J a) (h a) (e a) M 0 p⟩
  intro a; simpa [constantRecipe] using he a

lemma primary_residual_telescope (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (d : ℕ) (x : Spin n) (i : Fin n) :
    (∑k∈Finset.range d,residual j J h k x i)=spin x i-mag j J h d x i := by
  induction d with
  | zero=>simp [mag_zero]
  | succ d ih=>rw [Finset.sum_range_succ,ih];dsimp [Primary.residual];ring

theorem gibbs_constant_residuals (d : ℕ) (hR : 0≤R) (hB : 0≤B) (hW : 0≤W) (hC : 0≤C)
    (hn : ∀a,0<N a) (hJ : ∀a,(J a).IsSymm) (hdiag : ∀a i,J a i i=0)
    (hevent : ∀a,RecipeMatrixEvent j R (residualCoefficientBudget j 2 d 0) B W C (d+1) (2*d) (J a))
    (he : ∀a,vectorNorm (e a)≤1) (k : ℕ) (hk : k≤d) :
    UniformWeak (fun a=>fieldGibbs (J a) (h a))
      (fun a x=>∑i,(spin x i-mag j (J a) (h a) k x i)*e a i) ∧
    UniformSquare (fun a=>fieldGibbs (J a) (h a))
      (fun a x=>∑i,(spin x i-mag j (J a) (h a) k x i)*e a i) := by
  have H (l : ℕ) (hl : l<k):=
    gibbs_ordinary_residuals l 0 (by norm_num : (2:ℝ)≤2) (by omega : l<d+1)
      hR hB hW hC hn hJ hdiag
      (fun a=>(hevent a).mono (residualCoefficientBudget_depth_mono j (by omega)) (by omega))
      (fun a=>constantRecipe j (J a) (h a) (e a) (d+1)) (constantRecipe_family he (d+1) l)
  have H' (l : ℕ) (hl : l<k) :
      UniformWeak (fun a=>fieldGibbs (J a) (h a)) (fun a x=>∑i,residual j (J a) (h a) l x i*e a i) ∧
      UniformSquare (fun a=>fieldGibbs (J a) (h a)) (fun a x=>∑i,residual j (J a) (h a) l x i*e a i) := by
    simpa only [constantRecipe_source] using H l hl
  have hh (a : Ω) (x : Spin (N a)) :
      (∑l∈Finset.range k,∑i,residual j (J a) (h a) l x i*e a i)=
      ∑i,(spin x i-mag j (J a) (h a) k x i)*e a i := by
    rw [Finset.sum_comm]
    simp only [←Finset.sum_mul,primary_residual_telescope]
  exact ⟨((UniformWeak.finset_sum (Finset.range k) (fun l hl=>(H' l (Finset.mem_range.mp hl)).1))).congr hh,
    ((UniformSquare.finset_sum (Finset.range k) (fun l hl=>(H' l (Finset.mem_range.mp hl)).2))).congr hh⟩

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
universe u
variable {Ω : Type u} {n : Ω→ℕ}
lemma UniformMultiplier.neg {F : ∀a,Observables (n a)} (hF : UniformMultiplier F) :
    UniformMultiplier (fun a x=>-F a x) := by
  obtain ⟨B,L,hB,hL,hF,hd⟩:=hF
  refine ⟨B,L,hB,hL,fun a x=>by simpa using hF a x,fun a x=>?_⟩
  have he (i : Fin (n a)) : halfDiff i (fun y=>-F a y) x= -halfDiff i (F a) x := by unfold halfDiff;ring
  simpa only [he,neg_sq] using hd a x
lemma UniformMultiplier.mul {F G : ∀a,Observables (n a)} (hF : UniformMultiplier F)
    (hG : UniformMultiplier G) : UniformMultiplier (fun a x=>F a x*G a x) := by
  obtain ⟨B,L,hB,hL,hF,hdF⟩:=hF
  obtain ⟨D,K,hD,hK,hG,hdG⟩:=hG
  exact ⟨B*D,Real.sqrt (2*B^2*K^2+2*D^2*L^2),mul_nonneg hB hD,Real.sqrt_nonneg _,
    fun a=>(scalar_product_bounds (F a) (G a) hB hL hD hK (hF a) (hdF a) (hG a) (hdG a)).1,
    fun a=>(scalar_product_bounds (F a) (G a) hB hL hD hK (hF a) (hdF a) (hG a) (hdG a)).2⟩
lemma UniformMultiplier.finset_prod {τ : Type*} {F : τ→∀a,Observables (n a)} (s : Finset τ)
    (h : ∀t∈s,UniformMultiplier (F t)) : UniformMultiplier (fun a x=>∏t∈s,F t a x) := by
  classical
  induction s using Finset.induction_on with
  | empty=>simpa using UniformMultiplier.const (n:=n) 1
  | @insert t s ht ih=>
    simpa only [Finset.prod_insert ht] using (h t (Finset.mem_insert_self ..)).mul
      (ih (fun r hr=>h r (Finset.mem_insert_of_mem hr)))
end SKGapCutoff.Static
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
variable {Ω : Type u} {N : Ω→ℕ} {j R B ρ : ℝ} {M : ℕ}
variable {J : ∀a,Interaction (N a)} {h : ∀a,Fin (N a)→ℝ}

lemma residualCutoff_uniform (hρ : 0<ρ) (hR : 0≤R) (hB : 0≤B)
    (hn : ∀a,0<N a) (hop : ∀a,SKGap.opNorm (J a)≤R)
    (hformal : ∀a x l,l<M→ShapeBound (formalField j (J a) (h a) x l) B)
    (k : ℕ) (hk : k+2<M) :
    UniformMultiplier (fun a=>residualCutoff ρ j (J a) (h a) k) := by
  obtain ⟨K,hK⟩:=residualScalarCutoff_lipschitz
  let A:=residualDerivativeBudget j R B k
  let D:=residualDerivativeBudget j R B (k+1)
  have hA : 0≤A:=residualDerivativeBudget_nonneg hR hB k
  have hD : 0≤D:=residualDerivativeBudget_nonneg hR hB (k+1)
  let L:=2*(K:ℝ)/ρ^2*((4*A+2*A^2)+(4*D+2*D^2))
  have hL : 0≤L:=by dsimp [L];positivity
  refine ⟨1,L,zero_le_one,hL,fun a x=>?_,fun a x=>?_⟩
  · rw [abs_of_nonneg (residualCutoff_bounds ρ j (J a) (h a) k x).1]
    exact (residualCutoff_bounds ρ j (J a) (h a) k x).2
  · have H:=residualCutoff_gradient (hn a) hρ hK (J a) (h a) k x hA hD
      (residual_derivative_bound (hn a) hR hB (J a) (h a) (hop a) k (fun x l hl=>hformal a x l (by omega)) x)
      (residual_derivative_bound (hn a) hR hB (J a) (h a) (hop a) (k+1) (fun x l hl=>hformal a x l (by omega)) x)
    have hone : 1≤Real.sqrt (N a:ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hn a)
    have hd : ‖derivativeVector (residualCutoff ρ j (J a) (h a) k) x‖≤L :=
      H.trans (div_le_self hL hone)
    simpa only [norm_derivativeVector_sq] using pow_le_pow_left₀ (norm_nonneg _) hd 2

lemma cutoffWeight_uniform {C : ℕ→∀a,Observables (N a)} (k : ℕ)
    (hC : ∀l≤k,UniformMultiplier (C l)) :
    UniformMultiplier (fun a x=>cutoffWeight (fun l=>C l a x) k) := by
  exact (hC k le_rfl).mul (UniformMultiplier.finset_prod (Finset.range k)
    (fun l hl=>(UniformMultiplier.const 1).add (hC l (Finset.mem_range.mp hl).le).neg))

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_SelectionDeficit
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
variable {Ω : Type u} {N : Ω→ℕ}

lemma uniform_cutoff_partition {P H : ∀a,Observables (N a)}
    {C F : ℕ→∀a,Observables (N a)} (d : ℕ)
    (hP : ∀a x,0≤P a x)
    (hmult : ∀k<d,UniformMultiplier (C k))
    (hres : ∀k<d,UniformWeak P (fun a x=>H a x-F k a x))
    (hlocal : ∀k<d,UniformWeak P (fun a x=>C k a x*F k a x))
    (hdef : UniformWeak P (fun a x=>cutoffDeficit (fun k=>C k a x) d*H a x)) :
    UniformWeak P H := by
  classical
  let Q:=fun k a x=>∏l∈Finset.range k,(1-C l a x)
  have hQ (k : ℕ) (hk : k<d) : UniformMultiplier (Q k) := by
    apply UniformMultiplier.finset_prod
    intro l hl
    exact (UniformMultiplier.const 1).add (hmult l (lt_trans (Finset.mem_range.mp hl) hk)).neg
  have hw (k : ℕ) (hk : k<d) :
      UniformWeak P (fun a x=>cutoffWeight (fun l=>C l a x) k*H a x) := by
    have hr:=(hres k hk).mul hP (cutoffWeight_uniform k (fun l hl=>hmult l (lt_of_le_of_lt hl hk)))
    have hf:=(hlocal k hk).mul hP (hQ k hk)
    apply (hr.add hf).congr
    intro a x
    dsimp [cutoffWeight,Q]
    ring
  have hs:=(UniformWeak.finset_sum (Finset.range d) (fun k hk=>hw k (Finset.mem_range.mp hk))).add hdef
  apply hs.congr
  intro a x
  rw [←Finset.sum_mul]
  dsimp [cutoffDeficit]
  ring

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Posterior_BufferedPosteriorDirection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary Static
universe u

theorem buffered_root_posterior_direction {j K B Aroot ε c r₀ R ρ : ℝ}
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
    : ∃A : ℕ→ℝ,(∀k,1≤A k) ∧ ∀m:ℕ,∀δ:ℝ,0<δ→
      2<(m:ℝ)*ρ^2/4→2*(2*m:ℕ)*δ≤1→∀W C:ℝ,0≤W→0≤C→
      ∀(Ω : Type u) (n : Ω→ℕ) (J : ∀b,Interaction (n b))
      (h e : ∀b,Fin (n b)→ℝ),
      (∀b,0<n b)→(∀b,(J b).IsSymm)→(∀b i,J b i i=0)→
      (∀b,vectorNorm (e b)≤1)→
      (∀b k,k<2*m-1→StartedMatrixEvent j K (Real.exp (R/2)) (A k) (c/2) B W C (k+3) (2+2*(k+1)) (J b))→
      (∀b,RecipeMatrixEvent j K (residualCoefficientBudget j 2 (2*m) 0) B W C (2*m+1) (2*(2*m)) (J b))→
      (∀b,¬SKGap.rootBad j Aroot ε c r₀ (J b) (h b))→
      (∀b k,k<2*m-1→4*(residualDerivativeBudget j K B k+residualDerivativeBudget j K B (k+1))≤ρ*Real.sqrt (n b:ℝ))→
      ∃r : ∀b,Fin (n b)→ℝ,(∀b,SKGap.tapField j (J b) (h b) (r b)=0 ∧
        ∀v,SKGap.tapField j (J b) (h b) v=0→v=r b) ∧
      UniformWeak (fun b=>fieldGibbs (J b) (h b))
        (fun b x=>∑i,(spin x i-Real.tanh (r b i))*e b i) := by
  classical
  choose A hA hs using fun k=>buffered_root_direction_weak.{u} hj hK hB hA hc hr₀ hρ hε
    hAR hbuffer hR hsmall himplicit habsorb k
  refine ⟨A,hA,?_⟩
  intro m δ hδ hm hδm W C hW hC Ω n J h e hn hJ hdiag he hstarted hevent hbad hdim
  have hm0 : 0 < m := by
    by_contra hh
    have hz:m=0:=by omega
    subst m
    norm_num at hm
  have hd0 : 0<2*m-1:=by omega
  let P:=fun b=>fieldGibbs (J b) (h b)
  have hP : ∀b x,0≤P b x:=fun b x=>(fieldGibbs_pos _ _ _).le
  have hp : ∀b,∑x,P b x=1:=fun b=>sum_fieldGibbs _ _
  have hmean : ∀b x i,conditionalMean (P b) x i=mag j (J b) (h b) 1 x i :=
    fun b=>conditionalMean_primary j (J b) (hJ b) (hdiag b) (h b)
  obtain ⟨r,hr,D,hD,hdir⟩:=hs 0 W C hW hC Ω n J h e P hn hJ he
    (fun b=>hstarted b 0 hd0) hbad (fun b=>hdim b 0 hd0) hP hp hmean
  refine ⟨r,hr,?_⟩
  let F:=fun k b x=>∑i,(mag j (J b) (h b) (k+2) x i-Real.tanh (r b i))*e b i
  apply uniform_cutoff_partition (C:=fun k b=>residualCutoff ρ j (J b) (h b) k)
    (F:=F) (2*m-1) hP
  · intro k hk
    exact residualCutoff_uniform hρ hK hB hn (fun b=>(hevent b).1)
      (fun b x l hl=>(hevent b).2.1 (h b) x l hl) k (by omega)
  · intro k hk
    have hh:=(gibbs_constant_residuals (h:=h) (e:=e) (2*m) hK hB hW hC hn hJ hdiag hevent he (k+2) (by omega)).1
    apply hh.congr
    intro b x
    dsimp [F]
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · intro k hk
    obtain ⟨r',hr',D',hD',hh⟩:=hs k W C hW hC Ω n J h e P hn hJ he
      (fun b=>hstarted b k hk) hbad (fun b=>hdim b k hk) hP hp hmean
    have heqr : r'=r:=funext fun b=>(hr b).2 (r' b) (hr' b).1
    rw [heqr] at hh
    refine ⟨D',hD',fun b G=>?_⟩
    have hh':=hh b G
    change |∑x,P b x*G x*(residualCutoff ρ j (J b) (h b) k x*F k b x)|≤_
    have heq : (∑x,P b x*G x*(residualCutoff ρ j (J b) (h b) k x*F k b x))=
        ∑x,P b x*(residualCutoff ρ j (J b) (h b) k x*G x)*
          (∑i,(Real.tanh (fld j (J b) (h b) (k+1) x i)-Real.tanh (r b i))*e b i) := by
      apply Finset.sum_congr rfl
      intro x _
      simp only [F,mag_succ]
      ring
    rwa [heq]
  · obtain ⟨Q,hQ,hq⟩:=gibbs_residual_selection_deficit (h:=h) m hρ hδ hm hδm hK hB hW hC hn hJ hdiag hevent
    exact ⟨Q,hQ,fun b G=>hq b (r b) (e b) (he b) G⟩

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
open Primary Recipe
variable {n : ℕ}

lemma posterior_vectorNorm_le_of_unit_dot {n : ℕ} (v : Fin n→ℝ) {B : ℝ} (hB : 0≤B)
    (h : ∀e : Fin n→ℝ,vectorNorm e≤1→|∑i,v i*e i|≤B) : vectorNorm v≤B := by
  by_cases hv:vectorNorm v=0
  · simpa [hv] using hB
  have hp:0<vectorNorm v:=lt_of_le_of_ne (vectorNorm_nonneg _) (Ne.symm hv)
  let e:=fun i=>(vectorNorm v)⁻¹*v i
  have he:vectorNorm e=1 := by
    change SKGap.vectorNorm (fun i=>(vectorNorm v)⁻¹*v i)=1
    rw [SKGap.vectorNorm_smul,abs_of_pos (inv_pos.mpr hp)]
    exact inv_mul_cancel₀ hv
  have hh:=h e he.le
  have hd:(∑i,v i*e i)=vectorNorm v := by
    calc
      _ = (vectorNorm v)⁻¹*(∑i,(v i)^2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl;intro i _;dsimp [e];ring
      _ = (vectorNorm v)⁻¹*(vectorNorm v)^2 := by rw [vectorNorm_sq]
      _ = _ := by field_simp
  simpa only [hd,abs_of_nonneg (vectorNorm_nonneg _)] using hh

lemma weak_direction_center (P G : Observables n) (hp : ∑x,P x=1)
    (r e : Fin n→ℝ) {D : ℝ}
    (hw : ∀U,|∑x,P x*U x*(∑i,(spin x i-Real.tanh (r i))*e i)|≤D*starNorm P U) :
    |∑i,centeredSpinCovariance P G i*e i|≤
      D*Real.sqrt ((∑x,P x*(G x-∑y,P y*G y)^2)+varianceEnergy P G) := by
  let U:=fun x=>G x-∑y,P y*G y
  have hzero : (∑x,P x*U x)=0 := by
    dsimp [U]
    simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,hp,one_mul,sub_self]
  have he : varianceEnergy P U=varianceEnergy P G := by
    unfold varianceEnergy
    apply Finset.sum_congr rfl
    intro x _
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have hd : halfDiff i U x=halfDiff i G x:=by dsimp [halfDiff,U];ring
    rw [hd]
  have hid : (∑x,P x*U x*(∑i,(spin x i-Real.tanh (r i))*e i))=
      ∑i,centeredSpinCovariance P G i*e i := by
    simp only [sub_mul,Finset.sum_sub_distrib,mul_sub]
    rw [←Finset.sum_mul,hzero,zero_mul,sub_zero]
    simp only [Finset.mul_sum,centeredSpinCovariance,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro x _
    dsimp [U]
    ring
  have hh:=hw U
  rw [hid] at hh
  simpa only [starNorm,starSquared,he,U] using hh

end SKGapCutoff.Static

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Posterior_BufferedPosteriorCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary Static
universe u

theorem buffered_posterior_covariance_oai {j K B Aroot ε c r₀ R ρ : ℝ}
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
    : ∃A : ℕ→ℝ,(∀k,1≤A k) ∧ ∀m:ℕ,∀δ:ℝ,0<δ→
      2<(m:ℝ)*ρ^2/4→2*(2*m:ℕ)*δ≤1→∀W C:ℝ,0≤W→0≤C→
      ∀(Ω : Type u) (n : Ω→ℕ) (J : ∀b,Interaction (n b))
      (h : ∀b,Fin (n b)→ℝ),
      (∀b,0<n b)→(∀b,(J b).IsSymm)→(∀b i,J b i i=0)→
      (∀b k,k<2*m-1→StartedMatrixEvent j K (Real.exp (R/2)) (A k) (c/2) B W C (k+3) (2+2*(k+1)) (J b))→
      (∀b,RecipeMatrixEvent j K (residualCoefficientBudget j 2 (2*m) 0) B W C (2*m+1) (2*(2*m)) (J b))→
      (∀b,¬SKGap.rootBad j Aroot ε c r₀ (J b) (h b))→
      (∀b k,k<2*m-1→4*(residualDerivativeBudget j K B k+residualDerivativeBudget j K B (k+1))≤ρ*Real.sqrt (n b:ℝ))→
      ∃D≥0,∀b (G : Observables (n b)),
        vectorNorm (centeredSpinCovariance (fieldGibbs (J b) (h b)) G)≤
          D*Real.sqrt ((∑x,fieldGibbs (J b) (h b) x*
            (G x-∑y,fieldGibbs (J b) (h b) y*G y)^2)+
            varianceEnergy (fieldGibbs (J b) (h b)) G) := by
  obtain ⟨A,hA',hs⟩:=buffered_root_posterior_direction.{u} hj hK hB hA hc hr₀ hρ hε
    hAR hbuffer hR hsmall himplicit habsorb
  refine ⟨A,hA',?_⟩
  intro m δ hδ hm hδm W C hW hC Ω n J h hn hJ hdiag hstarted hevent hbad hdim
  let Λ:=Σb:Ω,{e : Fin (n b)→ℝ //vectorNorm e≤1}
  obtain ⟨r,hr,D,hD,hw⟩:=hs m δ hδ hm hδm W C hW hC Λ (fun a=>n a.1)
    (fun a=>J a.1) (fun a=>h a.1) (fun a=>a.2.1)
    (fun a=>hn a.1) (fun a=>hJ a.1) (fun a=>hdiag a.1) (fun a=>a.2.2)
    (fun a=>hstarted a.1) (fun a=>hevent a.1) (fun a=>hbad a.1) (fun a=>hdim a.1)
  refine ⟨D,hD,?_⟩
  intro b G
  apply posterior_vectorNorm_le_of_unit_dot _ (mul_nonneg hD (Real.sqrt_nonneg _))
  intro e he
  exact weak_direction_center _ G (sum_fieldGibbs _ _) (r ⟨b,e,he⟩) e (hw ⟨b,e,he⟩)

end SKGapCutoff.Recipe

end
end

end OAI
end

theorem solution.{u} : type_of% @OAI.SKGapCutoff.Recipe.buffered_posterior_covariance_oai.{u} := @OAI.SKGapCutoff.Recipe.buffered_posterior_covariance_oai.{u}
