-- Prove2me | solution 1 for OAI.SK.Analytic.narrowConstrainedPressure_scaled_gap
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T05:08:34.743364+00:00
-- url     : https://prove2.me/submissions/38dbf9bd-61f0-4a08-a0d4-013e26e5802a

import Mathlib
import Definitions.Def_OAIQ036S006
import Theorems.Thm_OAI_SK_Analytic_fourBlockQuadratic_tent_le
import Theorems.Thm_OAI_SK_Analytic_narrowCDFTrialCoefficient_quantitative
import Theorems.Thm_OAI_SK_Analytic_narrowConstrainedPressure_schedule
import Theorems.Thm_OAI_SK_Analytic_narrowSchedule_value_expansion

section
-- module Solutions.OAIQ036_SK.Compat
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
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_BlockStein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic

theorem massFromAtoms_castSucc (n : ℕ) (w : Fin (n+2) → ℝ) (i : Fin n) :
    massFromAtoms (n+1) w i.castSucc = massFromAtoms n (fun j => w j.castSucc) i := by
  unfold massFromAtoms
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc,Fin.val_last]
  have h : ¬ n+1 ≤ i.val := by omega
  rw [ite_eq_right h,add_zero]

theorem massFromAtoms_last (n : ℕ) (w : Fin (n+2) → ℝ) :
    massFromAtoms (n+1) w (Fin.last n) = ∑ j : Fin (n+1), w j.castSucc := by
  unfold massFromAtoms
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc,Fin.val_last,show ¬ n+1 ≤ n by omega,ite_false,add_zero]
  apply Finset.sum_congr rfl
  intro j _
  rw [ite_eq_left (by omega)]

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_BoundedProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem unitBoundedProduct_abs_le {a b : ℝ} (ha : |a|≤1) (hb : |b|≤1) : |a*b|≤1 := by
  rw [abs_mul]
  calc
    _ ≤ 1*1 := mul_le_mul ha hb (abs_nonneg _) (by norm_num)
    _ = _ := by ring

theorem unitBoundedProduct_sub {a b c d : ℝ} (hb : |b|≤1) (hc : |c|≤1) :
    |a*b-c*d|≤|a-c|+|b-d| := by
  calc
    _ = |(a-c)*b+c*(b-d)| := by congr 1; ring
    _ ≤ |(a-c)*b|+|c*(b-d)| := abs_add_le _ _
    _ = |a-c| * |b|+|c| * |b-d| := by rw [abs_mul,abs_mul]
    _ ≤ |a-c| * 1+1*|b-d| := add_le_add
      (mul_le_mul_of_nonneg_left hb (abs_nonneg _)) (mul_le_mul_of_nonneg_right hc (abs_nonneg _))
    _ = _ := by ring

theorem unitBoundedProduct_lipschitz {f g : ℝ → ℝ} {K L : ℝ≥0}
    (hf : LipschitzWith K f) (hg : LipschitzWith L g)
    (hfb : ∀ x,|f x|≤1) (hgb : ∀ x,|g x|≤1) :
    LipschitzWith (K+L) (fun x => f x*g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have H := unitBoundedProduct_sub (a:=f x) (d:=g y) (hgb x) (hfb y)
  have Hf := hf.dist_le_mul x y
  have Hg := hg.dist_le_mul x y
  simp only [Real.dist_eq,NNReal.coe_add] at Hf Hg ⊢
  nlinarith

theorem unitBoundedProduct_tendstoUniformly {F G : ℕ → ℝ → ℝ} {f g : ℝ → ℝ}
    (hG : ∀ n x,|G n x|≤1) (hf : ∀ x,|f x|≤1)
    (hF : TendstoUniformly F f atTop) (hU : TendstoUniformly G g atTop) :
    TendstoUniformly (fun n x => F n x*G n x) (fun x => f x*g x) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp hF (ε/2) (by positivity),
    Metric.tendstoUniformly_iff.mp hU (ε/2) (by positivity)] with n hn hm x
  have H := unitBoundedProduct_sub (a:=F n x) (d:=g x) (hG n x) (hf x)
  have Hf := hn x
  have Hg := hm x
  simp only [Real.dist_eq] at Hf Hg ⊢
  rw [abs_sub_comm] at Hf Hg ⊢
  linarith

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarAverageCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarStepAverage_bound {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    {B : ℝ} (hb : ∀ x, |g x| ≤ B) (m v x : ℝ) :
    |scalarStepAverage m v f g x| ≤ B := by
  exact gaussianAverage_norm_le (hf.compCLM (scalarStepLinear v)) m
    (g:=fun z => g (z.1+v*z.2)) (fun z => hb _) x

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarHierarchyAverageAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem BoundedScalar.add {g h : ℝ → ℝ} (hg : BoundedScalar g) (hh : BoundedScalar h) :
    BoundedScalar (fun x => g x+h x) := by
  obtain ⟨B,hB,hb⟩ := hg.bounded
  obtain ⟨C,hC,hc⟩ := hh.bounded
  exact ⟨hg.continuous.add hh.continuous,B+C,add_nonneg hB hC,
    fun x => (abs_add_le _ _).trans (add_le_add (hb x) (hc x))⟩

theorem BoundedScalar.const_mul {g : ℝ → ℝ} (hg : BoundedScalar g) (c : ℝ) :
    BoundedScalar (fun x => c*g x) := by
  obtain ⟨B,hB,hb⟩ := hg.bounded
  refine ⟨continuous_const.mul hg.continuous,|c| * B,mul_nonneg (abs_nonneg _) hB,fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hb x) (abs_nonneg _)

theorem BoundedScalar.sub {g h : ℝ → ℝ} (hg : BoundedScalar g) (hh : BoundedScalar h) :
    BoundedScalar (fun x => g x-h x) := by
  simpa only [neg_one_mul,sub_eq_add_neg] using hg.add (hh.const_mul (-1))

theorem scalarHierarchyAverage_integrable {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : BoundedScalar g) (n : ℕ) (m v : Fin n → ℝ) (x : ℝ) :
    Integrable (fun z => g (x+coordinateLinear n v z))
      (hierarchyPathLaw n m (fun z => f (x+coordinateLinear n v z)) 0) := by
  obtain ⟨B,_,hb⟩ := hg.bounded
  apply hierarchyPathLaw_integrable n m _ _ ((hf.translate x).compCLM (coordinateLinear n v))
    (hg.continuous.comp (continuous_const.add (coordinateLinear n v).continuous))
  exact fun z => hb _

theorem scalarHierarchyAverage_integral {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : BoundedScalar g) (n : ℕ) (m v : Fin n → ℝ) (x : ℝ) :
    scalarHierarchyAverage n m v f g x=
      ∫ z, g (x+coordinateLinear n v z) ∂hierarchyPathLaw n m
        (fun z => f (x+coordinateLinear n v z)) 0 := by
  obtain ⟨B,hB,hb⟩ := hg.bounded
  exact scalarHierarchyAverage_eq_integral n m v hf hg.continuous hB hb x

theorem scalarHierarchyAverage_sub {f g h : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : BoundedScalar g) (hh : BoundedScalar h) (n : ℕ) (m v : Fin n → ℝ) (x : ℝ) :
    scalarHierarchyAverage n m v f (fun y => g y-h y) x=
      scalarHierarchyAverage n m v f g x-scalarHierarchyAverage n m v f h x := by
  rw [scalarHierarchyAverage_integral hf (hg.sub hh),scalarHierarchyAverage_integral hf hg,
    scalarHierarchyAverage_integral hf hh,integral_sub
    (scalarHierarchyAverage_integrable hf hg n m v x) (scalarHierarchyAverage_integrable hf hh n m v x)]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_SmoothedObservable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarWindow_hasDerivAt {g : ℝ → ℝ} (hg : Continuous g) (h x : ℝ) :
    HasDerivAt (scalarWindow g h) (scalarWindowDerivative g h x) x := by
  convert (((boundedPrimitive_hasDerivAt hg (x+h)).comp x
    ((hasDerivAt_id x).add_const h)).sub (boundedPrimitive_hasDerivAt hg x)).div_const h using 1 <;>
    first | rfl | exact Subsingleton.elim _ _ | simp only [scalarWindowDerivative,mul_one]

theorem scalarWindowDerivative_continuous {g : ℝ → ℝ} (hg : Continuous g) (h : ℝ) :
    Continuous (scalarWindowDerivative g h) :=
  ((hg.comp (continuous_id.add continuous_const)).sub hg).div_const h

theorem scalarWindow_bound {g : ℝ → ℝ} (hg : Continuous g) {B : ℝ≥0}
    (hB : ∀ x, |g x| ≤ B) {h : ℝ} (hh : 0<h) (x : ℝ) :
    |scalarWindow g h x| ≤ B := by
  have H := (boundedPrimitive_lipschitz hg hB).dist_le_mul (x+h) x
  simp only [Real.dist_eq,add_sub_cancel_left,abs_of_pos hh] at H
  rw [scalarWindow,abs_div,abs_of_pos hh,div_le_iff₀ hh]
  exact H

theorem scalarWindowDerivative_bound {g : ℝ → ℝ} {B : ℝ≥0}
    (hB : ∀ x, |g x| ≤ B) {h : ℝ} (hh : 0<h) (x : ℝ) :
    |scalarWindowDerivative g h x| ≤ 2*(B:ℝ)/h := by
  rw [scalarWindowDerivative,abs_div,abs_of_pos hh]
  exact div_le_div_of_nonneg_right ((abs_sub (g (x+h)) (g x)).trans (by linarith [hB (x+h),hB x])) hh.le

theorem scalarWindow_integral {g : ℝ → ℝ} (hg : Continuous g) (h x : ℝ) :
    scalarWindow g h x=(∫ y in x..x+h, g y)/h := by
  have H := intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable (μ:=volume) 0 x) (hg.intervalIntegrable (μ:=volume) x (x+h))
  dsimp only [scalarWindow,boundedPrimitive]
  congr 1
  linarith

theorem scalarWindow_approx {g : ℝ → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    {h : ℝ} (hh : 0<h) (x : ℝ) : |scalarWindow g h x-g x| ≤ (L:ℝ)*h := by
  rw [scalarWindow_integral hg.continuous]
  have H := intervalIntegral.norm_integral_le_of_norm_le_const (a:=x) (b:=x+h)
    (f:=fun y => g y-g x) (C:=(L:ℝ)*h) (by
      intro y hy
      rw [uIoc_of_le (by linarith)] at hy
      have H := hg.dist_le_mul y x
      simp only [Real.dist_eq] at H
      rw [abs_of_nonneg (show 0≤y-x by linarith [hy.1])] at H
      rw [Real.norm_eq_abs]
      exact H.trans (mul_le_mul_of_nonneg_left (by linarith [hy.2]) L.coe_nonneg))
  rw [intervalIntegral.integral_sub (hg.continuous.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _),
    intervalIntegral.integral_const,smul_eq_mul,add_sub_cancel_left,Real.norm_eq_abs,
    abs_of_pos hh] at H
  rw [show (∫ y in x..x+h, g y)/h-g x=((∫ y in x..x+h, g y)-h*g x)/h by field_simp,
    abs_div,abs_of_pos hh,div_le_iff₀ hh]
  exact H

theorem scalarHierarchyAverage_observable_distance {f g a : ℝ → ℝ}
    (hf : BoundedDerivs f) (hg : BoundedScalar g) (ha : BoundedScalar a)
    {δ : ℝ} (_hδ : 0≤δ) (hga : ∀ z, |g z-a z| ≤ δ)
    (n : ℕ) (m v : Fin n → ℝ) (x : ℝ) :
    |scalarHierarchyAverage n m v f g x-scalarHierarchyAverage n m v f a x| ≤ δ := by
  rw [← scalarHierarchyAverage_sub hf hg ha,
    scalarHierarchyAverage_integral hf (hg.sub ha)]
  have : IsProbabilityMeasure (hierarchyPathLaw n m (fun z => f (x+coordinateLinear n v z)) 0) :=
    hierarchyPathLaw_probability n m _ ((hf.translate x).compCLM (coordinateLinear n v)) 0
  have H := norm_integral_le_of_norm_le_const (μ:=hierarchyPathLaw n m
    (fun z => f (x+coordinateLinear n v z)) 0) (f:=fun z => g (x+coordinateLinear n v z)-a (x+coordinateLinear n v z))
    (C:=δ) (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hga (x+coordinateLinear n v z)))
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_LipschitzObservable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem dyadicScalarAverage_tendsto_lipschitz (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    {K B L : ℝ≥0} (hfK : LipschitzWith K f) (hgL : LipschitzWith L g)
    (hB : ∀ z, |g z| ≤ B) (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    Tendsto (fun n => dyadicScalarAverage β α n s t f g x) atTop
      (𝓝 (scalarCDFAverage β α s t f g x)) := by
  apply CauchySeq.tendsto_limUnder
  rw [Metric.cauchySeq_iff]
  intro ε hε
  let h := ε/(4*((L:ℝ)+1))
  have hL : 0<(L:ℝ)+1 := by positivity
  have hh : 0<h := div_pos hε (mul_pos (by norm_num) hL)
  have hsmall : (L:ℝ)*h ≤ ε/4 := by
    calc
      _ ≤ ((L:ℝ)+1)*h := mul_le_mul_of_nonneg_right (by linarith) hh.le
      _ = ε/4 := by dsimp [h]; field_simp
  let C : ℝ≥0 := ⟨2*(B:ℝ)/h,div_nonneg (by positivity) hh.le⟩
  have hW := dyadicScalarAverage_tendsto_C1 β hα hmono hf
    (scalarWindow_hasDerivAt hgL.continuous h) (scalarWindowDerivative_continuous hgL.continuous h)
    hfK (scalarWindow_bound hgL.continuous hB hh) (C:=C)
    (scalarWindowDerivative_bound hB hh) s t ht x
  have hc := Metric.cauchySeq_iff.mp hW.cauchySeq (ε/4) (by positivity)
  obtain ⟨N,hN⟩ := hc
  refine ⟨N,fun m hm n hn => ?_⟩
  have he (j : ℕ) : |dyadicScalarAverage β α j s t f g x-
      dyadicScalarAverage β α j s t f (scalarWindow g h) x| ≤ ε/4 := by
    apply (scalarHierarchyAverage_observable_distance hf
      ⟨hgL.continuous,B,B.coe_nonneg,hB⟩
      ⟨continuous_iff_continuousAt.mpr (fun z => (scalarWindow_hasDerivAt hgL.continuous h z).continuousAt),
        B,B.coe_nonneg,scalarWindow_bound hgL.continuous hB hh⟩
      (mul_nonneg L.coe_nonneg hh.le) (fun z => ?_) _ _ _ x).trans hsmall
    rw [abs_sub_comm]
    exact scalarWindow_approx hgL hh z
  have hd := hN m hm n hn
  simp only [Real.dist_eq] at hd ⊢
  have H₁ := abs_sub_le (dyadicScalarAverage β α m s t f g x)
    (dyadicScalarAverage β α m s t f (scalarWindow g h) x)
    (dyadicScalarAverage β α n s t f g x)
  have H₂ := abs_sub_le (dyadicScalarAverage β α m s t f (scalarWindow g h) x)
    (dyadicScalarAverage β α n s t f (scalarWindow g h) x)
    (dyadicScalarAverage β α n s t f g x)
  rw [abs_sub_comm (dyadicScalarAverage β α n s t f (scalarWindow g h) x)] at H₂
  linarith [he m,he n]

theorem scalarCDFAverage_observable_distance (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hmono : Monotone α)
    {f g a : ℝ → ℝ} (hf : BoundedDerivs f)
    {K B C L M : ℝ≥0} (hfK : LipschitzWith K f)
    (hgL : LipschitzWith L g) (haM : LipschitzWith M a)
    (hB : ∀ z, |g z| ≤ B) (hC : ∀ z, |a z| ≤ C)
    {δ : ℝ} (hδ : 0≤δ) (hga : ∀ z, |g z-a z| ≤ δ)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (x : ℝ) :
    |scalarCDFAverage β α s t f g x-scalarCDFAverage β α s t f a x| ≤ δ := by
  apply le_of_tendsto ((dyadicScalarAverage_tendsto_lipschitz β hα hmono hf hfK hgL hB s t ht x).sub
    (dyadicScalarAverage_tendsto_lipschitz β hα hmono hf hfK haM hC s t ht x)).abs
  exact Eventually.of_forall (fun n => scalarHierarchyAverage_observable_distance hf
    ⟨hgL.continuous,B,B.coe_nonneg,hB⟩ ⟨haM.continuous,C,C.coe_nonneg,hC⟩ hδ hga _ _ _ x)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_LipschitzChainRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarWindowDerivative_lipschitz_bound {g : ℝ → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) {h : ℝ} (hh : 0<h) (x : ℝ) :
    |scalarWindowDerivative g h x| ≤ L := by
  have H := hg.dist_le_mul (x+h) x
  simp only [Real.dist_eq,add_sub_cancel_left,abs_of_pos hh] at H
  rw [scalarWindowDerivative,abs_div,abs_of_pos hh,div_le_iff₀ hh]
  exact H

theorem scalarWindow_lipschitz {g : ℝ → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) {h : ℝ} (hh : 0<h) : LipschitzWith L (scalarWindow g h) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun x => (scalarWindow_hasDerivAt hg.continuous h x).differentiableAt)
  intro x
  rw [(scalarWindow_hasDerivAt hg.continuous h x).deriv]
  exact_mod_cast scalarWindowDerivative_lipschitz_bound hg hh x

theorem scalarCDFAverage_eq_chainAverage_lipschitz {f g : ℝ → ℝ}
    (hf : BoundedDerivs f) {K B L : ℝ≥0} (hfK : LipschitzWith K f)
    (hgL : LipschitzWith L g) (hB : ∀ z, |g z| ≤ B)
    (β : ℝ) {α : ℝ → ℝ} (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hmono : Monotone α)
    (l : List (ℝ × ℝ≥0)) (hm : ∀ p∈l, p.1∈Icc (0:ℝ) 1)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (hdur : chainDuration l=t)
    (hmodel : TimeChainModels α s l) (x : ℝ) :
    scalarCDFAverage β α s t f g x=scalarTimeChainAverage β l f g x := by
  apply sub_eq_zero.mp
  apply abs_eq_zero.mp
  apply le_antisymm ?_ (abs_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  simp only [zero_add]
  let h := ε/(2*((L:ℝ)+1))
  have hL : 0<(L:ℝ)+1 := by positivity
  have hh : 0<h := div_pos hε (mul_pos (by norm_num) hL)
  have hsmall : (L:ℝ)*h ≤ ε/2 := by
    calc
      _ ≤ ((L:ℝ)+1)*h := mul_le_mul_of_nonneg_right (by linarith) hh.le
      _ = ε/2 := by dsimp [h]; field_simp
  have hd (z) : |g z-scalarWindow g h z| ≤ (L:ℝ)*h := by
    rw [abs_sub_comm]
    exact scalarWindow_approx hgL hh z
  have H₁ := scalarCDFAverage_observable_distance β hα hmono hf hfK hgL
    (scalarWindow_lipschitz hgL hh) hB (scalarWindow_bound hgL.continuous hB hh)
    (mul_nonneg L.coe_nonneg hh.le) hd s t ht x
  have H₂ := scalarHierarchyAverage_observable_distance hf
    ⟨hgL.continuous,B,B.coe_nonneg,hB⟩
    ⟨(scalarWindow_lipschitz hgL hh).continuous,B,B.coe_nonneg,scalarWindow_bound hgL.continuous hB hh⟩
    (mul_nonneg L.coe_nonneg hh.le) hd l.length (fun i => (l.get i).1)
    (fun i => β*Real.sqrt ((l.get i).2:ℝ)) x
  change |scalarTimeChainAverage β l f g x-scalarTimeChainAverage β l f (scalarWindow g h) x|≤_ at H₂
  have HE := scalarCDFAverage_eq_chainAverage hf
    (scalarWindow_hasDerivAt hgL.continuous h) (scalarWindowDerivative_continuous hgL.continuous h)
    hfK (scalarWindow_bound hgL.continuous hB hh) (scalarWindowDerivative_lipschitz_bound hgL hh)
    β hα hmono l hm s t ht hdur hmodel x
  rw [HE] at H₁
  have H := abs_sub_le (scalarCDFAverage β α s t f g x)
    (scalarTimeChainAverage β l f (scalarWindow g h) x) (scalarTimeChainAverage β l f g x)
  rw [abs_sub_comm (scalarTimeChainAverage β l f (scalarWindow g h) x)] at H
  linarith

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_LipschitzCDFStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFAverage_cdf_stability_lipschitz (β : ℝ) {α γ : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (hγ : ∀ z, γ z∈Icc (0:ℝ) 1) (hγm : Monotone γ)
    {f g : ℝ → ℝ} (hf : BoundedDerivs f) {K B L : ℝ≥0}
    (hfK : LipschitzWith K f) (hgL : LipschitzWith L g) (hB : ∀ z, |g z|≤B)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (x h : ℝ) (hh : 0<h) :
    |scalarCDFAverage β α s t f g x-scalarCDFAverage β γ s t f g x| ≤
      2*(scalarTimeMassConstantK β (K+B+B)*(∫ z in s..s+t, |α z-γ z|))/h+
        2*((L:ℝ)+2*(B:ℝ)^2)*h := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let d := ε/(2*((L:ℝ)+1))
  have hL : 0<(L:ℝ)+1 := by positivity
  have hd : 0<d := div_pos hε (mul_pos (by norm_num) hL)
  have hsmall : (L:ℝ)*d ≤ ε/2 := by
    calc
      _ ≤ ((L:ℝ)+1)*d := mul_le_mul_of_nonneg_right (by linarith) hd.le
      _ = ε/2 := by dsimp [d]; field_simp
  have hga (z) : |g z-scalarWindow g d z| ≤ (L:ℝ)*d := by
    rw [abs_sub_comm]
    exact scalarWindow_approx hgL hd z
  have Hα := scalarCDFAverage_observable_distance β hα hαm hf hfK hgL
    (scalarWindow_lipschitz hgL hd) hB (scalarWindow_bound hgL.continuous hB hd)
    (mul_nonneg L.coe_nonneg hd.le) hga s t ht x
  have Hγ := scalarCDFAverage_observable_distance β hγ hγm hf hfK hgL
    (scalarWindow_lipschitz hgL hd) hB (scalarWindow_bound hgL.continuous hB hd)
    (mul_nonneg L.coe_nonneg hd.le) hga s t ht x
  have Hc := scalarCDFAverage_cdf_stability_C1 β hα hαm hγ hγm hf
    (scalarWindow_hasDerivAt hgL.continuous d) (scalarWindowDerivative_continuous hgL.continuous d)
    hfK (scalarWindow_bound hgL.continuous hB hd) (scalarWindowDerivative_lipschitz_bound hgL hd)
    s t ht x h hh
  have H₁ := abs_sub_le (scalarCDFAverage β α s t f g x)
    (scalarCDFAverage β α s t f (scalarWindow g d) x) (scalarCDFAverage β γ s t f g x)
  have H₂ := abs_sub_le (scalarCDFAverage β α s t f (scalarWindow g d) x)
    (scalarCDFAverage β γ s t f (scalarWindow g d) x) (scalarCDFAverage β γ s t f g x)
  rw [abs_sub_comm (scalarCDFAverage β γ s t f (scalarWindow g d) x)] at H₂
  linarith

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_LipschitzTerminalStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFAverage_terminal_stability_lipschitz (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hmono : Monotone α)
    {f g a b : ℝ → ℝ} (hf : BoundedDerivs f) (hg : BoundedDerivs g)
    {K L B A C : ℝ≥0} (hfK : LipschitzWith K f) (hgL : LipschitzWith L g)
    (haA : LipschitzWith A a) (hbC : LipschitzWith C b)
    (haB : ∀ z, |a z| ≤ B) (hbB : ∀ z, |b z| ≤ B)
    {ε δ : ℝ} (hε : 0≤ε) (hfg : ∀ z, |f z-g z| ≤ ε)
    (hab : ∀ z, |a z-b z| ≤ δ) (s : ℝ) (t : ℝ≥0) (ht : t≤1) (x : ℝ) :
    |scalarCDFAverage β α s t f a x-scalarCDFAverage β α s t g b x| ≤
      δ+2*(B:ℝ)*(Real.exp (2*ε)-1) := by
  apply le_of_tendsto ((dyadicScalarAverage_tendsto_lipschitz β hα hmono hf hfK haA haB s t ht x).sub
    (dyadicScalarAverage_tendsto_lipschitz β hα hmono hg hgL hbC hbB s t ht x)).abs
  apply Eventually.of_forall
  intro n
  apply scalarHierarchyAverage_terminal_stability _ _ _
    (fun i => dyadicIntervals_mass_bounds hα n s t (List.get_mem _ _))
    (fun i j hij => ?_) hf hg hε hfg haA.continuous hbC.continuous B.coe_nonneg haB hbB hab x
  rcases lt_or_eq_of_le hij with hij|rfl
  · exact List.pairwise_iff_get.mp (dyadicIntervals_pairwise hmono n s t) i j hij
  · exact le_rfl

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_VectorAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section Vector
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem vectorStep_pullback (L : E →L[ℝ] F) (m : ℝ) (v : E) (f : F → ℝ) :
    vectorStep m v (f ∘ L)=vectorStep m (L v) f ∘ L := by
  funext x
  simp only [vectorStep,Function.comp_def,map_add,map_smul]
  rfl

theorem vectorStepAverage_pullback (L : E →L[ℝ] F) (m : ℝ) (v : E) (f g : F → ℝ) :
    vectorStepAverage m v (f ∘ L) (g ∘ L)=vectorStepAverage m (L v) f g ∘ L := by
  funext x
  simp only [vectorStepAverage,Function.comp_def,map_add,map_smul]
  rfl

end Vector

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_CommonBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem vectorStep_real (m v : ℝ) (f : ℝ → ℝ) : vectorStep m v f=scalarStep m v f := by
  simp only [vectorStep,scalarStep,smul_eq_mul,mul_comm]

theorem vectorStepAverage_real (m v : ℝ) (f g : ℝ → ℝ) : vectorStepAverage m v f g=scalarStepAverage m v f g := by
  funext x
  simp only [vectorStepAverage,scalarStepAverage,gaussianAverage,gaussianStepLaw,smul_eq_mul,mul_comm]

theorem vectorHierarchyAverage_real (n : ℕ) (m v : Fin n → ℝ) (f g : ℝ → ℝ) :
    vectorHierarchyAverage n m v f g=scalarHierarchyAverage n m v f g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih => rw [vectorHierarchyAverage,vectorStep_real,vectorStepAverage_real,ih]; rfl

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_VectorBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section Vector
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem vectorIncrementChain_append (l r : List (ℝ × E)) (f : E → ℝ) :
    vectorIncrementChain (l++r) f=vectorIncrementChain l (vectorIncrementChain r f) := by
  induction l with
  | nil => rfl
  | cons p l ih => simp only [List.cons_append,vectorIncrementChain,ih]

theorem vectorIncrementAverage_append (l r : List (ℝ × E)) (f g : E → ℝ) :
    vectorIncrementAverage (l++r) f g=
      vectorIncrementAverage l (vectorIncrementChain r f) (vectorIncrementAverage r f g) := by
  induction l with
  | nil => rfl
  | cons p l ih => simp only [List.cons_append,vectorIncrementAverage,vectorIncrementChain_append,ih]

theorem vectorIncrementAverage_ofFn (n : ℕ) (m : Fin n → ℝ) (v : Fin n → E) (f g : E → ℝ) :
    vectorIncrementAverage (List.ofFn (fun i => (m i,v i))) f g=vectorHierarchyAverage n m v f g := by
  induction n generalizing f g with
  | zero => simp [vectorIncrementAverage,vectorHierarchyAverage]
  | succ n ih =>
    rw [List.ofFn_succ',List.concat_eq_append,vectorIncrementAverage_append]
    exact ih _ _ _ _

end Vector

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyMassPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem massFromAtoms_hierarchyAtom (n : ℕ) (m : Fin n → ℝ) (u : ℝ) (i : Fin n) :
    massFromAtoms n (hierarchyAtom n m u) i=m i := by
  induction n generalizing u with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [massFromAtoms_last]
      simp only [hierarchyAtom,Fin.lastCases_castSucc]
      exact hierarchyAtom_sum n _ _
    · rw [massFromAtoms_castSucc]
      simp only [hierarchyAtom,Fin.lastCases_castSucc]
      exact ih _ _ j

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_MatrixChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

section Penalty
variable {E : Type} [AddCommMonoid E]

theorem chainPotentialPenalty_append (F : E → ℝ) (l r : List (ℝ × E)) (Q : E) :
    chainPotentialPenalty F (l++r) Q=chainPotentialPenalty F l Q+
      chainPotentialPenalty F r (Q+chainSum l) := by
  induction l generalizing Q with
  | nil => simp [chainPotentialPenalty]
  | cons p l ih => simp only [List.cons_append,chainPotentialPenalty,ih,chainSum_cons,add_assoc]

end Penalty

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleTailValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

section Vector
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem vectorIncrementChain_pullback (L : E →L[ℝ] F) (l : List (ℝ × E)) (f : F → ℝ) :
    vectorIncrementChain l (f ∘ L)=
      vectorIncrementChain (l.map (fun p => (p.1,L p.2))) f ∘ L := by
  induction l with
  | nil => rfl
  | cons p l ih => rw [vectorIncrementChain,ih,vectorStep_pullback]; rfl
end Vector

theorem vectorIncrementChain_real (l : List (ℝ × ℝ)) (f : ℝ → ℝ) :
    vectorIncrementChain l f=scalarIncrementChain l f := by
  induction l with
  | nil => rfl
  | cons p l ih => rw [vectorIncrementChain,scalarIncrementChain,ih,vectorStep_real]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_IncrementListAnalytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
section Vector
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem vectorIncrementAverage_pullback (L : E →L[ℝ] F) (l : List (ℝ × E)) (f g : F → ℝ) :
    vectorIncrementAverage l (f ∘ L) (g ∘ L)=
      vectorIncrementAverage (l.map (fun p => (p.1,L p.2))) f g ∘ L := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [vectorIncrementAverage,vectorIncrementChain_pullback,ih,vectorStepAverage_pullback]
    rfl

end Vector

theorem vectorIncrementAverage_real (l : List (ℝ × ℝ)) (f g : ℝ → ℝ) :
    vectorIncrementAverage l f g=scalarIncrementAverage l f g := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [vectorIncrementAverage,scalarIncrementAverage,vectorIncrementChain_real,ih,vectorStepAverage_real]

theorem scalarIncrementAverage_ofFn (n : ℕ) (m v : Fin n → ℝ) (f g : ℝ → ℝ) :
    scalarIncrementAverage (List.ofFn (fun i => (m i,v i))) f g=scalarHierarchyAverage n m v f g := by
  rw [← vectorIncrementAverage_real,vectorIncrementAverage_ofFn,vectorHierarchyAverage_real]

theorem scalarIncrementAverage_append (l r : List (ℝ × ℝ)) (f g : ℝ → ℝ) :
    scalarIncrementAverage (l++r) f g=scalarIncrementAverage l (scalarIncrementChain r f) (scalarIncrementAverage r f g) := by
  simp only [← vectorIncrementAverage_real,← vectorIncrementChain_real,vectorIncrementAverage_append]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleRetainedStats
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem mass_get_monotone {E : Type} {l : List (ℝ × E)}
    (hs : l.Pairwise (fun p q => p.1≤q.1)) : Monotone (fun i : Fin l.length => (l.get i).1) := by
  have H := hs
  rw [← List.ofFn_get l,List.pairwise_ofFn] at H
  intro i j hij
  rcases lt_or_eq_of_le hij with hij|rfl
  · exact H hij
  · exact le_rfl

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ProductBranchMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SK.Analytic
section Map
variable {E F E' F' : Type}

theorem mergedProductBranches_map (f : E → E') (g : F → F') (l : List (ℝ × E)) (r : List (ℝ × F)) :
    (mergedProductBranches l r).map (mapProductIncrement f g)=
      mergedProductBranches (l.map (fun p => (p.1,f p.2))) (r.map (fun p => (p.1,g p.2))) := by
  unfold mergedProductBranches
  rw [List.map_merge (s:=fun p q => decide (productMass p≤productMass q))
    (by intro a ha b hb; simp only [productMass_map])]
  simp only [List.map_map,Function.comp_def,mapProductIncrement,Sum.map_inl,Sum.map_inr]
end Map

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleScheduleScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
namespace SK.Analytic

theorem weightedUnderlying_scale (β : ℝ) (w : List (ℝ × (ℝ × ℝ))) :
    weightedUnderlying (scaleIncrementChain β w)=scaleIncrementChain β (weightedUnderlying w) := by
  simp only [weightedUnderlying,scaleIncrementChain,List.map_map,Function.comp_def,Prod.smul_fst]

theorem tripleTailBlock_scale (β : ℝ) (p : ℝ × ℝ) :
    scaleIncrementChain β (tripleTailBlock p)=tripleTailBlock (p.1,β*p.2) := by
  simp only [scaleIncrementChain,tripleTailBlock,List.map_cons,List.map_nil]
  have h0 : β • ![p.2,0,0]=![β*p.2,0,0] := by ext i; fin_cases i <;> simp
  have h1 : β • ![0,p.2,0]=![0,β*p.2,0] := by ext i; fin_cases i <;> simp
  have h2 : β • ![0,0,p.2]=![0,0,β*p.2] := by ext i; fin_cases i <;> simp
  rw [h0,h1,h2]

theorem tripleTailSchedule_scale (β : ℝ) (t : List (ℝ × ℝ)) :
    scaleIncrementChain β (tripleTailSchedule t)=tripleTailSchedule (scaleIncrementChain β t) := by
  induction t with
  | nil => rfl
  | cons p t ih =>
    change scaleIncrementChain β (tripleTailBlock p++tripleTailSchedule t)=
      tripleTailBlock (p.1,β*p.2)++tripleTailSchedule (scaleIncrementChain β t)
    rw [scaleIncrementChain_append,tripleTailBlock_scale,ih]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_ConstantWeightStats
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem constantWeightChain_penalty (κ : ℝ) (l : List (ℝ × ℝ)) (q : ℝ) :
    weightedCrossPenalty (constantWeightChain κ l) (κ*q)=κ^2*rawPenalty l q := by
  induction l generalizing q with
  | nil => simp [weightedCrossPenalty,rawPenalty,constantWeightChain,chainPotentialPenalty]
  | cons p l ih =>
    change p.1*((κ*q+p.2*(κ*p.2))^2-(κ*q)^2)+weightedCrossPenalty (constantWeightChain κ l) (κ*q+p.2*(κ*p.2))=
      κ^2*(p.1*((q+p.2^2)^2-q^2)+rawPenalty l (q+p.2^2))
    rw [show κ*q+p.2*(κ*p.2)=κ*(q+p.2^2) by ring,ih]
    ring

@[simp] theorem constantWeightChain_penalty_zero (κ : ℝ) (l : List (ℝ × ℝ)) :
    weightedCrossPenalty (constantWeightChain κ l) 0=κ^2*rawPenalty l 0 := by
  simpa only [mul_zero] using constantWeightChain_penalty κ l 0

theorem rawVariance_nonneg (l : List (ℝ × ℝ)) : 0 ≤ rawVariance l := by
  exact List.sum_nonneg (by intro a ha; obtain ⟨p,_,rfl⟩ := List.mem_map.mp ha; exact sq_nonneg _)

theorem rawPenalty_bounds (l : List (ℝ × ℝ)) {a b q : ℝ}
    (hm : ∀ p∈l,p.1∈Icc a b) (hq : 0 ≤ q) :
    rawPenalty l q∈Icc (a*((q+rawVariance l)^2-q^2)) (b*((q+rawVariance l)^2-q^2)) := by
  induction l generalizing q with
  | nil => simp [rawPenalty,rawVariance,chainPotentialPenalty]
  | cons p l ih =>
    have hp := hm p (List.mem_cons_self ..)
    have H := ih (fun z hz => hm z (List.mem_cons_of_mem _ hz)) (q:=q+p.2^2) (by positivity)
    have hΔ : 0 ≤ (q+p.2^2)^2-q^2 := by nlinarith [sq_nonneg p.2]
    change p.1*((q+p.2^2)^2-q^2)+rawPenalty l (q+p.2^2)∈
      Icc (a*((q+(p.2^2+rawVariance l))^2-q^2)) (b*((q+(p.2^2+rawVariance l))^2-q^2))
    constructor
    · have H' := add_le_add (mul_le_mul_of_nonneg_right hp.1 hΔ) H.1
      convert H' using 1
      all_goals try with_reducible_and_instances rfl
      ring
    · have H' := add_le_add (mul_le_mul_of_nonneg_right hp.2 hΔ) H.2
      convert H' using 1
      all_goals try with_reducible_and_instances rfl
      ring

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyProjectedCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyAtom_tail_sum (n : ℕ) (m : Fin n → ℝ) (c : ℝ) (i : Fin n) :
    (∑ j : Fin (n+1), if i.val < j.val then hierarchyAtom n m c j else 0)=c-m i := by
  have H := massFromAtoms_hierarchyAtom n m c i
  have he : (∑ j : Fin (n+1), if i.val < j.val then hierarchyAtom n m c j else 0)+
      massFromAtoms n (hierarchyAtom n m c) i=c := by
    rw [massFromAtoms,← Finset.sum_add_distrib]
    convert hierarchyAtom_sum n m c using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i.val < j.val <;> simp [hij,show (j.val ≤ i.val) ↔ ¬i.val < j.val by omega]
  rw [H] at he
  linarith

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarSusceptibilitySum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarStepAverage_translate (m v c : ℝ) (f g : ℝ → ℝ) (x : ℝ) :
    scalarStepAverage m v (fun t => f (c+t)) (fun t => g (c+t)) x=
      scalarStepAverage m v f g (c+x) := by
  simp only [scalarStepAverage,gaussianAverage,gaussianStepLaw,add_assoc]

theorem scalarHierarchyAverage_translate (n : ℕ) (m v : Fin n → ℝ)
    (f g : ℝ → ℝ) (c x : ℝ) :
    scalarHierarchyAverage n m v (fun y => f (c+y)) (fun y => g (c+y)) x=
      scalarHierarchyAverage n m v f g (c+x) := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [scalarHierarchyAverage]
    rw [funext (scalarStep_translate _ _ c f),funext (scalarStepAverage_translate _ _ c f g)]
    exact ih _ _ _ _

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_ConstantWeightMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem rawPenalty_shift (l : List (ℝ × ℝ)) (q s : ℝ) :
    rawPenalty l (q+s)=rawPenalty l q+2*s*rawArea l := by
  induction l generalizing q with
  | nil => simp [rawPenalty,rawArea,chainPotentialPenalty]
  | cons p l ih =>
    change p.1*((q+s+p.2^2)^2-(q+s)^2)+rawPenalty l (q+s+p.2^2)=
      p.1*((q+p.2^2)^2-q^2)+rawPenalty l (q+p.2^2)+2*s*(p.1*p.2^2+rawArea l)
    rw [show q+s+p.2^2=(q+p.2^2)+s by ring,ih]
    ring

theorem constantWeightChain_penalty_offset (κ : ℝ) (l : List (ℝ × ℝ)) (x : ℝ) :
    weightedCrossPenalty (constantWeightChain κ l) x=κ^2*rawPenalty l 0+2*x*κ*rawArea l := by
  induction l generalizing x with
  | nil => simp [weightedCrossPenalty,rawPenalty,rawArea,constantWeightChain,chainPotentialPenalty]
  | cons p l ih =>
    change p.1*((x+p.2*(κ*p.2))^2-x^2)+weightedCrossPenalty (constantWeightChain κ l) (x+p.2*(κ*p.2))=
      κ^2*(p.1*((0+p.2^2)^2-0^2)+rawPenalty l (0+p.2^2))+2*x*κ*(p.1*p.2^2+rawArea l)
    rw [ih]
    have H := rawPenalty_shift l 0 (p.2^2)
    simp only [zero_add] at *
    rw [H]
    ring

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_TimeChainExactPenalty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem TimeChainModels.area {α : ℝ → ℝ} (hα : Monotone α) {s : ℝ} {l : List (ℝ × ℝ≥0)}
    (hl : TimeChainModels α s l) : (l.map (fun p => p.1*(p.2:ℝ))).sum=∫ x in s..s+chainDuration l,α x := by
  induction l generalizing s with
  | nil => simp [chainDuration]
  | cons p l ih =>
    rcases p with ⟨m,d⟩
    obtain ⟨hc,ht⟩ := hl
    have hcell : (∫ x in s..s+d,α x)=m*(d:ℝ) := by
      rw [intervalIntegral.integral_congr_Ioo_of_le (le_add_of_nonneg_right d.coe_nonneg)
        (show (Ioo s (s+d)).EqOn α (fun _ => m) from fun x hx => hc x ⟨hx.1.le,hx.2⟩),intervalIntegral.integral_const]
      simp only [add_sub_cancel_left,smul_eq_mul,mul_comm]
    simp only [List.map_cons,List.sum_cons,chainDuration_cons,NNReal.coe_add]
    rw [ih ht,← add_assoc,← intervalIntegral.integral_add_adjacent_intervals
      (hα.intervalIntegrable (a:=s) (b:=s+d)) (hα.intervalIntegrable (a:=s+d) (b:=s+d+chainDuration l)),hcell]

theorem TimeChainModels.quadraticPenalty {α : ℝ → ℝ} (hα : Monotone α) {s : ℝ} {l : List (ℝ × ℝ≥0)}
    (hl : TimeChainModels α s l) : chainQuadraticPenalty s l=2*∫ x in s..s+chainDuration l,x*α x := by
  have hi (a b : ℝ) : IntervalIntegrable (fun x => x*α x) volume a b :=
    hα.intervalIntegrable.continuousOn_mul continuous_id.continuousOn
  induction l generalizing s with
  | nil => simp [chainQuadraticPenalty,chainDuration]
  | cons p l ih =>
    rcases p with ⟨m,d⟩
    obtain ⟨hc,ht⟩ := hl
    have hcell : (∫ x in s..s+d,x*α x)=m*((s+d)^2-s^2)/2 := by
      rw [intervalIntegral.integral_congr_Ioo_of_le (le_add_of_nonneg_right d.coe_nonneg)
        (show (Ioo s (s+d)).EqOn (fun x => x*α x) (fun x => x*m) from
          fun x hx => congrArg (fun y : ℝ => x*y) (hc x ⟨hx.1.le,hx.2⟩)),intervalIntegral.integral_mul_const,integral_id]
      ring
    simp only [chainQuadraticPenalty,chainDuration_cons,NNReal.coe_add]
    rw [ih ht,← add_assoc,← intervalIntegral.integral_add_adjacent_intervals (hi s (s+d)) (hi (s+d) (s+d+chainDuration l)),hcell]
    ring

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_TimeIncrementBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem rawTimeChain_mass (l : List (ℝ × ℝ≥0)) {P : ℝ → Prop} (hm : ∀ p∈l,P p.1) :
    ∀ p∈rawTimeChain l,P p.1 := by
  intro p hp; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp; exact hm q hq

theorem rawTimeChain_sorted (l : List (ℝ × ℝ≥0)) (hs : l.Pairwise (fun p q => p.1≤q.1)) :
    (rawTimeChain l).Pairwise (fun p q => p.1≤q.1) := by
  simpa only [rawTimeChain,List.pairwise_map] using hs

theorem scalarIncrementChain_rawTimeChain (β : ℝ) (l : List (ℝ × ℝ≥0)) (f : ℝ → ℝ) :
    scalarIncrementChain (scaleIncrementChain β (rawTimeChain l)) f=scalarTimeChain β l f := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    change scalarStep p.1 (β*Real.sqrt (p.2:ℝ)) (scalarIncrementChain (scaleIncrementChain β (rawTimeChain l)) f)=_
    rw [ih]
    rfl

theorem scalarIncrementAverage_rawTimeChain (β : ℝ) (l : List (ℝ × ℝ≥0)) (f g : ℝ → ℝ) :
    scalarIncrementAverage (scaleIncrementChain β (rawTimeChain l)) f g=scalarTimeChainAverage β l f g := by
  have he : scaleIncrementChain β (rawTimeChain l)=List.ofFn (fun i : Fin l.length => ((l.get i).1,β*Real.sqrt ((l.get i).2:ℝ))) := by
    simp only [scaleIncrementChain,rawTimeChain,List.map_map]
    conv_lhs => rw [← List.ofFn_get l,List.map_ofFn]
    rfl
  rw [he,scalarIncrementAverage_ofFn]
  rfl

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_QuantileChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem quantile_knots_gap (k : ℕ) (Q : Fin (k+1) → ℝ) (i : Fin (k+1)) :
    Fin.cons (α := fun _ => ℝ) 0 Q i.succ-Fin.cons (α := fun _ => ℝ) 0 Q i.castSucc=cumulativeGapMap k Q i := by
  refine Fin.cases ?_ (fun i => ?_) i
  · simp
  · rfl

theorem quantile_prefix_chain {k : ℕ} (Q : Fin (k+1) → ℝ)
    (hQ : Monotone Q) (h0 : 0 ≤ Q 0) :
    ∃ l : List (ℝ × ℝ≥0),
      (chainDuration l:ℝ)=Q (Fin.last k) ∧
      (∀ p ∈ l, p.1 ∈ Icc (0:ℝ) 1) ∧
      TimeChainModels (quantileCDF k Q) 0 l ∧
      ∀ β f, scalarTimeChain β l f=scalarHierarchy (k+1) (quantileMass k)
        (fun i => β*Real.sqrt (cumulativeGapMap k Q i)) f := by
  let q := Fin.cons (α := fun _ => ℝ) 0 Q
  let hq := monotone_cons_zero_quantiles Q hQ h0
  let l := partitionTimeChain (k+1) q hq (quantileMass k)
  refine ⟨l,?_,?_,?_,?_⟩
  · have H := partitionTimeChain_duration (k+1) q hq (quantileMass k)
    simpa only [q,← Fin.succ_last,Fin.cons_succ,Fin.cons_zero,sub_zero] using H
  · intro p hp
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    change quantileMass k i ∈ Icc (0:ℝ) 1
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · apply (div_le_one (by positivity : (0:ℝ)<(k+1:ℕ))).mpr
      exact_mod_cast i.isLt.le
  · change TimeChainModels (quantileCDF k Q) (q 0) (partitionTimeChain (k+1) q hq (quantileMass k))
    apply partitionTimeChain_models
    intro i z hz
    exact quantileCDF_on_interval Q hQ i z hz
  · intro β f
    dsimp only [l,partitionTimeChain]
    rw [scalarTimeChain_ofFn]
    congr 2
    funext i
    simp only [NNReal.coe_mk, q]
    rw [quantile_knots_gap]
end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFAtomicRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem quantile_full_chain {k : ℕ} (Q : Fin (k+1) → ℝ)
    (hQ : Monotone Q) (h0 : 0 ≤ Q 0) (h1 : Q (Fin.last k) ≤ 1) :
    ∃ l : List (ℝ × ℝ≥0), chainDuration l=1 ∧
      (∀ p ∈ l, p.1 ∈ Icc (0:ℝ) 1) ∧ TimeChainModels (quantileCDF k Q) 0 l ∧
      ∀ β, scalarTimeChain β l scalarSpinTerminal 0=atomicScalarValue k β Q := by
  obtain ⟨l,hd,hm,hmodel,he⟩ := quantile_prefix_chain Q hQ h0
  let t := NNReal.mk (1-Q (Fin.last k)) (sub_nonneg.mpr h1)
  refine ⟨l++[(1,t)],?_,?_,?_,?_⟩
  · apply NNReal.coe_injective
    simp only [chainDuration_append,chainDuration_cons,chainDuration_nil,add_zero,
      NNReal.coe_add,hd,t,NNReal.coe_mk,NNReal.coe_one]
    ring
  · intro p hp
    rcases List.mem_append.mp hp with hp|hp
    · exact hm p hp
    · have hp' := List.mem_singleton.mp hp
      subst p
      exact ⟨zero_le_one,le_rfl⟩
  · apply hmodel.append
    constructor
    · intro z hz
      apply quantileCDF_of_last_le Q hQ
      simpa only [zero_add,hd] using hz.1
    · trivial
  · intro β
    rw [scalarTimeChain_append]
    simp only [scalarTimeChain]
    rw [he]
    rfl

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFDerivativeConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem uniform_derivative_convergence {F D : ℕ → ℝ → ℝ} {f d : ℝ → ℝ} (K : ℝ≥0)
    (hD : ∀ n x, HasDerivAt (F n) (D n x) x) (hd : ∀ x, HasDerivAt f (d x) x)
    (hLip : ∀ n, LipschitzWith K (D n)) (hlip : LipschitzWith K d)
    (hF : TendstoUniformly F f atTop) : TendstoUniformly D d atTop := by
  rw [Metric.tendstoUniformly_iff] at hF ⊢
  intro ε hε
  let h : ℝ := ε/(8*((K:ℝ)+1))
  have hh : 0<h := div_pos hε (by positivity)
  have hke : 8*((K:ℝ)+1)*h=ε := by dsimp [h]; field_simp
  let δ : ℝ := ε*h/8
  have hδ : 0<δ := by dsimp [δ]; positivity
  filter_upwards [hF δ hδ] with n hn x
  have hb (z : ℝ) : |F n z-f z|≤δ := by simpa only [Real.dist_eq,abs_sub_comm] using (hn z).le
  have H := derivative_bound_of_uniform_value_and_lipschitz _ _ (K+K) δ
    (fun z => (hD n z).sub (hd z)) ((hLip n).sub hlip) hb x h hh
  have he : 2*δ/h=ε/4 := by dsimp [δ]; field_simp; ring
  rw [he,NNReal.coe_add] at H
  rw [Real.dist_eq,abs_sub_comm]
  have hk := K.coe_nonneg
  nlinarith

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFSuffixSemigroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem quantile_suffix_chain {k : ℕ} (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hQ : Q∈admissibleQuantiles k) {s : ℝ} (hs : s∈Icc (0:ℝ) 1) :
    ∃ l : List (ℝ × ℝ≥0), chainDuration l=Real.toNNReal (1-s) ∧
      (∀ p∈l, p.1∈Icc (0:ℝ) 1) ∧ TimeChainModels (quantileCDF k Q) s l := by
  obtain ⟨l,hd,hm,hmodel,_⟩ := quantile_full_chain Q hQ.1 (hQ.2 0).1 (hQ.2 (Fin.last k)).2
  have he : chainDuration l=Real.toNNReal s+Real.toNNReal (1-s) := by
    rw [hd]
    apply NNReal.coe_injective
    rw [NNReal.coe_add,Real.coe_toNNReal s hs.1,Real.coe_toNNReal (1-s) (sub_nonneg.mpr hs.2),NNReal.coe_one]
    ring
  obtain ⟨_,l₂,_,h₂,_,hm₂,_,hs₂,_⟩ := scalarTimeChain_split_at β (quantileCDF k Q) l hm 0 hmodel _ _ he
  exact ⟨l₂,h₂,hm₂,by simpa only [zero_add,Real.coe_toNNReal s hs.1] using hs₂⟩

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_PositiveTimeChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem positiveTimeChain_mem {l : List (ℝ × ℝ≥0)} {p : ℝ × ℝ≥0} (hp : p∈positiveTimeChain l) :
    p∈l ∧ 0<p.2 := by
  simpa only [positiveTimeChain,List.mem_filter,decide_eq_true_eq,ne_eq,pos_iff_ne_zero] using hp

theorem TimeChainModels.positiveTimeChain {α : ℝ → ℝ} {s : ℝ} {l : List (ℝ × ℝ≥0)}
    (hl : TimeChainModels α s l) : TimeChainModels α s (positiveTimeChain l) := by
  induction l generalizing s with
  | nil => trivial
  | cons p l ih =>
    rcases p with ⟨m,d⟩
    obtain ⟨hc,ht⟩ := hl
    by_cases hd : d=0
    · simpa [SK.Analytic.positiveTimeChain,hd] using ih ht
    · simp only [SK.Analytic.positiveTimeChain,List.filter_cons,hd,ne_eq,not_false_eq_true,decide_true,ite_true]
      exact ⟨hc,ih ht⟩

theorem TimeChainModels.sorted {α : ℝ → ℝ} (hα : Monotone α) {s : ℝ} {l : List (ℝ × ℝ≥0)}
    (hl : TimeChainModels α s l) (hpos : ∀ p∈l,0<p.2) : l.Pairwise (fun p q => p.1≤q.1) := by
  induction l generalizing s with
  | nil => simp
  | cons p l ih =>
    rcases p with ⟨m,d⟩
    obtain ⟨hc,ht⟩ := hl
    have hd : 0<(d:ℝ) := hpos (m,d) (List.mem_cons_self ..)
    have he : α s=m := hc s ⟨le_rfl,by linarith⟩
    apply List.pairwise_cons.mpr
    constructor
    · intro q hq
      rw [← he]
      exact (hα (le_add_of_nonneg_right d.coe_nonneg)).trans
        (ht.mass_bounds hα hq (hpos q (List.mem_cons_of_mem _ hq))).1
    · exact ih ht (fun q hq => hpos q (List.mem_cons_of_mem _ hq))

theorem quantile_interval_chain {k : ℕ} (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hQ : Q∈admissibleQuantiles k) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    ∃ l : List (ℝ × ℝ≥0), (chainDuration l:ℝ)=t-s ∧
      (∀ p∈l,p.1∈Icc (0:ℝ) 1) ∧ (∀ p∈l,0<p.2) ∧ TimeChainModels (quantileCDF k Q) s l := by
  obtain ⟨l,hd,hm,hmodel⟩ := quantile_suffix_chain β Q hQ ⟨hs,hst.trans ht⟩
  have hsplit : chainDuration l=Real.toNNReal (t-s)+Real.toNNReal (1-t) := by
    rw [hd]
    apply NNReal.coe_injective
    rw [NNReal.coe_add,Real.coe_toNNReal _ (by linarith),Real.coe_toNNReal _ (by linarith),Real.coe_toNNReal _ (by linarith)]
    ring
  obtain ⟨l₁,_,hd₁,_,hm₁,_,hmodel₁,_,_⟩ := scalarTimeChain_split_at β (quantileCDF k Q) l hm s hmodel _ _ hsplit
  refine ⟨positiveTimeChain l₁,?_,fun p hp => hm₁ p (positiveTimeChain_mem hp).1,
    fun p hp => (positiveTimeChain_mem hp).2,hmodel₁.positiveTimeChain⟩
  rw [chainDuration_positiveTimeChain,hd₁,Real.coe_toNNReal _ (sub_nonneg.mpr hst)]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_TimeChainOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem TimeChainOn.sorted {α : ℝ → ℝ} (hα : Monotone α) {s t : ℝ} (l : TimeChainOn α s t) :
    l.chain.Pairwise (fun p q => p.1≤q.1) := l.models.sorted hα l.positive

theorem TimeChainOn.raw_mass {α : ℝ → ℝ} {s t : ℝ} (l : TimeChainOn α s t) :
    ∀ p∈rawTimeChain l.chain,p.1∈Icc (0:ℝ) 1 := rawTimeChain_mass _ l.mass

theorem TimeChainOn.raw_sorted {α : ℝ → ℝ} (hα : Monotone α) {s t : ℝ} (l : TimeChainOn α s t) :
    (rawTimeChain l.chain).Pairwise (fun p q => p.1≤q.1) := rawTimeChain_sorted _ (l.sorted hα)

theorem exists_quantile_TimeChainOn {k : ℕ} (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hQ : Q∈admissibleQuantiles k) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    Nonempty (TimeChainOn (quantileCDF k Q) s t) := by
  obtain ⟨l,hd,hm,hp,hmodel⟩ := quantile_interval_chain β Q hQ hs hst ht
  exact ⟨⟨l,hd,hm,hp,hmodel⟩⟩

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFCramer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarCDFValue_rootGradient (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) :
    rootGradient 0 (scalarCDFValue β α s t)=scalarCDFGradient β α s t := by
  funext x
  exact ((scalarCDFValue_regular β ha hm s t ht).1.differentiable (by norm_num) x |>.hasDerivAt).unique
    (scalarCDFValue_hasDerivAt β ha hm s t ht x)

theorem scalarCDFValue_rootHessian (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) :
    rootHessian 0 (scalarCDFValue β α s t)=scalarCDFHessian β α s t := by
  funext x
  have H : HasDerivAt (rootGradient 0 (scalarCDFValue β α s t))
      (rootHessian 0 (scalarCDFValue β α s t) x) x := by
    simpa only [parameterAxis,smul_eq_mul,mul_one,zero_add] using
      rootGradientLine_hasDerivAt 0 (scalarCDFValue_regular β ha hm s t ht) 0 x
  rw [scalarCDFValue_rootGradient β ha hm s t ht] at H
  exact H.unique (scalarCDFGradient_hasDerivAt β ha hm s t ht x)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_TimeChainOnAnalytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem TimeChainOn.sub_nonneg {α : ℝ → ℝ} {s t : ℝ} (l : TimeChainOn α s t) : 0 ≤ t-s := by
  rw [← l.duration]; positivity

theorem TimeChainOn.nn_duration {α : ℝ → ℝ} {s t : ℝ} (l : TimeChainOn α s t) :
    chainDuration l.chain=Real.toNNReal (t-s) := by
  apply NNReal.coe_injective
  rw [l.duration,Real.coe_toNNReal _ l.sub_nonneg]

theorem TimeChainOn.nn_le_one {α : ℝ → ℝ} {s t : ℝ} (l : TimeChainOn α s t) (h : t-s≤1) :
    Real.toNNReal (t-s)≤1 := by
  rw [← NNReal.coe_le_coe,Real.coe_toNNReal _ l.sub_nonneg,NNReal.coe_one]; exact h

theorem TimeChainOn.scalar_operator (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α) {s t : ℝ} (l : TimeChainOn α s t)
    (h : t-s≤1) {f : ℝ → ℝ} (hf : BoundedDerivs f) {K : ℝ≥0} (hfK : LipschitzWith K f) :
    scalarIncrementChain (scaleIncrementChain β (rawTimeChain l.chain)) f=
      scalarCDFOperator β α s (Real.toNNReal (t-s)) f := by
  rw [scalarIncrementChain_rawTimeChain]
  funext x
  exact (scalarCDFOperator_eq_chain hf hfK β ha hm l.chain l.mass s _ (l.nn_le_one h) l.nn_duration l.models x).symm

theorem TimeChainOn.scalar_value (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α) {s t : ℝ} (l : TimeChainOn α s t)
    (h : t-s≤1) :
    scalarIncrementChain (scaleIncrementChain β (rawTimeChain l.chain)) scalarSpinTerminal=
      scalarCDFValue β α s (Real.toNNReal (t-s)) :=
  l.scalar_operator β ha hm h scalarSpinTerminal_regular scalarSpinTerminal_lipschitz

theorem TimeChainOn.scalar_hessian (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α) {s t : ℝ} (l : TimeChainOn α s t)
    (h : t-s≤1) :
    rootHessian 0 (scalarIncrementChain (scaleIncrementChain β (rawTimeChain l.chain)) scalarSpinTerminal)=
      scalarCDFHessian β α s (Real.toNNReal (t-s)) := by
  rw [l.scalar_value β ha hm h,scalarCDFValue_rootHessian β ha hm s _ (l.nn_le_one h)]

theorem TimeChainOn.scalar_average (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α) {s t : ℝ} (l : TimeChainOn α s t)
    (h : t-s≤1) {f g : ℝ → ℝ} (hf : BoundedDerivs f) {K B L : ℝ≥0}
    (hfK : LipschitzWith K f) (hgL : LipschitzWith L g) (hB : ∀ z,|g z|≤B) :
    scalarIncrementAverage (scaleIncrementChain β (rawTimeChain l.chain)) f g=
      scalarCDFAverage β α s (Real.toNNReal (t-s)) f g := by
  rw [scalarIncrementAverage_rawTimeChain]
  funext x
  exact (scalarCDFAverage_eq_chainAverage_lipschitz hf hfK hgL hB β ha hm l.chain l.mass s _
    (l.nn_le_one h) l.nn_duration l.models x).symm

theorem TimeChainOn.scalar_susceptibility (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α) {q : ℝ} (hq : q∈Icc (0:ℝ) 1)
    (l : TimeChainOn α 0 q) (r : TimeChainOn α q 1) :
    scalarIncrementAverage (scaleIncrementChain β (rawTimeChain l.chain))
      (scalarIncrementChain (scaleIncrementChain β (rawTimeChain r.chain)) scalarSpinTerminal)
      (rootHessian 0 (scalarIncrementChain (scaleIncrementChain β (rawTimeChain r.chain)) scalarSpinTerminal)) 0=
      scalarCDFSusceptibilityAverage β α q := by
  have h : 1-q≤1 := by linarith [hq.1]
  rw [r.scalar_hessian β ha hm h,r.scalar_value β ha hm h]
  rw [l.scalar_average β ha hm (by linarith [hq.2])
    (scalarCDFValue_regular β ha hm q _ (r.nn_le_one h))
    (scalarCDFValue_lipschitz β ha hm q _ (r.nn_le_one h))
    (scalarCDFHessian_lipschitz β ha hm q _ (r.nn_le_one h))
    (B:=1) (scalarCDFHessian_abs_le_one β ha hm q _ (r.nn_le_one h))]
  simp only [sub_zero,scalarCDFSusceptibilityAverage]

theorem TimeChainOn.area {α : ℝ → ℝ} (hm : Monotone α) {s t : ℝ} (l : TimeChainOn α s t) :
    rawArea (rawTimeChain l.chain)=∫ x in s..t,α x := by
  rw [rawArea_rawTimeChain,l.models.area hm,l.duration,add_sub_cancel]

theorem TimeChainOn.penalty {α : ℝ → ℝ} (hm : Monotone α) {s t : ℝ} (l : TimeChainOn α s t) :
    rawPenalty (rawTimeChain l.chain) s=2*∫ x in s..t,x*α x := by
  rw [rawPenalty_rawTimeChain,l.models.quadraticPenalty hm,l.duration,add_sub_cancel]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarSpatialAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarHierarchyAverage_abs_le {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    {C : ℝ} (hg : ∀ z, |g z| ≤ C) (n : ℕ) (m v : Fin n → ℝ) (x : ℝ) :
    |scalarHierarchyAverage n m v f g x| ≤ C := by
  induction n generalizing f g with
  | zero => exact hg x
  | succ n ih =>
    exact ih (scalarStep_regular hf _ _) (scalarStepAverage_bound hf hg _ _) _ _

theorem scalarHierarchyAverage_spatial_bound (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0:ℝ) 1) (hmono : Monotone m)
    {f g : ℝ → ℝ} (hf : BoundedDerivs f) {K L C : ℝ≥0}
    (hfK : LipschitzWith K f) (hgL : LipschitzWith L g)
    (hgC : ∀ z, |g z| ≤ C) (x y : ℝ) :
    |scalarHierarchyAverage n m v f g x-scalarHierarchyAverage n m v f g y| ≤
      ((L:ℝ)+2*(C:ℝ)*Real.exp (2*(K:ℝ)))*|x-y| := by
  have hExp : 1 ≤ Real.exp (2*(K:ℝ)) := Real.one_le_exp (by positivity)
  by_cases hd : |x-y| ≤ 1
  · have H := scalarHierarchyAverage_terminal_stability n m v hm hmono
      (hf.translate x) (hf.translate y) (by positivity : 0 ≤ (K:ℝ)*|x-y|)
      (fun z => by simpa only [Real.norm_eq_abs, add_sub_add_right_eq_sub] using
        hfK.norm_sub_le (x+z) (y+z))
      (hgL.continuous.comp (continuous_const.add continuous_id))
      (hgL.continuous.comp (continuous_const.add continuous_id))
      C.coe_nonneg (fun z => hgC (x+z)) (fun z => hgC (y+z))
      (fun z => by simpa only [Function.comp_apply, Pi.add_apply, id_eq, Real.norm_eq_abs,add_sub_add_right_eq_sub] using
        hgL.norm_sub_le (x+z) (y+z)) 0
    change |scalarHierarchyAverage n m v (fun z => f (x+z)) (fun z => g (x+z)) 0 -
      scalarHierarchyAverage n m v (fun z => f (y+z)) (fun z => g (y+z)) 0| ≤ _ at H
    rw [scalarHierarchyAverage_translate,scalarHierarchyAverage_translate] at H
    simp only [add_zero] at H
    have E := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (2*(K:ℝ)))
      (by linarith : 0 ≤ 1-|x-y|) (abs_nonneg (x-y)) (by ring : 1-|x-y|+|x-y|=1)
    simp only [smul_eq_mul,mul_zero,zero_add,Real.exp_zero,mul_one] at E
    have Ee : Real.exp (2*((K:ℝ)*|x-y|))-1 ≤ Real.exp (2*(K:ℝ))*|x-y| := by
      rw [show 2*((K:ℝ)*|x-y|)=|x-y| *(2*(K:ℝ)) by ring]
      nlinarith [abs_nonneg (x-y)]
    have E2 := mul_le_mul_of_nonneg_left Ee (by positivity : 0 ≤ 2*(C:ℝ))
    nlinarith
  · have H := (abs_sub (scalarHierarchyAverage n m v f g x)
        (scalarHierarchyAverage n m v f g y)).trans
      (add_le_add (scalarHierarchyAverage_abs_le hf hgC n m v x)
        (scalarHierarchyAverage_abs_le hf hgC n m v y))
    have hlow : 2*(C:ℝ) ≤ (L:ℝ)+2*(C:ℝ)*Real.exp (2*(K:ℝ)) := by
      have := mul_le_mul_of_nonneg_left hExp (by positivity : 0 ≤ 2*(C:ℝ))
      linarith [L.coe_nonneg]
    have H2 := hlow.trans (le_mul_of_one_le_right (by positivity) (le_of_not_ge hd))
    linarith

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_WeightedAugment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem weightedCrossPenalty_append (l r : List (ℝ × (ℝ × ℝ))) (g : ℝ) :
    weightedCrossPenalty (l++r) g=weightedCrossPenalty l g+weightedCrossPenalty r (g+weightedCross l) := by
  simp only [weightedCrossPenalty,List.map_append,chainPotentialPenalty_append,chainSum,
    List.map_map,weightedCross,Function.comp_def]

@[simp] theorem weightedCrossPenalty_full (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ)) :
    weightedCrossPenalty (zeroWeightChain c++w++zeroWeightChain t) 0=weightedCrossPenalty w 0 := by
  simp [weightedCrossPenalty_append]

theorem weighted_mass_iff (w : List (ℝ × (ℝ × ℝ))) {P : ℝ → Prop} :
    (∀ p∈w,P p.1) ↔ ∀ p∈weightedUnderlying w,P p.1 := by
  constructor
  · intro H p hp; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp; exact H q hq
  · intro H p hp; exact H _ (List.mem_map.mpr ⟨p,hp,rfl⟩)

theorem weighted_sorted_iff (w : List (ℝ × (ℝ × ℝ))) :
    w.Pairwise (fun p q => p.1≤q.1) ↔ (weightedUnderlying w).Pairwise (fun p q => p.1≤q.1) := by
  simp only [weightedUnderlying,List.pairwise_map]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_WeightedListIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem weightedBranch_average (w : List (ℝ × (ℝ × ℝ))) (f g : ℝ → ℝ) :
    vectorIncrementAverage w (fun p : ℝ × ℝ => f p.1) (fun p => g p.1)=
      fun p => scalarIncrementAverage (weightedUnderlying w) f g p.1 := by
  have H := vectorIncrementAverage_pullback (ContinuousLinearMap.fst ℝ ℝ ℝ) w f g
  rw [vectorIncrementAverage_real] at H
  exact H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_TentAtomMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Set
namespace SK.Analytic

theorem scalarTentAtomMass_nonneg (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i,m i∈Icc (0:ℝ) 1) (hs : Monotone m) (l s : Fin (n+1)) :
    0 ≤ scalarTentAtomMass n m l s := by
  exact Finset.sum_nonneg (fun j _ => hierarchyAtom_nonneg n m zero_le_one (fun i => (hm i).1)
    (fun i => (hm i).2) hs j)

theorem scalarTentAtomMass_eq (n : ℕ) (m : Fin n → ℝ) (l s : Fin (n+1)) (hls : l < s) :
    scalarTentAtomMass n m l s=m ⟨s.val-1,by have := s.isLt; omega⟩-
      m ⟨l.val,by have := s.isLt; change l.val < s.val at hls; omega⟩ := by
  let i : Fin n := ⟨l.val,by have := s.isLt; change l.val < s.val at hls; omega⟩
  let k : Fin n := ⟨s.val-1,by have := s.isLt; omega⟩
  have H := congrArg₂ (fun a b : ℝ => a-b) (hierarchyAtom_tail_sum n m 1 i) (hierarchyAtom_tail_sum n m 1 k)
  rw [← Finset.sum_sub_distrib] at H
  have he : (∑ j : Fin (n+1), ((if i.val<j.val then hierarchyAtom n m 1 j else 0)-
      (if k.val<j.val then hierarchyAtom n m 1 j else 0)))=scalarTentAtomMass n m l s := by
    unfold scalarTentAtomMass
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    have hls' : l.val < s.val := hls
    dsimp only [i,k]
    by_cases hlj : l.val<j.val
    · by_cases hjs : j.val < s.val
      · simp only [hlj,show ¬s.val-1<j.val by omega,ite_true,ite_false,sub_zero]
        rw [ite_eq_left ⟨hlj,hjs⟩]
      · simp only [hlj,show s.val-1<j.val by omega,ite_true,sub_self]
        rw [ite_eq_right (by intro h; exact hjs h.2)]
    · simp only [hlj,show ¬s.val-1<j.val by omega,ite_false,sub_self]
      rw [ite_eq_right (by intro h; exact hlj h.1)]
  rw [he] at H
  dsimp only [i,k] at H
  linarith

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_FourBlockAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Set
namespace SK.Analytic

theorem fourBlockTent_atom_le (κ : ℝ) (b l j k : List (ℝ × ℝ))
    (hl : 0<l.length) (hj : 0<j.length) {a d : ℝ}
    (hlo : ∀ p∈l,a≤p.1) (hhi : ∀ p∈j,p.1≤d) :
    scalarTentAtomMass (fourBlockTent κ b l j k).length (fun i => ((fourBlockTent κ b l j k).get i).1)
      (fourBlockLeft κ b l j k) (fourBlockRight κ b l j k)≤d-a := by
  have hls : fourBlockLeft κ b l j k<fourBlockRight κ b l j k := by
    change b.length<b.length+l.length+j.length
    omega
  rw [scalarTentAtomMass_eq _ _ _ _ hls]
  have HI := hhi (j.get ⟨j.length-1,by omega⟩) (List.get_mem ..)
  have HL := hlo (l.get ⟨0,hl⟩) (List.get_mem ..)
  have he1 : ((fourBlockTent κ b l j k).get
      ⟨(fourBlockRight κ b l j k).val-1,by have := (fourBlockRight κ b l j k).isLt; omega⟩).1=
      (j.get ⟨j.length-1,by omega⟩).1 := by
    simp only [List.get_eq_getElem,fourBlockTent,zeroWeightChain,constantWeightChain,
      List.getElem_append,List.length_append,List.length_map]
    simp (disch := omega) only [dite_eq_right,dite_eq_left,List.getElem_map]
    congr 2
    omega
  have he2 : ((fourBlockTent κ b l j k).get
      ⟨(fourBlockLeft κ b l j k).val,by change b.length<(fourBlockTent κ b l j k).length; rw [fourBlockTent_length]; omega⟩).1=
      (l.get ⟨0,hl⟩).1 := by
    simp only [List.get_eq_getElem,fourBlockTent,zeroWeightChain,constantWeightChain,
      List.getElem_append,List.length_append,List.length_map]
    simp (disch := omega) only [dite_eq_right,dite_eq_left,List.getElem_map,Nat.sub_self]
  rw [he1,he2]
  linarith

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_FourBlockMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Set
namespace SK.Analytic

theorem fourBlockTent_underlying (κ : ℝ) (b l j k : List (ℝ × ℝ)) :
    weightedUnderlying (fourBlockTent κ b l j k)=(b++l)++(j++k) := by
  simp [fourBlockTent]

theorem fourBlockTent_mass (κ : ℝ) (b l j k : List (ℝ × ℝ))
    (hm : ∀ p∈(b++l)++(j++k),p.1∈Icc (0:ℝ) 1) :
    ∀ p∈fourBlockTent κ b l j k,p.1∈Icc (0:ℝ) 1 := by
  apply (weighted_mass_iff _ (P:=fun x => x∈Icc (0:ℝ) 1)).mpr
  rw [fourBlockTent_underlying]; exact hm

theorem fourBlockTent_sorted (κ : ℝ) (b l j k : List (ℝ × ℝ))
    (hs : ((b++l)++(j++k)).Pairwise (fun p q => p.1≤q.1)) :
    (fourBlockTent κ b l j k).Pairwise (fun p q => p.1≤q.1) := by
  apply (weighted_sorted_iff _).mpr
  rw [fourBlockTent_underlying]; exact hs

theorem narrowTentError_mono {μ B R A ω : ℝ} (hμ : 0≤μ) (hB : 0≤B) (hA : 0≤A) (hAω : A≤ω) :
    narrowTentError μ B R A≤narrowTentError μ B R ω := by
  have HA := mul_le_mul_of_nonneg_left hAω hB
  have HS := sq_le_sq₀ (mul_nonneg hB hA) (mul_nonneg hB (hA.trans hAω))
  have H1 := mul_le_mul_of_nonneg_left hAω (show 0≤2*μ*B by positivity)
  have H2 := mul_le_mul_of_nonneg_left hAω (sq_nonneg B)
  dsimp [narrowTentError]
  nlinarith [(HS.mpr HA)]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_NarrowTimeBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

namespace NarrowTimeBlocks
variable {α : ℝ → ℝ} {r h q : ℝ} (B : NarrowTimeBlocks α r h q)

theorem common_raw (a : ℝ) : rawTimeChain B.common.chain=weightedUnderlying (B.c a) := by
  simp only [common,TimeChainOn.append,rawTimeChain_append,c_underlying,b,l]
theorem middle_raw (a : ℝ) : rawTimeChain B.middle.chain=weightedUnderlying (B.w a) := by
  simp only [middle,TimeChainOn.append,rawTimeChain_append,w_underlying,j,k]
theorem front_raw (a : ℝ) : rawTimeChain B.front.chain=weightedUnderlying (B.c a)++weightedUnderlying (B.w a) := by
  rw [front,TimeChainOn.append,rawTimeChain_append,B.common_raw a,B.middle_raw a]
theorem full_raw (a : ℝ) : rawTimeChain B.full.chain=weightedUnderlying (B.c a)++weightedUnderlying (B.w a)++B.t := by
  rw [full,TimeChainOn.append,rawTimeChain_append,B.front_raw a]; rfl

@[simp] theorem common_variance (a : ℝ) : rawVariance (weightedUnderlying (B.c a))=r := by
  rw [← B.common_raw a,rawVariance_rawTimeChain,B.common.duration,sub_zero]
@[simp] theorem front_variance (a : ℝ) : rawVariance (weightedUnderlying (B.c a)++weightedUnderlying (B.w a))=q := by
  rw [← B.front_raw a,rawVariance_rawTimeChain,B.front.duration,sub_zero]
@[simp] theorem full_variance (a : ℝ) : rawVariance (weightedUnderlying (B.c a)++weightedUnderlying (B.w a)++B.t)=1 := by
  rw [← B.full_raw a,rawVariance_rawTimeChain,B.full.duration,sub_zero]

theorem cross_stats (hh : h≠0) (a θ : ℝ) :
    weightedCross (B.c a)=a ∧ weightedCross (B.v θ)=θ ∧ weightedCross (B.w a)=-a := by
  simp only [c,v,w,weightedCross_append,weightedCross_zeroWeight,constantWeightChain_cross,B.l_variance,B.j_variance,zero_add,add_zero]
  field_simp
  simp

theorem variance_stats (hh : h≠0) (a θ : ℝ) :
    narrowVariance (B.c a) (B.v θ) (B.w a)=(2*a^2+θ^2)/h := by
  simp only [narrowVariance,c,v,w,weightedVariance_append,weightedVariance_zeroWeight,constantWeightChain_variance,B.l_variance,B.j_variance,zero_add,add_zero]
  field_simp
  ring

theorem absCross_stats (hh : 0<h) {a θ : ℝ} (ha : 0 ≤ a) (hθ : 0 ≤ θ) :
    narrowAbsCross (B.c a) (B.v θ) (B.w a)=5*a+θ := by
  simp only [narrowAbsCross,c,v,w,weightedAbsCross_append,weightedAbsCross_zeroWeight,constantWeightChain_absCross,B.l_variance,B.j_variance,zero_add,add_zero]
  rw [abs_of_nonneg (div_nonneg ha hh.le),abs_of_nonneg (div_nonneg hθ hh.le),abs_div,abs_neg,abs_of_nonneg ha,abs_of_pos hh]
  field_simp
  ring

theorem v_mean (θ : ℝ) : weightedMean (B.v θ)=(θ/h)*rawArea B.j := by
  simp [v]

end NarrowTimeBlocks

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_NegativePenalty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Set
namespace SK.Analytic

theorem rawArea_bounds (l : List (ℝ × ℝ)) {a b : ℝ} (hm : ∀ p∈l,p.1∈Icc a b) :
    rawArea l∈Icc (a*rawVariance l) (b*rawVariance l) := by
  induction l with
  | nil => simp [rawArea,rawVariance]
  | cons p l ih =>
    have hp := hm p (List.mem_cons_self ..)
    have H := ih (fun z hz => hm z (List.mem_cons_of_mem _ hz))
    change p.1*p.2^2+rawArea l∈Icc (a*(p.2^2+rawVariance l)) (b*(p.2^2+rawVariance l))
    constructor
    · nlinarith [H.1,mul_le_mul_of_nonneg_right hp.1 (sq_nonneg p.2)]
    · nlinarith [H.2,mul_le_mul_of_nonneg_right hp.2 (sq_nonneg p.2)]

theorem rawPenalty_negative_bounds (l : List (ℝ × ℝ)) {a b q : ℝ}
    (hm : ∀ p∈l,p.1∈Icc a b) (hq : q+rawVariance l ≤ 0) :
    rawPenalty l q∈Icc (b*((q+rawVariance l)^2-q^2)) (a*((q+rawVariance l)^2-q^2)) := by
  induction l generalizing q with
  | nil => simp [rawPenalty,rawVariance,chainPotentialPenalty]
  | cons p l ih =>
    have hp := hm p (List.mem_cons_self ..)
    change q+(p.2^2+rawVariance l) ≤ 0 at hq
    have H := ih (fun z hz => hm z (List.mem_cons_of_mem _ hz)) (q:=q+p.2^2) (by linarith)
    have hsum : 2*q+p.2^2 ≤ 0 := by nlinarith [rawVariance_nonneg l,sq_nonneg p.2]
    have hΔ : (q+p.2^2)^2-q^2 ≤ 0 := by
      nlinarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg p.2) hsum]
    change p.1*((q+p.2^2)^2-q^2)+rawPenalty l (q+p.2^2)∈
      Icc (b*((q+(p.2^2+rawVariance l))^2-q^2)) (a*((q+(p.2^2+rawVariance l))^2-q^2))
    constructor
    · have H' := add_le_add (mul_le_mul_of_nonpos_right hp.2 hΔ) H.1
      convert H' using 1
      all_goals try with_reducible_and_instances rfl
      ring
    · have H' := add_le_add (mul_le_mul_of_nonpos_right hp.1 hΔ) H.2
      convert H' using 1
      all_goals try with_reducible_and_instances rfl
      ring

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_NarrowBlockPenalty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open Set
namespace SK.Analytic

theorem TimeChainOn.raw_mass_interval {α : ℝ → ℝ} (hα : Monotone α) {s t : ℝ} (l : TimeChainOn α s t) :
    ∀ p∈rawTimeChain l.chain,p.1∈Icc (α s) (α t) := by
  apply rawTimeChain_mass
  intro p hp
  have H := l.models.mass_bounds hα hp (l.positive p hp)
  change α s ≤ p.1 ∧ p.1 ≤ α t
  simpa only [l.duration,add_sub_cancel] using H

namespace NarrowTimeBlocks
variable {α : ℝ → ℝ} {r h q : ℝ} (B : NarrowTimeBlocks α r h q)

theorem crossPenalty_lower (hα : Monotone α) (hh : 0<h) {a θ : ℝ} (ha : 0 ≤ a) (hθ : 0 ≤ θ) :
    α r*(2*a*θ+θ^2)-a^2*(α (r+h)-α (r-h)) ≤ narrowCrossPenalty (B.c a) (B.v θ) (B.w a) := by
  have hn : h≠0 := ne_of_gt hh
  have hstats := B.cross_stats hn a θ
  have hc : weightedCrossPenalty (B.c a) 0=(a/h)^2*rawPenalty B.l 0 := by
    simp [c,weightedCrossPenalty_append]
  have hv : weightedCrossPenalty (B.v θ) a=(θ/h)^2*rawPenalty B.j 0+2*a*(θ/h)*rawArea B.j := by
    simp [v,weightedCrossPenalty_append,constantWeightChain_penalty_offset]
  have hw : weightedCrossPenalty (B.w a) a=(a/h)^2*rawPenalty B.j (-h) := by
    have he : (-a/h)*(-h)=a := by field_simp
    have H := constantWeightChain_penalty (-a/h) B.j (-h)
    rw [he] at H
    simpa only [w,weightedCrossPenalty_append,weightedCrossPenalty_zeroWeight,add_zero,div_pow,neg_sq] using H
  have HL := (rawPenalty_bounds B.l (B.left.raw_mass_interval hα) (q:=0) le_rfl).1
  have HJ := (rawPenalty_bounds B.j (B.right.raw_mass_interval hα) (q:=0) le_rfl).1
  have HW := (rawPenalty_negative_bounds B.j (B.right.raw_mass_interval hα) (q:=-h) (by rw [B.j_variance]; linarith)).1
  have HA := (rawArea_bounds B.j (B.right.raw_mass_interval hα)).1
  simp only [B.l_variance,B.j_variance,zero_add,zero_pow (by norm_num : (2:ℕ)≠0),sub_zero] at HL HJ HA
  rw [B.j_variance] at HW
  have NL : α (r-h)*a^2 ≤ (a/h)^2*rawPenalty B.l 0 := by
    calc
      _ = (a/h)^2*(α (r-h)*h^2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left HL (sq_nonneg _)
  have NJ : α r*θ^2 ≤ (θ/h)^2*rawPenalty B.j 0 := by
    calc
      _ = (θ/h)^2*(α r*h^2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left HJ (sq_nonneg _)
  have NW : -α (r+h)*a^2 ≤ (a/h)^2*rawPenalty B.j (-h) := by
    calc
      _ = (a/h)^2*(α (r+h)*((-h+h)^2-(-h)^2)) := by field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left HW (sq_nonneg (a/h))
  have NA : 2*a*θ*α r ≤ 2*a*(θ/h)*rawArea B.j := by
    calc
      _ = (2*a*(θ/h))*(α r*h) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left HA (by positivity)
  rw [narrowCrossPenalty,hstats.1,hc,hv,hw]
  nlinarith

end NarrowTimeBlocks

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_NarrowBlockStats
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Set
namespace SK.Analytic

theorem rawVariance_pos_length {l : List (ℝ × ℝ)} (h : 0 < rawVariance l) : 0<l.length := by
  cases l with
  | nil => simp [rawVariance] at h
  | cons p l => simp

namespace NarrowTimeBlocks
variable {α : ℝ → ℝ} {r h q : ℝ} (C : NarrowTimeBlocks α r h q)

theorem v_absCross (hh : 0<h) {θ : ℝ} (hθ : 0≤θ) : weightedAbsCross (C.v θ)=θ := by
  simp only [v,weightedAbsCross_append,weightedAbsCross_zeroWeight,constantWeightChain_absCross,C.j_variance,add_zero]
  rw [abs_of_nonneg (div_nonneg hθ hh.le)]
  field_simp

theorem v_mean_bounds (hα : Monotone α) (hh : 0<h) {θ : ℝ} (hθ : 0≤θ) :
    weightedMean (C.v θ)∈Icc (θ*α r) (θ*α (r+h)) := by
  have HA := rawArea_bounds C.j (C.right.raw_mass_interval hα)
  rw [C.j_variance] at HA
  rw [C.v_mean]
  have hl := mul_le_mul_of_nonneg_left HA.1 (div_nonneg hθ hh.le)
  have hu := mul_le_mul_of_nonneg_left HA.2 (div_nonneg hθ hh.le)
  constructor
  · convert hl using 1; field_simp
  · convert hu using 1; field_simp

end NarrowTimeBlocks

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_NarrowMomentBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem narrowSusceptibility_eq (c w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ)) :
    narrowSusceptibility c w t=scalarIncrementAverage (weightedUnderlying (c++w))
      (scalarIncrementChain t scalarSpinTerminal) (rootHessian 0 (scalarIncrementChain t scalarSpinTerminal)) 0 := by
  dsimp only [narrowSusceptibility]
  rw [weightedBranch_average,weightedBranch_average,weightedUnderlying_append,scalarIncrementAverage_append]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFIntervalConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFValue_tendstoUniformly_interval (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (hn : ∀ n z, αn n z∈Icc (0:ℝ) 1) (hnm : ∀ n, Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (hs : 0 ≤ s) (hst : s + t ≤ 1) :
    TendstoUniformly (fun n => scalarCDFValue β (αn n) s t)
      (scalarCDFValue β α s t) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have HT : Tendsto (fun n => scalarTimeMassConstant β*cdfDistance (αn n) α) atTop (𝓝 0) := by
    simpa only [mul_zero] using hD.const_mul (scalarTimeMassConstant β)
  filter_upwards [(tendsto_order.mp HT).2 ε hε] with n hn' x
  have H := scalarCDFValue_cdf_lipschitz β (hn n) (hnm n) hα hαm s t ht x
  have HE := cdfDistance_subinterval_le (hnm n) hαm hs hst
  have HB := H.trans (mul_le_mul_of_nonneg_left HE (scalarTimeMassConstant_nonneg β))
  rw [Real.dist_eq,abs_sub_comm]
  exact HB.trans_lt hn'

theorem scalarCDFHessian_tendstoUniformly_interval (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (hn : ∀ n z, αn n z∈Icc (0:ℝ) 1) (hnm : ∀ n, Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (hs : 0 ≤ s) (hst : s + t ≤ 1) :
    TendstoUniformly (fun n => scalarCDFHessian β (αn n) s t)
      (scalarCDFHessian β α s t) atTop := by
  apply uniform_derivative_convergence susceptibilityLipschitzConstant
    (fun n x => scalarCDFGradient_hasDerivAt β (hn n) (hnm n) s t ht x)
    (scalarCDFGradient_hasDerivAt β hα hαm s t ht)
    (fun n => scalarCDFHessian_lipschitz β (hn n) (hnm n) s t ht)
    (scalarCDFHessian_lipschitz β hα hαm s t ht)
  exact uniform_derivative_convergence 1
    (fun n x => scalarCDFValue_hasDerivAt β (hn n) (hnm n) s t ht x)
    (scalarCDFValue_hasDerivAt β hα hαm s t ht)
    (fun n => scalarCDFGradient_lipschitz β (hn n) (hnm n) s t ht)
    (scalarCDFGradient_lipschitz β hα hαm s t ht)
    (scalarCDFValue_tendstoUniformly_interval β hα hαm hn hnm hD s t ht hs hst)

theorem scalarCDFAverage_tendsto_cdf_lipschitz (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (hn : ∀ n z, αn n z∈Icc (0:ℝ) 1) (hnm : ∀ n, Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    {f g : ℝ → ℝ} (hf : BoundedDerivs f) {K B L : ℝ≥0}
    (hfK : LipschitzWith K f) (hgL : LipschitzWith L g) (hB : ∀ z, |g z|≤B)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (hs : 0 ≤ s) (hst : s + t ≤ 1) (x : ℝ) :
    Tendsto (fun n => scalarCDFAverage β (αn n) s t f g x) atTop
      (𝓝 (scalarCDFAverage β α s t f g x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let A : ℝ := 2*((L:ℝ)+2*(B:ℝ)^2)
  have hA : 0≤A := by dsimp [A]; positivity
  let h : ℝ := ε/(4*(A+1))
  have hh : 0<h := by dsimp [h]; positivity
  have hsmall : A*h<ε := by
    have HE : 4*(A+1)*h=ε := by dsimp [h]; field_simp
    nlinarith
  have HT : Tendsto (fun n =>
      2*(scalarTimeMassConstantK β (K+B+B)*cdfDistance (αn n) α)/h+A*h) atTop (𝓝 (A*h)) := by
    simpa only [mul_zero,zero_div,zero_add] using
      (((hD.const_mul (scalarTimeMassConstantK β (K+B+B))).const_mul 2).div_const h).add_const (A*h)
  filter_upwards [(tendsto_order.mp HT).2 ε hsmall] with n hbound
  rw [Real.dist_eq]
  have H := scalarCDFAverage_cdf_stability_lipschitz β (hn n) (hnm n) hα hαm
    hf hfK hgL hB s t ht x h hh
  have HD := cdfDistance_subinterval_le (hnm n) hαm hs hst
  apply (H.trans ?_).trans_lt hbound
  exact add_le_add (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left HD (scalarTimeMassConstantK_nonneg β _)) (by norm_num : (0:ℝ)≤2)) hh.le) le_rfl

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleScaleStats
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem scaleIncrementChain_mass {E : Type} [SMul ℝ E] (β : ℝ) (l : List (ℝ × E)) {P : ℝ → Prop}
    (hm : ∀ p∈l,P p.1) : ∀ p∈scaleIncrementChain β l,P p.1 := by
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact hm q hq

theorem scaleIncrementChain_sorted {E : Type} [SMul ℝ E] (β : ℝ) (l : List (ℝ × E))
    (hs : l.Pairwise (fun p q => p.1≤q.1)) : (scaleIncrementChain β l).Pairwise (fun p q => p.1≤q.1) := by
  simpa only [scaleIncrementChain,List.pairwise_map] using hs

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarHessianFloor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarSusceptibilityFloor_pos (T A : ℝ) : 0 < scalarSusceptibilityFloor T A := by
  unfold scalarSusceptibilityFloor
  positivity

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFUniformAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFAverage_tendstoUniformly_cdf_lipschitz (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (hn : ∀ n z, αn n z∈Icc (0:ℝ) 1) (hnm : ∀ n, Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    {f g : ℝ → ℝ} (hf : BoundedDerivs f) {K B L : ℝ≥0}
    (hfK : LipschitzWith K f) (hgL : LipschitzWith L g) (hB : ∀ z, |g z|≤B)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (hs : 0 ≤ s) (hst : s + t ≤ 1) :
    TendstoUniformly (fun n => scalarCDFAverage β (αn n) s t f g)
      (scalarCDFAverage β α s t f g) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  let A : ℝ := 2*((L:ℝ)+2*(B:ℝ)^2)
  have hA : 0≤A := by dsimp [A]; positivity
  let h : ℝ := ε/(4*(A+1))
  have hh : 0<h := by dsimp [h]; positivity
  have hsmall : A*h<ε := by
    have HE : 4*(A+1)*h=ε := by dsimp [h]; field_simp
    nlinarith
  have HT : Tendsto (fun n =>
      2*(scalarTimeMassConstantK β (K+B+B)*cdfDistance (αn n) α)/h+A*h) atTop (𝓝 (A*h)) := by
    simpa only [mul_zero,zero_div,zero_add] using
      (((hD.const_mul (scalarTimeMassConstantK β (K+B+B))).const_mul 2).div_const h).add_const (A*h)
  filter_upwards [(tendsto_order.mp HT).2 ε hsmall] with n hbound x
  rw [Real.dist_eq,abs_sub_comm]
  have H := scalarCDFAverage_cdf_stability_lipschitz β (hn n) (hnm n) hα hαm
    hf hfK hgL hB s t ht x h hh
  have HD := cdfDistance_subinterval_le (hnm n) hαm hs hst
  apply (H.trans ?_).trans_lt hbound
  exact add_le_add (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left HD (scalarTimeMassConstantK_nonneg β _)) (by norm_num : (0:ℝ)≤2)) hh.le) le_rfl

theorem scalarCDFAverage_abs_le (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    {f g : ℝ → ℝ} (hf : BoundedDerivs f) {K L B : ℝ≥0}
    (hfK : LipschitzWith K f) (hgL : LipschitzWith L g) (hB : ∀ z,|g z|≤B)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (x : ℝ) :
    |scalarCDFAverage β α s t f g x|≤B := by
  apply le_of_tendsto (dyadicScalarAverage_tendsto_lipschitz β hα hm hf hfK hgL hB s t ht x).abs
  exact Eventually.of_forall (fun n => scalarHierarchyAverage_abs_le hf hB _ _ _ _)

theorem scalarCDFAverage_lipschitz (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    {f g : ℝ → ℝ} (hf : BoundedDerivs f) {K L B : ℝ≥0}
    (hfK : LipschitzWith K f) (hgL : LipschitzWith L g) (hB : ∀ z,|g z|≤B)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) :
    LipschitzWith (L+2*B*Real.toNNReal (Real.exp (2*(K:ℝ)))) (scalarCDFAverage β α s t f g) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq,NNReal.coe_add,NNReal.coe_mul,NNReal.coe_ofNat,
    Real.coe_toNNReal _ (Real.exp_pos _).le]
  apply le_of_tendsto ((dyadicScalarAverage_tendsto_lipschitz β hα hm hf hfK hgL hB s t ht x).sub
    (dyadicScalarAverage_tendsto_lipschitz β hα hm hf hfK hgL hB s t ht y)).abs
  apply Eventually.of_forall
  intro n
  apply scalarHierarchyAverage_spatial_bound _ _ _
    (fun i => dyadicIntervals_mass_bounds hα n s t (List.get_mem _ _)) (fun i j hij => ?_)
    hf hfK hgL hB x y
  rcases lt_or_eq_of_le hij with hij|rfl
  · exact List.pairwise_iff_get.mp (dyadicIntervals_pairwise hm n s t) i j hij
  · exact le_rfl

theorem scalarCDFAverage_tendstoUniformly_varying (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (hα : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    (hn : ∀ n z,αn n z∈Icc (0:ℝ) 1) (hnm : ∀ n,Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    {f g : ℝ → ℝ} {fn gn : ℕ → ℝ → ℝ}
    (hf : BoundedDerivs f) (hfn : ∀ n,BoundedDerivs (fn n)) {K L B : ℝ≥0}
    (hfK : LipschitzWith K f) (hfnK : ∀ n,LipschitzWith K (fn n))
    (hgL : LipschitzWith L g) (hgnL : ∀ n,LipschitzWith L (gn n))
    (hgB : ∀ z,|g z|≤B) (hgnB : ∀ n z,|gn n z|≤B)
    (hfU : TendstoUniformly fn f atTop) (hgU : TendstoUniformly gn g atTop)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (hs : 0 ≤ s) (hst : s + t ≤ 1) :
    TendstoUniformly (fun n => scalarCDFAverage β (αn n) s t (fn n) (gn n))
      (scalarCDFAverage β α s t f g) atTop := by
  have hfix := scalarCDFAverage_tendstoUniformly_cdf_lipschitz β hα hm hn hnm hD hf hfK hgL hgB s t ht hs hst
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  let φ : ℝ → ℝ := fun e => 2*e+2*(B:ℝ)*(Real.exp (2*e)-1)
  have hφ : ContinuousAt φ 0 := by dsimp [φ]; fun_prop
  obtain ⟨δ,hδ,hbound⟩ := Metric.continuousAt_iff.mp hφ ε hε
  let e := δ/2
  have he : 0<e := half_pos hδ
  have hsmall : φ e<ε := by
    have H := hbound (show dist e 0<δ by rw [Real.dist_eq,sub_zero,abs_of_pos he]; dsimp [e]; linarith)
    have hz : φ 0=0 := by simp [φ]
    rw [hz,Real.dist_eq,sub_zero] at H
    exact (le_abs_self _).trans_lt H
  filter_upwards [Metric.tendstoUniformly_iff.mp hfU e he,
    Metric.tendstoUniformly_iff.mp hgU e he,Metric.tendstoUniformly_iff.mp hfix e he] with n hfn' hgn' hfix' x
  have H := scalarCDFAverage_terminal_stability_lipschitz β (hn n) (hnm n) (hfn n) hf
    (hfnK n) hfK (hgnL n) hgL (hgnB n) hgB he.le
    (fun z => by simpa only [Real.dist_eq,abs_sub_comm] using (hfn' z).le)
    (fun z => by simpa only [Real.dist_eq,abs_sub_comm] using (hgn' z).le) s t ht x
  have hf' := hfix' x
  rw [Real.dist_eq,abs_sub_comm] at hf' ⊢
  have HT := abs_sub_le (scalarCDFAverage β (αn n) s t (fn n) (gn n) x)
    (scalarCDFAverage β (αn n) s t f g x) (scalarCDFAverage β α s t f g x)
  have HA : |scalarCDFAverage β (αn n) s t (fn n) (gn n) x-scalarCDFAverage β α s t f g x|<φ e := by
    dsimp [φ]
    linarith
  exact HA.trans hsmall

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFJointSusceptibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFConditionalSusceptibility_regular (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α) {r q : ℝ}
    (hr : 0 ≤ r) (hrq : r≤q) (hq : q≤1) :
    LipschitzWith conditionalSusceptibilityLipschitz (scalarCDFConditionalSusceptibility β α r q) ∧
      ∀ x,|scalarCDFConditionalSusceptibility β α r q x|≤1 := by
  have hs : Real.toNNReal (1-q)≤1 := by rw [← NNReal.coe_le_coe,Real.coe_toNNReal _ (by linarith),NNReal.coe_one]; linarith
  have ht : Real.toNNReal (q-r)≤1 := by rw [← NNReal.coe_le_coe,Real.coe_toNNReal _ (by linarith),NNReal.coe_one]; linarith
  have H := scalarCDFAverage_lipschitz β ha hm
    (scalarCDFValue_regular β ha hm q _ hs) (scalarCDFValue_lipschitz β ha hm q _ hs)
    (scalarCDFHessian_lipschitz β ha hm q _ hs) (B:=1) (scalarCDFHessian_abs_le_one β ha hm q _ hs) r _ ht
  refine ⟨?_,fun x => scalarCDFAverage_abs_le β ha hm
    (scalarCDFValue_regular β ha hm q _ hs) (scalarCDFValue_lipschitz β ha hm q _ hs)
    (scalarCDFHessian_lipschitz β ha hm q _ hs) (B:=1) (scalarCDFHessian_abs_le_one β ha hm q _ hs) r _ ht x⟩
  simpa only [scalarCDFConditionalSusceptibility,conditionalSusceptibilityLipschitz,NNReal.coe_one,mul_one] using H

theorem scalarCDFConditionalSusceptibility_tendstoUniformly (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    (hn : ∀ n z,αn n z∈Icc (0:ℝ) 1) (hnm : ∀ n,Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    {r q : ℝ} (hr : 0 ≤ r) (hrq : r≤q) (hq : q≤1) :
    TendstoUniformly (fun n => scalarCDFConditionalSusceptibility β (αn n) r q)
      (scalarCDFConditionalSusceptibility β α r q) atTop := by
  have hs0 : (Real.toNNReal (1-q):ℝ)=1-q := Real.coe_toNNReal _ (by linarith)
  have ht0 : (Real.toNNReal (q-r):ℝ)=q-r := Real.coe_toNNReal _ (by linarith)
  have hs : Real.toNNReal (1-q)≤1 := by rw [← NNReal.coe_le_coe,hs0,NNReal.coe_one]; linarith
  have ht : Real.toNNReal (q-r)≤1 := by rw [← NNReal.coe_le_coe,ht0,NNReal.coe_one]; linarith
  exact scalarCDFAverage_tendstoUniformly_varying β ha hm hn hnm hD
    (scalarCDFValue_regular β ha hm q _ hs) (fun n => scalarCDFValue_regular β (hn n) (hnm n) q _ hs)
    (scalarCDFValue_lipschitz β ha hm q _ hs) (fun n => scalarCDFValue_lipschitz β (hn n) (hnm n) q _ hs)
    (scalarCDFHessian_lipschitz β ha hm q _ hs) (fun n => scalarCDFHessian_lipschitz β (hn n) (hnm n) q _ hs)
    (B:=1) (scalarCDFHessian_abs_le_one β ha hm q _ hs) (fun n => scalarCDFHessian_abs_le_one β (hn n) (hnm n) q _ hs)
    (scalarCDFValue_tendstoUniformly_interval β ha hm hn hnm hD q _ hs (hr.trans hrq) (by rw [hs0]; linarith))
    (scalarCDFHessian_tendstoUniformly_interval β ha hm hn hnm hD q _ hs (hr.trans hrq) (by rw [hs0]; linarith))
    r _ ht hr (by rw [ht0]; linarith)

theorem scalarCDFJointSusceptibilityTest_regular (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α) {r q : ℝ}
    (hr : 0 ≤ r) (hrq : r≤q) (hq : q≤1) :
    LipschitzWith (susceptibilityLipschitzConstant+conditionalSusceptibilityLipschitz)
      (scalarCDFJointSusceptibilityTest β α r q) ∧
    ∀ x,|scalarCDFJointSusceptibilityTest β α r q x|≤1 := by
  have hs : Real.toNNReal (1-r)≤1 := by
    rw [← NNReal.coe_le_coe,Real.coe_toNNReal _ (by linarith),NNReal.coe_one]; linarith
  have H := scalarCDFConditionalSusceptibility_regular β ha hm hr hrq hq
  refine ⟨unitBoundedProduct_lipschitz (scalarCDFHessian_lipschitz β ha hm r _ hs) H.1
    (scalarCDFHessian_abs_le_one β ha hm r _ hs) H.2,?_⟩
  intro x
  exact unitBoundedProduct_abs_le (scalarCDFHessian_abs_le_one β ha hm r _ hs x) (H.2 x)

theorem scalarCDFJointSusceptibilityTest_tendstoUniformly (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    (hn : ∀ n z,αn n z∈Icc (0:ℝ) 1) (hnm : ∀ n,Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    {r q : ℝ} (hr : 0 ≤ r) (hrq : r≤q) (hq : q≤1) :
    TendstoUniformly (fun n => scalarCDFJointSusceptibilityTest β (αn n) r q)
      (scalarCDFJointSusceptibilityTest β α r q) atTop := by
  have hs0 : (Real.toNNReal (1-r):ℝ)=1-r := Real.coe_toNNReal _ (by linarith)
  have hs : Real.toNNReal (1-r)≤1 := by rw [← NNReal.coe_le_coe,hs0,NNReal.coe_one]; linarith
  exact unitBoundedProduct_tendstoUniformly
    (fun n => (scalarCDFConditionalSusceptibility_regular β (hn n) (hnm n) hr hrq hq).2)
    (scalarCDFHessian_abs_le_one β ha hm r _ hs)
    (scalarCDFHessian_tendstoUniformly_interval β ha hm hn hnm hD r _ hs hr (by rw [hs0]; linarith))
    (scalarCDFConditionalSusceptibility_tendstoUniformly β ha hm hn hnm hD hr hrq hq)

theorem scalarCDFJointSusceptibility_tendsto (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    (hn : ∀ n z,αn n z∈Icc (0:ℝ) 1) (hnm : ∀ n,Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    {r q : ℝ} (hr : 0 ≤ r) (hrq : r≤q) (hq : q≤1) :
    Tendsto (fun n => scalarCDFJointSusceptibility β (αn n) r q) atTop
      (𝓝 (scalarCDFJointSusceptibility β α r q)) := by
  have hs0 : (Real.toNNReal (1-r):ℝ)=1-r := Real.coe_toNNReal _ (by linarith)
  have ht0 : (Real.toNNReal r:ℝ)=r := Real.coe_toNNReal _ hr
  have hs : Real.toNNReal (1-r)≤1 := by rw [← NNReal.coe_le_coe,hs0,NNReal.coe_one]; linarith
  have ht : Real.toNNReal r≤1 := by rw [← NNReal.coe_le_coe,ht0,NNReal.coe_one]; linarith
  have hg := scalarCDFJointSusceptibilityTest_regular β ha hm hr hrq hq
  have hgn (n) := scalarCDFJointSusceptibilityTest_regular β (hn n) (hnm n) hr hrq hq
  have HP := scalarCDFJointSusceptibilityTest_tendstoUniformly β ha hm hn hnm hD hr hrq hq
  exact (scalarCDFAverage_tendstoUniformly_varying β ha hm hn hnm hD
    (scalarCDFValue_regular β ha hm r _ hs) (fun n => scalarCDFValue_regular β (hn n) (hnm n) r _ hs)
    (scalarCDFValue_lipschitz β ha hm r _ hs) (fun n => scalarCDFValue_lipschitz β (hn n) (hnm n) r _ hs)
    hg.1 (fun n => (hgn n).1)
    (B:=1) hg.2 (fun n => (hgn n).2)
    (scalarCDFValue_tendstoUniformly_interval β ha hm hn hnm hD r _ hs hr (by rw [hs0]; linarith)) HP
    0 _ ht le_rfl (by rw [ht0]; linarith)).tendsto_at 0

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFJointBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem timeChainJointHessian_eq_cdf (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α) {r q : ℝ}
    (hr : 0 ≤ r) (hrq : r≤q) (hq : q≤1)
    (l : TimeChainOn α 0 r) (j : TimeChainOn α r q) (k : TimeChainOn α q 1) :
    timeChainJointHessian β l.chain j.chain k.chain=scalarCDFJointSusceptibility β α r q := by
  let tr := Real.toNNReal r
  let tj := Real.toNNReal (q-r)
  let sr := Real.toNNReal (1-r)
  let sq := Real.toNNReal (1-q)
  have htr : (tr:ℝ)=r := Real.coe_toNNReal _ hr
  have htj : (tj:ℝ)=q-r := Real.coe_toNNReal _ (sub_nonneg.mpr hrq)
  have hsr : (sr:ℝ)=1-r := Real.coe_toNNReal _ (by linarith)
  have hsq : (sq:ℝ)=1-q := Real.coe_toNNReal _ (by linarith)
  have htr1 : tr≤1 := by rw [← NNReal.coe_le_coe,htr,NNReal.coe_one]; linarith
  have htj1 : tj≤1 := by rw [← NNReal.coe_le_coe,htj,NNReal.coe_one]; linarith
  have hsr1 : sr≤1 := by rw [← NNReal.coe_le_coe,hsr,NNReal.coe_one]; linarith
  have hsq1 : sq≤1 := by rw [← NNReal.coe_le_coe,hsq,NNReal.coe_one]; linarith
  have heF : scalarTimeChain β k.chain scalarSpinTerminal=scalarCDFValue β α q sq := by
    funext x
    exact (scalarCDFOperator_eq_chain scalarSpinTerminal_regular scalarSpinTerminal_lipschitz β ha hm
      k.chain k.mass q sq hsq1 (NNReal.coe_injective (k.duration.trans hsq.symm)) k.models x).symm
  have heH : scalarTimeChain β j.chain (scalarTimeChain β k.chain scalarSpinTerminal)=scalarCDFValue β α r sr := by
    rw [← scalarTimeChain_append]
    funext x
    exact (scalarCDFOperator_eq_chain scalarSpinTerminal_regular scalarSpinTerminal_lipschitz β ha hm
      (j.append k).chain (j.append k).mass r sr hsr1
      (NNReal.coe_injective ((j.append k).duration.trans hsr.symm)) (j.append k).models x).symm
  have heK : scalarTimeChainAverage β j.chain (scalarTimeChain β k.chain scalarSpinTerminal)
      (rootHessian 0 (scalarTimeChain β k.chain scalarSpinTerminal))=scalarCDFConditionalSusceptibility β α r q := by
    rw [heF,scalarCDFValue_rootHessian β ha hm q sq hsq1]
    funext x
    exact (scalarCDFAverage_eq_chainAverage_lipschitz
      (scalarCDFValue_regular β ha hm q sq hsq1) (scalarCDFValue_lipschitz β ha hm q sq hsq1)
      (scalarCDFHessian_lipschitz β ha hm q sq hsq1) (B:=1)
      (scalarCDFHessian_abs_le_one β ha hm q sq hsq1)
      β ha hm j.chain j.mass r tj htj1 (NNReal.coe_injective (j.duration.trans htj.symm)) j.models x).symm
  dsimp only [timeChainJointHessian]
  rw [heH,heK,scalarCDFValue_rootHessian β ha hm r sr hsr1]
  have hK := scalarCDFConditionalSusceptibility_regular β ha hm hr hrq hq
  have hp := unitBoundedProduct_lipschitz (scalarCDFHessian_lipschitz β ha hm r sr hsr1) hK.1
    (scalarCDFHessian_abs_le_one β ha hm r sr hsr1) hK.2
  have hb (x) : |scalarCDFHessian β α r sr x*scalarCDFConditionalSusceptibility β α r q x|≤(1:ℝ≥0) := by
    rw [abs_mul,NNReal.coe_one]
    exact (mul_le_mul (scalarCDFHessian_abs_le_one β ha hm r sr hsr1 x) (hK.2 x)
      (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  exact (scalarCDFAverage_eq_chainAverage_lipschitz
    (scalarCDFValue_regular β ha hm r sr hsr1) (scalarCDFValue_lipschitz β ha hm r sr hsr1) hp hb
    β ha hm l.chain l.mass 0 tr htr1
    (NNReal.coe_injective (by rw [l.duration,sub_zero,htr])) l.models 0).symm

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_NarrowTimeAnalytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem narrowJointMoment_eq (c w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ)) :
    narrowJointMoment c w t=scalarIncrementAverage (weightedUnderlying c)
      (scalarIncrementChain (weightedUnderlying w) (scalarIncrementChain t scalarSpinTerminal))
      (fun x => rootHessian 0 (scalarIncrementChain (weightedUnderlying w) (scalarIncrementChain t scalarSpinTerminal)) x*
        scalarIncrementAverage (weightedUnderlying w) (scalarIncrementChain t scalarSpinTerminal)
          (rootHessian 0 (scalarIncrementChain t scalarSpinTerminal)) x) 0 := by
  dsimp only [narrowJointMoment]
  simp_rw [weightedBranch_average]
  simp_rw [mul_comm]
  exact congrFun (weightedBranch_average c
    (scalarIncrementChain (weightedUnderlying w) (scalarIncrementChain t scalarSpinTerminal))
    (fun x => scalarIncrementAverage (weightedUnderlying w) (scalarIncrementChain t scalarSpinTerminal)
      (rootHessian 0 (scalarIncrementChain t scalarSpinTerminal)) x*
      rootHessian 0 (scalarIncrementChain (weightedUnderlying w) (scalarIncrementChain t scalarSpinTerminal)) x)) (0,0)

namespace NarrowTimeBlocks
variable {α : ℝ → ℝ} {r h q : ℝ} (B : NarrowTimeBlocks α r h q)

theorem full_mass (a : ℝ) : ∀ p∈weightedUnderlying (B.c a)++weightedUnderlying (B.w a)++B.t,p.1∈Icc (0:ℝ) 1 := by
  rw [← B.full_raw a]; exact B.full.raw_mass

theorem full_sorted (hm : Monotone α) (a : ℝ) :
    (weightedUnderlying (B.c a)++weightedUnderlying (B.w a)++B.t).Pairwise (fun p q => p.1≤q.1) := by
  rw [← B.full_raw a]; exact B.full.raw_sorted hm

theorem scalar_parisi (β : ℝ) (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α) (a : ℝ) :
    scalarIncrementChain (scaleIncrementChain β (weightedUnderlying (B.c a)++weightedUnderlying (B.w a)++B.t)) scalarSpinTerminal 0-
      β^2/4*rawPenalty (weightedUnderlying (B.c a)++weightedUnderlying (B.w a)++B.t) 0=scalarCDFParisi β α := by
  rw [← B.full_raw a,B.full.scalar_value β ha hm (by norm_num),B.full.penalty hm]
  simp only [sub_zero,Real.toNNReal_one,scalarCDFParisi,intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc]
  ring

theorem scalar_susceptibility (β : ℝ) (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    (hq : q∈Icc (0:ℝ) 1) (a : ℝ) :
    narrowSusceptibility (scaleIncrementChain β (B.c a)) (scaleIncrementChain β (B.w a)) (scaleIncrementChain β B.t)=
      scalarCDFSusceptibilityAverage β α q := by
  rw [narrowSusceptibility_eq,weightedUnderlying_append,weightedUnderlying_scale,weightedUnderlying_scale,
    ← scaleIncrementChain_append,← B.front_raw a]
  exact B.front.scalar_susceptibility β ha hm hq B.tail

theorem scalar_joint (β : ℝ) (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    (hr : 0 ≤ r) (hrq : r≤q) (hq : q≤1) (a : ℝ) :
    narrowJointMoment (scaleIncrementChain β (B.c a)) (scaleIncrementChain β (B.w a)) (scaleIncrementChain β B.t)=
      scalarCDFJointSusceptibility β α r q := by
  rw [narrowJointMoment_eq,weightedUnderlying_scale,weightedUnderlying_scale,← B.common_raw a,← B.middle_raw a]
  simp only [t,scalarIncrementChain_rawTimeChain,scalarIncrementAverage_rawTimeChain]
  exact timeChainJointHessian_eq_cdf β ha hm hr hrq hq B.common B.middle B.tail

theorem tail_area (hm : Monotone α) : rawArea B.t=∫ x in q..1,α x := B.tail.area hm

theorem right_area (hm : Monotone α) : rawArea B.j=∫ x in r..r+h,α x := B.right.area hm

end NarrowTimeBlocks

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_NarrowScheduleScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
namespace SK.Analytic

theorem narrowCommonSchedule_scale (β δ : ℝ) (c : List (ℝ × (ℝ × ℝ))) :
    scaleIncrementChain β (narrowCommonSchedule δ c)=narrowCommonSchedule δ (scaleIncrementChain β c) := by
  simp only [scaleIncrementChain,narrowCommonSchedule,List.map_map]
  apply List.map_congr_left
  intro p hp
  apply Prod.ext
  · rfl
  · ext i; fin_cases i <;> norm_num [Function.comp_def,smul_eq_mul] <;> ring

theorem narrowMiddleSchedule_scale (β δ : ℝ) (l : List NarrowMiddleIncrement) :
    scaleIncrementChain β (narrowMiddleSchedule δ l)=
      narrowMiddleSchedule δ (l.map (mapProductIncrement (fun x : ℝ × ℝ => β • x) (fun x : ℝ × ℝ => β • x))) := by
  simp only [scaleIncrementChain,narrowMiddleSchedule,List.map_map]
  apply List.map_congr_left
  intro p hp
  apply Prod.ext
  · simp only [Function.comp_def,productMass_map]
  · cases p <;> ext i <;> fin_cases i <;>
      norm_num [Function.comp_def,mapProductIncrement,narrowMiddleVector,smul_eq_mul] <;> ring

theorem narrowSchedule_scale (β δ : ℝ) (c v w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ)) :
    scaleIncrementChain β (narrowSchedule δ c v w t)=
      narrowSchedule δ (scaleIncrementChain β c) (scaleIncrementChain β v)
        (scaleIncrementChain β w) (scaleIncrementChain β t) := by
  simp only [narrowSchedule,scaleIncrementChain_append,narrowCommonSchedule_scale,narrowMiddleSchedule_scale,
    tripleTailSchedule_scale,mergedProductBranches_map]
  rfl

theorem narrowVariance_scale (β : ℝ) (c v w : List (ℝ × (ℝ × ℝ))) :
    narrowVariance (scaleIncrementChain β c) (scaleIncrementChain β v) (scaleIncrementChain β w)=β^2*narrowVariance c v w := by
  simp only [narrowVariance,weightedVariance_scale]
  ring

theorem narrowAbsCross_scale (β : ℝ) (c v w : List (ℝ × (ℝ × ℝ))) :
    narrowAbsCross (scaleIncrementChain β c) (scaleIncrementChain β v) (scaleIncrementChain β w)=β^2*narrowAbsCross c v w := by
  simp only [narrowAbsCross,weightedAbsCross_scale]
  ring

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_NarrowTimeQuadratic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

namespace NarrowTimeBlocks
variable {α : ℝ → ℝ} {r h q : ℝ} (C : NarrowTimeBlocks α r h q)

theorem scaled_v_mean (β : ℝ) (hα : Monotone α) (θ : ℝ) :
    weightedMean (scaleIncrementChain β (C.v θ))=narrowCDFMean β α r h θ := by
  rw [weightedMean_scale,C.v_mean,C.right_area hα]
  unfold narrowCDFMean; ring

theorem quadratic_le (β : ℝ) (hα : ∀ z,α z∈Icc (0:ℝ) 1) (hmα : Monotone α)
    (hr : 0 ≤ r) (hrq : r≤q) (hq : q≤1) (hh : 0<h) {a θ : ℝ} (ha : 0<a) (hθ : 0≤θ) :
    narrowBaseQuadratic (scaleIncrementChain β (C.c a)) (scaleIncrementChain β (C.v θ))
      (scaleIncrementChain β (C.w a)) (scaleIncrementChain β C.t)≤
      β^2*((2*a^2+θ^2)/h)*scalarCDFSusceptibilityAverage β α q+
      2*narrowCDFMean β α r h θ*(β^2*a)*scalarCDFJointSusceptibility β α r q+
      narrowTentError (narrowCDFMean β α r h θ) (β^2*a) (β^2*θ) (α (r+h)-α (r-h)) := by
  let b := scaleIncrementChain β C.b
  let l := scaleIncrementChain β C.l
  let j := scaleIncrementChain β C.j
  let k := scaleIncrementChain β C.k
  let t := scaleIncrementChain β C.t
  let κ := a/h
  let η := θ/h
  have hc : scaleIncrementChain β (C.c a)=fourBlockCommon κ b l := by
    simp only [c,scaleIncrementChain_append,zeroWeightChain_scale,constantWeightChain_scale]; rfl
  have hv : scaleIncrementChain β (C.v θ)=fourBlockFuture η j k := by
    simp only [v,scaleIncrementChain_append,zeroWeightChain_scale,constantWeightChain_scale]; rfl
  have hw : scaleIncrementChain β (C.w a)=fourBlockFuture (-κ) j k := by
    simp only [w,scaleIncrementChain_append,zeroWeightChain_scale,constantWeightChain_scale,neg_div]; rfl
  have heFull : (b++l)++(j++k)++t=scaleIncrementChain β
      (weightedUnderlying (C.c a)++weightedUnderlying (C.w a)++C.t) := by
    simp only [C.c_underlying,C.w_underlying,scaleIncrementChain_append]; rfl
  have hm : ∀ p∈(b++l)++(j++k)++t,p.1∈Icc (0:ℝ) 1 := by
    rw [heFull]; exact scaleIncrementChain_mass β _ (C.full_mass a)
  have hs : ((b++l)++(j++k)++t).Pairwise (fun p q => p.1≤q.1) := by
    rw [heFull]; exact scaleIncrementChain_sorted β _ (C.full_sorted hmα a)
  have hmF := fourBlockTent_mass κ b l j k (fun p hp => hm p (List.mem_append_left _ hp))
  have hsF := fourBlockTent_sorted κ b l j k (List.pairwise_append.mp hs).1
  have M := C.v_mean_bounds hmα hh hθ
  have hM : 0≤weightedMean (scaleIncrementChain β (C.v θ)) := by
    rw [weightedMean_scale]
    exact mul_nonneg (sq_nonneg β) ((mul_nonneg hθ (hα r).1).trans M.1)
  have hmean : 0≤weightedMean (fourBlockFuture η j k) := hv ▸ hM
  have hB : 0≤β^2*a := mul_nonneg (sq_nonneg β) ha.le
  have hn := ne_of_gt hh
  have an := ne_of_gt ha
  have hld : rawVariance l=(β^2*a)*(h/a) := by
    dsimp only [l]; rw [rawVariance_scale,C.l_variance]
    field_simp
  have hjd : rawVariance j=(β^2*a)*(h/a) := by
    dsimp only [j]; rw [rawVariance_scale,C.j_variance]
    field_simp
  have HK : κ*(h/a)=1 := by dsimp only [κ]; field_simp
  have H := fourBlockQuadratic_tent_le κ η b l j k t hm hs hmean (div_pos hh ha) hB HK hld hjd
  let A := scalarTentAtomMass (fourBlockTent κ b l j k).length (fun i => ((fourBlockTent κ b l j k).get i).1)
      (fourBlockLeft κ b l j k) (fourBlockRight κ b l j k)
  have hA : 0≤A := scalarTentAtomMass_nonneg _ _ (fun i => hmF _ (List.get_mem _ i))
    (mass_get_monotone hsF) _ _
  have hlL : 0<l.length := by
    dsimp only [l]; simp only [scaleIncrementChain,List.length_map]
    exact rawVariance_pos_length (show 0 < rawVariance C.l by rw [C.l_variance]; exact hh)
  have hjL : 0<j.length := by
    dsimp only [j]; simp only [scaleIncrementChain,List.length_map]
    exact rawVariance_pos_length (show 0 < rawVariance C.j by rw [C.j_variance]; exact hh)
  have hAω : A≤α (r+h)-α (r-h) := fourBlockTent_atom_le κ b l j k hlL hjL
    (scaleIncrementChain_mass (P:=fun x => α (r-h)≤x) β _ (fun p hp => (C.left.raw_mass_interval hmα p hp).1))
    (scaleIncrementChain_mass (P:=fun x => x≤α (r+h)) β _ (fun p hp => (C.right.raw_mass_interval hmα p hp).2))
  have Herr := narrowTentError_mono (R:=weightedAbsCross (fourBlockFuture η j k)) hmean hB hA hAω
  have H0 : narrowBaseQuadratic (fourBlockCommon κ b l) (fourBlockFuture η j k) (fourBlockFuture (-κ) j k) t≤narrowVariance (fourBlockCommon κ b l) (fourBlockFuture η j k) (fourBlockFuture (-κ) j k)*
      narrowSusceptibility (fourBlockCommon κ b l) (fourBlockFuture (-κ) j k) t+
      2*weightedMean (fourBlockFuture η j k)*(β^2*a)*narrowJointMoment (fourBlockCommon κ b l) (fourBlockFuture (-κ) j k) t+
      narrowTentError (weightedMean (fourBlockFuture η j k)) (β^2*a) (weightedAbsCross (fourBlockFuture η j k)) A := by
    simpa only [narrowTentError,A,add_assoc] using H
  have H' := H0.trans (add_le_add le_rfl Herr)
  rw [← hc,← hv,← hw] at H'
  rw [narrowVariance_scale,C.variance_stats hn,C.scalar_susceptibility β hα hmα ⟨hr.trans hrq,hq⟩ a,
    C.scalar_joint β hα hmα hr hrq hq a,C.scaled_v_mean β hmα θ,weightedAbsCross_scale,C.v_absCross hh hθ] at H'
  exact H'

end NarrowTimeBlocks

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_NarrowCDFTrial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

namespace NarrowTimeBlocks
variable {α : ℝ → ℝ} {r h q : ℝ} (C : NarrowTimeBlocks α r h q)

include C in
theorem pressure_trial {N : ℕ} (hN : 0<N) (β δ : ℝ)
    (hα : ∀ z,α z∈Icc (0:ℝ) 1) (hmα : Monotone α)
    (hr : 0 ≤ r) (hrq : r≤q) (hq : q≤1) (hh : 0<h)
    {a θ : ℝ} (ha : 0<a) (hθ : 0≤θ) (haθ : a+θ=1)
    (hD : Nonempty (MatrixStates N 3 (tripleGram r δ q)))
    {ε : ℝ} (hε : 0<ε) (hδ : 4*δ^2≤ε) (hδ1 : |δ|≤1)
    (hsmall : ε*(4*β^2*((2*a^2+θ^2)/h)+(2*β^2*(5*a+θ))^2)≤1/2) :
    matrixConstrainedPressure N 3 β (tripleGram r δ q)≤
      3*scalarCDFParisi β α+δ^2*narrowCDFTrialCoefficient β α r h q a θ+
      tripleExpansionConstant ε*|δ|^3+β^2*δ^4*((2*a^2+θ^2)/h)^2 := by
  have hn : h≠0 := ne_of_gt hh
  have hv : weightedUnderlying (C.v θ)=weightedUnderlying (C.w a) := by simp
  have Cs := C.cross_stats hn a θ
  have hy : weightedCross (C.c a)+weightedCross (C.w a)=0 := by rw [Cs.1,Cs.2.2]; ring
  have hg : weightedCross (C.c a)+weightedCross (C.v θ)=1 := by rw [Cs.1,Cs.2.1]; exact haθ
  have HP := narrowConstrainedPressure_schedule hN β δ (C.c a) (C.v θ) (C.w a) C.t hv hy
    (C.full_mass a) (C.full_sorted hmα a) (C.full_variance a) hg
    (by simpa only [C.common_variance,C.front_variance] using hD)
  rw [C.common_variance,C.front_variance] at HP
  change _≤vectorIncrementChain (scaleIncrementChain β (narrowSchedule δ (C.c a) (C.v θ) (C.w a) C.t)) _ _-_ -_+_ at HP
  rw [narrowSchedule_scale] at HP
  have he : weightedUnderlying (scaleIncrementChain β (C.c a))++weightedUnderlying (scaleIncrementChain β (C.w a))++scaleIncrementChain β C.t=
      scaleIncrementChain β (weightedUnderlying (C.c a)++weightedUnderlying (C.w a)++C.t) := by
    simp only [weightedUnderlying_scale,scaleIncrementChain_append]
  have hv' : weightedUnderlying (scaleIncrementChain β (C.v θ))=weightedUnderlying (scaleIncrementChain β (C.w a)) := by
    simp only [weightedUnderlying_scale,hv]
  have hs' : ε*(4*narrowVariance (scaleIncrementChain β (C.c a)) (scaleIncrementChain β (C.v θ)) (scaleIncrementChain β (C.w a))+
      (2*narrowAbsCross (scaleIncrementChain β (C.c a)) (scaleIncrementChain β (C.v θ)) (scaleIncrementChain β (C.w a)))^2)≤1/2 := by
    simpa only [narrowVariance_scale,C.variance_stats hn,narrowAbsCross_scale,C.absCross_stats hh ha.le hθ,mul_assoc] using hsmall
  have HE := narrowSchedule_value_expansion (scaleIncrementChain β (C.c a)) (scaleIncrementChain β (C.v θ))
    (scaleIncrementChain β (C.w a)) (scaleIncrementChain β C.t) hv'
    (by rw [he]; exact scaleIncrementChain_mass β _ (C.full_mass a))
    (by rw [he]; exact scaleIncrementChain_sorted β _ (C.full_sorted hmα a)) hε hδ hδ1 hs'
  rw [he] at HE
  have HQ := mul_le_mul_of_nonneg_left (C.quadratic_le β hα hmα hr hrq hq hh ha hθ) (sq_nonneg δ)
  have HC := mul_le_mul_of_nonneg_left (C.crossPenalty_lower hmα hh ha.le hθ) (show 0≤β^2*δ^2 by positivity)
  rw [C.variance_stats hn,C.tail_area hmα] at HP
  have HPar := C.scalar_parisi β hα hmα a
  unfold narrowCDFTrialCoefficient
  nlinarith only [HP,HE,HQ,HC,HPar]

end NarrowTimeBlocks

theorem narrowConstrainedPressure_quantile_trial {N k : ℕ} (hN : 0<N) (β δ : ℝ)
    (Q : Fin (k+1) → ℝ) (hQ : Q∈admissibleQuantiles k)
    {r h q a θ : ℝ} (hh : 0<h) (hhr : h ≤ r) (hhq : r+h≤q) (hq : q≤1)
    (ha : 0<a) (hθ : 0≤θ) (haθ : a+θ=1)
    (hD : Nonempty (MatrixStates N 3 (tripleGram r δ q)))
    {ε : ℝ} (hε : 0<ε) (hδ : 4*δ^2≤ε) (hδ1 : |δ|≤1)
    (hsmall : ε*(4*β^2*((2*a^2+θ^2)/h)+(2*β^2*(5*a+θ))^2)≤1/2) :
    matrixConstrainedPressure N 3 β (tripleGram r δ q)≤
      3*scalarCDFParisi β (quantileCDF k Q)+δ^2*narrowCDFTrialCoefficient β (quantileCDF k Q) r h q a θ+
      tripleExpansionConstant ε*|δ|^3+β^2*δ^4*((2*a^2+θ^2)/h)^2 := by
  obtain ⟨b⟩ := exists_quantile_TimeChainOn β Q hQ (s:=0) (t:=r-h) le_rfl (by linarith) (by linarith)
  obtain ⟨l⟩ := exists_quantile_TimeChainOn β Q hQ (s:=r-h) (t:=r) (by linarith) (by linarith) (by linarith)
  obtain ⟨j⟩ := exists_quantile_TimeChainOn β Q hQ (s:=r) (t:=r+h) (by linarith) (by linarith) (by linarith)
  obtain ⟨k'⟩ := exists_quantile_TimeChainOn β Q hQ (s:=r+h) (t:=q) (by linarith) hhq hq
  obtain ⟨t⟩ := exists_quantile_TimeChainOn β Q hQ (s:=q) (t:=1) (by linarith) hq le_rfl
  let C : NarrowTimeBlocks (quantileCDF k Q) r h q := ⟨b,l,j,k',t⟩
  exact C.pressure_trial hN β δ (quantileCDF_bounds k Q) (quantileCDF_monotone k Q)
    (by linarith) (by linarith) hq hh ha hθ haθ hD hε hδ hδ1 hsmall

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_NarrowCoefficientBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem narrowCDFErrorConstant_nonneg (β : ℝ) : 0≤narrowCDFErrorConstant β := by
  dsimp only [narrowCDFErrorConstant]; positivity

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFParisiContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem cdfPenalty_integrable {α : ℝ → ℝ} (hαm : Monotone α) :
    IntegrableOn (fun s => s*α s) (Icc (0:ℝ) 1) :=
  IntegrableOn.continuousOn_mul continuousOn_id (MonotoneOn.integrableOn_isCompact isCompact_Icc (hαm.monotoneOn _)) isCompact_Icc

theorem cdfPenalty_lipschitz {α γ : ℝ → ℝ} (hαm : Monotone α) (hγm : Monotone γ) :
    |(∫ s in Icc (0:ℝ) 1, s*α s)-(∫ s in Icc (0:ℝ) 1, s*γ s)| ≤
      ∫ s in Icc (0:ℝ) 1, |α s-γ s| := by
  rw [← integral_sub (cdfPenalty_integrable hαm) (cdfPenalty_integrable hγm)]
  calc
    _ ≤ ∫ s in Icc (0:ℝ) 1, |s*α s-s*γ s| := abs_integral_le_integral_abs
    _ ≤ _ := setIntegral_mono_on ((cdfPenalty_integrable hαm).sub (cdfPenalty_integrable hγm)).abs
      ((MonotoneOn.integrableOn_isCompact isCompact_Icc (hαm.monotoneOn _)).sub (MonotoneOn.integrableOn_isCompact isCompact_Icc (hγm.monotoneOn _))).abs measurableSet_Icc (by
        intro s hs
        rw [← mul_sub,abs_mul,abs_of_nonneg hs.1]
        exact mul_le_of_le_one_left (abs_nonneg _) hs.2)

theorem scalarCDFParisi_cdf_lipschitz (β : ℝ) {α γ : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hαm : Monotone α)
    (hγ : ∀ z, γ z ∈ Icc (0:ℝ) 1) (hγm : Monotone γ) :
    |scalarCDFParisi β α-scalarCDFParisi β γ| ≤
      (scalarTimeMassConstant β+β^2/2)*(∫ s in Icc (0:ℝ) 1, |α s-γ s|) := by
  have H := scalarCDFValue_cdf_lipschitz β hα hαm hγ hγm 0 1 le_rfl 0
  simp only [NNReal.coe_one,zero_add,intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc] at H
  unfold scalarCDFParisi
  calc
    _ = |(scalarCDFValue β α 0 1 0-scalarCDFValue β γ 0 1 0)-
        (β^2/2)*((∫ s in Icc (0:ℝ) 1, s*α s)-(∫ s in Icc (0:ℝ) 1, s*γ s))| := by congr 1; ring
    _ ≤ |scalarCDFValue β α 0 1 0-scalarCDFValue β γ 0 1 0|+
        (β^2/2)*|(∫ s in Icc (0:ℝ) 1, s*α s)-(∫ s in Icc (0:ℝ) 1, s*γ s)| := by
      calc
        _ ≤ |scalarCDFValue β α 0 1 0-scalarCDFValue β γ 0 1 0|+
            |(β^2/2)*((∫ s in Icc (0:ℝ) 1, s*α s)-(∫ s in Icc (0:ℝ) 1, s*γ s))| := by
          simpa only [sub_zero,zero_sub,abs_neg] using (abs_sub_le
            (scalarCDFValue β α 0 1 0-scalarCDFValue β γ 0 1 0) 0
            ((β^2/2)*((∫ s in Icc (0:ℝ) 1, s*α s)-(∫ s in Icc (0:ℝ) 1, s*γ s))))
        _ = _ := by rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ β^2/2)]
    _ ≤ scalarTimeMassConstant β*(∫ s in Icc (0:ℝ) 1, |α s-γ s|)+
        (β^2/2)*(∫ s in Icc (0:ℝ) 1, |α s-γ s|) :=
      add_le_add H (mul_le_mul_of_nonneg_left (cdfPenalty_lipschitz hαm hγm) (by positivity))
    _ = _ := by ring

theorem scalarCDFParisi_tendsto_of_L1 (β : ℝ) {α : ℝ → ℝ} {αs : ℕ → ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hαm : Monotone α)
    (hs : ∀ n z, αs n z ∈ Icc (0:ℝ) 1) (hsm : ∀ n, Monotone (αs n))
    (ht : Tendsto (fun n => ∫ z in Icc (0:ℝ) 1, |αs n z-α z|) atTop (𝓝 0)) :
    Tendsto (fun n => scalarCDFParisi β (αs n)) atTop (𝓝 (scalarCDFParisi β α)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have H := squeeze_zero (fun _ => abs_nonneg _)
    (fun n => scalarCDFParisi_cdf_lipschitz β (hs n) (hsm n) hα hαm)
    (by simpa only [mul_zero] using ht.const_mul (scalarTimeMassConstant β+β^2/2))
  simpa only [mul_zero,Real.norm_eq_abs] using H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_SusceptibilityConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFSusceptibilityAverage_tendsto (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (hn : ∀ n z, αn n z∈Icc (0:ℝ) 1) (hnm : ∀ n, Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    {r : ℝ} (hr : r∈Icc (0:ℝ) 1) :
    Tendsto (fun n => scalarCDFSusceptibilityAverage β (αn n) r) atTop
      (𝓝 (scalarCDFSusceptibilityAverage β α r)) := by
  let t := Real.toNNReal r
  let s := Real.toNNReal (1-r)
  have ht : (t:ℝ)=r := Real.coe_toNNReal r hr.1
  have hs : (s:ℝ)=1-r := Real.coe_toNNReal (1-r) (sub_nonneg.mpr hr.2)
  have ht1 : t≤1 := by rw [← NNReal.coe_le_coe,ht,NNReal.coe_one]; exact hr.2
  have hs1 : s≤1 := by rw [← NNReal.coe_le_coe,hs,NNReal.coe_one]; linarith [hr.1]
  have hrs : r+s≤1 := by rw [hs]; linarith
  let f := scalarCDFValue β α r s
  let g := scalarCDFHessian β α r s
  let fn := fun n => scalarCDFValue β (αn n) r s
  let gn := fun n => scalarCDFHessian β (αn n) r s
  have hfU : TendstoUniformly fn f atTop :=
    scalarCDFValue_tendstoUniformly_interval β hα hαm hn hnm hD r s hs1 hr.1 hrs
  have hgU : TendstoUniformly gn g atTop :=
    scalarCDFHessian_tendstoUniformly_interval β hα hαm hn hnm hD r s hs1 hr.1 hrs
  have hc := scalarCDFAverage_tendsto_cdf_lipschitz β hα hαm hn hnm hD
    (scalarCDFValue_regular β hα hαm r s hs1)
    (scalarCDFValue_lipschitz β hα hαm r s hs1)
    (scalarCDFHessian_lipschitz β hα hαm r s hs1)
    (B:=1) (scalarCDFHessian_abs_le_one β hα hαm r s hs1)
    0 t ht1 le_rfl (by simpa only [zero_add,ht] using hr.2) 0
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := Real.log (1+ε/8)/2
  have hd : 0<δ := div_pos (Real.log_pos (by linarith)) (by norm_num)
  have he : Real.exp (2*δ)-1=ε/8 := by
    rw [show 2*δ=Real.log (1+ε/8) by dsimp [δ]; ring,
      Real.exp_log (by linarith : 0<1+ε/8)]
    ring
  filter_upwards [(Metric.tendstoUniformly_iff.mp hfU) δ hd,
    (Metric.tendstoUniformly_iff.mp hgU) (ε/4) (by positivity),
    (Metric.tendsto_nhds.mp hc) (ε/4) (by positivity)] with n hf hg hcn
  have hfg (z) : |fn n z-f z|≤δ := by simpa only [Real.dist_eq,abs_sub_comm] using (hf z).le
  have hgg (z) : |gn n z-g z|≤ε/4 := by simpa only [Real.dist_eq,abs_sub_comm] using (hg z).le
  have Ht := scalarCDFAverage_terminal_stability_lipschitz β (hn n) (hnm n)
    (scalarCDFValue_regular β (hn n) (hnm n) r s hs1)
    (scalarCDFValue_regular β hα hαm r s hs1)
    (scalarCDFValue_lipschitz β (hn n) (hnm n) r s hs1)
    (scalarCDFValue_lipschitz β hα hαm r s hs1)
    (scalarCDFHessian_lipschitz β (hn n) (hnm n) r s hs1)
    (scalarCDFHessian_lipschitz β hα hαm r s hs1)
    (B:=1) (scalarCDFHessian_abs_le_one β (hn n) (hnm n) r s hs1)
    (scalarCDFHessian_abs_le_one β hα hαm r s hs1)
    hd.le hfg hgg 0 t ht1 0
  rw [he,NNReal.coe_one] at Ht
  change |scalarCDFAverage β (αn n) 0 t (fn n) (gn n) 0-
    scalarCDFAverage β (αn n) 0 t f g 0|≤_ at Ht
  change dist (scalarCDFAverage β (αn n) 0 t f g 0) (scalarCDFAverage β α 0 t f g 0)<ε/4 at hcn
  rw [Real.dist_eq] at hcn
  rw [Real.dist_eq]
  change |scalarCDFAverage β (αn n) 0 t (fn n) (gn n) 0-
    scalarCDFAverage β α 0 t f g 0|<ε
  have H := abs_sub_le (scalarCDFAverage β (αn n) 0 t (fn n) (gn n) 0)
    (scalarCDFAverage β (αn n) 0 t f g 0) (scalarCDFAverage β α 0 t f g 0)
  linarith

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleContinuumTrial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem cdfArea_distance_le {α γ : ℝ → ℝ} (hα : Monotone α) (hγ : Monotone γ)
    {q : ℝ} (hq : q ∈ Icc (0:ℝ) 1) :
    |(∫ z in q..1, α z)-(∫ z in q..1,γ z)| ≤ cdfDistance α γ := by
  rw [← intervalIntegral.integral_sub hα.intervalIntegrable hγ.intervalIntegrable]
  have H := cdfDistance_subinterval_le hα hγ (t:=Real.toNNReal (1-q)) hq.1
    (by rw [Real.coe_toNNReal _ (sub_nonneg.mpr hq.2)]; linarith)
  rw [Real.coe_toNNReal _ (sub_nonneg.mpr hq.2),add_sub_cancel] at H
  exact (intervalIntegral.abs_integral_le_integral_abs hq.2).trans H

theorem cdfArea_tendsto {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (hα : Monotone α) (hn : ∀ n,Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    {q : ℝ} (hq : q ∈ Icc (0:ℝ) 1) :
    Tendsto (fun n => ∫ z in q..1,αn n z) atTop (𝓝 (∫ z in q..1,α z)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using squeeze_zero (fun _ => abs_nonneg _)
    (fun n => cdfArea_distance_le (hn n) hα hq) hD

theorem uniformCDFQuantiles_pointwise_tendsto (α : StieltjesFunction ℝ)
    (hα : ∀ z,α z ∈ Icc (0:ℝ) 1) (hα1 : α 1=1) {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) :
    Tendsto (fun n => quantileCDF n (uniformCDFQuantiles n α) s) atTop (𝓝 (α s)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have H := squeeze_zero (fun _ => abs_nonneg _)
    (fun n => quantileCDF_uniformCDFQuantiles_error n α hα hα1 hs)
    (show Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)⁻¹) atTop (𝓝 0) by
      simpa only [Nat.cast_add,Nat.cast_one,one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)))
  simpa only [Real.norm_eq_abs] using H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_NarrowContinuumTrial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem intervalCDFArea_eq_sub_tail {α : ℝ → ℝ} (hα : Monotone α) (r s : ℝ) :
    (∫ z in r..s,α z)=(∫ z in r..1,α z)-(∫ z in s..1,α z) := by
  have H := intervalIntegral.integral_add_adjacent_intervals (a:=r) (b:=s) (c:=1) (μ:=volume)
    hα.intervalIntegrable hα.intervalIntegrable
  linarith

theorem narrowCDFMean_tendsto (β r h θ : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (hα : Monotone α) (hn : ∀ n,Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    (hr : r∈Icc (0:ℝ) 1) (hs : r+h∈Icc (0:ℝ) 1) :
    Tendsto (fun n => narrowCDFMean β (αn n) r h θ) atTop (𝓝 (narrowCDFMean β α r h θ)) := by
  simp only [narrowCDFMean,intervalCDFArea_eq_sub_tail hα r (r+h),intervalCDFArea_eq_sub_tail (hn _) r (r+h)]
  exact ((cdfArea_tendsto hα hn hD hr).sub (cdfArea_tendsto hα hn hD hs)).const_mul _

theorem narrowCDFTrialCoefficient_uniform_tendsto (β : ℝ) (α : StieltjesFunction ℝ)
    (hα : ∀ z,α z∈Icc (0:ℝ) 1) (hα1 : α 1=1)
    {r h q : ℝ} (hh : 0<h) (hhr : h ≤ r) (hhq : r+h≤q) (hq : q≤1) (a θ : ℝ) :
    Tendsto (fun n => narrowCDFTrialCoefficient β (quantileCDF n (uniformCDFQuantiles n α)) r h q a θ) atTop
      (𝓝 (narrowCDFTrialCoefficient β α r h q a θ)) := by
  let αn := fun n => quantileCDF n (uniformCDFQuantiles n α)
  have hn (n z) : αn n z∈Icc (0:ℝ) 1 := quantileCDF_bounds n _ z
  have hnm (n) : Monotone (αn n) := quantileCDF_monotone n _
  have hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0) := uniformCDFQuantiles_L1_tendsto α hα hα1
  have hχ := scalarCDFSusceptibilityAverage_tendsto β hα α.mono hn hnm hD (r:=q) ⟨by linarith,hq⟩
  have hA := cdfArea_tendsto α.mono hnm hD (q:=q) ⟨by linarith,hq⟩
  have hJ := scalarCDFJointSusceptibility_tendsto β hα α.mono hn hnm hD
    (r:=r) (q:=q) (by linarith) (by linarith) hq
  have hM := narrowCDFMean_tendsto β r h θ α.mono hnm hD ⟨by linarith,by linarith⟩ ⟨by linarith,by linarith⟩
  have hrA := uniformCDFQuantiles_pointwise_tendsto α hα hα1 (s:=r) ⟨by linarith,by linarith⟩
  have hω := (uniformCDFQuantiles_pointwise_tendsto α hα hα1 (s:=r+h) ⟨by linarith,by linarith⟩).sub
    (uniformCDFQuantiles_pointwise_tendsto α hα hα1 (s:=r-h) ⟨by linarith,by linarith⟩)
  have hE : Tendsto (fun n => narrowTentError (narrowCDFMean β (αn n) r h θ) (β^2*a) (β^2*θ) (αn n (r+h)-αn n (r-h))) atTop
      (𝓝 (narrowTentError (narrowCDFMean β α r h θ) (β^2*a) (β^2*θ) (α (r+h)-α (r-h)))) := by
    exact (((tendsto_const_nhds.add (((hM.const_mul 2).mul_const (β^2*a)).mul hω)).add
      ((hω.const_mul (β^2*a)).pow 2)).add (hω.const_mul ((β^2*a)^2)))
  exact ((((hχ.sub hA).const_mul (β^2*((2*a^2+θ^2)/h))).add
    (((hM.const_mul 2).mul_const (β^2*a)).mul hJ)).add hE).sub
      (((hrA.mul_const (2*a*θ+θ^2)).sub (hω.const_mul (a^2))).const_mul (β^2))

theorem narrowConstrainedPressure_continuum_trial {N : ℕ} (hN : 0<N) (β δ : ℝ)
    (α : StieltjesFunction ℝ) (hα : ∀ z,α z∈Icc (0:ℝ) 1) (hα1 : α 1=1)
    {r h q a θ : ℝ} (hh : 0<h) (hhr : h ≤ r) (hhq : r+h≤q) (hq : q≤1)
    (ha : 0<a) (hθ : 0≤θ) (haθ : a+θ=1)
    (hD : Nonempty (MatrixStates N 3 (tripleGram r δ q)))
    {ε : ℝ} (hε : 0<ε) (hδ : 4*δ^2≤ε) (hδ1 : |δ|≤1)
    (hsmall : ε*(4*β^2*((2*a^2+θ^2)/h)+(2*β^2*(5*a+θ))^2)≤1/2) :
    matrixConstrainedPressure N 3 β (tripleGram r δ q)≤
      3*scalarCDFParisi β α+δ^2*narrowCDFTrialCoefficient β α r h q a θ+
      tripleExpansionConstant ε*|δ|^3+β^2*δ^4*((2*a^2+θ^2)/h)^2 := by
  have hC := narrowCDFTrialCoefficient_uniform_tendsto β α hα hα1 hh hhr hhq hq a θ
  have hP := scalarCDFParisi_tendsto_of_L1 β hα α.mono
    (fun n => quantileCDF_bounds n (uniformCDFQuantiles n α))
    (fun n => quantileCDF_monotone n (uniformCDFQuantiles n α)) (uniformCDFQuantiles_L1_tendsto α hα hα1)
  apply ge_of_tendsto ((((hP.const_mul 3).add (hC.const_mul (δ^2))).add_const
    (tripleExpansionConstant ε*|δ|^3)).add_const (β^2*δ^4*((2*a^2+θ^2)/h)^2))
  exact Eventually.of_forall (fun n => narrowConstrainedPressure_quantile_trial hN β δ
    (uniformCDFQuantiles n α) (uniformCDFQuantiles_admissible n α hα1) hh hhr hhq hq ha hθ haθ hD hε hδ hδ1 hsmall)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_NarrowScaleAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem narrowExpansionDenominator_ge_one (β : ℝ) : 1≤ narrowExpansionDenominator β := by
  unfold narrowExpansionDenominator; nlinarith [sq_nonneg β,sq_nonneg (β^2)]

theorem narrowExpansionErrorConstant_pos (β : ℝ) : 0< narrowExpansionErrorConstant β := by
  have hd : 0< narrowExpansionDenominator β := lt_of_lt_of_le zero_lt_one (narrowExpansionDenominator_ge_one β)
  unfold narrowExpansionErrorConstant
  positivity

theorem narrowExpansion_smallness (β : ℝ) {h a θ : ℝ} (hh : 0< h) (hh1 : h≤1)
    (ha : 0≤ a) (hθ : 0≤θ) (haθ : a+θ=1) :
    (h/narrowExpansionDenominator β)*(4*β^2*((2*a^2+θ^2)/h)+(2*β^2*(5*a+θ))^2)≤1/2 := by
  have ha1 : a≤1 := by linarith
  have hθ1 : θ≤1 := by linarith
  have hK : 2*a^2+θ^2≤3 := by nlinarith [sq_nonneg (1-a),sq_nonneg (1-θ)]
  have hscore : (5*a+θ)^2≤36 := by nlinarith [sq_nonneg (6-(5*a+θ))]
  have hd : 0< narrowExpansionDenominator β := lt_of_lt_of_le zero_lt_one (narrowExpansionDenominator_ge_one β)
  have HP : 4*β^2*(2*a^2+θ^2)+h*(2*β^2*(5*a+θ))^2≤12*β^2+144*β^4 := by
    have HK := mul_le_mul_of_nonneg_left hK (show 0≤4*β^2 by positivity)
    have HS := mul_le_mul_of_nonneg_left hscore (show 0≤4*β^4 by positivity)
    have HH := mul_le_mul_of_nonneg_left hh1 (show 0≤(2*β^2*(5*a+θ))^2 by positivity)
    nlinarith only [HK,HS,HH]
  have HE : (h/narrowExpansionDenominator β)*(4*β^2*((2*a^2+θ^2)/h)+(2*β^2*(5*a+θ))^2)=
      (4*β^2*(2*a^2+θ^2)+h*(2*β^2*(5*a+θ))^2)/narrowExpansionDenominator β := by field_simp
  rw [HE,div_le_iff₀ hd]
  dsimp only [narrowExpansionDenominator]
  linarith

theorem tripleExpansionConstant_scaled_bound (β : ℝ) {h : ℝ} (hh : 0< h) (hh1 : h≤1) :
    tripleExpansionConstant (h/narrowExpansionDenominator β)≤ narrowExpansionErrorConstant β/h^2 := by
  have hd1 := narrowExpansionDenominator_ge_one β
  have hd : 0< narrowExpansionDenominator β := lt_of_lt_of_le zero_lt_one hd1
  have hL : 0≤(susceptibilityLipschitzConstant:ℝ) := NNReal.coe_nonneg _
  have hsq : h^2≤(narrowExpansionDenominator β)^2 := by nlinarith
  have HE : tripleExpansionConstant (h/narrowExpansionDenominator β)*h^2=
      4*(susceptibilityLipschitzConstant:ℝ)*h^2+(8*(susceptibilityLipschitzConstant:ℝ)+64)*(narrowExpansionDenominator β)^2 := by
    unfold tripleExpansionConstant
    field_simp
    ring
  rw [le_div_iff₀ (sq_pos_of_pos hh),HE]
  unfold narrowExpansionErrorConstant
  nlinarith [mul_le_mul_of_nonneg_left hsq (show 0≤4*(susceptibilityLipschitzConstant:ℝ) by positivity)]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFJointLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarJointLossConstant_pos {β a : ℝ} (hβ : β≠0) (ha : 0<a) :
    0 < scalarJointLossConstant β a := by
  unfold scalarJointLossConstant
  have hb4 : 0<β^4 := by
    have H := sq_pos_of_ne_zero hβ
    nlinarith [sq_pos_of_pos H]
  have hf := scalarSusceptibilityFloor_pos (β^2) (1+2*β^2+4*(β^2)^2)
  positivity

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_NarrowScaledRemainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem narrow_scaled_remainder (β : ℝ) {ρ δ : ℝ} (hρ : 0<ρ) (hρ1 : ρ≤1)
    (hδ : |δ|≤2*ρ^20) :
    tripleExpansionConstant (ρ^8/narrowExpansionDenominator β)*|δ|+
      β^2*δ^2*((2*(1-ρ^2)^2+(ρ^2)^2)/ρ^8)^2≤
      (2*narrowExpansionErrorConstant β+36*β^2)*ρ^4 := by
  have hh : 0<ρ^8 := pow_pos hρ _
  have hh1 : ρ^8≤1 := pow_le_one₀ hρ.le hρ1
  have hθ1 : ρ^2≤1 := pow_le_one₀ hρ.le hρ1
  have ha0 : 0≤1-ρ^2 := sub_nonneg.mpr hθ1
  have ha1 : 1-ρ^2≤1 := by nlinarith [sq_nonneg ρ]
  have hK0 : 0≤(2*(1-ρ^2)^2+(ρ^2)^2)/ρ^8 := by positivity
  have hK : (2*(1-ρ^2)^2+(ρ^2)^2)/ρ^8≤3/ρ^8 := by
    apply div_le_div_of_nonneg_right _ hh.le
    nlinarith [sq_nonneg (1-(1-ρ^2)),sq_nonneg (1-ρ^2)]
  have hK2 : ((2*(1-ρ^2)^2+(ρ^2)^2)/ρ^8)^2≤(3/ρ^8)^2 := by
    exact (sq_le_sq₀ hK0 (by positivity)).mpr hK
  have hδ2 : δ^2≤4*ρ^40 := by
    calc
      _ = |δ|^2 := (sq_abs _).symm
      _ ≤ (2*ρ^20)^2 := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hδ
      _ = _ := by ring
  have hE := tripleExpansionConstant_scaled_bound β hh hh1
  have hE0 : 0≤narrowExpansionErrorConstant β/(ρ^8)^2 := by have := (narrowExpansionErrorConstant_pos β).le; positivity
  have H₁ : tripleExpansionConstant (ρ^8/narrowExpansionDenominator β)*|δ|≤2*narrowExpansionErrorConstant β*ρ^4 := by
    calc
      _ ≤ (narrowExpansionErrorConstant β/(ρ^8)^2)*(2*ρ^20) := mul_le_mul hE hδ (abs_nonneg _) hE0
      _ = _ := by field_simp
  have H₂ : β^2*δ^2*((2*(1-ρ^2)^2+(ρ^2)^2)/ρ^8)^2≤36*β^2*ρ^4 := by
    calc
      _ ≤ β^2*(4*ρ^40)*(3/ρ^8)^2 := mul_le_mul (mul_le_mul_of_nonneg_left hδ2 (sq_nonneg β)) hK2 (sq_nonneg _) (by positivity)
      _ = 36*β^2*ρ^24 := by field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hρ.le hρ1 (by decide : 4≤24)) (by positivity)
  linarith

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_TripleNegativeCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem continuousAt_small_interval {f : ℝ → ℝ} (hf : ContinuousAt f 0)
    {b L : ℝ} (hb : f 0 < b) (hL : 0 < L) :
    ∃ e ∈ Ioo (0:ℝ) L, ∀ x ∈ Icc (0:ℝ) e, f x < b := by
  obtain ⟨d,hd,hf'⟩ := Metric.eventually_nhds_iff.mp (hf.eventually_lt continuousAt_const hb)
  refine ⟨min L d/2,⟨by positivity,?_⟩,?_⟩
  · have H := min_le_left L d; linarith [lt_min hL hd]
  · intro x hx
    apply hf'
    rw [Real.dist_eq,sub_zero,abs_of_nonneg hx.1]
    have H := min_le_right L d
    linarith [hx.2]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_NarrowScaledGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem narrowConstrainedPressure_scaled_gap_oai {β m : ℝ} (hβ : β≠0) (hm : 0 < m) :
    ∃ ρ₀ c : ℝ, 0<ρ₀ ∧ 0 < c ∧ ∀ (α : StieltjesFunction ℝ),
      (∀ z,α z∈Icc (0:ℝ) 1) → α 1=1 → ∀ (N : ℕ), 0<N →
      ∀ ρ r q u δ : ℝ, 0<ρ → ρ≤ρ₀ → ρ^8 ≤ r → r+ρ≤q → q≤1 → r<u → u≤1 →
      (∀ s∈Icc r u,scalarCDFOverlap β α s=s) → m≤α r →
      scalarCDFSusceptibilityAverage β α q=(∫ x in q..1,α x)+α q*(q-scalarCDFOverlap β α q) →
      |q-scalarCDFOverlap β α q|≤ρ^13 → α (r+ρ^8)-α (r-ρ^8)≤ρ^4 →
      |δ|≤2*ρ^20 → Nonempty (MatrixStates N 3 (tripleGram r δ q)) →
      matrixConstrainedPressure N 3 β (tripleGram r δ q)≤3*scalarCDFParisi β α-c*ρ^3*δ^2 := by
  let D := narrowExpansionDenominator β
  let E := narrowExpansionErrorConstant β
  let C := narrowCDFErrorConstant β
  let c := β^2*m*scalarJointLossConstant β m
  let A := 3*β^2+2*C+2*E+36*β^2
  have hD1 : 1≤D := narrowExpansionDenominator_ge_one β
  have hD : 0<D := lt_of_lt_of_le zero_lt_one hD1
  have hE : 0<E := narrowExpansionErrorConstant_pos β
  have hC : 0≤C := narrowCDFErrorConstant_nonneg β
  have hc : 0 < c := mul_pos (mul_pos (sq_pos_of_ne_zero hβ) hm) (scalarJointLossConstant_pos hβ hm)
  have hA : 0<A := by dsimp only [A]; positivity
  let f := fun x : ℝ => x^2+16*D*x^32+2*x^20+A*x
  obtain ⟨ρ₀,hρ₀,hf⟩ := continuousAt_small_interval
    (show ContinuousAt f 0 by dsimp only [f]; fun_prop)
    (b:=min (1/2) (c/2)) (by simpa only [f,zero_pow (by decide : 2≠0),zero_pow (by decide : 32≠0),zero_pow (by decide : 20≠0),mul_zero,add_zero] using lt_min (by norm_num : (0:ℝ)<1/2) (half_pos hc)) zero_lt_one
  refine ⟨ρ₀,c/2,hρ₀.1,half_pos hc,?_⟩
  intro α hα hα1 N hN ρ r q u δ hρ hρle hhr hrq hq hru hu hΓ hmr hS hdev hosc hδ hGram
  have hρ1 : ρ≤1 := hρle.trans hρ₀.2.le
  have Hf := hf ρ ⟨hρ.le,hρle⟩
  have Hf1 : f ρ<1/2 := Hf.trans_le (min_le_left _ _)
  have Hfc : f ρ < c/2 := Hf.trans_le (min_le_right _ _)
  have hθ : 0≤ρ^2 := sq_nonneg ρ
  have hθhalf : ρ^2≤1/2 := by dsimp only [f] at Hf1; nlinarith [mul_nonneg (show 0≤16*D by positivity) (pow_nonneg hρ.le 32),pow_nonneg hρ.le 20,mul_nonneg hA.le hρ.le]
  have hsmallδ : 16*D*ρ^32≤1 := by dsimp only [f] at Hf1; nlinarith [pow_nonneg hρ.le 20,mul_nonneg hA.le hρ.le]
  have hδone : |δ|≤1 := by dsimp only [f] at Hf1; nlinarith [mul_nonneg (show 0≤16*D by positivity) (pow_nonneg hρ.le 32),mul_nonneg hA.le hρ.le]
  have hAc : A*ρ ≤ c/2 := by dsimp only [f] at Hfc; nlinarith [mul_nonneg (show 0≤16*D by positivity) (pow_nonneg hρ.le 32),pow_nonneg hρ.le 20]
  have hh : 0<ρ^8 := pow_pos hρ _
  have hh1 : ρ^8≤1 := pow_le_one₀ hρ.le hρ1
  have hhalf : 1/2≤1-ρ^2 := by linarith
  have ha : 0<1-ρ^2 := by linarith
  have hr : 0 ≤ r := hh.le.trans hhr
  have hhq : r+ρ^8≤q := by
    have H : ρ^8≤ρ := by simpa only [pow_one] using pow_le_pow_of_le_one hρ.le hρ1 (by decide : 1≤8)
    linarith
  have hrq' : r≤q := by linarith
  have hε : 0<ρ^8/D := div_pos hh hD
  have hδ2 : δ^2≤4*ρ^40 := by
    calc
      _ = |δ|^2 := (sq_abs _).symm
      _ ≤ (2*ρ^20)^2 := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hδ
      _ = _ := by ring
  have hδsmall : 4*δ^2≤ρ^8/D := by
    apply (le_div_iff₀ hD).mpr
    have H := mul_le_mul_of_nonneg_right hsmallδ hh.le
    have H' := mul_le_mul_of_nonneg_right hδ2 (show 0≤4*D by positivity)
    nlinarith only [H,H']
  have HC := narrowCDFTrialCoefficient_quantitative hβ α hα hα1 hh hr hrq' hq hru hu hΓ hm hmr hhalf hθ
    (by ring : (1-ρ^2)+ρ^2=1) hS hdev
  have Hosc := mul_le_mul_of_nonneg_left hosc hC
  have HD := mul_le_mul_of_nonneg_left (show ρ≤q-r by linarith) (show 0 ≤ c*ρ^2 by positivity)
  have Heq : 3*β^2*ρ^13/ρ^8=3*β^2*ρ^5 := by field_simp
  rw [Heq] at HC
  have HC' : narrowCDFTrialCoefficient β α r (ρ^8) q (1-ρ^2) (ρ^2)≤(3*β^2+2*C)*ρ^4-c*ρ^3 := by
    have Hp := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hρ.le hρ1 (by decide : 4≤5)) (show 0≤3*β^2 by positivity)
    change _≤_+C*(_+(ρ^2)^2)-c*ρ^2*(q-r) at HC
    nlinarith only [HC,Hosc,HD,Hp]
  have HP := narrowConstrainedPressure_continuum_trial hN β δ α hα hα1 hh hhr hhq hq ha hθ
    (by ring : (1-ρ^2)+ρ^2=1) hGram hε hδsmall hδone (narrowExpansion_smallness β hh hh1 ha.le hθ (by ring))
  have HR := narrow_scaled_remainder β hρ hρ1 hδ
  have Hrem : tripleExpansionConstant (ρ^8/D)*|δ|^3+β^2*δ^4*((2*(1-ρ^2)^2+(ρ^2)^2)/ρ^8)^2≤
      δ^2*((2*E+36*β^2)*ρ^4) := by
    have H := mul_le_mul_of_nonneg_left HR (sq_nonneg δ)
    have HE : |δ|^3=δ^2*|δ| := by rw [←sq_abs δ]; ring
    rw [HE]
    nlinarith only [H]
  have Hquad := mul_le_mul_of_nonneg_left HC' (sq_nonneg δ)
  have Habs := mul_le_mul_of_nonneg_right hAc (pow_nonneg hρ.le 3)
  have Hfinal := mul_le_mul_of_nonneg_left Habs (sq_nonneg δ)
  dsimp only [A] at Hfinal
  change _≤3*scalarCDFParisi β α+δ^2*(_)+tripleExpansionConstant (ρ^8/D)*|δ|^3+β^2*δ^4*((2*(1-ρ^2)^2+(ρ^2)^2)/ρ^8)^2 at HP
  nlinarith only [HP,Hrem,Hquad,Hfinal]

end SK.Analytic

end
end

end OAI
end

theorem solution : type_of% @OAI.SK.Analytic.narrowConstrainedPressure_scaled_gap_oai := @OAI.SK.Analytic.narrowConstrainedPressure_scaled_gap_oai
