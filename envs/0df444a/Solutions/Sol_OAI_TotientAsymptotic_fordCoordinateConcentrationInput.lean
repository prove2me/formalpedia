-- Prove2me | solution 1 for OAI.TotientAsymptotic.fordCoordinateConcentrationInput
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:34:03.10906+00:00
-- url     : https://prove2.me/submissions/bf5e6fcd-e46e-4cc4-a39a-1b521149d566

import Mathlib
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.List.Nodup
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Topology.Algebra.LinearMapCompletion
import Definitions.Def_TotientAsymptotic
import Definitions.Def_OAIQ233A000

section
-- module Solutions.OAIQ233_TA.Compat
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_Renewal
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Existence, uniqueness and positivity of the renewal parameters. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma renewalSeries_rho : renewalSeries rho = 1 := rho_mem.2.2

lemma summable_moment :
    Summable (fun n : ℕ => (n+1 : ℝ) * a (n+1) * rho^(n+1)) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (mul_nonneg (by positivity) (a_pos (by omega)).le)
      (pow_nonneg rho_pos.le _))
    (fun n => mul_le_mul_of_nonneg_right ?_ (pow_nonneg rho_pos.le _))
    (summable_index_geometric rho_pos.le rho_lt_one 2)
  have h := mul_le_mul_of_nonneg_left (a_le_index (j := n+1) (by omega))
    (show (0 : ℝ) ≤ n+1 by positivity)
  simpa [pow_two] using h

lemma gamma_pos : 0 < gamma := by
  apply inv_pos.mpr
  apply summable_moment.tsum_pos (i := 0)
  · intro n
    exact mul_nonneg (mul_nonneg (by positivity) (a_pos (by omega)).le)
      (pow_nonneg rho_pos.le _)
  · simpa using mul_pos (a_pos (j := 1) le_rfl) rho_pos

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_Normalization
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalization of totient counts and uniform coefficient asymptotics. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma g_pos (j : ℕ) : 0 < g j := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero => simp [g]
    | succ n =>
      rw [g]
      apply Finset.sum_pos'
      · intro d hd
        exact (mul_pos (a_pos (by omega)) (ih (n-d) (by omega))).le
      · refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
        simpa using mul_pos (a_pos (by omega)) (ih n (by omega))

end TotientAsymptotic
end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RenewalConvolution
attribute [-instance] _root_.W21.instNorm _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The dominated convolution limit needed for the finite-tail volume asymptotic.
The sole published input here is Ford's bounded renewal error, Lemma 3.7 of
*The distribution of totients*, arXiv:1104.3264v2 (2013), with Ford's constant
lambda denoted by gamma in this development.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma normalizedRenewal_properties (hford : FordRenewalInput) :
    Tendsto normalizedRenewal atTop (nhds gamma) ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ n, ‖normalizedRenewal n‖ ≤ K := by
  obtain ⟨C, hC, herr⟩ := hford
  have hb (n : ℕ) : |normalizedRenewal n-gamma| ≤ C*rho^n := by
    have he : normalizedRenewal n-gamma = (g n-gamma*(rho^n)⁻¹)*rho^n := by
      unfold normalizedRenewal
      field_simp [rho_pos.ne']
    rw [he, abs_mul, abs_of_pos (pow_pos rho_pos _)]
    exact mul_le_mul_of_nonneg_right (herr n) (pow_nonneg rho_pos.le _)
  constructor
  · apply tendsto_iff_dist_tendsto_zero.mpr
    refine squeeze_zero (g := fun n => C*rho^n) (fun n => dist_nonneg) ?_ ?_
    · intro n
      simpa only [Real.dist_eq] using hb n
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one rho_pos.le rho_lt_one).const_mul C
  · refine ⟨gamma+C, add_nonneg gamma_pos.le hC, fun n => ?_⟩
    have hg : 0 ≤ normalizedRenewal n := mul_nonneg (g_pos n).le (pow_nonneg rho_pos.le _)
    rw [Real.norm_eq_abs, abs_of_nonneg hg]
    have hpow : rho^n ≤ 1 := pow_le_one₀ rho_pos.le rho_lt_one.le
    have h := (abs_le.mp (hb n)).2
    nlinarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RenewalConcavity
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete concavity of the coefficients in Ford's renewal recurrence. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma a_shift_integral (j k : ℕ) :
    a (j+k)=∫ t in (j : ℝ)..(j+1 : ℝ), Real.log (t+k) := by
  rw [a_eq_integral,intervalIntegral.integral_comp_add_right]
  push_cast
  congr 1
  ring

lemma log_shift_intervalIntegrable {j : ℕ} (hj : 1≤j) (k : ℕ) :
    IntervalIntegrable (fun t : ℝ => Real.log (t+k)) MeasureTheory.volume j (j+1) := by
  have hjR : (1 : ℝ)≤j := by exact_mod_cast hj
  apply ContinuousOn.intervalIntegrable_of_Icc (by linarith)
  intro t ht
  have hn : t+(k : ℝ)≠0 := by
    have hk : (0 : ℝ)≤k := Nat.cast_nonneg _
    linarith [ht.1]
  exact ((continuousAt_id.add continuousAt_const).log hn).continuousWithinAt

lemma log_second_difference_pos {t : ℝ} (ht : 0<t) :
    0<2*Real.log (t+1)-(Real.log t+Real.log (t+2)) := by
  have ht2 : 0<t+2 := by linarith
  have hh := Real.log_lt_log (mul_pos ht ht2)
    (show t*(t+2)<(t+1)^2 by nlinarith)
  rw [Real.log_mul ht.ne' ht2.ne',Real.log_pow] at hh
  norm_num at hh
  linarith

/-- The strict second difference used in Ford Lemma 3.7. -/
lemma a_second_difference_neg {j : ℕ} (hj : 1≤j) :
    a (j+2)-2*a (j+1)+a j<0 := by
  have hjR : (1 : ℝ)≤j := by exact_mod_cast hj
  have hc : ContinuousOn
      (fun t : ℝ => 2*Real.log (t+1)-(Real.log t+Real.log (t+2)))
      (Set.Icc (j : ℝ) (j+1)) := by
    intro t ht
    have ht0 : t≠0 := by linarith [ht.1]
    have ht1 : t+1≠0 := by linarith [ht.1]
    have ht2 : t+2≠0 := by linarith [ht.1]
    exact ((continuousAt_const.mul ((continuousAt_id.add continuousAt_const).log ht1)).sub
      ((continuousAt_id.log ht0).add ((continuousAt_id.add continuousAt_const).log ht2))).continuousWithinAt
  have hi : 0<∫ t in (j : ℝ)..(j+1 : ℝ),
      2*Real.log (t+1)-(Real.log t+Real.log (t+2)) := by
    apply intervalIntegral.integral_pos (by linarith) hc
    · intro t ht
      exact (log_second_difference_pos (by linarith [ht.1])).le
    · refine ⟨j+1,⟨by linarith,le_rfl⟩,?_⟩
      exact log_second_difference_pos (by linarith)
  have h0 := log_shift_intervalIntegrable hj 0
  have h1 := log_shift_intervalIntegrable hj 1
  have h2 := log_shift_intervalIntegrable hj 2
  have he1 := a_shift_integral j 1
  have he2 := a_shift_integral j 2
  simp only [Nat.cast_one,Nat.cast_ofNat] at h1 h2 he1 he2
  simp only [Nat.cast_zero,add_zero] at h0
  rw [intervalIntegral.integral_sub (h1.const_mul 2) (h0.add h2),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_add h0 h2,
    ← he1,← he2,← a_eq_integral j] at hi
  linarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RenewalSeparation
attribute [-instance] _root_.W21.instNorm _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A small root separation for the sign of Ford's transformed coefficients. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma renewalSeries_three_sevenths_lt_one : renewalSeries (3/7)<1 := by
  let r : ℝ := 3/7
  have hr0 : 0 ≤ r := by norm_num [r]
  have hr1 : r<1 := by norm_num [r]
  have hs := summable_renewal hr0 hr1
  have hg := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1
    (r := r) (by norm_num [r])
  have hsg : HasSum (fun n : ℕ => ((n+1 : ℕ) : ℝ)*r^(n+1)) (21/16 : ℝ) := by
    have h2 := hg.mul_right r
    have e1 : (fun i : ℕ => (((i + 1).choose 1 : ℕ) : ℝ) * r ^ i * r) =
        fun n : ℕ => ((n+1 : ℕ) : ℝ)*r^(n+1) := by
      ext n
      simp only [Nat.choose_one_right,Nat.cast_add,Nat.cast_one,pow_succ]
      ring
    have e2 : (1 / (1 - r) ^ (1 + 1)) * r = (21/16 : ℝ) := by norm_num [r]
    rw [e1, e2] at h2
    exact h2
  have htail : (∑' n : ℕ, a (n+2+1)*r^(n+2+1)) ≤
      ∑' n : ℕ, ((n+2+1 : ℕ) : ℝ)*r^(n+2+1) := by
    apply ((summable_nat_add_iff 2).mpr hs).tsum_le_tsum
    · intro n
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast a_le_index (j := n+2+1) (by omega)) (pow_nonneg hr0 _)
    · exact (summable_nat_add_iff 2).mpr hsg.summable
  have hf := hs.sum_add_tsum_nat_add 2
  have hi := hsg.summable.sum_add_tsum_nat_add 2
  rw [hsg.tsum_eq] at hi
  change _=renewalSeries r at hf
  norm_num [Finset.sum_range_succ,r] at hf hi htail
  have ha1 : a 1<1/2 := by
    norm_num [a]
    linarith [Real.log_two_lt_d9]
  have ha2 : a 2<1 := by
    norm_num [a]
    linarith [Real.log_two_gt_d9,Real.log_three_lt_d9]
  change renewalSeries r<1
  nlinarith

lemma rho_gt_three_sevenths : (3/7 : ℝ) < rho := by
  by_contra! hh
  have hm := renewalSeries_strictMonoOn.monotoneOn
    (show rho∈Set.Ico (0 : ℝ) 1 from ⟨rho_pos.le,rho_lt_one⟩)
    (show (3/7 : ℝ)∈Set.Ico (0 : ℝ) 1 by norm_num) hh
  rw [renewalSeries_rho] at hm
  linarith [renewalSeries_three_sevenths_lt_one]

lemma renewal_first_transformed_negative : rho⁻¹-a 1-2<0 := by
  have hr : rho⁻¹<(7/3 : ℝ) := by
    rw [inv_eq_one_div]
    apply (div_lt_iff₀ rho_pos).mpr
    nlinarith [rho_gt_three_sevenths]
  have ha : (1/3 : ℝ)<a 1 := by
    norm_num [a]
    linarith [Real.log_two_gt_d9]
  linarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RenewalTail
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tail coefficients in (1-F(z))/(1-z/rho). -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma a_le_a_succ {j : ℕ} (hj : 1≤j) : a j≤a (j+1) := by
  have hjR : (1 : ℝ)≤j := by exact_mod_cast hj
  have h0 := log_shift_intervalIntegrable hj 0
  have h1 := log_shift_intervalIntegrable hj 1
  have he1 := a_shift_integral j 1
  simp only [Nat.cast_zero,add_zero] at h0
  simp only [Nat.cast_one] at h1 he1
  rw [a_eq_integral,he1]
  apply intervalIntegral.integral_mono_on (by linarith) h0 h1
  intro t ht
  apply Real.log_le_log (by linarith [ht.1])
  linarith

lemma summable_renewalTail (n : ℕ) :
    Summable (fun k : ℕ => a (n+k+1)*rho^(k+1)) := by
  have hgeo : Summable (fun k : ℕ => rho^(k+1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one rho_pos.le rho_lt_one)
  have hmajor := (hgeo.mul_left (n : ℝ)).add
    (summable_index_geometric rho_pos.le rho_lt_one 1)
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (a_pos (by omega)).le (pow_pos rho_pos _).le) _ hmajor
  intro k
  have hh := mul_le_mul_of_nonneg_right (a_le_index (j := n+k+1) (by omega))
    (pow_pos rho_pos (k+1)).le
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  push_cast
  ring

lemma renewalTail_zero : renewalTail 0=1 := by
  simpa only [renewalTail,Nat.zero_add,renewalSeries] using renewalSeries_rho

lemma renewalTail_nonneg (n : ℕ) : 0 ≤ renewalTail n :=
  tsum_nonneg (fun k => mul_nonneg (a_pos (by omega)).le (pow_pos rho_pos _).le)

lemma renewalTail_le_succ (n : ℕ) : renewalTail n ≤ renewalTail (n+1) := by
  apply (summable_renewalTail n).tsum_le_tsum _ (summable_renewalTail (n+1))
  intro k
  apply mul_le_mul_of_nonneg_right _ (pow_pos rho_pos _).le
  convert a_le_a_succ (j := n+k+1) (by omega) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  omega

lemma renewalTail_recurrence (n : ℕ) :
    renewalTail n=rho*a (n+1)+rho*renewalTail (n+1) := by
  have hs := (summable_renewalTail n).sum_add_tsum_nat_add 1
  have he : (∑' k : ℕ, a (n+(k+1)+1)*rho^(k+1+1))=rho*renewalTail (n+1) := by
    rw [renewalTail,← tsum_mul_left]
    apply tsum_congr
    intro k
    rw [pow_succ]
    have hn : n+(k+1)+1=(n+1)+k+1 := by omega
    rw [hn]
    ring
  change _=renewalTail n at hs
  simp only [Finset.sum_range_one,Nat.add_zero,Nat.zero_add,pow_one] at hs
  rw [he] at hs
  simpa only [mul_comm] using hs.symm

lemma renewalTail_second_difference_neg (n : ℕ) :
    renewalTail (n+2)-2*renewalTail (n+1)+renewalTail n<0 := by
  have hs0 := summable_renewalTail n
  have hs1 := summable_renewalTail (n+1)
  have hs2 := summable_renewalTail (n+2)
  have he : renewalTail (n+2)+renewalTail n<2*renewalTail (n+1) := by
    rw [renewalTail,renewalTail,renewalTail,← hs2.tsum_add hs0,← tsum_mul_left]
    apply Summable.tsum_lt_tsum (i := 0)
    · intro k
      have hd := a_second_difference_neg (j := n+k+1) (by omega)
      have hpow := pow_pos rho_pos (k+1)
      have he1 : n+k+1+1=n+1+k+1 := by omega
      have he2 : n+k+1+2=n+2+k+1 := by omega
      rw [he1,he2] at hd
      nlinarith
    · have hd := a_second_difference_neg (j := n+1) (by omega)
      simp only [Nat.add_zero,Nat.zero_add,pow_one]
      have he1 : n+1+1=n+2 := by omega
      rw [he1] at hd
      have hp := mul_lt_mul_of_pos_right hd rho_pos
      nlinarith [hp]
    · exact hs2.add hs0
    · exact hs1.mul_left 2
  linarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RenewalMoment
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Evaluation of the tail generating series at its renewal root. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

private lemma momentPair_nonneg (p : ℕ×ℕ) : 0 ≤ momentPair p :=
  mul_nonneg (a_pos (by omega)).le (pow_pos rho_pos _).le

private lemma momentPair_diagonal (n : ℕ) :
    (∑ p : ↥(Finset.HasAntidiagonal.antidiagonal n), momentPair p)=
      (n+1 : ℝ)*a (n+1)*rho^(n+1) := by
  rw [Finset.sum_coe_sort]
  have he : (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, momentPair p)=
      ∑ _p ∈ Finset.HasAntidiagonal.antidiagonal n, a (n+1)*rho^(n+1) := by
    apply Finset.sum_congr rfl
    intro p hp
    simp only [momentPair,Finset.HasAntidiagonal.mem_antidiagonal.mp hp]
  rw [he,Finset.sum_const,Finset.Nat.card_antidiagonal]
  simp only [nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
  ring

private lemma summable_momentPair : Summable momentPair := by
  let e : (Σ n : ℕ, ↥(Finset.HasAntidiagonal.antidiagonal n)) ≃ ℕ×ℕ :=
    Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd
  have hs : Summable (fun p : Σ n : ℕ, ↥(Finset.HasAntidiagonal.antidiagonal n) => momentPair p.2) := by
    apply (summable_sigma_of_nonneg
      (f := fun p : Σ n : ℕ, ↥(Finset.HasAntidiagonal.antidiagonal n) => momentPair p.2)
      (fun p => momentPair_nonneg p.2)).mpr
    constructor
    · intro n
      exact (hasSum_fintype _).summable
    · simpa only [tsum_fintype,momentPair_diagonal] using summable_moment
  exact e.summable_iff.mp hs

lemma renewalTail_weighted_sum :
    Summable (fun n : ℕ => renewalTail n*rho^n) ∧
      (∑' n : ℕ, renewalTail n*rho^n)=gamma⁻¹ := by
  let e : (Σ n : ℕ, ↥(Finset.HasAntidiagonal.antidiagonal n)) ≃ ℕ×ℕ :=
    Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd
  have he (n : ℕ) : renewalTail n*rho^n=∑' k : ℕ, momentPair (n,k) := by
    rw [renewalTail,← tsum_mul_right]
    apply tsum_congr
    intro k
    dsimp [momentPair]
    rw [mul_assoc,← pow_add]
    congr 2
    omega
  have hsum := (summable_prod_of_nonneg momentPair_nonneg).mp summable_momentPair
  refine ⟨?_,?_⟩
  · simpa only [he] using hsum.2
  · calc
      _ = ∑' n : ℕ, ∑' k : ℕ, momentPair (n,k) := tsum_congr he
      _ = ∑' p : ℕ×ℕ, momentPair p := summable_momentPair.tsum_prod.symm
      _ = ∑' p : Σ n : ℕ, ↥(Finset.HasAntidiagonal.antidiagonal n), momentPair p.2 :=
        (e.tsum_eq momentPair).symm
      _ = ∑' n : ℕ, ∑' p : ↥(Finset.HasAntidiagonal.antidiagonal n), momentPair p :=
        (e.summable_iff.mpr summable_momentPair).tsum_sigma
      _ = ∑' n : ℕ, (n+1 : ℝ)*a (n+1)*rho^(n+1) := by
        apply tsum_congr
        intro n
        rw [tsum_fintype,momentPair_diagonal]
      _ = gamma⁻¹ := by simp [gamma]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RenewalKernel
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nonnegative transformed kernel in Ford's renewal argument. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma renewalIncrement_nonneg (n : ℕ) : 0 ≤ renewalIncrement n :=
  sub_nonneg.mpr (renewalTail_le_succ n)

lemma renewalKernel_pos (n : ℕ) : 0 < renewalKernel n := by
  cases n with
  | zero =>
    have hh := renewalTail_recurrence 0
    rw [renewalTail_zero] at hh
    have he : renewalTail 1=rho⁻¹-a 1 := by
      apply (mul_left_cancel₀ rho_pos.ne')
      calc
        rho*renewalTail 1=1-rho*a 1 := by linarith
        _ = rho*(rho⁻¹-a 1) := by field_simp [rho_pos.ne']
    simpa only [renewalKernel,renewalIncrement,renewalTail_zero,he] using
      (show 0<1-((rho⁻¹-a 1)-1) by linarith [renewal_first_transformed_negative])
  | succ n =>
    have hh := renewalTail_second_difference_neg n
    change 0<(renewalTail (n+1)-renewalTail n)-
      (renewalTail (n+1+1)-renewalTail (n+1))
    have he : n+1+1=n+2 := by omega
    rw [he]
    linarith

lemma renewalKernel_partial_sum (n : ℕ) :
    (∑ j ∈ Finset.range (n+1), renewalKernel j)=1-renewalIncrement n := by
  induction n with
  | zero => simp [renewalKernel]
  | succ n ih =>
    rw [Finset.sum_range_succ,ih,renewalKernel]
    ring

lemma renewalKernel_sum_le_one (n : ℕ) :
    (∑ j ∈ Finset.range n, renewalKernel j)≤1 := by
  cases n with
  | zero => simp
  | succ n =>
    rw [renewalKernel_partial_sum]
    linarith [renewalIncrement_nonneg n]

lemma renewalResolvent_bounds (n : ℕ) : 0 ≤ renewalResolvent n ∧ renewalResolvent n≤1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => norm_num [renewalResolvent]
    | succ n =>
      have hindex (j : ℕ) (hj : j∈Finset.range (n+1)) : n-j<n+1 := by omega
      constructor
      · rw [renewalResolvent]
        exact Finset.sum_nonneg (fun j hj => mul_nonneg (renewalKernel_pos j).le
          (ih (n-j) (hindex j hj)).1)
      · rw [renewalResolvent]
        calc
          _ ≤ ∑ j ∈ Finset.range (n+1), renewalKernel j := by
            apply Finset.sum_le_sum
            intro j hj
            exact mul_le_of_le_one_right (renewalKernel_pos j).le (ih (n-j) (hindex j hj)).2
          _ ≤ 1 := renewalKernel_sum_le_one (n+1)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RenewalSeriesAlgebra
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Formal coefficient identities for Ford's transformed recurrence. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

private lemma U_kernel_identity : Useries*(1-PowerSeries.X*Pseries)=1 := by
  have he : Useries*(1-PowerSeries.X*Pseries)=Useries-PowerSeries.X*(Pseries*Useries) := by ring
  rw [he]
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [Useries,renewalResolvent]
  | succ n =>
    simp only [map_sub,PowerSeries.coeff_succ_X_mul,Useries,PowerSeries.coeff_mk,
      PowerSeries.coeff_one,Nat.succ_ne_zero,ite_false, if_false]
    rw [PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [PowerSeries.coeff_mk,Pseries,renewalResolvent,sub_self]

private lemma kernel_factorization : (1-PowerSeries.X)^2*Lseries=1-PowerSeries.X*Pseries := by
  have he : (1-PowerSeries.X)^2*Lseries=
      Lseries-PowerSeries.X*Lseries-PowerSeries.X*Lseries+
        PowerSeries.X*(PowerSeries.X*Lseries) := by ring
  rw [he]
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [Lseries,renewalTail_zero]
  | succ n =>
    cases n with
    | zero =>
      simp [PowerSeries.coeff_succ_X_mul,PowerSeries.coeff_zero_X_mul,Lseries,Pseries,
        renewalKernel,renewalIncrement,renewalTail_zero]
    | succ n =>
      simp only [map_add,map_sub,PowerSeries.coeff_succ_X_mul,Lseries,Pseries,
        PowerSeries.coeff_mk,PowerSeries.coeff_one,Nat.succ_ne_zero,ite_false, if_false,
        renewalKernel,renewalIncrement]
      ring

private lemma L_H_identity : Lseries*Hseries=1 := by
  calc
    _ = Useries*((1-PowerSeries.X)^2*Lseries) := by dsimp [Hseries] <;> ring
    _ = Useries*(1-PowerSeries.X*Pseries) := by rw [kernel_factorization]
    _ = 1 := U_kernel_identity

private lemma L_A_identity : (1-PowerSeries.C rho⁻¹*PowerSeries.X)*Lseries=1-Aseries := by
  have he : (1-PowerSeries.C rho⁻¹*PowerSeries.X)*Lseries=
      Lseries-PowerSeries.C rho⁻¹*(PowerSeries.X*Lseries) := by ring
  rw [he]
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [Lseries,Aseries,renewalTail_zero]
  | succ n =>
    simp only [map_sub,PowerSeries.coeff_C_mul,PowerSeries.coeff_succ_X_mul,Lseries,Aseries,
      PowerSeries.coeff_mk,PowerSeries.coeff_one,Nat.succ_ne_zero,ite_false, if_false]
    have he := renewalTail_recurrence n
    have hh : rho⁻¹*renewalTail n=a (n+1)+renewalTail (n+1) := by
      rw [he]
      field_simp [rho_pos.ne']
    linarith

private lemma G_A_identity : Gseries*(1-Aseries)=1 := by
  have he : Gseries*(1-Aseries)=Gseries-PowerSeries.X*(PowerSeries.mk (fun n => a (n+1))*Gseries) := by
    dsimp [Aseries]
    ring
  rw [he]
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [Gseries,g]
  | succ n =>
    simp only [map_sub,PowerSeries.coeff_succ_X_mul,Gseries,PowerSeries.coeff_mk,
      PowerSeries.coeff_one,Nat.succ_ne_zero,ite_false, if_false]
    rw [PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [PowerSeries.coeff_mk,g,sub_self]

private lemma G_H_identity : Gseries*(1-PowerSeries.C rho⁻¹*PowerSeries.X)=Hseries := by
  calc
    _ = Gseries*(1-PowerSeries.C rho⁻¹*PowerSeries.X)*(Lseries*Hseries) := by rw [L_H_identity,mul_one]
    _ = (Gseries*((1-PowerSeries.C rho⁻¹*PowerSeries.X)*Lseries))*Hseries := by ring
    _ = (Gseries*(1-Aseries))*Hseries := by rw [L_A_identity]
    _ = Hseries := by rw [G_A_identity,one_mul]

lemma renewalRegular_bound (n : ℕ) : |renewalRegular n|≤4 := by
  have he : Hseries=Useries-PowerSeries.X*Useries-PowerSeries.X*Useries+
        PowerSeries.X*(PowerSeries.X*Useries) := by dsimp [Hseries] <;> ring
  rw [renewalRegular,he]
  cases n with
  | zero => norm_num [PowerSeries.coeff_zero_X_mul,Useries,renewalResolvent]
  | succ n =>
    cases n with
    | zero =>
      simp only [map_add,map_sub,PowerSeries.coeff_succ_X_mul,PowerSeries.coeff_zero_X_mul,
        Useries,PowerSeries.coeff_mk]
      norm_num only [show renewalResolvent 0=1 by rw [renewalResolvent],zero_add,add_zero]
      have hb := renewalResolvent_bounds 1
      rw [abs_le]
      constructor <;> linarith
    | succ n =>
      simp only [map_add,map_sub,PowerSeries.coeff_succ_X_mul,Useries,PowerSeries.coeff_mk]
      have h0 := renewalResolvent_bounds n
      have h1 := renewalResolvent_bounds (n+1)
      have h2 := renewalResolvent_bounds (n+1+1)
      rw [abs_le]
      constructor <;> linarith

lemma renewalRegular_zero : renewalRegular 0=1 := by
  simp [renewalRegular,Hseries,Useries,renewalResolvent]

lemma renewalRegular_recurrence (n : ℕ) :
    renewalRegular (n+1)=g (n+1)-rho⁻¹*g n := by
  have h := congrArg (PowerSeries.coeff (n+1)) G_H_identity
  rw [mul_sub,mul_one] at h
  have he : Gseries*(PowerSeries.C rho⁻¹*PowerSeries.X)=
      PowerSeries.C rho⁻¹*(Gseries*PowerSeries.X) := by ring
  rw [he] at h
  simpa only [map_sub,PowerSeries.coeff_C_mul,PowerSeries.coeff_succ_mul_X,Gseries,
    PowerSeries.coeff_mk,renewalRegular] using h.symm

lemma renewalTail_regular_convolution (n : ℕ) :
    (∑ j ∈ Finset.range (n+1), renewalTail j*renewalRegular (n-j))=
      if n=0 then 1 else 0 := by
  have h := congrArg (PowerSeries.coeff n) L_H_identity
  rw [PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simpa only [Lseries,PowerSeries.coeff_mk,renewalRegular,PowerSeries.coeff_one] using h

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RenewalRegularSum
attribute [-instance] _root_.W21.instNorm _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constant term at the renewal pole, using absolutely convergent sums. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma summable_norm_regular_weighted :
    Summable (fun n : ℕ => ‖renewalRegular n*rho^n‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    ((summable_geometric_of_lt_one rho_pos.le rho_lt_one).mul_left 4)
  intro n
  rw [norm_mul,Real.norm_eq_abs (rho^n),abs_of_pos (pow_pos rho_pos n),Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (renewalRegular_bound n) (pow_pos rho_pos n).le

lemma regular_weighted_sum_eq_gamma :
    (∑' n : ℕ, renewalRegular n*rho^n)=gamma := by
  have hL : Summable (fun n : ℕ => ‖renewalTail n*rho^n‖) := by
    convert renewalTail_weighted_sum.1 using 1
    all_goals try with_reducible_and_instances rfl
    ext n
    exact Real.norm_of_nonneg (mul_nonneg (renewalTail_nonneg n) (pow_pos rho_pos n).le)
  have ht := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hL summable_norm_regular_weighted
  have he (n : ℕ) : (∑ j ∈ Finset.range (n+1),
      (renewalTail j*rho^j)*(renewalRegular (n-j)*rho^(n-j)))=
      if n=0 then 1 else 0 := by
    calc
      _ = (∑ j ∈ Finset.range (n+1), renewalTail j*renewalRegular (n-j))*rho^n := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        have hjn : j≤n := by have := Finset.mem_range.mp hj; omega
        have hp : rho^j*rho^(n-j)=rho^n := by rw [← pow_add,Nat.add_sub_of_le hjn]
        calc
          _ = (renewalTail j*renewalRegular (n-j))*(rho^j*rho^(n-j)) := by ring
          _ = _ := by rw [hp]
      _ = _ := by rw [renewalTail_regular_convolution]; split_ifs with hn <;> simp [hn]
  simp only [he] at ht
  rw [renewalTail_weighted_sum.2] at ht
  have hs : (∑' n : ℕ, if n=0 then (1 : ℝ) else 0)=1 := by simp
  rw [hs] at ht
  have hmul := congrArg (fun x : ℝ => gamma*x) ht
  simpa only [← mul_assoc,mul_inv_cancel₀ gamma_pos.ne',one_mul,mul_one] using hmul

lemma normalized_renewal_eq_regular_partial (n : ℕ) :
    g n*rho^n=∑ j ∈ Finset.range (n+1), renewalRegular j*rho^j := by
  induction n with
  | zero => simp [g,renewalRegular_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ,← ih,renewalRegular_recurrence,pow_succ]
    field_simp [rho_pos.ne']
    ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RenewalInput
attribute [-instance] _root_.W21.instNorm _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Discharge of Ford Lemma 3.7 by the concrete transformed recurrence. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

private lemma regular_tail_bound (n : ℕ) :
    |∑' k : ℕ, renewalRegular (k+n+1)*rho^(k+1)|≤4*rho/(1-rho) := by
  have hg : HasSum (fun k : ℕ => 4*rho^(k+1)) (4*rho/(1-rho)) := by
    have h2 := (hasSum_geometric_of_lt_one rho_pos.le rho_lt_one).mul_left (4*rho)
    have e1 : (fun k : ℕ => 4*rho * rho^k) = fun k : ℕ => 4*rho^(k+1) := by
      ext k
      rw [pow_succ]
      ring
    have e2 : 4*rho*(1-rho)⁻¹ = 4*rho/(1-rho) := by rw [div_eq_mul_inv]
    rw [e1, e2] at h2
    exact h2
  have hb (k : ℕ) : ‖renewalRegular (k+n+1)*rho^(k+1)‖≤4*rho^(k+1) := by
    rw [norm_mul,Real.norm_eq_abs (rho^(k+1)),abs_of_pos (pow_pos rho_pos _),Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (renewalRegular_bound _) (pow_pos rho_pos _).le
  have hs : Summable (fun k : ℕ => ‖renewalRegular (k+n+1)*rho^(k+1)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hg.summable
  calc
    _ = ‖∑' k : ℕ, renewalRegular (k+n+1)*rho^(k+1)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' k : ℕ, ‖renewalRegular (k+n+1)*rho^(k+1)‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' k : ℕ, 4*rho^(k+1) := hs.tsum_le_tsum hb hg.summable
    _ = _ := hg.tsum_eq

/-- The bounded renewal error assumed throughout the conditional development
is now proved. A coarse explicit constant suffices for every application. -/
theorem fordRenewalInput : FordRenewalInput := by
  refine ⟨4*rho/(1-rho),div_nonneg (mul_nonneg (by norm_num) rho_pos.le) (by linarith [rho_lt_one]),?_⟩
  intro n
  have hp : rho^n≠0 := (pow_pos rho_pos n).ne'
  have hs := summable_norm_regular_weighted.of_norm.sum_add_tsum_nat_add (n+1)
  rw [regular_weighted_sum_eq_gamma,← normalized_renewal_eq_regular_partial n] at hs
  have he : (∑' k : ℕ, renewalRegular (k+(n+1))*rho^(k+(n+1)))=
      (∑' k : ℕ, renewalRegular (k+n+1)*rho^(k+1))*rho^n := by
    rw [← tsum_mul_right]
    apply tsum_congr
    intro k
    have hpow : rho^(k+(n+1))=rho^(k+1)*rho^n := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow]
    have hn : k+(n+1)=k+n+1 := by omega
    rw [hn]
    ring
  rw [he] at hs
  have herror : g n-gamma*(rho^n)⁻¹= -∑' k : ℕ, renewalRegular (k+n+1)*rho^(k+1) := by
    apply (mul_right_cancel₀ hp)
    calc
      (g n-gamma*(rho^n)⁻¹)*rho^n=g n*rho^n-gamma := by field_simp
      _ = _ := by nlinarith [hs]
  rw [herror,abs_neg]
  exact regular_tail_bound n

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrefixGeometry
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The triangular slack calculation underlying `lem:simplex` and
`eq:intersection-volume` in the manuscript. These are identities for the
actual renewal coefficients, with no volume or counting estimate assumed.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma g_convolution {j : ℕ} (hj : 0 < j) :
    g j = ∑ i ∈ Finset.range j, g i * a (j-i) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
  rw [g]
  apply Finset.sum_bij (fun d _ => n-d)
  · intro d hd
    have hd' := Finset.mem_range.mp hd
    exact Finset.mem_range.mpr (by omega)
  · intro d hd e he hde
    have hd' := Finset.mem_range.mp hd
    have he' := Finset.mem_range.mp he
    omega
  · intro i hi
    have hi' := Finset.mem_range.mp hi
    refine ⟨n-i, Finset.mem_range.mpr (by omega), ?_⟩
    omega
  · intro d hd
    have hd' := Finset.mem_range.mp hd
    have he : n+1-(n-d) = d+1 := by omega
    rw [he, mul_comm]

lemma weighted_slack_identity (N : ℕ) (u : ℕ → ℝ) :
    ∑ i ∈ Finset.range (N+1), g i * prefixSlack N u i = u 0 := by
  have inner (j : ℕ) (hj : j ∈ Finset.range (N+1)) :
      (∑ i ∈ Finset.range (N+1), if i < j then g i * (a (j-i) * u j) else 0) =
        g j * u j - if j = 0 then u 0 else 0 := by
    have hsub : Finset.range j ⊆ Finset.range (N+1) :=
      Finset.range_mono (Nat.le_of_lt (Finset.mem_range.mp hj))
    have he : (∑ i ∈ Finset.range (N+1), if i < j then g i * (a (j-i) * u j) else 0) =
        ∑ i ∈ Finset.range j, g i * (a (j-i) * u j) := by
      symm
      calc
        _ = ∑ i ∈ Finset.range j, if i < j then g i * (a (j-i) * u j) else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [ite_eq_left (Finset.mem_range.mp hi)]
        _ = _ := Finset.sum_subset hsub (by
          intro i _ hi
          rw [ite_eq_right (by simpa using hi)])
    rw [he]
    by_cases hj0 : j = 0
    · subst j
      simp [g]
    · rw [ite_eq_right hj0, sub_zero, g_convolution (Nat.pos_of_ne_zero hj0), Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
  simp only [prefixSlack, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  have hs : (∑ i ∈ Finset.range (N+1),
      ∑ j ∈ Finset.range (N+1), g i * (if i < j then a (j-i)*u j else 0)) =
      ∑ j ∈ Finset.range (N+1), (g j * u j - if j = 0 then u 0 else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    simpa only [mul_ite, mul_zero] using inner j hj
  rw [hs, Finset.sum_sub_distrib]
  simp

lemma prefixLinear_preserves_volume (N : ℕ) :
    MeasureTheory.Measure.map (prefixLinear N) MeasureTheory.volume = MeasureTheory.volume := by
  rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi (by rw [prefixLinear_det]; norm_num),
    prefixLinear_det]
  simp

lemma prefixLinear_apply (N : ℕ) (u : Fin N → ℝ) (i : Fin N) :
    prefixLinear N u i = u i - ∑ j : Fin N,
      if i < j then a (j.val-i.val) * u j else 0 := by
  change (∑ j : Fin N, prefixMatrix N i j * u j) = _
  have he (j : Fin N) : prefixMatrix N i j * u j =
      (if j = i then u j else 0) -
        (if i < j then a (j.val-i.val) * u j else 0) := by
    by_cases hij : i = j
    · subst j
      simp [prefixMatrix]
    · by_cases hij' : i < j <;> simp [prefixMatrix, hij, Ne.symm hij, hij']
  simp_rw [he]
  rw [Finset.sum_sub_distrib]
  simp

lemma prefixLinear_vector (N : ℕ) (u : ℕ → ℝ) (i : Fin N) :
    prefixLinear N (prefixVector N u) i = prefixSlack N u (i.val+1) := by
  rw [prefixLinear_apply]
  unfold prefixSlack prefixVector
  rw [Finset.sum_range_succ']
  simp only [Fin.lt_def, not_lt_zero, ite_false, if_false, add_zero]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun k => if i.val < k then a (k-i.val) * u (k+1) else 0)]
  apply Finset.sum_congr rfl
  intro j _
  simp

lemma prefixSlack_zero (N : ℕ) (u : ℕ → ℝ) :
    prefixSlack N u 0 = u 0 - ∑ i : Fin N, a (i.val+1) * u (i.val+1) := by
  unfold prefixSlack
  rw [Finset.sum_range_succ']
  simp only [Nat.zero_lt_succ, ite_true, if_true, Nat.sub_zero, lt_self_iff_false, ite_false, if_false, add_zero]
  rw [Fin.sum_univ_eq_sum_range (fun k => a (k+1) * u (k+1))]

lemma weighted_prefix_vector (N : ℕ) (u : ℕ → ℝ) :
    ∑ i : Fin N, g (i.val+1) * prefixLinear N (prefixVector N u) i =
      ∑ i : Fin N, a (i.val+1) * u (i.val+1) := by
  have h := weighted_slack_identity N u
  rw [Finset.sum_range_succ', ← Fin.sum_univ_eq_sum_range,
    prefixSlack_zero] at h
  have hg0 : g 0 = 1 := by simp [g]
  rw [hg0, one_mul] at h
  simp_rw [prefixLinear_vector]
  linarith

lemma prefixVector_extend (N : ℕ) (u : Fin N → ℝ) :
    prefixVector N (extendPrefix N u) = u := by
  funext i
  simp [prefixVector, extendPrefix]

lemma weighted_prefixLinear (N : ℕ) (u : Fin N → ℝ) :
    ∑ i : Fin N, g (i.val+1) * prefixLinear N u i =
      ∑ i : Fin N, a (i.val+1) * u i := by
  have h := weighted_prefix_vector N (extendPrefix N u)
  simpa [prefixVector_extend, extendPrefix] using h

/-- The available slack is the top budget minus all weighted tail thresholds. -/
lemma prefixRegion_eq_simplex_preimage (N : ℕ) (B C₀ : ℝ) (C : Fin N → ℝ) :
    prefixRegion N B C₀ C =
      (fun u => prefixLinear N u - C) ⁻¹'
        weightedSimplex N (B-C₀-∑ i : Fin N, g (i.val+1)*C i) := by
  ext u
  simp only [prefixRegion, weightedSimplex, Set.mem_ofPred_eq, Set.mem_preimage,
    Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, weighted_prefixLinear]
  constructor
  · rintro ⟨hlo, hsum⟩
    exact ⟨fun i => sub_nonneg.mpr (hlo i), sub_le_sub_right hsum _⟩
  · rintro ⟨hlo, hsum⟩
    exact ⟨fun i => sub_nonneg.mp (hlo i), (sub_le_sub_iff_right _).mp hsum⟩

lemma prefixAffine_preserves_volume (N : ℕ) (C : Fin N → ℝ) :
    MeasureTheory.MeasurePreserving (fun u => prefixLinear N u - C)
      MeasureTheory.volume MeasureTheory.volume := by
  have hlin : MeasureTheory.MeasurePreserving (prefixLinear N)
      MeasureTheory.volume MeasureTheory.volume :=
    ⟨(prefixLinear N).continuous_of_finiteDimensional.measurable,
      prefixLinear_preserves_volume N⟩
  simpa only [sub_eq_add_neg, Function.comp_def] using
    (MeasureTheory.measurePreserving_add_right MeasureTheory.volume (-C)).comp hlin

lemma measurableSet_weightedSimplex (N : ℕ) (T : ℝ) :
    MeasurableSet (weightedSimplex N T) := by
  change MeasurableSet ({v : Fin N → ℝ | ∀ i, 0 ≤ v i} ∩
    {v : Fin N → ℝ | (∑ i, g (i.val+1) * v i) ≤ T})
  apply MeasurableSet.inter
  · rw [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i => (isClosed_le continuous_const (continuous_apply i)).measurableSet)
  · exact measurableSet_le (by fun_prop) measurable_const

/-- Exact reduction of the prefix volume, valid for every fixed tail threshold. -/
theorem volume_prefixRegion (N : ℕ) (B C₀ : ℝ) (C : Fin N → ℝ) :
    MeasureTheory.volume (prefixRegion N B C₀ C) =
      MeasureTheory.volume
        (weightedSimplex N (B-C₀-∑ i : Fin N, g (i.val+1)*C i)) := by
  rw [prefixRegion_eq_simplex_preimage]
  exact (prefixAffine_preserves_volume N C).measure_preimage
    (measurableSet_weightedSimplex _ _).nullMeasurableSet

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrefixLower
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Propagating the first discrete tail coordinate through the prefix. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

/-- The renewal recurrence propagates any terminal lower bound through the
triangular prefix inequalities. This includes the first discrete tail prime. -/
theorem renewal_prefix_lower (N : ℕ) (u : ℕ → ℝ)
    (hs : ∀ i < N, (∑ j ∈ Finset.Icc (i+1) N, a (j-i)*u j) ≤ u i)
    {i : ℕ} (hi : i ≤ N) : g (N-i)*u N ≤ u i := by
  have hmain : ∀ d : ℕ, ∀ j : ℕ, j+d=N → g d*u N ≤ u j := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro j hj
      by_cases hd : d = 0
      · subst d
        have hjN : j = N := by omega
        simp [hjN, g]
      · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
        have hrec := g_convolution hdpos
        calc
          g d*u N = ∑ r ∈ Finset.range d, a (d-r)*(g r*u N) := by
            rw [hrec, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro r hr
            ring
          _ ≤ ∑ r ∈ Finset.range d, a (d-r)*u (N-r) := by
            apply Finset.sum_le_sum
            intro r hr
            have hrd := Finset.mem_range.mp hr
            apply mul_le_mul_of_nonneg_left
              (ih r hrd (N-r) (by omega)) (a_pos (by omega)).le
          _ = ∑ k ∈ Finset.Icc (j+1) N, a (k-j)*u k := by
            apply Finset.sum_bij (fun r _ => N-r)
            · intro r hr
              have := Finset.mem_range.mp hr
              exact Finset.mem_Icc.mpr (by omega)
            · intro r hr s hs hrs
              have := Finset.mem_range.mp hr
              have := Finset.mem_range.mp hs
              omega
            · intro k hk
              have := Finset.mem_Icc.mp hk
              exact ⟨N-k, Finset.mem_range.mpr (by omega), by omega⟩
            · intro r hr
              have := Finset.mem_range.mp hr
              congr 2
              omega
          _ ≤ u j := hs j (by omega)
  exact hmain (N-i) i (Nat.add_sub_of_le hi)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RenewalLower
attribute [-instance] _root_.W21.instNorm _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform lower bounds for renewal coefficients and unbanded prefix coordinates. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma normalizedRenewal_pos (n : ℕ) : 0 < normalizedRenewal n :=
  mul_pos (g_pos _) (pow_pos rho_pos _)

lemma renewal_uniform_lower (hford : FordRenewalInput) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, c*(rho^n)⁻¹ ≤ g n := by
  have hlim := (normalizedRenewal_properties hford).1
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hlim.eventually (eventually_gt_nhds (show gamma/2 < gamma by linarith [gamma_pos])))
  let T := insert (gamma/2) ((Finset.range N).image normalizedRenewal)
  have hT : T.Nonempty := Finset.insert_nonempty _ _
  let c := T.min' hT
  have hc : 0 < c := by
    apply (Finset.lt_min'_iff _ _).mpr
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact div_pos gamma_pos (by norm_num)
    · obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hy
      exact normalizedRenewal_pos n
  refine ⟨c, hc, fun n => ?_⟩
  have hh : c ≤ normalizedRenewal n := by
    by_cases hn : n < N
    · exact Finset.min'_le _ _ (Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr hn, rfl⟩))
    · exact (Finset.min'_le _ _ (Finset.mem_insert_self _ _)).trans (hN n (by omega)).le
  have hp := mul_le_mul_of_nonneg_right hh (inv_pos.mpr (pow_pos rho_pos n)).le
  simpa only [normalizedRenewal, mul_assoc, mul_inv_cancel₀ (pow_pos rho_pos n).ne', mul_one]
    using hp

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RenewalRatios
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform coefficient ratios for the simplex coordinate estimates. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma renewal_ratio_error : ∃ C : ℝ, 0<C ∧ ∀ i k : ℕ,
    |g k/(rho^i*g (i+k))-1|≤C*rho^k := by
  obtain ⟨E,hE,he⟩ := fordRenewalInput
  obtain ⟨c,hc,hg⟩ := renewal_uniform_lower fordRenewalInput
  refine ⟨2*(E+1)/c,by positivity,?_⟩
  intro i k
  have hr : 0 < rho^i := pow_pos rho_pos i
  have hrk : 0 < rho^k := pow_pos rho_pos k
  have hi1 : rho^i≤1 := pow_le_one₀ rho_pos.le rho_lt_one.le
  have hD : 0 < rho^i*g (i+k) := mul_pos hr (g_pos _)
  have hnorm : |g k-rho^i*g (i+k)|≤2*(E+1) := by
    have hid : g k-rho^i*g (i+k)=
        (g k-gamma*(rho^k)⁻¹)-rho^i*(g (i+k)-gamma*(rho^(i+k))⁻¹) := by
      rw [pow_add]
      field_simp [hr.ne',hrk.ne']
      ring
    rw [hid]
    calc
      _ ≤ |g k-gamma*(rho^k)⁻¹|+|rho^i*(g (i+k)-gamma*(rho^(i+k))⁻¹)| := abs_sub _ _
      _ ≤ E+rho^i*E := by
        rw [abs_mul,abs_of_pos hr]
        exact add_le_add (he k) (mul_le_mul_of_nonneg_left (he (i+k)) hr.le)
      _ ≤ 2*(E+1) := by nlinarith
  have hden : c*(rho^k)⁻¹ ≤ rho^i*g (i+k) := by
    have hh := mul_le_mul_of_nonneg_left (hg (i+k)) hr.le
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    rw [pow_add]
    field_simp [hr.ne',hrk.ne']
  have hi : (rho^i*g (i+k))⁻¹ ≤ rho^k/c := by
    have hh := inv_anti₀ (mul_pos hc (inv_pos.mpr hrk)) hden
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    simp only [mul_inv_rev,inv_inv,div_eq_mul_inv]
  have hid : g k/(rho^i*g (i+k))-1=(g k-rho^i*g (i+k))/(rho^i*g (i+k)) := by
    field_simp [hD.ne', (g_pos (i+k)).ne', hr.ne']
  rw [hid,abs_div,abs_of_pos hD,div_eq_mul_inv]
  calc
    _ ≤ 2*(E+1)*(rho^k/c) := mul_le_mul hnorm hi (inv_pos.mpr hD).le (by positivity)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ConcentrationExponents
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The numerical exponent saving for fixed one-fortieth deviations. -/
noncomputable section
namespace TotientAsymptotic

lemma concentrationTilt_pos {M : ℝ} (hM : 1 ≤ M) : 0 < concentrationTilt M := by
  unfold concentrationTilt
  positivity

lemma concentrationTilt_mul {M : ℝ} (hM : 1 ≤ M) : concentrationTilt M*M = 1/320 := by
  unfold concentrationTilt
  field_simp

lemma concentrationTilt_le {M : ℝ} (hM : 1 ≤ M) : concentrationTilt M ≤ 1/320 := by
  have hs := concentrationTilt_pos hM
  have hm := concentrationTilt_mul hM
  nlinarith

lemma concentration_exponents {M K m S Q : ℝ} (hM : 1 ≤ M) (hK : 0 ≤ K)
    (hm : 1 ≤ m) (hS : |S-m| ≤ K) (hQ : Q ≤ M*(m+K)) :
    let s := concentrationTilt M
    (s*(39/40)*(m-1)-s*S+2*s^2*Q ≤ 3*s*(K+1)-(s/100)*(m-1)) ∧
    (-s*(41/40)*(m-1)+s*S+2*s^2*Q ≤ 3*s*(K+1)-(s/100)*(m-1)) := by
  dsimp only
  let s := concentrationTilt M
  have hs : 0 < s := concentrationTilt_pos hM
  have hsm : s*M = 1/320 := concentrationTilt_mul hM
  have hquad : 2*s^2*Q ≤ (s/160)*(m+K) := by
    have hh := mul_le_mul_of_nonneg_left hQ (show 0 ≤ 2*s^2 by positivity)
    have he : 2*s^2*(M*(m+K)) = (s/160)*(m+K) := by
      calc
        _ = 2*s*(s*M)*(m+K) := by ring
        _ = _ := by rw [hsm]; ring
    exact hh.trans_eq he
  have hSm := abs_le.mp hS
  have hSl := mul_le_mul_of_nonneg_left hSm.1 hs.le
  have hSu := mul_le_mul_of_nonneg_left hSm.2 hs.le
  have hsk : 0 ≤ s*K := mul_nonneg hs.le hK
  have hsm' : s ≤ s*m := le_mul_of_one_le_right hs.le hm
  constructor <;> dsimp only [s] at * <;> nlinarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrefixCoordinates
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact coordinates of the triangular prefix simplex in its slack variables. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma prefixSlack_shift (N : ℕ) (u : ℕ → ℝ) {i : ℕ} (hi : i ≤ N) (k : ℕ) :
    prefixSlack (N-i) (fun j => u (i+j)) k = prefixSlack N u (i+k) := by
  have hs : (∑ j ∈ Finset.range (N+1),
      if i+k < j then a (j-(i+k))*u j else 0) =
      ∑ j ∈ Finset.range (N-i+1), if k < j then a (j-k)*u (i+j) else 0 := by
    rw [show N+1 = i+(N-i+1) by omega, Finset.sum_range_add]
    have hz : (∑ j ∈ Finset.range i,
        if i+k < j then a (j-(i+k))*u j else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [ite_eq_right (by have := Finset.mem_range.mp hj; omega)]
    rw [hz, zero_add]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Nat.add_lt_add_iff_left, Nat.add_sub_add_left]
  simp only [prefixSlack, hs]

lemma prefix_coordinate_slacks (N : ℕ) (u : ℕ → ℝ) {i : ℕ} (hi : i ≤ N) :
    u i = ∑ k ∈ Finset.range (N-i+1), g k*prefixSlack N u (i+k) := by
  have hh := weighted_slack_identity (N-i) (fun j => u (i+j))
  simp only [prefixSlack_shift N u hi, Nat.add_zero] at hh
  exact hh.symm

lemma prefix_coordinate_full_sum (N : ℕ) (u : ℕ → ℝ) {i : ℕ} (hi : i < N) :
    u (i+1) = ∑ j ∈ Finset.range N,
      if i ≤ j then g (j-i)*prefixSlack N u (j+1) else 0 := by
  rw [prefix_coordinate_slacks N u (by omega : i+1 ≤ N)]
  have hsplit := Finset.sum_range_add
    (fun j => if i ≤ j then g (j-i)*prefixSlack N u (j+1) else 0) i (N-i)
  rw [Nat.add_sub_of_le hi.le] at hsplit
  rw [hsplit]
  have hz : (∑ j ∈ Finset.range i,
      if i ≤ j then g (j-i)*prefixSlack N u (j+1) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [ite_eq_right (by have := Finset.mem_range.mp hj; omega)]
  rw [hz, zero_add]
  have he : N-(i+1)+1 = N-i := by omega
  rw [he]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Nat.le_add_right, ite_true, if_true, Nat.add_sub_cancel_left]
  congr 2
  omega

/-- The inverse of the determinant-one triangular slack map. -/
theorem prefixLinear_coordinate (N : ℕ) (u : Fin N → ℝ) (i : Fin N) :
    u i = ∑ j : Fin N,
      if i ≤ j then g (j.val-i.val)*prefixLinear N u j else 0 := by
  have hh := prefix_coordinate_full_sum N (extendPrefix N u) i.isLt
  have hv : extendPrefix N u (i.val+1) = u i := by simp [extendPrefix]
  rw [hv] at hh
  rw [← Fin.sum_univ_eq_sum_range] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro j _
  rw [← prefixLinear_vector, prefixVector_extend]
  rfl

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SimplexVolume
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The elementary simplex volume used by the prefix mass calculation. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

lemma measurableSet_standardSimplex (N : ℕ) (T : ℝ) :
    MeasurableSet (standardSimplex N T) := by
  change MeasurableSet ({v : Fin N → ℝ | ∀ i, 0 ≤ v i} ∩
    {v : Fin N → ℝ | (∑ i, v i) ≤ T})
  apply MeasurableSet.inter
  · rw [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i =>
      (isClosed_le continuous_const (continuous_apply i)).measurableSet)
  · exact measurableSet_le (by fun_prop) measurable_const

lemma measurableSet_simplexSection (N : ℕ) (T : ℝ) :
    MeasurableSet (simplexSection N T) := by
  change MeasurableSet ({p : ℝ × (Fin N → ℝ) | p.1 ∈ Set.Icc 0 T} ∩
    ({p : ℝ × (Fin N → ℝ) | ∀ i, 0 ≤ p.2 i} ∩
      {p : ℝ × (Fin N → ℝ) | (∑ i, p.2 i) ≤ T-p.1}))
  apply MeasurableSet.inter (measurable_fst measurableSet_Icc)
  apply MeasurableSet.inter
  · rw [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i =>
      (isClosed_le continuous_const ((continuous_apply i).comp continuous_snd)).measurableSet)
  · exact measurableSet_le (by fun_prop) (by fun_prop)

lemma standardSimplex_succ_preimage (N : ℕ) (T : ℝ) :
    standardSimplex (N+1) T =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N+1) => ℝ) 0) ⁻¹'
        simplexSection N T := by
  ext u
  simp only [standardSimplex, simplexSection, Set.mem_preimage, Set.mem_ofPred_eq,
    MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply,
    Fin.removeNth, Fin.succAbove_zero, Set.mem_Icc]
  simp only [Fin.sum_univ_succ, Fin.forall_fin_succ]
  constructor
  · rintro ⟨⟨h0, hn⟩, hs⟩
    have hn' : 0 ≤ ∑ i : Fin N, u i.succ := Finset.sum_nonneg (fun i _ => hn i)
    exact ⟨⟨h0, by linarith⟩, ⟨hn, by linarith⟩⟩
  · rintro ⟨⟨h0, _⟩, hn, hs⟩
    exact ⟨⟨h0, hn⟩, by linarith⟩

lemma volume_standardSimplex_succ (N : ℕ) (T : ℝ) :
    volume (standardSimplex (N+1) T) =
      ∫⁻ x in Set.Icc 0 T, volume (standardSimplex N (T-x)) := by
  rw [standardSimplex_succ_preimage]
  rw [(volume_preserving_piFinSuccAbove (fun _ : Fin (N+1) => ℝ) 0).measure_preimage
    (measurableSet_simplexSection N T).nullMeasurableSet]
  change (volume.prod volume) (simplexSection N T) = _
  rw [Measure.prod_apply (measurableSet_simplexSection N T)]
  rw [← lintegral_indicator measurableSet_Icc]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ Set.Icc 0 T
  · have hx' := hx
    simp only [Set.mem_Icc] at hx'
    simp [simplexSection, hx, hx'.1, hx'.2]
  · have hx' : ¬ (0 ≤ x ∧ x ≤ T) := hx
    simp [simplexSection, hx, hx']

lemma volume_standardSimplex_zero {T : ℝ} (hT : 0 ≤ T) :
    volume (standardSimplex 0 T) = 1 := by
  have he : standardSimplex 0 T = Set.univ := by
    ext u
    simp [standardSimplex, hT]
  rw [he]
  change Measure.pi (fun _ : Fin 0 => (volume : Measure ℝ)) Set.univ = 1
  simp

lemma integral_simplex_power (N : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ x in Set.Icc 0 T, (T-x)^N / (N.factorial : ℝ)) =
      T^(N+1) / ((N+1).factorial : ℝ) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT,
    intervalIntegral.integral_div]
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x^N)]
  simp only [sub_zero, sub_self]
  rw [integral_pow]
  simp only [zero_pow (by omega : N+1 ≠ 0), sub_zero,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [div_div]

theorem volume_standardSimplex (N : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    volume (standardSimplex N T) = ENNReal.ofReal (T^N / (N.factorial : ℝ)) := by
  induction N generalizing T with
  | zero => simpa using volume_standardSimplex_zero hT
  | succ N ih =>
    rw [volume_standardSimplex_succ]
    have he : (∫⁻ x in Set.Icc 0 T, volume (standardSimplex N (T-x))) =
        ∫⁻ x in Set.Icc 0 T, ENNReal.ofReal ((T-x)^N / (N.factorial : ℝ)) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro x hx
      exact ih (sub_nonneg.mpr hx.2)
    rw [he, ← ofReal_integral_eq_lintegral_ofReal]
    · rw [integral_simplex_power N hT]
    · exact (show Continuous (fun x : ℝ => (T-x)^N / (N.factorial : ℝ)) by
        fun_prop).continuousOn.integrableOn_Icc
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      exact div_nonneg (pow_nonneg (sub_nonneg.mpr hx.2) _) (Nat.cast_nonneg _)

lemma weightedScale_apply (N : ℕ) (v : Fin N → ℝ) (i : Fin N) :
    weightedScale N v i = g (i.val+1) * v i := by
  simp [weightedScale, Matrix.toLin'_apply, Matrix.mulVec_diagonal]

lemma weightedScale_det (N : ℕ) :
    LinearMap.det (weightedScale N) = ∏ i : Fin N, g (i.val+1) := by
  rw [weightedScale, LinearMap.det_toLin', Matrix.det_diagonal]

lemma weightedScale_det_pos (N : ℕ) : 0 < LinearMap.det (weightedScale N) := by
  rw [weightedScale_det]
  exact Finset.prod_pos (fun (i : Fin N) _ => g_pos (i.val+1))

lemma weightedSimplex_eq_preimage (N : ℕ) (T : ℝ) :
    weightedSimplex N T = weightedScale N ⁻¹' standardSimplex N T := by
  ext v
  simp only [weightedSimplex, standardSimplex, Set.mem_preimage, Set.mem_ofPred_eq,
    weightedScale_apply]
  exact and_congr (forall_congr' fun i => (mul_nonneg_iff_of_pos_left (g_pos _)).symm)
    Iff.rfl

lemma volume_weightedSimplex_nonneg (N : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    volume (weightedSimplex N T) =
      ENNReal.ofReal (T^N / ((N.factorial : ℝ) * ∏ i : Fin N, g (i.val+1))) := by
  rw [weightedSimplex_eq_preimage, ← Measure.map_apply
    (weightedScale N).continuous_of_finiteDimensional.measurable
    (measurableSet_standardSimplex N T),
    Real.map_linearMap_volume_pi_eq_smul_volume_pi (weightedScale_det_pos N).ne',
    Measure.smul_apply, smul_eq_mul, volume_standardSimplex N hT,
    weightedScale_det, abs_inv, abs_of_pos (Finset.prod_pos (fun (i : Fin N) _ => g_pos (i.val+1))),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (Finset.prod_nonneg (fun (i : Fin N) _ => (g_pos (i.val+1)).le)))]
  congr 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

lemma volume_weightedSimplex (N : ℕ) (hN : 0 < N) (T : ℝ) :
    volume (weightedSimplex N T) =
      ENNReal.ofReal ((max T 0)^N / ((N.factorial : ℝ) * ∏ i : Fin N, g (i.val+1))) := by
  by_cases hT : 0 ≤ T
  · rw [max_eq_left hT]
    exact volume_weightedSimplex_nonneg N hT
  · have he : weightedSimplex N T = ∅ := by
      ext v
      simp only [weightedSimplex, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hv, hs⟩
      have hn : 0 ≤ ∑ i : Fin N, g (i.val+1) * v i :=
        Finset.sum_nonneg (fun i _ => mul_nonneg (g_pos _).le (hv i))
      linarith
    rw [he, measure_empty, max_eq_right (le_of_not_ge hT), zero_pow hN.ne', zero_div,
      ENNReal.ofReal_zero]

/-- The explicit determinant-one prefix volume formula from the manuscript. -/
theorem volume_prefixRegion_explicit (N : ℕ) (hN : 0 < N)
    (B C₀ : ℝ) (C : Fin N → ℝ) :
    volume (prefixRegion N B C₀ C) =
      ENNReal.ofReal ((max (B-C₀-∑ i : Fin N, g (i.val+1)*C i) 0)^N /
        ((N.factorial : ℝ) * ∏ i : Fin N, g (i.val+1))) := by
  rw [volume_prefixRegion, volume_weightedSimplex N hN]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrefixWeights
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded weights expressing each prefix coordinate in standard-simplex variables. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma prefixSimplexMap_coordinate (N : ℕ) (u : Fin N → ℝ) (i : Fin N) :
    u i/rho^(i.val+1) = ∑ j, prefixWeight N i j*prefixSimplexMap N u j := by
  conv_lhs => rw [prefixLinear_coordinate N u i]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  simp only [prefixWeight, prefixSimplexMap, LinearMap.comp_apply, weightedScale_apply]
  split_ifs
  · field_simp [(g_pos (j.val+1)).ne']
  · simp

lemma sum_suffix_weights (N : ℕ) (i : Fin N) (f : ℕ → ℝ) :
    (∑ j : Fin N, if i ≤ j then f (j.val-i.val) else 0) =
      ∑ k ∈ Finset.range (N-i.val), f k := by
  change (∑ j : Fin N, if i.val ≤ j.val then f (j.val-i.val) else 0) = _
  rw [Fin.sum_univ_eq_sum_range (fun j => if i.val ≤ j then f (j-i.val) else 0)]
  have hs := Finset.sum_range_add (fun j => if i.val ≤ j then f (j-i.val) else 0)
    i.val (N-i.val)
  rw [Nat.add_sub_of_le (Nat.le_of_lt i.isLt)] at hs
  rw [hs]
  have hz : (∑ j ∈ Finset.range i.val, if i.val ≤ j then f (j-i.val) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [ite_eq_right (by have := Finset.mem_range.mp hj; omega)]
  rw [hz, zero_add]
  apply Finset.sum_congr rfl
  intro j _
  simp

lemma prefixWeight_nonneg (N : ℕ) (i j : Fin N) : 0 ≤ prefixWeight N i j := by
  unfold prefixWeight
  split_ifs
  · exact div_nonneg (g_pos _).le (mul_pos (pow_pos rho_pos _) (g_pos _)).le
  · rfl

lemma prefixWeight_error {C : ℝ}
    (hC : ∀ i k : ℕ, |g k/(rho^i*g (i+k))-1| ≤ C*rho^k)
    (N : ℕ) (i j : Fin N) (hij : i ≤ j) :
    |prefixWeight N i j-1| ≤ C*rho^(j.val-i.val) := by
  have hh := hC (i.val+1) (j.val-i.val)
  have he : i.val+1+(j.val-i.val) = j.val+1 := by
    have : i.val ≤ j.val := hij
    omega
  simpa only [he, prefixWeight, ite_eq_left hij] using hh

/-- Uniform first- and second-moment bounds; the error is independent of dimension. -/
theorem prefixWeight_bounds : ∃ M K : ℝ, 1 ≤ M ∧ 0 < K ∧
    ∀ (N : ℕ) (i : Fin N),
      (∀ j, 0 ≤ prefixWeight N i j ∧ prefixWeight N i j ≤ M) ∧
      |(∑ j, prefixWeight N i j)-(N-i.val:ℕ)| ≤ K ∧
      (∑ j, (prefixWeight N i j)^2) ≤ M*((N-i.val:ℕ)+K) := by
  obtain ⟨C,hC,he⟩ := renewal_ratio_error
  let M := C+1
  let K := C/(1-rho)
  have hK : 0 < K := div_pos hC (sub_pos.mpr rho_lt_one)
  refine ⟨M,K,by dsimp [M] <;> linarith,hK,?_⟩
  intro N i
  have hpoint (j : Fin N) : |prefixWeight N i j-(if i ≤ j then 1 else 0)| ≤
      if i ≤ j then C*rho^(j.val-i.val) else 0 := by
    by_cases hij : i ≤ j
    · simpa only [ite_eq_left hij] using prefixWeight_error he N i j hij
    · simp [prefixWeight, hij]
  have hupper (j : Fin N) : prefixWeight N i j ≤ M := by
    by_cases hij : i ≤ j
    · have hh := (abs_le.mp (prefixWeight_error he N i j hij)).2
      have hp := pow_le_one₀ rho_pos.le rho_lt_one.le (n := j.val-i.val)
      dsimp [M]
      nlinarith
    · simp only [prefixWeight, ite_eq_right hij]
      dsimp [M]
      linarith
  have herror : |(∑ j, prefixWeight N i j)-(N-i.val:ℕ)| ≤ K := by
    have hone : (∑ j : Fin N, if i ≤ j then (1:ℝ) else 0) = (N-i.val:ℕ) := by
      rw [sum_suffix_weights N i (fun _ => 1)]
      simp
    rw [← hone, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ j, |prefixWeight N i j-(if i ≤ j then 1 else 0)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin N, if i ≤ j then C*rho^(j.val-i.val) else 0 := Finset.sum_le_sum (fun j _ => hpoint j)
      _ = C*∑ k ∈ Finset.range (N-i.val), rho^k := by rw [sum_suffix_weights N i (fun k => C*rho^k), Finset.mul_sum]
      _ ≤ K := by
        have hg := (hasSum_geometric_of_lt_one rho_pos.le rho_lt_one).summable.sum_le_tsum
          (Finset.range (N-i.val)) (fun k _ => (pow_pos rho_pos k).le)
        rw [tsum_geometric_of_lt_one rho_pos.le rho_lt_one] at hg
        exact mul_le_mul_of_nonneg_left hg hC.le
  refine ⟨fun j => ⟨prefixWeight_nonneg N i j,hupper j⟩,herror,?_⟩
  calc
    _ ≤ M*(∑ j, prefixWeight N i j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      have hn := prefixWeight_nonneg N i j
      have hu := hupper j
      nlinarith
    _ ≤ M*((N-i.val:ℕ)+K) := by
      apply mul_le_mul_of_nonneg_left _ (by dsimp [M] <;> positivity)
      have hh := (abs_le.mp herror).2
      linarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RegionLower
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A terminal tail prime forces lower bounds throughout the actual witness region. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma prefixLinear_terminal_lower {N : ℕ} (u : Fin N → ℝ) (T : ℝ)
    (hu : ∀ i, a (N-i.val)*T ≤ prefixLinear N u i) :
    ∀ i, g (N-i.val)*T ≤ u i := by
  let v : ℕ → ℝ := fun j => if hj : j < N then u ⟨j, hj⟩ else T
  have hv (j : ℕ) (hj : j < N) : v j = u ⟨j, hj⟩ := by simp [v, hj]
  have hvN : v N = T := by simp [v]
  have hslack (i : ℕ) (hi : i < N) :
      (∑ j ∈ Finset.Icc (i+1) N, a (j-i)*v j) ≤ v i := by
    let i' : Fin N := ⟨i, hi⟩
    have hh := hu i'
    rw [prefixLinear_apply] at hh
    have hsum : (∑ j : Fin N, if i' < j then a (j.val-i'.val)*u j else 0) =
        ∑ j ∈ Finset.Icc (i+1) (N-1), a (j-i)*v j := by
      have heq : (∑ j : Fin N, if i' < j then a (j.val-i'.val)*u j else 0) =
          ∑ j : Fin N, if i < j.val then a (j.val-i)*v j.val else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        change (if i < j.val then a (j.val-i)*u j else 0) = _
        rw [hv j.val j.isLt]
      rw [heq, Fin.sum_univ_eq_sum_range
        (fun k => if i < k then a (k-i)*v k else 0), ← Finset.sum_filter]
      have he : (Finset.range N).filter (fun j => i < j) = Finset.Icc (i+1) (N-1) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
        omega
      rw [he]
    rw [hsum] at hh
    have hsplit : (∑ j ∈ Finset.Icc (i+1) N, a (j-i)*v j) =
        (∑ j ∈ Finset.Icc (i+1) (N-1), a (j-i)*v j)+a (N-i)*T := by
      have hN : N-1+1=N := by omega
      rw [← hN, Finset.sum_Icc_succ_top (by omega : i+1 ≤ N-1+1), hN, hvN]
    rw [hsplit, hv i hi]
    change a (N-i)*T ≤ u ⟨i, hi⟩ - _ at hh
    linarith
  intro i
  simpa only [hvN, hv i.val i.isLt] using
    (renewal_prefix_lower N v hslack (Nat.le_of_lt i.isLt))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SimplexShell
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit slack-shell bounds for the prefix simplexes. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

lemma measurableSet_prefixRegion (N : ℕ) (B C₀ : ℝ) (C : Fin N → ℝ) :
    MeasurableSet (prefixRegion N B C₀ C) := by
  rw [prefixRegion_eq_simplex_preimage]
  exact (prefixAffine_preserves_volume _ _).measurable (measurableSet_weightedSimplex _ _)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordSimplexEmbedding
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relating our terminal coefficient to Ford's stronger terminal inequality. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

lemma a_one_lt_one : a 1 < 1 := by
  norm_num [a]
  linarith [Real.log_two_lt_d9]

lemma prefixRegion_nonneg {N : ℕ} {B : ℝ} {u : Fin N → ℝ}
    (hu : u ∈ prefixRegion N B 0 0) : ∀ i, 0 ≤ u i := by
  have hh := prefixLinear_terminal_lower u 0 (fun i => by simpa using hu.1 i)
  simpa using hh

lemma shrinkLast_apply (N : ℕ) (u : Fin (N+2) → ℝ) (i : Fin (N+2)) :
    shrinkLast N u i = (if i = Fin.last (N+1) then a 1 else 1)*u i := by
  simp [shrinkLast, Matrix.toLin'_apply, Matrix.mulVec_diagonal]

lemma shrinkLast_det (N : ℕ) : LinearMap.det (shrinkLast N) = a 1 := by
  rw [shrinkLast, LinearMap.det_toLin', Matrix.det_diagonal]
  simp

lemma shrinkLast_le {N : ℕ} {u : Fin (N+2) → ℝ} (hu : ∀ i, 0 ≤ u i) :
    ∀ i, shrinkLast N u i ≤ u i := by
  intro i
  rw [shrinkLast_apply]
  split_ifs
  · exact mul_le_of_le_one_left (hu i) a_one_lt_one.le
  · simp

/-- Scaling only the last coordinate by `a₁` places our exact simplex inside
Ford's `S*`. All earlier coordinates, hence their band events, are preserved. -/
theorem shrinkLast_mem_fordSimplex {N : ℕ} {B : ℝ} {u : Fin (N+2) → ℝ}
    (hu : u ∈ prefixRegion (N+2) B 0 0) : shrinkLast N u ∈ fordSimplex N B := by
  have hnonneg := prefixRegion_nonneg hu
  have hle := shrinkLast_le hnonneg
  have ha : 0 < a 1 := a_pos le_rfl
  constructor
  · constructor
    · intro i
      by_cases hi : i = Fin.last (N+1)
      · subst i
        rw [prefixLinear_apply]
        have hs : (∑ j : Fin (N+2), if Fin.last (N+1) < j then
            a (j.val-(Fin.last (N+1)).val)*shrinkLast N u j else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro j _
          exact ite_eq_right (not_lt_of_ge (Fin.le_last j))
        rw [hs, sub_zero, shrinkLast_apply]
        simp only [ite_true, if_true]
        exact mul_nonneg ha.le (hnonneg _)
      · have hh := hu.1 i
        rw [prefixLinear_apply] at hh ⊢
        rw [shrinkLast_apply, ite_eq_right hi, one_mul]
        apply le_trans hh
        apply sub_le_sub_left
        apply Finset.sum_le_sum
        intro j _
        split_ifs with hij
        · exact mul_le_mul_of_nonneg_left (hle j) (a_pos (by have := hij; simp only [Fin.lt_def] at this; omega)).le
        · exact le_rfl
    · have hh := hu.2
      simp only [sub_zero] at hh ⊢
      apply le_trans _ hh
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hle i) (a_pos (by omega)).le
  · have hh := hu.1 ⟨N, by omega⟩
    rw [prefixLinear_apply] at hh
    have hs : (∑ j : Fin (N+2), if (⟨N, by omega⟩ : Fin (N+2)) < j then
        a (j.val-N)*u j else 0) = a 1*u (Fin.last (N+1)) := by
      rw [Finset.sum_eq_single (Fin.last (N+1))]
      · have hlt : (⟨N, by omega⟩ : Fin (N+2)) < Fin.last (N+1) := by
          change N < N+1
          omega
        simp only [hlt, ite_true, if_true, Fin.val_last, Nat.add_sub_cancel_left]
      · intro j _ hj
        rw [ite_eq_right]
        simp only [Fin.lt_def]
        have hval : j.val ≠ N+1 := by
          intro he
          apply hj
          exact Fin.ext he
        have := j.isLt
        omega
      · simp
    rw [hs] at hh
    change shrinkLast N u (Fin.last (N+1)) ≤ shrinkLast N u ⟨N, by omega⟩
    rw [shrinkLast_apply, shrinkLast_apply]
    simp only [ite_true, if_true]
    rw [ite_eq_right (by intro h; have he := congrArg Fin.val h; simp at he), one_mul]
    change 0 ≤ u ⟨N, by omega⟩-a 1*u (Fin.last (N+1)) at hh
    linarith

/-- A measurable event in Ford's simplex bounds its preimage in our simplex,
with only the fixed Jacobian factor `1/a₁`. -/
theorem shrinkLast_volume_bound {N : ℕ} {B : ℝ}
    (S T : Set (Fin (N+2) → ℝ)) (hT : MeasurableSet T)
    (hS : ∀ u ∈ S, u ∈ prefixRegion (N+2) B 0 0)
    (hST : ∀ u ∈ S, shrinkLast N u ∈ T) :
    volume S ≤ ENNReal.ofReal ((a 1)⁻¹)*volume (fordSimplex N B ∩ T) := by
  have ha := a_pos (j := 1) le_rfl
  have hford : MeasurableSet (fordSimplex N B) := by
    change MeasurableSet (prefixRegion (N+2) B 0 0 ∩
      {u : Fin (N+2) → ℝ | u (Fin.last (N+1)) ≤ u ⟨N, by omega⟩})
    exact (measurableSet_prefixRegion _ _ _ _).inter
      (measurableSet_le (measurable_pi_apply (Fin.last (N+1)))
        (measurable_pi_apply (⟨N, by omega⟩ : Fin (N+2))))
  have hincl : S ⊆ (shrinkLast N) ⁻¹' (fordSimplex N B ∩ T) := by
    intro u hu
    exact ⟨shrinkLast_mem_fordSimplex (hS u hu), hST u hu⟩
  apply (measure_mono hincl).trans_eq
  rw [← Measure.map_apply (shrinkLast N).continuous_of_finiteDimensional.measurable (hford.inter hT),
    Real.map_linearMap_volume_pi_eq_smul_volume_pi (by rw [shrinkLast_det]; exact ha.ne'),
    shrinkLast_det, Measure.smul_apply, smul_eq_mul, abs_of_pos (inv_pos.mpr ha)]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PublishedConcentration
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The fixed-deviation consequence of Ford, *The distribution of totients*,
arXiv:1104.3264v2 (2013), Lemma 6.1, (6.6)--(6.8), pp. 30--31.
We use deviation 1/40 only. For the lower tail take
`theta = (1/40)/(1-1/40)` in (6.6); for the upper tail take
`theta = -(1/40)/(1+1/40)` in (6.7) or (6.8), splitting at
`-i*lambda_i/L`. The uniform bounds (6.4) give positive absolute
constants in `exp (-c*(L-i))`. Letting the terminal cutoff decrease to
zero and rescaling the simplex gives precisely the input below.
The transfer from Ford's terminal coefficient 1 to our coefficient a_1
is proved here using `shrinkLast`, rather than assumed in this input.
-/

noncomputable section
open MeasureTheory

namespace TotientAsymptotic

lemma prefixRegion_volume_ne_top {N : ℕ} (hN : 0 < N) (B : ℝ) :
    volume (prefixRegion N B 0 0) ≠ ⊤ := by
  rw [volume_prefixRegion_explicit _ hN]
  exact ENNReal.ofReal_ne_top

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrefixSimplexMap
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transporting the coordinate events through the exact simplex map. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

lemma prefixSimplexMap_det (N : ℕ) :
    LinearMap.det (prefixSimplexMap N) = ∏ i : Fin N, g (i.val+1) := by
  rw [prefixSimplexMap, LinearMap.det_comp, prefixLinear_det, mul_one, weightedScale_det]

lemma prefixSimplexMap_det_pos (N : ℕ) : 0 < LinearMap.det (prefixSimplexMap N) := by
  rw [prefixSimplexMap_det]
  exact Finset.prod_pos (fun i _ => g_pos _)

lemma prefixSimplexMap_preimage (N : ℕ) (B : ℝ) :
    prefixRegion N B 0 0 = prefixSimplexMap N ⁻¹' standardSimplex N B := by
  rw [prefixRegion_eq_simplex_preimage]
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, sub_zero,
    weightedSimplex_eq_preimage]
  rfl

lemma volume_prefixSimplexMap_preimage (N : ℕ) (T : Set (Fin N → ℝ))
    (hT : MeasurableSet T) :
    volume (prefixSimplexMap N ⁻¹' T) =
      ENNReal.ofReal ((LinearMap.det (prefixSimplexMap N))⁻¹)*volume T := by
  rw [← Measure.map_apply (prefixSimplexMap N).continuous_of_finiteDimensional.measurable hT,
    Real.map_linearMap_volume_pi_eq_smul_volume_pi (prefixSimplexMap_det_pos N).ne',
    Measure.smul_apply, smul_eq_mul, abs_of_pos (inv_pos.mpr (prefixSimplexMap_det_pos N))]

lemma prefixSimplexMap_ford_ratio (N : ℕ) (B : ℝ) (u : Fin (N+2) → ℝ)
    (i : Fin (N+2)) :
    (∑ j, prefixWeight (N+2) i j*prefixSimplexMap (N+2) u j)/
        (B*(((N+2-i.val:ℕ):ℝ)-1)/(N+2:ℝ)) = u i/fordSimplexCenter N B i := by
  rw [← prefixSimplexMap_coordinate]
  have hi : i.val ≤ N+2 := by omega
  have hden : fordSimplexCenter N B i = rho^(i.val+1)*
      (B*(((N+2-i.val:ℕ):ℝ)-1)/(N+2:ℝ)) := by
    unfold fordSimplexCenter
    rw [Nat.cast_sub hi]
    push_cast
    field_simp
    ring
  rw [hden, div_div]

lemma prefixSimplexMap_bad_preimage (N : ℕ) (B : ℝ) (i : Fin (N+2)) :
    prefixRegion (N+2) B 0 0 ∩ fordCoordinateBad N B i =
      prefixSimplexMap (N+2) ⁻¹'
        (standardSimplex (N+2) B ∩
          {v | (1/40:ℝ) < |(∑ j, prefixWeight (N+2) i j*v j)/
            (B*(((N+2-i.val:ℕ):ℝ)-1)/(N+2:ℝ))-1|}) := by
  rw [prefixSimplexMap_preimage]
  ext u
  simp only [Set.mem_inter_iff, Set.mem_preimage, fordCoordinateBad, Set.mem_ofPred_eq,
    prefixSimplexMap_ford_ratio]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SimplexTilt
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Diagonal changes of variables bounding a linear cap of the standard simplex. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

lemma simplexDiagonal_apply (N : ℕ) (w v : Fin N → ℝ) (i : Fin N) :
    simplexDiagonal N w v i = w i*v i := by
  simp [simplexDiagonal, Matrix.toLin'_apply, Matrix.mulVec_diagonal]

lemma simplexDiagonal_det (N : ℕ) (w : Fin N → ℝ) :
    LinearMap.det (simplexDiagonal N w) = ∏ i, w i := by
  rw [simplexDiagonal, LinearMap.det_toLin', Matrix.det_diagonal]

lemma positiveSimplex_eq_preimage (N : ℕ) (w : Fin N → ℝ)
    (hw : ∀ i, 0 < w i) (T : ℝ) :
    positiveSimplex N w T = simplexDiagonal N w ⁻¹' standardSimplex N T := by
  ext v
  simp only [positiveSimplex, standardSimplex, Set.mem_preimage, Set.mem_ofPred_eq,
    simplexDiagonal_apply]
  exact and_congr (forall_congr' fun i => (mul_nonneg_iff_of_pos_left (hw i)).symm) Iff.rfl

lemma volume_positiveSimplex (N : ℕ) (w : Fin N → ℝ)
    (hw : ∀ i, 0 < w i) {T : ℝ} (hT : 0 ≤ T) :
    volume (positiveSimplex N w T) =
      ENNReal.ofReal (T^N / ((N.factorial : ℝ)*∏ i, w i)) := by
  have hp : 0 < ∏ i, w i := Finset.prod_pos (fun i _ => hw i)
  rw [positiveSimplex_eq_preimage N w hw,
    ← Measure.map_apply (simplexDiagonal N w).continuous_of_finiteDimensional.measurable
      (measurableSet_standardSimplex N T),
    Real.map_linearMap_volume_pi_eq_smul_volume_pi (by rw [simplexDiagonal_det]; exact hp.ne'),
    simplexDiagonal_det, Measure.smul_apply, smul_eq_mul, volume_standardSimplex N hT,
    abs_inv, abs_of_pos hp, ← ENNReal.ofReal_mul (inv_nonneg.mpr hp.le)]
  congr 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

lemma simplex_lower_cap_subset (N : ℕ) (B t s : ℝ) (w : Fin N → ℝ)
    (hs : 0 ≤ s) :
    standardSimplex N B ∩ {v | (∑ i, w i*v i) ≤ t} ⊆
      positiveSimplex N (fun i => 1+s*w i) (B+s*t) := by
  rintro v ⟨⟨hv,hB⟩,ht⟩
  refine ⟨hv,?_⟩
  calc
    _ = (∑ i, v i)+s*(∑ i, w i*v i) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ B+s*t := add_le_add hB (mul_le_mul_of_nonneg_left ht hs)

/-- A finite-dimensional Chernoff bound, before logarithmic estimation. -/
theorem volume_simplex_lower_cap_le (N : ℕ) (B t s : ℝ) (w : Fin N → ℝ)
    (hs : 0 ≤ s) (hw : ∀ i, 0 < 1+s*w i) (hT : 0 ≤ B+s*t) :
    (volume (standardSimplex N B ∩ {v | (∑ i, w i*v i) ≤ t})).toReal ≤
      (B+s*t)^N / ((N.factorial : ℝ)*∏ i, (1+s*w i)) := by
  have hb : volume (standardSimplex N B ∩ {v | (∑ i, w i*v i) ≤ t}) ≤
      volume (positiveSimplex N (fun i => 1+s*w i) (B+s*t)) :=
    measure_mono (simplex_lower_cap_subset N B t s w hs)
  rw [volume_positiveSimplex N _ hw hT] at hb
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [ENNReal.toReal_ofReal (div_nonneg (pow_nonneg hT _)
    (mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun i _ => (hw i).le))))] at hh
  exact hh

lemma simplex_upper_cap_eq_lower (N : ℕ) (w : Fin N → ℝ) (t : ℝ) :
    {v : Fin N → ℝ | t ≤ ∑ i, w i*v i} =
      {v | (∑ i, (-w i)*v i) ≤ -t} := by
  ext v
  simp only [Set.mem_ofPred_eq, neg_mul, Finset.sum_neg_distrib, neg_le_neg_iff]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SimplexExponential
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exponential estimates for linear caps, using only a diagonal volume change. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

lemma log_one_add_quadratic_lower {x : ℝ} (hx : -(1/2 : ℝ) ≤ x) :
    x-2*x^2 ≤ Real.log (1+x) := by
  have hp : 0 < 1+x := by linarith
  have hl := Real.one_sub_inv_le_log_of_pos hp
  apply le_trans _ hl
  have hm : 0 ≤ x^2*(1+2*x) := mul_nonneg (sq_nonneg x) (by linarith)
  have hid : 1-(1+x)⁻¹ = x/(1+x) := by field_simp <;> ring
  rw [hid]
  exact (le_div_iff₀ hp).mpr (by nlinarith)

lemma tilted_product_lower (N : ℕ) (w : Fin N → ℝ) (s : ℝ)
    (hw : ∀ i, -(1/2 : ℝ) ≤ s*w i) :
    Real.exp (s*(∑ i, w i)-2*s^2*(∑ i, (w i)^2)) ≤
      ∏ i, (1+s*w i) := by
  have he : s*(∑ i, w i)-2*s^2*(∑ i, (w i)^2) =
      ∑ i, (s*w i-2*(s*w i)^2) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, Real.exp_sum]
  apply Finset.prod_le_prod (fun i _ => (Real.exp_pos _).le)
  intro i _
  have hp : 0 < 1+s*w i := by have := hw i; linarith
  exact (Real.exp_le_exp.mpr (log_one_add_quadratic_lower (hw i))).trans_eq (Real.exp_log hp)

lemma simplex_tilt_power (N : ℕ) {B : ℝ} (hB : 0 < B) (s t : ℝ)
    (hT : 0 ≤ B+s*t) :
    (B+s*t)^N ≤ B^N*Real.exp ((N:ℝ)*(s*t/B)) := by
  have hbase : B+s*t ≤ B*Real.exp (s*t/B) := by
    have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (s*t/B)) hB.le
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    field_simp [hB.ne']
    ring
  calc
    _ ≤ (B*Real.exp (s*t/B))^N := pow_le_pow_left₀ hT hbase N
    _ = _ := by rw [mul_pow, Real.exp_nat_mul]

/-- An explicit Chernoff estimate for the lower cap of a uniform simplex. -/
theorem volume_simplex_lower_cap_exp (N : ℕ) {B : ℝ} (hB : 0 < B)
    (t s : ℝ) (w : Fin N → ℝ) (hs : 0 ≤ s)
    (hw : ∀ i, -(1/2 : ℝ) ≤ s*w i) (hT : 0 ≤ B+s*t) :
    (volume (standardSimplex N B ∩ {v | (∑ i, w i*v i) ≤ t})).toReal ≤
      Real.exp ((N:ℝ)*(s*t/B)-s*(∑ i, w i)+2*s^2*(∑ i, (w i)^2))*
        (volume (standardSimplex N B)).toReal := by
  have hp : ∀ i, 0 < 1+s*w i := fun i => by have := hw i; linarith
  have hprod := tilted_product_lower N w s hw
  have hpow := simplex_tilt_power N hB s t hT
  have hfac : 0 < (N.factorial:ℝ) := by positivity
  have hden : 0 < (N.factorial:ℝ)*Real.exp (s*(∑ i,w i)-2*s^2*(∑ i,(w i)^2)) := by positivity
  apply (volume_simplex_lower_cap_le N B t s w hs hp hT).trans
  calc
    _ ≤ (B^N*Real.exp ((N:ℝ)*(s*t/B)))/
        ((N.factorial:ℝ)*Real.exp (s*(∑ i,w i)-2*s^2*(∑ i,(w i)^2))) := by
      apply div_le_div₀ (by positivity) hpow hden
      exact mul_le_mul_of_nonneg_left hprod hfac.le
    _ = _ := by
      rw [volume_standardSimplex N hB.le, ENNReal.toReal_ofReal (by positivity)]
      conv_rhs => rw [show (N:ℝ)*(s*t/B)-s*(∑ i,w i)+2*s^2*(∑ i,(w i)^2) =
        (N:ℝ)*(s*t/B)-(s*(∑ i,w i)-2*s^2*(∑ i,(w i)^2)) by ring, Real.exp_sub]
      ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SimplexFixedCaps
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-deviation cap estimates with constants uniform in the dimension. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

lemma simplex_fixed_caps (M K : ℝ) (hM : 1 ≤ M) (hK : 0 ≤ K)
    (N m : ℕ) (hm : 2 ≤ m) (hmN : m ≤ N) (B : ℝ) (hB : 0 < B)
    (w : Fin N → ℝ) (hw : ∀ j, 0 ≤ w j ∧ w j ≤ M)
    (hS : |(∑ j,w j)-(m:ℝ)| ≤ K) (hQ : (∑ j,(w j)^2) ≤ M*((m:ℝ)+K)) :
    let t := B*((m:ℝ)-1)/(N:ℝ)
    let s := concentrationTilt M
    let E := Real.exp (3*s*(K+1)-(s/100)*((m:ℝ)-1))*(volume (standardSimplex N B)).toReal
    (volume (standardSimplex N B ∩ {v | (∑ j,w j*v j) ≤ (39/40)*t})).toReal ≤ E ∧
    (volume (standardSimplex N B ∩ {v | (41/40)*t ≤ ∑ j,w j*v j})).toReal ≤ E := by
  dsimp only
  let t := B*((m:ℝ)-1)/(N:ℝ)
  let s := concentrationTilt M
  have hs : 0 < s := concentrationTilt_pos hM
  have hsle : s ≤ 1/320 := concentrationTilt_le hM
  have hsm : s*M = 1/320 := concentrationTilt_mul hM
  have hn : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hm' : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hmn : (m:ℝ) ≤ N := by exact_mod_cast hmN
  have ht : 0 < t := div_pos (mul_pos hB (by linarith)) hn
  have htB : t ≤ B := by
    apply (div_le_iff₀ hn).mpr
    nlinarith
  have hl : 0 ≤ B+s*((39/40)*t) := by positivity
  have hu : 0 ≤ B+s*(-((41/40)*t)) := by
    have hh : s*((41/40)*t) ≤ (1/320)*((41/40)*B) :=
      mul_le_mul hsle (mul_le_mul_of_nonneg_left htB (by norm_num)) (by positivity) (by norm_num)
    nlinarith
  have hwl (j : Fin N) : -(1/2:ℝ) ≤ s*w j := by
    have := mul_nonneg hs.le (hw j).1
    linarith
  have hwu (j : Fin N) : -(1/2:ℝ) ≤ s*(-w j) := by
    have hh := mul_le_mul_of_nonneg_left (hw j).2 hs.le
    rw [hsm] at hh
    nlinarith
  have he := concentration_exponents hM hK (show (1:ℝ) ≤ m by linarith) hS hQ
  have hel : (N:ℝ)*(s*((39/40)*t)/B)-s*(∑ j,w j)+2*s^2*(∑ j,(w j)^2) ≤
      3*s*(K+1)-(s/100)*((m:ℝ)-1) := by
    have hid : (N:ℝ)*(s*((39/40)*t)/B) = s*(39/40)*((m:ℝ)-1) := by
      dsimp [t]
      field_simp
    rw [hid]
    exact he.1
  have heu : (N:ℝ)*(s*(-((41/40)*t))/B)-s*(∑ j,(-w j))+2*s^2*(∑ j,(-w j)^2) ≤
      3*s*(K+1)-(s/100)*((m:ℝ)-1) := by
    have hid : (N:ℝ)*(s*(-((41/40)*t))/B) = -s*(41/40)*((m:ℝ)-1) := by
      dsimp [t]
      field_simp
    rw [hid]
    simp only [Finset.sum_neg_distrib, mul_neg, sub_neg_eq_add, neg_sq]
    exact he.2
  constructor
  · exact (volume_simplex_lower_cap_exp N hB ((39/40)*t) s w hs.le hwl hl).trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hel) ENNReal.toReal_nonneg)
  · rw [simplex_upper_cap_eq_lower]
    exact (volume_simplex_lower_cap_exp N hB (-((41/40)*t)) s (fun j => -w j) hs.le hwu hu).trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr heu) ENNReal.toReal_nonneg)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SimplexConcentration
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform two-sided concentration of bounded linear forms on a simplex. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

lemma volume_simplex_fixed_deviation (M K : ℝ) (hM : 1 ≤ M) (hK : 0 ≤ K)
    (N m : ℕ) (hm : 2 ≤ m) (hmN : m ≤ N) (B : ℝ) (hB : 0 < B)
    (w : Fin N → ℝ) (hw : ∀ j, 0 ≤ w j ∧ w j ≤ M)
    (hS : |(∑ j,w j)-(m:ℝ)| ≤ K) (hQ : (∑ j,(w j)^2) ≤ M*((m:ℝ)+K)) :
    (volume (standardSimplex N B ∩
      {v | (1/40:ℝ) < |(∑ j,w j*v j)/(B*((m:ℝ)-1)/(N:ℝ))-1|})).toReal ≤
      2*Real.exp (3*concentrationTilt M*(K+1))*
        Real.exp (-(concentrationTilt M/100)*(m-1:ℕ))*
          (volume (standardSimplex N B)).toReal := by
  let t := B*((m:ℝ)-1)/(N:ℝ)
  let S := standardSimplex N B
  let L := S ∩ {v | (∑ j,w j*v j) ≤ (39/40)*t}
  let U := S ∩ {v | (41/40)*t ≤ ∑ j,w j*v j}
  have hn : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hm' : (2:ℝ) ≤ m := by exact_mod_cast hm
  have ht : 0 < t := div_pos (mul_pos hB (by linarith)) hn
  have hsub : S ∩ {v | (1/40:ℝ) < |(∑ j,w j*v j)/t-1|} ⊆ L ∪ U := by
    rintro v ⟨hv,hbad⟩
    by_cases hl : (∑ j,w j*v j) ≤ (39/40)*t
    · exact Or.inl ⟨hv,hl⟩
    · refine Or.inr ⟨hv,?_⟩
      by_contra hu
      have hlo : 39/40 < (∑ j,w j*v j)/t := (lt_div_iff₀ ht).mpr (lt_of_not_ge hl)
      have hup : (∑ j,w j*v j)/t < 41/40 := (div_lt_iff₀ ht).mpr (lt_of_not_ge hu)
      have habs : |(∑ j,w j*v j)/t-1| ≤ (1/40:ℝ) := abs_le.mpr ⟨by linarith,by linarith⟩
      exact (not_lt_of_ge habs) hbad
  have hfin : volume S ≠ ⊤ := by
    dsimp [S]
    rw [volume_standardSimplex N hB.le]
    exact ENNReal.ofReal_ne_top
  have hL : volume L ≠ ⊤ := ne_top_of_le_ne_top hfin (measure_mono Set.inter_subset_left)
  have hU : volume U ≠ ⊤ := ne_top_of_le_ne_top hfin (measure_mono Set.inter_subset_left)
  have hh : volume (S ∩ {v | (1/40:ℝ) < |(∑ j,w j*v j)/t-1|}) ≤ volume L+volume U :=
    (measure_mono hsub).trans (measure_union_le _ _)
  have hr := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hL,hU⟩) hh
  rw [ENNReal.toReal_add hL hU] at hr
  have hcaps := simplex_fixed_caps M K hM hK N m hm hmN B hB w hw hS hQ
  apply hr.trans
  calc
    _ ≤ 2*(Real.exp (3*concentrationTilt M*(K+1)-
        (concentrationTilt M/100)*((m:ℝ)-1))*(volume S).toReal) := by
      have hl : (volume L).toReal ≤ Real.exp (3*concentrationTilt M*(K+1)-
        (concentrationTilt M/100)*((m:ℝ)-1))*(volume S).toReal := hcaps.1
      have hu : (volume U).toReal ≤ Real.exp (3*concentrationTilt M*(K+1)-
        (concentrationTilt M/100)*((m:ℝ)-1))*(volume S).toReal := hcaps.2
      linarith only [hl,hu]
    _ = _ := by
      dsimp only [S]
      rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
      rw [Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg]
      ring_nf

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrefixConcentration
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unconditional coordinate concentration for the exact prefix simplex. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

lemma prefixSimplexMap_transfer (N : ℕ) (B R : ℝ) (T : Set (Fin N → ℝ))
    (hT : MeasurableSet T)
    (hbound : (volume T).toReal ≤ R*(volume (standardSimplex N B)).toReal) :
    (volume (prefixSimplexMap N ⁻¹' T)).toReal ≤
      R*(volume (prefixRegion N B 0 0)).toReal := by
  rw [volume_prefixSimplexMap_preimage N T hT, ENNReal.toReal_mul,
    prefixSimplexMap_preimage, volume_prefixSimplexMap_preimage N _
      (measurableSet_standardSimplex N B), ENNReal.toReal_mul]
  exact (mul_le_mul_of_nonneg_left hbound ENNReal.toReal_nonneg).trans_eq (by ring)

theorem prefix_coordinate_concentration_unconditional :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ N : ℕ, ∀ B : ℝ, 0 < B → ∀ i : Fin (N+2), i.val < N →
      (volume (prefixRegion (N+2) B 0 0 ∩ fordCoordinateBad N B i)).toReal ≤
        C*Real.exp (-c*(N+2-(i.val+1) : ℕ))*(volume (prefixRegion (N+2) B 0 0)).toReal := by
  obtain ⟨M,K,hM,hK,hweights⟩ := prefixWeight_bounds
  let s := concentrationTilt M
  refine ⟨2*Real.exp (3*s*(K+1)),s/100,by positivity,
    div_pos (concentrationTilt_pos hM) (by norm_num),?_⟩
  intro N B hB i hi
  obtain ⟨hw,hS,hQ⟩ := hweights (N+2) i
  have hm : 2 ≤ N+2-i.val := by omega
  have hmN : N+2-i.val ≤ N+2 := Nat.sub_le _ _
  have hc := volume_simplex_fixed_deviation M K hM hK.le (N+2) (N+2-i.val) hm hmN B hB
    (prefixWeight (N+2) i) hw hS hQ
  have he : N+2-i.val-1 = N+2-(i.val+1) := by omega
  rw [he] at hc
  rw [prefixSimplexMap_bad_preimage]
  apply prefixSimplexMap_transfer
  · apply (measurableSet_standardSimplex _ _).inter
    apply measurableSet_lt measurable_const
    fun_prop
  · simpa only [Nat.cast_add,Nat.cast_ofNat] using hc

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ConcentrationInput
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Discharging Ford's fixed-deviation coordinate input by elementary simplex caps. -/
noncomputable section
open MeasureTheory
namespace TotientAsymptotic

/-- The only distinction between the exact triangular simplex and Ford's
terminal inequality costs the fixed determinant factor `1/a₁`. -/
theorem fordCoordinateConcentrationInput_oai : FordCoordinateConcentrationInput := by
  obtain ⟨C,c,hC,hc,hprefix⟩ := prefix_coordinate_concentration_unconditional
  have ha : 0 < a 1 := a_pos le_rfl
  refine ⟨C/a 1,c,0,div_pos hC ha,hc,?_⟩
  intro N _ B hB i hi
  have hfin := prefixRegion_volume_ne_top (by omega : 0 < N+2) B
  have hfordfin : volume (fordSimplex N B) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (measure_mono (fun _ hu => hu.1))
  have hbadfin : volume (prefixRegion (N+2) B 0 0 ∩ fordCoordinateBad N B i) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (measure_mono Set.inter_subset_left)
  have hmono : (volume (fordSimplex N B ∩ fordCoordinateBad N B i)).toReal ≤
      (volume (prefixRegion (N+2) B 0 0 ∩ fordCoordinateBad N B i)).toReal :=
    ENNReal.toReal_mono hbadfin (measure_mono (fun _ hu => ⟨hu.1.1,hu.2⟩))
  have hvol := shrinkLast_volume_bound (prefixRegion (N+2) B 0 0) Set.univ
    MeasurableSet.univ (fun _ hu => hu) (fun _ _ => Set.mem_univ _)
  simp only [Set.inter_univ] at hvol
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfordfin) hvol
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (inv_pos.mpr ha).le] at hreal
  calc
    _ ≤ (volume (prefixRegion (N+2) B 0 0 ∩ fordCoordinateBad N B i)).toReal := hmono
    _ ≤ C*Real.exp (-c*(N+2-(i.val+1):ℕ))*(volume (prefixRegion (N+2) B 0 0)).toReal :=
      hprefix N B hB i hi
    _ ≤ C*Real.exp (-c*(N+2-(i.val+1):ℕ))*((a 1)⁻¹*(volume (fordSimplex N B)).toReal) :=
      mul_le_mul_of_nonneg_left hreal (by positivity)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

theorem solution : type_of% @OAI.TotientAsymptotic.fordCoordinateConcentrationInput_oai := @OAI.TotientAsymptotic.fordCoordinateConcentrationInput_oai
