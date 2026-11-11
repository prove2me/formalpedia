-- Prove2me | solution 1 for OAI.TotientAsymptotic.ford_structure_value_count
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:37:49.401604+00:00
-- url     : https://prove2.me/submissions/da3aa207-4530-4eee-87a9-72eb745eab5a

import Batteries.Tactic.Lemma
import Mathlib
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Squarefree
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.Bound
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Order.Compact
import Definitions.Def_TotientAsymptotic
import Definitions.Def_OAIQ233A000
import Theorems.Thm_OAI_TotientAsymptotic_failed_row_count_bound
import Theorems.Thm_OAI_TotientAsymptotic_real_coordinate_deviation
import Theorems.Thm_OAI_TotientAsymptotic_small_head_real_gaussian
import Theorems.Thm_OAI_TotientAsymptotic_small_terminal_row_count

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

lemma alpha_pos (s : ℝ) : 0 < alpha s := mul_pos lam_pos (Real.exp_pos _)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_Phase
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cofinal logarithmic phases and convergence of the coefficient approximants. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma self_sub_log_tendsto :
    Tendsto (fun t : ℝ => t - Real.log t) atTop atTop := by
  have hlog : Tendsto (fun t : ℝ => Real.log t / t) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hone : Tendsto (fun t : ℝ => 1 - Real.log t / t) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hlog
  have hmul : Tendsto (fun t : ℝ => t * (1-Real.log t / t)) atTop atTop :=
    Filter.Tendsto.atTop_mul_pos zero_lt_one tendsto_id hone
  apply hmul.congr'
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
  field_simp

lemma psi_tendsto : Tendsto psi atTop atTop := by
  exact (self_sub_log_tendsto.comp Real.tendsto_log_atTop).atTop_div_const lam_pos



lemma theta_eventually_mem : ∀ᶠ x : ℝ in atTop, theta x ∈ Set.Ico (0 : ℝ) 1 := by
  have hp : Tendsto (fun x => psi (B x)) atTop atTop :=
    psi_tendsto.comp (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
  filter_upwards [hp.eventually (eventually_ge_atTop (0 : ℝ))] with x hx
  constructor
  · exact sub_nonneg.mpr (Nat.floor_le hx)
  · have h := Nat.lt_floor_add_one (psi (B x))
    change psi (B x) - (⌊psi (B x)⌋₊ : ℕ) < 1
    linarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BandComparison
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The comparison of the exact Ford band centers with the phase-dependent
centers in the manuscript, equation `alpha-comparison`.  The ratio is
independent of the retained prime index, so its convergence gives a
uniform comparison over all indices below `m`.
-/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma rho_pow_eq_exp (j : ℕ) : rho^j = Real.exp (-lam * j) := by
  have hlog : Real.log rho = -lam := by
    simp only [lam, one_div, Real.log_inv, neg_neg]
  rw [mul_comm, ← hlog, Real.exp_nat_mul, Real.exp_log rho_pos]

lemma alpha_theta_eq {x : ℝ} (hB : 1 < B x) :
    alpha (theta x) = lam * (B x / Real.log (B x)) * rho^(m x) := by
  have hlog : 0 < Real.log (B x) := Real.log_pos hB
  have he : lam * theta x =
      (Real.log (B x) - Real.log (Real.log (B x))) - lam * m x := by
    unfold theta psi
    field_simp [lam_pos.ne']
  rw [alpha, he, Real.exp_sub, Real.exp_sub,
    Real.exp_log (zero_lt_one.trans hB), Real.exp_log hlog, rho_pow_eq_exp]
  rw [neg_mul, Real.exp_neg]
  ring

lemma B_tendsto : Tendsto B atTop atTop :=
  Real.tendsto_log_atTop.comp Real.tendsto_log_atTop

lemma m_tendsto : Tendsto m atTop atTop :=
  tendsto_nat_floor_atTop.comp (psi_tendsto.comp B_tendsto)

lemma bandCenterRatio_tendsto : Tendsto bandCenterRatio atTop (nhds 1) := by
  have hlogB : Tendsto (fun x => Real.log (B x)) atTop atTop :=
    Real.tendsto_log_atTop.comp B_tendsto
  have hsmall : Tendsto (fun x => Real.log (Real.log (B x)) / Real.log (B x))
      atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hlogB
  have hpsi : Tendsto (fun x => psi (B x) / Real.log (B x))
      atTop (nhds (1 / lam)) := by
    have hh : Tendsto
        (fun x => (1 - Real.log (Real.log (B x)) / Real.log (B x)) / lam)
        atTop (nhds (1 / lam)) := by
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hsmall).div_const lam
    apply hh.congr'
    filter_upwards [hlogB.eventually (eventually_gt_atTop (0 : ℝ))] with x hx
    unfold psi
    field_simp [hx.ne', lam_pos.ne']
  have hfloor : Tendsto (fun x => (m x : ℝ) / psi (B x)) atTop (nhds 1) :=
    tendsto_nat_floor_div_atTop.comp (psi_tendsto.comp B_tendsto)
  have hmratio : Tendsto (fun x => (m x : ℝ) / Real.log (B x))
      atTop (nhds (1 / lam)) := by
    have hh := hfloor.mul hpsi
    simp only [one_mul] at hh
    apply hh.congr'
    filter_upwards [(psi_tendsto.comp B_tendsto).eventually
      (eventually_gt_atTop (0 : ℝ))] with x hx
    change 0 < psi (B x) at hx
    field_simp [hx.ne']
  have hlm : Tendsto (fun x => lam * ((m x : ℝ) / Real.log (B x)))
      atTop (nhds 1) := by
    simpa only [mul_one_div_cancel lam_pos.ne'] using hmratio.const_mul lam
  have hh := hlm.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  change Tendsto (fun x => Real.log (B x) / (lam * m x)) atTop (nhds 1)
  simpa only [inv_one, mul_inv_rev, inv_div, inv_inv, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using hh

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CofactorEnvelope
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The cofactor envelope from Mertens' published prime-product theorem.
We use only its upper bound, stated as Theorem 1.1, equation (1.2), in
J. D. Lichtman, *Mertens' prime product formula, dissected*,
arXiv:2002.03361v3 (2021), citing Mertens (1874),
*J. reine angew. Math.* 78, 46–62. This is an explicit conditional input.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma totient_ratio_product {n : ℕ} (hn : 0 < n) :
    (n : ℝ)/n.totient = ∏ p ∈ n.primeFactors, (p : ℝ)/(p-1) := by
  have hφ : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr hn
  have hprod : (0 : ℝ) < ∏ p ∈ n.primeFactors, (p-1 : ℝ) := by
    apply Finset.prod_pos
    intro p hp
    have hh : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    linarith
  have he := congrArg (fun k : ℕ => (k : ℝ)) (Nat.totient_mul_prod_primeFactors n)
  push_cast at he
  have he' : (n.totient : ℝ)*(∏ p ∈ n.primeFactors, (p : ℝ)) =
      n*(∏ p ∈ n.primeFactors, (p-1 : ℝ)) := by
    convert he using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_lt.le, Nat.cast_one]
  rw [Finset.prod_div_distrib]
  exact (div_eq_div_iff hφ.ne' hprod.ne').mpr (by nlinarith [he'])

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CanceledPrimeMass
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reciprocal cost of fixing the canceled primes, from Mertens' input. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma primeEulerProduct_pos (N : ℕ) : 0 < primeEulerProduct N := by
  apply Finset.prod_pos
  intro p hp
  have hprime := (Finset.mem_filter.mp hp).2
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
  exact div_pos (by linarith) (by linarith)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionScale
attribute [-instance] _root_.W21.instNorm _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete renewal bounds needed for the manuscript's collision cutoff.
These are proved from the defining series; no additional numerical input is assumed. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

private lemma small_log_identities :
    Real.log 4 = 2*Real.log 2 ∧ Real.log 6 = Real.log 2+Real.log 3 ∧
    Real.log 8 = 3*Real.log 2 ∧ Real.log 9 = 2*Real.log 3 := by
  refine ⟨Real.log_four_eq, ?_, ?_, ?_⟩
  · convert Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)
  · convert Real.log_pow (2 : ℝ) 3 using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)
  · convert Real.log_pow (3 : ℝ) 2 using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)

private lemma log_seven_bounds :
    3*Real.log 2-1/7 ≤ Real.log 7 ∧ Real.log 7 ≤ 3*Real.log 2-1/8 := by
  have hu := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<7/8)
  have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<8/7)
  rw [Real.log_div (by norm_num : (7 : ℝ) ≠ 0) (by norm_num : (8 : ℝ) ≠ 0),
    small_log_identities.2.2.1] at hu
  rw [Real.log_div (by norm_num : (8 : ℝ) ≠ 0) (by norm_num : (7 : ℝ) ≠ 0),
    small_log_identities.2.2.1] at hl
  constructor <;> linarith

private lemma renewal_tail_majorant {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (k : ℕ) :
    (∑' n : ℕ, a (n+k+1)*r^(n+k+1)) ≤
      r^(k+1)*(r/(1-r)^2+(k+1)/(1-r)) := by
  have hn : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hs := (hasSum_coe_mul_geometric_of_norm_lt_one hn).add
    ((hasSum_geometric_of_lt_one hr0 hr1).mul_left (k+1 : ℝ))
  have hh : HasSum (fun n : ℕ => (n+k+1 : ℝ)*r^(n+k+1))
      (r^(k+1)*(r/(1-r)^2+(k+1)/(1-r))) := by
    have h2 := hs.mul_left (r^(k+1))
    have e1 : (fun b : ℕ => r^(k+1) * ((b : ℝ) * r^b + ((k : ℝ)+1) * r^b)) =
        fun n : ℕ => (n+k+1 : ℝ)*r^(n+k+1) := by
      ext n
      have : r^(n+k+1) = r^(k+1)*r^n := by
        rw [show n+k+1 = n+(k+1) by omega, pow_add]; ring
      rw [this]; ring
    have e2 : r^(k+1) * (r/(1-r)^2 + ((k:ℝ)+1) * (1-r)⁻¹) =
        r^(k+1)*(r/(1-r)^2+(k+1)/(1-r)) := by simp only [div_eq_mul_inv]
    rw [e1, e2] at h2
    exact h2
  rw [← hh.tsum_eq]
  apply Summable.tsum_le_tsum _ _ hh.summable
  · intro n
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast a_le_index (j := n+k+1) (by omega))
      (pow_nonneg hr0 _)
  · simpa only [Nat.add_assoc] using
      (summable_nat_add_iff (f := fun n : ℕ => a (n+1)*r^(n+1)) k).2
        (summable_renewal hr0 hr1)

lemma renewalSeries_thirteen_twentyfifths_lt_one : renewalSeries (13/25) < 1 := by
  have hs := (summable_renewal (r := (13/25 : ℝ)) (by norm_num) (by norm_num)).sum_add_tsum_nat_add 8
  have ht := renewal_tail_majorant (r := (13/25 : ℝ)) (by norm_num) (by norm_num) 8
  change (∑ n ∈ Finset.range 8, a (n+1)*(13/25 : ℝ)^(n+1)) + _ = renewalSeries (13/25) at hs
  have hfinite : (∑ n ∈ Finset.range 8, a (n+1)*(13/25 : ℝ)^(n+1)) < 9/10 := by
    norm_num [Finset.sum_range_succ, a, small_log_identities.1,
      small_log_identities.2.1, small_log_identities.2.2.1,
      small_log_identities.2.2.2]
    linarith [Real.log_two_lt_d9, Real.log_three_lt_d9, Real.log_five_lt_d9,
      log_seven_bounds.2]
  have htail : (∑' n : ℕ, a (n+8+1)*(13/25 : ℝ)^(n+8+1)) < 1/10 := by
    exact ht.trans_lt (by norm_num)
  have heq : (∑' n : ℕ, a (n+1+8)*(13/25 : ℝ)^(n+1+8)) =
      ∑' n : ℕ, a (n+8+1)*(13/25 : ℝ)^(n+8+1) := by
    congr 1
  simp only [heq] at hs
  linarith

lemma renewalSeries_onehundredthirtyseven_twohundredfiftieths_gt_one :
    1 < renewalSeries (137/250) := by
  have hs := summable_renewal (r := (137/250 : ℝ)) (by norm_num) (by norm_num)
  have hl := hs.sum_le_tsum (Finset.range 8)
    (fun n _ => mul_nonneg (a_pos (by omega)).le (pow_nonneg (by norm_num) _))
  change _ ≤ renewalSeries (137/250) at hl
  have hfinite : 1 < (∑ n ∈ Finset.range 8, a (n+1)*(137/250 : ℝ)^(n+1)) := by
    norm_num [Finset.sum_range_succ, a, small_log_identities.1,
      small_log_identities.2.1, small_log_identities.2.2.1,
      small_log_identities.2.2.2]
    linarith [Real.log_two_gt_d9, Real.log_three_gt_d9, Real.log_five_gt_d9,
      log_seven_bounds.1]
  exact hfinite.trans_le hl

lemma collision_rho_bounds : (13/25 : ℝ) < rho ∧ rho < 137/250 := by
  constructor
  · by_contra! h
    have hh := renewalSeries_strictMonoOn.monotoneOn
      (show rho ∈ Set.Ico (0 : ℝ) 1 from ⟨rho_pos.le, rho_lt_one⟩)
      (show (13/25 : ℝ) ∈ Set.Ico 0 1 by norm_num) h
    rw [renewalSeries_rho] at hh
    linarith [renewalSeries_thirteen_twentyfifths_lt_one]
  · by_contra! h
    have hh := renewalSeries_strictMonoOn.monotoneOn
      (show (137/250 : ℝ) ∈ Set.Ico 0 1 by norm_num)
      (show rho ∈ Set.Ico (0 : ℝ) 1 from ⟨rho_pos.le, rho_lt_one⟩) h
    rw [renewalSeries_rho] at hh
    linarith [renewalSeries_onehundredthirtyseven_twohundredfiftieths_gt_one]

lemma collision_lambda_bounds : (3/5 : ℝ) < lam ∧ lam < 2/3 := by
  have he3 : Real.exp (3/5 : ℝ) < 250/137 := by
    have he : (Real.exp (3/5 : ℝ))^5 < (250/137 : ℝ)^5 := by
      calc
        _ = (Real.exp 1)^3 := by rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; congr 1; norm_num
        _ < (2.7182818286 : ℝ)^3 := pow_lt_pow_left₀ Real.exp_one_lt_d9 (by positivity) (by norm_num)
        _ < _ := by norm_num
    exact (pow_lt_pow_iff_left₀ (Real.exp_pos _).le (by norm_num) (by norm_num : 5 ≠ 0)).mp he
  have he2 : (25/13 : ℝ) < Real.exp (2/3 : ℝ) := by
    have he : (25/13 : ℝ)^3 < (Real.exp (2/3 : ℝ))^3 := by
      calc
        _ < (2.7182818283 : ℝ)^2 := by norm_num
        _ < (Real.exp 1)^2 := pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)
        _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; congr 1; norm_num
    exact (pow_lt_pow_iff_left₀ (by norm_num) (Real.exp_pos _).le (by norm_num : 3 ≠ 0)).mp he
  unfold lam
  constructor
  · apply (Real.lt_log_iff_exp_lt (div_pos zero_lt_one rho_pos)).mpr
    apply he3.trans
    apply (lt_div_iff₀ rho_pos).mpr
    nlinarith [collision_rho_bounds.2]
  · apply (Real.log_lt_iff_lt_exp (div_pos zero_lt_one rho_pos)).mpr
    apply lt_trans _ he2
    apply (div_lt_iff₀ rho_pos).mpr
    nlinarith [collision_rho_bounds.1]

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

lemma G_pos {x : ℝ} (hx : 0 < B x) (j : ℕ) : 0 < G x j := by
  unfold G
  apply div_pos (pow_pos hx _)
  exact mul_pos (by exact_mod_cast Nat.factorial_pos j)
    (Finset.prod_pos (fun i _ => g_pos i))

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TailRenewal
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized finite-tail budget and its renewal-convolution limit. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma alpha_ge_lam {s : ℝ} (hs : 0 ≤ s) : lam ≤ alpha s := by
  unfold alpha
  have he : 1 ≤ Real.exp (lam*s) := Real.one_le_exp (mul_nonneg lam_pos.le hs)
  nlinarith [lam_pos]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_Prefactor
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-tail prefactor, including its dependence on the moving phase. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma G_step {x : ℝ} (hB : 0 < B x) (j : ℕ) :
    G x j = ((j+1 : ℝ)*g (j+1)/B x)*G x (j+1) := by
  have hp : (∏ i ∈ Finset.Icc 1 j, g i) ≠ 0 :=
    (Finset.prod_pos (fun i _ => g_pos i)).ne'
  have hf : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero j)
  have hj : (j+1 : ℝ) ≠ 0 := by positivity
  unfold G
  rw [Finset.prod_Icc_succ_top (by omega), Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp [hB.ne', hp, hf, hj, (g_pos (j+1)).ne']

lemma G_sub_eq_product {x : ℝ} (hB : 0 < B x) (n H : ℕ) (hH : H ≤ n) :
    G x (n-H) = G x n *
      ∏ k ∈ Finset.range H, ((n-k : ℕ) : ℝ)*g (n-k)/B x := by
  induction H with
  | zero => simp
  | succ H ih =>
    have hH' : H ≤ n := by omega
    have hidx : n-(H+1)+1 = n-H := by omega
    have hcast : ((n-(H+1) : ℕ) : ℝ)+1 = ((n-H : ℕ) : ℝ) := by
      exact_mod_cast hidx
    rw [G_step hB (n-(H+1)), hidx, ih hH', Finset.prod_range_succ]
    rw [hcast]
    ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_UniformPrefactor
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A simultaneous bound for all projected prefix volumes. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma inverse_scale_eq {x : ℝ} (hB : 1 < B x) (hm : 0 < m x) :
    (m x : ℝ)/(B x*rho^(m x)) = (alpha (theta x)*bandCenterRatio x)⁻¹ := by
  rw [alpha_theta_eq hB]
  unfold bandCenterRatio
  field_simp [(Real.log_pos hB).ne', (zero_lt_one.trans hB).ne',
    lam_pos.ne', Nat.cast_ne_zero.mpr hm.ne', rho_pos.ne']

lemma inverse_scale_bound : ∀ᶠ x : ℝ in atTop,
    (m x : ℝ)/(B x*rho^(m x)) ≤ 2/lam := by
  filter_upwards [theta_eventually_mem,
    B_tendsto.eventually (eventually_gt_atTop (1 : ℝ)),
    m_tendsto.eventually (eventually_gt_atTop 0),
    bandCenterRatio_tendsto.eventually
      (eventually_gt_nhds (show (1/2 : ℝ) < 1 by norm_num))] with x hx hB hm hv
  rw [inverse_scale_eq hB hm]
  have ha := alpha_ge_lam hx.1
  have hprod : lam/2 ≤ alpha (theta x)*bandCenterRatio x := by
    nlinarith [lam_pos, alpha_pos (theta x)]
  calc
    _ ≤ (lam/2)⁻¹ := inv_anti₀ (div_pos lam_pos (by norm_num)) hprod
    _ = _ := by ring

lemma uniform_step_bound (hford : FordRenewalInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ i ≤ m x,
      ((m x-i : ℕ) : ℝ)*g (m x-i)/B x ≤ C*rho^i := by
  obtain ⟨_, K, hK, hg⟩ := normalizedRenewal_properties hford
  let C := 2*(K+1)/lam
  refine ⟨C, div_pos (mul_pos (by norm_num) (by linarith)) lam_pos, ?_⟩
  filter_upwards [inverse_scale_bound,
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with x hx hB
  intro i hi
  have hgn : g (m x-i)*rho^(m x-i) ≤ K+1 := by
    have hh := hg (m x-i)
    change |g (m x-i)*rho^(m x-i)| ≤ K at hh
    exact (le_abs_self _).trans (hh.trans (by linarith))
  have hg' : g (m x-i) ≤ (K+1)/rho^(m x-i) :=
    (le_div_iff₀ (pow_pos rho_pos _)).mpr hgn
  have hm' : ((m x-i : ℕ) : ℝ) ≤ m x := by exact_mod_cast Nat.sub_le (m x) i
  have hpow : rho^(m x-i)*rho^i = rho^(m x) := by
    rw [← pow_add, Nat.sub_add_cancel hi]
  calc
    _ ≤ (m x : ℝ)*((K+1)/rho^(m x-i))/B x := by
      apply div_le_div_of_nonneg_right _ hB.le
      exact mul_le_mul hm' hg' (g_pos _).le (Nat.cast_nonneg _)
    _ = ((K+1)*((m x : ℝ)/(B x*rho^(m x))))*rho^i := by
      rw [← hpow]
      field_simp [rho_pos.ne']
    _ ≤ ((K+1)*(2/lam))*rho^i :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx (by linarith))
        (pow_nonneg rho_pos.le _)
    _ = C*rho^i := by dsimp [C] <;> ring

/-- Ford's bounded renewal error yields the manuscript's simultaneous
projected-volume majorant, including prefixes whose length moves with `x`. -/
theorem uniform_projected_volume_bound (hford : FordRenewalInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ H ≤ m x,
      G x (m x-H)/G x (m x) ≤ C^H*rho^(H*(H-1)/2) := by
  obtain ⟨C, hC, hstep⟩ := uniform_step_bound hford
  refine ⟨C, hC, ?_⟩
  filter_upwards [hstep, B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))]
    with x hx hB
  intro H hH
  rw [G_sub_eq_product hB (m x) H hH, mul_div_cancel_left₀ _ (G_pos hB _).ne']
  calc
    _ ≤ ∏ i ∈ Finset.range H, C*rho^i := by
      apply Finset.prod_le_prod
      · intro i hi
        exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (g_pos _).le) hB.le
      · intro i hi
        exact hx i (by have := Finset.mem_range.mp hi; omega)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
        Finset.prod_pow_eq_pow_sum, Finset.sum_range_id]

lemma summable_projectedEnvelope {C : ℝ} (hC : 0 < C) :
    Summable (projectedEnvelope C) := by
  have hh : Tendsto (fun n : ℕ => C*rho^n) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one rho_pos.le rho_lt_one).const_mul C
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (hh.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)))
  let q := C*rho^K
  have hq : 0 < q := mul_pos hC (pow_pos rho_pos _)
  have hq1 : q < 1 := hK K le_rfl
  have hg : Summable (fun n : ℕ => q^n) :=
    summable_geometric_of_lt_one hq.le hq1
  apply hg.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop (2*K+1)] with n hn
  have htri : K*n ≤ n*(n-1)/2 := by
    have hn' : 2*K ≤ n-1 := by omega
    have hm := Nat.mul_le_mul_left n hn'
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr
    nlinarith
  unfold projectedEnvelope
  rw [Real.norm_eq_abs, abs_of_pos
    (mul_pos (pow_pos hC _) (pow_pos rho_pos _))]
  calc
    _ ≤ C^n*rho^(K*n) := mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one rho_pos.le rho_lt_one.le htri) (pow_pos hC _).le
    _ = q^n := by rw [pow_mul, mul_pow]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_MertensEuler
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite Euler product controlled by a convergent real power series. -/
noncomputable section
open scoped BigOperators
open MeasureTheory Set
namespace TotientAsymptotic

lemma negative_power_sum_le {s : ℝ} (hs : 1 < s) :
    (∑' n : ℕ, (n : ℝ)^(-s)) ≤ 1+1/(s-1) := by
  have hsum : Summable (fun n : ℕ => (n : ℝ)^(-s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have htail := AntitoneOn.tsum_comp_add_le_integral (f := fun x : ℝ => x^(-s)) 1
    (fun x hx y _ hxy => Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le (by simpa using hx)) hxy (by linarith))
    (integrableOn_Ioi_rpow_of_lt (by linarith : -s < -1) (by norm_num))
    (fun x hx => Real.rpow_nonneg (zero_lt_one.trans (by simpa using hx)).le _)
  simp only [Nat.cast_one] at htail
  rw [integral_Ioi_rpow_of_lt (by linarith : -s < -1) (by norm_num : (0 : ℝ)<1)] at htail
  have he : (∑' n : ℕ, (n : ℝ)^(-s))=1+∑' n : ℕ, ((n+1+1 : ℕ) : ℝ)^(-s) := by
    rw [← hsum.sum_add_tsum_nat_add 2]
    norm_num [Finset.sum_range_succ,show s≠0 by linarith]
    congr 1
    funext n
    congr 1
    ring
  rw [he]
  have htail' : (∑' n : ℕ, ((n+1+1 : ℕ) : ℝ)^(-s)) ≤ 1/(s-1) := by
    have hi : -(1 : ℝ)^(-s+1)/(-s+1)=1/(s-1) := by
      rw [Real.one_rpow,show -s+1= -(s-1) by ring]
      simp only [div_neg,neg_div,neg_neg]
    exact hi ▸ htail
  linarith

lemma finite_power_euler_product_le {s : ℝ} (hs : 1 < s) (S : Finset ℕ) :
    (∏ p ∈ S.filter Nat.Prime, (1-(p : ℝ)^(-s))⁻¹) ≤ 1+1/(s-1) := by
  have hp : ∀ {p : ℕ}, p.Prime → ‖negativePower s p‖<1 := by
    intro p hp
    change ‖(p : ℝ)^(-s)‖<1
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    have h := Real.rpow_lt_rpow_of_exponent_lt (show (1 : ℝ)<p by exact_mod_cast hp.one_lt)
      (show -s<0 by linarith)
    simpa only [Real.rpow_zero] using h
  have he := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := negativePower s) hp S
  have hsum : Summable (fun n : ℕ => (n : ℝ)^(-s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hb := hsum.tsum_subtype_le (fun n : ℕ => (n : ℝ)^(-s))
    (Nat.factoredNumbers S) (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have heq : (∑' n : Nat.factoredNumbers S, negativePower s n)=
      ∏ p ∈ S.filter Nat.Prime, (1-(p : ℝ)^(-s))⁻¹ := he.2.tsum_eq
  exact heq.symm.trans_le (hb.trans (negative_power_sum_le hs))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_MertensLogMass
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite summation-by-parts bound sufficient for the Mertens product. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

private lemma weighted_sum_le_harmonic (a : ℕ → ℝ) (C : ℝ)
    (ha0 : a 0=0)
    (hA : ∀ n : ℕ, (∑ i ∈ Finset.range (n+1), a i) ≤ C*(n+1)) (n : ℕ) :
    (∑ i ∈ Finset.range (n+1), a i/(i : ℝ)) ≤
      (∑ i ∈ Finset.range (n+1), a i)/(n+1)+C*(harmonic n : ℝ) := by
  induction n with
  | zero => simp [ha0]
  | succ n ih =>
    have hn : (0 : ℝ)<n+1 := by positivity
    have hn2 : (0 : ℝ)<n+2 := by positivity
    let A := ∑ i ∈ Finset.range (n+2), a i
    have hA' : A ≤ C*(n+2) := by
      convert hA (n+1) using 1
      all_goals try with_reducible_and_instances rfl
      simp only [Nat.cast_add,Nat.cast_one]
      ring
    have hstep : A/(n+1) ≤ A/(n+2)+C/(n+1) := by
      apply (div_le_iff₀ hn).mpr
      have hdiv : A/(n+2) ≤ C := (div_le_iff₀ hn2).mpr hA'
      have he : A/(n+2)*(n+2)=A := div_mul_cancel₀ A hn2.ne'
      rw [add_mul,div_mul_cancel₀ _ hn.ne']
      nlinarith
    have hrec : A=(∑ i ∈ Finset.range (n+1), a i)+a (n+1) := by
      exact Finset.sum_range_succ a (n+1)
    calc
      _ = (∑ i ∈ Finset.range (n+1), a i/(i : ℝ))+a (n+1)/(n+1) := by
        rw [Finset.sum_range_succ]
        push_cast
        rfl
      _ ≤ (∑ i ∈ Finset.range (n+1), a i)/(n+1)+C*(harmonic n : ℝ)+
          a (n+1)/(n+1) := add_le_add ih le_rfl
      _ = A/(n+1)+C*(harmonic n : ℝ) := by
        rw [hrec,add_div]
        ring
      _ ≤ A/(n+2)+C/(n+1)+C*(harmonic n : ℝ) := add_le_add hstep le_rfl
      _ = _ := by
        rw [harmonic_succ]
        push_cast
        dsimp [A]
        ring

/-- Only a coarse logarithmic bound is needed; no Mertens theorem is assumed. -/
lemma prime_log_mass_le (N : ℕ) (hN : 2 ≤ N) :
    (∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime, Real.log p/(p : ℝ)) ≤
      Real.log 4*(2+Real.log N) := by
  classical
  let a : ℕ → ℝ := fun n => if n.Prime then Real.log n else 0
  have he (n : ℕ) : (∑ i ∈ Finset.range (n+1), a i)=Chebyshev.theta n := by
    rw [Chebyshev.theta_eq_sum_Icc,Nat.floor_natCast,← Nat.range_succ_eq_Icc_zero,
      Finset.sum_filter]

  have hA (n : ℕ) : (∑ i ∈ Finset.range (n+1), a i) ≤ Real.log 4*(n+1) := by
    rw [he]
    have hh := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n)
    have hc : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    nlinarith
  have hb := weighted_sum_le_harmonic a (Real.log 4) (by simp [a]) hA N
  have hsum : (∑ i ∈ Finset.range (N+1), a i/(i : ℝ))=
      ∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime, Real.log p/(p : ℝ) := by
    rw [Nat.range_succ_eq_Icc_zero,Finset.sum_filter]
    simp only [a,ite_div,zero_div]
    symm
    apply Finset.sum_subset (fun p hp => by
      have hh := Finset.mem_Icc.mp hp
      exact Finset.mem_Icc.mpr ⟨by omega,hh.2⟩)
    · intro p hp hnot
      have hp2 : p<2 := by
        have hh := Finset.mem_Icc.mp hp
        simp only [Finset.mem_Icc,not_and_or,not_le] at hnot
        omega
      have hprime : ¬p.Prime := fun hh => (not_le_of_gt hp2) hh.two_le
      simp [hprime]
  rw [hsum] at hb
  have ht := (div_le_iff₀ (show (0 : ℝ)<N+1 by positivity)).mpr (hA N)
  have hh := harmonic_le_one_add_log N
  have hc : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hh hc
  nlinarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_MertensFactor
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Comparison of the ordinary and convergent prime Euler factors. -/
noncomputable section
namespace TotientAsymptotic

lemma mertens_factor_le {u : ℝ} (hu : 0<u) {p : ℕ} (hp : p.Prime) :
    (p : ℝ)/(p-1) ≤ Real.exp (2*u*Real.log p/p)*(1-(p : ℝ)^(-(1+u)))⁻¹ := by
  have hp2 : (2 : ℝ)≤p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ)<p := by linarith
  have hd : (0 : ℝ)<p-1 := by linarith
  have hv : 0≤u*Real.log p := mul_nonneg hu.le (Real.log_nonneg (by linarith))
  have hpow : (p : ℝ)^(-(1+u))=(p : ℝ)⁻¹*Real.exp (-(u*Real.log p)) := by
    rw [Real.rpow_def_of_pos hp0]
    have he : Real.log (p : ℝ)*(-(1+u))= -Real.log p+ -(u*Real.log p) := by ring
    rw [he,Real.exp_add,Real.exp_neg,Real.exp_log hp0]
  have hpowlt : (p : ℝ)^(-(1+u))<1 := by
    have h := Real.rpow_lt_rpow_of_exponent_lt (show (1 : ℝ)<p by linarith)
      (show -(1+u)<0 by linarith)
    simpa using h
  have hB : 0<1-(p : ℝ)^(-(1+u)) := by linarith
  have hr : (1 : ℝ)/(p-1)≤2/p := by
    apply (div_le_div_iff₀ hd hp0).mpr
    nlinarith
  have he : (p : ℝ)/(p-1)*(1-(p : ℝ)^(-(1+u))) ≤ Real.exp (2*u*Real.log p/p) := by
    calc
      _ = 1+(1-Real.exp (-(u*Real.log p)))/(p-1) := by
        rw [hpow]
        field_simp
        ring
      _ ≤ 1+(u*Real.log p)/(p-1) := by
        apply add_le_add le_rfl
        apply div_le_div_of_nonneg_right _ hd.le
        linarith [Real.one_sub_le_exp_neg (u*Real.log p)]
      _ ≤ 1+2*u*Real.log p/p := by
        have hh := mul_le_mul_of_nonneg_left hr hv
        first | (convert add_le_add_left hh 1 using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans ((add_le_add_left hh 1).trans (le_of_eq (by ring)))
      _ ≤ _ := by simpa [add_comm] using Real.add_one_le_exp (2*u*Real.log p/p)
  simpa only [div_eq_mul_inv] using (le_div_iff₀ hB).mpr he

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_MertensProduct
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete Mertens upper bound used by the totient asymptotic. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma primeEulerProduct_rankin {u : ℝ} (hu : 0<u) (N : ℕ) :
    primeEulerProduct N ≤
      Real.exp (2*u*(∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime,
        Real.log p/(p : ℝ)))*(1+1/u) := by
  let S := (Finset.Icc 2 N).filter Nat.Prime
  have he : (∏ p ∈ S, Real.exp (2*u*Real.log p/p))=
      Real.exp (2*u*(∑ p ∈ S, Real.log p/p)) := by
    rw [← Real.exp_sum,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro p hp
    ring
  calc
    primeEulerProduct N ≤ ∏ p ∈ S,
        Real.exp (2*u*Real.log p/p)*(1-(p : ℝ)^(-(1+u)))⁻¹ := by
      apply Finset.prod_le_prod
      · intro p hp
        have hp2 : (2 : ℝ)≤p := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
        exact div_nonneg (Nat.cast_nonneg _) (by linarith)
      · intro p hp
        exact mertens_factor_le hu (Finset.mem_filter.mp hp).2
    _ = Real.exp (2*u*(∑ p ∈ S, Real.log p/p))*
        ∏ p ∈ S, (1-(p : ℝ)^(-(1+u)))⁻¹ := by
      rw [Finset.prod_mul_distrib,he]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      have hh := finite_power_euler_product_le (show 1<1+u by linarith) (Finset.Icc 2 N)
      simpa only [add_sub_cancel_left] using hh

/-- Mertens' full asymptotic is unnecessary here: Chebyshev, finite Euler
products and the integral test prove exactly the required upper bound. -/
theorem mertensProductInput : MertensProductInput := by
  refine ⟨3*Real.exp (10*Real.log 4),by positivity,?_⟩
  intro N hN
  have hlog : (1/2 : ℝ)<Real.log N := by
    have hn : (2 : ℝ)≤N := by exact_mod_cast hN
    have hh := Real.log_le_log (by norm_num : (0 : ℝ)<2) hn
    linarith [Real.log_two_gt_d9]
  have hc : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
  have hu : 0<1/Real.log N := by positivity
  have hb := primeEulerProduct_rankin hu N
  have hm := mul_le_mul_of_nonneg_left (prime_log_mass_le N hN)
    (show 0≤2*(1/Real.log N) by positivity)
  have hexp : 2*(1/Real.log N)*(∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime,
      Real.log p/(p : ℝ)) ≤ 10*Real.log 4 := by
    have hi : 1/Real.log N≤2 := by
      apply (div_le_iff₀ (by linarith : 0<Real.log N)).mpr
      linarith
    have he : 2*(1/Real.log N)*(Real.log 4*(2+Real.log N))=
        4*(1/Real.log N)*Real.log 4+2*Real.log 4 := by
      field_simp
      ring
    rw [he] at hm
    nlinarith
  have hlast : 1+1/(1/Real.log N) ≤ 3*Real.log N := by
    simp only [one_div_one_div]
    linarith
  calc
    primeEulerProduct N ≤ Real.exp (2*(1/Real.log N)*
        (∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime, Real.log p/(p : ℝ)))*
        (1+1/(1/Real.log N)) := hb
    _ ≤ Real.exp (10*Real.log 4)*(3*Real.log N) :=
      mul_le_mul (Real.exp_le_exp.mpr hexp) hlast (by positivity) (by positivity)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TotientRatioLogLog
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform log-log bound for the elementary totient ratio. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma totient_factor_large_prime {p : ℕ} (hp : p.Prime) {L : ℝ}
    (hL : 0<L) (hpL : L≤p) :
    (p:ℝ)/(p-1) ≤ Real.exp (4*Real.log p/L) := by
  have hp2 : (2:ℝ)≤p := by exact_mod_cast hp.two_le
  have hp0 : (0:ℝ)<p := by linarith
  have hp1 : (0:ℝ)<p-1 := by linarith
  have hlog : (1/2:ℝ)≤Real.log p := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ)<2) hp2
    linarith [Real.log_two_gt_d9]
  have hfirst : (1:ℝ)/(p-1) ≤ 2/(p:ℝ) := by
    apply (div_le_div_iff₀ hp1 hp0).mpr
    linarith
  have hsecond : 2/(p:ℝ) ≤ 4*Real.log p/L := by
    apply (div_le_div_iff₀ hp0 hL).mpr
    nlinarith
  have he : (p:ℝ)/(p-1) = 1+1/(p-1) := by field_simp <;> ring
  rw [he]
  have hh := Real.add_one_le_exp (4*Real.log p/L)
  linarith

lemma totient_large_prime_product {b : ℕ} (hb : 0<b) {L : ℝ} (hL : 0<L)
    (hbL : Real.log b ≤ L) (T : Finset ℕ) (hT : T ⊆ b.primeFactors)
    (hlarge : ∀ p ∈ T,L≤p) :
    (∏ p ∈ T,(p:ℝ)/(p-1)) ≤ Real.exp 4 := by
  have hprimes : ∀ p ∈ T,p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hT hp)
  have hprod0 : (0:ℝ)<(∏ p ∈ T,p : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun p hp => (hprimes p hp).pos)
  have hdvd : (∏ p ∈ T,p) ∣ b :=
    (Finset.prod_dvd_prod_of_subset T b.primeFactors id hT).trans b.prod_primeFactors_dvd
  have hsum : (∑ p ∈ T,Real.log p) ≤ L := by
    have he : Real.log ((∏ p ∈ T,p : ℕ):ℝ) = ∑ p ∈ T,Real.log p := by
      rw [Nat.cast_prod,Real.log_prod (fun p hp => by exact_mod_cast (hprimes p hp).ne_zero)]
    rw [← he]
    exact (Real.log_le_log hprod0 (by exact_mod_cast Nat.le_of_dvd hb hdvd)).trans hbL
  calc
    _ ≤ ∏ p ∈ T,Real.exp (4*Real.log p/L) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hp1 : (1:ℝ)<p := by exact_mod_cast (hprimes p hp).one_lt
        exact div_nonneg (Nat.cast_nonneg _) (by linarith)
      · intro p hp
        exact totient_factor_large_prime (hprimes p hp) hL (hlarge p hp)
    _ = Real.exp ((4/L)*(∑ p ∈ T,Real.log p)) := by
      rw [← Real.exp_sum,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hsum (show 0≤4/L by positivity)
      have he : (4/L)*L=4 := by field_simp
      rwa [he] at hh

/-- Uniformity in `b ≤ x` is the form needed when summing shifted prime pairs. -/
theorem totient_ratio_loglog_bound : ∃ C : ℝ, 0<C ∧ ∀ x : ℝ, Real.exp 2 ≤ x →
    ∀ b : ℕ, 0<b → (b:ℝ)≤x → (b:ℝ)/b.totient ≤ C*Real.log (Real.log x) := by
  classical
  obtain ⟨C,hC,hM⟩ := mertensProductInput
  refine ⟨C*Real.exp 4,by positivity,?_⟩
  intro x hx b hb hbx
  have hx0 : 0<x := (Real.exp_pos 2).trans_le hx
  have hlog : 2 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hx
  have hN : 2 ≤ ⌊Real.log x⌋₊ := (Nat.le_floor_iff (by linarith)).mpr hlog
  let S := b.primeFactors.filter (fun p : ℕ => (p:ℝ)≤Real.log x)
  let T := b.primeFactors.filter (fun p : ℕ => ¬(p:ℝ)≤Real.log x)
  have hsmall : (∏ p ∈ S,(p:ℝ)/(p-1)) ≤ primeEulerProduct ⌊Real.log x⌋₊ := by
    apply Finset.prod_le_prod_of_subset_of_one_le
    · intro p hp
      obtain ⟨hpb,hpL⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨(Nat.prime_of_mem_primeFactors hpb).two_le,Nat.le_floor hpL⟩,
        Nat.prime_of_mem_primeFactors hpb⟩
    · intro p hp
      have hp1 : (1:ℝ)<p := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).one_lt
      exact div_nonneg (Nat.cast_nonneg _) (by linarith)
    · intro p hp _
      have hp1 : (1:ℝ)<p := by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
      apply (le_div_iff₀ (by linarith : (0:ℝ)<p-1)).mpr
      linarith
  have hlarge : (∏ p ∈ T,(p:ℝ)/(p-1)) ≤ Real.exp 4 :=
    totient_large_prime_product hb (by linarith)
      (Real.log_le_log (by exact_mod_cast hb) hbx) T (Finset.filter_subset _ _)
      (fun p hp => (le_of_not_ge (Finset.mem_filter.mp hp).2))
  have hsmall0 : 0 ≤ ∏ p ∈ S,(p:ℝ)/(p-1) := by
    apply Finset.prod_nonneg
    intro p hp
    have hp1 : (1:ℝ)<p := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).one_lt
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  have hsplit : (b:ℝ)/b.totient =
      (∏ p ∈ S,(p:ℝ)/(p-1))*(∏ p ∈ T,(p:ℝ)/(p-1)) := by
    rw [totient_ratio_product hb]
    exact (Finset.prod_filter_mul_prod_filter_not b.primeFactors
      (fun p : ℕ => (p:ℝ)≤Real.log x) (fun p => (p:ℝ)/(p-1))).symm
  have hlN : Real.log (⌊Real.log x⌋₊:ℝ) ≤ Real.log (Real.log x) :=
    Real.log_le_log (by exact_mod_cast (show 0<⌊Real.log x⌋₊ by omega))
      (Nat.floor_le (by linarith))
  calc
    (b:ℝ)/b.totient = _ := hsplit
    _ ≤ primeEulerProduct ⌊Real.log x⌋₊ * Real.exp 4 :=
      mul_le_mul hsmall hlarge (Finset.prod_nonneg (fun p hp => by
        have hp1 : (1:ℝ)<p := by
          exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).one_lt
        exact div_nonneg (Nat.cast_nonneg _) (by linarith)))
        (primeEulerProduct_pos _).le
    _ ≤ (C*Real.log (⌊Real.log x⌋₊:ℝ))*Real.exp 4 :=
      mul_le_mul_of_nonneg_right (hM _ hN) (Real.exp_pos _).le
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hlN (show 0≤C*Real.exp 4 by positivity)
      nlinarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SimplexCube
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every box meeting a basic full prime tuple lies in a controlled
multiplicative enlargement of the full simplex. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma xi_bounds (x : ℝ) (i : ℕ) : 1 ≤ xi x i ∧ xi x i ≤ 2 := by
  have hp := Real.exp_pos (-((m x-i : ℕ) : ℝ)/40)
  have he : Real.exp (-((m x-i : ℕ) : ℝ)/40) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by have := Nat.cast_nonneg (m x-i) (α := ℝ); linarith)
  constructor <;> dsimp [xi] <;> linarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TotientPreimageBound
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete preimage bounds for the finite totient counting reductions. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma prime_le_shift_square {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : p ≤ (p-1)^2 := by
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  have he : p-1+1=p := by omega
  nlinarith

lemma radical_le_twice_shift_product_square (n : ℕ) :
    (∏ p ∈ n.primeFactors,p) ≤ 2*(∏ p ∈ n.primeFactors,(p-1))^2 := by
  let E := n.primeFactors.erase 2
  have hprod : (∏ p ∈ E,p) ≤ (∏ p ∈ E,(p-1))^2 := by
    rw [← Finset.prod_pow]
    apply Finset.prod_le_prod'
    intro p hp
    exact prime_le_shift_square (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp))
      (Finset.mem_erase.mp hp).1
  by_cases h2 : 2 ∈ n.primeFactors
  · have hrad := Finset.mul_prod_erase n.primeFactors (fun p : ℕ => p) h2
    have hshift := Finset.mul_prod_erase n.primeFactors (fun p : ℕ => p-1) h2
    norm_num only [Nat.reduceSub,one_mul] at hshift
    rw [← hrad,← hshift]
    exact Nat.mul_le_mul_left 2 hprod
  · have hE : E=n.primeFactors := Finset.erase_eq_of_notMem h2
    rw [hE] at hprod
    omega

lemma totient_preimage_quadratic {n : ℕ} (hn : 0 < n) : n ≤ 2*n.totient^2 := by
  let r := ∏ p ∈ n.primeFactors,p
  let s := ∏ p ∈ n.primeFactors,(p-1)
  have hr : 0 < r := Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
  have hs : 0 < s := Finset.prod_pos (fun p hp => by have := (Nat.prime_of_mem_primeFactors hp).two_le; omega)
  obtain ⟨w,hw⟩ := n.prod_primeFactors_dvd
  change n=r*w at hw
  have hw0 : 0 < w := by nlinarith
  have he := Nat.totient_mul_prod_primeFactors n
  change n.totient*r=n*s at he
  have hφ : n.totient=w*s := by
    apply Nat.eq_of_mul_eq_mul_left hr
    rw [Nat.mul_comm r n.totient,he,hw]
    ring
  have hrad : r ≤ 2*s^2 := radical_le_twice_shift_product_square n
  rw [hφ,hw]
  nlinarith [Nat.mul_le_mul_right w hrad,show w ≤ w^2 by nlinarith]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PreimageLoglogBound
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform range for every preimage of every totient up to x. -/
noncomputable section
namespace TotientAsymptotic

lemma doubleLog_twice_square {x : ℝ} (hx : Real.exp (Real.exp 1) ≤ x) :
    B (2*x^2) ≤ 3*B x := by
  have hexp : 2 ≤ Real.exp (1:ℝ) := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hx2 : Real.exp 2 ≤ x := (Real.exp_le_exp.mpr hexp).trans hx
  have hx0 : 0 < x := (Real.exp_pos 2).trans_le hx2
  have hl : 2 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hx2
  have hB : 1 ≤ B x := by
    have hh := Real.log_le_log (Real.exp_pos (1:ℝ))
      ((Real.le_log_iff_exp_le hx0).mpr hx)
    simpa only [Real.log_exp,B] using hh
  have he : Real.log (2*x^2)=Real.log 2+2*Real.log x := by
    rw [Real.log_mul (by norm_num) (pow_ne_zero _ hx0.ne'),Real.log_pow]
    norm_num
  have hh : Real.log (2*x^2) ≤ 3*Real.log x := by
    rw [he]
    linarith [Real.log_two_lt_d9]
  have hlpos : 0 < Real.log (2*x^2) := by rw [he]; positivity
  have hlog := Real.log_le_log hlpos hh
  rw [Real.log_mul (by norm_num) (by linarith : Real.log x ≠ 0)] at hlog
  have h3 : Real.log (3:ℝ) ≤ 2 := by simpa only [show (3:ℝ)-1=2 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
  change B (2*x^2) ≤ Real.log 3+B x at hlog
  linarith

theorem preimage_loglog_bound : ∃ C : ℝ,0 < C ∧
    ∀ x : ℝ,Real.exp (Real.exp 1) ≤ x → ∀ n : ℕ,0 < n → (n.totient:ℝ) ≤ x →
      (n:ℝ) ≤ C*x*B x := by
  obtain ⟨C,hC,hratio⟩ := totient_ratio_loglog_bound
  refine ⟨3*C,by positivity,?_⟩
  intro x hx n hn hφ
  have hx0 : 0 < x := (Real.exp_pos _).trans_le hx
  have hx1 : 1 < x := (Real.one_lt_exp_iff.mpr (Real.exp_pos _)).trans_le hx
  have hφ0 : (0:ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr hn
  have hnX : (n:ℝ) ≤ 2*x^2 := by
    have hh : (n:ℝ) ≤ 2*(n.totient:ℝ)^2 := by exact_mod_cast totient_preimage_quadratic hn
    exact hh.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hφ0.le hφ 2) (by norm_num))
  have hX : Real.exp 2 ≤ 2*x^2 := by
    have he : 2 ≤ Real.exp (1:ℝ) := by linarith [Real.add_one_le_exp (1:ℝ)]
    have hy : Real.exp 2 ≤ x := (Real.exp_le_exp.mpr he).trans hx
    nlinarith
  have hh := (hratio (2*x^2) hX n hn hnX).trans
    (mul_le_mul_of_nonneg_left (doubleLog_twice_square hx) hC.le)
  have hnonneg : 0 ≤ C*(3*B x) := (div_pos (by exact_mod_cast hn) hφ0).le.trans hh
  calc
    (n:ℝ) = ((n:ℝ)/n.totient)*n.totient := (div_mul_cancel₀ _ hφ0.ne').symm
    _ ≤ (C*(3*B x))*n.totient := mul_le_mul_of_nonneg_right hh hφ0.le
    _ ≤ (C*(3*B x))*x := mul_le_mul_of_nonneg_left hφ hnonneg
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordFactorization
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical finite prime-factor decomposition for the Ford coordinates. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma fordPrime_eq_get {n i : ℕ} (hi : i < n.primeFactorsList.length) :
    fordPrime n i = n.primeFactorsList.reverse[i]'(by simpa using hi) := by
  unfold fordPrime
  rw [show n.primeFactorsList.reverse[i]? = some (n.primeFactorsList.reverse[i]'(by simpa using hi)) from
    List.getElem?_eq_getElem _]
  rfl

lemma fordPrime_prime {n i : ℕ} (hi : i < n.primeFactorsList.length) : (fordPrime n i).Prime := by
  rw [fordPrime_eq_get hi]
  exact Nat.prime_of_mem_primeFactorsList (List.mem_reverse.mp (List.getElem_mem _))

lemma fordPrime_antitone {n i j : ℕ} (hi : i < n.primeFactorsList.length)
    (hj : j < n.primeFactorsList.length) (hij : i ≤ j) : fordPrime n j ≤ fordPrime n i := by
  rw [fordPrime_eq_get hi,fordPrime_eq_get hj]
  exact (Nat.primeFactorsList_sorted n).reverse.getElem_ge_getElem_of_le hij

lemma fordCofactor_pos (n k : ℕ) : 0 < fordCofactor n k := by
  apply List.prod_pos
  intro p hp
  exact (Nat.prime_of_mem_primeFactorsList (List.mem_reverse.mp (List.mem_of_mem_drop hp))).pos

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ThirdPrimeSize
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complement of the two-coordinate exception has a small third prime. -/
noncomputable section
namespace TotientAsymptotic

lemma ford_coordinate_antitone (n : ℕ) {i j : ℕ} (hij : i ≤ j) :
    fordPrimeCoordinate n j ≤ fordPrimeCoordinate n i := by
  by_cases hj : j < n.primeFactorsList.length
  · have hi : i < n.primeFactorsList.length := by omega
    have hp := fordPrime_prime hj
    have horder := fordPrime_antitone hi hj hij
    have hB : primeDoubleLog n j ≤ primeDoubleLog n i :=
      Real.log_le_log (Real.log_pos (by exact_mod_cast hp.one_lt))
        (Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast horder))
    exact max_le_max le_rfl hB
  · have he : fordPrime n j=1 := by
      unfold fordPrime
      rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hj)]
      rfl
    simp only [fordPrimeCoordinate,primeDoubleLog,he,Nat.cast_one,Real.log_one,Real.log_zero,max_self]
    exact le_max_left _ _

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CoordinateDeviationExponent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical decay rate used for the exceptional-value estimate. -/
noncomputable section
namespace TotientAsymptotic

lemma coordinate_decay_bounds {ω : ℝ} {k : ℕ} (hω : 0 ≤ ω) (hω1 : ω ≤ 1) :
    0 ≤ coordinateDecay ω k ∧ coordinateDecay ω k ≤ 1/4 ∧
      coordinateDecay ω k ≤ ω/2 := by
  have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg _
  have hp : 1 ≤ ((k:ℝ)+2)^6 := one_le_pow₀ (by linarith)
  have hd : 0 < 12000000*((k:ℝ)+2)^6 := by positivity
  have hsq : ω^2 ≤ ω := by nlinarith
  have hsq1 : ω^2 ≤ 1 := by nlinarith
  refine ⟨by unfold coordinateDecay; positivity,?_,?_⟩
  · apply (div_le_iff₀ hd).mpr
    nlinarith
  · apply (div_le_iff₀ hd).mpr
    have hh := mul_le_mul_of_nonneg_left hp hω
    nlinarith

lemma coordinate_decay_pos {ω : ℝ} (hω : 0 < ω) (k : ℕ) :
    0 < coordinateDecay ω k := by unfold coordinateDecay; positivity

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordCofactorStep
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact removal of the ordered largest primes, including short factorizations. -/
noncomputable section
namespace TotientAsymptotic

lemma fordPrime_pos (n k : ℕ) : 0 < fordPrime n k := by
  by_cases hk : k < n.primeFactorsList.length
  · exact (fordPrime_prime hk).pos
  · unfold fordPrime
    rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hk)]
    norm_num

lemma fordCofactor_step (n k : ℕ) :
    fordCofactor n k = fordPrime n k * fordCofactor n (k+1) := by
  by_cases hk : k < n.primeFactorsList.length
  · unfold fordCofactor
    rw [List.drop_eq_getElem_cons (by simpa using hk),List.prod_cons,fordPrime_eq_get hk]
  · have hl : n.primeFactorsList.length ≤ k := Nat.le_of_not_gt hk
    have h0 : n.primeFactorsList.reverse.drop k = [] := List.drop_eq_nil_iff.mpr (by simpa using hl)
    have h1 : n.primeFactorsList.reverse.drop (k+1) = [] :=
      List.drop_eq_nil_iff.mpr (by simp only [List.length_reverse]; omega)
    have hp : fordPrime n k=1 := by
      unfold fordPrime
      rw [List.getElem?_eq_none (by simpa using hl)]
      rfl
    simp only [fordCofactor,h0,h1,List.prod_nil,hp,one_mul]

lemma fordCofactor_zero {n : ℕ} (hn : 0 < n) : fordCofactor n 0=n := by
  simp only [fordCofactor,List.drop_zero,List.prod_reverse,Nat.prod_primeFactorsList hn.ne']

lemma ford_first_two_factorization {n : ℕ} (hn : 0 < n) :
    n=fordPrime n 0*fordPrime n 1*fordCofactor n 2 := by
  calc
    n = fordCofactor n 0 := (fordCofactor_zero hn).symm
    _ = _ := by
      rw [fordCofactor_step n 0,fordCofactor_step n 1]
      simp only [Nat.reduceAdd]
      ring

lemma fordPrime_le_first (n k : ℕ) : fordPrime n k ≤ fordPrime n 0 := by
  by_cases hk : k < n.primeFactorsList.length
  · exact fordPrime_antitone (by omega) hk (Nat.zero_le k)
  · have hp : fordPrime n k=1 := by
      unfold fordPrime
      rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hk)]
      rfl
    rw [hp]
    exact fordPrime_pos n 0

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordCofactorCoordinates
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing an ordered prime prefix shifts all remaining Ford coordinates. -/
noncomputable section
namespace TotientAsymptotic

lemma fordCofactor_primeFactorsList (n k : ℕ) :
    (fordCofactor n k).primeFactorsList.reverse = n.primeFactorsList.reverse.drop k := by
  let l := n.primeFactorsList.reverse.drop k
  have hprime : ∀ p ∈ l,p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primeFactorsList (List.mem_reverse.mp (List.mem_of_mem_drop hp))
  have hp := Nat.primeFactorsList_unique (n:=fordCofactor n k) (l:=l) rfl hprime
  have hrev : n.primeFactorsList.reverse.SortedGE := (Nat.primeFactorsList_sorted n).reverse
  have hs : l.SortedGE := (hrev.pairwise.sublist (List.drop_sublist k _)).sortedGE
  have ht := (Nat.primeFactorsList_sorted (fordCofactor n k)).reverse
  exact (hp.trans (List.reverse_perm _).symm).eq_of_sortedGE hs ht |>.symm

lemma fordCofactor_prime (n k i : ℕ) :
    fordPrime (fordCofactor n k) i = fordPrime n (k+i) := by
  unfold fordPrime
  rw [fordCofactor_primeFactorsList,List.getElem?_drop]

lemma fordCofactor_coordinate (n k i : ℕ) :
    fordPrimeCoordinate (fordCofactor n k) i = fordPrimeCoordinate n (k+i) := by
  simp only [fordPrimeCoordinate,primeDoubleLog,fordCofactor_prime]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FailedRowCofactor
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The failed original row is the first row of its actual residual preimage. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma fordRowSum_cofactor {n L j : ℕ} (hjL : j ≤ L) :
    fordRowSum L (fordPrimeCoordinate n) j =
      ∑ i : Fin (L-j), a (i.val+1)*fordPrimeCoordinate (fordCofactor n j) (i.val+1) := by
  symm
  unfold fordRowSum
  apply Finset.sum_bij (fun i _ => j+i.val+1)
  · intro i _
    exact Finset.mem_Icc.mpr (by have := i.isLt; omega)
  · intro i _ k _ hik
    apply Fin.ext
    omega
  · intro r hr
    have hr := Finset.mem_Icc.mp hr
    refine ⟨⟨r-j-1,by omega⟩,Finset.mem_univ _,?_⟩
    simp only
    omega
  · intro i _
    rw [fordCofactor_coordinate]
    have he : j+i.val+1-j=i.val+1 := by omega
    rw [he]
    congr 2

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_QuarterPowerBudget
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary logarithmic budgets at a power-four-thirds threshold. -/
noncomputable section
namespace TotientAsymptotic

lemma logarithm_square_quarter_bound {b : ℝ} (hb : 1 ≤ b) :
    (Real.log (b+4))^2 ≤ 320*b^(1/4:ℝ) := by
  have hb0 : 0 < b := by linarith
  have hl : 0 ≤ Real.log (b+4) := Real.log_nonneg (by linarith)
  have hlog := Real.log_le_rpow_div (show 0 ≤ b+4 by linarith)
    (by norm_num : (0:ℝ)<1/8)
  have hq : ((b+4)^(1/8:ℝ))^2=(b+4)^(1/4:ℝ) := by
    rw [pow_two,← Real.rpow_add (by linarith : 0 < b+4)]
    norm_num
  have hp := Real.rpow_nonneg (show 0 ≤ b+4 by linarith) (1/8:ℝ)
  have hs : (Real.log (b+4))^2 ≤ 64*(b+4)^(1/4:ℝ) := by
    norm_num at hlog
    nlinarith only [hlog,hq,hl,hp]
  have ht : (b+4)^(1/4:ℝ) ≤ 5*b^(1/4:ℝ) := by
    calc
      _ ≤ (5*b)^(1/4:ℝ) := Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
      _ = (5:ℝ)^(1/4:ℝ)*b^(1/4:ℝ) := Real.mul_rpow (by norm_num) hb0.le
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_self_of_one_le (by norm_num : (1:ℝ)≤5) (by norm_num))
        (Real.rpow_nonneg hb0.le _)
  linarith only [hs,ht]

lemma logarithm_budget_quarter_bound {b F : ℝ} (hb : 1 ≤ b) (hF : 0 ≤ F) :
    100*(Real.log (b+4)+F+30)^2 ≤ (10000*(F+31)^2)*b^(1/4:ℝ) := by
  have hlog := logarithm_square_quarter_bound hb
  have hs := Real.one_le_rpow hb (by norm_num : (0:ℝ)≤1/4)
  have hsum : (Real.log (b+4)+F+30)^2 ≤ 2*(Real.log (b+4))^2+2*(F+30)^2 := by
    nlinarith only [sq_nonneg (Real.log (b+4)-(F+30))]
  have hc : 64000+200*(F+30)^2 ≤ 10000*(F+31)^2 := by
    nlinarith only [hF,sq_nonneg F]
  have hmul := mul_le_mul_of_nonneg_left hs (sq_nonneg (F+30))
  have hfinal := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (by linarith : 0 ≤ b) (1/4:ℝ))
  nlinarith only [hlog,hsum,hmul,hfinal]

lemma four_thirds_threshold_budget {b F δ : ℝ} (hb : 1 ≤ b) (hF : 0 ≤ F) (hδ : 0 < δ)
    (hthreshold : ((10000*(F+31)^2)/δ)^(4/3:ℝ) ≤ b) :
    100*(Real.log (b+4)+F+30)^2 ≤ δ*b := by
  have hb0 : 0 < b := by linarith
  have hK : 0 ≤ 10000*(F+31)^2 := by positivity
  have hs : (10000*(F+31)^2)/δ ≤ b^(3/4:ℝ) := by
    have hh := Real.rpow_le_rpow
      (Real.rpow_nonneg (div_nonneg hK hδ.le) (4/3:ℝ)) hthreshold
      (by norm_num : (0:ℝ)≤3/4)
    rw [← Real.rpow_mul (div_nonneg hK hδ.le)] at hh
    norm_num at hh
    exact hh
  have hc : 10000*(F+31)^2 ≤ δ*b^(3/4:ℝ) := by
    have hh := (div_le_iff₀ hδ).mp hs
    linarith only [hh]
  have hm := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hb0.le (1/4:ℝ))
  have he : δ*b^(3/4:ℝ)*b^(1/4:ℝ)=δ*b := by
    rw [mul_assoc,← Real.rpow_add hb0]
    norm_num
  exact (logarithm_budget_quarter_bound hb hF).trans (by simpa only [he] using hm)

lemma four_thirds_threshold_tail {b F δ : ℝ} (hb : 1 ≤ b) (hF : 0 ≤ F)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hthreshold : ((10000*(F+31)^2)/δ)^(4/3:ℝ) ≤ b) :
    δ⁻¹ ≤ Real.exp (δ*b) := by
  have hK : 1 ≤ 10000*(F+31)^2 := by nlinarith only [hF,sq_nonneg F]
  have hratio : δ⁻¹ ≤ (10000*(F+31)^2)/δ := by
    simpa only [one_div] using div_le_div_of_nonneg_right hK hδ.le
  have hi : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).mpr hδ1
  have hr : 1 ≤ (10000*(F+31)^2)/δ := hi.trans hratio
  have hp : (10000*(F+31)^2)/δ ≤ ((10000*(F+31)^2)/δ)^(4/3:ℝ) := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hr (by norm_num : (1:ℝ)≤4/3))
  have hib : δ⁻¹ ≤ b := hratio.trans (hp.trans hthreshold)
  have hlog : Real.log (δ⁻¹) ≤ Real.log (b+4) :=
    Real.log_le_log (inv_pos.mpr hδ) (by linarith only [hib])
  have hl : 0 ≤ Real.log (b+4) := Real.log_nonneg (by linarith)
  have hbudget := four_thirds_threshold_budget hb hF hδ hthreshold
  have hs : Real.log (b+4) ≤ 100*(Real.log (b+4)+F+30)^2 := by
    nlinarith only [hl,hF,sq_nonneg (Real.log (b+4)),sq_nonneg F]
  exact (Real.log_le_iff_le_exp (inv_pos.mpr hδ)).mp (hlog.trans (hs.trans hbudget))

lemma row_mass_cutoff_height_bounds {F δ ω : ℝ} (hF : 0 ≤ F)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hδω : 64000000*δ ≤ ω^2) :
    10000 ≤ rowMassCutoffHeight F δ ∧
    (8000/ω)^2 ≤ rowMassCutoffHeight F δ ∧
    max 300000000 (((10000*(F+31)^2)/δ)^(4/3:ℝ)) ≤ rowMassCutoffHeight F δ-1 ∧
    4 ≤ (ω/2)*rowMassCutoffHeight F δ ∧
    δ⁻¹ ≤ Real.exp (δ*rowMassCutoffHeight F δ) := by
  let R := ((10000*(F+31)^2)/δ)^(4/3:ℝ)
  have hK : 1 ≤ 10000*(F+31)^2 := by nlinarith only [hF,sq_nonneg F]
  have hi : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).mpr hδ1
  have hir : δ⁻¹ ≤ (10000*(F+31)^2)/δ := by
    simpa only [one_div] using div_le_div_of_nonneg_right hK hδ.le
  have hr : 1 ≤ (10000*(F+31)^2)/δ := hi.trans hir
  have hR : (10000*(F+31)^2)/δ ≤ R := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hr (by norm_num : (1:ℝ)≤4/3)
  have hR1 : 1 ≤ R := hr.trans hR
  have hdR : 1 ≤ δ*R := by
    have hh := mul_le_mul_of_nonneg_left (hir.trans hR) hδ.le
    simpa only [mul_inv_cancel₀ hδ.ne'] using hh
  have hb : rowMassCutoffHeight F δ=1000000000*R := rfl
  have hdb : 1000000000 ≤ δ*rowMassCutoffHeight F δ := by
    rw [hb]
    nlinarith only [hdR]
  have hb0 : 0 ≤ rowMassCutoffHeight F δ := by rw [hb]; positivity
  have hwb : 64000000 ≤ ω^2*rowMassCutoffHeight F δ := by
    have hh := mul_le_mul_of_nonneg_right hδω hb0
    nlinarith only [hh,hdb]
  have hhead : (8000/ω)^2 ≤ rowMassCutoffHeight F δ := by
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hω)).mpr
    nlinarith only [hwb]
  have hωsq : ω^2 ≤ ω := by nlinarith only [hω,hω1]
  have hlinear := mul_le_mul_of_nonneg_right hωsq hb0
  have hthreshold : R ≤ rowMassCutoffHeight F δ-1 := by rw [hb]; linarith only [hR1]
  refine ⟨by rw [hb]; linarith only [hR1],hhead,
    max_le (by rw [hb]; linarith only [hR1]) hthreshold,
    by nlinarith only [hlinear,hwb],?_⟩
  exact four_thirds_threshold_tail (by rw [hb]; linarith only [hR1]) hF hδ hδ1
    (hthreshold.trans (by linarith))

lemma row_mass_cutoff_log_bound {F δ : ℝ} (hF : 0 ≤ F)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Real.log (rowMassCutoffHeight F δ+4) ≤ Real.log 2000000000+
      (4/3:ℝ)*(Real.log (10000*(F+31)^2)-Real.log δ) := by
  have hK : 1 ≤ 10000*(F+31)^2 := by nlinarith only [hF,sq_nonneg F]
  have hr : 1 ≤ (10000*(F+31)^2)/δ :=
    (le_div_iff₀ hδ).mpr (by linarith only [hK,hδ1])
  have hR : 1 ≤ ((10000*(F+31)^2)/δ)^(4/3:ℝ) :=
    Real.one_le_rpow hr (by norm_num)
  have hp : 0 < ((10000*(F+31)^2)/δ)^(4/3:ℝ) := by positivity
  have hle : rowMassCutoffHeight F δ+4 ≤
      2000000000*((10000*(F+31)^2)/δ)^(4/3:ℝ) := by
    unfold rowMassCutoffHeight
    linarith only [hR]
  calc
    _ ≤ Real.log (2000000000*((10000*(F+31)^2)/δ)^(4/3:ℝ)) :=
      Real.log_le_log (by unfold rowMassCutoffHeight; positivity) hle
    _ = _ := by
      rw [Real.log_mul (by norm_num : (2000000000:ℝ)≠0) hp.ne',Real.log_rpow
        (div_pos (by linarith only [hK]) hδ),Real.log_div (by linarith only [hK]) hδ.ne']

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FailedRowPrefix
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual prime prefix before a first failed row belongs to the unbanded simplex. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma fordRowSum_truncate {K L j : ℕ} (hKL : K ≤ L) (u : ℕ → ℝ)
    (hu : ∀ r, 0 ≤ u r) : fordRowSum K u j ≤ fordRowSum L u j := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro r hr
    have hr := Finset.mem_Icc.mp hr
    exact Finset.mem_Icc.mpr ⟨hr.1,hr.2.trans hKL⟩
  · intro r hr _
    have hr := Finset.mem_Icc.mp hr
    exact mul_nonneg (a_pos (by omega)).le (hu r)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FailedRowCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit residual cutoffs satisfying every first-failed-row mass budget. -/
noncomputable section
namespace TotientAsymptotic

lemma failed_row_cutoff_loglog (F ω : ℝ) (k : ℕ) :
    B (failedRowCutoff F ω k)=rowMassCutoffHeight F (coordinateDecay (ω/4) k) := by
  simp only [B,failedRowCutoff,Real.log_exp]

lemma failed_row_cutoff_budget {F ω : ℝ} (hF : 0 ≤ F) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (k : ℕ) : FailedRowMassBudget F ω (failedRowCutoff F ω k) k := by
  let δ := coordinateDecay (ω/4) k
  let b := rowMassCutoffHeight F δ
  have hδ : 0 < δ := coordinate_decay_pos (by linarith) k
  have hδ1 : δ ≤ 1 :=
    (coordinate_decay_bounds (k:=k) (by linarith : 0 ≤ ω/4) (by linarith : ω/4 ≤ 1)).2.1.trans
      (by norm_num)
  have hp : 1 ≤ ((k:ℝ)+2)^6 := one_le_pow₀ (by have := Nat.cast_nonneg (α:=ℝ) k; linarith)
  have hδω : 64000000*δ ≤ ω^2 := by
    have hd : 12000000 ≤ 12000000*((k:ℝ)+2)^6 := by nlinarith only [hp]
    have hh := div_le_div_of_nonneg_left (sq_nonneg (ω/4)) (by norm_num : (0:ℝ)<12000000) hd
    change δ ≤ (ω/4)^2/12000000 at hh
    have he : (ω/4)^2/12000000=ω^2/192000000 := by ring
    rw [he] at hh
    nlinarith only [hh,sq_nonneg ω]
  obtain ⟨hb,hhead,hthreshold,hlarge,hinv⟩ := row_mass_cutoff_height_bounds hF hδ hδ1 hω hω1 hδω
  change 10000 ≤ b at hb
  have hBU : B (failedRowCutoff F ω k)=b := failed_row_cutoff_loglog F ω k
  have hexp := Real.add_one_le_exp b
  have hexpexp := Real.add_one_le_exp (Real.exp b)
  have hU : 512 ≤ failedRowCutoff F ω k := by
    change 512 ≤ Real.exp (Real.exp b)
    linarith only [hb,hexp,hexpexp]
  have hUexp : 2*Real.exp (Real.exp 1) ≤ failedRowCutoff F ω k := by
    have hlog : Real.log (2*Real.exp (Real.exp 1)) ≤ Real.exp b := by
      rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (Real.exp_ne_zero _),Real.log_exp]
      have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
      linarith only [hl2,Real.exp_one_lt_three,hb,hexp]
    change 2*Real.exp (Real.exp 1) ≤ Real.exp (Real.exp b)
    exact (Real.log_le_iff_le_exp (by positivity)).mp hlog
  unfold FailedRowMassBudget
  rw [hBU]
  exact ⟨hω,hω1,hU,hUexp,hb,hhead,hthreshold,hlarge,hinv⟩

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RowCutoffModel
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The size of the explicit residual cutoff for Ford's exponential row slack. -/
noncomputable section
namespace TotientAsymptotic

lemma row_model_decay_bounds {t : ℝ} (ht : 0 ≤ t) :
    0 < rowModelDecay t ∧ rowModelDecay t ≤ 1 := by
  have he : Real.exp (-t/40) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hp : 1 ≤ (t+2)^6 := one_le_pow₀ (by linarith)
  constructor
  · unfold rowModelDecay
    positivity
  · unfold rowModelDecay
    apply (div_le_iff₀ (by positivity : 0 < 12000000*(t+2)^6)).mpr
    have hx : 0 ≤ Real.exp (-t/40)/40000 := by positivity
    have hx1 : Real.exp (-t/40)/40000 ≤ 1 := by linarith
    nlinarith only [hx,hx1,hp]

lemma row_model_decay_log {t : ℝ} (ht : 0 ≤ t) :
    Real.log (rowModelDecay t) =
      -t/20-2*Real.log 40000-Real.log 12000000-6*Real.log (t+2) := by
  unfold rowModelDecay
  rw [Real.log_div (by positivity) (by positivity),Real.log_pow,
    Real.log_div (Real.exp_ne_zero _) (by norm_num),Real.log_exp,
    Real.log_mul (by norm_num) (by positivity),Real.log_pow]
  ring

lemma row_model_constant_nonneg {F : ℝ} (hF : 0 ≤ F) : 0 ≤ rowModelConstant F := by
  have hK : 1 ≤ 10000*(F+31)^2 := by nlinarith only [hF,sq_nonneg F]
  have h0 := Real.log_nonneg hK
  have h1 := Real.log_nonneg (by norm_num : (1:ℝ)≤2000000000)
  have h2 := Real.log_nonneg (by norm_num : (1:ℝ)≤40000)
  have h3 := Real.log_nonneg (by norm_num : (1:ℝ)≤12000000)
  have h4 := Real.log_nonneg (by norm_num : (1:ℝ)≤24000)
  unfold rowModelConstant
  positivity

lemma row_model_cutoff_log_bound {F t : ℝ} (hF : 0 ≤ F) (ht : 0 ≤ t) :
    0 ≤ Real.log (rowMassCutoffHeight F (rowModelDecay t)+4) ∧
    Real.log (rowMassCutoffHeight F (rowModelDecay t)+4) ≤
      (67/1000:ℝ)*t+rowModelConstant F := by
  have hd := row_model_decay_bounds ht
  have hbound := row_mass_cutoff_log_bound hF hd.1 hd.2
  rw [row_model_decay_log ht] at hbound
  have hlog : Real.log (t+2) ≤ t/24000+Real.log 24000+1 := by
    have hh := Real.log_le_sub_one_of_pos (by positivity : 0 < (t+2)/24000)
    rw [Real.log_div (by linarith : t+2≠0) (by norm_num)] at hh
    linarith only [hh]
  have hb0 : 0 ≤ rowMassCutoffHeight F (rowModelDecay t) := by
    unfold rowMassCutoffHeight
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (div_nonneg (by positivity) hd.1.le) _)
  refine ⟨Real.log_nonneg (by linarith only [hb0]),?_⟩
  unfold rowModelConstant
  linarith only [hbound,hlog]

lemma row_model_mass_exponent_bound {F t : ℝ} (hF : 0 ≤ F) (ht : 0 ≤ t) :
    10*(Real.log (rowMassCutoffHeight F (rowModelDecay t)+4))^2 ≤
      t^2/21+210*(rowModelConstant F)^2 := by
  obtain ⟨hL,hbound⟩ := row_model_cutoff_log_bound hF ht
  have hC := row_model_constant_nonneg hF
  have hsq : (Real.log (rowMassCutoffHeight F (rowModelDecay t)+4))^2 ≤
      ((67/1000:ℝ)*t+rowModelConstant F)^2 := by nlinarith only [hL,hbound,hC,ht]
  have hy := sq_nonneg ((67/1000:ℝ)*t-20*rowModelConstant F)
  nlinarith only [hsq,hy,sq_nonneg t]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ProjectedGaussian
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The projected simplex factor absorbs the complete residual mass. -/
noncomputable section
namespace TotientAsymptotic

lemma projected_gaussian_bound {J r : ℝ} (hJ : 0 < J) (hr : 0 < r)
    (hsmall : r ≤ Real.exp (-3/5:ℝ)) (k : ℕ) :
    J^(k+1)*r^((k+1)*k/2)*Real.exp ((k:ℝ)^2/21) ≤
      Real.exp (105*(Real.log J)^2+Real.log J)*Real.exp (-(k:ℝ)^2/4) := by
  let n := (k+1)*k/2
  have hn : n*2=(k+1)*k := Nat.div_mul_cancel (by
    simpa only [Nat.mul_comm] using Nat.two_dvd_mul_add_one k)
  have hnR := congrArg (fun a : ℕ => (a:ℝ)) hn
  norm_num only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at hnR
  have hlog := Real.log_le_log hr hsmall
  rw [Real.log_exp] at hlog
  have hlogn := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg n : (0:ℝ)≤n)
  have hJexp : J^(k+1)=Real.exp (((k:ℝ)+1)*Real.log J) := by
    simpa only [Nat.cast_add,Nat.cast_one,Real.exp_log hJ] using
      (Real.exp_nat_mul (Real.log J) (k+1)).symm
  have hrexp : r^n=Real.exp ((n:ℝ)*Real.log r) := by
    simpa only [Real.exp_log hr] using (Real.exp_nat_mul (Real.log r) n).symm
  change J^(k+1)*r^n*Real.exp ((k:ℝ)^2/21) ≤ _
  rw [hJexp,hrexp,← Real.exp_add,← Real.exp_add,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hy := sq_nonneg ((k:ℝ)-210*Real.log J)
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith only [hlogn,hnR,hy,hk]

lemma projected_row_mass_bound {J r F : ℝ} (hJ : 0 < J) (hr : 0 < r)
    (hsmall : r ≤ Real.exp (-3/5:ℝ)) (hF : 0 ≤ F) (k : ℕ) :
    J^(k+1)*r^((k+1)*k/2)*
      Real.exp (10*(Real.log (rowMassCutoffHeight F (rowModelDecay k)+4))^2) ≤
    Real.exp (210*(rowModelConstant F)^2+105*(Real.log J)^2+Real.log J)*
      Real.exp (-(k:ℝ)^2/4) := by
  have hb := Real.exp_le_exp.mpr (row_model_mass_exponent_bound hF (Nat.cast_nonneg k))
  have hfactor : 0 ≤ J^(k+1)*r^((k+1)*k/2) := by positivity
  calc
    _ ≤ J^(k+1)*r^((k+1)*k/2)*
        Real.exp ((k:ℝ)^2/21+210*(rowModelConstant F)^2) :=
      mul_le_mul_of_nonneg_left hb hfactor
    _ = Real.exp (210*(rowModelConstant F)^2)*
        (J^(k+1)*r^((k+1)*k/2)*Real.exp ((k:ℝ)^2/21)) := by
      rw [Real.exp_add]
      ring
    _ ≤ Real.exp (210*(rowModelConstant F)^2)*
        (Real.exp (105*(Real.log J)^2+Real.log J)*Real.exp (-(k:ℝ)^2/4)) :=
      mul_le_mul_of_nonneg_left (projected_gaussian_bound hJ hr hsmall k) (Real.exp_pos _).le
    _ = _ := by rw [← mul_assoc,← Real.exp_add]; congr 2; ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FirstFailedRowBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete Gaussian count for any fixed first failed row after the head. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem first_failed_row_bound : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ x : ℝ in atTop, ∀ j : ℕ, 1 ≤ j → j ≤ m x →
    ∀ Q : Finset ℕ, ∀ n : ℕ → ℕ,
      (∀ v ∈ Q, 0 < n v ∧ (n v).totient=v ∧
        x^(1/4:ℝ) ≤ fordPrime (n v) 0 ∧ (v:ℝ) ≤ x ∧
        (∀ i < j, fordRowSum (m x) (fordPrimeCoordinate (n v)) i ≤
          xi x i*(if i=0 then B x else fordPrimeCoordinate (n v) i)) ∧
        xi x j*fordPrimeCoordinate (n v) j <
          fordRowSum (m x) (fordPrimeCoordinate (n v)) j) →
      (Q.card:ℝ) ≤ C*(x/Real.log x)*G x (m x)*
        Real.exp (-((m x-j:ℕ):ℝ)^2/4) := by
  obtain ⟨A,F,hA,hF,hcount⟩ := failed_row_count_bound
  obtain ⟨J,hJ,hproj⟩ := uniform_projected_volume_bound fordRenewalInput
  let C := A*Real.exp (210*(rowModelConstant F)^2+105*(Real.log J)^2+Real.log J)
  refine ⟨C,mul_pos hA (Real.exp_pos _),?_⟩
  filter_upwards [hcount,hproj,eventually_gt_atTop (1:ℝ),
    B_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with x hx hp hx1 hB
  intro j hj hjm Q n hQ
  let k := m x-j
  let ω : ℝ := Real.exp (-(k:ℝ)/40)/10000
  have hω : 0 < ω := by dsimp [ω] <;> positivity
  have hω1 : ω ≤ 1 := by
    have he : Real.exp (-(k:ℝ)/40) ≤ 1 := Real.exp_le_one_iff.mpr (by have := Nat.cast_nonneg (α:=ℝ) k; linarith)
    dsimp [ω]
    linarith only [he]
  have hxi : xi x j=1+ω := by dsimp [xi,ω,k] <;> ring
  have hcut := failed_row_cutoff_budget hF.le hω hω1 k
  have hc := hx j hj hjm ω (failedRowCutoff F ω k) hxi hcut Q n hQ
  have hmodel : coordinateDecay (ω/4) k=rowModelDecay k := by
    dsimp [coordinateDecay,rowModelDecay,ω]
    ring
  have hBcut : B (failedRowCutoff F ω k)=rowMassCutoffHeight F (rowModelDecay k) := by
    rw [failed_row_cutoff_loglog,hmodel]
  rw [hBcut] at hc
  have hkm : k+1 ≤ m x := by dsimp [k]; omega
  have hg := (div_le_iff₀ (G_pos hB (m x))).mp (hp (k+1) hkm)
  rw [show m x-(k+1)=j-1 by dsimp [k]; omega] at hg
  have hrho : rho ≤ Real.exp (-3/5:ℝ) := by
    have he : rho=Real.exp (-lam) := by
      simp only [lam,one_div,Real.log_inv,neg_neg,Real.exp_log rho_pos]
    rw [he]
    exact Real.exp_le_exp.mpr (by linarith only [collision_lambda_bounds.1])
  have hmass := projected_row_mass_bound hJ rho_pos hrho hF.le k
  have hbase : 0 ≤ A*(x/Real.log x)*G x (m x) :=
    mul_nonneg (mul_nonneg hA.le (div_nonneg (by linarith) (Real.log_pos hx1).le))
      (G_pos hB _).le
  calc
    _ ≤ A*(x/Real.log x)*G x (j-1)*
        Real.exp (10*(Real.log (rowMassCutoffHeight F (rowModelDecay k)+4))^2) := hc
    _ = (A*(x/Real.log x)*
        Real.exp (10*(Real.log (rowMassCutoffHeight F (rowModelDecay k)+4))^2))*G x (j-1) := by ring
    _ ≤ (A*(x/Real.log x)*
        Real.exp (10*(Real.log (rowMassCutoffHeight F (rowModelDecay k)+4))^2))*
        (J^(k+1)*rho^((k+1)*k/2)*G x (m x)) :=
      mul_le_mul_of_nonneg_left hg (mul_nonneg
        (mul_nonneg hA.le (div_nonneg (by linarith only [hx1]) (Real.log_pos hx1).le))
        (Real.exp_pos _).le)
    _ = (A*(x/Real.log x)*G x (m x))*
        (J^(k+1)*rho^((k+1)*k/2)*
          Real.exp (10*(Real.log (rowMassCutoffHeight F (rowModelDecay k)+4))^2)) := by ring
    _ ≤ (A*(x/Real.log x)*G x (m x))*
        (Real.exp (210*(rowModelConstant F)^2+105*(Real.log J)^2+Real.log J)*
          Real.exp (-(k:ℝ)^2/4)) := mul_le_mul_of_nonneg_left hmass hbase
    _ = _ := by dsimp [C,k] <;> ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_GaussianTail
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Gaussian tails with the same exponent at the first index. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma finite_gaussian_tail (Q : Finset ℕ) (Ψ : ℕ) (hQ : ∀ k ∈ Q, Ψ ≤ k) :
    (∑ k ∈ Q,Real.exp (-(k:ℝ)^2/4)) ≤
      Real.exp (-(Ψ:ℝ)^2/4)/(1-Real.exp (-1/4:ℝ)) := by
  classical
  let q : ℝ := Real.exp (-1/4:ℝ)
  have hq : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hterm (k : ℕ) (hk : k ∈ Q) :
      Real.exp (-(k:ℝ)^2/4) ≤ Real.exp (-(Ψ:ℝ)^2/4)*q^(k-Ψ) := by
    have hsub : (k:ℝ)=(Ψ:ℝ)+(k-Ψ:ℕ) := by
      exact_mod_cast (Nat.add_sub_of_le (hQ k hk)).symm
    have hd : (k-Ψ:ℕ) ≤ ((k-Ψ:ℕ):ℝ)^2 := by
      by_cases hz : k-Ψ=0
      · simp [hz]
      · have hh : (1:ℝ) ≤ (k-Ψ:ℕ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hz)
        nlinarith
    have hΨ : (0:ℝ) ≤ Ψ := Nat.cast_nonneg Ψ
    have hd0 : (0:ℝ) ≤ (k-Ψ:ℕ) := Nat.cast_nonneg _
    have hex : q^(k-Ψ)=Real.exp (-((k-Ψ:ℕ):ℝ)/4) := by
      dsimp [q]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hex,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [hsub,hd,hΨ,hd0]
  have hinj : Set.InjOn (fun k : ℕ => k-Ψ) ↑Q := by
    intro k hk l hl he
    have hkΨ := hQ k hk
    have hlΨ := hQ l hl
    change k-Ψ=l-Ψ at he
    omega
  have hsum : (∑ k ∈ Q,q^(k-Ψ)) ≤ 1/(1-q) := by
    rw [← Finset.sum_image hinj]
    have hs := hasSum_geometric_of_lt_one hq hq1
    simpa only [one_div] using
      (hs.summable.sum_le_tsum _ (fun i _ => pow_nonneg hq i)).trans_eq hs.tsum_eq
  calc
    _ ≤ ∑ k ∈ Q,Real.exp (-(Ψ:ℝ)^2/4)*q^(k-Ψ) := Finset.sum_le_sum hterm
    _ = Real.exp (-(Ψ:ℝ)^2/4)*(∑ k ∈ Q,q^(k-Ψ)) := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-(Ψ:ℝ)^2/4)*(1/(1-q)) :=
      mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le
    _ = _ := by dsimp [q] <;> ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FirstFailedRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing the first-failed-row classes without losing the Gaussian exponent. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma first_failed_row_exists {x : ℝ} {n J : ℕ}
    (h0 : fordRowHolds x n 0)
    (hfail : ∃ j, j ≤ J ∧ ¬fordRowHolds x n j) :
    ∃ j, 1 ≤ j ∧ j ≤ J ∧ FirstFailedRowAt x n j := by
  classical
  let hex : ∃ j, ¬fordRowHolds x n j := by
    obtain ⟨j,_,hj⟩ := hfail
    exact ⟨j,hj⟩
  let j := Nat.find hex
  have hj := Nat.find_spec hex
  change ¬fordRowHolds x n j at hj
  have hj0 : j≠0 := by
    intro he
    exact hj (by simpa only [he] using h0)
  refine ⟨j,by omega,?_,?_,hj⟩
  · obtain ⟨l,hl,he⟩ := hfail
    exact (Nat.find_min' hex he).trans hl
  · intro i hi
    exact Classical.byContradiction (fun h => Nat.find_min hex hi h)

theorem first_failed_rows_tail_bound : ∃ C : ℝ,0 < C ∧
    ∀ᶠ x : ℝ in atTop, ∀ Ψ : ℕ, ∀ Q : Finset ℕ, ∀ n : ℕ → ℕ,
      (∀ v ∈ Q, 0 < n v ∧ (n v).totient=v ∧
        x^(1/4:ℝ) ≤ fordPrime (n v) 0 ∧ (v:ℝ) ≤ x ∧
        ∃ j,1 ≤ j ∧ j ≤ m x-Ψ ∧ FirstFailedRowAt x (n v) j) →
      (Q.card:ℝ) ≤ C*(x/Real.log x)*G x (m x)*Real.exp (-(Ψ:ℝ)^2/4) := by
  classical
  obtain ⟨A,hA,hcount⟩ := first_failed_row_bound
  let q : ℝ := Real.exp (-1/4:ℝ)
  have hq : q < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  refine ⟨A/(1-q),div_pos hA (sub_pos.mpr hq),?_⟩
  filter_upwards [hcount,eventually_gt_atTop (1:ℝ),
    B_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with x hx hx1 hB
  intro Ψ Q n hQ
  let I := Finset.Icc 1 (m x-Ψ)
  let R (j : ℕ) := Q.filter (fun v => FirstFailedRowAt x (n v) j)
  have hcover : Q ⊆ I.biUnion R := by
    intro v hv
    obtain ⟨_,_,_,_,j,hj,hjm,hfirst⟩ := hQ v hv
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_Icc.mpr ⟨hj,hjm⟩,
      Finset.mem_filter.mpr ⟨hv,hfirst⟩⟩
  have hcard : (Q.card:ℝ) ≤ ∑ j ∈ I,((R j).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hrow (j : ℕ) (hj : j ∈ I) : (R j).card ≤
      A*(x/Real.log x)*G x (m x)*Real.exp (-((m x-j:ℕ):ℝ)^2/4) := by
    obtain ⟨hj,hjm⟩ := Finset.mem_Icc.mp hj
    apply hx j hj (hjm.trans (Nat.sub_le _ _)) (R j) n
    intro v hv
    obtain ⟨hv,hfirst⟩ := Finset.mem_filter.mp hv
    obtain ⟨hn,hφ,hhead,hvx,_⟩ := hQ v hv
    refine ⟨hn,hφ,hhead,hvx,hfirst.1,?_⟩
    have hh := not_le.mp hfirst.2
    simpa only [fordRowHolds,ite_eq_right (by omega : j≠0)] using hh
  have hinj : Set.InjOn (fun j => m x-j) ↑I := by
    intro j hj l hl he
    have hjm := (Finset.mem_Icc.mp hj).2
    have hlm := (Finset.mem_Icc.mp hl).2
    change m x-j=m x-l at he
    omega
  have hsum : (∑ j ∈ I,Real.exp (-((m x-j:ℕ):ℝ)^2/4)) ≤
      Real.exp (-(Ψ:ℝ)^2/4)/(1-q) := by
    have he : (∑ k ∈ I.image (fun j => m x-j),Real.exp (-(k:ℝ)^2/4)) =
        ∑ j ∈ I,Real.exp (-((m x-j:ℕ):ℝ)^2/4) := Finset.sum_image hinj
    rw [← he]
    apply finite_gaussian_tail
    intro k hk
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk
    have hjm := (Finset.mem_Icc.mp hj).2
    have hj1 := (Finset.mem_Icc.mp hj).1
    omega
  have hfac : 0 ≤ A*(x/Real.log x)*G x (m x) :=
    mul_nonneg (mul_nonneg hA.le (div_nonneg (by linarith) (Real.log_pos hx1).le)) (G_pos hB _).le
  calc
    _ ≤ ∑ j ∈ I,((R j).card:ℝ) := hcard
    _ ≤ ∑ j ∈ I,A*(x/Real.log x)*G x (m x)*Real.exp (-((m x-j:ℕ):ℝ)^2/4) :=
      Finset.sum_le_sum hrow
    _ = (A*(x/Real.log x)*G x (m x))*(∑ j ∈ I,Real.exp (-((m x-j:ℕ):ℝ)^2/4)) := by
      rw [Finset.mul_sum]
    _ ≤ (A*(x/Real.log x)*G x (m x))*(Real.exp (-(Ψ:ℝ)^2/4)/(1-q)) :=
      mul_le_mul_of_nonneg_left hsum hfac
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RowModelScale
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The row cutoff and decay rate fit below the ambient Ford scale. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma row_model_height_eventually {F : ℝ} (hF : 0 ≤ F) :
    ∀ᶠ t : ℝ in atTop,
      rowMassCutoffHeight F (rowModelDecay t)+4 ≤ Real.exp (t/2) := by
  filter_upwards [eventually_ge_atTop (0:ℝ),
    eventually_ge_atTop (100*(rowModelConstant F+1))] with t ht hlarge
  obtain ⟨_,hlog⟩ := row_model_cutoff_log_bound hF ht
  have hb : 0 < rowMassCutoffHeight F (rowModelDecay t)+4 := by
    unfold rowMassCutoffHeight
    have hd := (row_model_decay_bounds ht).1
    positivity
  have he := Real.exp_le_exp.mpr (show Real.log (rowMassCutoffHeight F (rowModelDecay t)+4) ≤ t/2 by
    linarith only [hlog,hlarge,ht])
  simpa only [Real.exp_log hb] using he

lemma row_model_decay_eventually : ∀ᶠ t : ℝ in atTop,
    Real.exp (-t/2) ≤ rowModelDecay t := by
  let D : ℝ := 2*Real.log 40000+Real.log 12000000+6*(Real.log 24000+1)
  filter_upwards [eventually_ge_atTop (0:ℝ),eventually_ge_atTop (100*(D+1))]
    with t ht hlarge
  have hlog : Real.log (t+2) ≤ t/24000+Real.log 24000+1 := by
    have hh := Real.log_le_sub_one_of_pos (by positivity : 0 < (t+2)/24000)
    rw [Real.log_div (by linarith : t+2≠0) (by norm_num)] at hh
    linarith only [hh]
  have he : -t/2 ≤ Real.log (rowModelDecay t) := by
    rw [row_model_decay_log ht]
    dsimp [D] at hlarge
    linarith only [hlog,hlarge,ht]
  simpa only [Real.exp_log (row_model_decay_bounds ht).1] using Real.exp_le_exp.mpr he

lemma row_model_quadratic_eventually : ∀ᶠ t : ℝ in atTop,
    t^2/4 ≤ Real.exp (t/10) := by
  have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2:ℝ) (1/10:ℝ) (by norm_num)).eventually
    (eventually_lt_nhds (by norm_num : (0:ℝ)<4))
  filter_upwards [hh] with t ht
  have hpow : t^(2:ℝ)=t^2 := Real.rpow_natCast t 2
  have hdiv : t^2/Real.exp (t/10) ≤ 4 := by
    change t^(2:ℝ)*Real.exp (-(1/10:ℝ)*t)<4 at ht
    rw [hpow,show -(1/10:ℝ)*t=-(t/10) by ring,Real.exp_neg] at ht
    simpa only [div_eq_mul_inv] using ht.le
  have hb := (div_le_iff₀ (Real.exp_pos (t/10))).mp hdiv
  linarith only [hb]

lemma row_model_ambient_budget {F : ℝ} (hF : 0 ≤ F) :
    ∀ᶠ t : ℝ in atTop, ∀ b : ℝ,Real.exp ((3/5:ℝ)*t) ≤ b →
      rowMassCutoffHeight F (rowModelDecay t)+4 ≤ b ∧
      t^2/4 ≤ rowModelDecay t*b := by
  filter_upwards [row_model_height_eventually hF,row_model_decay_eventually,
    row_model_quadratic_eventually,eventually_ge_atTop (0:ℝ)] with t hh hd hq ht
  intro b hb
  refine ⟨hh.trans ((Real.exp_le_exp.mpr (by linarith)).trans hb),?_⟩
  have hm := mul_le_mul hd hb (Real.exp_pos _).le (row_model_decay_bounds ht).1.le
  have he : Real.exp (-t/2)*Real.exp ((3/5:ℝ)*t)=Real.exp (t/10) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at hm
  exact hq.trans hm

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordDimensionScale
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary lower bounds for the dimension and volume normalization. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma dimension_exponential_lower : ∀ᶠ x : ℝ in atTop,
    Real.exp ((3/5:ℝ)*(m x:ℝ)) ≤ B x := by
  filter_upwards [theta_eventually_mem,
    B_tendsto.eventually (eventually_ge_atTop (Real.exp 1))] with x hθ hB
  have hbpos : 0 < B x := (Real.exp_pos 1).trans_le hB
  have hlogB : 1 ≤ Real.log (B x) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hB
  have hloglog : 0 ≤ Real.log (Real.log (B x)) := Real.log_nonneg hlogB
  have hm : (m x:ℝ) ≤ psi (B x) := by
    have hh := hθ.1
    change 0 ≤ psi (B x)-(m x:ℝ) at hh
    linarith only [hh]
  have hm' := (le_div_iff₀ lam_pos).mp hm
  have hLam := mul_le_mul_of_nonneg_right collision_lambda_bounds.1.le
    (Nat.cast_nonneg (m x) : (0:ℝ) ≤ m x)
  have he : (3/5:ℝ)*(m x:ℝ) ≤ Real.log (B x) := by
    change (m x:ℝ)*lam ≤ Real.log (B x)-Real.log (Real.log (B x)) at hm'
    nlinarith only [hm',hLam,hloglog]
  simpa only [Real.exp_log hbpos] using Real.exp_le_exp.mpr he

lemma central_volume_one_le : ∀ᶠ x : ℝ in atTop,1 ≤ G x (m x) := by
  obtain ⟨J,hJ,hproj⟩ := uniform_projected_volume_bound fordRenewalInput
  have hsmall := ((summable_projectedEnvelope hJ).tendsto_atTop_zero.comp m_tendsto).eventually
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hproj,hsmall,B_tendsto.eventually (eventually_gt_atTop (0:ℝ))]
    with x hx hs hB
  change projectedEnvelope J (m x)<1 at hs
  have hp := hx (m x) le_rfl
  rw [Nat.sub_self,show G x 0=1 by simp [G]] at hp
  change 1/G x (m x) ≤ projectedEnvelope J (m x) at hp
  have hh := (div_le_iff₀ (G_pos hB (m x))).mp hp
  have hl := mul_le_mul_of_nonneg_right hs.le (G_pos hB (m x)).le
  linarith only [hh,hl]

lemma dimension_row_model_budget {F : ℝ} (hF : 0 ≤ F) :
    ∀ᶠ x : ℝ in atTop,
      rowMassCutoffHeight F (rowModelDecay (m x))+4 ≤ B x ∧
      (m x:ℝ)^2/4 ≤ rowModelDecay (m x)*B x := by
  have hm : Tendsto (fun x : ℝ => (m x:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp m_tendsto
  have hbud := hm.eventually (row_model_ambient_budget hF)
  filter_upwards [hbud,dimension_exponential_lower] with x hx hb
  exact hx (B x) hb

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SmallTerminalPrefix
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded terminal coordinate supplies an exact smooth residual split. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma ford_prime_le_exp_exp {n j : ℕ} {t : ℝ} (_ht : 0 ≤ t)
    (hj : fordPrimeCoordinate n j ≤ t) :
    (fordPrime n j:ℝ) ≤ Real.exp (Real.exp t) := by
  by_cases hp : fordPrime n j=1
  · rw [hp,Nat.cast_one]
    exact Real.one_le_exp (Real.exp_pos _).le
  have hp1 : (1:ℝ) < fordPrime n j := by
    exact_mod_cast (show 1 < fordPrime n j from lt_of_le_of_ne (fordPrime_pos n j) (Ne.symm hp))
  have hlog : 0 < Real.log (fordPrime n j:ℝ) := Real.log_pos hp1
  have hh : Real.log (Real.log (fordPrime n j:ℝ)) ≤ t := (le_max_right _ _).trans hj
  have he : Real.log (fordPrime n j:ℝ) ≤ Real.exp t :=
    (Real.log_le_iff_le_exp hlog).mp hh
  exact (Real.log_le_iff_le_exp (zero_lt_one.trans hp1)).mp he

lemma first_small_terminal_exists {n L : ℕ} {t : ℝ}
    (hhead : t < fordPrimeCoordinate n 0) (htail : fordPrimeCoordinate n L ≤ t) :
    ∃ j,1 ≤ j ∧ j ≤ L ∧ t < fordPrimeCoordinate n (j-1) ∧
      fordPrimeCoordinate n j ≤ t := by
  classical
  let h : ∃ j,fordPrimeCoordinate n j ≤ t := ⟨L,htail⟩
  let j := Nat.find h
  have hj := Nat.find_spec h
  change fordPrimeCoordinate n j ≤ t at hj
  have hj0 : j≠0 := by
    intro he
    have hh : fordPrimeCoordinate n 0 ≤ t := by simpa only [he] using hj
    exact (not_lt_of_ge hh) hhead
  refine ⟨j,by omega,Nat.find_min' h htail,?_,hj⟩
  exact lt_of_not_ge (Nat.find_min h (show j-1 < j by omega))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordSimplexRows
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assemble Ford's stated simplex condition from the full row inequalities. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma ford_simplex_of_full_rows {x : ℝ} {Ψ n : ℕ} (hΨ : Ψ < m x)
    (htail : 2 < fordPrimeCoordinate n (m x-Ψ))
    (hcap : fordPrimeCoordinate n 1 ≤ B x)
    (hrows : ∀ i < m x-Ψ,fordRowSum (m x) (fordPrimeCoordinate n) i ≤
      xi x i*(if i=0 then B x else fordPrimeCoordinate n i)) :
    fordSimplexCondition x Ψ n := by
  let J := m x-Ψ
  have hJ : 1 ≤ J := by dsimp [J]; omega
  have hB : 0 ≤ B x := (le_max_left _ _).trans hcap
  refine ⟨htail,?_,?_⟩
  · intro i hi
    obtain ⟨hi1,hiJ⟩ := Finset.mem_Icc.mp hi
    exact ⟨ford_coordinate_antitone n hiJ,(ford_coordinate_antitone n hi1).trans hcap⟩
  · intro i hi
    obtain ⟨_,hiJ⟩ := Finset.mem_Ico.mp hi
    change i < J at hiJ
    by_cases hlast : i+1=J
    · rw [ite_eq_left hlast]
      by_cases hi0 : i=0
      · subst i
        have he : J=1 := by omega
        change fordSimplexCoordinate x n J ≤ xi x 0*fordSimplexCoordinate x n 0
        rw [he]
        change fordPrimeCoordinate n 1 ≤ xi x 0*B x
        exact hcap.trans (by nlinarith only [(xi_bounds x 0).1,hB])
      · have ho := ford_coordinate_antitone n (show i ≤ J by omega)
        have hn : 0 ≤ fordPrimeCoordinate n i := le_max_left _ _
        have hx := (xi_bounds x i).1
        change fordSimplexCoordinate x n J ≤ xi x i*fordSimplexCoordinate x n i
        simp only [fordSimplexCoordinate,ite_eq_right (by omega : J≠0),ite_eq_right hi0]
        exact ho.trans (by nlinarith only [hx,hn])
    · rw [ite_eq_right hlast]
      have he : (∑ r ∈ Finset.Icc (i+1) J,a (r-i)*fordSimplexCoordinate x n r) =
          fordRowSum J (fordPrimeCoordinate n) i := by
        unfold fordRowSum
        apply Finset.sum_congr rfl
        intro r hr
        have hr := Finset.mem_Icc.mp hr
        rw [fordSimplexCoordinate,ite_eq_right (by omega : r≠0)]
      rw [he]
      exact (fordRowSum_truncate (Nat.sub_le _ _) _ (fun _ => le_max_left _ _)).trans (hrows i hiJ)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SecondPrimeBound
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All nonleading prime coordinates lie below the ambient log-log scale. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma ford_second_prime_sq_le {n : ℕ} (hn : 0 < n) : (fordPrime n 1)^2 ≤ n := by
  have ho := fordPrime_le_first n 1
  have hp := Nat.mul_le_mul_right (fordPrime n 1) ho
  have ht := Nat.le_mul_of_pos_right (fordPrime n 0*fordPrime n 1) (fordCofactor_pos n 2)
  rw [← ford_first_two_factorization hn] at ht
  simpa only [pow_two] using hp.trans ht

lemma all_preimages_square_bound : ∀ᶠ x : ℝ in atTop,
    ∀ n : ℕ,0 < n → (n.totient:ℝ) ≤ x → (n:ℝ) ≤ x^2 := by
  obtain ⟨C,hC,hpre⟩ := preimage_loglog_bound
  have hsmall := Real.isLittleO_log_id_atTop.bound (show (0:ℝ)<1/C by positivity)
  filter_upwards [hsmall,eventually_ge_atTop (Real.exp (Real.exp 1)),
    eventually_gt_atTop (1:ℝ)] with x hx hxexp hx1
  have hx0 : 0 < x := by linarith only [hx1]
  have hl : 0 < Real.log x := Real.log_pos hx1
  have hlog : Real.log x ≤ (1/C)*x := (le_abs_self _).trans (by
    simpa only [Real.norm_eq_abs,abs_of_pos hx0,id_eq] using hx)
  have hBx : B x ≤ Real.log x := by
    have hh := Real.log_le_sub_one_of_pos hl
    change Real.log (Real.log x) ≤ Real.log x
    linarith only [hh]
  have hCB : C*B x ≤ x := by
    have hh := mul_le_mul_of_nonneg_left (hBx.trans hlog) hC.le
    simpa only [← mul_assoc,mul_one_div_cancel hC.ne',one_mul] using hh
  intro n hn hφ
  calc
    (n:ℝ) ≤ C*x*B x := hpre x hxexp n hn hφ
    _ = x*(C*B x) := by ring
    _ ≤ x*x := mul_le_mul_of_nonneg_left hCB hx0.le
    _ = x^2 := by ring

lemma all_preimages_second_coordinate : ∀ᶠ x : ℝ in atTop,
    ∀ n : ℕ,0 < n → (n.totient:ℝ) ≤ x → fordPrimeCoordinate n 1 ≤ B x := by
  filter_upwards [all_preimages_square_bound,B_tendsto.eventually (eventually_ge_atTop (0:ℝ)),
    eventually_gt_atTop (1:ℝ)] with x hx hB hx1
  intro n hn hφ
  have hnat : (fordPrime n 1:ℝ)^2 ≤ (n:ℝ) := by exact_mod_cast ford_second_prime_sq_le hn
  have hs : (fordPrime n 1:ℝ)^2 ≤ x^2 := hnat.trans (hx n hn hφ)
  have hprime : (fordPrime n 1:ℝ) ≤ x := by
    nlinarith only [hs,Nat.cast_nonneg (α:=ℝ) (fordPrime n 1),hx1]
  by_cases he : fordPrime n 1=1
  · simpa only [fordPrimeCoordinate,primeDoubleLog,he,Nat.cast_one,Real.log_one,
      Real.log_zero,max_self] using hB
  have hp1 : (1:ℝ) < fordPrime n 1 := by
    exact_mod_cast (show 1 < fordPrime n 1 from lt_of_le_of_ne (fordPrime_pos n 1) (Ne.symm he))
  apply max_le hB
  exact Real.log_le_log (Real.log_pos hp1)
    (Real.log_le_log (zero_lt_one.trans hp1) hprime)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SmallTerminalTail
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing the bounded-terminal classes with the same Gaussian exponent. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem small_terminal_tail_count : ∃ C : ℝ,0 < C ∧
    ∀ᶠ x : ℝ in atTop,∀ Ψ : ℕ,∀ Q : Finset ℕ,∀ n : ℕ → ℕ,
    (∀ v ∈ Q,0 < n v ∧ (n v).totient=v ∧ x^(1/4:ℝ) ≤ fordPrime (n v) 0 ∧
      (v:ℝ) ≤ x ∧ 2 < fordPrimeCoordinate (n v) 0 ∧
      fordPrimeCoordinate (n v) (m x-Ψ) ≤ 2 ∧
      (∀ i ≤ m x-Ψ,fordRowSum (m x) (fordPrimeCoordinate (n v)) i ≤
        xi x i*(if i=0 then B x else fordPrimeCoordinate (n v) i))) →
    (Q.card:ℝ) ≤ C*(x/Real.log x)*G x (m x)*Real.exp (-(Ψ:ℝ)^2/4) := by
  classical
  obtain ⟨A,hA,hcount⟩ := small_terminal_row_count
  let q : ℝ := Real.exp (-1/4:ℝ)
  have hq : q < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  refine ⟨A/(1-q),div_pos hA (sub_pos.mpr hq),?_⟩
  filter_upwards [hcount,eventually_gt_atTop (1:ℝ),
    B_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with x hx hx1 hB
  intro Ψ Q n hQ
  let I := Finset.Icc 1 (m x-Ψ)
  let R (j : ℕ) := Q.filter (fun v => 2 < fordPrimeCoordinate (n v) (j-1) ∧
    fordPrimeCoordinate (n v) j ≤ 2)
  have hcover : Q ⊆ I.biUnion R := by
    intro v hv
    obtain ⟨_,_,_,_,hhead,htail,_⟩ := hQ v hv
    obtain ⟨j,hj,hjL,hprev,hcur⟩ := first_small_terminal_exists hhead htail
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_Icc.mpr ⟨hj,hjL⟩,
      Finset.mem_filter.mpr ⟨hv,hprev,hcur⟩⟩
  have hcard : (Q.card:ℝ) ≤ ∑ j ∈ I,((R j).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hrow (j : ℕ) (hj : j ∈ I) : (R j).card ≤
      A*(x/Real.log x)*G x (m x)*Real.exp (-((m x-j:ℕ):ℝ)^2/4) := by
    obtain ⟨hj,hjL⟩ := Finset.mem_Icc.mp hj
    apply hx j hj (hjL.trans (Nat.sub_le _ _)) (R j) n
    intro v hv
    obtain ⟨hv,hprev,hcur⟩ := Finset.mem_filter.mp hv
    obtain ⟨hn,hφ,hlarge,hvx,_,_,hrows⟩ := hQ v hv
    exact ⟨hn,hφ,hlarge,hvx,hprev,hcur,fun i hi => hrows i (by omega)⟩
  have hinj : Set.InjOn (fun j => m x-j) ↑I := by
    intro j hj l hl he
    have hjm := (Finset.mem_Icc.mp hj).2
    have hlm := (Finset.mem_Icc.mp hl).2
    change m x-j=m x-l at he
    omega
  have hsum : (∑ j ∈ I,Real.exp (-((m x-j:ℕ):ℝ)^2/4)) ≤
      Real.exp (-(Ψ:ℝ)^2/4)/(1-q) := by
    have he : (∑ k ∈ I.image (fun j => m x-j),Real.exp (-(k:ℝ)^2/4)) =
        ∑ j ∈ I,Real.exp (-((m x-j:ℕ):ℝ)^2/4) := Finset.sum_image hinj
    rw [← he]
    apply finite_gaussian_tail
    intro k hk
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk
    have hjm := (Finset.mem_Icc.mp hj).2
    have hj1 := (Finset.mem_Icc.mp hj).1
    omega
  have hfac : 0 ≤ A*(x/Real.log x)*G x (m x) :=
    mul_nonneg (mul_nonneg hA.le (div_nonneg (by linarith) (Real.log_pos hx1).le)) (G_pos hB _).le
  calc
    _ ≤ ∑ j ∈ I,((R j).card:ℝ) := hcard
    _ ≤ ∑ j ∈ I,A*(x/Real.log x)*G x (m x)*Real.exp (-((m x-j:ℕ):ℝ)^2/4) :=
      Finset.sum_le_sum hrow
    _ = (A*(x/Real.log x)*G x (m x))*(∑ j ∈ I,Real.exp (-((m x-j:ℕ):ℝ)^2/4)) := by
      rw [Finset.mul_sum]
    _ ≤ (A*(x/Real.log x)*G x (m x))*(Real.exp (-(Ψ:ℝ)^2/4)/(1-q)) :=
      mul_le_mul_of_nonneg_left hsum hfac
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TopRowCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Failure of the initial Ford simplex row has a uniform Gaussian saving. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem top_row_failure_count : ∃ C : ℝ,0 < C ∧
    ∀ᶠ x : ℝ in atTop, ∀ Ψ : ℕ, Ψ ≤ m x → ∀ Q : Finset ℕ,
      (∀ v ∈ Q,∃ n : ℕ,0 < n ∧ n.totient=v ∧ (v:ℝ) ≤ x ∧
        xi x 0*B x < fordRowSum (m x) (fordPrimeCoordinate n) 0) →
      (Q.card:ℝ) ≤ C*(x/Real.log x)*G x (m x)*Real.exp (-(Ψ:ℝ)^2/4) := by
  obtain ⟨C,F,hC,hF,hcount⟩ := real_coordinate_deviation
  refine ⟨C,hC,?_⟩
  filter_upwards [dimension_row_model_budget hF.le,central_volume_one_le,
    eventually_ge_atTop (512:ℝ),eventually_ge_atTop (2*Real.exp (Real.exp 1)),
    B_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with x hb hG hx hxexp hB
  intro Ψ hΨ Q hQ
  let k := m x
  let ω : ℝ := Real.exp (-(k:ℝ)/40)/10000
  have hω : 0 < ω := by dsimp [ω] <;> positivity
  have hω1 : ω ≤ 1 := by
    have he : Real.exp (-(k:ℝ)/40) ≤ 1 := Real.exp_le_one_iff.mpr
      (by have := Nat.cast_nonneg (α:=ℝ) k; linarith)
    dsimp [ω]
    linarith only [he]
  have hmodel : coordinateDecay (ω/4) k=rowModelDecay k := by
    dsimp [coordinateDecay,rowModelDecay,ω]
    ring
  have hbudget := failed_row_cutoff_budget hF.le hω hω1 k
  obtain ⟨_,_,_,_,_,_,hthreshold,_,_⟩ := hbudget
  rw [failed_row_cutoff_loglog,hmodel] at hthreshold
  have hthreshold' : max 300000000 ((coordinateBudgetConstant F/coordinateDecay (ω/4) k)^(4/3:ℝ)) ≤ B x-1 := by
    rw [hmodel]
    exact hthreshold.trans (by dsimp [k] at *; linarith only [hb.1])
  have hc := hcount x hx hxexp k (ω/4) (by linarith) (by linarith) hthreshold' Q (by
    intro v hv
    obtain ⟨n,hn,hφ,hvx,hrow⟩ := hQ v hv
    refine ⟨⟨n,hn,hφ⟩,hvx,n,hn,hφ,?_⟩
    have hxi : xi x 0=1+ω := by dsimp [xi,ω,k] <;> ring
    rw [hxi] at hrow
    have hsum : fordRowSum (m x) (fordPrimeCoordinate n) 0 =
        ∑ i : Fin k,a (i.val+1)*fordPrimeCoordinate n (i.val+1) := by
      simpa only [Nat.sub_zero,fordCofactor_zero hn] using
        (fordRowSum_cofactor (n:=n) (L:=m x) (j:=0) (Nat.zero_le _))
    rw [hsum] at hrow
    have hh := mul_le_mul_of_nonneg_right (show 1+ω/4 ≤ 1+ω by linarith) hB.le
    exact hh.trans hrow.le)
  have hΨsq : (Ψ:ℝ)^2 ≤ (m x:ℝ)^2 := by
    have hle : (Ψ:ℝ) ≤ m x := by exact_mod_cast hΨ
    nlinarith only [hle,Nat.cast_nonneg (α:=ℝ) Ψ,Nat.cast_nonneg (α:=ℝ) (m x)]
  have hsave : Real.exp (-coordinateDecay (ω/4) k*B x) ≤ Real.exp (-(Ψ:ℝ)^2/4) := by
    apply Real.exp_le_exp.mpr
    rw [hmodel]
    dsimp [k]
    linarith only [hb.2,hΨsq]
  have hx1 : 1 < x := by linarith only [hx]
  have hfac : 0 ≤ C*(x/Real.log x) := mul_nonneg hC.le
    (div_nonneg (by linarith only [hx]) (Real.log_pos hx1).le)
  calc
    _ ≤ C*(x/Real.log x)*Real.exp (-coordinateDecay (ω/4) k*B x) := by
      simpa only [div_eq_mul_inv,mul_assoc] using hc
    _ ≤ C*(x/Real.log x)*Real.exp (-(Ψ:ℝ)^2/4) := mul_le_mul_of_nonneg_left hsave hfac
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hG hfac
      simpa only [mul_one] using mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordStructureCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete unnormalized exceptional-value bound in Ford Theorem 16. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma large_head_coordinate_gt_two : ∀ᶠ x : ℝ in atTop,∀ n : ℕ,
    x^(1/4:ℝ) ≤ fordPrime n 0 → 2 < fordPrimeCoordinate n 0 := by
  filter_upwards [(tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/4)).eventually
    (eventually_gt_atTop (Real.exp (Real.exp 2)))] with x hx
  intro n hn
  by_contra hh
  have hu := ford_prime_le_exp_exp (by norm_num) (le_of_not_gt hh)
  linarith only [hx,hn,hu]

theorem ford_structure_value_count_oai : ∃ C : ℝ,0 < C ∧
    ∀ᶠ x : ℝ in atTop,∀ Ψ : ℕ,Ψ < m x → ∀ Q : Finset ℕ,∀ n : ℕ → ℕ,
    (∀ v ∈ Q,0 < n v ∧ (n v).totient=v ∧ (v:ℝ) ≤ x ∧ ¬fordSimplexCondition x Ψ (n v)) →
    (Q.card:ℝ) ≤ C*(x/Real.log x)*G x (m x)*Real.exp (-(Ψ:ℝ)^2/4) := by
  classical
  obtain ⟨A,hA,hsmall⟩ := small_head_real_gaussian
  obtain ⟨D,hD,htop⟩ := top_row_failure_count
  obtain ⟨E,hE,hfirst⟩ := first_failed_rows_tail_bound
  obtain ⟨F,hF,htail⟩ := small_terminal_tail_count
  refine ⟨A+D+E+F,by positivity,?_⟩
  filter_upwards [hsmall,htop,hfirst,htail,large_head_coordinate_gt_two,all_preimages_second_coordinate]
    with x hs ht hf hu hhead hsecond
  intro Ψ hΨ Q n hQ
  let H := Q.filter (fun v => (fordPrime (n v) 0:ℝ) < x^(1/4:ℝ))
  let T := Q.filter (fun v => ¬fordRowHolds x (n v) 0)
  let Fst := Q.filter (fun v => x^(1/4:ℝ) ≤ fordPrime (n v) 0 ∧
    ∃ j,1 ≤ j ∧ j ≤ m x-Ψ ∧ FirstFailedRowAt x (n v) j)
  let U := Q.filter (fun v => x^(1/4:ℝ) ≤ fordPrime (n v) 0 ∧
    2 < fordPrimeCoordinate (n v) 0 ∧ fordPrimeCoordinate (n v) (m x-Ψ) ≤ 2 ∧
    ∀ i ≤ m x-Ψ,fordRowHolds x (n v) i)
  have hH := hs Ψ hΨ.le H (by
    intro v hv
    obtain ⟨hv,hhead⟩ := Finset.mem_filter.mp hv
    obtain ⟨hn,hφ,hvx,_⟩ := hQ v hv
    exact ⟨⟨n v,hn,hφ⟩,hvx,n v,hn,hφ,hhead⟩)
  have hT := ht Ψ hΨ.le T (by
    intro v hv
    obtain ⟨hv,hbad⟩ := Finset.mem_filter.mp hv
    obtain ⟨hn,hφ,hvx,_⟩ := hQ v hv
    refine ⟨n v,hn,hφ,hvx,?_⟩
    simpa only [fordRowHolds,ite_true, if_true] using not_le.mp hbad)
  have hFst := hf Ψ Fst n (by
    intro v hv
    obtain ⟨hv,hlarge,hfirst⟩ := Finset.mem_filter.mp hv
    obtain ⟨hn,hφ,hvx,_⟩ := hQ v hv
    exact ⟨hn,hφ,hlarge,hvx,hfirst⟩)
  have hU := hu Ψ U n (by
    intro v hv
    obtain ⟨hv,hlarge,hhead,htail,hrows⟩ := Finset.mem_filter.mp hv
    obtain ⟨hn,hφ,hvx,_⟩ := hQ v hv
    exact ⟨hn,hφ,hlarge,hvx,hhead,htail,hrows⟩)
  have hcover : Q ⊆ H ∪ T ∪ Fst ∪ U := by
    intro v hv
    obtain ⟨hn,hφ,hvx,hbad⟩ := hQ v hv
    by_cases hsmall : (fordPrime (n v) 0:ℝ) < x^(1/4:ℝ)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hv,hsmall⟩)))
    have hlarge : x^(1/4:ℝ) ≤ fordPrime (n v) 0 := le_of_not_gt hsmall
    by_cases htop : fordRowHolds x (n v) 0
    · by_cases hfail : ∃ j,j ≤ m x-Ψ ∧ ¬fordRowHolds x (n v) j
      · have hfirst := first_failed_row_exists htop hfail
        exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hv,hlarge,hfirst⟩))
      · have hrows : ∀ i ≤ m x-Ψ,fordRowHolds x (n v) i := by
          intro i hi
          by_contra hh
          exact hfail ⟨i,hi,hh⟩
        have htail : fordPrimeCoordinate (n v) (m x-Ψ) ≤ 2 := by
          by_contra hh
          apply hbad
          exact ford_simplex_of_full_rows hΨ (lt_of_not_ge hh)
            (hsecond (n v) hn (by simpa only [hφ] using hvx))
            (fun i hi => hrows i hi.le)
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨hv,hlarge,hhead (n v) hlarge,htail,hrows⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hv,htop⟩)))
  have hc : (Q.card:ℝ) ≤ H.card+T.card+Fst.card+U.card := by
    exact_mod_cast (Finset.card_le_card hcover).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_right
        ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)) _))
  calc
    _ ≤ (H.card:ℝ)+T.card+Fst.card+U.card := hc
    _ ≤ A*(x/Real.log x)*G x (m x)*Real.exp (-(Ψ:ℝ)^2/4)+
        D*(x/Real.log x)*G x (m x)*Real.exp (-(Ψ:ℝ)^2/4)+
        E*(x/Real.log x)*G x (m x)*Real.exp (-(Ψ:ℝ)^2/4)+
        F*(x/Real.log x)*G x (m x)*Real.exp (-(Ψ:ℝ)^2/4) := by
      linarith only [hH,hT,hFst,hU]
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

theorem solution : type_of% @OAI.TotientAsymptotic.ford_structure_value_count_oai := @OAI.TotientAsymptotic.ford_structure_value_count_oai
