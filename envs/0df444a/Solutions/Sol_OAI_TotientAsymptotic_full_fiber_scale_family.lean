-- Prove2me | solution 1 for OAI.TotientAsymptotic.full_fiber_scale_family
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:37:09.34601+00:00
-- url     : https://prove2.me/submissions/9cffd144-a5a8-455b-9228-da7dba454c87

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
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
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
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Squarefree
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.Measure
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
import Mathlib.Order.Fin.Tuple
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
import Theorems.Thm_OAI_TotientAsymptotic_full_fiber_scale_of_local_count
import Theorems.Thm_OAI_TotientAsymptotic_local_full_candidate_count
import Theorems.Thm_OAI_TotientAsymptotic_local_normal_candidate_abundance
import Theorems.Thm_OAI_TotientAsymptotic_ppt_original_regular_count
import Theorems.Thm_OAI_TotientAsymptotic_ppt_regular_geometric_count

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_Renewal
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
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

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeBoxGeometry
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The arithmetic prime boxes and their real double-logarithmic cells agree. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma mem_unitPrimeBox_iff {p m : ℕ} :
    p ∈ unitPrimeBox m ↔ p.Prime ∧
      (m : ℝ)-1 ≤ Real.log (Real.log (p : ℝ)) ∧
      Real.log (Real.log (p : ℝ)) < m := by
  have hlog {p : ℕ} (hp : p.Prime) : 0 < Real.log (p : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hp.one_lt
  constructor
  · intro hp
    obtain ⟨_, hp, hlo, hhi⟩ := Finset.mem_filter.mp hp
    refine ⟨hp, ?_, ?_⟩
    · have h1 := Real.log_le_log (Real.exp_pos _) hlo
      have h2 := Real.log_le_log (Real.exp_pos _) (by simpa only [Real.log_exp] using h1)
      simpa only [Real.log_exp] using h2
    · have h1 := Real.log_lt_log (by exact_mod_cast hp.pos) hhi
      have h2 := Real.log_lt_log (hlog hp) (by simpa only [Real.log_exp] using h1)
      simpa only [Real.log_exp] using h2
  · rintro ⟨hp, hlo, hhi⟩
    have hlo' : Real.exp (Real.exp ((m : ℝ)-1)) ≤ p := by
      have h1 := Real.exp_le_exp.mpr hlo
      have h2 := Real.exp_le_exp.mpr (by simpa only [Real.exp_log (hlog hp)] using h1)
      simpa only [Real.exp_log (by exact_mod_cast hp.pos : (0 : ℝ)<p)] using h2
    have hhi' : (p : ℝ) < Real.exp (Real.exp (m : ℝ)) := by
      have h1 := Real.exp_lt_exp.mpr hhi
      have h2 := Real.exp_lt_exp.mpr (by simpa only [Real.exp_log (hlog hp)] using h1)
      simpa only [Real.exp_log (by exact_mod_cast hp.pos : (0 : ℝ)<p)] using h2
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.two_le, ?_⟩, hp, hlo', hhi'⟩
    exact_mod_cast hhi'.le.trans (Nat.le_ceil _)

lemma mem_primeBoxTuples_iff {N : ℕ} {p m : Fin N → ℕ} :
    p ∈ primeBoxTuples m ↔ (∀ i, (p i).Prime) ∧ primePrefixCoord p ∈ unitGridCell m := by
  simp only [primeBoxTuples, Fintype.mem_piFinset, mem_unitPrimeBox_iff,
    unitGridCell, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Ico,
    primePrefixCoord]
  constructor
  · intro h
    exact ⟨fun i => (h i).1, fun i => (h i).2⟩
  · rintro ⟨hp, hu⟩ i
    exact ⟨hp i, hu i⟩

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_UniformPrefactor
attribute [-instance] _root_.instMeasurableSpace
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

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CubeBoundary
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unit boxes meeting the boundary lie in explicit prefix-slack shells. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma unitGridCell_coordinate_distance {N : ℕ} {m : Fin N → ℕ}
    {u v : Fin N → ℝ} (hu : u ∈ unitGridCell m) (hv : v ∈ unitGridCell m) :
    ∀ i, |u i-v i| ≤ 1 := by
  intro i
  have hui := hu i (Set.mem_univ _)
  have hvi := hv i (Set.mem_univ _)
  exact abs_le.mpr ⟨by linarith [hui.1, hvi.2], by linarith [hui.2, hvi.1]⟩

lemma prefixLinear_cube_error {N : ℕ} (u v : Fin N → ℝ)
    (hdist : ∀ j, |u j-v j| ≤ 1) (i : Fin N) :
    |prefixLinear N u i-prefixLinear N v i| ≤ ((N-i.val : ℕ) : ℝ)^2 := by
  have he : prefixLinear N u i-prefixLinear N v i =
      (u i-v i)-∑ j ∈ Finset.Ioi i, a (j.val-i.val)*(u j-v j) := by
    rw [prefixLinear_apply, prefixLinear_apply]
    have hs : (∑ j : Fin N, ((if i < j then a (j.val-i.val)*u j else 0)-
        (if i < j then a (j.val-i.val)*v j else 0))) =
        ∑ j ∈ Finset.Ioi i, a (j.val-i.val)*(u j-v j) := by
      have heach (j : Fin N) :
          ((if i < j then a (j.val-i.val)*u j else 0)-
            (if i < j then a (j.val-i.val)*v j else 0)) =
          if i < j then a (j.val-i.val)*(u j-v j) else 0 := by
        split_ifs <;> ring
      simp_rw [heach]
      rw [← Finset.sum_filter]
      congr 1
      ext j
      simp
    calc
      _ = (u i-v i)-((∑ j : Fin N, if i < j then a (j.val-i.val)*u j else 0)-
          ∑ j : Fin N, if i < j then a (j.val-i.val)*v j else 0) := by ring
      _ = _ := by rw [← Finset.sum_sub_distrib, hs]
  rw [he]
  have hcoef (j : Fin N) (hj : j ∈ Finset.Ioi i) :
      0 ≤ a (j.val-i.val) ∧ a (j.val-i.val) ≤ (N-i.val : ℕ) := by
    have hji : i < j := Finset.mem_Ioi.mp hj
    have hji' : i.val < j.val := hji
    refine ⟨(a_pos (by omega)).le, (a_le_index (by omega)).trans ?_⟩
    exact_mod_cast (show j.val-i.val ≤ N-i.val by omega)
  calc
    _ ≤ |u i-v i|+|∑ j ∈ Finset.Ioi i, a (j.val-i.val)*(u j-v j)| := by simpa using abs_sub_le (u i-v i) 0 (∑ j ∈ Finset.Ioi i, a (j.val-i.val)*(u j-v j))
    _ ≤ 1+∑ j ∈ Finset.Ioi i, |a (j.val-i.val)*(u j-v j)| :=
      add_le_add (hdist i) (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ 1+∑ _j ∈ Finset.Ioi i, ((N-i.val : ℕ) : ℝ) := by
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul, abs_of_nonneg (hcoef j hj).1]
      exact (mul_le_of_le_one_right (hcoef j hj).1 (hdist j)).trans (hcoef j hj).2
    _ ≤ _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, Fin.card_Ioi]
      have hi : i.val < N := i.isLt
      have he : N-1-i.val = N-i.val-1 := by omega
      rw [he, Nat.cast_sub (by omega : 1 ≤ N-i.val), Nat.cast_one]
      have hn : (1 : ℝ) ≤ (N-i.val : ℕ) := by exact_mod_cast (show 1 ≤ N-i.val by omega)
      nlinarith

lemma prefixBudget_cube_error {N : ℕ} (u v : Fin N → ℝ)
    (hdist : ∀ j, |u j-v j| ≤ 1) :
    |(∑ j, a (j.val+1)*u j)-(∑ j, a (j.val+1)*v j)| ≤ (N : ℝ)^2 := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j : Fin N, |a (j.val+1)*u j-a (j.val+1)*v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin N, (N : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      rw [← mul_sub, abs_mul, abs_of_pos (a_pos (by omega))]
      apply (mul_le_of_le_one_right (a_pos (by omega)).le (hdist j)).trans
      exact (a_le_index (by omega)).trans (by exact_mod_cast (show j.val+1 ≤ N by omega))
    _ = _ := by simp <;> ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalityAlignment
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Factor-count additivity and largest-factor alignment for collision pairs. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma primeFactor_le_largest {n p : ℕ} (hp : p ∈ n.primeFactorsList) :
    p ≤ largestPrimeFactor n := by
  have hm : p ∈ n.primeFactors := by
    change p ∈ n.primeFactorsList.toFinset
    exact List.mem_toFinset.mpr hp
  exact (Finset.le_sup (f := id) hm).trans (le_max_right _ _)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SmoothSuffix
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothness of the residual totient in an actual basic collision witness. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma largestPrimeFactor_le_of_prime_divisors {n z : ℕ} (hz : 1 ≤ z)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → n ≠ 0 → p ≤ z) : largestPrimeFactor n ≤ z := by
  apply max_le hz
  apply Finset.sup_le
  intro p hp
  obtain ⟨hp', hd, hn⟩ := Nat.mem_primeFactors.mp hp
  exact h p hp' hd hn

lemma prime_dvd_le_largest {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) (hd : p ∣ n) :
    p ≤ largestPrimeFactor n :=
  primeFactor_le_largest ((Nat.mem_primeFactorsList_iff_dvd hn hp).mpr hd)

lemma largestPrimeFactor_mul_le {a b z : ℕ}
    (ha : largestPrimeFactor a ≤ z) (hb : largestPrimeFactor b ≤ z) :
    largestPrimeFactor (a*b) ≤ z := by
  apply largestPrimeFactor_le_of_prime_divisors ((le_max_left _ _).trans ha)
  intro p hp hd hn
  rcases hp.dvd_mul.mp hd with hpa | hpb
  · exact (prime_dvd_le_largest hp (left_ne_zero_of_mul hn) hpa).trans ha
  · exact (prime_dvd_le_largest hp (right_ne_zero_of_mul hn) hpb).trans hb

lemma largestPrimeFactor_prod_le {ι : Type*} (I : Finset ι) (f : ι → ℕ) {z : ℕ}
    (hz : 1 ≤ z) (hf : ∀ i ∈ I, largestPrimeFactor (f i) ≤ z) :
    largestPrimeFactor (∏ i ∈ I, f i) ≤ z := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa [largestPrimeFactor] using hz
  | @insert i I hi ih =>
    rw [Finset.prod_insert hi]
    exact largestPrimeFactor_mul_le (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma largestPrimeFactor_prime {p : ℕ} (hp : p.Prime) : largestPrimeFactor p = p := by
  simp [largestPrimeFactor, hp.primeFactors, max_eq_right hp.one_lt.le]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionCoordinateEndpoint
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original prime coordinate differs from a dyadic endpoint by at most one. -/

noncomputable section

namespace TotientAsymptotic

lemma prime_coordinate_endpoint_bound {p : ℕ} {y : ℝ}
    (hp : 3 ≤ p) (hy : Real.exp 1 ≤ y) (hpy : (p-1 : ℕ) ≤ y) :
    B p ≤ B y+1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1<p)
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hp1
  have hy1 : 1 ≤ Real.log y := by
    have he := Real.log_le_log (Real.exp_pos 1) hy
    simpa only [Real.log_exp] using he
  have hy0 : 0<y := (Real.exp_pos 1).trans_le hy
  have hyge1 : (1 : ℝ) ≤ y := by
    have he := Real.add_one_le_exp (1 : ℝ)
    linarith
  have he : (p : ℝ)=(p-1 : ℕ)+1 := by exact_mod_cast (Nat.sub_add_cancel (by omega : 1≤p)).symm
  have hp2y : (p : ℝ) ≤ 2*y := by rw [he]; linarith
  have hl := Real.log_le_log hp0 hp2y
  rw [Real.log_mul (by norm_num : (2 : ℝ)≠0) hy0.ne'] at hl
  have hl2 : Real.log (p : ℝ) ≤ 2*Real.log y := by
    have hc := Real.log_two_lt_d9
    linarith
  have hb := Real.log_le_log (Real.log_pos hp1) hl2
  rw [Real.log_mul (by norm_num : (2 : ℝ)≠0) (by linarith : Real.log y≠0)] at hb
  change B (p : ℝ)≤B y+1
  change Real.log (Real.log (p : ℝ))≤Real.log (Real.log y)+1
  linarith [Real.log_two_lt_d9]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_DyadicCollisionMass
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite dyadic quotient can be integrated from its actual lowest slice. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma dyadic_nat_bounds {v : ℕ} (hv : 1 < v) :
    1 ≤ Nat.clog 2 v ∧ (2 : ℝ)^(Nat.clog 2 v)/2 < v ∧
      (v : ℝ) ≤ (2 : ℝ)^(Nat.clog 2 v) := by
  have hn : 1 ≤ Nat.clog 2 v := by
    have hh := (Nat.lt_clog_iff_pow_lt (by norm_num : 1 < 2) (x := v) (y := 0)).mpr
      (by simpa using hv)
    omega
  refine ⟨hn,?_,?_⟩
  · have hh := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) hv
    have he : Nat.clog 2 v=Nat.clog 2 v-1+1 := by omega
    rw [he,pow_succ]
    have hcast : (2 : ℝ)^(Nat.clog 2 v-1) < v := by exact_mod_cast hh
    convert hcast using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) v

lemma dyadic_endpoint_log (n : ℕ) :
    Real.log ((2 : ℝ)^n)=(n : ℝ)*Real.log 2 := by rw [Real.log_pow]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FiniteDyadicHarmonic
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite reciprocal sum from dyadic counts of order y/log y. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma finite_dyadic_harmonic_mass {α : Type*} (Q : Finset α)
    (n : α → ℕ) (v : α → ℝ) (L : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hn : ∀ a ∈ Q, n a ∈ Finset.Icc 1 L)
    (hlo : ∀ a ∈ Q, (2 : ℝ)^(n a)/4 ≤ v a)
    (hcount : ∀ k ∈ Finset.Icc 1 L, ((Q.filter (fun a => n a=k)).card : ℝ) ≤
      A*(2 : ℝ)^k/(k : ℝ)) :
    (∑ a ∈ Q, (v a)⁻¹) ≤ 4*A*(1+Real.log L) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to hn]
  have hf (k : ℕ) (hk : k ∈ Finset.Icc 1 L) :
      (∑ a ∈ Q.filter (fun a => n a=k), (v a)⁻¹) ≤ 4*A*(k : ℝ)⁻¹ := by
    have hy : (0 : ℝ) < (2 : ℝ)^k := by positivity
    calc
      _ ≤ ∑ _a ∈ Q.filter (fun a => n a=k), 4/(2 : ℝ)^k := by
        apply Finset.sum_le_sum
        intro a ha
        obtain ⟨ha,he⟩ := Finset.mem_filter.mp ha
        have hh := hlo a ha
        rw [he] at hh
        have hr := inv_anti₀ (div_pos hy (by norm_num)) hh
        simpa only [inv_div] using hr
      _ = ((Q.filter (fun a => n a=k)).card : ℝ)*(4/(2 : ℝ)^k) := by simp
      _ ≤ (A*(2 : ℝ)^k/(k : ℝ))*(4/(2 : ℝ)^k) :=
        mul_le_mul_of_nonneg_right (hcount k hk) (by positivity)
      _ = _ := by field_simp
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 L, 4*A*(k : ℝ)⁻¹ := Finset.sum_le_sum hf
    _ = 4*A*(harmonic L : ℝ) := by
      simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log L) (by positivity)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeDiscardCutoff
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common dyadic endpoint for the short suffix. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma discardExponent_bounds {b : ℝ} (hb : 2 ≤ b) :
    2 ≤ discardExponent b ∧ Real.log (discardExponent b : ℝ) ≤ 2*b+1 := by
  have he := Real.add_one_le_exp (2*b)
  have hm := Nat.le_ceil (Real.exp (2*b))
  have hm0 : (2 : ℝ) ≤ discardExponent b := by dsimp [discardExponent] <;> linarith
  refine ⟨by exact_mod_cast hm0,?_⟩
  have hc : (discardExponent b : ℝ) ≤ 2*Real.exp (2*b) := by
    have hu := Nat.ceil_lt_add_one (show 0 ≤ Real.exp (2*b) from (Real.exp_pos _).le)
    dsimp [discardExponent]
    linarith
  calc
    _ ≤ Real.log (2*Real.exp (2*b)) := Real.log_le_log (by linarith) hc
    _ = Real.log 2+2*b := by rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne',Real.log_exp]
    _ ≤ _ := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)]

lemma discardPrimeBound_bounds {b : ℝ} (hb : 2 ≤ b) :
    4 ≤ discardPrimeBound b ∧ 0 ≤ B (discardPrimeBound b) ∧
    B (discardPrimeBound b) ≤ 2*b+1 ∧
    Real.exp (Real.exp ((6/5 : ℝ)*b)) ≤ discardPrimeBound b := by
  obtain ⟨hM,hlogM⟩ := discardExponent_bounds hb
  have hM2 : (2 : ℝ) ≤ discardExponent b := by exact_mod_cast hM
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2up : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)]
  have hlog2low : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hB : B (discardPrimeBound b)=Real.log ((discardExponent b : ℝ)*Real.log 2) := by
    simp only [discardPrimeBound,B,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
  refine ⟨?_,?_,?_,?_⟩
  · have he := Nat.pow_le_pow_right (by norm_num : 0<2) hM
    exact he
  · rw [hB]
    apply Real.log_nonneg
    nlinarith
  · rw [hB]
    have hh : (discardExponent b : ℝ)*Real.log 2 ≤ discardExponent b := by nlinarith
    exact (Real.log_le_log (by positivity) hh).trans hlogM
  · have he : (2 : ℝ) ≤ Real.exp ((4/5 : ℝ)*b) := by
      linarith [Real.add_one_le_exp ((4/5 : ℝ)*b)]
    have hsplit : Real.exp (2*b)=Real.exp ((6/5 : ℝ)*b)*Real.exp ((4/5 : ℝ)*b) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hceil := Nat.le_ceil (Real.exp (2*b))
    change Real.exp (2*b) ≤ (discardExponent b : ℝ) at hceil
    have hh : Real.exp ((6/5 : ℝ)*b) ≤ (discardExponent b : ℝ)*Real.log 2 := by
      rw [hsplit] at hceil
      nlinarith [Real.exp_pos ((6/5 : ℝ)*b)]
    have hNpos : (0 : ℝ) < discardPrimeBound b := by
      unfold discardPrimeBound
      positivity
    apply (Real.le_log_iff_exp_le hNpos).mp
    simpa only [discardPrimeBound,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow] using hh

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_DyadicLogGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary log-log comparisons at dyadic endpoints. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma double_log_double_le {x : ℝ} (hx : 2 ≤ x) : B (2*x) ≤ B x+1 := by
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog2 : Real.log (2:ℝ) ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hlog : Real.log (2*x) ≤ 2*Real.log x := by
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hx0.ne']
    linarith
  have hp : 0 < Real.log (2*x) := Real.log_pos (by linarith)
  have hh := Real.log_le_log hp hlog
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hl.ne'] at hh
  have htwo : Real.log (2:ℝ) ≤ 1 := by linarith [Real.log_two_lt_d9]
  change Real.log (Real.log (2*x)) ≤ Real.log (Real.log x)+1
  linarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordDimensionScale
attribute [-instance] _root_.instMeasurableSpace
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

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_MovingSmoothDyadic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A moving smoothness condition on a totient transfers to its dyadic slice. -/
noncomputable section
namespace TotientAsymptotic

lemma B_mono {x y : ℝ} (hx : 1 < x) (hxy : x ≤ y) : B x ≤ B y :=
  Real.log_le_log (Real.log_pos hx) (Real.log_le_log (by linarith) hxy)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_OrderedPrimeProduct
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact recovery of an ordered prime tuple from its product. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma prime_coordinates_strictAnti {n : ℕ} {p : Fin n → ℕ}
    (hp : ∀ i,(p i).Prime) (hcoord : StrictAnti (primePrefixCoord p)) : StrictAnti p := by
  intro i j hij
  by_contra! hh
  have hip : (0:ℝ) < p i := by exact_mod_cast (hp i).pos
  have hi1 : (1:ℝ) < p i := by exact_mod_cast (hp i).one_lt
  have hlog := Real.log_le_log hip (show (p i:ℝ) ≤ p j by exact_mod_cast hh)
  have hloglog := Real.log_le_log (Real.log_pos hi1) hlog
  have hstrict := hcoord hij
  change Real.log (Real.log (p j:ℝ)) < Real.log (Real.log (p i:ℝ)) at hstrict
  exact (not_lt_of_ge hloglog) hstrict

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_StrictContractionCost
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inverse-cube row contraction has a bounded full Jacobian. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma rowContractionError_nonneg (h : ℕ) : 0 ≤ rowContractionError h := by
  unfold rowContractionError
  positivity

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_StrictCube
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unit-coordinate errors preserve strict rows when paid from their margin. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma strict_row_cube {N : ℕ} (u v : Fin N → ℝ) (i : Fin N) {r e : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hrow : (∑ j : Fin N,if i < j then a (j.val-i.val)*u j else 0) ≤ r*u i)
    (hdist : ∀ j,|u j-v j| ≤ 1)
    (hmargin : ((N-i.val:ℕ):ℝ)^2+1 ≤ e*v i) :
    (∑ j : Fin N,if i < j then a (j.val-i.val)*v j else 0) ≤ (r+e)*v i := by
  have hd := (le_abs_self _).trans (prefixLinear_cube_error u v hdist i)
  have hvu := (neg_le_abs _).trans (hdist i)
  have hweight : (1-r)*(v i-u i) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hvu (by linarith only [hr1] : 0 ≤ 1-r)
    nlinarith only [hh,hr]
  rw [prefixLinear_apply,prefixLinear_apply] at hd
  nlinarith only [hd,hrow,hweight,hmargin]

lemma strict_gap_cube {N : ℕ} (u v : Fin N → ℝ) (i j : Fin N) {r e : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hgap : u j ≤ r*u i)
    (hdist : ∀ k,|u k-v k| ≤ 1) (hmargin : 2 ≤ e*v i) :
    v j ≤ (r+e)*v i := by
  have hi := (le_abs_self _).trans (hdist i)
  have hj := (neg_le_abs _).trans (hdist j)
  have hmul := mul_le_mul_of_nonneg_left hi hr
  nlinarith only [hgap,hi,hj,hmul,hr1,hmargin]

lemma strict_top_cube {N : ℕ} (u v : Fin N → ℝ) {B₀ B : ℝ}
    (hrow : (∑ j : Fin N,a (j.val+1)*u j) ≤ B₀)
    (hdist : ∀ j,|u j-v j| ≤ 1) (hmargin : B₀+(N:ℝ)^2 ≤ B) :
    (∑ j : Fin N,a (j.val+1)*v j) ≤ B := by
  have hh := (neg_le_abs _).trans (prefixBudget_cube_error u v hdist)
  linarith only [hrow,hh,hmargin]

lemma reciprocal_row_margin {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) :
    e/6 ≤ (1+e/2)⁻¹-(1+e)⁻¹ := by
  have h₁ : 0 < 1+e/2 := by positivity
  have h₂ : 0 < 1+e := by positivity
  have hid : (1+e/2)⁻¹-(1+e)⁻¹=e/(2*(1+e/2)*(1+e)) := by field_simp <;> ring
  rw [hid]
  apply (le_div_iff₀ (by positivity : 0 < 2*(1+e/2)*(1+e))).mpr
  have hprod : 2*(1+e/2)*(1+e) ≤ 6 := by nlinarith only [he.le,he1]
  nlinarith only [mul_le_mul_of_nonneg_left hprod he.le]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_InverseCubeMargin
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit polynomial threshold pays for each inverse-cube row margin. -/
noncomputable section
namespace TotientAsymptotic

lemma inverse_cube_margin {h : ℕ} (hh : 1 ≤ h) {u v : ℝ}
    (hu : 100*(h:ℝ)^5 ≤ u) (hdist : |u-v| ≤ 1) :
    0 < v ∧ (h:ℝ)^2+1 ≤
      ((1+1/(10*(h:ℝ)^3))⁻¹-(1+1/(5*(h:ℝ)^3))⁻¹)*v := by
  have hh' : (1:ℝ) ≤ h := by exact_mod_cast hh
  have hp : (0:ℝ) < h := lt_of_lt_of_le zero_lt_one hh'
  have hp3 : 1 ≤ (h:ℝ)^3 := one_le_pow₀ hh'
  have hp5 : 1 ≤ (h:ℝ)^5 := one_le_pow₀ hh'
  have h35 : (h:ℝ)^3 ≤ (h:ℝ)^5 := pow_le_pow_right₀ hh' (by omega)
  have hd := (le_abs_self _).trans hdist
  have hv : 0 < v := by nlinarith only [hu,hd,hp5]
  refine ⟨hv,?_⟩
  have hbase : 30*(h:ℝ)^5+30*(h:ℝ)^3 ≤ v := by
    nlinarith only [hu,hd,hp5,h35]
  have hquot : (h:ℝ)^2+1 ≤ v/(30*(h:ℝ)^3) := by
    apply (le_div_iff₀ (by positivity : 0 < 30*(h:ℝ)^3)).mpr
    convert hbase using 1 <;> first | rfl | ring
  have he : 0 < 1/(5*(h:ℝ)^3) := by positivity
  have he1 : 1/(5*(h:ℝ)^3) ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 5*(h:ℝ)^3)).mpr
    linarith only [hp3]
  have hmargin := reciprocal_row_margin he he1
  have heq : 1/(5*(h:ℝ)^3)/2=1/(10*(h:ℝ)^3) := by ring
  rw [heq] at hmargin
  apply hquot.trans
  have hh := mul_le_mul_of_nonneg_right hmargin hv.le
  convert hh using 1 <;> first | rfl | ring

lemma inverse_cube_top_margin {m n : ℕ} (hn : n ≤ m) {B : ℝ}
    (hB : 100*(m+1:ℝ)^5 ≤ B) :
    B/(1+1/(5*(m+1:ℝ)^3))+(n:ℝ)^2 ≤ B/(1+1/(10*(m+1:ℝ)^3)) := by
  have he := (inverse_cube_margin (h:=m+1) (by omega)
    (by simpa only [Nat.cast_add,Nat.cast_one] using hB) (by simp : |B-B| ≤ 1)).2
  have hn' : (n:ℝ) ≤ m+1 := by exact_mod_cast (show n ≤ m+1 by omega)
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg n) hn' 2
  simp only [Nat.cast_add,Nat.cast_one] at he
  have hid : ((1+1/(10*(m+1:ℝ)^3))⁻¹-(1+1/(5*(m+1:ℝ)^3))⁻¹)*B=
      B/(1+1/(10*(m+1:ℝ)^3))-B/(1+1/(5*(m+1:ℝ)^3)) := by ring
  rw [hid] at he
  linarith only [he,hs]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_GeometricCube
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive-volume family retains half of every margin in its unit grid. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma geometric_family_unit_cube {m n : ℕ} {B c : ℝ} (hn : n ≤ m)
    {u v : Fin n → ℝ} (hu : u ∈ geometricContractedFamily m n B c)
    (hdist : ∀ i,|u i-v i| ≤ 1)
    (hlarge : ∀ i,100*((m-i.val:ℕ):ℝ)^5 ≤ u i)
    (hB : 100*(m+1:ℝ)^5 ≤ B) :
    v ∈ relaxedGeometricFamily m n B (c/2) := by
  have hi (i : Fin n) : 1 ≤ m-i.val := by have := i.isLt; omega
  have herr (i : Fin n) : rowContractionError (m-(i.val+1)) =
      1/(5*((m-i.val:ℕ):ℝ)^3) := by
    unfold rowContractionError
    have he : m-(i.val+1)+1=m-i.val := by have := i.isLt; omega
    have he' : ((m-(i.val+1):ℕ):ℝ)+1=((m-i.val:ℕ):ℝ) := by
      exact_mod_cast he
    rw [he']
  have hhalf (i : Fin n) : rowContractionError (m-(i.val+1))/2 =
      1/(10*((m-i.val:ℕ):ℝ)^3) := by rw [herr]; ring
  have hmargin (i : Fin n) := inverse_cube_margin (hi i) (hlarge i) (hdist i)
  have hpos (i : Fin n) : 0 < v i := (hmargin i).1
  have hgap (i j : Fin n) (hij : i < j) :
      v j ≤ v i/(1+rowContractionError (m-(i.val+1))/2) := by
    let r := (1+rowContractionError (m-(i.val+1)))⁻¹
    let e := (1+rowContractionError (m-(i.val+1))/2)⁻¹-r
    have hr : 0 ≤ r := by
      dsimp [r]
      exact inv_nonneg.mpr (by linarith only [rowContractionError_nonneg (m-(i.val+1))])
    have hr1 : r ≤ 1 := by
      apply inv_le_one_of_one_le₀
      linarith only [rowContractionError_nonneg (m-(i.val+1))]
    have he : 2 ≤ e*v i := by
      have hp : (1:ℝ) ≤ ((m-i.val:ℕ):ℝ)^2 :=
        one_le_pow₀ (by exact_mod_cast hi i)
      have hh := (hmargin i).2
      dsimp [e,r]
      rw [hhalf,herr]
      linarith only [hp,hh]
    have hg := strict_gap_cube u v i j hr hr1
      (by simpa only [r,div_eq_mul_inv,mul_comm] using hu.2.2 i j hij) hdist he
    simpa only [e,r,add_sub_cancel,div_eq_mul_inv,mul_comm] using hg
  refine ⟨⟨fun i => (hpos i).le,?_,?_,?_⟩,?_,hgap⟩
  · intro i j hij
    apply (hgap i j hij).trans_lt
    apply div_lt_self (hpos i)
    have he : 0 < rowContractionError (m-(i.val+1)) := by
      unfold rowContractionError
      positivity
    linarith
  · intro i
    let r := (1+rowContractionError (m-(i.val+1)))⁻¹
    let e := (1+rowContractionError (m-(i.val+1))/2)⁻¹-r
    have hr : 0 ≤ r := by
      dsimp [r]
      exact inv_nonneg.mpr (by linarith only [rowContractionError_nonneg (m-(i.val+1))])
    have hr1 : r ≤ 1 := by
      apply inv_le_one_of_one_le₀
      linarith only [rowContractionError_nonneg (m-(i.val+1))]
    have hh := (hmargin i).2
    have hni : ((n-i.val:ℕ):ℝ) ≤ ((m-i.val:ℕ):ℝ) := by
      exact_mod_cast Nat.sub_le_sub_right hn i.val
    have hs := pow_le_pow_left₀ (Nat.cast_nonneg (n-i.val)) hni 2
    have he : ((n-i.val:ℕ):ℝ)^2+1 ≤ e*v i := by
      dsimp [e,r]
      rw [hhalf,herr]
      linarith only [hs,hh]
    have hrw := strict_row_cube u v i hr hr1
      (by simpa only [r,div_eq_mul_inv,mul_comm] using hu.1.2.2.1 i) hdist he
    simpa only [e,r,add_sub_cancel,div_eq_mul_inv,mul_comm] using hrw
  · apply strict_top_cube u v hu.1.2.2.2 hdist
    have he : 1/(5*(m+1:ℝ)^3)/2=1/(10*(m+1:ℝ)^3) := by
      field_simp
      ring
    simpa only [rowContractionError,he] using inverse_cube_top_margin hn hB
  · intro i
    have hh := (le_abs_self _).trans (hdist i)
    have hp : (1:ℝ) ≤ ((m-i.val:ℕ):ℝ)^5 := one_le_pow₀ (by exact_mod_cast hi i)
    have hcu := hu.2.1 i
    have hlu := hlarge i
    nlinarith only [hh,hp,hcu,hlu]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_GeometricLowerBudget
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two numerical margins needed for the inner prime grid. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma geometric_dominates_polynomial {c : ℝ} (hc : 0 < c) (A : ℝ) (k : ℕ) :
    ∀ᶠ H : ℕ in atTop,∀ h : ℕ,H ≤ h → A*(h:ℝ)^k ≤ c*(rho^h)⁻¹ := by
  have hlim : Tendsto (fun h : ℕ => A*((h:ℝ)^k*rho^h)) atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_const_mul_const_pow_of_lt_one k rho_pos.le rho_lt_one).const_mul A
  have ht := hlim.eventually (eventually_lt_nhds hc)
  obtain ⟨H,hH⟩ := eventually_atTop.mp ht
  filter_upwards [eventually_ge_atTop H] with J hJ
  intro h hh
  have hs := (hH h (hJ.trans hh)).le
  apply (le_div_iff₀ (pow_pos rho_pos h)).mpr
  simpa only [div_eq_mul_inv,mul_assoc] using hs

lemma ambient_polynomial_budget (A : ℝ) (k : ℕ) :
    ∀ᶠ x : ℝ in atTop,A*(m x:ℝ)^k ≤ B x := by
  have ht : Tendsto (fun x : ℝ => A*(m x:ℝ)^k*
      Real.exp (-((3/5:ℝ)*(m x:ℝ)))) atTop (nhds 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (k:ℝ) (3/5) (by norm_num : (0:ℝ) < 3/5)).comp
        (tendsto_natCast_atTop_atTop.comp m_tendsto)
    simpa only [Real.rpow_natCast,mul_zero,Function.comp_apply,neg_mul,mul_assoc] using h.const_mul A
  filter_upwards [ht.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),
    dimension_exponential_lower] with x hx hB
  have hs : A*(m x:ℝ)^k ≤ Real.exp ((3/5:ℝ)*(m x:ℝ)) := by
    have hh := mul_le_mul_of_nonneg_right hx.le (Real.exp_pos ((3/5:ℝ)*(m x:ℝ))).le
    rw [mul_assoc,←Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one,one_mul] at hh
    exact hh
  exact hs.trans hB

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_GeometricPrimeRegion
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The outer grid has both positive prime mass and strict arithmetic coordinates. -/
noncomputable section
open scoped Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

lemma ambient_successor_fifth_budget :
    ∀ᶠ x : ℝ in atTop,100*(m x+1:ℝ)^5 ≤ B x := by
  filter_upwards [ambient_polynomial_budget 3200 5,
    m_tendsto.eventually (eventually_ge_atTop 1)] with x hx hm
  have hm' : (1:ℝ) ≤ m x := by exact_mod_cast hm
  have hpow := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ m x+1)
    (show (m x:ℝ)+1 ≤ 2*m x by linarith only [hm']) 5
  have he : (2*(m x:ℝ))^5=32*(m x:ℝ)^5 := by ring
  rw [he] at hpow
  linarith only [hpow,hx]

lemma geometric_grid_coordinates {c : ℝ} (hc : 0 < c) :
    ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∀ n : ℕ,n+H=m x → ∀ b ∈ geometricPrimeGrid x c n,
        ∀ v : Fin n → ℝ,v ∈ unitGridCell b →
          v ∈ relaxedGeometricFamily (m x) n (B x) (c/2) := by
  filter_upwards [geometric_dominates_polynomial hc 100 5] with H hH
  filter_upwards [ambient_successor_fifth_budget] with x hx
  intro n hn b hb v hv
  obtain ⟨_,u,hu,hfamily⟩ := Finset.mem_filter.mp hb
  apply geometric_family_unit_cube (by omega) hfamily
    (unitGridCell_coordinate_distance hu hv) _ hx
  intro i
  exact (hH _ (by have := i.isLt; omega)).trans (hfamily.2.1 i)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_HeadLimitedPrimeMass
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive prime mass with the leading tail separated from the new head. -/
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

lemma headLimitedPrimeGrid_subset {x c : ℝ} {n : ℕ} :
    headLimitedPrimeGrid x c n ⊆ geometricPrimeGrid x c n := by
  intro b hb
  obtain ⟨hb,u,hu,hs⟩ := Finset.mem_filter.mp hb
  exact Finset.mem_filter.mpr ⟨hb,u,hu,hs.1⟩

lemma head_limited_prime_coordinates {c : ℝ} (hc : 0 < c) :
    ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∀ n : ℕ,n+H=m x → ∀ p ∈ gridPrimeTuples (headLimitedPrimeGrid x c n),
        (∀ i,(p i).Prime) ∧
        primePrefixCoord p ∈ relaxedGeometricFamily (m x) n (B x) (c/2) ∧
        ∀ i,primePrefixCoord p i ≤ (19/25:ℝ)*B x := by
  filter_upwards [geometric_grid_coordinates hc] with H hH
  filter_upwards [hH,B_tendsto.eventually (eventually_ge_atTop (100:ℝ))] with x hx hB
  intro n hn p hp
  obtain ⟨b,hb,hpb⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨hp,hcell⟩ := mem_primeBoxTuples_iff.mp hpb
  refine ⟨hp,hx n hn b (headLimitedPrimeGrid_subset hb) _ hcell,?_⟩
  obtain ⟨_,u,hu,hfamily⟩ := Finset.mem_filter.mp hb
  have hdist := unitGridCell_coordinate_distance hu hcell
  intro i
  have hi := (neg_le_abs _).trans (hdist i)
  have hu := hfamily.2 i
  nlinarith only [hi,hu,hB]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TailProductBounds
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The capped tail has the subpower denominator required by the prime window. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma prime_tail_log_bound {n : ℕ} (p : Fin n → ℕ)
    (hp : ∀ i,(p i).Prime) {T : ℝ} (hT : ∀ i,primePrefixCoord p i ≤ T) :
    Real.log ((∏ i,p i : ℕ):ℝ) ≤ n*Real.exp T := by
  rw [Nat.cast_prod,Real.log_prod (fun i _ => by exact_mod_cast (hp i).ne_zero)]
  calc
    _ ≤ ∑ i : Fin n,Real.exp T := by
      apply Finset.sum_le_sum
      intro i _
      have hi := Real.exp_le_exp.mpr (hT i)
      have hip : (1:ℝ) < p i := by exact_mod_cast (hp i).one_lt
      simpa only [primePrefixCoord,Real.exp_log (Real.log_pos hip)] using hi
    _ = _ := by simp

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalNormalityMass
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ford's proved exceptional-prime estimate at each local indexed scale. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma localNormalityScale_gt_two (h : ℕ) : 2 < localNormalityScale h := by
  have he := Real.one_le_exp (show 0 ≤ (h:ℝ)^4 by positivity)
  have htwo : 2 < Real.exp 1 := by
    linarith only [Real.add_one_lt_exp (by norm_num : (1:ℝ) ≠ 0)]
  exact htwo.trans_le (Real.exp_le_exp.mpr he)


end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalSquareNormality
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual logarithmic square cutoff lies below each local normality scale. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

theorem local_square_cutoff_le_normality {A : ℝ} (_hA : 0 ≤ A) :
    ∀ᶠ h : ℕ in atTop,∀ z : ℝ,1 < z → 0 ≤ B z →
      Real.log (B z+4) ≤ A*h →
      (localSquareCutoff z:ℝ) ≤ localNormalityScale h := by
  have hlog6 : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
    (eventually_ge_atTop (A+Real.log 6+2)),eventually_ge_atTop (2:ℕ)] with h hh hh2
  intro z hz hB hlog
  have hh1 : (1:ℝ) ≤ h := by exact_mod_cast (show 1≤h by omega)
  have hlogh := mul_le_mul_of_nonneg_left hh1 hlog6
  have hlarge := mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg (α:=ℝ) h)
  have hpow : (h:ℝ)^2 ≤ (h:ℝ)^4 := by
    have hsq : 1 ≤ (h:ℝ)^2 := one_le_pow₀ hh1
    have hm := mul_nonneg (sq_nonneg (h:ℝ)) (sub_nonneg.mpr hsq)
    nlinarith only [hm]
  have hexponent : Real.log 6+A*h ≤ (h:ℝ)^4 := by
    nlinarith only [hlogh,hlarge,hpow,Nat.cast_nonneg (α:=ℝ) h]
  have harg : 6*B z ≤ Real.exp ((h:ℝ)^4) := by
    have he := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log (by linarith only [hB] : 0 < B z+4)] at he
    have hm := mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ)≤6)
    have hh := Real.exp_le_exp.mpr hexponent
    rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<6)] at hh
    linarith only [hm,hh]
  have hlogz : 0 < Real.log z := Real.log_pos hz
  have heq : (Real.log z)^6=Real.exp (6*B z) := by
    simpa only [Nat.cast_ofNat,B,Real.exp_log hlogz] using
      (Real.exp_nat_mul (B z) 6).symm
  have hfloor : (localSquareCutoff z:ℝ) ≤ (Real.log z)^6 :=
    Nat.floor_le (pow_nonneg hlogz.le 6)
  exact hfloor.trans (heq.trans_le (Real.exp_le_exp.mpr harg))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ResidualDyadicMass
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local residual counts integrate against their actual reciprocal totients. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem residual_dyadic_mass (R : Finset ℕ) (d L : ℕ) {A : ℝ}
    (hA : 0 ≤ A)
    (hrange : ∀ r ∈ R,1 < d*r.totient ∧ ((d*r.totient:ℕ):ℝ) ≤ (2:ℝ)^L)
    (hcount : ∀ k ∈ Finset.Icc 1 L,
      ((R.filter (fun r => Nat.clog 2 (d*r.totient)=k)).card:ℝ) ≤ A*(2:ℝ)^k/k) :
    (∑ r ∈ R,(r.totient:ℝ)⁻¹) ≤ 4*d*A*(1+Real.log L) := by
  classical
  have hn : ∀ r ∈ R,Nat.clog 2 (d*r.totient) ∈ Finset.Icc 1 L := by
    intro r hr
    refine Finset.mem_Icc.mpr ⟨(dyadic_nat_bounds (hrange r hr).1).1,?_⟩
    apply (Nat.clog_le_iff_le_pow (by decide : 1<2)).mpr
    exact_mod_cast (hrange r hr).2
  have hlo : ∀ r ∈ R,(2:ℝ)^(Nat.clog 2 (d*r.totient))/4 ≤ ((d*r.totient:ℕ):ℝ) := by
    intro r hr
    have hh := (dyadic_nat_bounds (hrange r hr).1).2.1
    have hp : 0 < (2:ℝ)^(Nat.clog 2 (d*r.totient)) := by positivity
    linarith only [hh,hp]
  have hm := finite_dyadic_harmonic_mass R (fun r => Nat.clog 2 (d*r.totient))
    (fun r => ((d*r.totient:ℕ):ℝ)) L hA hn hlo hcount
  have he : (∑ r ∈ R,(r.totient:ℝ)⁻¹) =
      (d:ℝ)*(∑ r ∈ R,(((d*r.totient:ℕ):ℝ))⁻¹) := by
    by_cases hR : R.Nonempty
    · obtain ⟨r,hr⟩ := hR
      have hd : d≠0 := by intro h; simpa [h] using (hrange r hr).1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [Nat.cast_mul,mul_inv]
      field_simp
    · rw [Finset.not_nonempty_iff_eq_empty.mp hR]
      simp
  rw [he]
  have hh := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg d)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NaturalCoordinateUpper
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform coordinate scale at each fixed distance below the natural dimension. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma direct_scale_eq {x : ℝ} (hB : 1 < B x) (hm : 0 < m x) :
    B x*rho^(m x)/(m x:ℝ)=alpha (theta x)*bandCenterRatio x := by
  have hh := inverse_scale_eq hB hm
  have hi := congrArg (fun z : ℝ => z⁻¹) hh
  simpa only [inv_div,inv_inv] using hi

lemma natural_coordinate_scale_upper : ∃ A : ℝ,0 < A ∧
    ∀ H : ℕ,∀ᶠ x : ℝ in atTop,
      0 < m x-H ∧ B x*rho^(m x)/((m x-H:ℕ):ℝ) ≤ A := by
  refine ⟨4*lam/rho,div_pos (mul_pos (by norm_num) lam_pos) rho_pos,?_⟩
  intro H
  filter_upwards [theta_eventually_mem,
    B_tendsto.eventually (eventually_gt_atTop (1:ℝ)),
    m_tendsto.eventually (eventually_gt_atTop (2*H)),
    bandCenterRatio_tendsto.eventually (eventually_lt_nhds (by norm_num : (1:ℝ)<2)),
    bandCenterRatio_tendsto.eventually (eventually_gt_nhds (by norm_num : (0:ℝ)<1))]
    with x hphase hB hm hc hc0
  have hm0 : 0 < m x := by omega
  have hn : 0 < m x-H := by omega
  refine ⟨hn,?_⟩
  have hbasic : B x*rho^(m x)/(m x:ℝ) ≤ 2*lam/rho := by
    rw [direct_scale_eq hB hm0]
    have hh := mul_le_mul (alpha_le _ hphase) hc.le hc0.le
      (div_pos lam_pos rho_pos).le
    exact hh.trans_eq (by ring)
  have hsize : (m x:ℝ) ≤ 2*((m x-H:ℕ):ℝ) := by
    exact_mod_cast (show m x ≤ 2*(m x-H) by omega)
  have hnm : (0:ℝ) < ((m x-H:ℕ):ℝ) := by exact_mod_cast hn
  have hbasic' := (div_le_iff₀ (show (0:ℝ) < (m x:ℝ) by exact_mod_cast hm0)).mp hbasic
  apply (div_le_iff₀ hnm).mpr
  have hmul := mul_le_mul_of_nonneg_left hsize (show 0 ≤ 2*lam/rho from (div_pos (mul_pos (by norm_num) lam_pos) rho_pos).le)
  exact hbasic'.trans (hmul.trans_eq (by ring))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalCoordinateBounds
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Turning buffered concentration into geometric upper bounds at every index. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma localCoordinateCap_geometric {n m : ℕ} {B A : ℝ} (hn : 0 < n)
    (hnm : n ≤ m) (hA : 0 < A) (hscale : B*rho^m/(n:ℝ) ≤ A)
    (hB : 0 ≤ B) (i : Fin n) :
    localCoordinateCap n B i ≤ 2*A*(m-i.val:ℕ)*(rho^(m-i.val))⁻¹ := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hpow : rho^(i.val+1)*rho^(m-i.val)=rho^m*rho := by
    rw [←pow_add,show i.val+1+(m-i.val)=m+1 by have := i.isLt; omega,pow_succ]
  have he : localCoordinateCap n B i*rho^(m-i.val) =
      2*(B*rho^m/(n:ℝ))*rho*(n-i.val:ℕ) := by
    unfold localCoordinateCap
    calc
      _ = (2*B*(n-i.val:ℕ)/(n:ℝ))*(rho^(i.val+1)*rho^(m-i.val)) := by ring
      _ = _ := by rw [hpow]; ring
  have hdim : ((n-i.val:ℕ):ℝ) ≤ (m-i.val:ℕ) := by
    exact_mod_cast Nat.sub_le_sub_right hnm i.val
  have hs0 : 0 ≤ B*rho^m/(n:ℝ) := div_nonneg (mul_nonneg hB (pow_pos rho_pos _).le) hn'.le
  have hr : (B*rho^m/(n:ℝ))*rho ≤ A :=
    (mul_le_of_le_one_right hs0 rho_lt_one.le).trans hscale
  have hb : 2*((B*rho^m/(n:ℝ))*rho)*(n-i.val:ℕ) ≤
      2*A*(m-i.val:ℕ) := by
    apply mul_le_mul (mul_le_mul_of_nonneg_left hr (by norm_num)) hdim
    · exact Nat.cast_nonneg _
    · positivity
  change localCoordinateCap n B i ≤ (2*A*(m-i.val:ℕ))/rho^(m-i.val)
  apply (le_div_iff₀ (pow_pos rho_pos _)).mpr
  rw [he]
  nlinarith only [hb]

lemma locally_concentrated_all_coordinates {m n L : ℕ} {B c A : ℝ}
    (hL : L+2 ≤ n) (hnm : n ≤ m) (hB : 0 ≤ B) (hA : 0 < A)
    (hscale : B*rho^m/(n:ℝ) ≤ A)
    {u : Fin n → ℝ} (hu : u ∈ locallyConcentratedFamily m n B c L) :
    ∀ i : Fin n,u i ≤
      2*A*(m-i.val+L+2:ℕ)*(rho^(m-i.val+L+2))⁻¹ := by
  intro i
  let j : Fin n := ⟨min i.val (n-(L+2)),by omega⟩
  have hji : j ≤ i := by show j.val ≤ i.val; exact min_le_left _ _
  have hjL : j.val+L+2 ≤ n := by
    have hh : j.val ≤ n-(L+2) := min_le_right _ _
    omega
  have horder : u i ≤ u j := hu.1.1.1.2.1.antitone hji
  have hcap := hu.2 j hjL
  have hgeo := localCoordinateCap_geometric (by omega) hnm hA hscale hB j
  have hdist : m-j.val ≤ m-i.val+L+2 := by
    dsimp [j]
    have := i.isLt
    omega
  have hd := index_inv_pow_mono hdist
  exact horder.trans (hcap.trans (hgeo.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hd (show 0 ≤ 2*A by positivity))))

theorem local_candidate_coordinate_envelope : ∃ A : ℝ,0 < A ∧
    ∀ H L : ℕ,∀ᶠ x : ℝ in atTop,∀ c : ℝ,
      ∀ u ∈ locallyConcentratedFamily (m x) (m x-H) (B x) c L,
        ∀ i : Fin (m x-H),u i ≤
          A*(m x-i.val+L+2:ℕ)*(rho^(m x-i.val+L+2))⁻¹ := by
  obtain ⟨A,hA,hscale⟩ := natural_coordinate_scale_upper
  refine ⟨2*A,by positivity,?_⟩
  intro H L
  filter_upwards [hscale H,m_tendsto.eventually (eventually_ge_atTop (H+L+2)),
    B_tendsto.eventually (eventually_ge_atTop (0:ℝ))] with x hx hm hB
  intro c u hu i
  exact locally_concentrated_all_coordinates (by omega) (Nat.sub_le _ _) hB hA hx.2 hu i

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalPrimeGrid
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive prime mass with geometric upper bounds at every local index. -/
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

lemma localPrimeGrid_subset {x c : ℝ} {L n : ℕ} :
    localPrimeGrid x c L n ⊆ headLimitedPrimeGrid x c n := by
  intro b hb
  obtain ⟨hb,u,hu,hs⟩ := Finset.mem_filter.mp hb
  exact Finset.mem_filter.mpr ⟨hb,u,hu,hs.1⟩

theorem local_prime_coordinates {c : ℝ} (hc : 0 < c) :
    ∃ A : ℝ,0 < A ∧ ∀ L : ℕ,∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∀ n : ℕ,n+H=m x → ∀ p ∈ gridPrimeTuples (localPrimeGrid x c L n),
        (∀ i,(p i).Prime) ∧
        primePrefixCoord p ∈ relaxedGeometricFamily (m x) n (B x) (c/2) ∧
        (∀ i,primePrefixCoord p i ≤ (19/25:ℝ)*B x) ∧
        ∀ i,primePrefixCoord p i ≤
          A*(m x-i.val+L+2:ℕ)*(rho^(m x-i.val+L+2))⁻¹+1 := by
  obtain ⟨A,hA,hupper⟩ := local_candidate_coordinate_envelope
  refine ⟨A,hA,?_⟩
  intro L
  filter_upwards [head_limited_prime_coordinates hc] with H hH
  filter_upwards [hH,hupper H L] with x hx hu
  intro n hn p hp
  have hpn : p ∈ gridPrimeTuples (headLimitedPrimeGrid x c n) := by
    obtain ⟨b,hb,hpb⟩ := Finset.mem_biUnion.mp hp
    exact Finset.mem_biUnion.mpr ⟨b,localPrimeGrid_subset hb,hpb⟩
  obtain ⟨hpr,hr,hcap⟩ := hx n hn p hpn
  refine ⟨hpr,hr,hcap,?_⟩
  obtain ⟨b,hb,hpb⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨_,u,hucell,hfamily⟩ := Finset.mem_filter.mp hb
  have hpcell := (mem_primeBoxTuples_iff.mp hpb).2
  have hdist := unitGridCell_coordinate_distance hucell hpcell
  have hdim : n=m x-H := by omega
  subst n
  intro i
  have hupp := hu c u hfamily i
  have hclose := (neg_le_abs _).trans (hdist i)
  linarith only [hupp,hclose]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalPrimeSupport
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each suffix lies in a prime interval determined only by its distance from the end. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma localPrimeHeight_ge_two {A : ℝ} (hA : 0 ≤ A) (L h : ℕ) :
    2 ≤ localPrimeHeight A L h := by
  unfold localPrimeHeight
  have hn : 0 ≤ A*(h+L+2:ℕ)*(rho^(h+L+2))⁻¹ :=
    mul_nonneg (mul_nonneg hA (Nat.cast_nonneg _)) (inv_pos.mpr (pow_pos rho_pos _)).le
  linarith only [hn]

lemma localPrimeHeight_mono {A : ℝ} (hA : 0 ≤ A) (L : ℕ) :
    Monotone (localPrimeHeight A L) := by
  intro h k hhk
  have hh : h+L+2 ≤ k+L+2 := by omega
  have he := mul_le_mul_of_nonneg_left (index_inv_pow_mono hh) hA
  unfold localPrimeHeight
  simpa only [mul_assoc,add_comm] using add_le_add_right he 2

lemma localPrimeHeight_log_bound {A : ℝ} (hA : 0 < A) (L : ℕ) :
    ∃ D : ℝ,0 < D ∧ ∀ᶠ h : ℕ in atTop,
      Real.log (6*localPrimeHeight A L h) ≤ D*h := by
  let D := |Real.log (6*(A+2))|+2*(1+lam)
  have hD : 0 < D := by dsimp [D] <;> linarith [lam_pos,abs_nonneg (Real.log (6*(A+2)))]
  refine ⟨D,hD,?_⟩
  filter_upwards [eventually_ge_atTop (L+2),eventually_ge_atTop 1] with h hh hh1
  let k := h+L+2
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by dsimp [k]; omega)
  have hk0 : (0:ℝ) < k := zero_lt_one.trans_le hk1
  have hkh : (k:ℝ) ≤ 2*h := by exact_mod_cast (show k ≤ 2*h by dsimp [k]; omega)
  have hr : (1:ℝ) ≤ (rho^k)⁻¹ :=
    (one_le_inv₀ (pow_pos rho_pos _)).mpr (pow_le_one₀ rho_pos.le rho_lt_one.le)
  have hkr : (1:ℝ) ≤ (k:ℝ)*(rho^k)⁻¹ := one_le_mul_of_one_le_of_one_le hk1 hr
  have hu : localPrimeHeight A L h ≤ (A+2)*(k:ℝ)*(rho^k)⁻¹ := by
    unfold localPrimeHeight
    change A*(k:ℝ)*(rho^k)⁻¹+2 ≤ _
    nlinarith only [hkr]
  have hu0 : 0 < localPrimeHeight A L h :=
    lt_of_lt_of_le (by norm_num) (localPrimeHeight_ge_two hA.le L h)
  have hlog := Real.log_le_log (mul_pos (by norm_num) hu0)
    (mul_le_mul_of_nonneg_left hu (by norm_num : (0:ℝ) ≤ 6))
  have he : 6*((A+2)*(k:ℝ)*(rho^k)⁻¹) = (6*(A+2))*(k:ℝ)*(rho^k)⁻¹ := by ring
  rw [he,Real.log_mul (mul_pos (by linarith) hk0).ne' (inv_ne_zero (pow_pos rho_pos _).ne'),
    Real.log_mul (by linarith : 6*(A+2) ≠ 0) hk0.ne',Real.log_inv,Real.log_pow] at hlog
  have hlrho : Real.log rho= -lam := by simp [lam,one_div,Real.log_inv]
  rw [hlrho] at hlog
  have hklog := Real.log_le_self hk0.le
  have hconst := mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ h by exact_mod_cast hh1)
    (abs_nonneg (Real.log (6*(A+2))))
  have hlinear := mul_le_mul_of_nonneg_left hkh (show 0 ≤ 1+lam by linarith [lam_pos])
  dsimp [D]
  nlinarith only [hlog,hklog,hconst,hlinear,le_abs_self (Real.log (6*(A+2)))]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalResidualDecay
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summable numerical bounds for the local residual reciprocal masses. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma localPrimeHeight_linear_geometric {A : ℝ} (hA : 0 ≤ A) (L : ℕ) :
    ∃ C : ℝ,0 < C ∧ ∀ h : ℕ,
      localPrimeHeight A L h ≤ C*((h:ℝ)+1)*(rho^h)⁻¹ := by
  let C := A*(L+2:ℕ)*(rho^(L+2))⁻¹+2
  refine ⟨C,?_,?_⟩
  · dsimp [C]
    exact add_pos_of_nonneg_of_pos
      (mul_nonneg (mul_nonneg hA (Nat.cast_nonneg _))
        (inv_pos.mpr (pow_pos rho_pos _)).le) (by norm_num)
  · intro h
    have hk : (h+L+2:ℕ) ≤ (L+2:ℕ)*((h:ℝ)+1) := by
      push_cast
      nlinarith only [Nat.cast_nonneg (α:=ℝ) L,Nat.cast_nonneg (α:=ℝ) h]
    have hinv : 1 ≤ (rho^h)⁻¹ :=
      (one_le_inv₀ (pow_pos rho_pos _)).mpr (pow_le_one₀ rho_pos.le rho_lt_one.le)
    have hh : 1 ≤ ((h:ℝ)+1)*(rho^h)⁻¹ :=
      one_le_mul_of_one_le_of_one_le (by have := Nat.cast_nonneg (α:=ℝ) h; linarith) hinv
    have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk hA)
      (mul_nonneg (inv_pos.mpr (pow_pos rho_pos h)).le
        (inv_pos.mpr (pow_pos rho_pos (L+2))).le)
    unfold localPrimeHeight
    rw [show h+L+2=h+(L+2) by omega,pow_add,mul_inv]
    dsimp [C]
    push_cast at hmul ⊢
    nlinarith only [hmul,hh]

theorem local_residual_mass_decay {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (L : ℕ) :
    ∀ᶠ h : ℕ in atTop,C*localPrimeHeight A L h*rho^(3*h) ≤ rho^h := by
  obtain ⟨D,hD,hbound⟩ := localPrimeHeight_linear_geometric hA L
  have ht : Tendsto (fun h : ℕ => C*D*((h:ℝ)+1)*rho^h) atTop (nhds 0) := by
    have hlin := tendsto_pow_const_mul_const_pow_of_lt_one 1 rho_pos.le rho_lt_one
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one rho_pos.le rho_lt_one
    convert (hlin.add hpow).const_mul (C*D) using 1
    · funext h
      simp only [pow_one]
      ring_nf
    · ring_nf
  filter_upwards [ht.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with h hh
  have hsmall : C*D*((h:ℝ)+1)*rho^h ≤ 1 := hh.le
  have hr : rho^h ≤ 1 := pow_le_one₀ rho_pos.le rho_lt_one.le
  have hpow : rho^(3*h)=(rho^h)^3 := by rw [←pow_mul]; congr 1; omega
  have he : C*(D*((h:ℝ)+1)*(rho^h)⁻¹)*rho^(3*h) =
      (C*D*((h:ℝ)+1)*rho^h)*rho^h := by
    rw [hpow]
    field_simp
  calc
    _ ≤ C*(D*((h:ℝ)+1)*(rho^h)⁻¹)*rho^(3*h) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hbound h) hC)
        (pow_pos rho_pos _).le
    _ = (C*D*((h:ℝ)+1)*rho^h)*rho^h := he
    _ ≤ rho^h := by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hsmall (pow_pos rho_pos h).le

lemma local_geometric_inverse_fourth {c t : ℝ} {h : ℕ}
    (hc : 0 < c) (ht : c*(rho^h)⁻¹ ≤ t) :
    t^(-4:ℝ) ≤ (c^4)⁻¹*rho^(4*h) := by
  have hc0 : 0 < c*(rho^h)⁻¹ := mul_pos hc (inv_pos.mpr (pow_pos rho_pos _))
  have ht0 : 0 < t := hc0.trans_le ht
  have hh := inv_anti₀ (pow_pos hc0 4) (pow_le_pow_left₀ hc0.le ht 4)
  have he : t^(-4:ℝ)=(t^4)⁻¹ := by
    rw [Real.rpow_neg ht0.le]
    norm_num
  rw [he]
  apply hh.trans_eq
  rw [mul_pow,inv_pow,mul_inv,inv_inv,←pow_mul]
  congr 1
  congr 1
  omega

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTLocalValueEnvelope
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Local value and right-preimage prime bounds from the actual candidate
prime product.  A late residual is controlled by its own coordinate
envelope, rather than by the original ambient counting parameter.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

/-- The seed-times-totient value is bounded directly by the sum of the
logarithms of the actual primes. -/
lemma ppt_seed_totient_prime_product_log_le {d n : ℕ} {T : ℝ}
    (hd : 0 < d) (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime)
    (hcoords : ∀ i, B (p i) ≤ T) :
    Real.log ((d*(∏ i, p i).totient : ℕ) : ℝ) ≤
      Real.log (d : ℝ)+(n : ℝ)*Real.exp T := by
  have hprod : 0 < ∏ i, p i := Finset.prod_pos (fun i _ => (hp i).pos)
  have hφ : 0 < (∏ i, p i).totient := Nat.totient_pos.mpr hprod
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hφR : (0 : ℝ) < (∏ i, p i).totient := by exact_mod_cast hφ
  have hφlog := Real.log_le_log hφR
    (Nat.cast_le.mpr (Nat.totient_le (∏ i, p i)))
  have hprodlog := prime_tail_log_bound p hp (by
    intro i
    simpa only [primePrefixCoord, B] using hcoords i)
  rw [Nat.cast_mul, Real.log_mul hdR.ne' hφR.ne']
  linarith only [hφlog, hprodlog]

/-- A product with at most `H+1` prime factors has value below the
double-exponential endpoint of its local coordinate height. -/
theorem ppt_local_prime_product_value_bound {d n H : ℕ} {T : ℝ}
    (hd : 0 < d) (hT : 0 ≤ T) (hn : n ≤ H+1)
    (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime)
    (hcoords : ∀ i, B (p i) ≤ T) :
    ((d*(∏ i, p i).totient : ℕ) : ℝ) ≤
      Real.exp (Real.exp (pptLocalValueHeight d H T)) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hlogd : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg hd1
  have hbase : 1 ≤ Real.log (d : ℝ)+(H : ℝ)+1 := by
    linarith [(Nat.cast_nonneg H : (0 : ℝ) ≤ H)]
  have hnR : (n : ℝ) ≤ (H : ℝ)+1 := by exact_mod_cast hn
  have hseed := mul_le_mul_of_nonneg_left (Real.one_le_exp hT) hlogd
  have hdim := mul_le_mul_of_nonneg_right hnR (Real.exp_pos T).le
  have hlog : Real.log ((d*(∏ i, p i).totient : ℕ) : ℝ) ≤
      Real.exp (pptLocalValueHeight d H T) := by
    apply (ppt_seed_totient_prime_product_log_le hd p hp hcoords).trans
    unfold pptLocalValueHeight
    rw [Real.exp_add, Real.exp_log (zero_lt_one.trans_le hbase)]
    nlinarith only [hseed, hdim]
  have hv : (0 : ℝ) < (d*(∏ i, p i).totient : ℕ) := by
    exact_mod_cast Nat.mul_pos hd (Nat.totient_pos.mpr
      (Finset.prod_pos (fun i _ => (hp i).pos)))
  simpa only [Real.exp_log hv] using Real.exp_le_exp.mpr hlog

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalResidualHeight
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single geometric height controls each residual value and its dyadic layers. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma local_residual_value_height {A : ℝ} (_hA : 0 ≤ A) (L h d : ℕ)
    (hd : 0 < d) :
    pptLocalValueHeight d h (localPrimeHeight A L h) ≤
      localPrimeHeight (A+Real.log d+2) L h := by
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hlogd : 0 ≤ Real.log (d:ℝ) := Real.log_nonneg hd1
  let k := h+L+2
  have hk : (h:ℝ)+1 ≤ k := by dsimp [k]; push_cast <;> linarith
  have hk0 : (1:ℝ) ≤ k := by linarith only [hk,Nat.cast_nonneg (α:=ℝ) h]
  have hr : (1:ℝ) ≤ (rho^k)⁻¹ :=
    (one_le_inv₀ (pow_pos rho_pos _)).mpr (pow_le_one₀ rho_pos.le rho_lt_one.le)
  have ht : (k:ℝ) ≤ (k:ℝ)*(rho^k)⁻¹ := le_mul_of_one_le_right (by positivity) hr
  have hl := Real.log_le_self (show 0 ≤ Real.log (d:ℝ)+(h:ℝ)+1 by positivity)
  unfold pptLocalValueHeight localPrimeHeight
  change A*(k:ℝ)*(rho^k)⁻¹+2+Real.log (Real.log (d:ℝ)+(h:ℝ)+1) ≤
    (A+Real.log (d:ℝ)+2)*(k:ℝ)*(rho^k)⁻¹+2
  have hmul := mul_le_mul_of_nonneg_left (hk0.trans ht) hlogd
  nlinarith only [hl,hk,ht,hmul]

theorem local_residual_value_bound {A : ℝ} (hA : 0 ≤ A)
    (L h d n : ℕ) (hd : 0 < d) (hn : n ≤ h+1)
    (p : Fin n → ℕ) (hp : ∀ i,(p i).Prime)
    (hcoords : ∀ i,B (p i) ≤ localPrimeHeight A L h) :
    ((d*(∏ i,p i).totient:ℕ):ℝ) ≤
      Real.exp (Real.exp (localPrimeHeight (A+Real.log d+2) L h)) := by
  have hh := ppt_local_prime_product_value_bound hd
    (show 0 ≤ localPrimeHeight A L h from (by norm_num : (0:ℝ)≤2).trans
      (localPrimeHeight_ge_two hA L h)) hn p hp hcoords
  exact hh.trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr
    (local_residual_value_height hA L h d hd)))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalSuffixBounds
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both endpoint bounds for the actual suffix products of the local grid. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma prime_predecessor_le_seed_totient {r p d : ℕ} (hr : 0 < r)
    (hp : p.Prime) (hpr : p ∣ r) (hd : 0 < d) : p-1 ≤ d*r.totient := by
  have hdiv : p-1 ∣ r.totient := by
    simpa only [Nat.totient_prime hp] using Nat.totient_dvd_of_dvd hpr
  have hle := Nat.le_of_dvd (Nat.totient_pos.mpr hr) hdiv
  exact hle.trans (Nat.le_mul_of_pos_left _ hd)

theorem local_prime_suffix_value_bounds {c : ℝ} (hc : 0 < c)
    (d : ℕ) (hd : 0 < d) :
    ∃ A : ℝ,0 < A ∧ ∀ L : ℕ,∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∀ n : ℕ,n+H=m x → ∀ p ∈ gridPrimeTuples (localPrimeGrid x c L n),
      ∀ i : Fin n,
        (c/2)*(rho^(m x-i.val))⁻¹ ≤ B (p i) ∧
        p i-1 ≤ d*(∏ j,primeFinal p i.val j).totient ∧
        ((d*(∏ j,primeFinal p i.val j).totient:ℕ):ℝ) ≤
          Real.exp (Real.exp (localPrimeHeight (A+Real.log d+2) L (m x-i.val))) := by
  obtain ⟨A,hA,hcoords⟩ := local_prime_coordinates hc
  refine ⟨A,hA,?_⟩
  intro L
  filter_upwards [hcoords L] with H hH
  filter_upwards [hH] with x hx
  intro n hn p hp i
  obtain ⟨hpr,hgeom,_,hu⟩ := hx n hn p hp
  have hpos : 0 < ∏ j,primeFinal p i.val j := by
    exact Finset.prod_pos (fun j _ => (hpr _).pos)
  have hdiv : p i ∣ ∏ j,primeFinal p i.val j := by
    let j : Fin (n-i.val) := ⟨0,by have := i.isLt; omega⟩
    have he : primeFinal p i.val j=p i := by
      apply congrArg p
      apply Fin.ext
      simp [j]
    rw [←he]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  refine ⟨hgeom.2.1 i,prime_predecessor_le_seed_totient hpos (hpr i) hdiv hd,?_⟩
  apply local_residual_value_bound hA.le L (m x-i.val) d (n-i.val) hd (by omega)
    (primeFinal p i.val) (fun j => hpr _)
  intro j
  let k : Fin n := ⟨i.val+j.val,by have := j.isLt; omega⟩
  have hk : m x-k.val ≤ m x-i.val := Nat.sub_le_sub_left (by dsimp [k]; omega) _
  have he : B (primeFinal p i.val j) ≤ localPrimeHeight A L (m x-k.val) := by
    have hh := hu k
    change B (p k) ≤ _
    unfold localPrimeHeight
    change primePrefixCoord p k ≤ _
    linarith only [hh]
  exact he.trans (localPrimeHeight_mono hA.le L hk)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalResidualLayers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform dyadic data from the actual geometric residual endpoints. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma predecessor_B_lower {p v : ℕ} (hp : 2 ≤ p) (hv : 2 ≤ v)
    (hpv : p-1 ≤ v) : B p ≤ B v+1 := by
  have hp1 : (1:ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hv2 : (2:ℝ) ≤ v := by exact_mod_cast hv
  have hle : (p:ℝ) ≤ 2*v := by
    exact_mod_cast (show p ≤ 2*v by omega)
  exact (B_mono hp1 hle).trans (double_log_double_le hv2)

lemma local_dyadic_height {U : ℝ} (hU : 2 ≤ U) {v : ℕ} (hv : 1 < v)
    (hvu : (v:ℝ) ≤ Real.exp (Real.exp U)) :
    v ≤ 2^discardExponent U ∧
    B ((2:ℝ)^(Nat.clog 2 v)) ≤ 2*U+1 ∧
    1+Real.log (discardExponent U) ≤ 3*U := by
  have hbound := discardPrimeBound_bounds hU
  have hU' : U ≤ (6/5:ℝ)*U := by linarith only [hU]
  have hvN : (v:ℝ) ≤ discardPrimeBound U :=
    hvu.trans ((Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hU')).trans hbound.2.2.2)
  have hvN' : v ≤ 2^discardExponent U := by exact_mod_cast hvN
  have hk : Nat.clog 2 v ≤ discardExponent U :=
    (Nat.clog_le_iff_le_pow (by decide : 1<2)).mpr hvN'
  have hz1 : 1 < (2:ℝ)^(Nat.clog 2 v) :=
    lt_of_lt_of_le (by exact_mod_cast hv) (dyadic_nat_bounds hv).2.2
  have hle : (2:ℝ)^(Nat.clog 2 v) ≤ (discardPrimeBound U:ℝ) := by
    simpa only [discardPrimeBound,Nat.cast_pow,Nat.cast_ofNat] using
      pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hk
  refine ⟨hvN',(B_mono hz1 hle).trans hbound.2.2.1,?_⟩
  have hlog := (discardExponent_bounds hU).2
  linarith only [hlog,hU]

theorem local_residual_layer_bounds {c A : ℝ} (hc : 0 < c) (hA : 0 < A)
    (L : ℕ) : ∃ D : ℝ,0 < D ∧ ∀ z₀ : ℝ,
      ∀ᶠ h : ℕ in atTop,∀ p v : ℕ,p.Prime → p-1 ≤ v →
        c*(rho^h)⁻¹ ≤ B p →
        (v:ℝ) ≤ Real.exp (Real.exp (localPrimeHeight A L h)) →
        1 < v ∧ v ≤ 2^discardExponent (localPrimeHeight A L h) ∧
        let z := (2:ℝ)^(Nat.clog 2 v)
        max 256 z₀ ≤ z ∧ (c/2)*(rho^h)⁻¹ ≤ B z ∧ 0 ≤ B z ∧
        Real.log (B z+4) ≤ D*h ∧
        (localSquareCutoff z:ℝ) ≤ localNormalityScale h := by
  obtain ⟨D,hD,hlog⟩ := localPrimeHeight_log_bound hA L
  refine ⟨D,hD,?_⟩
  intro z₀
  let Z := max 256 z₀
  obtain ⟨H,hH⟩ := eventually_atTop.mp
    (geometric_dominates_polynomial (half_pos hc) (max 4 (B Z+1)) 0)
  filter_upwards [eventually_ge_atTop H,hlog,local_square_cutoff_le_normality hD.le]
    with h hh hlog hcut
  intro p v hp hpv hgeo hupper
  have hlarge : max 4 (B Z+1) ≤ (c/2)*(rho^h)⁻¹ := by
    simpa only [pow_zero,mul_one] using hH h hh h le_rfl
  have hfour : 4 ≤ (c/2)*(rho^h)⁻¹ := (le_max_left _ _).trans hlarge
  have hhalf : (c/2)*(rho^h)⁻¹=(c*(rho^h)⁻¹)/2 := by ring
  have hp4 : 4 ≤ p := by
    by_contra hn
    have hp3 : (p:ℝ) ≤ 3 := by exact_mod_cast (show p≤3 by omega)
    have hlogp : 0 ≤ Real.log (p:ℝ) :=
      (Real.log_pos (by exact_mod_cast hp.one_lt)).le
    have hBp : B p ≤ p :=
      (Real.log_le_self hlogp).trans (Real.log_le_self (by positivity))
    rw [hhalf] at hfour
    linarith only [hBp,hp3,hfour,hgeo]
  have hv : 1 < v := by omega
  have hv1 : (1:ℝ) < v := by exact_mod_cast hv
  have hdata := local_dyadic_height (localPrimeHeight_ge_two hA.le L h) hv hupper
  let z := (2:ℝ)^(Nat.clog 2 v)
  have hvz : (v:ℝ) ≤ z := (dyadic_nat_bounds hv).2.2
  have hz1 : 1 < z := hv1.trans_le hvz
  have hBvz := B_mono hv1 hvz
  have hBpv := predecessor_B_lower hp.two_le (by omega) hpv
  have hBlow : (c/2)*(rho^h)⁻¹ ≤ B z := by
    rw [hhalf] at hfour ⊢
    linarith only [hfour,hBpv,hgeo,hBvz]
  have hB0 : 0 ≤ B z := (by positivity : 0≤(c/2)*(rho^h)⁻¹).trans hBlow
  have hZ : Z ≤ z := by
    have hZ0 : 1 < Z := by dsimp [Z]; have := le_max_left (256:ℝ) z₀; linarith
    have hBZZ : B Z ≤ B z := by
      have hh := (le_max_right 4 (B Z+1)).trans hlarge
      linarith only [hh,hBlow]
    exact (Real.log_le_log_iff (by linarith : 0<Z) (by linarith : 0<z)).mp
      ((Real.log_le_log_iff (Real.log_pos hZ0) (Real.log_pos hz1)).mp hBZZ)
  have hlogz : Real.log (B z+4) ≤ D*h := by
    apply le_trans _ hlog
    apply Real.log_le_log (by linarith only [hB0])
    have hU := localPrimeHeight_ge_two hA.le L h
    have hBupper : B z ≤ 2*localPrimeHeight A L h+1 := hdata.2.1
    linarith only [hBupper,hU]
  exact ⟨hv,hdata.1,hZ,hBlow,hB0,hlogz,hcut z hz1 hB0 hlogz⟩

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalRegularPrimeMass
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A positive prime mass satisfying every needed indexed normality condition. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

lemma local_regular_normality {x c : ℝ} {L H : ℕ}
    {p : Fin (m x-H) → ℕ} (hp : p ∈ localRegularPrimeTuples x c L H) :
    ∀ i j : Fin (m x-H),i ≤ j → IsNormalPrime (localNormalityScale (m x-i.val)) (p j) := by
  obtain ⟨hp,hnot⟩ := Finset.mem_sdiff.mp hp
  intro i j hij
  by_contra hn
  apply hnot
  apply Finset.mem_biUnion.mpr
  refine ⟨i,Finset.mem_univ _,Finset.mem_biUnion.mpr ?_⟩
  exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hij⟩,Finset.mem_filter.mpr ⟨hp,hn⟩⟩

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalCandidateAbundance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual prime-product candidates retaining all local normality conditions. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

lemma local_grid_tuples_subset {x c : ℝ} {L n : ℕ} :
    gridPrimeTuples (localPrimeGrid x c L n) ⊆
      gridPrimeTuples (headLimitedPrimeGrid x c n) := by
  intro p hp
  obtain ⟨b,hb,hp⟩ := Finset.mem_biUnion.mp hp
  exact Finset.mem_biUnion.mpr ⟨b,localPrimeGrid_subset hb,hp⟩

lemma local_regular_tuples_subset {x c : ℝ} {L H : ℕ} :
    localRegularPrimeTuples x c L H ⊆
      gridPrimeTuples (headLimitedPrimeGrid x c (m x-H)) := by
  intro p hp
  exact local_grid_tuples_subset (Finset.mem_sdiff.mp hp).1

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalSuffixFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The distinct bad suffixes retain the local value bounds and normality. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem local_bad_suffix_value_bounds {c : ℝ} (hc : 0 < c)
    (d : ℕ) (hd : 0 < d) :
    ∃ A : ℝ,0 < A ∧ ∀ L : ℕ,∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∀ i : Fin (m x-H),∀ r ∈ localBadSuffixValues x c d L H i,
        ((d*r.totient:ℕ):ℝ) ≤
          Real.exp (Real.exp (localPrimeHeight (A+Real.log d+2) L (m x-i.val))) ∧
        ∃ p : ℕ,p.Prime ∧ p-1 ≤ d*r.totient ∧
          (c/2)*(rho^(m x-i.val))⁻¹ ≤ B p := by
  classical
  obtain ⟨A,hA,hbound⟩ := local_prime_suffix_value_bounds hc d hd
  refine ⟨A,hA,?_⟩
  intro L
  filter_upwards [hbound L] with H hH
  filter_upwards [hH,m_tendsto.eventually (eventually_ge_atTop H)] with x hx hm
  intro i r hr
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hr
  have hregular := (Finset.mem_filter.mp hp).1
  have hpgrid := (Finset.mem_sdiff.mp hregular).1
  have hh := hx _ (Nat.sub_add_cancel hm) p hpgrid i
  refine ⟨hh.2.2,p i,?_,hh.2.1,hh.1⟩
  exact (local_regular_normality hregular i i le_rfl).1

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalResidualExceptionData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the exceptional estimates to the actual distinct suffix values. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

lemma local_regular_witness_properties {R : Finset ℕ} {F : ℕ → ℕ} {h r : ℕ}
    (hr : r ∈ localWitnessRegular R F h) :
    r∈R ∧ (∀ p : ℕ,p.Prime → p ∣ F r → IsNormalPrime (localNormalityScale h) p) ∧
      SquarefreeAbove (F r) (localNormalityScale h) ∧
      SquarefreeAbove (F r).totient (localNormalityScale h) := by
  classical
  obtain ⟨hr,hnot⟩ := Finset.mem_sdiff.mp hr
  have hn : r ∉ localWitnessNonnormal R F h := fun h => hnot (Finset.mem_union_left _ h)
  have hs : r ∉ localWitnessSquare R F h := fun h => hnot (Finset.mem_union_right _ h)
  refine ⟨hr,?_,?_,?_⟩
  · intro p hp hdiv
    by_contra hbad
    exact hn (Finset.mem_filter.mpr ⟨hr,p,hp,hdiv,hbad⟩)
  · intro p hp hlarge hdiv
    exact hs (Finset.mem_filter.mpr ⟨hr,p,hp,hlarge,Or.inl hdiv⟩)
  · intro p hp hlarge hdiv
    exact hs (Finset.mem_filter.mpr ⟨hr,p,hp,hlarge,Or.inr hdiv⟩)

lemma localNormalityScale_tendsto : Tendsto localNormalityScale atTop atTop :=
  Real.tendsto_exp_atTop.comp (Real.tendsto_exp_atTop.comp
    ((tendsto_pow_atTop (by decide : 4≠0)).comp tendsto_natCast_atTop_atTop))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalSuffixComparisonData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual bad suffixes retain the ordered geometric prime coordinates of
their parent tuple, together with an explicit order embedding. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem local_bad_suffix_geometric_data {c : ℝ} (hc : 0 < c)
    (d L : ℕ) :
    ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∀ (i : Fin (m x-H)) (r : ℕ),r ∈ localBadSuffixValues x c d L H i →
        ∃ p : Fin (m x-H) → ℕ,
          r=∏ j,primeFinal p i.val j ∧
          primePrefixCoord p ∈ relaxedGeometricFamily (m x) (m x-H) (B x) (c/2) ∧
          StrictAnti p ∧
          (∀ j,(p j).Prime) ∧
          (∀ j : Fin (m x-H-i.val),
            IsNormalPrime (localNormalityScale (m x-i.val)) (primeFinal p i.val j)) ∧
          (∀ j : Fin (m x-H-i.val),
            primePrefixCoord p (primeFinalOrderEmbedding i.val j)=B (primeFinal p i.val j)) := by
  classical
  filter_upwards [head_limited_prime_coordinates hc] with H hcoords
  filter_upwards [hcoords,m_tendsto.eventually (eventually_ge_atTop H)] with x hcoords hm
  intro i r hr
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hr
  have hpreg := (Finset.mem_filter.mp hp).1
  have hd := hcoords _ (Nat.sub_add_cancel hm) p (local_regular_tuples_subset hpreg)
  refine ⟨p,rfl,hd.2.1,prime_coordinates_strictAnti hd.1 hd.2.1.1.2.1,hd.1,?_,?_⟩
  · intro j
    exact local_regular_normality hpreg i (primeFinalOrderEmbedding i.val j)
      (by change i.val ≤ i.val+j.val; omega)
  · intro j
    rfl

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalPrimeRoughness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At each actual residual index the geometric head-prime minimum exceeds
its fourth-power normality cutoff. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem local_geometric_prime_above_normality {c : ℝ} (hc : 0 < c) :
    ∀ᶠ h : ℕ in atTop,∀ p : ℕ,p.Prime →
      c*(rho^h)⁻¹≤B p → localNormalityScale h<(p:ℝ) := by
  filter_upwards [geometric_dominates_polynomial hc 2 4,eventually_ge_atTop 1]
    with h hh hh1
  intro p hp hgeo
  have hhpos : (0:ℝ)<h := by exact_mod_cast hh1
  have hs : (h:ℝ)^4 < c*(rho^h)⁻¹ := by
    have hbound := hh h le_rfl
    have hp4 : 0<(h:ℝ)^4 := pow_pos hhpos _
    linarith only [hbound,hp4]
  have hlt : (h:ℝ)^4<B p := hs.trans_le hgeo
  have he := Real.exp_lt_exp.mpr (Real.exp_lt_exp.mpr hlt)
  have hp1 : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  simpa only [localNormalityScale,B,Real.exp_log (Real.log_pos hp1),
    Real.exp_log (zero_lt_one.trans hp1)] using he


theorem local_geometric_primes_three {c : ℝ} (hc : 0 < c) :
    ∀ᶠ H : ℕ in atTop,∀ m n : ℕ,n+H=m →
      ∀ budget : ℝ,∀ p : Fin n → ℕ,(∀ i,(p i).Prime) →
      primePrefixCoord p ∈ relaxedGeometricFamily m n budget c → ∀ i,3 ≤ p i := by
  obtain ⟨H₀,hH₀⟩ := eventually_atTop.mp (local_geometric_prime_above_normality hc)
  filter_upwards [eventually_ge_atTop H₀] with H hH
  intro m n hmn budget p hp hgeom i
  have hhi : H₀ ≤ m-i.val := by have := i.isLt; omega
  have hbig := hH₀ _ hhi _ (hp i) (hgeom.2.1 i)
  have htwo : (2:ℝ)<p i := (localNormalityScale_gt_two _).trans hbig
  have htwoN : 2<p i := by exact_mod_cast htwo
  omega

lemma ordered_prime_product_largest {N : ℕ} (hN : 0<N) (p : Fin N → ℕ)
    (hp : ∀ i,(p i).Prime) (ho : StrictAnti p) :
    largestPrimeFactor (∏ i,p i)=p ⟨0,hN⟩ := by
  apply le_antisymm
  · apply largestPrimeFactor_prod_le _ _ (hp ⟨0,hN⟩).one_lt.le
    intro i _
    rw [largestPrimeFactor_prime (hp i)]
    exact ho.antitone (show (⟨0,hN⟩ : Fin N) ≤ i from Nat.zero_le _)
  · apply prime_dvd_le_largest (hp ⟨0,hN⟩)
      (Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero))
    exact Finset.dvd_prod_of_mem p (Finset.mem_univ _)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalRegularReciprocalMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrate an actual regular-residual counting estimate over its occupied
layers. Only the fourth inverse power of the local double logarithm is needed. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem residual_fourth_power_mass (d J : ℕ) {T : ℝ} (hT : 0<T)
    (Q : Finset ℕ)
    (hrange : ∀ r∈Q,1<d*r.totient ∧ ((d*r.totient:ℕ):ℝ)≤(2:ℝ)^J)
    (hlower : ∀ r∈Q,T≤B ((2:ℝ)^(Nat.clog 2 (d*r.totient))))
    (hcount : ∀ k∈Finset.Icc 1 J,
      (Q.filter (fun r => Nat.clog 2 (d*r.totient)=k)).Nonempty →
      ((Q.filter (fun r => Nat.clog 2 (d*r.totient)=k)).card:ℝ) ≤
        (2:ℝ)^k/Real.log ((2:ℝ)^k)*(B ((2:ℝ)^k))^(-4:ℝ)) :
    (∑ r∈Q,(r.totient:ℝ)⁻¹) ≤
      (4*d/Real.log 2)*T^(-4:ℝ)*(1+Real.log J) := by
  classical
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hcoef : 0≤T^(-4:ℝ)/Real.log 2 := by positivity
  have hc (k : ℕ) (hk : k∈Finset.Icc 1 J) :
      ((Q.filter (fun r => Nat.clog 2 (d*r.totient)=k)).card:ℝ) ≤
        (T^(-4:ℝ)/Real.log 2)*(2:ℝ)^k/k := by
    by_cases hQ : (Q.filter (fun r => Nat.clog 2 (d*r.totient)=k)).Nonempty
    · obtain ⟨r,hr⟩ := hQ
      obtain ⟨hr,he⟩ := Finset.mem_filter.mp hr
      have hlo := hlower r hr
      rw [he] at hlo
      have hpow := Real.rpow_le_rpow_of_nonpos hT hlo (by norm_num : (-4:ℝ)≤0)
      have hkpos : (0:ℝ)<k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
      have hfac : 0≤(2:ℝ)^k/Real.log ((2:ℝ)^k) := by
        rw [dyadic_endpoint_log]
        positivity
      apply ((hcount k hk ⟨r,Finset.mem_filter.mpr ⟨hr,he⟩⟩).trans
        (mul_le_mul_of_nonneg_left hpow hfac)).trans_eq
      rw [dyadic_endpoint_log]
      ring
    · rw [Finset.not_nonempty_iff_eq_empty.mp hQ]
      simp only [Finset.card_empty,Nat.cast_zero]
      positivity
  apply (residual_dyadic_mass Q d J hcoef hrange hc).trans_eq
  ring

theorem local_residual_mass_of_fourth_power_count {c A : ℝ}
    (hc : 0 < c) (hA : 0<A) (d L : ℕ) :
    ∀ᶠ h : ℕ in atTop,∀ Q : Finset ℕ,
      (∀ r∈Q,∃ p : ℕ,p.Prime ∧ p-1≤d*r.totient ∧
        c*(rho^h)⁻¹≤B p ∧ ((d*r.totient:ℕ):ℝ)≤
          Real.exp (Real.exp (localPrimeHeight A L h))) →
      (∀ k∈Finset.Icc 1 (discardExponent (localPrimeHeight A L h)),
        (Q.filter (fun r => Nat.clog 2 (d*r.totient)=k)).Nonempty →
        ((Q.filter (fun r => Nat.clog 2 (d*r.totient)=k)).card:ℝ) ≤
          (2:ℝ)^k/Real.log ((2:ℝ)^k)*(B ((2:ℝ)^k))^(-4:ℝ)) →
      (∑ r∈Q,(r.totient:ℝ)⁻¹) ≤ rho^h := by
  obtain ⟨D,_hD,hlayers⟩ := local_residual_layer_bounds hc hA L
  let K : ℝ := ((c/2)^4)⁻¹
  let C : ℝ := (12*d/Real.log 2)*K
  have hC : 0≤C := by dsimp [C,K] <;> positivity
  filter_upwards [hlayers 256,local_residual_mass_decay hA.le hC L] with h hdata hdecay
  intro Q hvalues hcount
  let U := localPrimeHeight A L h
  let J := discardExponent U
  let T := (c/2)*(rho^h)⁻¹
  have hT : 0<T := mul_pos (half_pos hc) (inv_pos.mpr (pow_pos rho_pos h))
  have hpoint (r) (hr : r∈Q) :
      1<d*r.totient ∧ d*r.totient≤2^J ∧
      let z := (2:ℝ)^(Nat.clog 2 (d*r.totient))
      max 256 256≤z ∧ (c/2)*(rho^h)⁻¹≤B z ∧ 0≤B z ∧
        Real.log (B z+4)≤D*h ∧ (localSquareCutoff z:ℝ)≤localNormalityScale h := by
    obtain ⟨p,hp,hpv,hgeo,hu⟩ := hvalues r hr
    exact hdata p (d*r.totient) hp hpv hgeo hu
  have hm := residual_fourth_power_mass d J hT Q
    (fun r hr => ⟨(hpoint r hr).1,by exact_mod_cast (hpoint r hr).2.1⟩)
    (fun r hr => (hpoint r hr).2.2.2.1) hcount
  have hU := localPrimeHeight_ge_two hA.le L h
  have hJ : 1+Real.log J≤3*U := by
    have hh := (discardExponent_bounds hU).2
    dsimp only [J]
    linarith only [hh,hU]
  have hpow : T^(-4:ℝ)≤K*rho^(3*h) := by
    have hh := local_geometric_inverse_fourth (half_pos hc) (le_refl T)
    apply hh.trans
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one rho_pos.le rho_lt_one.le (by omega : 3*h≤4*h))
      (inv_nonneg.mpr (pow_nonneg (half_pos hc).le 4))
  calc
    _ ≤ (4*d/Real.log 2)*T^(-4:ℝ)*(1+Real.log J) := hm
    _ ≤ (4*d/Real.log 2)*T^(-4:ℝ)*(3*U) :=
      mul_le_mul_of_nonneg_left hJ (by positivity)
    _ ≤ (4*d/Real.log 2)*(K*rho^(3*h))*(3*U) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity))
        (by have hu : 0≤U := by dsimp only [U]; linarith only [hU]
            positivity)
    _ = C*U*rho^(3*h) := by dsimp [C] <;> ring
    _ ≤ rho^h := hdecay

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTComparisonDecay
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The fixed-seed comparison budget in the proof of Ford (5.23).  The
positive error has size at most a constant times `t^(2/3) (log t)^2`,
where `t = log log z`; the negative simplex gap has size `t/(log t)^3`.
The latter absorbs every fixed inverse power of `t`.
-/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

theorem ppt_comparison_exp_decay (A K : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ t : ℝ in atTop,
      Real.exp (A*t^(2/3 : ℝ)*(Real.log t)^2 - δ*t/(Real.log t)^3) ≤ t^(-K) := by
  have h₅ : Tendsto (fun t : ℝ => (Real.log t)^5/t^(1/3 : ℝ)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (5 : ℕ)
        (show (0 : ℝ) < 1/3 by norm_num)).tendsto_div_nhds_zero
  have h₄ : Tendsto (fun t : ℝ => (Real.log t)^4/t) atTop (𝓝 0) :=
    Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero
  have hsum : Tendsto (fun t : ℝ =>
      A*((Real.log t)^5/t^(1/3 : ℝ)) + K*((Real.log t)^4/t)) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (h₅.const_mul A).add (h₄.const_mul K)
  filter_upwards [hsum.eventually (eventually_lt_nhds hδ),
    eventually_gt_atTop (1 : ℝ)] with t hbudget ht
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hlog : 0 < Real.log t := Real.log_pos ht
  have hthird : 0 < t^(1/3 : ℝ) := Real.rpow_pos_of_pos ht0 _
  have hprod : t^(2/3 : ℝ)*t^(1/3 : ℝ) = t := by
    rw [← Real.rpow_add ht0]
    norm_num
  have h₁ : A*t^(2/3 : ℝ)*(Real.log t)^2 =
      (A*(Real.log t)^5/t^(1/3 : ℝ))*(t/(Real.log t)^3) := by
    rw [div_mul_div_comm]
    apply (eq_div_iff (mul_ne_zero hthird.ne' (pow_pos hlog 3).ne')).mpr
    calc
      _ = A*(Real.log t)^5*(t^(2/3 : ℝ)*t^(1/3 : ℝ)) := by ring
      _ = _ := by rw [hprod]
  have h₂ : K*Real.log t = (K*(Real.log t)^4/t)*(t/(Real.log t)^3) := by
    rw [div_mul_div_comm]
    apply (eq_div_iff (mul_ne_zero ht0.ne' (pow_pos hlog 3).ne')).mpr
    ring
  simp only [mul_div_assoc] at h₁ h₂
  have hbudget' : A*t^(2/3 : ℝ)*(Real.log t)^2 + K*Real.log t ≤
      δ*t/(Real.log t)^3 := by
    calc
      _ = (A*((Real.log t)^5/t^(1/3 : ℝ)) +
          K*((Real.log t)^4/t))*(t/(Real.log t)^3) := by
        rw [add_mul, ← h₁, ← h₂]
      _ ≤ δ*(t/(Real.log t)^3) :=
        mul_le_mul_of_nonneg_right hbudget.le (div_pos ht0 (pow_pos hlog 3)).le
      _ = _ := by ring
  conv_rhs => rw [Real.rpow_def_of_pos ht0]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Direct substitution of the totient scale, with the conventional
`(log log z)^(-K)` remainder in the exceptional-candidate count. -/
theorem ppt_comparison_exp_decay_at_scale (A K : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ z : ℝ in atTop,
      Real.exp (A*(B z)^(2/3 : ℝ)*(Real.log (B z))^2 -
        δ*B z/(Real.log (B z))^3) ≤ (B z)^(-K) := by
  exact (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
    (ppt_comparison_exp_decay A K hδ)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTGridCount
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Counting the finite paired-grid labels at a local PPT comparison scale.
The bound uses the local dimension and the actual mesh, independently of
the ambient Ford bands or a globally chosen normality cutoff.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

/-- The actual PPT mesh is at least the reciprocal of its local double
logarithm.  Doubling this mesh preserves the same lower bound. -/
lemma ppt_mesh_reciprocal_lower {t : ℝ} (ht0 : 0 < t) (ht : 1 ≤ Real.log t) :
    1/t ≤ (Real.log t)^5/Real.sqrt t := by
  have ht1 : 1 < t := (Real.log_pos_iff ht0.le).mp (zero_lt_one.trans_le ht)
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hsqrtle : Real.sqrt t ≤ t := by
    nlinarith only [Real.sq_sqrt ht0.le, Real.sqrt_nonneg t, ht1.le]
  have hlogpow : 1 ≤ (Real.log t)^5 := one_le_pow₀ ht
  calc
    1/t ≤ 1/Real.sqrt t := one_div_le_one_div_of_le hsqrt hsqrtle
    _ ≤ (Real.log t)^5/Real.sqrt t :=
      div_le_div_of_nonneg_right hlogpow hsqrt.le

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTGridError
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The PPT grid uses a mesh of order `(log t)^5 / sqrt t`, where `t` is the
double logarithm of the comparison scale.  With logarithmically many
coordinates its rounding and normality errors fit inside the constructed
inverse-cube row margin.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

/-- The logarithmic dimension range is uniform in the integer dimension.
Its sixth power is absorbed by the square-root denominator of the mesh. -/
theorem ppt_log_dimension_mesh_budget {C : ℝ} (_hC : 0 < C) :
    ∀ᶠ t : ℝ in atTop, ∀ H : ℕ,
      1 ≤ H → (H : ℝ) ≤ C*Real.log t →
      32*(H : ℝ)^3*((Real.log t)^5/Real.sqrt t) ≤
        1/(80*(H : ℝ)^3) := by
  have hlim : Tendsto (fun t : ℝ => (Real.log t)^11/Real.sqrt t)
      atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow, Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (11 : ℕ)
        (show (0 : ℝ) < 1/2 by norm_num)).tendsto_div_nhds_zero
  have hscaled : Tendsto (fun t : ℝ =>
      2560*C^6*((Real.log t)^11/Real.sqrt t)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hlim.const_mul (2560*C^6)
  filter_upwards [hscaled.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop (1 : ℝ)] with t ht ht1
  intro H hH hdim
  have ht0 : 0 < t := zero_lt_one.trans ht1
  have hlog : 0 < Real.log t := Real.log_pos ht1
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hH0 : (0 : ℝ) < H := zero_lt_one.trans_le hHR
  have hδ : 0 ≤ (Real.log t)^5/Real.sqrt t := by positivity
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg H) hdim 6
  have hbudget : 2560*(H : ℝ)^6*((Real.log t)^5/Real.sqrt t) ≤ 1 := by
    calc
      _ ≤ 2560*(C*Real.log t)^6*((Real.log t)^5/Real.sqrt t) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num)) hδ
      _ = 2560*C^6*((Real.log t)^11/Real.sqrt t) := by ring
      _ ≤ 1 := ht.le
  apply (le_div_iff₀ (by positivity : 0 < 80*(H : ℝ)^3)).mpr
  convert hbudget using 1
  all_goals try with_reducible_and_instances rfl
  ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTLocalDimension
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The geometric lower bound on a remaining prime coordinate bounds the
length of that suffix in terms of its own comparison scale.  This is a
local statement; it does not transfer normality from a larger scale.
-/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma ppt_local_dimension_constant_pos (c : ℝ) :
    0 < pptLocalDimensionConstant c := by
  unfold pptLocalDimensionConstant
  exact div_pos (by positivity) lam_pos

/-- A geometric endpoint lower bound gives a logarithmic local length
bound, with a constant depending only on the fixed candidate family. -/
lemma ppt_local_dimension_bound {c t U : ℝ} {H : ℕ}
    (hc : 0 < c) (ht : Real.exp 1 ≤ t)
    (hlower : c*(rho^H)⁻¹ ≤ U) (hupper : U ≤ t+1) :
    (H : ℝ) ≤ pptLocalDimensionConstant c*Real.log t := by
  have ht1 : 1 ≤ t := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans ht
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  have hlogt : 1 ≤ Real.log t := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) ht
  have hr : 0 < rho^H := pow_pos rho_pos H
  have hlog := Real.log_le_log (mul_pos hc (inv_pos.mpr hr)) (hlower.trans hupper)
  rw [Real.log_mul hc.ne' (inv_pos.mpr hr).ne', Real.log_inv, Real.log_pow] at hlog
  have hlam : Real.log rho = -lam := by
    simp only [lam, one_div, Real.log_inv, neg_neg]
  rw [hlam] at hlog
  have hlogupper : Real.log (t+1) ≤ Real.log t+1 := by
    have hh := Real.log_le_log (by positivity : 0 < t+1)
      (show t+1 ≤ 2*t by linarith only [ht1])
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ht0.ne'] at hh
    have htwo : Real.log (2 : ℝ) ≤ 1 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at hh ⊢
      exact hh
    linarith only [hh, htwo]
  have habs := mul_le_mul_of_nonneg_left hlogt (abs_nonneg (Real.log c))
  have hmain : (H : ℝ)*lam ≤ (2+|Real.log c|)*Real.log t := by
    nlinarith only [hlog, hlogupper, hlogt, neg_le_abs (Real.log c), habs]
  calc
    (H : ℝ) ≤ ((2+|Real.log c|)*Real.log t)/lam := (le_div_iff₀ lam_pos).mpr hmain
    _ = pptLocalDimensionConstant c*Real.log t := by
      unfold pptLocalDimensionConstant
      ring

/-- The endpoint form used for a largest prime in a local comparison
block.  The harmless `+1` comes from replacing `p-1` by `p`. -/
theorem ppt_local_prime_dimension {c : ℝ} (hc : 0 < c) :
    ∀ᶠ z : ℝ in atTop, ∀ (H p : ℕ),
      3 ≤ p → c*(rho^H)⁻¹ ≤ B p → (p-1 : ℕ) ≤ z →
      (H : ℝ) ≤ pptLocalDimensionConstant c*Real.log (B z) := by
  filter_upwards [B_tendsto.eventually (eventually_ge_atTop (Real.exp 1)),
    eventually_ge_atTop (Real.exp 1)] with z hB hz
  intro H p hp hlower hsize
  exact ppt_local_dimension_bound hc hB hlower (prime_coordinate_endpoint_bound hp hz hsize)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTGridSeparation
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The grid separation used in the residual comparison follows from the
actual contraction of candidate prime coordinates.  Normality changes a
prime coordinate to its largest-predecessor-factor coordinate by at most
the doubled mesh.  The inverse-cube contraction still dominates all
paired-grid padding in the logarithmic local dimension range.
-/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

/-- The first rounded coordinate keeps a fixed inverse-log-cube loss
from one.  This feeds both the published first-cutoff power restriction
and the common adaptive head endpoint. -/
theorem ppt_local_contracted_first_loss {A : ℝ} (hA : 0 < A) :
    ∀ᶠ t : ℝ in atTop, ∀ (H : ℕ) (ω u ν : ℝ),
      1 ≤ H → (H : ℝ) ≤ A*Real.log t →
      1/(10*(H : ℝ)^3) ≤ ω → ω ≤ 1 →
      u ≤ (1+1/t)/(1+ω) →
      ν ≤ u+(2*(H : ℝ)+3)*(2*((Real.log t)^5/Real.sqrt t)) →
      ν ≤ 1-(1/(80*A^3))/(Real.log t)^3 := by
  filter_upwards [ppt_log_dimension_mesh_budget hA,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_gt_atTop (1 : ℝ)] with t hbudget hlog ht
  intro H ω u ν hH hdim hω hω1 hu hν
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hH0 : (0 : ℝ) < H := zero_lt_one.trans_le hHr
  have hω0 : 0 < ω := (by positivity : 0 < 1/(10*(H : ℝ)^3)).trans_le hω
  have hden : 0 < 1+ω := by linarith only [hω0]
  have hm0 : 0 ≤ (Real.log t)^5/Real.sqrt t := by positivity
  have hrec := ppt_mesh_reciprocal_lower ht0 hlog
  let e : ℝ := 1/t+(2*(H : ℝ)+3)*(2*((Real.log t)^5/Real.sqrt t))
  have hH3 : (H : ℝ) ≤ (H : ℝ)^3 := by
    simpa only [pow_one] using (pow_le_pow_right₀ hHr (show 1 ≤ 3 by omega))
  have herr : e ≤ 1/(80*(H : ℝ)^3) := by
    apply le_trans _ (hbudget H hH hdim)
    dsimp only [e]
    have hmul := mul_le_mul_of_nonneg_right
      (show 4*(H : ℝ)+7 ≤ 32*(H : ℝ)^3 by nlinarith only [hHr, hH3]) hm0
    nlinarith only [hrec, hmul]
  have herrω : 4*e ≤ ω := by
    have hsmall : 4*(1/(80*(H : ℝ)^3)) ≤ 1/(10*(H : ℝ)^3) := by
      have hpos : 0 ≤ 1/(10*(H : ℝ)^3) := by positivity
      have he : 4*(1/(80*(H : ℝ)^3)) = (1/2 : ℝ)*(1/(10*(H : ℝ)^3)) := by ring
      rw [he]
      linarith only [hpos]
    nlinarith only [herr, hsmall, hω]
  have hu' : u ≤ 1/(1+ω)+1/t := by
    apply hu.trans
    rw [add_div]
    apply add_le_add le_rfl
    apply (div_le_iff₀ hden).mpr
    have hp : 0 ≤ (1/t)*ω := mul_nonneg (one_div_pos.mpr ht0).le hω0.le
    nlinarith only [hp]
  have hν' : ν ≤ 1/(1+ω)+e := by
    dsimp only [e]
    linarith only [hu', hν]
  have hrecω : 1/(1+ω) ≤ 1-ω/2 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hω0, hω1]
  have hmargin : (1/(80*A^3))/(Real.log t)^3 ≤ 1/(80*(H : ℝ)^3) := by
    have hp := pow_le_pow_left₀ hH0.le hdim 3
    have hh : 1/(80*(A*Real.log t)^3) ≤ 1/(80*(H : ℝ)^3) :=
      one_div_le_one_div_of_le (by positivity)
        (mul_le_mul_of_nonneg_left hp (by norm_num))
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    rw [div_div, mul_pow]
    ring
  have hsmall : 1/(80*(H : ℝ)^3) ≤ ω/4 := by
    have hnonneg : 0 ≤ 1/(80*(H : ℝ)^3) := by positivity
    have he : 1/(10*(H : ℝ)^3) = 8*(1/(80*(H : ℝ)^3)) := by ring
    rw [he] at hω
    linarith only [hω, hnonneg]
  linarith only [hν', hrecω, herrω, hmargin, hsmall]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTResidualSmallness
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small common factors and small left tails in the residual comparison. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

/-- A logarithmic number of primes below the strict first-coordinate
gap has an arbitrarily small fixed power of the local value scale. -/
theorem ppt_prime_product_subpower_of_gap {A γ ε : ℝ}
    (hA : 0 ≤ A) (hγ : 0 < γ) (hε : 0 < ε) :
    ∀ᶠ z : ℝ in atTop, ∀ (n : ℕ) (p : Fin n → ℕ),
      (∀ i, (p i).Prime) → (n : ℝ) ≤ A*Real.log (B z) →
      (∀ i, B (p i) ≤ B z-γ*B z/(Real.log (B z))^3) →
      ((∏ i, p i : ℕ) : ℝ) ≤ z^ε := by
  filter_upwards [ppt_comparison_exp_decay_at_scale 0 2 hγ,
    B_tendsto.eventually (eventually_ge_atTop (max 1 (A/ε))),
    eventually_gt_atTop (1 : ℝ)] with z hdecay ht hz
  intro n p hp hdim hcoords
  have ht1 : 1 ≤ B z := (le_max_left _ _).trans ht
  have ht0 : 0 < B z := zero_lt_one.trans_le ht1
  have htA : A/ε ≤ B z := (le_max_right _ _).trans ht
  have hN : (n : ℝ) ≤ A*B z := hdim.trans
    (mul_le_mul_of_nonneg_left (Real.log_le_self ht0.le) hA)
  have hdecay' : Real.exp (-(γ*B z/(Real.log (B z))^3)) ≤ 1/(B z)^2 := by
    simpa only [zero_mul, zero_sub, Real.rpow_neg ht0.le, Real.rpow_two, one_div] using hdecay
  have hsmall : (n : ℝ)*Real.exp (-(γ*B z/(Real.log (B z))^3)) ≤ ε := by
    calc
      _ ≤ (A*B z)*(1/(B z)^2) :=
        mul_le_mul hN hdecay' (Real.exp_pos _).le (mul_nonneg hA ht0.le)
      _ = A/B z := by field_simp
      _ ≤ ε := by
        apply (div_le_iff₀ ht0).mpr
        have hh := (div_le_iff₀ hε).mp htA
        nlinarith only [hh]
  have hlog := prime_tail_log_bound p hp (by
    intro i
    exact hcoords i)
  have hlog' : Real.log ((∏ i, p i : ℕ) : ℝ) ≤ ε*Real.log z := by
    apply hlog.trans
    calc
      _ = ((n : ℝ)*Real.exp (-(γ*B z/(Real.log (B z))^3)))*Real.exp (B z) := by
        rw [show B z-γ*B z/(Real.log (B z))^3 =
          -(γ*B z/(Real.log (B z))^3)+B z by ring, Real.exp_add]
        ring
      _ ≤ ε*Real.exp (B z) := mul_le_mul_of_nonneg_right hsmall (Real.exp_pos _).le
      _ = ε*Real.log z := by rw [B, Real.exp_log (Real.log_pos hz)]
  have hprod : (0 : ℝ) < (∏ i, p i : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun i _ => (hp i).pos)
  have hh := Real.exp_le_exp.mpr hlog'
  rw [Real.exp_log hprod] at hh
  simpa only [Real.rpow_def_of_pos (zero_lt_one.trans hz), mul_comm] using hh

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTRelativeHead
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The head of each local dyadic suffix is large relative to that suffix's value scale. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

/-- The actual inverse-cube coordinate gap makes every suffix tail a
small power of its dyadic value endpoint. The first prime therefore
satisfies the large-head hypothesis in the comparison theorem. -/
theorem ppt_local_suffix_head (d : ℕ) {A : ℝ} (hA : 0 < A) :
    ∀ᶠ z : ℝ in atTop, ∀ (N H : ℕ) (p : Fin N → ℕ) (ω : ℝ),
      ∀ hN : 0 < N,
      (∀ i, (p i).Prime) → (∀ i, 3 ≤ p i) →
      1 ≤ H → N ≤ H → (H : ℝ) ≤ A*Real.log (B z) →
      1/(10*(H : ℝ)^3) ≤ ω → ω ≤ 1 →
      (∀ i : Fin N, 0 < i.val → B (p i) ≤ B (p ⟨0,hN⟩)/(1+ω)) →
      (p ⟨0,hN⟩-1 : ℕ) ≤ z →
      z/2 < ((d*(∏ i, p i).totient : ℕ) : ℝ) →
      z^(9/10 : ℝ) < p ⟨0,hN⟩ := by
  have hγ : 0 < 1/(80*A^3) := by positivity
  filter_upwards [B_tendsto.eventually (ppt_local_contracted_first_loss hA),
    ppt_prime_product_subpower_of_gap hA.le hγ (by norm_num : (0 : ℝ) < 1/20),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/20)).eventually
      (eventually_ge_atTop (2*(d : ℝ))),
    B_tendsto.eventually (eventually_gt_atTop (1 : ℝ)),
    eventually_ge_atTop (Real.exp 1), eventually_gt_atTop (1 : ℝ)]
    with z hgap htail hconstant hB hzexp hz
  intro N H p ω hN hp hp3 hH hNH hdim hω hω1 hcontract hheadsize hvalue
  cases N with
  | zero => omega
  | succ k =>
    have hz0 : 0 < z := zero_lt_one.trans hz
    have ht : 0 < B z := zero_lt_one.trans hB
    have hH0 : (0 : ℝ) < H := by exact_mod_cast (zero_lt_one.trans_le hH)
    have hω0 : 0 < ω := (by positivity : 0 < 1/(10*(H : ℝ)^3)).trans_le hω
    have hden : 0 < 1+ω := by linarith only [hω0]
    have hhead : B (p 0) ≤ B z+1 := prime_coordinate_endpoint_bound (hp3 0) hzexp hheadsize
    let q : Fin k → ℕ := fun i => p i.succ
    have hcoords (i : Fin k) :
        B (q i) ≤ B z-(1/(80*A^3))*B z/(Real.log (B z))^3 := by
      have hu : B (q i)/B z ≤ (1+1/B z)/(1+ω) := by
        calc
          _ ≤ (B (p 0)/(1+ω))/B z :=
            div_le_div_of_nonneg_right (hcontract i.succ (by simp)) ht.le
          _ ≤ ((B z+1)/(1+ω))/B z :=
            div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hhead hden.le) ht.le
          _ = _ := by field_simp
      have hpad : B (q i)/B z ≤ B (q i)/B z+
          (2*(H : ℝ)+3)*(2*((Real.log (B z))^5/Real.sqrt (B z))) := by
        have hl : 0 ≤ Real.log (B z) := (Real.log_pos hB).le
        have he : 0 ≤ (2*(H : ℝ)+3)*(2*((Real.log (B z))^5/Real.sqrt (B z))) := by positivity
        linarith only [he]
      have hh := hgap H ω (B (q i)/B z) (B (q i)/B z) hH hdim hω hω1 hu hpad
      have hh' := (div_le_iff₀ ht).mp hh
      convert hh' using 1
      all_goals try with_reducible_and_instances rfl
      ring
    have hqdim : (k : ℝ) ≤ A*Real.log (B z) :=
      (Nat.cast_le.mpr (show k ≤ H by omega)).trans hdim
    have hprod : ((∏ i, q i : ℕ) : ℝ) ≤ z^(1/20 : ℝ) :=
      htail k q (fun i => hp i.succ) hqdim hcoords
    have hφ : ((∏ i, p i).totient : ℝ) ≤ (p 0 : ℝ)*((∏ i, q i : ℕ) : ℝ) := by
      calc
        _ ≤ ((∏ i, p i : ℕ) : ℝ) := Nat.cast_le.mpr (Nat.totient_le (∏ i, p i))
        _ = _ := by rw [Fin.prod_univ_succ, Nat.cast_mul]
    have hp0 : 0 ≤ (p 0 : ℝ) := Nat.cast_nonneg _
    have hstep : z < (2*(d : ℝ))*(p 0 : ℝ)*z^(1/20 : ℝ) := by
      have hprod' := mul_le_mul_of_nonneg_left hprod hp0
      have hφ' := hφ.trans hprod'
      have hh := mul_le_mul_of_nonneg_left hφ' (Nat.cast_nonneg d)
      push_cast at hvalue
      nlinarith only [hh, hvalue]
    have hstep' : z < (p 0 : ℝ)*z^(1/10 : ℝ) := by
      apply hstep.trans_le
      calc
        _ ≤ z^(1/20 : ℝ)*(p 0 : ℝ)*z^(1/20 : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hconstant hp0)
            (Real.rpow_pos_of_pos hz0 _).le
        _ = (p 0 : ℝ)*z^((1/20 : ℝ)+1/20) := by rw [Real.rpow_add hz0]; ring
        _ = _ := by norm_num
    have hzpow : z = z^(9/10 : ℝ)*z^(1/10 : ℝ) := by
      rw [← Real.rpow_add hz0]
      norm_num
    nth_rw 1 [hzpow] at hstep'
    exact (mul_lt_mul_iff_left₀ (Real.rpow_pos_of_pos hz0 (1/10 : ℝ))).mp hstep'


/-- Direct specialization to any suffix of the constructed geometric
prime family. Its actual first coordinate controls the local dimension
and supplies the required contraction. -/
theorem ppt_geometric_suffix_head (d : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ z : ℝ in atTop, ∀ (m n : ℕ) (budget : ℝ) (p : Fin n → ℕ),
      n ≤ m → (∀ j, (p j).Prime) → (∀ j, 3 ≤ p j) →
      primePrefixCoord p ∈ relaxedGeometricFamily m n budget c →
      ∀ i : Fin n, (p i-1 : ℕ) ≤ z →
        z/2 < ((d*(∏ j, primeFinal p i.val j).totient : ℕ) : ℝ) →
        z^(9/10 : ℝ) < p i := by
  filter_upwards [ppt_local_suffix_head d (ppt_local_dimension_constant_pos c),
    ppt_local_prime_dimension hc] with z hhead hdim
  intro m n budget p hnm hp hp3 hgeom i hsize hvalue
  have hH : 1 ≤ m-i.val := by have := i.isLt; omega
  have hN : 0 < n-i.val := Nat.sub_pos_of_lt i.isLt
  have hNle : n-i.val ≤ m-i.val := Nat.sub_le_sub_right hnm _
  have hdim' := hdim (m-i.val) (p i) (hp3 i) (hgeom.2.1 i) hsize
  have hzero : primeFinal p i.val ⟨0,hN⟩ = p i := by
    apply congrArg p
    apply Fin.ext
    simp only [Nat.add_zero]
  let ω : ℝ := 1/(10*((m-i.val : ℕ) : ℝ)^3)
  have hHr : (1 : ℝ) ≤ (m-i.val : ℕ) := by exact_mod_cast hH
  have hω1 : ω ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 10*((m-i.val : ℕ) : ℝ)^3)).mpr
    have hh : (1 : ℝ) ≤ ((m-i.val : ℕ) : ℝ)^3 := one_le_pow₀ hHr
    linarith only [hh]
  have herr : rowContractionError (m-(i.val+1))/2 = ω := by
    have he : m-(i.val+1)+1 = m-i.val := by have := i.isLt; omega
    have her : ((m-(i.val+1) : ℕ) : ℝ)+1 = ((m-i.val : ℕ) : ℝ) := by exact_mod_cast he
    dsimp only [rowContractionError, ω]
    rw [her]
    ring
  have hcontract (j : Fin (n-i.val)) (hj : 0 < j.val) :
      B (primeFinal p i.val j) ≤ B (primeFinal p i.val ⟨0,hN⟩)/(1+ω) := by
    let k : Fin n := ⟨i.val+j.val,by have := j.isLt; omega⟩
    have hik : i < k := by change i.val < i.val+j.val; omega
    have hh := hgeom.2.2 i k hik
    change B (p k) ≤ B (p i)/(1+rowContractionError (m-(i.val+1))/2) at hh
    rw [herr] at hh
    have hpk : primeFinal p i.val j = p k := by
      apply congrArg p
      apply Fin.ext
      simp only [k]
    rw [hpk,hzero]
    exact hh
  have hh := hhead (n-i.val) (m-i.val) (primeFinal p i.val) ω hN
    (fun j => hp _) (fun j => hp3 _) hH hNle hdim' le_rfl hω1 hcontract
    (by simpa only [hzero] using hsize) hvalue
  simpa only [hzero] using hh

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalSuffixRegular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the finite regular comparison count to the actual distinct suffix
values, then integrate their occupied dyadic layers. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

theorem local_suffix_regular_bound {c : ℝ} (hc : 0 < c)
    (d : ℕ) (hd : 0 < d) (L : ℕ) :
    ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,LocalSuffixRegularBound x c d L H := by
  classical
  let D := pptLocalDimensionConstant (c/2)
  have hD : 0 < D := ppt_local_dimension_constant_pos _
  obtain ⟨z₀,hz₀⟩ := eventually_atTop.mp
    ((ppt_regular_geometric_count d hd hD 4).and
      ((ppt_geometric_suffix_head d (half_pos hc)).and
        (ppt_local_prime_dimension (half_pos hc))))
  obtain ⟨A,hA,hvalues⟩ := local_bad_suffix_value_bounds hc d hd
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hA' : 0 < A+Real.log d+2 := by
    have := Real.log_nonneg hd1
    linarith
  obtain ⟨E,_hE,hlayers⟩ := local_residual_layer_bounds (half_pos hc) hA' L
  obtain ⟨H₁,hH₁⟩ := eventually_atTop.mp (hlayers z₀)
  obtain ⟨H₂,hH₂⟩ := eventually_atTop.mp
    (local_residual_mass_of_fourth_power_count (half_pos hc) hA' d L)
  obtain ⟨H₃,hH₃⟩ := eventually_atTop.mp
    (localNormalityScale_tendsto.eventually (eventually_ge_atTop (largestPrimeFactor d:ℝ)))
  filter_upwards [local_bad_suffix_geometric_data hc d L,hvalues L,
    local_geometric_primes_three (half_pos hc),
    eventually_ge_atTop (max H₁ (max H₂ (max H₃ 1)))]
    with H hdata hvalues hthree hlarge
  filter_upwards [hdata,hvalues] with x hdata hvalues
  intro i F
  dsimp only
  intro _hinj hF
  let R := localBadSuffixValues x c d L H i
  let h := m x-i.val
  let Q := localWitnessRegular R F h
  have hlarge' : max H₁ (max H₂ (max H₃ 1)) ≤ h := by
    have := i.isLt
    dsimp only [h]
    omega
  have hh1 : H₁ ≤ h := (le_max_left _ _).trans hlarge'
  have hh2 : H₂ ≤ h := (le_max_left _ _).trans ((le_max_right _ _).trans hlarge')
  have hh3 : H₃ ≤ h := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hlarge'))
  have hhpos : 1 ≤ h := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hlarge'))
  have hQR : Q⊆R := by intro r hr; exact (Finset.mem_sdiff.mp hr).1
  have hval (r) (hr : r∈Q) :
      ∃ p : ℕ,p.Prime ∧ p-1 ≤ d*r.totient ∧ (c/2)*(rho^h)⁻¹ ≤ B p ∧
        ((d*r.totient:ℕ):ℝ) ≤ Real.exp (Real.exp (localPrimeHeight (A+Real.log d+2) L h)) := by
    obtain ⟨hu,p,hp,hpv,hgeo⟩ := hvalues i r (hQR hr)
    exact ⟨p,hp,hpv,hgeo,hu⟩
  apply hH₂ h hh2 Q hval
  intro k _hk hnonempty
  let T := Q.filter (fun r => Nat.clog 2 (d*r.totient)=k)
  let z : ℝ := (2:ℝ)^k
  obtain ⟨r₀,hr₀⟩ := hnonempty
  obtain ⟨hr₀Q,hr₀k⟩ := Finset.mem_filter.mp hr₀
  obtain ⟨p₀,hp₀,hpv₀,hgeo₀,hu₀⟩ := hval r₀ hr₀Q
  have hend := hH₁ h hh1 p₀ (d*r₀.totient) hp₀ hpv₀ hgeo₀ hu₀
  have hz : max 256 z₀ ≤ z := by
    simpa only [hr₀k,z] using hend.2.2.1
  have hB0 : 0 ≤ B z := by
    simpa only [hr₀k,z] using hend.2.2.2.2.1
  obtain ⟨hcount,hhead,hdim⟩ := hz₀ z ((le_max_right _ _).trans hz)
  have hz1 : 1 < z := lt_of_lt_of_le (by norm_num : (1:ℝ) < 256) ((le_max_left _ _).trans hz)
  have hlogz : 0 < Real.log z := Real.log_pos hz1
  have hTQ : T⊆Q := Finset.filter_subset _ _
  have hTR : T⊆R := hTQ.trans hQR
  have hex (r : ℕ) : ∃ p : Fin (m x-H) → ℕ,r∈T →
      r=∏ j,primeFinal p i.val j ∧
      primePrefixCoord p ∈ relaxedGeometricFamily (m x) (m x-H) (B x) (c/2) ∧
      StrictAnti p ∧ (∀ j,(p j).Prime) ∧
      (∀ j : Fin (m x-H-i.val),IsNormalPrime (localNormalityScale h) (primeFinal p i.val j)) := by
    by_cases hr : r∈T
    · obtain ⟨p,he,hgeom,ho,hp,hn,_hembed⟩ := hdata i r (hTR hr)
      exact ⟨p,fun _ => ⟨he,hgeom,ho,hp,hn⟩⟩
    · exact ⟨fun _=>1,fun hh => (hr hh).elim⟩
  choose p hp using hex
  let q (r : ℕ) := primeFinal (p r) i.val
  let v (r : ℕ) := primePrefixCoord (p r)
  let ι (_r : ℕ) := primeFinalOrderEmbedding (N:=m x-H) i.val
  have hN : 0 < m x-H-i.val := Nat.sub_pos_of_lt i.isLt
  have hqprime (r) (hr : r∈T) (j) : (q r j).Prime := (hp r hr).2.2.2.1 _
  have hqanti (r) (hr : r∈T) : StrictAnti (q r) := by
    intro j k hjk
    exact (hp r hr).2.2.1 ((primeFinalOrderEmbedding i.val).strictMono hjk)
  have hqthree (r) (hr : r∈T) (j) : 3 ≤ q r j := by
    have hn : m x-H+H=m x := Nat.sub_add_cancel (by have := i.isLt; omega)
    exact hthree (m x) (m x-H) hn (B x) (p r) (hp r hr).2.2.2.1 (hp r hr).2.1 _
  have hrpos (r) (hr : r∈T) : 0 < r := by
    rw [(hp r hr).1]
    exact Finset.prod_pos (fun j _ => (hqprime r hr j).pos)
  have hpredecessor (r) (hr : r∈T) (j) : (q r j-1:ℕ) ≤ z := by
    have hdiv : q r j ∣ r :=
      (Finset.dvd_prod_of_mem (q r) (Finset.mem_univ j)).trans (dvd_of_eq (hp r hr).1.symm)
    have hle := prime_predecessor_le_seed_totient (hrpos r hr) (hqprime r hr j) hdiv hd
    have he := (Finset.mem_filter.mp hr).2
    have hdyad := (dyadic_nat_bounds (show 1 < d*r.totient from by
      obtain ⟨p,hp,hpv,hgeo,hu⟩ := hval r (hTQ hr)
      exact (hH₁ h hh1 p (d*r.totient) hp hpv hgeo hu).1)).2.2
    exact (Nat.cast_le.mpr hle).trans (by simpa only [he,z] using hdyad)
  have hremaining : (h:ℝ) ≤ D*Real.log (B z) := by
    have hgeo := (hp r₀ (show r₀∈T from hr₀)).2.1.2.1 i
    have hq0 : q r₀ ⟨0,hN⟩=p r₀ i := by unfold q primeFinal; congr 1
    exact hdim h (p r₀ i) (by rw [←hq0]; exact hqthree r₀ hr₀ _)
      hgeo (by rw [←hq0]; exact hpredecessor r₀ hr₀ _)
  have hresult := hcount (m x) (m x-H) (m x-H-i.val) h (B x) (c/2)
    (localNormalityScale h) T F q v ι hN (Nat.sub_le _ _) (by dsimp [h]; omega) hremaining
    (by
      apply Real.exp_le_exp.mpr
      apply Real.exp_le_exp.mpr
      have hhr : (1:ℝ) ≤ h := by exact_mod_cast hhpos
      exact one_le_pow₀ hhr)
    (by simp only [localNormalityScale,B,Real.log_exp]; exact le_rfl)
    (hH₃ h hh3)
    (by intro r hr; change m x-(i.val+0) ≤ h; simp only [add_zero]; exact le_rfl)
    (fun r hr => (hp r hr).2.1)
    (by intro r hr j; rfl)
    (fun r hr => (hp r hr).2.2.2.2)
    hqthree hqanti
    (fun r hr => ⟨(hF r (hTR hr)).1,(hF r (hTR hr)).2.1,(hp r hr).1⟩)
    (by intro r hr; exact ⟨(local_regular_witness_properties (hTQ hr)).2.2.1,
      (local_regular_witness_properties (hTQ hr)).2.2.2⟩)
    (fun r hr => (local_regular_witness_properties (hTQ hr)).2.1)
    (by
      intro r hr
      have he : largestPrimeFactor r=q r ⟨0,hN⟩ := by
        exact (congrArg largestPrimeFactor (hp r hr).1).trans
          (ordered_prime_product_largest hN (q r) (hqprime r hr) (hqanti r hr))
      rw [←he]
      exact (hF r (hTR hr)).2.2.2)
    hpredecessor
    (by
      intro r hr
      rw [(hF r (hTR hr)).2.1]
      have he := (Finset.mem_filter.mp hr).2
      have hdyad := (dyadic_nat_bounds (show 1 < d*r.totient from by
        obtain ⟨p,hp,hpv,hgeo,hu⟩ := hval r (hTQ hr)
        exact (hH₁ h hh1 p (d*r.totient) hp hpv hgeo hu).1)).2.2
      simpa only [he,z] using hdyad)
    (by
      intro r hr
      have hn : m x-H ≤ m x := Nat.sub_le _ _
      have hlow : z/2 < ((d*(∏ j,primeFinal (p r) i.val j).totient:ℕ):ℝ) := by
        rw [←(hp r hr).1]
        have he := (Finset.mem_filter.mp hr).2
        obtain ⟨p,hp,hpv,hgeo,hu⟩ := hval r (hTQ hr)
        have hdyr := (dyadic_nat_bounds (hH₁ h hh1 p (d*r.totient) hp hpv hgeo hu).1).2.1
        simpa only [he,z] using hdyr
      have hp3 := hthree (m x) (m x-H) (Nat.sub_add_cancel (by have := i.isLt; omega))
        (B x) (p r) (hp r hr).2.2.2.1 (hp r hr).2.1
      have hq0 : q r ⟨0,hN⟩=p r i := by unfold q primeFinal; congr 1
      rw [hq0]
      exact (hhead (m x) (m x-H) (B x) (p r) hn (hp r hr).2.2.2.1 hp3
        (hp r hr).2.1 i (by rw [←hq0]; exact hpredecessor r hr _) hlow).le)
  have hcoef : z/((d:ℝ)*Real.log z) ≤ z/Real.log z := by
    apply div_le_div_of_nonneg_left (zero_lt_one.trans hz1).le hlogz
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hd1 hlogz.le
  exact hresult.trans (mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hB0 _))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FiberPropagationInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Discharge the fixed-seed fiber propagation input by pruning the actual
normal candidate family. Seed one also supplies Ford's lower counting bound. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

theorem full_fiber_scale_family_oai (d : ℕ) (hd : IsTotient d) :
    ∃ a K : ℝ,0 < a ∧ 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      0 < x ∧ ∃ S : Finset ℕ,a*(x/Real.log x)*G x (m x) ≤ (S.card:ℝ) ∧
        ∀ b∈S,0 < b ∧ ((d*b.totient:ℕ):ℝ) ≤ x ∧
          FullFiber d b ∧ (b:ℝ)/b.totient ≤ K := by
  obtain ⟨q,hqpos,hq⟩ := hd
  have hdpos : 0 < d := hq ▸ Nat.totient_pos.mpr hqpos
  obtain ⟨c,δ,L,hc,hδ,_hL,habundance⟩ := local_normal_candidate_abundance
  apply full_fiber_scale_of_local_count hc hδ d hdpos L
  apply local_full_candidate_count hc hδ d q hdpos hqpos hq L
    (habundance d hdpos) _ (local_suffix_regular_bound hc d hdpos L)
  filter_upwards [ppt_original_regular_count hc d hdpos L] with H hH
  filter_upwards [hH] with x hx
  intro F
  dsimp only
  intro _hinj hF
  exact hx F hF

end TotientAsymptotic

end

end OAI
end

theorem solution : type_of% @OAI.TotientAsymptotic.full_fiber_scale_family_oai := @OAI.TotientAsymptotic.full_fiber_scale_family_oai
