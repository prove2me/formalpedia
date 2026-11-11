-- Prove2me | solution 1 for OAI.TotientAsymptotic.small_head_real_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:37:52.191419+00:00
-- url     : https://prove2.me/submissions/7fd7a9d3-e9be-4c10-b333-ada5e10d8d4d

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
import Theorems.Thm_OAI_TotientAsymptotic_bootstrap_good_nat_count

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_Basic
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arithmetic data and renewal coefficients for counting totient values. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic



lemma isTotient_pos {d : ℕ} (hd : IsTotient d) : 0 < d := by
  obtain ⟨n, hn, rfl⟩ := hd
  exact Nat.totient_pos.mpr hn

end TotientAsymptotic

end

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

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BootstrapGaussianBudget
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit preliminary counting errors fit the Gaussian Ford scale. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma logarithmic_gaussian_budget {b t c : ℝ} (hb : 1 ≤ b) (ht : 0 ≤ t)
    (hexp : Real.exp ((3/5:ℝ)*t) ≤ b)
    (hbudget : 100*(Real.log (b+4)+30)^2 ≤ c*b) :
    (b+4)^6*Real.exp (9*(Real.log (b+4))^2-c*b) ≤ Real.exp (-t^2/4) := by
  have hb0 : 0 < b := by linarith
  have hlog : 0 ≤ Real.log (b+4) := Real.log_nonneg (by linarith)
  have hlower : (3/5:ℝ)*t ≤ Real.log b := by
    have hh := Real.log_le_log (Real.exp_pos _) hexp
    simpa only [Real.log_exp] using hh
  have hmono : Real.log b ≤ Real.log (b+4) := Real.log_le_log hb0 (by linarith)
  have ht' : t ≤ 2*Real.log (b+4) := by linarith only [hlower,hmono,hlog]
  have hsq : t^2/4 ≤ (Real.log (b+4))^2 := by
    nlinarith only [sq_nonneg (2*Real.log (b+4)-t),mul_nonneg ht (sub_nonneg.mpr ht')]
  have hpow : (b+4)^6=Real.exp (6*Real.log (b+4)) := by
    simpa only [Nat.cast_ofNat,Real.exp_log (by linarith : 0 < b+4)] using
      (Real.exp_nat_mul (Real.log (b+4)) 6).symm
  rw [hpow,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith only [hbudget,hsq,hlog,sq_nonneg (Real.log (b+4))]

lemma bootstrap_error_gaussian_budget {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop,
      (B x+4)^6*Real.exp (9*(Real.log (B x+4))^2-c*B x) ≤
        Real.exp (-(m x:ℝ)^2/4) := by
  filter_upwards [dimension_exponential_lower,
    B_tendsto.eventually (eventually_ge_atTop (max 1 (((10000*(0+31)^2)/c)^(4/3:ℝ))))]
    with x hexp hb
  have hb1 : 1 ≤ B x := (le_max_left _ _).trans hb
  have hthreshold : ((10000*((0:ℝ)+31)^2)/c)^(4/3:ℝ) ≤ B x := (le_max_right _ _).trans hb
  have hbudget := four_thirds_threshold_budget hb1 (le_refl (0:ℝ)) hc hthreshold
  exact logarithmic_gaussian_budget hb1 (Nat.cast_nonneg _) hexp
    (by simpa only [add_zero] using hbudget)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ResidualFactorCount
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prime-factor counts in actual residual totients, including a repeated
last prime in the cofactor. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma omega_count_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a*b).primeFactorsList.length=a.primeFactorsList.length+b.primeFactorsList.length := by
  simpa only [List.length_append] using (Nat.perm_primeFactorsList_mul ha hb).length_eq

lemma omega_count_prod {ι : Type*} (I : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ I, f i ≠ 0) :
    (∏ i ∈ I, f i).primeFactorsList.length=∑ i ∈ I, (f i).primeFactorsList.length := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    rw [Finset.prod_insert hi,Finset.sum_insert hi,omega_count_mul
      (hf i (Finset.mem_insert_self _ _))
      (Finset.prod_ne_zero_iff.mpr (fun j hj => hf j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PreimageOmega
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

/-- Apart from the possible prime 2, every distinct prime contributes at
least one factor to the corresponding shifted-prime product. -/
lemma prime_shift_factor_count {p : ℕ} (hp : p.Prime) (hne : p ≠ 2) :
    1 ≤ (p-1).primeFactorsList.length := by
  by_contra! h
  have hnil : (p-1).primeFactorsList=[] := List.length_eq_zero_iff.mp (by omega)
  have he := Nat.prod_primeFactorsList (by have := hp.two_le; omega : p-1 ≠ 0)
  rw [hnil,List.prod_nil] at he
  have := hp.two_le
  omega

lemma preimage_factor_count {n : ℕ} (hn : 0 < n) :
    n.primeFactorsList.length ≤ n.totient.primeFactorsList.length+1 := by
  have hpn (p : ℕ) (hp : p ∈ n.primeFactors) : p ≠ 0 :=
    (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hsn (p : ℕ) (hp : p ∈ n.primeFactors) : p-1 ≠ 0 := by
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have he := congrArg (fun t : ℕ => t.primeFactorsList.length) (Nat.totient_mul_prod_primeFactors n)
  rw [omega_count_mul (Nat.totient_pos.mpr hn).ne' (Finset.prod_ne_zero_iff.mpr hpn),
    omega_count_mul hn.ne' (Finset.prod_ne_zero_iff.mpr hsn),
    omega_count_prod _ _ hpn,omega_count_prod _ _ hsn] at he
  have hpcount : (∑ p ∈ n.primeFactors, p.primeFactorsList.length)=n.primeFactors.card := by
    calc
      _ = ∑ _p ∈ n.primeFactors, 1 := by
        apply Finset.sum_congr rfl
        intro p hp
        simp [Nat.primeFactorsList_prime (Nat.prime_of_mem_primeFactors hp)]
      _ = _ := by simp
  rw [hpcount] at he
  have hs : n.primeFactors.card ≤ 1+∑ p ∈ n.primeFactors, (p-1).primeFactorsList.length := by
    have hcard : n.primeFactors.card ≤ (n.primeFactors.erase 2).card+1 := by
      by_cases hm : 2 ∈ n.primeFactors
      · have := Finset.card_pos.mpr ⟨2,hm⟩
        rw [Finset.card_erase_of_mem hm]
        omega
      · simp [hm]
    have hsum : (n.primeFactors.erase 2).card ≤ ∑ p ∈ n.primeFactors.erase 2, (p-1).primeFactorsList.length := by
      calc
        _ = ∑ _p ∈ n.primeFactors.erase 2, 1 := by simp
        _ ≤ _ := Finset.sum_le_sum (fun p hp => prime_shift_factor_count
          (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)) (Finset.mem_erase.mp hp).1)
    have hsub := Finset.sum_le_sum_of_subset (Finset.erase_subset (a := 2) (s := n.primeFactors))
      (f := fun p => (p-1).primeFactorsList.length)
    omega
  omega

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordCoordinateBounds
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete bounds and nondegeneracy of the two coordinates in the bootstrap. -/
noncomputable section
namespace TotientAsymptotic

lemma first_two_a_bounds : 0 < a 1 ∧ a 1 ≤ 1/2 ∧ 0 < a 2 ∧ a 2 ≤ 1 := by
  have h1 : a 1=2*Real.log 2-1 := by norm_num [a]
  have h2 : a 2=3*Real.log 3-2*Real.log 2-1 := by norm_num [a]
  refine ⟨a_pos (by norm_num),?_,a_pos (by norm_num),?_⟩
  · rw [h1]
    linarith [Real.log_two_lt_d9]
  · rw [h2]
    linarith [Real.log_three_lt_d9,Real.log_two_gt_d9]

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

lemma third_coordinate_bound {x : ℝ} {n : ℕ}
    (hscore : a 1*fordPrimeCoordinate n 1+a 2*fordPrimeCoordinate n 2 ≤ (101/100:ℝ)*B x) :
    fordPrimeCoordinate n 2 ≤ (4/5:ℝ)*B x := by
  have ha := first_two_a_bounds
  have hsum : (32/25:ℝ) ≤ a 1+a 2 := by
    have he : a 1+a 2=3*Real.log 3-2 := by norm_num [a] <;> ring
    rw [he]
    linarith [Real.log_three_gt_d9]
  have horder := ford_coordinate_antitone n (show 1 ≤ 2 by norm_num)
  have hnon : 0 ≤ fordPrimeCoordinate n 2 := le_max_left _ _
  have h1 := mul_le_mul_of_nonneg_left horder ha.1.le
  have h2 := mul_le_mul_of_nonneg_right hsum hnon
  nlinarith only [hscore,h1,h2,hnon]

lemma third_prime_size {x : ℝ} {n : ℕ} (hx : 1 < x)
    (hscore : a 1*fordPrimeCoordinate n 1+a 2*fordPrimeCoordinate n 2 ≤ (101/100:ℝ)*B x) :
    (fordPrime n 2:ℝ) ≤ Real.exp ((Real.log x)^(4/5:ℝ)) := by
  have hcoord := third_coordinate_bound hscore
  have hraw : B (fordPrime n 2) ≤ (4/5:ℝ)*B x := (le_max_right _ _).trans hcoord
  by_cases hi : 2 < n.primeFactorsList.length
  · have hp := fordPrime_prime hi
    have hplog : 0 < Real.log (fordPrime n 2) := Real.log_pos (by exact_mod_cast hp.one_lt)
    have hxp : 0 < Real.log x := Real.log_pos hx
    have hh := Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hraw)
    rw [B,Real.exp_log hplog,Real.exp_log (by exact_mod_cast hp.pos)] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    rw [Real.rpow_def_of_pos hxp]
    congr 2
    unfold B
    ring
  · have he : fordPrime n 2=1 := by
      unfold fordPrime
      rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hi)]
      rfl
    rw [he,Nat.cast_one]
    exact Real.one_le_exp (Real.rpow_nonneg (Real.log_pos hx).le _)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BootstrapResidualSize
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! After two leading primes, a surviving preimage has a subpower residual. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma fordCofactor_le_power (n k : ℕ) :
    fordCofactor n k ≤ (fordPrime n k)^n.primeFactorsList.length := by
  by_cases hk : k < n.primeFactorsList.length
  · let l := n.primeFactorsList.reverse.drop k
    have hmem (p : ℕ) (hp : p ∈ l) : p ≤ fordPrime n k := by
      obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hp
      have hki : k+i < n.primeFactorsList.length := by
        dsimp [l] at hi
        simp only [List.length_drop,List.length_reverse] at hi
        omega
      have he' : fordPrime n (k+i)=p := by
        rw [fordPrime_eq_get hki]
        simpa only [l,List.getElem_drop] using he
      rw [← he']
      exact fordPrime_antitone hk hki (by omega)
    have hp1 : 1 ≤ fordPrime n k := (fordPrime_prime hk).one_le
    have hl : l.length ≤ n.primeFactorsList.length := by simp [l]
    exact (List.prod_le_pow_card l _ hmem).trans (pow_le_pow_right₀ hp1 hl)
  · have hl : n.primeFactorsList.length ≤ k := by omega
    have hp : fordPrime n k=1 := by
      unfold fordPrime
      rw [List.getElem?_eq_none (by simpa using hl)]
      rfl
    have hd : n.primeFactorsList.reverse.drop k = [] :=
      List.drop_eq_nil_iff.mpr (by simpa using hl)
    simp only [fordCofactor,hd,List.prod_nil,hp,one_pow,le_refl]

lemma fordCofactor_log_le (n k : ℕ) :
    Real.log (fordCofactor n k) ≤ n.primeFactorsList.length*Real.log (fordPrime n k) := by
  have hp := fordCofactor_pos n k
  have hh := Real.log_le_log (by exact_mod_cast hp) (Nat.cast_le.mpr (fordCofactor_le_power n k))
  simpa only [Nat.cast_pow,Real.log_pow] using hh

lemma bootstrap_factor_scale : ∀ᶠ x : ℝ in atTop,
    5*B x+1 ≤ (Real.log x)^(1/100:ℝ) := by
  have h1 : Tendsto (fun b : ℝ => b*Real.exp (-(1/100:ℝ)*b)) atTop (nhds 0) := by
    simpa only [Real.rpow_one] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1:ℝ) (1/100) (by norm_num))
  have h0 : Tendsto (fun b : ℝ => Real.exp (-(1/100:ℝ)*b)) atTop (nhds 0) := by
    simpa only [Real.rpow_zero,one_mul] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (0:ℝ) (1/100) (by norm_num))
  have ht := ((h1.const_mul 5).add h0).comp B_tendsto
  simp only [mul_zero,add_zero] at ht
  filter_upwards [ht.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),
    eventually_gt_atTop (1:ℝ)] with x hx hx1
  have hlog : 0 < Real.log x := Real.log_pos hx1
  change 5*(B x*Real.exp (-(1/100:ℝ)*B x))+Real.exp (-(1/100:ℝ)*B x) < 1 at hx
  have he : (5*B x+1)*Real.exp (-(1/100:ℝ)*B x) ≤ 1 := by nlinarith only [hx]
  have hh := mul_le_mul_of_nonneg_right he (Real.exp_pos ((1/100:ℝ)*B x)).le
  have hid : Real.exp (-(1/100:ℝ)*B x)*Real.exp ((1/100:ℝ)*B x)=1 := by
    rw [← Real.exp_add]
    simp
  rw [mul_assoc,hid,mul_one,one_mul] at hh
  simpa only [Real.rpow_def_of_pos hlog,B,mul_comm] using hh

theorem bootstrap_cofactor_size : ∀ᶠ x : ℝ in atTop,∀ n : ℕ,0 < n →
    (n.totient.primeFactorsList.length:ℝ) ≤ 5*B x →
    a 1*fordPrimeCoordinate n 1+a 2*fordPrimeCoordinate n 2 ≤ (101/100:ℝ)*B x →
    (fordCofactor n 2:ℝ) ≤ Real.exp ((Real.log x)^(81/100:ℝ)) := by
  filter_upwards [bootstrap_factor_scale,eventually_gt_atTop (1:ℝ)] with x hx hx1
  intro n hn hΩ hscore
  have hlog : 0 < Real.log x := Real.log_pos hx1
  have hlen : (n.primeFactorsList.length:ℝ) ≤ 5*B x+1 := by
    have hh : (n.primeFactorsList.length:ℝ) ≤ n.totient.primeFactorsList.length+1 := by
      exact_mod_cast preimage_factor_count hn
    linarith
  have hprime := third_prime_size hx1 hscore
  have hprimeLog : Real.log (fordPrime n 2) ≤ (Real.log x)^(4/5:ℝ) := by
    have hp : 0 < fordPrime n 2 := by
      by_cases hi : 2 < n.primeFactorsList.length
      · exact (fordPrime_prime hi).pos
      · unfold fordPrime
        rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hi)]
        norm_num
    have hh := Real.log_le_log (by exact_mod_cast hp) hprime
    simpa only [Real.log_exp] using hh
  have hcof : Real.log (fordCofactor n 2) ≤ (Real.log x)^(81/100:ℝ) := by
    calc
      _ ≤ n.primeFactorsList.length*Real.log (fordPrime n 2) := fordCofactor_log_le n 2
      _ ≤ (5*B x+1)*(Real.log x)^(4/5:ℝ) :=
        (mul_le_mul_of_nonneg_left hprimeLog (Nat.cast_nonneg _)).trans
          (mul_le_mul_of_nonneg_right hlen (Real.rpow_nonneg hlog.le _))
      _ ≤ (Real.log x)^(1/100:ℝ)*(Real.log x)^(4/5:ℝ) :=
        mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg hlog.le _)
      _ = _ := by rw [← Real.rpow_add hlog]; norm_num
  exact (Real.log_le_iff_le_exp (by exact_mod_cast fordCofactor_pos n 2)).mp hcof

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BootstrapLargeHead
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A large surviving value has a largest prime in the quarter-power range. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma bootstrap_residual_quarter : ∀ᶠ x : ℝ in atTop,
    Real.exp ((Real.log x)^(81/100:ℝ)) ≤ x^(1/4:ℝ) := by
  have ht := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<19/100)).comp Real.tendsto_log_atTop
  filter_upwards [ht.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1/4)),
    eventually_gt_atTop (1:ℝ)] with x hx hx1
  have hl : 0 < Real.log x := Real.log_pos hx1
  have hp : (Real.log x)^(81/100:ℝ)=(Real.log x)*(Real.log x)^(-(19/100:ℝ)) := by
    calc
      _ = (Real.log x)^((1:ℝ)+(-(19/100:ℝ))) := by norm_num
      _ = (Real.log x)^(1:ℝ)*(Real.log x)^(-(19/100:ℝ)) := Real.rpow_add hl _ _
      _ = _ := by rw [Real.rpow_one]
  change (Real.log x)^(-(19/100:ℝ)) < 1/4 at hx
  rw [Real.rpow_def_of_pos (by linarith : 0<x)]
  apply Real.exp_le_exp.mpr
  rw [hp]
  exact mul_le_mul_of_nonneg_left hx.le hl.le

lemma quarter_prime_of_residual {x : ℝ} {n : ℕ} (hx : 1 < x) (hn : 0 < n)
    (htail : (fordCofactor n 2:ℝ) ≤ x^(1/4:ℝ))
    (hv : x^(3/4:ℝ) < (n.totient:ℝ)) :
    x^(1/4:ℝ) ≤ fordPrime n 0 := by
  have hx0 : 0 < x := by linarith
  have hpow : 0 < x^(1/4:ℝ) := Real.rpow_pos_of_pos hx0 _
  have horder : (fordPrime n 1:ℝ) ≤ fordPrime n 0 := by exact_mod_cast fordPrime_le_first n 1
  have h0 : 0 ≤ (fordPrime n 0:ℝ) := Nat.cast_nonneg _
  have htail0 : 0 ≤ (fordCofactor n 2:ℝ) := Nat.cast_nonneg _
  have hbound : (n:ℝ) ≤ (fordPrime n 0:ℝ)^2*(fordCofactor n 2:ℝ) := by
    have he := congrArg (fun m : ℕ => (m:ℝ)) (ford_first_two_factorization hn)
    simp only [Nat.cast_mul] at he
    nlinarith only [he,mul_le_mul_of_nonneg_left horder h0,htail0]
  by_contra hh
  have hp : (fordPrime n 0:ℝ) < x^(1/4:ℝ) := lt_of_not_ge hh
  have hs : (fordPrime n 0:ℝ)^2 < (x^(1/4:ℝ))^2 := by nlinarith
  have hprod : (n:ℝ) < (x^(1/4:ℝ))^2*x^(1/4:ℝ) :=
    hbound.trans_lt ((mul_le_mul_of_nonneg_left htail (sq_nonneg _)).trans_lt
      (mul_lt_mul_of_pos_right hs hpow))
  have hid : (x^(1/4:ℝ))^2*x^(1/4:ℝ)=x^(3/4:ℝ) := by
    rw [pow_two,← Real.rpow_add hx0,← Real.rpow_add hx0]
    norm_num
  rw [hid] at hprod
  have hφ : (n.totient:ℝ) ≤ n := Nat.cast_le.mpr (Nat.totient_le n)
  linarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_DyadicValueBounds
attribute [-simp] _root_.SelbergSieve.selbergBoundingSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise value-counting bounds from the finite dyadic envelope. -/
noncomputable section
namespace TotientAsymptotic

lemma log_floor_lower {x : ℝ} (hx : 4 ≤ x) :
    2 ≤ ⌊x⌋₊ ∧ Real.log x/2 ≤ Real.log (⌊x⌋₊:ℝ) := by
  have hx0 : 0 ≤ x := by linarith
  have hN : 2 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).mpr (by norm_num <;> linarith)
  refine ⟨hN,?_⟩
  have hh : x/2 ≤ (⌊x⌋₊:ℝ) := by linarith [Nat.sub_one_lt_floor x]
  have hl := Real.log_le_log (by positivity : 0 < x/2) hh
  rw [Real.log_div (by linarith : x ≠ 0) (by norm_num)] at hl
  have hl4 : Real.log (4:ℝ) ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have he : Real.log (4:ℝ)=2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num
  rw [he] at hl4
  linarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CoordinateRealEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rounding the endpoint of the coordinate count loses only an absolute factor. -/
noncomputable section
namespace TotientAsymptotic

lemma coordinate_floor_bounds {x : ℝ} (hx : 4 ≤ x) :
    2 ≤ ⌊x⌋₊ ∧ x/2 ≤ (⌊x⌋₊:ℝ) ∧ (⌊x⌋₊:ℝ) ≤ x ∧
    Real.log x/2 ≤ Real.log (⌊x⌋₊:ℝ) ∧ B x-1 ≤ B (⌊x⌋₊:ℝ) ∧ B (⌊x⌋₊:ℝ) ≤ B x := by
  have hf := log_floor_lower hx
  have hfloor := Nat.floor_le (show 0 ≤ x by linarith)
  have hbelow := Nat.sub_one_lt_floor x
  have hlog : 0 < Real.log (⌊x⌋₊:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < ⌊x⌋₊ by omega))
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlow := Real.log_le_log (show 0 < Real.log x/2 by positivity) hf.2
  rw [Real.log_div hlogx.ne' (by norm_num : (2:ℝ)≠0)] at hlow
  have hlog2 : Real.log (2:ℝ) ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hu : B (⌊x⌋₊:ℝ) ≤ B x :=
    Real.log_le_log hlog (Real.log_le_log (by exact_mod_cast (show 0 < ⌊x⌋₊ by omega)) hfloor)
  refine ⟨hf.1,by linarith,hfloor,hf.2,?_,hu⟩
  change Real.log (Real.log x)-1 ≤ Real.log (Real.log (⌊x⌋₊:ℝ))
  linarith

lemma coordinate_floor_normalization {x δ : ℝ} (hx : 4 ≤ x) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (⌊x⌋₊:ℝ)/Real.log (⌊x⌋₊:ℝ)*Real.exp (-δ*B (⌊x⌋₊:ℝ)) ≤
      2*Real.exp 1*(x/Real.log x*Real.exp (-δ*B x)) := by
  have hf := coordinate_floor_bounds hx
  have hlog : 0 < Real.log (⌊x⌋₊:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < ⌊x⌋₊ by omega))
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hnormal : (⌊x⌋₊:ℝ)/Real.log (⌊x⌋₊:ℝ) ≤ 2*(x/Real.log x) := by
    apply (div_le_iff₀ hlog).mpr
    apply (le_trans hf.2.2.1)
    have hh := mul_le_mul_of_nonneg_left hf.2.2.2.1 (show 0 ≤ 2*x/Real.log x by positivity)
    have he : (2*x/Real.log x)*(Real.log x/2)=x := by field_simp
    rw [he] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hexp : Real.exp (-δ*B (⌊x⌋₊:ℝ)) ≤ Real.exp 1*Real.exp (-δ*B x) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_left hf.2.2.2.2.1 hδ,hδ1]
  have hh := mul_le_mul hnormal hexp (Real.exp_pos _).le (by positivity : 0 ≤ 2*(x/Real.log x))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BootstrapRealGaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer the explicit preliminary exception to every real endpoint. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

theorem bootstrap_good_real_gaussian : ∃ C : ℝ,0 < C ∧
    ∀ᶠ x : ℝ in atTop,∀ Ψ : ℕ,Ψ ≤ m x → ∀ Q : Finset ℕ,
    (∀ v ∈ Q,IsTotient v ∧ (v:ℝ) ≤ x ∧ ¬BootstrapGood ⌊x⌋₊ v) →
    (Q.card:ℝ) ≤ C*(x/Real.log x)*G x (m x)*Real.exp (-(Ψ:ℝ)^2/4) := by
  obtain ⟨A,hA,hcount⟩ := bootstrap_good_nat_count
  refine ⟨2*Real.exp 1*A,by positivity,?_⟩
  filter_upwards [tendsto_nat_floor_atTop.eventually hcount,
    B_tendsto.eventually (eventually_ge_atTop (2:ℝ)),eventually_ge_atTop (4:ℝ),
    bootstrap_error_gaussian_budget (by norm_num : (0:ℝ)<1/600000000),
    central_volume_one_le] with x hc hb hx hbudget hG
  intro Ψ hΨ Q hQ
  have hf := coordinate_floor_bounds hx
  have hbf : 0 ≤ B (⌊x⌋₊:ℝ) := by linarith only [hf.2.2.2.2.1,hb]
  have hbx : 0 ≤ B x := by linarith only [hb]
  have hlog : 0 < Real.log x := Real.log_pos (by linarith only [hx])
  have hlogf : 0 < Real.log (⌊x⌋₊:ℝ) := Real.log_pos
    (by exact_mod_cast (show 1 < ⌊x⌋₊ from lt_of_lt_of_le (by norm_num) hf.1))
  have hh := hc Q (by
    intro v hv
    exact ⟨(hQ v hv).1,Nat.le_floor (hQ v hv).2.1,(hQ v hv).2.2⟩)
  have hpoly : (B (⌊x⌋₊:ℝ)+4)^6*Real.exp (9*(Real.log (B (⌊x⌋₊:ℝ)+4))^2) ≤
      (B x+4)^6*Real.exp (9*(Real.log (B x+4))^2) := by
    have hlower : 0 ≤ Real.log (B (⌊x⌋₊:ℝ)+4) := Real.log_nonneg (by linarith only [hbf])
    have hl := Real.log_le_log (by linarith only [hbf] : 0 < B (⌊x⌋₊:ℝ)+4)
      (by linarith only [hf.2.2.2.2.2] : B (⌊x⌋₊:ℝ)+4 ≤ B x+4)
    apply mul_le_mul
    · exact pow_le_pow_left₀ (by linarith only [hbf]) (by linarith only [hf.2.2.2.2.2]) 6
    · apply Real.exp_le_exp.mpr
      nlinarith only [hlower,hl]
    · positivity
    · positivity
  have hnorm := coordinate_floor_normalization (δ:=1/600000000) hx (by norm_num) (by norm_num)
  have hweight : bootstrapErrorWeight (B (⌊x⌋₊:ℝ))*((⌊x⌋₊:ℝ)/Real.log (⌊x⌋₊:ℝ)) ≤
      2*Real.exp 1*bootstrapErrorWeight (B x)*(x/Real.log x) := by
    have hfac : 0 ≤ ((⌊x⌋₊:ℝ)/Real.log (⌊x⌋₊:ℝ))*Real.exp (-(1/600000000:ℝ)*B (⌊x⌋₊:ℝ)) := by positivity
    have hprod := mul_le_mul hpoly hnorm hfac (by positivity)
    have he (b : ℝ) : Real.exp (9*(Real.log (b+4))^2-b/600000000)=
        Real.exp (9*(Real.log (b+4))^2)*Real.exp (-(1/600000000:ℝ)*b) := by
      rw [← Real.exp_add]
      congr 1
      ring
    unfold bootstrapErrorWeight
    rw [he,he]
    convert hprod using 1 <;> first | (with_reducible_and_instances rfl) | (ring_nf)
  have hsq : (Ψ:ℝ)^2 ≤ (m x:ℝ)^2 := by
    have ht : (Ψ:ℝ) ≤ m x := by exact_mod_cast hΨ
    nlinarith only [ht,Nat.cast_nonneg (α:=ℝ) Ψ,Nat.cast_nonneg (α:=ℝ) (m x)]
  have hsave : bootstrapErrorWeight (B x) ≤ Real.exp (-(Ψ:ℝ)^2/4) := by
    have hh : bootstrapErrorWeight (B x) ≤ Real.exp (-(m x:ℝ)^2/4) := by
      simpa only [bootstrapErrorWeight,div_eq_mul_inv,one_mul,mul_comm] using hbudget
    exact hh.trans (Real.exp_le_exp.mpr (by linarith only [hsq]))
  have hbase : 0 ≤ (2*Real.exp 1*A)*(x/Real.log x) := by positivity
  calc
    _ ≤ A*bootstrapErrorWeight (B (⌊x⌋₊:ℝ))*((⌊x⌋₊:ℝ)/Real.log (⌊x⌋₊:ℝ)) := hh
    _ = A*(bootstrapErrorWeight (B (⌊x⌋₊:ℝ))*((⌊x⌋₊:ℝ)/Real.log (⌊x⌋₊:ℝ))) := by ring
    _ ≤ A*(2*Real.exp 1*bootstrapErrorWeight (B x)*(x/Real.log x)) := mul_le_mul_of_nonneg_left hweight hA.le
    _ = ((2*Real.exp 1*A)*(x/Real.log x))*bootstrapErrorWeight (B x) := by ring
    _ ≤ ((2*Real.exp 1*A)*(x/Real.log x))*Real.exp (-(Ψ:ℝ)^2/4) := mul_le_mul_of_nonneg_left hsave hbase
    _ ≤ _ := by
      have ht := mul_le_mul_of_nonneg_left hG hbase
      simpa only [mul_one] using mul_le_mul_of_nonneg_right ht (Real.exp_pos _).le

lemma bootstrap_floor_good_large_head : ∀ᶠ x : ℝ in atTop,∀ v n : ℕ,
    BootstrapGood ⌊x⌋₊ v → x^(3/4:ℝ) < (v:ℝ) → 0 < n → n.totient=v →
    x^(1/4:ℝ) ≤ fordPrime n 0 := by
  filter_upwards [bootstrap_cofactor_size,bootstrap_residual_quarter,
    eventually_ge_atTop (4:ℝ)] with x hcof hquarter hx
  intro v n hv hlarge hn hφ
  have hmono := (coordinate_floor_bounds hx).2.2.2.2.2
  have hΩ : (n.totient.primeFactorsList.length:ℝ) ≤ 5*B x := by
    rw [hφ]
    exact hv.1.1.trans (by linarith only [hmono])
  have hscore : a 1*fordPrimeCoordinate n 1+a 2*fordPrimeCoordinate n 2 ≤ (101/100:ℝ)*B x :=
    (hv.2 n hn hφ).trans (by linarith only [hmono])
  have htail := (hcof n hn hΩ hscore).trans hquarter
  apply quarter_prime_of_residual (by linarith only [hx]) hn htail
  simpa only [hφ] using hlarge

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SmallValueGaussian
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Values below the three-quarter power are negligible at every Ford dimension. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma small_value_gaussian_scale : ∀ᶠ x : ℝ in atTop,
    x^(3/4:ℝ) ≤ (x/Real.log x)*Real.exp (-(m x:ℝ)^2/4) := by
  have h2 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2:ℝ) 1 (by norm_num)
  have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1:ℝ) 1 (by norm_num)
  have hlim := ((h2.add h1).const_mul 4).comp B_tendsto
  simp only [add_zero,mul_zero] at hlim
  filter_upwards [dimension_exponential_lower,eventually_gt_atTop (1:ℝ),
    B_tendsto.eventually (eventually_ge_atTop (1:ℝ)),
    hlim.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))]
    with x hm hx hB hs
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hB0 : 0 < B x := by linarith only [hB]
  have hsize : (3/5:ℝ)*(m x:ℝ) ≤ B x := by
    have hh := Real.log_le_log (Real.exp_pos _) hm
    rw [Real.log_exp] at hh
    have hl := Real.log_le_sub_one_of_pos hB0
    linarith only [hh,hl]
  have hsq : (m x:ℝ)^2/4 ≤ (B x)^2 := by
    have hnat := Nat.cast_nonneg (α:=ℝ) (m x)
    have hd : (m x:ℝ) ≤ 2*B x := by linarith only [hsize,hB]
    nlinarith only [mul_nonneg hnat (sub_nonneg.mpr hd),sq_nonneg (2*B x-(m x:ℝ))]
  change 4*((B x)^(2:ℝ)*Real.exp (-(1:ℝ)*B x)+
    (B x)^(1:ℝ)*Real.exp (-(1:ℝ)*B x)) < 1 at hs
  rw [Real.rpow_two,Real.rpow_one] at hs
  have he : Real.exp (B x)=Real.log x := Real.exp_log hlog
  have hbudget : 4*((B x)^2+B x) ≤ Real.log x := by
    have hh := mul_le_mul_of_nonneg_right hs.le (Real.exp_pos (B x)).le
    have hn : Real.exp (-(1:ℝ)*B x)*Real.exp (B x)=1 := by
      rw [← Real.exp_add]
      simp
    calc
      _ = (4*((B x)^2*Real.exp (-(1:ℝ)*B x)+B x*Real.exp (-(1:ℝ)*B x)))*Real.exp (B x) := by
        calc
          _ = 4*((B x)^2+B x)*(Real.exp (-(1:ℝ)*B x)*Real.exp (B x)) := by rw [hn]; ring
          _ = _ := by ring
      _ ≤ 1*Real.exp (B x) := hh
      _ = _ := by rw [one_mul,he]
  have hratio : x/Real.log x=Real.exp (Real.log x-B x) := by
    rw [Real.exp_sub,Real.exp_log (zero_lt_one.trans hx),he]
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hx),hratio,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith only [hbudget,hsq]

lemma small_value_gaussian_count : ∀ᶠ x : ℝ in atTop,
    ∀ Ψ : ℕ,Ψ ≤ m x → ∀ Q : Finset ℕ,
    (∀ v ∈ Q,0 < v ∧ (v:ℝ) ≤ x^(3/4:ℝ)) →
    (Q.card:ℝ) ≤ (x/Real.log x)*G x (m x)*Real.exp (-(Ψ:ℝ)^2/4) := by
  filter_upwards [small_value_gaussian_scale,central_volume_one_le,
    eventually_gt_atTop (1:ℝ)] with x hx hG hx1
  intro Ψ hΨ Q hQ
  have hsub : Q ⊆ Finset.Icc 1 ⌊x^(3/4:ℝ)⌋₊ := by
    intro v hv
    exact Finset.mem_Icc.mpr ⟨(hQ v hv).1,Nat.le_floor (hQ v hv).2⟩
  have hc : (Q.card:ℝ) ≤ x^(3/4:ℝ) := by
    have hh := Finset.card_le_card hsub
    simp only [Nat.card_Icc,Nat.add_sub_cancel] at hh
    exact (Nat.cast_le.mpr hh).trans (Nat.floor_le (Real.rpow_nonneg (by linarith only [hx1]) _))
  have hs : (Ψ:ℝ)^2 ≤ (m x:ℝ)^2 := by
    have hh : (Ψ:ℝ) ≤ m x := by exact_mod_cast hΨ
    nlinarith only [hh,Nat.cast_nonneg (α:=ℝ) Ψ,Nat.cast_nonneg (α:=ℝ) (m x)]
  have hf : 0 ≤ x/Real.log x := div_nonneg (by linarith only [hx1]) (Real.log_pos hx1).le
  calc
    _ ≤ (x/Real.log x)*Real.exp (-(m x:ℝ)^2/4) := hc.trans hx
    _ ≤ (x/Real.log x)*Real.exp (-(Ψ:ℝ)^2/4) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hs])) hf
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hG hf
      simpa only [mul_one] using mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BootstrapLargeValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Outside the explicit Gaussian exception, every preimage has a large head. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

theorem small_head_real_gaussian_oai : ∃ C : ℝ,0 < C ∧
    ∀ᶠ x : ℝ in atTop,∀ Ψ : ℕ,Ψ ≤ m x → ∀ Q : Finset ℕ,
    (∀ v ∈ Q,IsTotient v ∧ (v:ℝ) ≤ x ∧
      ∃ n : ℕ,0 < n ∧ n.totient=v ∧ (fordPrime n 0:ℝ) < x^(1/4:ℝ)) →
    (Q.card:ℝ) ≤ C*(x/Real.log x)*G x (m x)*Real.exp (-(Ψ:ℝ)^2/4) := by
  classical
  obtain ⟨A,hA,hcount⟩ := bootstrap_good_real_gaussian
  refine ⟨A+1,by positivity,?_⟩
  filter_upwards [hcount,bootstrap_floor_good_large_head,small_value_gaussian_count]
    with x hc hhead hsmall
  intro Ψ hΨ Q hQ
  let R := Q.filter (fun v => ¬BootstrapGood ⌊x⌋₊ v)
  let T := Q\R
  have hR := hc Ψ hΨ R (by
    intro v hv
    obtain ⟨hv,hr⟩ := Finset.mem_filter.mp hv
    exact ⟨(hQ v hv).1,(hQ v hv).2.1,hr⟩)
  have hT := hsmall Ψ hΨ T (by
    intro v hv
    obtain ⟨hv,hvR⟩ := Finset.mem_sdiff.mp hv
    refine ⟨isTotient_pos (hQ v hv).1,?_⟩
    have hgood : BootstrapGood ⌊x⌋₊ v := by
      by_contra hh
      exact hvR (Finset.mem_filter.mpr ⟨hv,hh⟩)
    by_contra hh
    have hvlarge : x^(3/4:ℝ) < v := lt_of_not_ge hh
    obtain ⟨n,hn,hφ,hbad⟩ := (hQ v hv).2.2
    exact (not_lt_of_ge (hhead v n hgood hvlarge hn hφ)) hbad)
  have hcard : (Q.card:ℝ)=(R.card:ℝ)+(T.card:ℝ) := by
    have hh := Finset.card_sdiff_add_card_eq_card (show R ⊆ Q from Finset.filter_subset _ _)
    exact_mod_cast (show Q.card=R.card+T.card by dsimp [T]; omega)
  rw [hcard]
  calc
    _ ≤ A*(x/Real.log x)*G x (m x)*Real.exp (-(Ψ:ℝ)^2/4)+
        (x/Real.log x)*G x (m x)*Real.exp (-(Ψ:ℝ)^2/4) := add_le_add hR hT
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

theorem solution : type_of% @OAI.TotientAsymptotic.small_head_real_gaussian_oai := @OAI.TotientAsymptotic.small_head_real_gaussian_oai
