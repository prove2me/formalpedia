-- Prove2me | solution 1 for OAI.TotientAsymptotic.ambient_nonnormal_witness_count
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:34:01.613745+00:00
-- url     : https://prove2.me/submissions/2586277c-024e-49be-b206-7da2be08e73e

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
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Nodup
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
import Mathlib.Tactic.Bound
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Order.Compact
import Definitions.Def_TotientAsymptotic
import Definitions.Def_OAIQ233A000
import Theorems.Thm_OAI_TotientAsymptotic_counting_envelope_real_bound
import Theorems.Thm_OAI_TotientAsymptotic_fordLemma26Input

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_StructuralInput
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Minimal structural inputs from Ford, *The distribution of totients*,
arXiv:1104.3264v2 (14 July 2013), Theorems 10 and 16.

The exceptional sets count values with **some** failing preimage, as in the
convention preceding Theorem 10, p. 5.  Consequently every preimage of a value
outside the exceptional set satisfies the property.  Ford's coordinates in
(4.2), p. 17, are clamped double logarithms.  Theorem 16, (6.1)--(6.2), p. 29,
also supplies the terminal lower bound that allows removing this clamp.

The band center below is Ford's B*rho^i*(1-i/m), not the phase-dependent
`bandScale` in Basic.lean.  Passing between these two centers is an additional
analytic step, governed by the manuscript's equation alpha-comparison.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma fordBandScale_pos {x : ℝ} {i : ℕ} (hB : 0 < B x) (hi : i < m x) :
    0 < fordBandScale x i := by
  have hm : (0 : ℝ) < m x := Nat.cast_pos.mpr (lt_of_le_of_lt (Nat.zero_le i) hi)
  have hi' : (i : ℝ) < m x := Nat.cast_lt.mpr hi
  exact mul_pos (mul_pos hB (pow_pos rho_pos _))
    (sub_pos.mpr ((div_lt_one hm).mpr hi'))

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

lemma bandScale_pos {x : ℝ} {i : ℕ} (hi : i < m x) : 0 < bandScale x i := by
  unfold bandScale
  exact mul_pos (mul_pos (alpha_pos _) (Nat.cast_pos.mpr (Nat.sub_pos_of_lt hi)))
    (inv_pos.mpr (pow_pos rho_pos _))

lemma fordBandScale_eq_ratio_mul {x : ℝ} {i : ℕ}
    (hB : 1 < B x) (hi : i < m x) :
    fordBandScale x i = bandCenterRatio x * bandScale x i := by
  have hm : (m x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hl : Real.log (B x) ≠ 0 := (Real.log_pos hB).ne'
  have hpow : rho^(m x) = rho^(m x-i) * rho^i := by
    rw [← pow_add, Nat.sub_add_cancel hi.le]
  unfold fordBandScale bandCenterRatio bandScale
  rw [alpha_theta_eq hB, Nat.cast_sub hi.le, hpow]
  field_simp [hm, hl, lam_pos.ne', rho_pos.ne']

lemma fordBandScale_div_bandScale {x : ℝ} {i : ℕ}
    (hB : 1 < B x) (hi : i < m x) :
    fordBandScale x i / bandScale x i = bandCenterRatio x := by
  rw [fordBandScale_eq_ratio_mul hB hi, mul_div_cancel_right₀ _ (bandScale_pos hi).ne']

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

/-- The error bound is simultaneous over every retained index. -/
theorem fordBandScale_uniform_comparison {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ i : ℕ, i < m x →
      |fordBandScale x i / bandScale x i - 1| < ε := by
  filter_upwards [B_tendsto.eventually (eventually_gt_atTop (1 : ℝ)),
    Metric.tendsto_nhds.mp bandCenterRatio_tendsto ε hε] with x hB hx
  intro i hi
  rw [fordBandScale_div_bandScale hB hi]
  simpa only [Real.dist_eq] using hx

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RenewalMagnitude
attribute [-instance] _root_.W21.instNorm _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A coarse numerical separation sufficient for the cofactor envelope. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma renewalSeries_three_eighths_lt_one : renewalSeries (3/8) < 1 := by
  have hh := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1
    (r := (3/8 : ℝ)) (by norm_num)
  have hsum : HasSum (fun n : ℕ => (n+1 : ℝ)*(3/8 : ℝ)^(n+1)) (24/25 : ℝ) := by
    have h2 := hh.mul_right (3/8 : ℝ)
    have e1 : (fun i : ℕ => ((i + 1).choose 1 : ℝ) * (3/8 : ℝ)^i * (3/8 : ℝ)) =
        fun n : ℕ => (n+1 : ℝ)*(3/8 : ℝ)^(n+1) := by
      ext n
      simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one, pow_succ]
      ring
    have e2 : (1 / (1 - 3/8 : ℝ)^(1+1)) * (3/8 : ℝ) = 24/25 := by norm_num
    rw [e1, e2] at h2
    exact h2
  have hbound : renewalSeries (3/8) ≤ (24/25 : ℝ) := by
    rw [← hsum.tsum_eq]
    unfold renewalSeries
    apply (summable_renewal (r := (3/8 : ℝ)) (by norm_num) (by norm_num)).tsum_le_tsum
      (g := fun n : ℕ => (n+1 : ℝ)*(3/8 : ℝ)^(n+1))
    · intro n
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast a_le_index (j := n+1) (by omega))
        (pow_nonneg (by norm_num) _)
    · exact hsum.summable
  linarith

lemma rho_gt_three_eighths : (3/8 : ℝ) < rho := by
  by_contra! hh
  have hm := renewalSeries_strictMonoOn.monotoneOn
    (show rho ∈ Set.Ico (0 : ℝ) 1 from ⟨rho_pos.le, rho_lt_one⟩)
    (show (3/8 : ℝ) ∈ Set.Ico (0 : ℝ) 1 by norm_num) hh
  have hroot : renewalSeries rho = 1 := rho_mem.2.2
  rw [hroot] at hm
  linarith [renewalSeries_three_eighths_lt_one]

lemma lam_lt_one : lam < 1 := by
  unfold lam
  have hr : 1/rho < (8/3 : ℝ) := by
    apply (div_lt_iff₀ rho_pos).mpr
    nlinarith [rho_gt_three_eighths]
  have hh := Real.log_lt_log (div_pos zero_lt_one rho_pos) hr
  apply hh.trans
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ)<8/3)).mpr
  linarith [Real.exp_one_gt_d9]

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

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionLogBudget
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Logarithmic normality losses are smaller than the final collision band. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma ford_band_log_upper : ∀ᶠ x : ℝ in atTop, ∀ i < m x,
    Real.log (6*fordBandScale x i) ≤ 26*(m x-i : ℕ) := by
  filter_upwards [fordBandScale_uniform_comparison (ε := 1) (by norm_num),theta_eventually_mem,
    B_tendsto.eventually (eventually_gt_atTop (1 : ℝ))] with x hx htheta hB
  intro i hi
  have hh : (1 : ℝ) ≤ (m x-i : ℕ) := by exact_mod_cast (Nat.sub_pos_of_lt hi)
  have hh0 : (0 : ℝ) < (m x-i : ℕ) := zero_lt_one.trans_le hh
  have hp := pow_pos rho_pos (m x-i)
  have hb := bandScale_pos hi
  have hf : fordBandScale x i ≤ 2*bandScale x i := by
    have hu := (div_lt_iff₀ hb).mp (show fordBandScale x i/bandScale x i < 2 by
      linarith [(abs_lt.mp (hx i hi)).2])
    exact hu.le
  have ha : alpha (theta x) ≤ 2 := by
    have hl := alpha_le (theta x) htheta
    have hq : lam/rho < 2 := (div_lt_iff₀ rho_pos).mpr (by linarith [lam_lt_one,collision_rho_bounds.1])
    exact hl.trans hq.le
  have hmodel : bandScale x i ≤ 2*(m x-i : ℕ)/rho^(m x-i) := by
    unfold bandScale
    simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right ha hh0.le) (inv_pos.mpr hp).le
  have hu : 6*fordBandScale x i ≤ 24*(m x-i : ℕ)/rho^(m x-i) := by
    calc
      _ ≤ 12*bandScale x i := by linarith
      _ ≤ 12*(2*(m x-i : ℕ)/rho^(m x-i)) := mul_le_mul_of_nonneg_left hmodel (by norm_num)
      _ = _ := by ring
  have hf0 := fordBandScale_pos (zero_lt_one.trans hB) hi
  have hl := Real.log_le_log (mul_pos (by norm_num : (0 : ℝ) < 6) hf0) hu
  rw [Real.log_div (mul_pos (by norm_num : (0 : ℝ) < 24) hh0).ne' hp.ne',
    Real.log_mul (by norm_num : (24 : ℝ) ≠ 0) hh0.ne',Real.log_pow] at hl
  have hrho : Real.log rho = -lam := by simp only [lam,one_div,Real.log_inv,neg_neg]
  rw [hrho] at hl
  have hl24 : Real.log (24 : ℝ) ≤ 24 := Real.log_le_self (by norm_num)
  have hlh := Real.log_le_self hh0.le
  have hlam := mul_le_mul_of_nonneg_right lam_lt_one.le hh0.le
  nlinarith

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

lemma dyadic_endpoint_B (n : ℕ) :
    B ((2 : ℝ)^n)=Real.log ((n : ℝ)*Real.log 2) := by
  rw [B,dyadic_endpoint_log]

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PublishedNormality
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Ford, The distribution of totients, revised arXiv:1104.3264v2 (2013),
Lemma 2.6, p. 9. The author-hosted PDF states uniformity for x > 3 and
S > 2: https://www.ford126.web.illinois.edu/wwwpapers/totients.pdf .
Only this count of exceptional primes is assumed. Reciprocal-weight and
actual good-witness discard estimates are derived separately.
-/

noncomputable section
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma normal_two {S : ℝ} (hS : 1 < S) (hBS : 0 ≤ B S) : IsNormalPrime S 2 := by
  refine ⟨Nat.prime_two,?_,?_⟩
  · simp only [show (2 : ℕ)-1=1 from rfl,omegaIn,Nat.primeFactorsList_one,List.filter_nil,
      List.length_nil,Nat.cast_zero]
    linarith
  · intro U T hSU hUT hT
    norm_num at hT
    linarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalitySmallParameter
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The elementary parameter range in Ford's exceptional-prime estimate. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma doubleLog_nat_pos {n : ℕ} (hn : 3 < n) : 0 < B n := by
  unfold B
  apply Real.log_pos
  apply (Real.lt_log_iff_exp_lt (by positivity : (0:ℝ)<n)).mpr
  have hn' : (3:ℝ) < n := by exact_mod_cast hn
  exact Real.exp_one_lt_three.trans hn'

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalPrimeMass
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Derive the exceptional reciprocal-prime mass from Ford's count. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma nonNormalPrime_ge_three {S : ℝ} {N p : ℕ} (hS : 1 < S) (hBS : 0 ≤ B S)
    (hp : p ∈ nonNormalPrimes S N) : 3 ≤ p := by
  obtain ⟨hp,hn⟩ := Finset.mem_filter.mp hp
  have hprime := (Nat.mem_primesLE.mp hp).2
  by_contra hh
  have he : p=2 := by have := hprime.two_le; omega
  subst p
  exact hn (normal_two hS hBS)

lemma dyadic_shift_lower {p : ℕ} (hp : 2 ≤ p) :
    (2 : ℝ)^(Nat.clog 2 p)/4 ≤ ((p-1 : ℕ) : ℝ) := by
  have hd := (dyadic_nat_bounds (by omega : 1 < p)).2.1
  have hsub : ((p-1 : ℕ) : ℝ)+1=p := by exact_mod_cast (show p-1+1=p by omega)
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  nlinarith

/-- The only arithmetic input is the literal count in Ford Lemma 2.6.
Dyadic summation supplies its needed reciprocal-weight consequence. -/
theorem non_normal_prime_mass (hford : FordLemma26Input) :
    ∃ C : ℝ, 0 < C ∧ ∀ S : ℝ, 2 < S → 0 ≤ B S → ∀ N : ℕ, 4 ≤ N →
      let L := Nat.clog 2 N
      (∑ p ∈ nonNormalPrimes S N, ((p-1 : ℕ) : ℝ)⁻¹) ≤
        C*(B ((2 : ℝ)^L))^5*(1+Real.log L)*(Real.log S)^(-1/6 : ℝ) := by
  obtain ⟨C,hC,hcount⟩ := hford
  refine ⟨4*C/Real.log 2,by positivity,?_⟩
  intro S hS hBS N hN
  dsimp only
  let L := Nat.clog 2 N
  let Q := nonNormalPrimes S N
  let W := B ((2 : ℝ)^L)
  let E := (Real.log S)^(-1/6 : ℝ)
  let A := C*W^5*E/Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 2 ≤ L := by
    have hh := Nat.clog_mono_right 2 hN
    have hc : Nat.clog 2 4=2 := by
      exact Nat.clog_pow 2 2 (by norm_num)
    rw [hc] at hh
    exact hh
  have hW : 0 ≤ W := by
    dsimp [W]
    rw [dyadic_endpoint_B]
    apply Real.log_nonneg
    have hL' : (2 : ℝ) ≤ L := by exact_mod_cast hL
    nlinarith [Real.log_two_gt_d9]
  have hE : 0 ≤ E := Real.rpow_nonneg (Real.log_nonneg (by linarith : (1 : ℝ) ≤ S)) _
  have hA : 0 ≤ A := div_nonneg (mul_nonneg (mul_nonneg hC.le (pow_nonneg hW _)) hE) hlog2.le
  have hn : ∀ p ∈ Q, Nat.clog 2 p ∈ Finset.Icc 1 L := by
    intro p hp
    have hp3 := nonNormalPrime_ge_three (by linarith) hBS hp
    refine Finset.mem_Icc.mpr ⟨(dyadic_nat_bounds (by omega : 1 < p)).1,?_⟩
    exact Nat.clog_mono_right 2 ((Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).1)
  have hf : ∀ k ∈ Finset.Icc 1 L,
      ((Q.filter (fun p => Nat.clog 2 p=k)).card : ℝ) ≤ A*(2 : ℝ)^k/(k : ℝ) := by
    intro k hk
    by_cases hne : (Q.filter (fun p => Nat.clog 2 p=k)).Nonempty
    · obtain ⟨p,hp⟩ := hne
      obtain ⟨hp,hpk⟩ := Finset.mem_filter.mp hp
      have hp3 := nonNormalPrime_ge_three (by linarith) hBS hp
      have hk2 : 2 ≤ k := by
        have he : 1 < Nat.clog 2 p := (Nat.lt_clog_iff_pow_lt (by norm_num)).mpr (by norm_num; omega)
        omega
      have hsub : Q.filter (fun p => Nat.clog 2 p=k) ⊆ nonNormalPrimes S (2^k) := by
        intro p hp
        obtain ⟨hp,he⟩ := Finset.mem_filter.mp hp
        obtain ⟨hp,hnormal⟩ := Finset.mem_filter.mp hp
        refine Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨?_,(Nat.mem_primesLE.mp hp).2⟩,hnormal⟩
        simpa only [he] using Nat.le_pow_clog (by norm_num : 1 < 2) p
      have hklarge : 3 < (2 : ℕ)^k := by
        have he := Nat.pow_le_pow_right (by norm_num : 0 < 2) hk2
        norm_num at he ⊢
        omega
      have hb := (show ((Q.filter (fun p => Nat.clog 2 p=k)).card : ℝ) ≤
          (nonNormalPrimes S (2^k)).card by exact_mod_cast Finset.card_le_card hsub).trans
        (hcount S hS (2^k) hklarge)
      have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      have hWk : 0 ≤ B ((2 : ℝ)^k) := by
        rw [dyadic_endpoint_B]
        apply Real.log_nonneg
        have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk2
        nlinarith [Real.log_two_gt_d9]
      have hWB : B ((2 : ℝ)^k) ≤ W := by
        dsimp [W]
        rw [dyadic_endpoint_B,dyadic_endpoint_B]
        apply Real.log_le_log (mul_pos hkpos hlog2)
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast (Finset.mem_Icc.mp hk).2) hlog2.le
      have hb' : ((Q.filter (fun p => Nat.clog 2 p=k)).card : ℝ) ≤
          C*(2 : ℝ)^k/Real.log ((2 : ℝ)^k)*(B ((2 : ℝ)^k))^5*E := by
        simpa only [Nat.cast_pow,Nat.cast_ofNat,E] using hb
      apply hb'.trans
      calc
        _ ≤ C*(2 : ℝ)^k/Real.log ((2 : ℝ)^k)*W^5*E :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hWk hWB 5) (by rw [dyadic_endpoint_log]; positivity)) hE
        _ = _ := by dsimp [A]; rw [dyadic_endpoint_log]; ring
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty,Nat.cast_zero]
      positivity
  have he := finite_dyadic_harmonic_mass Q (Nat.clog 2)
    (fun p => ((p-1 : ℕ) : ℝ)) L hA hn
    (fun p hp => dyadic_shift_lower (by have := nonNormalPrime_ge_three (by linarith) hBS hp; omega)) hf
  apply he.trans_eq
  dsimp [A,W,E,L]
  ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalNormalityDecay
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Indexed normality: a polynomial logarithmic cutoff beats each bounded local tail. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma localNormalityScale_factor (h : ℕ) :
    (Real.log (localNormalityScale h))^(-1/6:ℝ)=Real.exp (-(h:ℝ)^4/6) := by
  rw [localNormalityScale,Real.log_exp,←Real.exp_mul]
  congr 1
  ring

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeExtensionCount
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distinct totient values after adjoining a large prime to a residual preimage. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma mem_quarterPrimes {x : ℝ} {d p : ℕ} (hd : 0 < d) :
    p ∈ quarterPrimes x d ↔ p.Prime ∧ x^(1/4:ℝ) ≤ p ∧ ((p-1)*d:ℕ) ≤ x := by
  classical
  constructor
  · intro hp
    obtain ⟨hp,hx,hs⟩ := Finset.mem_filter.mp hp
    exact ⟨(Nat.mem_primesLE.mp hp).2,hx,hs⟩
  · rintro ⟨hp,hx,hs⟩
    refine Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨Nat.le_floor ?_,hp⟩,hx,hs⟩
    have hdR : (0:ℝ) < d := by exact_mod_cast hd
    have hpn : 1 ≤ p := hp.one_le
    have hle : ((p:ℝ)-1)*d ≤ x := by exact_mod_cast hs
    have hh := (le_div_iff₀ hdR).mpr hle
    linarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeExtensionCoverage
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact coverage of large-prime totients by their residual totient values. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma totient_prime_extension_cases {n p : ℕ} (hp : p.Prime) (hpn : p ∣ n) :
    n.totient=(p-1)*(n/p).totient ∨ n.totient=p*(n/p).totient := by
  have he : p*(n/p)=n := Nat.mul_div_cancel' hpn
  by_cases hd : p ∣ n/p
  · right
    conv_lhs => rw [← he]
    exact Nat.totient_mul_of_prime_of_dvd hp hd
  · left
    conv_lhs => rw [← he]
    exact Nat.totient_mul_of_prime_of_not_dvd hp hd

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NonNormalExtensionCount
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Residual-value grouping for the large-prime half of Ford Lemma 2.8. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

/-- On a nonempty prime interval, its lower cutoff supplies the logarithm
in Ford's exceptional-prime estimate. -/
theorem non_normal_quarter_prime_count : ∃ C : ℝ,0 < C ∧
    ∀ S x : ℝ,2 < S → 4 ≤ x → ∀ d : ℕ,0 < d → ∀ Q : Finset ℕ,
    (∀ p ∈ Q,p.Prime ∧ 4 ≤ p ∧ x^(1/4:ℝ) ≤ p ∧
      ((p-1)*d:ℕ) ≤ x ∧ ¬IsNormalPrime S p) →
    (Q.card:ℝ) ≤ C*x/(d*Real.log x)*(B (2*x))^5*(Real.log S)^(-1/6:ℝ) := by
  classical
  obtain ⟨C,hC,hford⟩ := fordLemma26Input
  refine ⟨8*C,by positivity,?_⟩
  intro S x hS hx d hd Q hQ
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hlS : 0 < Real.log S := Real.log_pos (by linarith)
  have hs : 0 ≤ (Real.log S)^(-1/6:ℝ) := Real.rpow_nonneg hlS.le _
  by_cases hne : Q.Nonempty
  · let N := ⌊1+x/d⌋₊
    have hpN (p : ℕ) (hp : p ∈ Q) : p ≤ N := by
      have hh := (hQ p hp).2.2.2.1
      have hp1 : 1 ≤ p := (hQ p hp).1.one_le
      have hhR : ((p:ℝ)-1)*d ≤ x := by exact_mod_cast hh
      apply Nat.le_floor
      have hdiv := (le_div_iff₀ hd0).mpr hhR
      linarith
    obtain ⟨p,hp⟩ := hne
    have hN4 : 4 ≤ N := (hQ p hp).2.1.trans (hpN p hp)
    have hN0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hN1 : (1:ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have hlogN : Real.log x/4 ≤ Real.log N := by
      have hlo := (hQ p hp).2.2.1.trans (Nat.cast_le.mpr (hpN p hp))
      have hh := Real.log_le_log (Real.rpow_pos_of_pos hx0 _) hlo
      rw [Real.log_rpow hx0] at hh
      linarith
    have hlogN0 : 0 < Real.log N := Real.log_pos hN1
    have hdx : (d:ℝ) ≤ x := by
      have hp1 : 1 ≤ p-1 := by have := (hQ p hp).1.two_le; omega
      exact (Nat.cast_le.mpr (show d ≤ (p-1)*d by nlinarith)).trans (hQ p hp).2.2.2.1
    have hNupper : (N:ℝ) ≤ 2*x/d := by
      have hn : (N:ℝ) ≤ 1+x/d := Nat.floor_le (by positivity)
      have hh : (1:ℝ) ≤ x/d := (le_div_iff₀ hd0).mpr (by simpa using hdx)
      rw [show 2*x/(d:ℝ)=2*(x/d) by ring]
      linarith only [hn,hh]
    have hN2x : (N:ℝ) ≤ 2*x := hNupper.trans ((div_le_iff₀ hd0).mpr (by nlinarith only [hd1,hx0]))
    have hBN : 0 ≤ B N := (doubleLog_nat_pos hN4).le
    have hBmono : B N ≤ B (2*x) := by
      apply Real.log_le_log hlogN0
      exact Real.log_le_log hN0 hN2x
    have hB2 : 0 ≤ B (2*x) := hBN.trans hBmono
    have hsub : Q ⊆ nonNormalPrimes S N := by
      intro q hq
      exact Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hpN q hq,(hQ q hq).1⟩,(hQ q hq).2.2.2.2⟩
    have hcard : (Q.card:ℝ) ≤ (nonNormalPrimes S N).card := Nat.cast_le.mpr (Finset.card_le_card hsub)
    have hrat : C*N/Real.log N ≤ 8*C*x/(d*Real.log x) := by
      calc
        _ ≤ C*(2*x/d)/(Real.log x/4) :=
          div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hNupper hC.le)
            (by positivity) hlogN
        _ = _ := by ring
    calc
      _ ≤ C*N/Real.log N*(B N)^5*(Real.log S)^(-1/6:ℝ) :=
        hcard.trans (hford S hS N hN4)
      _ ≤ (8*C*x/(d*Real.log x))*(B (2*x))^5*(Real.log S)^(-1/6:ℝ) := by
        apply mul_le_mul_of_nonneg_right _ hs
        exact mul_le_mul hrat (pow_le_pow_left₀ hBN hBmono 5) (by positivity) (by positivity)
      _ = _ := by ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty,Nat.cast_zero]
    have hB2 : 0 ≤ B (2*x) := by
      have hh : B 4 ≤ B (2*x) := Real.log_le_log
        (Real.log_pos (by norm_num)) (Real.log_le_log (by norm_num) (by linarith))
      exact (doubleLog_nat_pos (n:=4) (by norm_num)).le.trans hh
    positivity

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TotientCountingEnvelope
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite dyadic counting envelope used to bootstrap the global upper bound. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma dyadicTotientEnvelope_one_le (J : ℕ) : 1 ≤ dyadicTotientEnvelope J := le_max_left _ _

lemma dyadicTotientEnvelope_term_le {k J : ℕ} (hkJ : k ≤ J) :
    V ((2:ℝ)^k)*(k:ℝ)/(2:ℝ)^k ≤ dyadicTotientEnvelope J := by
  unfold dyadicTotientEnvelope
  have hs : k ∈ Finset.range (J+1) := Finset.mem_range.mpr (by omega)
  exact (Finset.le_sup' (s:=Finset.range (J+1))
    (fun k => V ((2:ℝ)^k)*(k:ℝ)/(2:ℝ)^k) hs).trans (le_max_right _ _)

lemma dyadic_totient_count_le {k J : ℕ} (hk : 1 ≤ k) (hkJ : k ≤ J) :
    V ((2:ℝ)^k) ≤ dyadicTotientEnvelope J*(2:ℝ)^k/(k:ℝ) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hpow : (0:ℝ) < 2^k := by positivity
  have he := dyadicTotientEnvelope_term_le hkJ
  apply (le_div_iff₀ hk0).mpr
  exact (div_le_iff₀ hpow).mp he

lemma totient_values_subset {x y : ℝ} (hxy : x ≤ y) : totientValues x ⊆ totientValues y := by
  classical
  intro v hv
  obtain ⟨hv,ht⟩ := Finset.mem_filter.mp hv
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hv).1,(Finset.mem_Icc.mp hv).2.trans (Nat.floor_mono hxy)⟩,ht⟩

lemma V_monotone : Monotone V := by
  intro x y hxy
  exact Nat.cast_le.mpr (Finset.card_le_card (totient_values_subset hxy))

lemma dyadic_totient_reciprocal_mass {J : ℕ} (_hJ : 1 ≤ J) (Q : Finset ℕ)
    (hQ : ∀ v ∈ Q,IsTotient v ∧ (v:ℝ) ≤ (2:ℝ)^J) :
    (∑ v ∈ Q,(v:ℝ)⁻¹) ≤ 1+4*dyadicTotientEnvelope J*(1+Real.log J) := by
  classical
  let E := Q.erase 1
  have hE (v : ℕ) (hv : v ∈ E) : IsTotient v ∧ 1 < v ∧ (v:ℝ) ≤ (2:ℝ)^J := by
    obtain ⟨hne,hv⟩ := Finset.mem_erase.mp hv
    have h := hQ v hv
    exact ⟨h.1,by have := isTotient_pos h.1; omega,h.2⟩
  have hn : ∀ v ∈ E,Nat.clog 2 v ∈ Finset.Icc 1 J := by
    intro v hv
    have hb := dyadic_nat_bounds (hE v hv).2.1
    refine Finset.mem_Icc.mpr ⟨hb.1,?_⟩
    apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr
    exact_mod_cast (hE v hv).2.2
  have hcount (k : ℕ) (hk : k ∈ Finset.Icc 1 J) :
      ((E.filter (fun v => Nat.clog 2 v=k)).card:ℝ) ≤
      dyadicTotientEnvelope J*(2:ℝ)^k/(k:ℝ) := by
    have hsub : E.filter (fun v => Nat.clog 2 v=k) ⊆ totientValues ((2:ℝ)^k) := by
      intro v hv
      obtain ⟨hv,he⟩ := Finset.mem_filter.mp hv
      have h := hE v hv
      have hb := (dyadic_nat_bounds h.2.1).2.2
      rw [he] at hb
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨isTotient_pos h.1,Nat.le_floor hb⟩,h.1⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (dyadic_totient_count_le (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2)
  have hm := finite_dyadic_harmonic_mass E (Nat.clog 2) (fun v => (v:ℝ)) J
    (zero_le_one.trans (dyadicTotientEnvelope_one_le J)) hn (by
      intro v hv
      have hh := (dyadic_nat_bounds (hE v hv).2.1).2.1
      have hp : (0:ℝ) < 2^(Nat.clog 2 v) := by positivity
      linarith) hcount
  have hs : (∑ v ∈ Q,(v:ℝ)⁻¹) ≤ 1+∑ v ∈ E,(v:ℝ)⁻¹ := by
    by_cases h1 : 1 ∈ Q
    · rw [← Finset.add_sum_erase Q _ h1]
      norm_num [E]
    · have he : E=Q := Finset.erase_eq_of_notMem h1
      rw [he]
      linarith
  exact hs.trans (add_le_add le_rfl hm)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LargeNonNormalValues
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distinct exceptional totient values, grouped by the residual value. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

lemma abnormal_extension_values_card (S x : ℝ) (d : ℕ) :
    (abnormalExtensionValues S x d).card ≤ 2*(abnormalExtensionPrimes S x d).card := by
  classical
  calc
    _ ≤ ∑ _p ∈ abnormalExtensionPrimes S x d,({(0:ℕ),1}:Finset ℕ).card :=
      Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun p _ => by simp; exact Finset.card_insert_le _ _))
    _ = _ := by simp; omega

lemma totient_mem_abnormalExtensionValues {S x : ℝ} {n p : ℕ}
    (hn : 0 < n) (hp : p.Prime) (hpn : p ∣ n) (hp4 : 4 ≤ p)
    (hpx : x^(1/4:ℝ) ≤ p) (hx : (n.totient:ℝ) ≤ x) (hbad : ¬IsNormalPrime S p) :
    n.totient ∈ abnormalExtensionValues S x (n/p).totient := by
  classical
  have hd : 0 < (n/p).totient := Nat.totient_pos.mpr
    (Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos)
  have hsize : (((p-1)*(n/p).totient:ℕ):ℝ) ≤ x := by
    rcases totient_prime_extension_cases hp hpn with h|h
    · rwa [← h]
    · exact (Nat.cast_le.mpr (Nat.mul_le_mul_right (n/p).totient (Nat.sub_le p 1))).trans (by rwa [← h])
  refine Finset.mem_biUnion.mpr ⟨p,Finset.mem_filter.mpr
    ⟨(mem_quarterPrimes hd).mpr ⟨hp,hpx,hsize⟩,hp4,hbad⟩,?_⟩
  rcases totient_prime_extension_cases hp hpn with h|h <;>
    simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto

/-- Large non-normal prime divisors cost only the reciprocal mass of the
residual totient values, even when a value has many preimages. -/
theorem large_non_normal_value_count : ∃ C : ℝ,0 < C ∧
    ∀ S x : ℝ,2 < S → 4 ≤ x → ∀ R Q : Finset ℕ,(∀ d ∈ R,0 < d) →
    (∀ v ∈ Q,∃ n p : ℕ,0 < n ∧ n.totient=v ∧ p.Prime ∧ p ∣ n ∧ 4 ≤ p ∧
      x^(1/4:ℝ) ≤ p ∧ (v:ℝ) ≤ x ∧ ¬IsNormalPrime S p ∧ (n/p).totient ∈ R) →
    (Q.card:ℝ) ≤ (C*x/Real.log x*(B (2*x))^5*(Real.log S)^(-1/6:ℝ))*
      ∑ d ∈ R,(d:ℝ)⁻¹ := by
  classical
  obtain ⟨C,hC,hcount⟩ := non_normal_quarter_prime_count
  refine ⟨2*C,by positivity,?_⟩
  intro S x hS hx R Q hR hQ
  have hsub : Q ⊆ R.biUnion (abnormalExtensionValues S x) := by
    intro v hv
    obtain ⟨n,p,hn,hφ,hp,hpn,hp4,hpx,hvx,hbad,hr⟩ := hQ v hv
    refine Finset.mem_biUnion.mpr ⟨(n/p).totient,hr,?_⟩
    rw [← hφ]
    exact totient_mem_abnormalExtensionValues hn hp hpn hp4 hpx (by rwa [hφ]) hbad
  have hbound (d : ℕ) (hd : d ∈ R) :
      ((abnormalExtensionValues S x d).card:ℝ) ≤
      (2*C*x/Real.log x*(B (2*x))^5*(Real.log S)^(-1/6:ℝ))*(d:ℝ)⁻¹ := by
    have hh := hcount S x hS hx d (hR d hd) (abnormalExtensionPrimes S x d) (by
      intro p hp
      obtain ⟨hp,hp4,hbad⟩ := Finset.mem_filter.mp hp
      obtain ⟨hp,hpx,hsize⟩ := (mem_quarterPrimes (hR d hd)).mp hp
      exact ⟨hp,hp4,hpx,hsize,hbad⟩)
    have hc : ((abnormalExtensionValues S x d).card:ℝ) ≤
        2*((abnormalExtensionPrimes S x d).card:ℝ) := by
      exact_mod_cast abnormal_extension_values_card S x d
    calc
      _ ≤ 2*((abnormalExtensionPrimes S x d).card:ℝ) := hc
      _ ≤ 2*(C*x/(d*Real.log x)*(B (2*x))^5*(Real.log S)^(-1/6:ℝ)) :=
        mul_le_mul_of_nonneg_left hh (by norm_num)
      _ = _ := by ring
  calc
    _ ≤ ((R.biUnion (abnormalExtensionValues S x)).card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ ∑ d ∈ R,((abnormalExtensionValues S x d).card:ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le : (R.biUnion (abnormalExtensionValues S x)).card ≤
        ∑ d ∈ R,(abnormalExtensionValues S x d).card)
    _ ≤ ∑ d ∈ R,(2*C*x/Real.log x*(B (2*x))^5*(Real.log S)^(-1/6:ℝ))*(d:ℝ)⁻¹ :=
      Finset.sum_le_sum hbound
    _ = _ := (Finset.mul_sum ..).symm

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

lemma dyadic_value_count_bound {N J : ℕ} (hN : 2 ≤ N) (hNJ : N ≤ 2^J) :
    V N ≤ 2*dyadicTotientEnvelope J*N/Real.log N := by
  let k := Nat.clog 2 N
  have hb := dyadic_nat_bounds (by omega : 1 < N)
  have hk : 1 ≤ k := hb.1
  have hkJ : k ≤ J := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr hNJ
  have hNpow : (N:ℝ) ≤ (2:ℝ)^k := hb.2.2
  have hpowN : (2:ℝ)^k ≤ 2*N := by linarith [hb.2.1]
  have hN0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hlog : Real.log N ≤ k := by
    have hh := Real.log_le_log hN0 hNpow
    rw [Real.log_pow] at hh
    have hl2 : Real.log (2:ℝ) ≤ 1 := by
      have he := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
      norm_num at he
      exact he
    have hm := mul_le_mul_of_nonneg_left hl2 hk0.le
    nlinarith only [hh,hm]
  have hE : 0 ≤ dyadicTotientEnvelope J := zero_le_one.trans (dyadicTotientEnvelope_one_le J)
  calc
    _ ≤ V ((2:ℝ)^k) := V_monotone hNpow
    _ ≤ dyadicTotientEnvelope J*(2:ℝ)^k/(k:ℝ) := dyadic_totient_count_le hk hkJ
    _ ≤ 2*dyadicTotientEnvelope J*N/(k:ℝ) := by
      apply div_le_div_of_nonneg_right _ hk0.le
      nlinarith only [mul_le_mul_of_nonneg_left hpowN hE]
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hlN hlog

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

lemma V_floor (x : ℝ) : V (⌊x⌋₊:ℝ)=V x := by
  unfold V
  rw [Nat.floor_natCast]

lemma dyadic_real_value_count_bound {x : ℝ} {J : ℕ} (hx : 4 ≤ x)
    (hJ : x ≤ (2:ℝ)^J) : V x ≤ 4*dyadicTotientEnvelope J*x/Real.log x := by
  have hfloor := log_floor_lower hx
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hfloorlog : 0 < Real.log (⌊x⌋₊:ℝ) := lt_of_lt_of_le (by positivity) hfloor.2
  have hN : ⌊x⌋₊ ≤ 2^J := by
    exact_mod_cast (Nat.floor_le (by linarith : 0 ≤ x)).trans hJ
  have hb := dyadic_value_count_bound hfloor.1 hN
  rw [V_floor] at hb
  have hE : 0 ≤ dyadicTotientEnvelope J := zero_le_one.trans (dyadicTotientEnvelope_one_le J)
  calc
    _ ≤ 2*dyadicTotientEnvelope J*(⌊x⌋₊:ℝ)/Real.log (⌊x⌋₊:ℝ) := hb
    _ ≤ 2*dyadicTotientEnvelope J*x/Real.log (⌊x⌋₊:ℝ) := by
      apply div_le_div_of_nonneg_right _ hfloorlog.le
      exact mul_le_mul_of_nonneg_left (Nat.floor_le (by linarith)) (by positivity)
    _ ≤ 2*dyadicTotientEnvelope J*x/(Real.log x/2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hfloor.2
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeDivisorValueCount
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact value counting by a selected prime divisor of a preimage. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma totient_mem_divisorExtensionValues {x : ℝ} {n p : ℕ}
    (hn : 0 < n) (hp : p.Prime) (hpn : p ∣ n) (hx : (n.totient:ℝ) ≤ x) :
    n.totient ∈ divisorExtensionValues x p := by
  classical
  have hq : 0 < n/p := Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos
  have hd : 0 < (n/p).totient := Nat.totient_pos.mpr hq
  have hcases := totient_prime_extension_cases hp hpn
  have hsize : (((p-1)*(n/p).totient:ℕ):ℝ) ≤ x := by
    rcases hcases with h|h
    · rwa [← h]
    · exact (Nat.cast_le.mpr (Nat.mul_le_mul_right (n/p).totient (Nat.sub_le p 1))).trans (by rwa [← h])
  have hp1 : (0:ℝ) < (p-1:ℕ) := by exact_mod_cast (show 0 < p-1 by have := hp.two_le; omega)
  have hdsize : ((n/p).totient:ℝ) ≤ x/(p-1:ℕ) := by
    apply (le_div_iff₀ hp1).mpr
    simpa only [Nat.cast_mul,mul_comm] using hsize
  have hdmem : (n/p).totient ∈ totientValues (x/(p-1:ℕ)) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hd,Nat.le_floor hdsize⟩,⟨n/p,hq,rfl⟩⟩
  rcases hcases with h|h
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(n/p).totient,hdmem,h.symm⟩)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(n/p).totient,hdmem,h.symm⟩)

lemma divisorExtensionValues_card (x : ℝ) (p : ℕ) :
    ((divisorExtensionValues x p).card:ℝ) ≤ 2*V (x/(p-1:ℕ)) := by
  classical
  have hh : (divisorExtensionValues x p).card ≤
      (totientValues (x/(p-1:ℕ))).card+(totientValues (x/(p-1:ℕ))).card :=
    (Finset.card_union_le _ _).trans
      (Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le))
  change ((divisorExtensionValues x p).card:ℝ) ≤ 2*((totientValues (x/(p-1:ℕ))).card:ℝ)
  have hhR : ((divisorExtensionValues x p).card:ℝ) ≤
      ((totientValues (x/(p-1:ℕ))).card:ℝ)+(totientValues (x/(p-1:ℕ))).card := by
    exact_mod_cast hh
  linarith

theorem prime_divisor_value_count (x : ℝ) (P Q : Finset ℕ)
    (hQ : ∀ v ∈ Q,∃ n p : ℕ,0 < n ∧ n.totient=v ∧ p.Prime ∧ p ∣ n ∧
      (v:ℝ) ≤ x ∧ p ∈ P) :
    (Q.card:ℝ) ≤ 2*∑ p ∈ P,V (x/(p-1:ℕ)) := by
  classical
  have hs : Q ⊆ P.biUnion (divisorExtensionValues x) := by
    intro v hv
    obtain ⟨n,p,hn,hφ,hp,hpn,hvx,hP⟩ := hQ v hv
    refine Finset.mem_biUnion.mpr ⟨p,hP,?_⟩
    rw [← hφ]
    exact totient_mem_divisorExtensionValues hn hp hpn (by rwa [hφ])
  calc
    _ ≤ ((P.biUnion (divisorExtensionValues x)).card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card hs)
    _ ≤ ∑ p ∈ P,((divisorExtensionValues x p).card:ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le : (P.biUnion (divisorExtensionValues x)).card ≤
        ∑ p ∈ P,(divisorExtensionValues x p).card)
    _ ≤ ∑ p ∈ P,2*V (x/(p-1:ℕ)) := Finset.sum_le_sum (fun p _ => divisorExtensionValues_card x p)
    _ = _ := (Finset.mul_sum ..).symm

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SmallPrimeValueCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The small-prime half of the exceptional-value count in Ford Lemma 2.8.
The envelope counts residual totient values, independently of fiber sizes. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma small_divisor_value_bound {x : ℝ} {d J : ℕ} (hx : 16 ≤ x)
    (hd : 0 < d) (hdx : (d:ℝ)^2 ≤ x) (hJ : x ≤ (2:ℝ)^J) :
    V (x/d) ≤ (8*dyadicTotientEnvelope J*x/Real.log x)*(d:ℝ)⁻¹ := by
  have hx0 : 0 < x := by linarith
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hdx' : (d:ℝ) ≤ x/4 := by
    by_contra hh
    have hh' : x/4 < (d:ℝ) := lt_of_not_ge hh
    have hd4 : 4 < (d:ℝ) := by linarith
    nlinarith only [hdx,hh',hd4]
  have ht4 : 4 ≤ x/d := (le_div_iff₀ hd0).mpr (by linarith)
  have htx : x/d ≤ x := (div_le_iff₀ hd0).mpr (by nlinarith only [hd1,hx0])
  have hlog : Real.log x/2 ≤ Real.log (x/d) := by
    have hh := Real.log_le_log (sq_pos_of_pos hd0) hdx
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    rw [Real.log_div hx0.ne' hd0.ne']
    linarith
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hE : 0 ≤ dyadicTotientEnvelope J := zero_le_one.trans (dyadicTotientEnvelope_one_le J)
  have hb := dyadic_real_value_count_bound ht4 (htx.trans hJ)
  calc
    _ ≤ 4*dyadicTotientEnvelope J*(x/d)/Real.log (x/d) := hb
    _ ≤ 4*dyadicTotientEnvelope J*(x/d)/(Real.log x/2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hlog
    _ = _ := by ring

/-- Prime divisors up to the square-root scale, with no choice of preimage
counted more than once. -/
theorem small_prime_value_count {x : ℝ} {J : ℕ} (hx : 16 ≤ x)
    (hJ : x ≤ (2:ℝ)^J) (P Q : Finset ℕ)
    (hP : ∀ p ∈ P,p.Prime ∧ (p:ℝ)^2 ≤ x)
    (hQ : ∀ v ∈ Q,∃ n p : ℕ,0 < n ∧ n.totient=v ∧ p.Prime ∧ p ∣ n ∧
      (v:ℝ) ≤ x ∧ p ∈ P) :
    (Q.card:ℝ) ≤ (16*dyadicTotientEnvelope J*x/Real.log x)*
      ∑ p ∈ P,((p-1:ℕ):ℝ)⁻¹ := by
  have hb := prime_divisor_value_count x P Q hQ
  have hpbound (p : ℕ) (hp : p ∈ P) :
      V (x/(p-1:ℕ)) ≤ (8*dyadicTotientEnvelope J*x/Real.log x)*((p-1:ℕ):ℝ)⁻¹ := by
    have hprime := (hP p hp).1
    apply small_divisor_value_bound hx (by have := hprime.two_le; omega) _ hJ
    have hs : ((p-1:ℕ):ℝ) ≤ p := by exact_mod_cast Nat.sub_le p 1
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hs 2).trans (hP p hp).2
  calc
    _ ≤ 2*∑ p ∈ P,V (x/(p-1:ℕ)) := hb
    _ ≤ 2*∑ p ∈ P,(8*dyadicTotientEnvelope J*x/Real.log x)*((p-1:ℕ):ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpbound) (by norm_num)
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- The exceptional-value bound for small prime factors. -/
theorem small_non_normal_value_count : ∃ C : ℝ,0 < C ∧
    ∀ (S x : ℝ) (N J : ℕ),2 < S → 0 ≤ B S → 4 ≤ N → 16 ≤ x →
    (N:ℝ)^2 ≤ x → x ≤ (2:ℝ)^J → ∀ Q : Finset ℕ,
    (∀ v ∈ Q,∃ n p : ℕ,0 < n ∧ n.totient=v ∧ p.Prime ∧ p ∣ n ∧
      (v:ℝ) ≤ x ∧ p ≤ N ∧ ¬IsNormalPrime S p) →
    (Q.card:ℝ) ≤ C*dyadicTotientEnvelope J*x/Real.log x*
      (B ((2:ℝ)^(Nat.clog 2 N)))^5*(1+Real.log (Nat.clog 2 N))*
        (Real.log S)^(-1/6:ℝ) := by
  classical
  obtain ⟨C,hC,hmass⟩ := non_normal_prime_mass fordLemma26Input
  refine ⟨16*C,by positivity,?_⟩
  intro S x N J hS hBS hN hx hNx hJ Q hQ
  have hP (p : ℕ) (hp : p ∈ nonNormalPrimes S N) : p.Prime ∧ (p:ℝ)^2 ≤ x := by
    have hh := Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1
    exact ⟨hh.2,(pow_le_pow_left₀ (Nat.cast_nonneg p) (by exact_mod_cast hh.1) 2).trans hNx⟩
  have hb := small_prime_value_count hx hJ (nonNormalPrimes S N) Q hP (by
    intro v hv
    obtain ⟨n,p,hn,hφ,hp,hpn,hv,hle,hnormal⟩ := hQ v hv
    exact ⟨n,p,hn,hφ,hp,hpn,hv,Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hle,hp⟩,hnormal⟩⟩)
  have hc : 0 ≤ 16*dyadicTotientEnvelope J*x/Real.log x := by
    have := Real.log_pos (show 1 < x by linarith)
    have := zero_le_one.trans (dyadicTotientEnvelope_one_le J)
    positivity
  calc
    _ ≤ (16*dyadicTotientEnvelope J*x/Real.log x)*
        ∑ p ∈ nonNormalPrimes S N,((p-1:ℕ):ℝ)⁻¹ := hb
    _ ≤ (16*dyadicTotientEnvelope J*x/Real.log x)*
        (C*(B ((2:ℝ)^(Nat.clog 2 N)))^5*(1+Real.log (Nat.clog 2 N))*(Real.log S)^(-1/6:ℝ)) :=
      mul_le_mul_of_nonneg_left (hmass S hS hBS N hN) hc
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ExceptionalValueCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete non-normal-prime contribution to Ford's nice-value exception.
All fibers are handled by finite value covers, without multiplicity weights. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

lemma totient_div_prime_le {n p : ℕ} (hp : p.Prime) (hpn : p ∣ n) :
    (n/p).totient ≤ n.totient := by
  have hp1 : 1 ≤ p-1 := by have := hp.two_le; omega
  rcases totient_prime_extension_cases hp hpn with h|h
  · rw [h]
    simpa using Nat.mul_le_mul_right (n/p).totient hp1
  · rw [h]
    simpa using Nat.mul_le_mul_right (n/p).totient hp.one_le

/-- A finite, uniform form of the non-normal-prime part of Ford Lemma 2.8.
The two numeric inequalities select any cutoff between the fourth-root and
square-root scales. -/
theorem non_normal_value_count_split : ∃ C D : ℝ,0 < C ∧ 0 < D ∧
    ∀ (S x : ℝ) (N J : ℕ),2 < S → 0 ≤ B S → 4 ≤ N → 16 ≤ x →
    (N:ℝ)^2 ≤ x → x^(1/4:ℝ) ≤ N → 1 ≤ J → x ≤ (2:ℝ)^J →
    ∀ Q : Finset ℕ,
    (∀ v ∈ Q,∃ n p : ℕ,0 < n ∧ n.totient=v ∧ p.Prime ∧ p ∣ n ∧
      (v:ℝ) ≤ x ∧ ¬IsNormalPrime S p) →
    (Q.card:ℝ) ≤
      C*dyadicTotientEnvelope J*x/Real.log x*
        (B ((2:ℝ)^(Nat.clog 2 N)))^5*(1+Real.log (Nat.clog 2 N))*
          (Real.log S)^(-1/6:ℝ) +
      (D*x/Real.log x*(B (2*x))^5*(Real.log S)^(-1/6:ℝ))*
        (1+4*dyadicTotientEnvelope J*(1+Real.log J)) := by
  obtain ⟨C,hC,hsmall⟩ := small_non_normal_value_count
  obtain ⟨D,hD,hlarge⟩ := large_non_normal_value_count
  refine ⟨C,D,hC,hD,?_⟩
  intro S x N J hS hBS hN hx hNx hroot hJ hxJ Q hQ
  let A := Q.filter (fun v => ∃ n p : ℕ,0 < n ∧ n.totient=v ∧ p.Prime ∧ p ∣ n ∧
    (v:ℝ) ≤ x ∧ p ≤ N ∧ ¬IsNormalPrime S p)
  let T := Q\A
  have hsmall' := hsmall S x N J hS hBS hN hx hNx hxJ A
    (fun v hv => (Finset.mem_filter.mp hv).2)
  have hres (d : ℕ) (hd : d ∈ totientValues x) :
      IsTotient d ∧ (d:ℝ) ≤ (2:ℝ)^J := by
    obtain ⟨hd,ht⟩ := Finset.mem_filter.mp hd
    exact ⟨ht,(Nat.floor_le (by linarith : 0 ≤ x)).trans' (Nat.cast_le.mpr (Finset.mem_Icc.mp hd).2) |>.trans hxJ⟩
  have hlarge' := hlarge S x hS (by linarith) (totientValues x) T
    (fun d hd => isTotient_pos (hres d hd).1) (by
      intro v hv
      obtain ⟨hvQ,hvA⟩ := Finset.mem_sdiff.mp hv
      obtain ⟨n,p,hn,hφ,hp,hpn,hvx,hbad⟩ := hQ v hvQ
      have hpN : N < p := by
        by_contra hh
        exact hvA (Finset.mem_filter.mpr ⟨hvQ,n,p,hn,hφ,hp,hpn,hvx,by omega,hbad⟩)
      have hd : 0 < (n/p).totient := Nat.totient_pos.mpr
        (Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos)
      have hdx : ((n/p).totient:ℝ) ≤ x :=
        (Nat.cast_le.mpr (totient_div_prime_le hp hpn)).trans (by rwa [hφ])
      refine ⟨n,p,hn,hφ,hp,hpn,by omega,hroot.trans (by exact_mod_cast hpN.le),hvx,hbad,?_⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hd,Nat.le_floor hdx⟩,⟨n/p,
        Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos,rfl⟩⟩)
  have hB : 0 ≤ B (2*x) := by
    have hh : B 4 ≤ B (2*x) := Real.log_le_log
      (Real.log_pos (by norm_num)) (Real.log_le_log (by norm_num) (by linarith))
    exact (doubleLog_nat_pos (n:=4) (by norm_num)).le.trans hh
  have hcoef : 0 ≤ D*x/Real.log x*(B (2*x))^5*(Real.log S)^(-1/6:ℝ) := by
    have := Real.log_pos (show 1 < x by linarith)
    have := Real.log_pos (show 1 < S by linarith)
    positivity
  have hmass := dyadic_totient_reciprocal_mass hJ (totientValues x) hres
  have hcard : (Q.card:ℝ) = (A.card:ℝ)+(T.card:ℝ) := by
    have hsubset : A ⊆ Q := Finset.filter_subset _ _
    have hh := Finset.card_sdiff_add_card_eq_card hsubset
    dsimp only [T]
    exact_mod_cast (show Q.card=A.card+(Q\A).card by omega)
  rw [hcard]
  exact add_le_add hsmall' (hlarge'.trans (mul_le_mul_of_nonneg_left hmass hcoef))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SqrtCountingCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete cutoff between the fourth-root and square-root scales. -/
noncomputable section
namespace TotientAsymptotic

lemma sqrt_counting_cutoff {x : ℝ} (hx : 256 ≤ x) :
    4 ≤ ⌊Real.sqrt x⌋₊ ∧ ((⌊Real.sqrt x⌋₊:ℝ)^2 ≤ x) ∧
      x^(1/4:ℝ) ≤ (⌊Real.sqrt x⌋₊:ℝ) := by
  have hx0 : 0 ≤ x := by linarith
  have hy16 : 16 ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by nlinarith : (16:ℝ)^2 ≤ x)
  have hy0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hn : 4 ≤ ⌊Real.sqrt x⌋₊ := Nat.le_floor (show (4:ℝ) ≤ Real.sqrt x by linarith)
  have hs : (⌊Real.sqrt x⌋₊:ℝ)^2 ≤ x := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg ⌊Real.sqrt x⌋₊) (Nat.floor_le hy0) 2
    rwa [Real.sq_sqrt hx0] at hh
  have hroot : x^(1/4:ℝ)=Real.sqrt (Real.sqrt x) := by
    rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,← Real.rpow_mul hx0]
    norm_num
  have hhalf : Real.sqrt (Real.sqrt x) ≤ Real.sqrt x/2 := by
    apply (Real.sqrt_le_iff).mpr ⟨by positivity,?_⟩
    nlinarith only [hy16]
  have hf : Real.sqrt x/2 ≤ (⌊Real.sqrt x⌋₊:ℝ) := by
    linarith [Nat.sub_one_lt_floor (Real.sqrt x)]
  exact ⟨hn,hs,hroot ▸ hhalf.trans hf⟩

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_UniformNonNormalCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform form of the non-normal-prime value exception. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem uniform_non_normal_value_count : ∃ C : ℝ,0 < C ∧
    ∀ (S x : ℝ) (J : ℕ),2 < S → 0 ≤ B S → 256 ≤ x → 1 ≤ J →
    x ≤ (2:ℝ)^J → ∀ Q : Finset ℕ,
    (∀ v ∈ Q,∃ n p : ℕ,0 < n ∧ n.totient=v ∧ p.Prime ∧ p ∣ n ∧
      (v:ℝ) ≤ x ∧ ¬IsNormalPrime S p) →
    (Q.card:ℝ) ≤ C*dyadicTotientEnvelope J*x/Real.log x*
      (B (2*x))^5*(1+Real.log J)*(Real.log S)^(-1/6:ℝ) := by
  obtain ⟨C,D,hC,hD,hcount⟩ := non_normal_value_count_split
  refine ⟨C+5*D,by positivity,?_⟩
  intro S x J hS hBS hx hJ hxJ Q hQ
  let N := ⌊Real.sqrt x⌋₊
  let L := Nat.clog 2 N
  have hcut := sqrt_counting_cutoff hx
  have hN : 4 ≤ N := hcut.1
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNx : (N:ℝ) ≤ x := by nlinarith only [hcut.2.1,hNR]
  have hNJ : N ≤ 2^J := by exact_mod_cast hNx.trans hxJ
  have hLJ : L ≤ J := (Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)).mpr hNJ
  have hb := dyadic_nat_bounds (show 1 < N by omega)
  have hL1 : 1 ≤ L := hb.1
  have hLlog : 1+Real.log L ≤ 1+Real.log J := by
    exact add_le_add le_rfl (Real.log_le_log (by exact_mod_cast (show 0 < L by omega))
      (by exact_mod_cast hLJ))
  have hLlog0 : 0 ≤ 1+Real.log L := by
    have hh := Real.log_nonneg (show (1:ℝ) ≤ L by exact_mod_cast hL1)
    linarith
  have hJlog1 : 1 ≤ 1+Real.log J := by
    have hh := Real.log_nonneg (show (1:ℝ) ≤ J by exact_mod_cast hJ)
    linarith
  have hpow2x : (2:ℝ)^L ≤ 2*x := by nlinarith only [hb.2.1,hNx]
  have hBsmall0 : 0 ≤ B ((2:ℝ)^L) := by
    have h4 : 4 ≤ (2:ℕ)^L := hN.trans (Nat.le_pow_clog (by norm_num : 1 < 2) N)
    have hh := (doubleLog_nat_pos h4).le
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using hh
  have hB : B ((2:ℝ)^L) ≤ B (2*x) := by
    have hp : (1:ℝ) < 2^L := by
      have h4 : 4 ≤ (2:ℕ)^L := hN.trans (Nat.le_pow_clog (by norm_num : 1 < 2) N)
      exact_mod_cast (show 1 < (2:ℕ)^L by omega)
    exact Real.log_le_log (Real.log_pos hp) (Real.log_le_log (by positivity) hpow2x)
  have hB0 : 0 ≤ B (2*x) := hBsmall0.trans hB
  have hmass : (B ((2:ℝ)^L))^5*(1+Real.log L) ≤ (B (2*x))^5*(1+Real.log J) :=
    mul_le_mul (pow_le_pow_left₀ hBsmall0 hB 5) hLlog hLlog0 (pow_nonneg hB0 _)
  have hE1 : 1 ≤ dyadicTotientEnvelope J := dyadicTotientEnvelope_one_le J
  have hE0 : 0 ≤ dyadicTotientEnvelope J := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogS : 0 < Real.log S := Real.log_pos (by linarith)
  have hsn : 0 ≤ (Real.log S)^(-1/6:ℝ) := Real.rpow_nonneg hlogS.le _
  have hlarge : 1+4*dyadicTotientEnvelope J*(1+Real.log J) ≤
      5*dyadicTotientEnvelope J*(1+Real.log J) := by
    have hh := mul_le_mul hE1 hJlog1 (by norm_num) hE0
    nlinarith only [hh]
  have hs : C*dyadicTotientEnvelope J*x/Real.log x*
      (B ((2:ℝ)^L))^5*(1+Real.log L)*(Real.log S)^(-1/6:ℝ) ≤
      C*dyadicTotientEnvelope J*x/Real.log x*
        (B (2*x))^5*(1+Real.log J)*(Real.log S)^(-1/6:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmass (show 0 ≤ C*dyadicTotientEnvelope J*x/Real.log x by positivity)) hsn
    first | (convert hh using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (hh.trans (le_of_eq (by ring)))
  have hl : (D*x/Real.log x*(B (2*x))^5*(Real.log S)^(-1/6:ℝ))*
      (1+4*dyadicTotientEnvelope J*(1+Real.log J)) ≤
      (5*D)*dyadicTotientEnvelope J*x/Real.log x*(B (2*x))^5*(1+Real.log J)*(Real.log S)^(-1/6:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hlarge
      (show 0 ≤ D*x/Real.log x*(B (2*x))^5*(Real.log S)^(-1/6:ℝ) by positivity)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hc := hcount S x N J hS hBS hN (by linarith) hcut.2.1 hcut.2.2 hJ hxJ Q hQ
  exact hc.trans ((add_le_add hs hl).trans_eq (by ring))

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BootstrapRealCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The counting bootstrap at arbitrary real endpoints. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma counting_dyadic_index_bounds {x : ℝ} (hx : 4 ≤ x) :
    1 ≤ countingDyadicIndex x ∧ x ≤ (2:ℝ)^(countingDyadicIndex x) ∧
    bootstrapHeight (countingDyadicIndex x) ≤ B x+4 := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx1
  have h2 : 0 < Real.log (2:ℝ) := by positivity
  have h2lo : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h4 : 1 ≤ Real.log x := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ)<4) hx
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  let J := countingDyadicIndex x
  have hlo : Real.log x/Real.log 2 ≤ (J:ℝ) := Nat.le_ceil _
  have hhi : (J:ℝ) < Real.log x/Real.log 2+1 := Nat.ceil_lt_add_one (by positivity)
  have hJ : 1 ≤ J := by
    have hp : 0 < (J:ℝ) := (div_pos hlog h2).trans_le hlo
    have hjpos : 0 < J := Nat.cast_pos.mp hp
    omega
  have hJhi : (J:ℝ)+1 ≤ 4*Real.log x := by
    have hh := (div_le_iff₀ h2).mpr (show Real.log x ≤ 2*Real.log x*Real.log 2 by nlinarith)
    linarith
  refine ⟨hJ,?_,?_⟩
  · have hs : Real.log x ≤ (J:ℝ)*Real.log 2 := (div_le_iff₀ h2).mp hlo
    have he := Real.exp_le_exp.mpr hs
    simpa only [Real.exp_log hx0,Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)] using he
  · have hl := Real.log_le_log (by positivity : 0 < (J:ℝ)+1) hJhi
    rw [Real.log_mul (by norm_num : (4:ℝ)≠0) hlog.ne'] at hl
    have hlog4 : Real.log (4:ℝ) ≤ 3 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
      norm_num at hh
      exact hh
    change 1+Real.log ((J:ℝ)+1) ≤ B x+4
    unfold B
    linarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CountingEnvelopeReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The dyadic counting envelope and its normality factor at real endpoints. -/
noncomputable section
namespace TotientAsymptotic

lemma counting_normality_polynomial {x : ℝ} (hx : 4 ≤ x) (hB : 0 ≤ B x) :
    (B (2*x))^5*(1+Real.log (countingDyadicIndex x)) ≤ (B x+4)^6 := by
  have hbounds := counting_dyadic_index_bounds hx
  have hBupper := double_log_double_le (show 2 ≤ x by linarith)
  have hx0 : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hBmono : B x ≤ B (2*x) := by
    apply Real.log_le_log hlogx
    exact Real.log_le_log hx0 (by linarith)
  have hlog : 1+Real.log (countingDyadicIndex x) ≤ B x+4 := by
    have hJ0 : (0:ℝ) < countingDyadicIndex x := by
      exact_mod_cast (show 0 < countingDyadicIndex x by omega)
    have hh := Real.log_le_log hJ0 (show (countingDyadicIndex x:ℝ) ≤ (countingDyadicIndex x:ℝ)+1 by linarith)
    have hheight := hbounds.2.2
    change 1+Real.log ((countingDyadicIndex x:ℝ)+1) ≤ B x+4 at hheight
    linarith
  have hlog0 : 0 ≤ 1+Real.log (countingDyadicIndex x) := by
    have hh := Real.log_nonneg (show (1:ℝ) ≤ countingDyadicIndex x by exact_mod_cast hbounds.1)
    linarith
  calc
    _ ≤ (B x+4)^5*(B x+4) := mul_le_mul
      (pow_le_pow_left₀ (hB.trans hBmono) (by linarith) 5) hlog hlog0 (by positivity)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTNormalWitness
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The finite singleton-fiber reduction in Ford's exclusion (vi).  If the
candidate primes and the fixed seed primes are normal, a chosen preimage
with a nonnormal prime can only come from a singleton candidate-totient
fiber.  The exceptional candidates therefore give distinct target
totients, retaining the multiplicities elsewhere in the construction.
-/

noncomputable section

namespace TotientAsymptotic

/-- A nonnormal chosen preimage cannot lie in the seed-multiple branch of
the injective witness construction. -/
theorem ppt_nonnormal_witness_totient_injective {S Q : Finset ℕ}
    {F : ℕ → ℕ} {q : ℕ} {W : ℝ} (hQS : Q ⊆ S)
    (hS : ∀ n ∈ S, ∀ p : ℕ, p.Prime → p ∣ n → IsNormalPrime W p)
    (hq : ∀ p : ℕ, p.Prime → p ∣ q → IsNormalPrime W p)
    (hbranch : ∀ n ∈ S,
      (∃ m ∈ S, m ≠ n ∧ m.totient = n.totient) →
        ∃ c ∈ S, F n = c*q)
    (hbad : ∀ n ∈ Q, ∃ p : ℕ, p.Prime ∧ p ∣ F n ∧ ¬IsNormalPrime W p) :
    Set.InjOn Nat.totient (Q : Set ℕ) := by
  intro n hn m hm he
  by_contra hne
  obtain ⟨c, hc, hF⟩ := hbranch n (hQS hn)
    ⟨m, hQS hm, Ne.symm hne, he.symm⟩
  obtain ⟨p, hp, hpd, hpn⟩ := hbad n hn
  rw [hF] at hpd
  rcases hp.dvd_mul.mp hpd with hpc | hpq
  · exact hpn (hS c hc p hp hpc)
  · exact hpn (hq p hp hpq)

/-- The corresponding seed-scaled target totients are distinct as well. -/
theorem ppt_nonnormal_witness_target_injective {S Q : Finset ℕ}
    {F : ℕ → ℕ} {d q : ℕ} {W : ℝ} (hd : 0 < d) (hQS : Q ⊆ S)
    (hS : ∀ n ∈ S, ∀ p : ℕ, p.Prime → p ∣ n → IsNormalPrime W p)
    (hq : ∀ p : ℕ, p.Prime → p ∣ q → IsNormalPrime W p)
    (hbranch : ∀ n ∈ S,
      (∃ m ∈ S, m ≠ n ∧ m.totient = n.totient) →
        ∃ c ∈ S, F n = c*q)
    (hbad : ∀ n ∈ Q, ∃ p : ℕ, p.Prime ∧ p ∣ F n ∧ ¬IsNormalPrime W p) :
    Set.InjOn (fun n : ℕ => d*n.totient) (Q : Set ℕ) := by
  intro n hn m hm he
  exact ppt_nonnormal_witness_totient_injective hQS hS hq hbranch hbad hn hm
    (Nat.eq_of_mul_eq_mul_left hd he)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTNormalWitnessCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The nonnormal-target discard in the PPT construction, at the existing
dyadic counting-envelope scale.  The finite singleton-fiber argument
allows the unconditional exceptional-totient estimate to count the
original candidate integers without any multiplicity loss.
-/

noncomputable section

namespace TotientAsymptotic

theorem ppt_nonnormal_witness_count_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (W x : ℝ) (J d q : ℕ),
      2 < W → 0 ≤ B W → 256 ≤ x → 1 ≤ J → x ≤ (2 : ℝ)^J → 0 < d →
      ∀ (A Q : Finset ℕ) (F : ℕ → ℕ), Q ⊆ A →
      (∀ n ∈ A, ∀ p : ℕ, p.Prime → p ∣ n → IsNormalPrime W p) →
      (∀ p : ℕ, p.Prime → p ∣ q → IsNormalPrime W p) →
      (∀ n ∈ A, (∃ m ∈ A, m ≠ n ∧ m.totient = n.totient) →
        ∃ c ∈ A, F n = c*q) →
      (∀ n ∈ Q, ∃ p : ℕ, p.Prime ∧ p ∣ F n ∧ ¬IsNormalPrime W p) →
      (∀ n ∈ Q, 0 < F n ∧ (F n).totient = d*n.totient ∧
        ((d*n.totient : ℕ) : ℝ) ≤ x) →
      (Q.card : ℝ) ≤ C*dyadicTotientEnvelope J*x/Real.log x*
        (B (2*x))^5*(1+Real.log J)*(Real.log W)^(-1/6 : ℝ) := by
  classical
  obtain ⟨C, hC, hcount⟩ := uniform_non_normal_value_count
  refine ⟨C, hC, ?_⟩
  intro W x J d q hW hBW hx hJ hxJ hd A Q F hQA hA hq hbranch hbad hF
  have hinj := ppt_nonnormal_witness_target_injective hd hQA hA hq hbranch hbad
  have hb := hcount W x J hW hBW hx hJ hxJ
    (Q.image (fun n : ℕ => d*n.totient)) (by
      intro v hv
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨p, hp, hpd, hpn⟩ := hbad n hn
      have hnF := hF n hn
      exact ⟨F n, p, hnF.1, hnF.2.1, hp, hpd, hnF.2.2, hpn⟩)
  rwa [Finset.card_image_of_injOn hinj] at hb

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalValueNormality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nonnormal preimages at a local residual endpoint, with the actual value envelope. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma local_value_normality_decay_rate {C A : ℝ} (hC : 0 < C) (hA : 0 ≤ A) (K : ℕ) :
    ∀ᶠ h : ℕ in atTop,∀ u : ℝ,1 ≤ u → Real.log u ≤ A*h →
      C*Real.exp (9*(Real.log u)^2)*u^6*Real.exp (-(h:ℝ)^4/6) ≤ rho^(K*h) := by
  let M := |Real.log C|+9*A^2+6*A+K*lam+1
  have hM : 1 ≤ M := by
    dsimp [M]
    nlinarith only [abs_nonneg (Real.log C),sq_nonneg A,hA,lam_pos,mul_nonneg (Nat.cast_nonneg K) lam_pos.le]
  filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
    (eventually_ge_atTop (6*M))] with h hh
  intro u hu hlog
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have hh1 : (1:ℝ) ≤ h := by nlinarith only [hh,hM]
  have hh2 : (h:ℝ) ≤ (h:ℝ)^2 := by nlinarith only [hh1]
  have hlu : 0 ≤ Real.log u := Real.log_nonneg hu
  have hlog2 : (Real.log u)^2 ≤ A^2*(h:ℝ)^2 := by
    exact (pow_le_pow_left₀ hlu hlog 2).trans_eq (by ring)
  have hconst := mul_le_mul_of_nonneg_left
    (show (1:ℝ)≤(h:ℝ)^2 by nlinarith only [hh1]) (abs_nonneg (Real.log C))
  have hlinear := mul_le_mul_of_nonneg_left hh2
    (show 0 ≤ 6*A+K*lam from add_nonneg (mul_nonneg (by norm_num) hA)
      (mul_nonneg (Nat.cast_nonneg K) lam_pos.le))
  have hsmall : Real.log C+9*(Real.log u)^2+6*Real.log u+(K*lam)*h ≤ M*(h:ℝ)^2 := by
    dsimp [M]
    nlinarith only [hconst,hlinear,hlog2,hlog,le_abs_self (Real.log C),sq_nonneg (h:ℝ)]
  have hlarge : 6*M ≤ (h:ℝ)^2 := by nlinarith only [hh,hh1]
  have hmul := mul_nonneg (sq_nonneg (h:ℝ)) (sub_nonneg.mpr hlarge)
  have he : Real.log C+9*(Real.log u)^2+6*Real.log u-(h:ℝ)^4/6 ≤ -lam*(K*h) := by
    nlinarith only [hsmall,hmul]
  have hp : u^6=Real.exp (6*Real.log u) := by
    simpa only [Nat.cast_ofNat,Real.exp_log hu0] using (Real.exp_nat_mul (Real.log u) 6).symm
  rw [hp,←Real.exp_log hC,←Real.exp_add,←Real.exp_add,←Real.exp_add]
  rw [neg_div,←sub_eq_add_neg]
  apply (Real.exp_le_exp.mpr he).trans_eq
  have hlrho : Real.log rho= -lam := by simp [lam,one_div,Real.log_inv]
  rw [show -lam*(K*h:ℝ)=((K*h:ℕ):ℝ)*Real.log rho by rw [hlrho,Nat.cast_mul]; ring,
    Real.exp_nat_mul,Real.exp_log rho_pos]

/-- The singleton-target argument controls arbitrary nonnormal preimages
without any assumption on their multiplicity. -/
theorem local_nonnormal_witness_count_rate {A : ℝ} (hA : 0 ≤ A) (K : ℕ) :
    ∀ᶠ h : ℕ in atTop,∀ (z : ℝ) (d q : ℕ),
      256 ≤ z → 0 ≤ B z → Real.log (B z+4) ≤ A*h → 0 < d →
      ∀ (R Q : Finset ℕ) (F : ℕ → ℕ),Q ⊆ R →
      (∀ n ∈ R,∀ p : ℕ,p.Prime → p ∣ n → IsNormalPrime (localNormalityScale h) p) →
      (∀ p : ℕ,p.Prime → p ∣ q → IsNormalPrime (localNormalityScale h) p) →
      (∀ n ∈ R,(∃ m ∈ R,m≠n ∧ m.totient=n.totient) → ∃ c ∈ R,F n=c*q) →
      (∀ n ∈ Q,∃ p : ℕ,p.Prime ∧ p ∣ F n ∧ ¬IsNormalPrime (localNormalityScale h) p) →
      (∀ n ∈ Q,0<F n ∧ (F n).totient=d*n.totient ∧ ((d*n.totient:ℕ):ℝ)≤z) →
      (Q.card:ℝ) ≤ z/Real.log z*rho^(K*h) := by
  obtain ⟨C,hC,hcount⟩ := ppt_nonnormal_witness_count_bound
  obtain ⟨D,hD,henvelope⟩ := counting_envelope_real_bound
  filter_upwards [local_value_normality_decay_rate (mul_pos hC hD) hA K] with h hdecay
  intro z d q hz hB hlog hd R Q F hQR hR hq hbranch hbad hF
  have hz4 : 4 ≤ z := by linarith only [hz]
  have hb := counting_dyadic_index_bounds hz4
  have hs : 0 ≤ B (localNormalityScale h) := by
    simp only [localNormalityScale,B,Real.log_exp]
    positivity
  have hc := hcount (localNormalityScale h) z (countingDyadicIndex z) d q
    (localNormalityScale_gt_two h) hs hz hb.1 hb.2.1 hd R Q F hQR hR hq hbranch hbad hF
  rw [localNormalityScale_factor] at hc
  have hp := counting_normality_polynomial hz4 hB
  have hen := henvelope z hz4
  have hfac : 0 ≤ z/Real.log z := (div_pos (by linarith only [hz]) (Real.log_pos (by linarith only [hz]))).le
  have hB2 : 0 ≤ B (2*z) := by
    exact hB.trans (Real.log_le_log (Real.log_pos (by linarith only [hz]))
      (Real.log_le_log (by linarith only [hz]) (by linarith only [hz])))
  have hJ : 0 ≤ 1+Real.log (countingDyadicIndex z) := by
    have hh := Real.log_nonneg (show (1:ℝ) ≤ countingDyadicIndex z by exact_mod_cast hb.1)
    linarith only [hh]
  have hmul := mul_le_mul hen hp
    (mul_nonneg (pow_nonneg hB2 _) hJ) (by positivity)
  have hbound := mul_le_mul_of_nonneg_left hmul hC.le
  have hsave := hdecay (B z+4) (by linarith only [hB]) hlog
  calc
    _ ≤ (z/Real.log z)*(C*(dyadicTotientEnvelope (countingDyadicIndex z)*
        ((B (2*z))^5*(1+Real.log (countingDyadicIndex z))))*Real.exp (-(h:ℝ)^4/6)) := by
      convert hc using 1
      all_goals try with_reducible_and_instances rfl
      ring
    _ ≤ (z/Real.log z)*((C*D)*Real.exp (9*(Real.log (B z+4))^2)*
        (B z+4)^6*Real.exp (-(h:ℝ)^4/6)) := by
      apply mul_le_mul_of_nonneg_left _ hfac
      have hh := mul_le_mul_of_nonneg_right hbound (Real.exp_pos (-(h:ℝ)^4/6)).le
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsave hfac

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_AmbientResidualExceptions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original-head exceptions are counted at the ambient endpoint. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma ambient_local_log_bound : ∀ᶠ x : ℝ in atTop,
    Real.log (B x+4) ≤ 26*(m x:ℝ) := by
  filter_upwards [ford_band_log_upper,m_tendsto.eventually (eventually_ge_atTop 1),
    B_tendsto.eventually (eventually_ge_atTop (1:ℝ))] with x hlog hm hB
  have hh : Real.log (6*B x) ≤ 26*(m x:ℝ) := by
    simpa [fordBandScale] using hlog 0 (by omega)
  exact (Real.log_le_log (by linarith only [hB]) (by linarith only [hB])).trans hh

theorem ambient_nonnormal_witness_count_oai (d q : ℕ) (hd : 0 < d) :
    ∀ᶠ x : ℝ in atTop,∀ (R Q : Finset ℕ) (F : ℕ → ℕ),Q ⊆ R →
      (∀ r ∈ R,∀ p : ℕ,p.Prime → p ∣ r → IsNormalPrime (localNormalityScale (m x)) p) →
      (∀ p : ℕ,p.Prime → p ∣ q → IsNormalPrime (localNormalityScale (m x)) p) →
      (∀ r ∈ R,(∃ s ∈ R,s≠r ∧ s.totient=r.totient) → ∃ s ∈ R,F r=s*q) →
      (∀ r ∈ Q,∃ p : ℕ,p.Prime ∧ p ∣ F r ∧ ¬IsNormalPrime (localNormalityScale (m x)) p) →
      (∀ r ∈ Q,0<F r ∧ (F r).totient=d*r.totient ∧ ((d*r.totient:ℕ):ℝ)≤x) →
      (Q.card:ℝ) ≤ x/Real.log x*rho^(m x) := by
  filter_upwards [ambient_local_log_bound,
    m_tendsto.eventually (local_nonnormal_witness_count_rate (A:=26) (by norm_num) 1),
    B_tendsto.eventually (eventually_ge_atTop (0:ℝ)),eventually_ge_atTop (256:ℝ)]
    with x hlog hcount hB hx
  intro R Q F hQR hR hq hbranch hbad hF
  simpa only [one_mul] using hcount x d q hx hB hlog hd R Q F hQR hR hq hbranch hbad hF

end TotientAsymptotic

end

end OAI
end

theorem solution : type_of% @OAI.TotientAsymptotic.ambient_nonnormal_witness_count_oai := @OAI.TotientAsymptotic.ambient_nonnormal_witness_count_oai
