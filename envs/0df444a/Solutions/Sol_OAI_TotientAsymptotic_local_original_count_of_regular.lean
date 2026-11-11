-- Prove2me | solution 1 for OAI.TotientAsymptotic.local_original_count_of_regular
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:36:00.944239+00:00
-- url     : https://prove2.me/submissions/b3afe0d4-e692-4fd2-bc66-6c976ed50988

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
import Theorems.Thm_OAI_TotientAsymptotic_ambient_nonnormal_witness_count

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
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
end OAICompat434

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LargeSquareCount
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Counts for repeated large prime factors in values and their preimages. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma large_square_count (N K : ℕ) (Q : Finset ℕ)
    (hQ : ∀ n ∈ Q,0 < n ∧ n ≤ N ∧ ∃ d : ℕ,K < d ∧ d^2 ∣ n) :
    (Q.card:ℝ) ≤ 2*N/(K+1:ℕ) := by
  classical
  let P := Finset.Ioo K (N+1)
  let M := fun d : ℕ => (Finset.range (N+1)).filter (fun n => n ≠ 0 ∧ d^2 ∣ n)
  have hsub : Q ⊆ P.biUnion M := by
    intro n hn
    obtain ⟨hn0,hnN,d,hKd,hd⟩ := hQ n hn
    have hd1 : 1 ≤ d := by omega
    have hdn : d ≤ n := (by nlinarith : d ≤ d^2).trans (Nat.le_of_dvd hn0 hd)
    exact Finset.mem_biUnion.mpr ⟨d,Finset.mem_Ioo.mpr ⟨hKd,by omega⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hn0.ne',hd⟩⟩
  have hterm (d : ℕ) (hd : d ∈ P) : ((M d).card:ℝ) ≤ N/(d:ℝ)^2 := by
    have hd0 : 0 < d := by have := (Finset.mem_Ioo.mp hd).1; omega
    have hh : (M d).card=N/d^2 := Nat.card_multiples' N (d^2)
    rw [hh]
    have hle : (N/d^2)*d^2 ≤ N := Nat.div_mul_le_self N (d^2)
    apply (le_div_iff₀ (sq_pos_of_pos (show (0:ℝ)<d by exact_mod_cast hd0))).mpr
    exact_mod_cast hle
  calc
    _ ≤ ((P.biUnion M).card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ ∑ d ∈ P,((M d).card:ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le : (P.biUnion M).card ≤ ∑ d ∈ P,(M d).card)
    _ ≤ ∑ d ∈ P,N/(d:ℝ)^2 := Finset.sum_le_sum hterm
    _ = N*(∑ d ∈ P,((d:ℝ)^2)⁻¹) := by rw [Finset.mul_sum]; simp only [div_eq_mul_inv]
    _ ≤ N*(2/(K+1:ℕ)) := mul_le_mul_of_nonneg_left
      (by simpa [P,Nat.cast_add,Nat.cast_one] using (sum_Ioo_inv_sq_le (α:=ℝ) K (N+1))) (Nat.cast_nonneg N)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ShiftDivisorMass
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary reciprocal mass of divisible prime shifts and square tails. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma shifted_divisor_mass (N : ℕ) {d : ℕ} (hd : 0 < d) :
    (∑ p ∈ shiftDivisiblePrimes N d, ((p-1 : ℕ) : ℝ)⁻¹) ≤
      (1+Real.log N)/(d : ℝ) := by
  let Q := shiftDivisiblePrimes N d
  let f : ℕ → ℕ := fun p => (p-1)/d
  have hp (p : ℕ) (h : p ∈ Q) : p.Prime ∧ p ≤ N ∧ d ∣ p-1 := by
    obtain ⟨hN,hd⟩ := Finset.mem_filter.mp h
    obtain ⟨hN,hp⟩ := Nat.mem_primesLE.mp hN
    exact ⟨hp,hN,hd⟩
  have he (p : ℕ) (h : p ∈ Q) : d*f p=p-1 := Nat.mul_div_cancel' (hp p h).2.2
  have hi : Set.InjOn f (↑Q : Set ℕ) := by
    intro p hP q hQ h
    have h1 := he p hP
    have h2 := he q hQ
    have hp2 := (hp p hP).1.two_le
    have hq2 := (hp q hQ).1.two_le
    change f p=f q at h
    rw [h] at h1
    omega
  have hsub : Q.image f ⊆ Finset.Icc 1 N := by
    intro k hk
    obtain ⟨p,hpQ,rfl⟩ := Finset.mem_image.mp hk
    have h := hp p hpQ
    refine Finset.mem_Icc.mpr ⟨?_,(Nat.div_le_self _ _).trans ((Nat.sub_le p 1).trans h.2.1)⟩
    have hh := he p hpQ
    have h2 := h.1.two_le
    by_contra hn
    have hz : f p=0 := by omega
    rw [hz,mul_zero] at hh
    omega
  calc
    _ = (d : ℝ)⁻¹*∑ k ∈ Q.image f, (k : ℝ)⁻¹ := by
      rw [Finset.sum_image hi,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hpQ
      have hh : (d : ℝ)*(f p : ℝ)=((p-1 : ℕ) : ℝ) := by exact_mod_cast he p hpQ
      rw [← hh,mul_inv]
    _ ≤ (d : ℝ)⁻¹*∑ k ∈ Finset.Icc 1 N, (k : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)) (by positivity)
    _ = (d : ℝ)⁻¹*(harmonic N : ℝ) := by
      simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    _ ≤ _ := by
      simpa only [div_eq_mul_inv,mul_comm] using
        mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) (by positivity : 0 ≤ (d : ℝ)⁻¹)

lemma inverse_square_tail (Q : Finset ℕ) {z : ℝ} (hz : 1 ≤ z)
    (hQ : ∀ q ∈ Q, z < (q : ℝ)) :
    (∑ q ∈ Q, ((q : ℝ)^2)⁻¹) ≤ 2/z := by
  let k := ⌊z⌋₊
  let N := Q.sup id+1
  have hsub : Q ⊆ Finset.Ioo k N := by
    intro q hq
    refine Finset.mem_Ioo.mpr ⟨?_,?_⟩
    · have hh : (k : ℝ) ≤ z := Nat.floor_le (by linarith)
      have hqz := hQ q hq
      exact_mod_cast (show (k : ℝ) < q by linarith)
    · have hh : q ≤ Q.sup id := Finset.le_sup (f := id) hq
      dsimp [N]
      omega
  have hk : z < (k : ℝ)+1 := Nat.lt_floor_add_one z
  have hk0 : 0 < (k : ℝ)+1 := by positivity
  calc
    _ ≤ ∑ q ∈ Finset.Ioo k N, ((q : ℝ)^2)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    _ ≤ 2/((k : ℝ)+1) := sum_Ioo_inv_sq_le k N
    _ ≤ 2/z := div_le_div_of_nonneg_left (by norm_num) (by linarith) hk.le

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SquareDivisor
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A square in a finite product comes from one factor or two distinct factors. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma prime_dvd_product {ι : Type*} (I : Finset ι) (f : ι → ℕ)
    {q : ℕ} (hq : q.Prime) (hd : q ∣ ∏ j ∈ I, f j) : ∃ j ∈ I, q ∣ f j := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using hq.not_dvd_one hd
  | @insert a I ha ih =>
    rw [Finset.prod_insert ha] at hd
    rcases hq.dvd_mul.mp hd with h | h
    · exact ⟨a,Finset.mem_insert_self _ _,h⟩
    · obtain ⟨j,hj,hdj⟩ := ih h
      exact ⟨j,Finset.mem_insert_of_mem hj,hdj⟩

lemma square_dvd_product {ι : Type*} (I : Finset ι) (f : ι → ℕ)
    {q : ℕ} (hq : q.Prime) (hd : q^2 ∣ ∏ j ∈ I, f j) :
    (∃ j ∈ I, q^2 ∣ f j) ∨
    (∃ j ∈ I, ∃ k ∈ I, j ≠ k ∧ q ∣ f j ∧ q ∣ f k) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    have hh : q ∣ 1 := (dvd_pow_self q (by norm_num : 2 ≠ 0)).trans (by simpa using hd)
    exact (hq.not_dvd_one hh).elim
  | @insert a I ha ih =>
    rw [Finset.prod_insert ha] at hd
    by_cases h1 : q^2 ∣ f a
    · exact Or.inl ⟨a,Finset.mem_insert_self _ _,h1⟩
    by_cases h2 : q^2 ∣ ∏ j ∈ I, f j
    · rcases ih h2 with ⟨j,hj,hj2⟩ | ⟨j,hj,k,hk,hjk,hqj,hqk⟩
      · exact Or.inl ⟨j,Finset.mem_insert_of_mem hj,hj2⟩
      · exact Or.inr ⟨j,Finset.mem_insert_of_mem hj,k,Finset.mem_insert_of_mem hk,hjk,hqj,hqk⟩
    · have haq : q ∣ f a := by
        by_contra hn
        exact h2 (hq.prime.pow_dvd_of_dvd_mul_left 2 hn hd)
      have hIq : q ∣ ∏ j ∈ I, f j := by
        by_contra hn
        exact h1 (hq.prime.pow_dvd_of_dvd_mul_right 2 hn hd)
      obtain ⟨k,hk,hqk⟩ := prime_dvd_product I f hq hIq
      exact Or.inr ⟨a,Finset.mem_insert_self _ _,k,Finset.mem_insert_of_mem hk,
        (fun he => ha (he ▸ hk)),haq,hqk⟩

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTTotientSquare
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The large-square-in-a-totient branch of the PPT pruning argument.
Euler's product formula reduces it to a square in the integer, a square
in one prime predecessor, or a common factor of two distinct prime
predecessors.  Elementary reciprocal divisor bounds suffice when the
cutoff is a sufficiently large fixed power of the logarithm.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

theorem ppt_totient_square_cases {n p : ℕ} (hn : 0 < n) (hp : p.Prime)
    (hsq : p^2 ∣ n.totient) :
    p^2 ∣ n ∨
      (∃ q : ℕ, q.Prime ∧ q ∣ n ∧ p^2 ∣ q-1) ∨
      (∃ q r : ℕ, q.Prime ∧ r.Prime ∧ q ≠ r ∧ q ∣ n ∧ r ∣ n ∧
        p ∣ q-1 ∧ p ∣ r-1) := by
  by_cases hpn : p^2 ∣ n
  · exact Or.inl hpn
  have hnot : ¬p ∣ n/(∏ q ∈ n.primeFactors, q) := by
    intro hd
    have hrad := Nat.prod_primeFactors_dvd n
    have hpd : p ∣ n := hd.trans (Nat.div_dvd_of_dvd hrad)
    have hpmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpd, hn.ne'⟩
    have hpRad : p ∣ ∏ q ∈ n.primeFactors, q := Finset.dvd_prod_of_mem id hpmem
    have hmul := Nat.mul_dvd_mul hpRad hd
    rw [Nat.mul_div_cancel' hrad] at hmul
    exact hpn (by simpa only [pow_two] using hmul)
  rw [Nat.totient_eq_div_primeFactors_mul] at hsq
  have hprod := hp.prime.pow_dvd_of_dvd_mul_left 2 hnot hsq
  rcases square_dvd_product n.primeFactors (fun q : ℕ => q-1) hp hprod with
    ⟨q, hq, hsq⟩ | ⟨q, hq, r, hr, hne, hqp, hrp⟩
  · exact Or.inr (Or.inl ⟨q, Nat.prime_of_mem_primeFactors hq,
      Nat.dvd_of_mem_primeFactors hq, hsq⟩)
  · exact Or.inr (Or.inr ⟨q, r, Nat.prime_of_mem_primeFactors hq,
      Nat.prime_of_mem_primeFactors hr, hne, Nat.dvd_of_mem_primeFactors hq,
      Nat.dvd_of_mem_primeFactors hr, hqp, hrp⟩)

private lemma ppt_multiples_mem {N d n : ℕ} (hn : 0 < n) (hN : n ≤ N) (hd : d ∣ n) :
    n ∈ pptDivisorMultiples N d :=
  Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hn.ne', hd⟩

private lemma ppt_multiples_card (N d : ℕ) :
    ((pptDivisorMultiples N d).card : ℝ) ≤ (N : ℝ)/d := by
  have he : (pptDivisorMultiples N d).card = N/d := Nat.card_multiples' N d
  rw [he]
  exact Nat.cast_div_le

private lemma ppt_shift_prime_mem {N d q : ℕ} (hq : q ∈ shiftDivisiblePrimes N d) :
    q.Prime ∧ q ≤ N ∧ d ∣ q-1 := by
  have hh := Finset.mem_filter.mp hq
  have hp := Nat.mem_primesLE.mp hh.1
  exact ⟨hp.2, hp.1, hh.2⟩

private lemma ppt_shift_prime_reciprocal (N : ℕ) {d : ℕ} (hd : 0 < d) :
    (∑ q ∈ shiftDivisiblePrimes N d, (q : ℝ)⁻¹) ≤ (1+Real.log N)/(d : ℝ) := by
  apply le_trans _ (shifted_divisor_mass N hd)
  apply Finset.sum_le_sum
  intro q hq
  have hp := (ppt_shift_prime_mem hq).1
  exact inv_anti₀ (by exact_mod_cast Nat.sub_pos_of_lt hp.one_lt)
    (Nat.cast_le.mpr (Nat.sub_le q 1))

/-- A fixed prime-square divisor of a totient is rare among all integers,
without any restriction on their total number of prime factors. -/
theorem ppt_fixed_totient_square_count {N p : ℕ} (hp : p.Prime)
    (Q : Finset ℕ) (hQ : ∀ n ∈ Q, 0 < n ∧ n ≤ N ∧ p^2 ∣ n.totient) :
    (Q.card : ℝ) ≤ (N : ℝ)*(1+(1+Real.log N)+(1+Real.log N)^2)/(p : ℝ)^2 := by
  classical
  let L : ℝ := 1+Real.log N
  let R := shiftDivisiblePrimes N (p^2)
  let S := shiftDivisiblePrimes N p
  let Q₀ := pptDivisorMultiples N (p^2)
  let Q₁ := R.biUnion (pptDivisorMultiples N)
  let F : ℕ × ℕ → Finset ℕ := fun r =>
    if r.1 = r.2 then ∅ else pptDivisorMultiples N (r.1*r.2)
  let Q₂ := (S.product S).biUnion F
  have hsub : Q ⊆ Q₀ ∪ Q₁ ∪ Q₂ := by
    intro n hn
    obtain ⟨hn0, hnN, hsq⟩ := hQ n hn
    rcases ppt_totient_square_cases hn0 hp hsq with hnSq | hOne | hTwo
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (ppt_multiples_mem hn0 hnN hnSq))
    · obtain ⟨q, hq, hqn, hqSq⟩ := hOne
      have hqR : q ∈ R := Finset.mem_filter.mpr
        ⟨Nat.mem_primesLE.mpr ⟨(Nat.le_of_dvd hn0 hqn).trans hnN, hq⟩, hqSq⟩
      exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨q, hqR, ppt_multiples_mem hn0 hnN hqn⟩))
    · obtain ⟨q, r, hq, hr, hne, hqn, hrn, hqp, hrp⟩ := hTwo
      have hqS : q ∈ S := Finset.mem_filter.mpr
        ⟨Nat.mem_primesLE.mpr ⟨(Nat.le_of_dvd hn0 hqn).trans hnN, hq⟩, hqp⟩
      have hrS : r ∈ S := Finset.mem_filter.mpr
        ⟨Nat.mem_primesLE.mpr ⟨(Nat.le_of_dvd hn0 hrn).trans hnN, hr⟩, hrp⟩
      have hqrn := ((Nat.coprime_primes hq hr).mpr hne).mul_dvd_of_dvd_of_dvd hqn hrn
      apply Finset.mem_union_right
      refine Finset.mem_biUnion.mpr ⟨(q, r), Finset.mem_product.mpr ⟨hqS, hrS⟩, ?_⟩
      simpa only [F, ite_eq_right hne] using ppt_multiples_mem hn0 hnN hqrn
  have h₀ : (Q₀.card : ℝ) ≤ (N : ℝ)/(p : ℝ)^2 := by
    change ((pptDivisorMultiples N (p^2)).card : ℝ) ≤ (N : ℝ)/(p : ℝ)^2
    rw [← (Nat.cast_pow p 2 : ((p^2 : ℕ) : ℝ) = (p : ℝ)^2)]
    exact ppt_multiples_card N (p^2)
  have hR : (∑ q ∈ R, (q : ℝ)⁻¹) ≤ L/(p : ℝ)^2 := by
    simpa only [Nat.cast_pow] using ppt_shift_prime_reciprocal N (pow_pos hp.pos 2)
  have hS : (∑ q ∈ S, (q : ℝ)⁻¹) ≤ L/(p : ℝ) := ppt_shift_prime_reciprocal N hp.pos
  have h₁ : (Q₁.card : ℝ) ≤ (N : ℝ)*L/(p : ℝ)^2 := by
    calc
      _ ≤ ∑ q ∈ R, ((pptDivisorMultiples N q).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le : Q₁.card ≤ ∑ q ∈ R, (pptDivisorMultiples N q).card)
      _ ≤ ∑ q ∈ R, (N : ℝ)/q := Finset.sum_le_sum (fun q _ => ppt_multiples_card N q)
      _ = (N : ℝ)*(∑ q ∈ R, (q : ℝ)⁻¹) := by
        rw [Finset.mul_sum]
        simp only [div_eq_mul_inv]
      _ ≤ (N : ℝ)*(L/(p : ℝ)^2) := mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg N)
      _ = _ := by ring
  have h₂ : (Q₂.card : ℝ) ≤ (N : ℝ)*(L/(p : ℝ))^2 := by
    calc
      _ ≤ ∑ r ∈ S.product S, ((F r).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le : Q₂.card ≤ ∑ r ∈ S.product S, (F r).card)
      _ ≤ ∑ r ∈ S.product S, (N : ℝ)/(r.1*r.2 : ℕ) := by
        apply Finset.sum_le_sum
        intro r _
        by_cases he : r.1 = r.2
        · simp only [F, ite_eq_left he, Finset.card_empty, Nat.cast_zero]
          positivity
        · simpa only [F, ite_eq_right he] using ppt_multiples_card N (r.1*r.2)
      _ = (N : ℝ)*(∑ q ∈ S, (q : ℝ)⁻¹)^2 := by
        calc
          _ = ∑ q ∈ S, ∑ r ∈ S, (N : ℝ)/((q*r : ℕ) : ℝ) :=
            Finset.sum_product S S _
          _ = _ := by
            rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro q hq
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro r hr
            simp only [Nat.cast_mul, div_eq_mul_inv, mul_inv]
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hS 2)
        (Nat.cast_nonneg N)
  have hcard : (Q.card : ℝ) ≤ (Q₀.card : ℝ)+(Q₁.card : ℝ)+(Q₂.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans
      ((Finset.card_union_le (Q₀ ∪ Q₁) Q₂).trans
        (Nat.add_le_add_right (Finset.card_union_le Q₀ Q₁) Q₂.card))
  calc
    _ ≤ (N : ℝ)/(p : ℝ)^2 + (N : ℝ)*L/(p : ℝ)^2 + (N : ℝ)*(L/(p : ℝ))^2 :=
      hcard.trans (add_le_add (add_le_add h₀ h₁) h₂)
    _ = _ := by dsimp only [L] <;> ring

/-- Summing over the large square divisor uses the already proved inverse
square tail; the resulting cutoff may be any positive integer. -/
theorem ppt_large_totient_square_count {N K : ℕ} (hN : 1 ≤ N) (hK : 1 ≤ K)
    (Q : Finset ℕ)
    (hQ : ∀ n ∈ Q, 0 < n ∧ n ≤ N ∧ ∃ p : ℕ, p.Prime ∧ K < p ∧ p^2 ∣ n.totient) :
    (Q.card : ℝ) ≤ 6*(N : ℝ)*(1+Real.log N)^2/(K : ℝ) := by
  classical
  let R := (Nat.primesLE N).filter (fun p => K < p)
  let F : ℕ → Finset ℕ := fun p => Q.filter (fun n => p^2 ∣ n.totient)
  let L : ℝ := 1+Real.log N
  have hL : 1 ≤ L := by
    dsimp only [L]
    linarith [Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hN)]
  have hsub : Q ⊆ R.biUnion F := by
    intro n hn
    obtain ⟨hn0, hnN, p, hp, hKp, hsq⟩ := hQ n hn
    have hpn : p ≤ N :=
      (Nat.le_of_dvd (Nat.totient_pos.mpr hn0)
        ((dvd_pow_self p (by norm_num : 2 ≠ 0)).trans hsq)).trans
        ((Nat.totient_le n).trans hnN)
    exact Finset.mem_biUnion.mpr ⟨p,
      Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hpn, hp⟩, hKp⟩,
      Finset.mem_filter.mpr ⟨hn, hsq⟩⟩
  have htail : (∑ p ∈ R, ((p : ℝ)^2)⁻¹) ≤ 2/(K : ℝ) := by
    apply inverse_square_tail R (by exact_mod_cast hK)
    intro p hp
    exact_mod_cast (Finset.mem_filter.mp hp).2
  have hcoef : 0 ≤ (N : ℝ)*(1+L+L^2) := by positivity
  calc
    _ ≤ ∑ p ∈ R, ((F p).card : ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    _ ≤ ∑ p ∈ R, (N : ℝ)*(1+L+L^2)/(p : ℝ)^2 := by
      apply Finset.sum_le_sum
      intro p hp
      apply ppt_fixed_totient_square_count (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
      intro n hn
      have hh := Finset.mem_filter.mp hn
      exact ⟨(hQ n hh.1).1, (hQ n hh.1).2.1, hh.2⟩
    _ = (N : ℝ)*(1+L+L^2)*(∑ p ∈ R, ((p : ℝ)^2)⁻¹) := by
      rw [Finset.mul_sum]
      simp only [div_eq_mul_inv]
    _ ≤ (N : ℝ)*(1+L+L^2)*(2/(K : ℝ)) := mul_le_mul_of_nonneg_left htail hcoef
    _ ≤ _ := by
      have hpoly : 1+L+L^2 ≤ 3*L^2 := by nlinarith
      have hh := mul_le_mul_of_nonneg_left hpoly (show 0 ≤ (N : ℝ) by positivity)
      have hdiv := mul_le_mul_of_nonneg_right hh (show 0 ≤ 2/(K : ℝ) by positivity)
      dsimp only [L] at hdiv ⊢
      exact hdiv.trans_eq (by ring)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTSquareWitness
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Prune squares in a selected bad preimage and in its totient.  Injectivity
of the chosen preimages, rather than of the totient values, preserves the
cardinality bound required by the PPT construction.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

theorem ppt_square_witness_count {N K : ℕ} (hN : 1 ≤ N) (hK : 1 ≤ K)
    (S : Finset ℕ) (F : ℕ → ℕ) (hinj : Set.InjOn F (S : Set ℕ))
    (hsize : ∀ n ∈ S, 0 < F n ∧ F n ≤ N)
    (hsq : ∀ n ∈ S, ∃ p : ℕ, p.Prime ∧ K < p ∧
      (p^2 ∣ F n ∨ p^2 ∣ (F n).totient)) :
    (S.card : ℝ) ≤ 2*(N : ℝ)/(K+1 : ℕ) +
      6*(N : ℝ)*(1+Real.log N)^2/(K : ℝ) := by
  classical
  let Q := S.image F
  let A := Q.filter (fun u => ∃ p : ℕ, K < p ∧ p^2 ∣ u)
  let B := Q.filter (fun u => ∃ p : ℕ, p.Prime ∧ K < p ∧ p^2 ∣ u.totient)
  have hsizeQ (u : ℕ) (hu : u ∈ Q) : 0 < u ∧ u ≤ N := by
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hu
    exact hsize n hn
  have hcover : Q ⊆ A ∪ B := by
    intro u hu
    obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hu
    obtain ⟨p, hp, hKp, hcase⟩ := hsq n hn
    rcases hcase with hcase | hcase
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hu,
        p, hKp, he ▸ hcase⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hu,
        p, hp, hKp, he ▸ hcase⟩)
  have hA : (A.card : ℝ) ≤ 2*(N : ℝ)/(K+1 : ℕ) := by
    apply large_square_count N K A
    intro u hu
    have hh := Finset.mem_filter.mp hu
    exact ⟨(hsizeQ u hh.1).1, (hsizeQ u hh.1).2, hh.2⟩
  have hB : (B.card : ℝ) ≤ 6*(N : ℝ)*(1+Real.log N)^2/(K : ℝ) := by
    apply ppt_large_totient_square_count hN hK B
    intro u hu
    have hh := Finset.mem_filter.mp hu
    exact ⟨(hsizeQ u hh.1).1, (hsizeQ u hh.1).2, hh.2⟩
  have hcard : (S.card : ℝ) ≤ (A.card : ℝ)+(B.card : ℝ) := by
    rw [← Finset.card_image_of_injOn hinj]
    exact_mod_cast (Finset.card_le_card hcover).trans (Finset.card_union_le A B)
  exact hcard.trans (add_le_add hA hB)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PreimageLinearBound
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A linear-times-log-log size bound for every preimage of a bounded totient. -/
noncomputable section
namespace TotientAsymptotic

theorem totient_preimage_linear_loglog : ∃ C : ℝ,0 < C ∧
    ∀ z : ℝ,Real.exp 2 ≤ z → ∀ n : ℕ,0 < n → (n.totient:ℝ) ≤ z →
      (n:ℝ) ≤ C*z*(B z+2) := by
  obtain ⟨C,hC,hratio⟩ := totient_ratio_loglog_bound
  refine ⟨C,hC,?_⟩
  intro z hz n hn hφ
  have hz0 : 0 < z := (Real.exp_pos 2).trans_le hz
  have hlz : 2 ≤ Real.log z := (Real.le_log_iff_exp_le hz0).mpr hz
  have hz1 : 1 ≤ z := (Real.one_le_exp (by norm_num : (0:ℝ)≤2)).trans hz
  have hzsq : z ≤ z^2 := by nlinarith only [hz1]
  have hsize : (n:ℝ) ≤ 2*z^2 := by
    have hq : (n:ℝ) ≤ 2*(n.totient:ℝ)^2 := by exact_mod_cast totient_preimage_quadratic hn
    have hφ0 : (0:ℝ) ≤ n.totient := Nat.cast_nonneg _
    exact hq.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hφ0 hφ 2) (by norm_num))
  have hN : Real.exp 2 ≤ 2*z^2 := hz.trans (by nlinarith only [hzsq,hz0])
  have hB : B (2*z^2) ≤ B z+2 := by
    have hlog2 : Real.log (2:ℝ) ≤ 1 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
      norm_num at hh ⊢
      exact hh
    have hlog3 : Real.log (3:ℝ) ≤ 2 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
      norm_num at hh ⊢
      exact hh
    have hlog : Real.log (2*z^2) ≤ 3*Real.log z := by
      rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (pow_ne_zero 2 hz0.ne'),Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      nlinarith only [hlog2,hlz]
    have hlogpos : 0 < Real.log (2*z^2) := Real.log_pos (by nlinarith only [hz1])
    have hh := Real.log_le_log hlogpos hlog
    rw [Real.log_mul (by norm_num : (3:ℝ)≠0) (by linarith only [hlz] : Real.log z≠0)] at hh
    change Real.log (Real.log (2*z^2)) ≤ Real.log (Real.log z)+2
    linarith only [hh,hlog3]
  have hratio' := hratio (2*z^2) hN n hn hsize
  have hφpos : (0:ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr hn
  have hmain := (div_le_iff₀ hφpos).mp hratio'
  have hBpos : 0 ≤ B (2*z^2) := Real.log_nonneg
    (by have hh := (Real.le_log_iff_exp_le (show 0<2*z^2 by positivity)).mpr hN; linarith only [hh])
  calc
    (n:ℝ) ≤ C*B (2*z^2)*(n.totient:ℝ) := hmain
    _ ≤ C*B (2*z^2)*z := mul_le_mul_of_nonneg_left hφ (mul_nonneg hC.le hBpos)
    _ ≤ C*z*(B z+2) := by
      have hh := mul_le_mul_of_nonneg_left hB (mul_nonneg hC.le hz0.le)
      nlinarith only [hh]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalSquareCount
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The square discard at a local endpoint keeps the linear preimage scale. -/
noncomputable section
namespace TotientAsymptotic

lemma square_witness_local_bound {C z : ℝ} {N K : ℕ}
    (_hC : 0 < C) (hz : Real.exp 2 ≤ z) (hN : 1 ≤ N) (hK : 1 ≤ K)
    (hsize : (N:ℝ) ≤ C*z*(B z+2)) (hlog : Real.log N ≤ 2*Real.log z)
    (hcut : (Real.log z)^6 ≤ 2*(K:ℝ))
    (S : Finset ℕ) (F : ℕ → ℕ) (hinj : Set.InjOn F (S : Set ℕ))
    (hF : ∀ n ∈ S,0 < F n ∧ F n ≤ N)
    (hsq : ∀ n ∈ S,∃ p : ℕ,p.Prime ∧ K<p ∧ (p^2 ∣ F n ∨ p^2 ∣ (F n).totient)) :
    (S.card:ℝ) ≤ 112*C*z*(B z+2)/(Real.log z)^4 := by
  have hz0 : 0 < z := (Real.exp_pos 2).trans_le hz
  have hlz : 2 ≤ Real.log z := (Real.le_log_iff_exp_le hz0).mpr hz
  have hL : 0 < Real.log z := by linarith only [hlz]
  have hK0 : (0:ℝ) < K := by exact_mod_cast (show 0<K by omega)
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hlog' : (1+Real.log N)^2 ≤ 9*(Real.log z)^2 := by
    have hh : 1+Real.log N ≤ 3*Real.log z := by linarith only [hlog,hlz]
    have hp := pow_le_pow_left₀ (by linarith only [hlog0] : 0≤1+Real.log N) hh 2
    nlinarith only [hp]
  have hnK : (K:ℝ) ≤ ((K+1:ℕ):ℝ) := by exact_mod_cast Nat.le_succ K
  have hfirst : 2*(N:ℝ)/((K+1:ℕ):ℝ) ≤ 2*(N:ℝ)/K :=
    div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hN0) hK0 hnK
  have hsecond : 6*(N:ℝ)*(1+Real.log N)^2/(K:ℝ) ≤
      54*(N:ℝ)*(Real.log z)^2/(K:ℝ) := by
    apply div_le_div_of_nonneg_right _ hK0.le
    nlinarith only [mul_le_mul_of_nonneg_left hlog' (show 0≤6*(N:ℝ) by positivity)]
  have hsmall : (2*(N:ℝ)+54*(N:ℝ)*(Real.log z)^2)/(K:ℝ) ≤
      56*(N:ℝ)*(Real.log z)^2/(K:ℝ) := by
    apply div_le_div_of_nonneg_right _ hK0.le
    have hh : (1:ℝ) ≤ (Real.log z)^2 := by nlinarith only [hlz]
    nlinarith only [mul_le_mul_of_nonneg_left hh hN0]
  have hcut' : 56*(N:ℝ)*(Real.log z)^2/(K:ℝ) ≤
      112*(N:ℝ)/(Real.log z)^4 := by
    apply (div_le_div_iff₀ hK0 (pow_pos hL 4)).mpr
    have hh := mul_le_mul_of_nonneg_left hcut (show 0≤56*(N:ℝ) by positivity)
    nlinarith only [hh]
  have hc := ppt_square_witness_count hN hK S F hinj hF hsq
  calc
    (S.card:ℝ) ≤ 2*(N:ℝ)/((K+1:ℕ):ℝ)+6*(N:ℝ)*(1+Real.log N)^2/(K:ℝ) := hc
    _ ≤ 2*(N:ℝ)/K+54*(N:ℝ)*(Real.log z)^2/K := add_le_add hfirst hsecond
    _ = (2*(N:ℝ)+54*(N:ℝ)*(Real.log z)^2)/(K:ℝ) := by ring
    _ ≤ 56*(N:ℝ)*(Real.log z)^2/(K:ℝ) := hsmall
    _ ≤ 112*(N:ℝ)/(Real.log z)^4 := hcut'
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (pow_pos hL 4).le
      nlinarith only [hsize]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalSquareCutoff
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete logarithmic square cutoff for arbitrary selected preimages. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

theorem linear_preimage_cutoff_bounds {C : ℝ} (hC : 0 < C) :
    ∀ᶠ z : ℝ in atTop,
      let N := ⌈C*z*(B z+2)⌉₊
      1 ≤ N ∧ (N:ℝ) ≤ 2*C*z*(B z+2) ∧ Real.log N ≤ 2*Real.log z ∧
      1 ≤ localSquareCutoff z ∧ (Real.log z)^6 ≤ 2*(localSquareCutoff z:ℝ) := by
  have hlog : Tendsto (fun z : ℝ => Real.log z/z) atTop (nhds 0) := by
    simpa only [pow_one,id_eq] using (Real.isLittleO_pow_log_id_atTop (n:=1)).tendsto_div_nhds_zero
  have hinv : Tendsto (fun z : ℝ => 1/z) atTop (nhds 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero
  have hlim : Tendsto (fun z : ℝ => 2*C*(Real.log z+2)/z) atTop (nhds 0) := by
    convert (hlog.add (hinv.const_mul 2)).const_mul (2*C) using 1
    · funext z; ring
    · norm_num
  filter_upwards [hlim.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),
    B_tendsto.eventually (eventually_ge_atTop (2:ℝ)),eventually_ge_atTop (1/C),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2:ℝ)),
    eventually_gt_atTop (0:ℝ)] with z hsmall hB hzC hlz hz0
  let N := ⌈C*z*(B z+2)⌉₊
  have hCz : 1 ≤ C*z := by
    have hh := mul_le_mul_of_nonneg_left hzC hC.le
    have he : C*(1/C)=1 := by field_simp
    rw [he] at hh
    exact hh
  have hM : 1 ≤ C*z*(B z+2) := by nlinarith only [hCz,hB]
  have hN1 : 1 ≤ N := by
    exact Nat.one_le_ceil_iff.mpr (zero_lt_one.trans_le hM)
  have hN : (N:ℝ) ≤ 2*C*z*(B z+2) := by
    have hh := Nat.ceil_lt_add_one (zero_le_one.trans hM)
    change (N:ℝ) < C*z*(B z+2)+1 at hh
    nlinarith only [hh,hM]
  have hBLog : B z ≤ Real.log z := Real.log_le_self (by linarith only [hlz])
  have hline : 2*C*(B z+2) ≤ z := by
    have hh := (div_le_iff₀ hz0).mp hsmall.le
    have hh' := mul_le_mul_of_nonneg_left hBLog (show 0≤2*C by positivity)
    linarith only [hh,hh']
  have hNsquare : (N:ℝ) ≤ z^2 := by
    have hh := mul_le_mul_of_nonneg_right hline hz0.le
    nlinarith only [hN,hh]
  have hlogN : Real.log N ≤ 2*Real.log z := by
    have hh := Real.log_le_log (show (0:ℝ)<N by exact_mod_cast (show 0<N by omega)) hNsquare
    simpa only [Real.log_pow,Nat.cast_ofNat] using hh
  have hL : 2 ≤ (Real.log z)^6 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) hlz 6
    norm_num at hh
    linarith only [hh]
  have hfloor := Nat.sub_one_lt_floor ((Real.log z)^6)
  have hcut : (Real.log z)^6 ≤ 2*(localSquareCutoff z:ℝ) := by
    change (Real.log z)^6 ≤ 2*(⌊(Real.log z)^6⌋₊:ℝ)
    linarith only [hfloor,hL]
  have hcut1 : 1 ≤ localSquareCutoff z := by
    have hh : (1:ℝ) ≤ localSquareCutoff z := by linarith only [hL,hcut]
    exact_mod_cast hh
  exact ⟨hN1,hN,hlogN,hcut1,hcut⟩

theorem local_square_witness_count : ∃ C : ℝ,0 < C ∧ ∀ᶠ z : ℝ in atTop,
    ∀ (S : Finset ℕ) (F : ℕ → ℕ),Set.InjOn F (S : Set ℕ) →
      (∀ n ∈ S,0 < F n ∧ ((F n).totient:ℝ) ≤ z) →
      (∀ n ∈ S,∃ p : ℕ,p.Prime ∧ localSquareCutoff z<p ∧
        (p^2 ∣ F n ∨ p^2 ∣ (F n).totient)) →
      (S.card:ℝ) ≤ C*z*(B z+2)/(Real.log z)^4 := by
  obtain ⟨C,hC,hpreimage⟩ := totient_preimage_linear_loglog
  refine ⟨224*C,by positivity,?_⟩
  filter_upwards [linear_preimage_cutoff_bounds hC,eventually_ge_atTop (Real.exp 2)]
    with z hbounds hz
  dsimp only at hbounds
  intro S F hinj hF hsq
  let N := ⌈C*z*(B z+2)⌉₊
  have hsize (n) (hn : n∈S) : 0<F n ∧ F n≤N := by
    have hh := hF n hn
    refine ⟨hh.1,?_⟩
    exact_mod_cast (hpreimage z hz (F n) hh.1 hh.2).trans (Nat.le_ceil _)
  have hh := square_witness_local_bound (C:=2*C) (by positivity) hz
    hbounds.1 hbounds.2.2.2.1 hbounds.2.1 hbounds.2.2.1 hbounds.2.2.2.2 S F hinj hsize hsq
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalSquareDecay
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete square cutoff saves every fixed power of the local double logarithm. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma local_square_error_decay {C : ℝ} (hC : 0 < C) (K : ℝ) :
    ∀ᶠ z : ℝ in atTop,C*(B z+2)/(Real.log z)^3 ≤ (B z)^(-K) := by
  have ht : Tendsto (fun t : ℝ => (3*C)*t^(K+1)*Real.exp (-3*t)) atTop (nhds 0) := by
    simpa only [mul_zero,mul_assoc] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (K+1) 3 (by norm_num)).const_mul (3*C)
  filter_upwards [B_tendsto.eventually (ht.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))),
    B_tendsto.eventually (eventually_ge_atTop (1:ℝ)),eventually_gt_atTop (1:ℝ)]
    with z hz hB hz1
  have hB0 : 0 < B z := zero_lt_one.trans_le hB
  have hl : 0 < Real.log z := Real.log_pos hz1
  have he : Real.exp (-3*B z)=((Real.log z)^3)⁻¹ := by
    rw [show -3*B z= -((3:ℝ)*B z) by ring,Real.exp_neg]
    have hh : Real.exp ((3:ℝ)*B z)=(Real.log z)^3 := by
      simpa only [Nat.cast_ofNat,B,Real.exp_log hl] using Real.exp_nat_mul (B z) 3
    rw [hh]
  have hpower : (B z)^(K+1)=(B z)^K*B z := by
    rw [Real.rpow_add hB0,Real.rpow_one]
  have hmain : (C*(B z+2)/(Real.log z)^3)*(B z)^K ≤ 1 := by
    have hle : C*(B z+2) ≤ (3*C)*B z := by nlinarith only [hC,hB]
    have hh := mul_le_mul_of_nonneg_right hle
      (mul_nonneg (inv_pos.mpr (pow_pos hl 3)).le (Real.rpow_pos_of_pos hB0 K).le)
    calc
      _ = C*(B z+2)*(((Real.log z)^3)⁻¹*(B z)^K) := by ring
      _ ≤ (3*C)*B z*(((Real.log z)^3)⁻¹*(B z)^K) := hh
      _ ≤ 1 := by
        rw [hpower,he] at hz
        convert hz.le using 1
        all_goals try with_reducible_and_instances rfl
        ring
  have hpos := Real.rpow_pos_of_pos hB0 K
  have hh := (le_div_iff₀ hpos).mpr hmain
  simpa only [one_div,Real.rpow_neg hB0.le] using hh

theorem local_square_witness_power_saving (K : ℝ) :
    ∀ᶠ z : ℝ in atTop,∀ (S : Finset ℕ) (F : ℕ → ℕ),Set.InjOn F (S : Set ℕ) →
      (∀ n ∈ S,0 < F n ∧ ((F n).totient:ℝ) ≤ z) →
      (∀ n ∈ S,∃ p : ℕ,p.Prime ∧ localSquareCutoff z<p ∧
        (p^2 ∣ F n ∨ p^2 ∣ (F n).totient)) →
      (S.card:ℝ) ≤ z/Real.log z*(B z)^(-K) := by
  obtain ⟨C,hC,hcount⟩ := local_square_witness_count
  filter_upwards [hcount,local_square_error_decay hC K,eventually_gt_atTop (1:ℝ)] with z hz hdec hz1
  intro S F hinj hF hsq
  have hfac : 0 ≤ z/Real.log z := (div_pos (zero_lt_one.trans hz1) (Real.log_pos hz1)).le
  calc
    _ ≤ C*z*(B z+2)/(Real.log z)^4 := hz S F hinj hF hsq
    _ = (z/Real.log z)*(C*(B z+2)/(Real.log z)^3) := by
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hdec hfac

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeWindow
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform largest-prime windows for the actual subpower prefix denominators. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma subpower_log_ratio :
    Tendsto (fun x : ℝ => (Real.log x)^(4/5 : ℝ)/Real.log x) atTop (nhds 0) := by
  have hh := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<1/5)).comp Real.tendsto_log_atTop
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  dsimp only [Function.comp_def]
  rw [show -(1/5 : ℝ) = 4/5-1 by norm_num, Real.rpow_sub (Real.log_pos hx), Real.rpow_one]

lemma small_denominator_window {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hδsmall : δ ≤ 1/4) :
    ∀ᶠ x : ℝ in atTop, ∀ D t : ℝ, 1 ≤ D →
      Real.log D ≤ (Real.log x)^(4/5 : ℝ) → a*x ≤ t → t ≤ x →
      let z := t/D
      let y := 1+z
      x^(1/2 : ℝ) ≤ z ∧ z ≤ y ∧ y ≤ (1+δ)*z ∧
      (1-δ)*Real.log x ≤ Real.log y ∧ Real.log y ≤ (1+δ)*Real.log x := by
  have hc : Tendsto (fun x : ℝ => -Real.log a/Real.log x) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hh : Tendsto (fun x : ℝ => (Real.log x)^(4/5 : ℝ)/Real.log x +
      -Real.log a/Real.log x) atTop (nhds 0) := by
    simpa only [add_zero] using subpower_log_ratio.add hc
  have hroot : Tendsto (fun x : ℝ => x^(1/2 : ℝ)) atTop atTop := tendsto_rpow_atTop (by norm_num)
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    hh.eventually (eventually_lt_nhds hδ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (Real.log 2/δ)),
    hroot.eventually (eventually_ge_atTop (1/δ))] with x hx hsmall hlog2 hlarge
  intro D t hD hlogD ht htx
  dsimp only
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hL : 0 < Real.log x := Real.log_pos hx
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have ht0 : 0 < t := (mul_pos ha hx0).trans_le ht
  have hz0 : 0 < t/D := div_pos ht0 hD0
  have hlo : (1-δ)*Real.log x ≤ Real.log (t/D) := by
    have hb := (div_lt_iff₀ hL).mp (show ((Real.log x)^(4/5 : ℝ)-Real.log a)/Real.log x < δ by
      have e : ((Real.log x)^(4/5 : ℝ)-Real.log a)/Real.log x =
          (Real.log x)^(4/5 : ℝ)/Real.log x + -Real.log a/Real.log x := by ring
      rw [e]; exact hsmall)
    have hlt := Real.log_le_log (mul_pos ha hx0) ht
    rw [Real.log_mul ha.ne' hx0.ne'] at hlt
    rw [Real.log_div ht0.ne' hD0.ne']
    linarith
  have hz : x^(1/2 : ℝ) ≤ t/D := by
    rw [Real.rpow_def_of_pos hx0]
    calc
      _ ≤ Real.exp (Real.log (t/D)) := Real.exp_le_exp.mpr (by nlinarith)
      _ = _ := Real.exp_log hz0
  refine ⟨hz, by linarith, ?_, ?_, ?_⟩
  · have hh : 1 ≤ δ*(t/D) := by
      calc
        1 = δ*(1/δ) := by field_simp
        _ ≤ δ*(t/D) := mul_le_mul_of_nonneg_left (hlarge.trans hz) hδ.le
    linarith
  · exact hlo.trans (Real.log_le_log hz0 (by linarith))
  · have hzle : t/D ≤ x := (div_le_iff₀ hD0).mpr (by nlinarith)
    have hyle : 1+t/D ≤ 2*x := by linarith
    have hb := Real.log_le_log (by positivity : (0 : ℝ)<1+t/D) hyle
    rw [Real.log_mul (by norm_num : (2 : ℝ)≠0) hx0.ne'] at hb
    have h2 : Real.log 2 ≤ δ*Real.log x := by simpa only [mul_comm] using (div_le_iff₀ hδ).mp hlog2
    linarith

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTTrivialFibers
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The elementary part of Ford's full-fiber construction, *The distribution of
totients*, Section 5, p. 25, immediately after (5.18).  Its candidates have
every prime divisor larger than the fixed seed plus one.  Their target
preimages which contain the candidate are exactly its multiples by seed
preimages.  Thus the sieve only has to exclude preimages which do not
contain the candidate.

This reduction does not prove the abundance of candidates, or the bound on
the candidates with a nontrivial preimage.
-/

namespace TotientAsymptotic

open scoped BigOperators

/-- Every prime divisor of an inverse image of `d` is at most `d+1`. -/
lemma prime_le_seed_add_one {d m p : ℕ} (hd : 0 < d) (hm : m.totient = d)
    (hp : p.Prime) (hpm : p ∣ m) : p ≤ d+1 := by
  have hdiv : p-1 ∣ d := by
    simpa only [Nat.totient_prime hp, hm] using Nat.totient_dvd_of_dvd hpm
  have hle := Nat.le_of_dvd hd hdiv
  have hp1 := hp.one_lt
  omega

/-- A candidate supported on primes above `d+1` is coprime to every seed
preimage, independently of the number or exponents of its prime factors. -/
lemma seed_preimage_coprime {d b m : ℕ} (hd : 0 < d) (hm : m.totient = d)
    (hrough : ∀ p : ℕ, p.Prime → p ∣ b → d+1 < p) : b.Coprime m := by
  apply Nat.coprime_of_dvd
  intro p hp hpb hpm
  exact (not_lt_of_ge (prime_le_seed_add_one hd hm hp hpm)) (hrough p hp hpb)

lemma seed_multiple_totient {d b m : ℕ} (hd : 0 < d) (hm : m.totient = d)
    (hrough : ∀ p : ℕ, p.Prime → p ∣ b → d+1 < p) :
    (b*m).totient = d*b.totient := by
  rw [Nat.totient_mul (seed_preimage_coprime hd hm hrough), hm, Nat.mul_comm]

/-- The roughness hypothesis is inherited by a finite product of primes. -/
lemma primeProduct_rough {ι : Type*} (I : Finset ι) (p : ι → ℕ) (d : ℕ)
    (hp : ∀ i ∈ I, (p i).Prime) (hlarge : ∀ i ∈ I, d+1 < p i) :
    ∀ q : ℕ, q.Prime → q ∣ ∏ i ∈ I, p i → d+1 < q := by
  intro q hq hdiv
  obtain ⟨i, hi, hqi⟩ := (hq.prime.dvd_finsetProd_iff p).mp hdiv
  have heq : q = p i := (Nat.prime_dvd_prime_iff_eq hq (hp i hi)).mp hqi
  simpa only [heq] using hlarge i hi

end TotientAsymptotic

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTBadWitness
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The injective choice of nontrivial preimages used in Ford, Section 5,
p. 25, between (5.20) and (5.21).  Candidate sets are partitioned by their
totient value.  A singleton fiber uses its given nontrivial preimage; on a
larger fiber, a cyclic permutation followed by multiplication by a fixed
seed preimage supplies distinct nontrivial preimages.  The full fiber
multiplicity is retained throughout this construction.
-/

noncomputable section

namespace TotientAsymptotic

private lemma ppt_finRotate_ne_self {n : ℕ} (hn : 1 < n) (i : Fin n) :
    finRotate n i ≠ i := by
  cases n with
  | zero => omega
  | succ n =>
    intro he
    have hv := congrArg Fin.val he
    rw [coe_finRotate] at hv
    split_ifs at hv with hi
    · have hilast : (i : ℕ) = n := by rw [hi]; rfl
      omega
    · omega

private lemma pptFiniteRotation_ne_self (α : Type*) [Fintype α]
    (hcard : 1 < Fintype.card α) (a : α) : pptFiniteRotation α a ≠ a := by
  intro he
  have he' := congrArg (Fintype.equivFin α) he
  have he'' : finRotate (Fintype.card α) (Fintype.equivFin α a) =
      Fintype.equivFin α a := by
    simpa only [pptFiniteRotation, Equiv.trans_apply, Equiv.apply_symm_apply] using he'
  exact ppt_finRotate_ne_self hcard _ he''

/-- Two rough candidates of the same totient cannot properly divide one
another.  The only alternative in the general totient lemma is doubling,
which roughness excludes. -/
lemma ppt_rough_eq_of_dvd_same_totient {d b c : ℕ} (hd : 0 < d)
    (hc : ∀ p : ℕ, p.Prime → p ∣ c → d+1 < p)
    (hφ : b.totient = c.totient) (hdiv : b ∣ c) : b = c := by
  apply (Nat.eq_or_eq_of_totient_eq_totient hdiv hφ).resolve_right
  intro hdouble
  have htwo : 2 ∣ c := by rw [← hdouble]; exact dvd_mul_right 2 b
  have hh := hc 2 Nat.prime_two htwo
  omega

lemma ppt_rough_eq_of_dvd_seed_multiple {d q b c : ℕ} (hd : 0 < d)
    (hq : q.totient = d)
    (hb : ∀ p : ℕ, p.Prime → p ∣ b → d+1 < p)
    (hc : ∀ p : ℕ, p.Prime → p ∣ c → d+1 < p)
    (hφ : b.totient = c.totient) (hdiv : b ∣ c*q) : b = c := by
  apply ppt_rough_eq_of_dvd_same_totient hd hc hφ
  exact (seed_preimage_coprime hd hq hb).dvd_mul_right.mp hdiv

private lemma ppt_bad_witness_on_fiber {d q v : ℕ} (hd : 0 < d)
    (hqpos : 0 < q) (hq : q.totient = d) (T : Finset ℕ)
    (hT : ∀ n ∈ T, 0 < n ∧ n.totient = v ∧
      ∀ p : ℕ, p.Prime → p ∣ n → d+1 < p)
    (hbad : ∀ n ∈ T, ∃ u : ℕ, 0 < u ∧ u.totient = d*n.totient ∧ ¬n ∣ u) :
    ∃ F : ℕ → ℕ, Set.InjOn F (T : Set ℕ) ∧
      ∀ n ∈ T, 0 < F n ∧ (F n).totient = d*n.totient ∧ ¬n ∣ F n ∧
        (1 < T.card → ∃ c ∈ T, F n = c*q) := by
  classical
  by_cases hcard : 1 < T.card
  · let σ := pptFiniteRotation ↥T
    let F : ℕ → ℕ := fun n => if hn : n ∈ T then (σ ⟨n, hn⟩).val*q else 0
    have hσ (n : ↥T) : (σ n).val ≠ n.val := by
      intro he
      apply pptFiniteRotation_ne_self ↥T (by simpa using hcard) n
      exact Subtype.ext he
    have hF (n : ℕ) (hn : n ∈ T) : F n = (σ ⟨n, hn⟩).val*q := by
      simp only [F, dite_eq_left hn]
    refine ⟨F, ?_, ?_⟩
    · intro n hn m hm he
      change n ∈ T at hn
      change m ∈ T at hm
      have he' : (σ ⟨n, hn⟩).val*q = (σ ⟨m, hm⟩).val*q := by
        simpa only [hF n hn, hF m hm] using he
      have he'' := Nat.eq_of_mul_eq_mul_right hqpos he'
      have hs : σ ⟨n, hn⟩ = σ ⟨m, hm⟩ := Subtype.ext he''
      exact congrArg Subtype.val (σ.injective hs)
    · intro n hn
      let c := σ ⟨n, hn⟩
      have hc := hT c.val c.property
      have hn' := hT n hn
      have hcn : c.val.totient = n.totient := hc.2.1.trans hn'.2.1.symm
      have hnF : F n = c.val*q := hF n hn
      rw [hnF]
      refine ⟨Nat.mul_pos hc.1 hqpos, ?_, ?_, ?_⟩
      · rw [seed_multiple_totient hd hq hc.2.2, hcn]
      · intro hdiv
        have he := ppt_rough_eq_of_dvd_seed_multiple hd hq hn'.2.2 hc.2.2 hcn.symm hdiv
        exact hσ ⟨n, hn⟩ he.symm
      · intro _
        exact ⟨c.val, c.property, rfl⟩
  · let F : ℕ → ℕ := fun n => if hn : n ∈ T then Classical.choose (hbad n hn) else 0
    have hsmall : T.card ≤ 1 := Nat.le_of_not_gt hcard
    refine ⟨F, ?_, ?_⟩
    · intro n hn m hm _
      exact Finset.card_le_one.mp hsmall n hn m hm
    · intro n hn
      have hb := Classical.choose_spec (hbad n hn)
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa only [F, dite_eq_left hn] using hb.1
      · simpa only [F, dite_eq_left hn] using hb.2.1
      · simpa only [F, dite_eq_left hn] using hb.2.2
      · intro hc
        omega

/-- The injective association retains its seed-multiple construction on
every nonsingleton totient fiber. This is needed for normality exclusion. -/
theorem ppt_injective_bad_preimages_seed_branch {d q : ℕ} (hd : 0 < d)
    (hqpos : 0 < q) (hq : q.totient = d) (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ ∀ p : ℕ, p.Prime → p ∣ n → d+1 < p)
    (hbad : ∀ n ∈ S, ∃ u : ℕ, 0 < u ∧ u.totient = d*n.totient ∧ ¬n ∣ u) :
    ∃ F : ℕ → ℕ, Set.InjOn F (S : Set ℕ) ∧
      (∀ n ∈ S, 0 < F n ∧ (F n).totient = d*n.totient ∧ ¬n ∣ F n) ∧
      ∀ n ∈ S, (∃ m ∈ S, m ≠ n ∧ m.totient = n.totient) →
        ∃ c ∈ S, F n = c*q := by
  classical
  let T : ℕ → Finset ℕ := fun v => S.filter (fun n => n.totient = v)
  have hex (v : ℕ) : ∃ F : ℕ → ℕ, Set.InjOn F (T v : Set ℕ) ∧
      ∀ n ∈ T v, 0 < F n ∧ (F n).totient = d*n.totient ∧ ¬n ∣ F n ∧
        (1 < (T v).card → ∃ c ∈ T v, F n = c*q) := by
    apply ppt_bad_witness_on_fiber hd hqpos hq (T v)
    · intro n hn
      have hh := Finset.mem_filter.mp hn
      exact ⟨(hS n hh.1).1, hh.2, (hS n hh.1).2⟩
    · intro n hn
      exact hbad n (Finset.mem_filter.mp hn).1
  choose F hFinj hFprop using hex
  let G : ℕ → ℕ := fun n => F n.totient n
  have hmem (n : ℕ) (hn : n ∈ S) : n ∈ T n.totient := Finset.mem_filter.mpr ⟨hn, rfl⟩
  have hG (n : ℕ) (hn : n ∈ S) :
      0 < G n ∧ (G n).totient = d*n.totient ∧ ¬n ∣ G n := by
    have hh := hFprop n.totient n (hmem n hn)
    exact ⟨hh.1, hh.2.1, hh.2.2.1⟩
  refine ⟨G, ?_, hG, ?_⟩
  · intro n hn m hm he
    have hscaled : d*n.totient = d*m.totient :=
      (hG n hn).2.1.symm.trans ((congrArg Nat.totient he).trans (hG m hm).2.1)
    have hv : n.totient = m.totient := Nat.eq_of_mul_eq_mul_left hd hscaled
    apply hFinj n.totient (hmem n hn) (Finset.mem_filter.mpr ⟨hm, hv.symm⟩)
    change F n.totient n = F m.totient m at he
    simpa only [← hv] using he
  · intro n hn hmulti
    obtain ⟨m, hm, hmn, hφ⟩ := hmulti
    have hmT : m ∈ T n.totient := Finset.mem_filter.mpr ⟨hm, hφ⟩
    have hc : 1 < (T n.totient).card := by
      by_contra hsmall
      have hcard : (T n.totient).card ≤ 1 := Nat.le_of_not_gt hsmall
      exact hmn (Finset.card_le_one.mp hcard m hmT n (hmem n hn))
    obtain ⟨c, hcT, hcF⟩ := (hFprop n.totient n (hmem n hn)).2.2.2 hc
    exact ⟨c, (Finset.mem_filter.mp hcT).1, hcF⟩

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTSeedNormality
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The fixed seed introduces no nonnormal prime factors in the rotated-fiber
branch of Ford's construction.  For a fixed prime, the interval part of
normality is eventually vacuous and the small-factor bound follows from
`B(S) → ∞`.  This is the elementary seed step in exclusion (vi), p. 27.
-/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma ppt_normal_prime_of_small_shift {p : ℕ} {S : ℝ} (hp : p.Prime)
    (hpS : (p-1 : ℕ) ≤ S)
    (hΩ : ((p-1).primeFactorsList.length : ℝ) ≤ 2*B S) :
    IsNormalPrime S p := by
  refine ⟨hp, ?_, ?_⟩
  · have hc : omegaIn (p-1) 1 S ≤ (p-1).primeFactorsList.length :=
      List.length_filter_le _ _
    exact (Nat.cast_le.mpr hc).trans hΩ
  · intro U T hSU hUT hT
    exfalso
    linarith

lemma ppt_fixed_prime_eventually_normal {p : ℕ} (hp : p.Prime) :
    ∀ᶠ S : ℝ in atTop, IsNormalPrime S p := by
  filter_upwards [eventually_ge_atTop (((p-1 : ℕ) : ℝ)),
    B_tendsto.eventually (eventually_ge_atTop
      (((p-1).primeFactorsList.length : ℝ)/2))] with S hS hB
  exact ppt_normal_prime_of_small_shift hp hS (by linarith)

/-- All prime divisors of one fixed positive seed preimage are eventually
normal for the same parameter. -/
theorem ppt_seed_prime_factors_eventually_normal {c : ℕ} (hc : 0 < c) :
    ∀ᶠ S : ℝ in atTop, ∀ p : ℕ, p.Prime → p ∣ c → IsNormalPrime S p := by
  have he : ∀ᶠ S : ℝ in atTop, ∀ p ∈ c.primeFactors, IsNormalPrime S p :=
    (eventually_all_finset c.primeFactors).mpr (fun p hp =>
      ppt_fixed_prime_eventually_normal (Nat.prime_of_mem_primeFactors hp))
  filter_upwards [he] with S hS
  intro p hp hpc
  exact hS p (Nat.mem_primeFactors.mpr ⟨hp, hpc, hc.ne'⟩)

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

theorem ambient_square_witness_count :
    ∀ᶠ x : ℝ in atTop,∀ (Q : Finset ℕ) (F : ℕ → ℕ),Set.InjOn F (Q : Set ℕ) →
      (∀ r ∈ Q,0<F r ∧ ((F r).totient:ℝ)≤x) →
      (∀ r ∈ Q,∃ p : ℕ,p.Prime ∧ localNormalityScale (m x)<p ∧
        (p^2 ∣ F r ∨ p^2 ∣ (F r).totient)) →
      (Q.card:ℝ) ≤ x/Real.log x*(B x)^(-4:ℝ) := by
  filter_upwards [ambient_local_log_bound,
    m_tendsto.eventually (local_square_cutoff_le_normality (A:=26) (by norm_num)),
    local_square_witness_power_saving (4:ℝ),
    B_tendsto.eventually (eventually_ge_atTop (0:ℝ)),eventually_gt_atTop (1:ℝ)]
    with x hlog hcut hcount hB hx
  intro Q F hinj hF hbad
  apply hcount Q F hinj hF
  intro r hr
  obtain ⟨p,hp,hlarge,hsq⟩ := hbad r hr
  refine ⟨p,hp,?_,hsq⟩
  exact_mod_cast (hcut x hx hB hlog).trans_lt hlarge

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_HeadPrimeCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform abundance of head primes above a subpower tail denominator. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma mem_head_prime_interval {x D : ℝ} (hx : 0 ≤ x) (hD : 0 < D) {p : ℕ}
    (hp : p ∈ primeInterval (x/(2*D)) (x/D)) :
    p.Prime ∧ x/(2*D) < p ∧ (p:ℝ) ≤ x/D := by
  obtain ⟨hp,hlo⟩ := Finset.mem_filter.mp hp
  have hh := Nat.mem_primesLE.mp hp
  exact ⟨hh.2,hlo,(Nat.cast_le.mpr hh.1).trans (Nat.floor_le (div_nonneg hx hD.le))⟩

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CandidateArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The head-prime extension counts actual distinct integers and their totients. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

lemma candidate_prime_extension_totient {n : ℕ} {p : Fin n → ℕ} {q : ℕ}
    (hp : ∀ i,(p i).Prime) (hq : q.Prime) (hqp : ∀ i,p i < q) :
    (q*(∏ i,p i)).totient=(q-1)*(∏ i,p i).totient := by
  have hcop : q.Coprime (∏ i,p i) := by
    apply Nat.coprime_prod_right_iff.mpr
    intro i _
    apply hq.coprime_iff_not_dvd.mpr
    intro hdvd
    have hh := Nat.le_of_dvd (hp i).pos hdvd
    exact (not_le_of_gt (hqp i)) hh
  rw [Nat.totient_mul hcop,Nat.totient_prime hq]

lemma candidate_totient_bound {n : ℕ} {x : ℝ} (hx : 0 ≤ x) {d : ℕ} (hd : 0 < d)
    {p : Fin n → ℕ} {q : ℕ} (hp : ∀ i,(p i).Prime)
    (hq : q ∈ primeInterval (x/(2*((d*(∏ i,p i).totient:ℕ):ℝ)))
      (x/((d*(∏ i,p i).totient:ℕ):ℝ))) (hqp : ∀ i,p i < q) :
    ((d*(q*(∏ i,p i)).totient:ℕ):ℝ) ≤ x := by
  have hr : 0 < ∏ i,p i := Finset.prod_pos (fun i _ => (hp i).pos)
  have hD : (0:ℝ) < ((d*(∏ i,p i).totient:ℕ):ℝ) := by
    exact_mod_cast Nat.mul_pos hd (Nat.totient_pos.mpr hr)
  obtain ⟨hqprime,_,hqu⟩ := mem_head_prime_interval hx hD hq
  rw [candidate_prime_extension_totient hp hqprime hqp]
  have hh := (le_div_iff₀ hD).mp hqu
  have hle : (q-1:ℝ)*((d*(∏ i,p i).totient:ℕ):ℝ) ≤ x := by
    nlinarith only [hh,hD]
  push_cast
  rw [Nat.cast_sub hqprime.one_le,Nat.cast_one]
  push_cast at hle
  nlinarith only [hle]

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

lemma capped_tail_denominator_budget (d : ℕ) : ∀ᶠ x : ℝ in atTop,
    Real.log (d:ℝ)+(m x:ℝ)*Real.exp ((19/25:ℝ)*B x) ≤ (Real.log x)^(4/5:ℝ) := by
  have h₁ : Tendsto (fun x : ℝ => B x*Real.exp (-(1/25:ℝ)*B x)) atTop (nhds 0) := by
    simpa only [Real.rpow_one,Function.comp_def,neg_mul] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1:ℝ) (1/25) (by norm_num)).comp B_tendsto
  have h₂ : Tendsto (fun x : ℝ => Real.log (d:ℝ)*Real.exp (-(4/5:ℝ)*B x)) atTop (nhds 0) := by
    simpa only [Real.rpow_zero,one_mul,mul_zero,Function.comp_def,neg_mul] using
      ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (0:ℝ) (4/5) (by norm_num)).comp B_tendsto).const_mul (Real.log (d:ℝ))
  have hs := (h₁.add h₂).eventually (eventually_lt_nhds (by norm_num : (0:ℝ)+0<1))
  filter_upwards [hs,ambient_polynomial_budget 1 1,eventually_gt_atTop (1:ℝ)] with x hx hm hx1
  have hm' : (m x:ℝ) ≤ B x := by simpa only [one_mul,pow_one] using hm
  have he : (B x*Real.exp (-(1/25:ℝ)*B x)+Real.log (d:ℝ)*Real.exp (-(4/5:ℝ)*B x))*
      Real.exp ((4/5:ℝ)*B x)=
      B x*Real.exp ((19/25:ℝ)*B x)+Real.log (d:ℝ) := by
    rw [add_mul,mul_assoc,mul_assoc,←Real.exp_add,←Real.exp_add]
    rw [show -(1/25:ℝ)*B x+(4/5:ℝ)*B x=(19/25:ℝ)*B x by ring,
      show -(4/5:ℝ)*B x+(4/5:ℝ)*B x=0 by ring,Real.exp_zero,mul_one]
  have hh := mul_le_mul_of_nonneg_right hx.le (Real.exp_pos ((4/5:ℝ)*B x)).le
  rw [he,one_mul] at hh
  have hpower : Real.exp ((4/5:ℝ)*B x)=(Real.log x)^(4/5:ℝ) := by
    rw [Real.rpow_def_of_pos (Real.log_pos hx1)]
    unfold B
    rw [mul_comm]
  rw [hpower] at hh
  have hmul := mul_le_mul_of_nonneg_right hm' (Real.exp_pos ((19/25:ℝ)*B x)).le
  linarith only [hmul,hh]

lemma capped_prime_tail_denominator {d : ℕ} (hd : 0 < d) :
    ∀ᶠ x : ℝ in atTop,∀ n : ℕ,n ≤ m x → ∀ p : Fin n → ℕ,
      (∀ i,(p i).Prime) → (∀ i,primePrefixCoord p i ≤ (19/25:ℝ)*B x) →
      Real.log ((d*(∏ i,p i).totient:ℕ):ℝ) ≤ (Real.log x)^(4/5:ℝ) := by
  filter_upwards [capped_tail_denominator_budget d] with x hx
  intro n hn p hp hcap
  have hr : 0 < ∏ i,p i := Finset.prod_pos (fun i _ => (hp i).pos)
  have hφ : 0 < (∏ i,p i).totient := Nat.totient_pos.mpr hr
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have hφ' : (0:ℝ) < (∏ i,p i:ℕ).totient := by exact_mod_cast hφ
  have hlog := Real.log_le_log hφ'
    (show ((∏ i,p i:ℕ).totient:ℝ) ≤ (∏ i,p i:ℕ) by
      exact_mod_cast Nat.totient_le (∏ i,p i))
  have htail := prime_tail_log_bound p hp hcap
  have hdim := mul_le_mul_of_nonneg_right (show (n:ℝ) ≤ m x by exact_mod_cast hn)
    (Real.exp_pos ((19/25:ℝ)*B x)).le
  rw [Nat.cast_mul,Real.log_mul hd'.ne' hφ'.ne']
  linarith only [hlog,htail,hdim,hx]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CandidateHeadSeparation
attribute [-simp] _root_.SelbergSieve.selbergBoundingSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prime extension is larger than every prime in the capped tail. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma capped_prime_le_sqrt : ∀ᶠ x : ℝ in atTop,∀ p : ℕ,p.Prime →
    Real.log (Real.log (p:ℝ)) ≤ (19/25:ℝ)*B x → (p:ℝ) ≤ x^(1/2:ℝ) := by
  filter_upwards [B_tendsto.eventually (eventually_ge_atTop ((25/6:ℝ)*Real.log 2)),
    eventually_gt_atTop (1:ℝ)] with x hB hx
  intro p hp hcap
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have hsmall : Real.exp (-(6/25:ℝ)*B x) ≤ 1/2 := by
    have he := Real.exp_le_exp.mpr (show -(6/25:ℝ)*B x ≤ -Real.log 2 by linarith only [hB])
    simpa only [Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<2),one_div] using he
  have hfactor : Real.exp ((19/25:ℝ)*B x)=
      Real.exp (B x)*Real.exp (-(6/25:ℝ)*B x) := by
    rw [←Real.exp_add]
    congr 1
    ring
  have hbexp : Real.exp (B x)=Real.log x := Real.exp_log (Real.log_pos hx)
  have hlog : Real.log (p:ℝ) ≤ (1/2:ℝ)*Real.log x := by
    have he := Real.exp_le_exp.mpr hcap
    rw [Real.exp_log (Real.log_pos hp1),hfactor,hbexp] at he
    have hh := mul_le_mul_of_nonneg_left hsmall (Real.log_pos hx).le
    nlinarith only [he,hh]
  have he := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hp0] at he
  rw [Real.rpow_def_of_pos hx0]
  simpa only [mul_comm] using he

lemma head_interval_above_tail : ∀ᶠ x : ℝ in atTop,
    ∀ D : ℝ,1 ≤ D → Real.log D ≤ (Real.log x)^(4/5:ℝ) →
      ∀ n : ℕ,∀ p : Fin n → ℕ,(∀ i,(p i).Prime) →
        (∀ i,primePrefixCoord p i ≤ (19/25:ℝ)*B x) →
        ∀ q ∈ primeInterval (x/(2*D)) (x/D),q.Prime ∧ ∀ i,p i < q := by
  filter_upwards [capped_prime_le_sqrt,
    small_denominator_window (a:=1/2) (δ:=1/4) (by norm_num) (by norm_num) (by norm_num),
    eventually_gt_atTop (1:ℝ)] with x hcap hwindow hx
  intro D hD hlog n p hp hcoords q hq
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  obtain ⟨hqprime,hql,_⟩ := mem_head_prime_interval hx0.le hD0 hq
  refine ⟨hqprime,?_⟩
  have hsize := hwindow D ((1/2:ℝ)*x) hD hlog le_rfl (by linarith only [hx0])
  have hroot : x^(1/2:ℝ) ≤ x/(2*D) := by
    convert hsize.1 using 1
    all_goals try with_reducible_and_instances rfl
    ring
  intro i
  exact_mod_cast (hcap (p i) (hp i) (hcoords i)).trans_lt (hroot.trans_lt hql)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CandidateProperties
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arithmetic and size properties of the actual counted candidates. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem raw_candidate_prime_data {c : ℝ} (hc : 0 < c) (d : ℕ) (hd : 0 < d) :
    ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,∀ b ∈ rawCandidates x c d H,
      ∃ (p : Fin (m x-H) → ℕ) (q : ℕ),
        b=q*(∏ i,p i) ∧ (∀ i,(p i).Prime) ∧ StrictAnti p ∧
        primePrefixCoord p ∈ relaxedGeometricFamily (m x) (m x-H) (B x) (c/2) ∧
        (∀ i,primePrefixCoord p i ≤ (19/25:ℝ)*B x) ∧
        q ∈ primeInterval (x/(2*((d*(∏ i,p i).totient:ℕ):ℝ)))
          (x/((d*(∏ i,p i).totient:ℕ):ℝ)) ∧
        q.Prime ∧ (∀ i,p i < q) ∧
        Real.log ((d*(∏ i,p i).totient:ℕ):ℝ) ≤ (Real.log x)^(4/5:ℝ) := by
  filter_upwards [head_limited_prime_coordinates hc] with H hH
  filter_upwards [hH,capped_prime_tail_denominator hd,head_interval_above_tail,
    m_tendsto.eventually (eventually_ge_atTop H)] with x hcoords hdenom hhead hm
  intro b hb
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨hzQ,hzq⟩ := Finset.mem_sigma.mp hz
  have hn : m x-H+H=m x := Nat.sub_add_cancel hm
  obtain ⟨hpr,hr,hcap⟩ := hcoords (m x-H) hn z.1 hzQ
  have hD : (1:ℝ) ≤ ((d*(∏ i,z.1 i).totient:ℕ):ℝ) := by
    exact_mod_cast Nat.mul_pos hd (Nat.totient_pos.mpr
      (Finset.prod_pos (fun i _ => (hpr i).pos)))
  have hlog := hdenom (m x-H) (Nat.sub_le _ _) z.1 hpr hcap
  obtain ⟨hq,hqp⟩ := hhead _ hD hlog _ z.1 hpr hcap z.2 hzq
  exact ⟨z.1,z.2,rfl,hpr,prime_coordinates_strictAnti hpr hr.1.2.1,
    hr,hcap,hzq,hq,hqp,hlog⟩

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CandidateRoughness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-seed roughness of the counted candidates. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem raw_candidate_rough {c : ℝ} (hc : 0 < c) (d : ℕ) (hd : 0 < d) :
    ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,∀ b ∈ rawCandidates x c d H,
      ∀ p : ℕ,p.Prime → p ∣ b → d+1 < p := by
  filter_upwards [raw_candidate_prime_data hc d hd,
    geometric_dominates_polynomial (half_pos hc) ((d:ℝ)+2) 0] with H hH hlarge
  filter_upwards [hH,m_tendsto.eventually (eventually_ge_atTop (H+1))]
    with x hx hm
  intro b hb
  obtain ⟨p,q,rfl,hp,_,hr,_,_,hq,hqp,_⟩ := hx b hb
  have hn : 0 < m x-H := by omega
  have htail (i : Fin (m x-H)) : d+1 < p i := by
    have hi := i.isLt
    have hdH : H ≤ m x-i.val := by omega
    have hl := hlarge (m x-i.val) hdH
    simp only [pow_zero,mul_one] at hl
    have hp1 : (1:ℝ) ≤ p i := by exact_mod_cast (hp i).one_le
    have hcoord : primePrefixCoord p i ≤ p i :=
      (Real.log_le_self (Real.log_nonneg hp1)).trans (Real.log_le_self (Nat.cast_nonneg _))
    have hh := hl.trans ((hr.2.1 i).trans hcoord)
    have hh' : (d:ℝ)+1 < p i := by linarith only [hh]
    exact_mod_cast hh'
  have hhead : d+1 < q := (htail ⟨0,hn⟩).trans (hqp ⟨0,hn⟩)
  intro r hpr hdvd
  rcases hpr.dvd_mul.mp hdvd with hdiv|hdiv
  · have he : r=q := (Nat.prime_dvd_prime_iff_eq hpr hq).mp hdiv
    exact he ▸ hhead
  · exact primeProduct_rough Finset.univ p d (fun i _ => hp i)
      (fun i _ => htail i) r hpr hdiv

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CandidatePrimeList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The counted prime tuples as finite ordered lists for prefix cancellation. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma candidatePrimeAt_fin {n : ℕ} (p : Fin n → ℕ) (q : ℕ) (i : Fin (n+1)) :
    candidatePrimeAt p q i= (Fin.cons q p : Fin (n+1) → ℕ) i := by
  simp only [candidatePrimeAt,dite_eq_left i.isLt]

lemma candidatePrimeAt_product {n : ℕ} (p : Fin n → ℕ) (q : ℕ) :
    pptSuffixProduct (candidatePrimeAt p q) (n+1) 0=q*(∏ i,p i) := by
  unfold pptSuffixProduct
  rw [Nat.Ico_zero_eq_range,Finset.prod_range]
  simp only [candidatePrimeAt_fin,Fin.prod_cons]

lemma candidatePrimeAt_prime {n : ℕ} (p : Fin n → ℕ) {q : ℕ}
    (hp : ∀ i,(p i).Prime) (hq : q.Prime) :
    ∀ i < n+1,(candidatePrimeAt p q i).Prime := by
  intro i hi
  have hh : ∀ j : Fin (n+1),((Fin.cons q p : Fin (n+1) → ℕ) j).Prime := by
    intro j
    refine Fin.cases hq (fun k => hp k) j
  simpa only [candidatePrimeAt,dite_eq_left hi] using hh ⟨i,hi⟩

lemma candidatePrimeAt_order {n : ℕ} (p : Fin n → ℕ) {q : ℕ}
    (hp : StrictAnti p) (hq : ∀ i,p i < q) :
    ∀ i k : ℕ,i < k → k < n+1 → candidatePrimeAt p q k < candidatePrimeAt p q i := by
  have ho : StrictAnti (Fin.cons q p) := by
    apply (Fin.strictMono_cons (α:=OrderDual ℕ)).mpr
    exact ⟨hq,hp⟩
  intro i k hik hk
  have hi : i < n+1 := hik.trans hk
  simpa only [candidatePrimeAt,dite_eq_left hi,dite_eq_left hk] using
    ho (show (⟨i,hi⟩:Fin (n+1)) < ⟨k,hk⟩ from hik)

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

lemma local_regular_candidates_subset {x c : ℝ} {d L H : ℕ} :
    localRegularCandidates x c d L H ⊆ rawCandidates x c d H := by
  intro b hb
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨hp,hq⟩ := Finset.mem_sigma.mp hz
  exact Finset.mem_image.mpr ⟨z,Finset.mem_sigma.mpr
    ⟨local_regular_tuples_subset hp,hq⟩,rfl⟩

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalNormalCandidates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A positive family of actual candidates with head and indexed tail normality. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

lemma local_normal_candidates_subset {x c : ℝ} {d L H : ℕ} :
    localNormalCandidates x c d L H ⊆ localRegularCandidates x c d L H := by
  intro b hb
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hb
  exact Finset.mem_image.mpr ⟨z,(Finset.mem_filter.mp hz).1,rfl⟩

lemma local_normal_candidate_representation {x c : ℝ} {d L H b : ℕ}
    (hb : b ∈ localNormalCandidates x c d L H) :
    ∃ (p : Fin (m x-H) → ℕ) (q : ℕ),
      b=q*(∏ i,p i) ∧ p ∈ localRegularPrimeTuples x c L H ∧
      q ∈ primeInterval (x/(2*((d*(∏ i,p i).totient:ℕ):ℝ)))
        (x/((d*(∏ i,p i).totient:ℕ):ℝ)) ∧
      IsNormalPrime (localNormalityScale (m x)) q ∧
      ∀ i j : Fin (m x-H),i ≤ j → IsNormalPrime (localNormalityScale (m x-i.val)) (p j) := by
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨hz,hnormal⟩ := Finset.mem_filter.mp hz
  obtain ⟨hp,hq⟩ := Finset.mem_sigma.mp hz
  exact ⟨z.1,z.2,rfl,hp,hq,hnormal,local_regular_normality hp⟩

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalCandidateLists
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local normality requirements persist after every removed prefix. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma candidatePrimeAt_zero {n : ℕ} (p : Fin n → ℕ) (q : ℕ) :
    candidatePrimeAt p q 0=q := by
  simpa only [Fin.val_zero,Fin.cons_zero] using candidatePrimeAt_fin p q (0 : Fin (n+1))

lemma candidatePrimeAt_succ {n : ℕ} (p : Fin n → ℕ) (q i : ℕ) (hi : i<n) :
    candidatePrimeAt p q (i+1)=p ⟨i,hi⟩ := by
  simpa only [Fin.val_succ,Fin.cons_succ] using
    candidatePrimeAt_fin p q (Fin.succ ⟨i,hi⟩)

lemma candidatePrimeAt_local_normality {m n : ℕ} (p : Fin n → ℕ) (q : ℕ)
    (hq : IsNormalPrime (localNormalityScale m) q)
    (hp : ∀ i j : Fin n,i ≤ j → IsNormalPrime (localNormalityScale (m-i.val)) (p j)) :
    ∀ J k : ℕ,J ≤ k → k < n+1 →
      IsNormalPrime (localNormalityScale (m-(J-1))) (candidatePrimeAt p q k) := by
  intro J k hJk hk
  by_cases hk0 : k=0
  · have hJ0 : J=0 := by omega
    simpa only [hk0,hJ0,Nat.zero_sub,Nat.sub_zero,candidatePrimeAt_zero] using hq
  have hk' : k-1<n := by omega
  have hkE : k-1+1=k := by omega
  rw [←hkE,candidatePrimeAt_succ p q (k-1) hk']
  have hJ : J-1<n := by omega
  exact hp ⟨J-1,hJ⟩ ⟨k-1,hk'⟩ (by change J-1 ≤ k-1; omega)

theorem local_normal_candidate_list_data {c : ℝ} (hc : 0 < c)
    (d : ℕ) (hd : 0 < d) (L : ℕ) :
    ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∃ p : ℕ → ℕ → ℕ,∀ b ∈ localNormalCandidates x c d L H,
        b=pptSuffixProduct (p b) (m x-H+1) 0 ∧
        (∀ i < m x-H+1,(p b i).Prime) ∧
        (∀ i k : ℕ,i < k → k < m x-H+1 → p b k < p b i) ∧
        (∀ i < m x-H+1,d+1 < p b i) ∧
        ∀ J k : ℕ,J ≤ k → k < m x-H+1 →
          IsNormalPrime (localNormalityScale (m x-(J-1))) (p b k) := by
  classical
  filter_upwards [head_limited_prime_coordinates hc,raw_candidate_rough hc d hd] with H hcoord hrough
  filter_upwards [hcoord,hrough,m_tendsto.eventually (eventually_ge_atTop H),
    capped_prime_tail_denominator hd,head_interval_above_tail]
    with x hcoord hrough hm hdenom hhead
  have hex (b : ℕ) (hb : b ∈ localNormalCandidates x c d L H) :
      ∃ r : ℕ → ℕ,b=pptSuffixProduct r (m x-H+1) 0 ∧
        (∀ i < m x-H+1,(r i).Prime) ∧
        (∀ i k : ℕ,i < k → k < m x-H+1 → r k < r i) ∧
        (∀ i < m x-H+1,d+1 < r i) ∧
        ∀ J k : ℕ,J ≤ k → k < m x-H+1 →
          IsNormalPrime (localNormalityScale (m x-(J-1))) (r k) := by
    obtain ⟨p,q,he,hpQ,hinterval,hqnormal,hpnorm⟩ := local_normal_candidate_representation hb
    obtain ⟨hpr,hr,hcap⟩ := hcoord _ (Nat.sub_add_cancel hm) p (local_regular_tuples_subset hpQ)
    have ho := prime_coordinates_strictAnti hpr hr.1.2.1
    have hD : (1:ℝ) ≤ ((d*(∏ i,p i).totient:ℕ):ℝ) := by
      exact_mod_cast Nat.mul_pos hd (Nat.totient_pos.mpr
        (Finset.prod_pos (fun i _ => (hpr i).pos)))
    obtain ⟨hq,hqp⟩ := hhead _ hD (hdenom _ (Nat.sub_le _ _) p hpr hcap) _ p hpr hcap q hinterval
    let r := candidatePrimeAt p q
    have hprod := candidatePrimeAt_product p q
    have hrpr := candidatePrimeAt_prime p hpr hq
    refine ⟨r,he.trans hprod.symm,hrpr,candidatePrimeAt_order p ho hqp,?_,
      candidatePrimeAt_local_normality p q hqnormal hpnorm⟩
    intro i hi
    apply hrough b (local_regular_candidates_subset (local_normal_candidates_subset hb))
      (r i) (hrpr i hi)
    rw [he,←hprod]
    exact Finset.dvd_prod_of_mem r (Finset.mem_Ico.mpr ⟨Nat.zero_le _,hi⟩)
  choose p hp using hex
  refine ⟨fun b => if hb : b ∈ localNormalCandidates x c d L H then p b hb else fun _ => 1,?_⟩
  intro b hb
  simpa only [dite_eq_left hb] using hp b hb

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalBadCandidates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual failed candidates admit normal, ordered, maximal-prefix residuals. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

lemma normal_prime_divisor_suffix {N J : ℕ} {p : ℕ → ℕ} {S : ℝ}
    (hprime : ∀ i < N,(p i).Prime)
    (hnormal : ∀ i,J ≤ i → i < N → IsNormalPrime S (p i)) :
    ∀ q : ℕ,q.Prime → q ∣ pptSuffixProduct p N J → IsNormalPrime S q := by
  intro q hq hdiv
  obtain ⟨i,hi,hqi⟩ := (hq.prime.dvd_finsetProd_iff p).mp hdiv
  have hi' := Finset.mem_Ico.mp hi
  have he : q=p i := (Nat.prime_dvd_prime_iff_eq hq (hprime i hi'.2)).mp hqi
  exact he ▸ hnormal i hi'.1 hi'.2

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalResidualWitness
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choose bad preimages on each distinct residual family before dyadic counting. -/
noncomputable section
namespace TotientAsymptotic

theorem local_bad_residual_witness {d q : ℕ} (hd : 0 < d)
    (hqpos : 0 < q) (hq : q.totient=d) (R : Finset ℕ)
    (hR : ∀ r ∈ R,PPTBadResidual d r) :
    ∃ F : ℕ → ℕ,Set.InjOn F (R : Set ℕ) ∧
      (∀ r ∈ R,0 < F r ∧ (F r).totient=d*r.totient ∧ ¬r ∣ F r ∧
        largestPrimeFactor (F r) ≠ largestPrimeFactor r) ∧
      ∀ r ∈ R,(∃ s ∈ R,s≠r ∧ s.totient=r.totient) →
        ∃ s ∈ R,F r=s*q := by
  obtain ⟨F,hinj,hF,hseed⟩ := ppt_injective_bad_preimages_seed_branch hd hqpos hq R
    (fun r hr => ⟨(hR r hr).1,(hR r hr).2.1⟩)
    (fun r hr => (hR r hr).2.2.1)
  refine ⟨F,hinj,?_,hseed⟩
  intro r hr
  have hh := hF r hr
  exact ⟨hh.1,hh.2.1,hh.2.2,(hR r hr).2.2.2 (F r) hh.1 hh.2.1 hh.2.2⟩

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

lemma local_residual_card_partition (R : Finset ℕ) (F : ℕ → ℕ) (h : ℕ) :
    R.card ≤ (localWitnessNonnormal R F h).card+(localWitnessSquare R F h).card+
      (localWitnessRegular R F h).card := by
  classical
  let N := localWitnessNonnormal R F h
  let S := localWitnessSquare R F h
  have hsub : N∪S ⊆ R := Finset.union_subset
    (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hsplit := Finset.card_sdiff_add_card_eq_card hsub
  have hunion := Finset.card_union_le N S
  change R.card ≤ N.card+S.card+(R\(N∪S)).card
  omega

lemma localNormalityScale_tendsto : Tendsto localNormalityScale atTop atTop :=
  Real.tendsto_exp_atTop.comp (Real.tendsto_exp_atTop.comp
    ((tendsto_pow_atTop (by decide : 4≠0)).comp tendsto_natCast_atTop_atTop))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalOriginalExceptions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Direct exceptional counts for the original-head branch of the actual family. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem local_normal_candidate_normality_and_value {c : ℝ} (hc : 0 < c)
    (d : ℕ) (hd : 0 < d) (L : ℕ) :
    ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,∀ b ∈ localNormalCandidates x c d L H,
      ((d*b.totient:ℕ):ℝ) ≤ x ∧
      ∀ p : ℕ,p.Prime → p ∣ b → IsNormalPrime (localNormalityScale (m x)) p := by
  filter_upwards [local_normal_candidate_list_data hc d hd L,
    raw_candidate_prime_data hc d hd] with H hlist hraw
  filter_upwards [hlist,hraw,eventually_ge_atTop (0:ℝ)] with x hlist hraw hx
  obtain ⟨p,hp⟩ := hlist
  intro b hb
  have hbr := local_regular_candidates_subset (local_normal_candidates_subset hb)
  obtain ⟨t,q,he,ht,_ho,_hr,_hcap,hinterval,_hq,hqp,_hlog⟩ := hraw b hbr
  refine ⟨?_,?_⟩
  · rw [he]
    exact candidate_totient_bound hx hd ht hinterval hqp
  · intro r hr hdiv
    have hh := hp b hb
    have hnorm : ∀ i : ℕ, 0 ≤ i → i < m x-H+1 →
        IsNormalPrime (localNormalityScale (m x)) (p b i) := by
      intro i hi hiN
      simpa only [Nat.zero_sub,Nat.sub_zero] using hh.2.2.2.2 0 i hi hiN
    have hdiv' : r ∣ pptSuffixProduct (p b) (m x-H+1) 0 := by
      rw [←hh.1]
      exact hdiv
    exact normal_prime_divisor_suffix hh.2.1 hnorm r hr hdiv' 

theorem local_original_exception_data {c : ℝ} (hc : 0 < c)
    (d q : ℕ) (hd : 0 < d) (hqpos : 0 < q) (hq : q.totient=d) (L : ℕ) :
    ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      let R := localOriginalBad x c d L H
      ∃ F : ℕ → ℕ,Set.InjOn F (R : Set ℕ) ∧
        (∀ r ∈ R,0<F r ∧ (F r).totient=d*r.totient ∧ ¬r ∣ F r ∧
          largestPrimeFactor (F r) ≠ largestPrimeFactor r) ∧
        ((localWitnessNonnormal R F (m x)).card:ℝ) ≤ x/Real.log x*rho^(m x) ∧
        ((localWitnessSquare R F (m x)).card:ℝ) ≤ x/Real.log x*(B x)^(-4:ℝ) := by
  classical
  filter_upwards [local_normal_candidate_normality_and_value hc d hd L] with H hH
  filter_upwards [hH,ambient_nonnormal_witness_count d q hd,ambient_square_witness_count,
    (localNormalityScale_tendsto.comp m_tendsto).eventually
      (ppt_seed_prime_factors_eventually_normal hqpos)] with x hx hn hs hseed
  let R := localOriginalBad x c d L H
  have hR (r) (hr : r∈R) : r∈localNormalCandidates x c d L H :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1
  obtain ⟨F,hinj,hF,hbranch⟩ := local_bad_residual_witness hd hqpos hq R
    (fun _ hr => (Finset.mem_filter.mp hr).2)
  refine ⟨F,hinj,hF,?_,?_⟩
  · apply hn R (localWitnessNonnormal R F (m x)) F (Finset.filter_subset _ _)
      (fun r hr => (hx r (hR r hr)).2) hseed hbranch
      (fun _ hr => (Finset.mem_filter.mp hr).2)
    intro r hr
    have hrR := (Finset.mem_filter.mp hr).1
    exact ⟨(hF r hrR).1,(hF r hrR).2.1,(hx r (hR r hrR)).1⟩
  · apply hs (localWitnessSquare R F (m x)) F (hinj.mono (Finset.filter_subset _ _))
    · intro r hr
      have hrR := (Finset.mem_filter.mp hr).1
      refine ⟨(hF r hrR).1,?_⟩
      rw [(hF r hrR).2.1]
      exact (hx r (hR r hrR)).1
    · exact fun _ hr => (Finset.mem_filter.mp hr).2

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalOriginalPruning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two direct exceptions and the surviving comparison case cover
the actual original-head bad candidates. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

theorem local_original_count_of_regular_oai {c : ℝ} (hc : 0 < c)
    (d q : ℕ) (hd : 0 < d) (hqpos : 0 < q) (hq : q.totient=d) (L : ℕ) :
    ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      (∀ F : ℕ → ℕ,let R := localOriginalBad x c d L H
        Set.InjOn F (R : Set ℕ) →
        (∀ r ∈ R,0<F r ∧ (F r).totient=d*r.totient ∧ ¬r ∣ F r ∧
          largestPrimeFactor (F r) ≠ largestPrimeFactor r) →
        ((localWitnessRegular R F (m x)).card:ℝ) ≤ x/Real.log x*(B x)^(-4:ℝ)) →
      ((localOriginalBad x c d L H).card:ℝ) ≤
        x/Real.log x*(rho^(m x)+2*(B x)^(-4:ℝ)) := by
  filter_upwards [local_original_exception_data hc d q hd hqpos hq L] with H hH
  filter_upwards [hH] with x hx
  intro hregular
  obtain ⟨F,hinj,hF,hn,hs⟩ := hx
  have hr := hregular F hinj hF
  have hpart : ((localOriginalBad x c d L H).card:ℝ) ≤
      ((localWitnessNonnormal (localOriginalBad x c d L H) F (m x)).card:ℝ)+
      ((localWitnessSquare (localOriginalBad x c d L H) F (m x)).card:ℝ)+
      ((localWitnessRegular (localOriginalBad x c d L H) F (m x)).card:ℝ) := by
    exact_mod_cast local_residual_card_partition (localOriginalBad x c d L H) F (m x)
  nlinarith only [hpart,hn,hs,hr]

end TotientAsymptotic

end

end OAI
end

theorem solution : type_of% @OAI.TotientAsymptotic.local_original_count_of_regular_oai := @OAI.TotientAsymptotic.local_original_count_of_regular_oai
