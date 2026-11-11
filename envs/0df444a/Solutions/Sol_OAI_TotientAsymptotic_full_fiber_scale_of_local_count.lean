-- Prove2me | solution 1 for OAI.TotientAsymptotic.full_fiber_scale_of_local_count
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:34:43.696884+00:00
-- url     : https://prove2.me/submissions/1105512e-9d44-4744-a691-ee34c25d6c3f

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
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_Prefactor
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.TotientAsymptotic.mem_prefixDataFinset _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
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

lemma sub_div_self_tendsto (k : ℕ) :
    Tendsto (fun x : ℝ => ((m x-k : ℕ) : ℝ)/(m x : ℝ)) atTop (nhds 1) := by
  have hi : Tendsto (fun x : ℝ => (m x : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp m_tendsto)
  have hh : Tendsto (fun x : ℝ => 1-(k : ℝ)*(m x : ℝ)⁻¹) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub (hi.const_mul (k : ℝ))
  apply hh.congr'
  filter_upwards [m_tendsto.eventually (eventually_ge_atTop k),
    m_tendsto.eventually (eventually_gt_atTop 0)] with x hk hm
  rw [Nat.cast_sub hk]
  field_simp [show (m x : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr hm.ne']

lemma normalized_prefactor_step (hford : FordRenewalInput) (k : ℕ) :
    Tendsto (fun x : ℝ => alpha (theta x) *
      (((m x-k : ℕ) : ℝ)*g (m x-k)/B x)) atTop (nhds (gamma*rho^k)) := by
  have hn := (normalizedRenewal_properties hford).1.comp
    ((tendsto_sub_atTop_nat k).comp m_tendsto)
  have hh := (((sub_div_self_tendsto k).mul hn).mul_const (rho^k)).div
    bandCenterRatio_tendsto (by norm_num : (1 : ℝ) ≠ 0)
  simp only [one_mul, div_one] at hh
  apply hh.congr'
  filter_upwards [B_tendsto.eventually (eventually_gt_atTop (1 : ℝ)),
    m_tendsto.eventually (eventually_ge_atTop k),
    m_tendsto.eventually (eventually_gt_atTop 0)] with x hB hk hm
  have hpow : rho^(m x-k)*rho^k = rho^(m x) := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  change (((m x-k : ℕ) : ℝ)/(m x : ℝ) * normalizedRenewal (m x-k) * rho^k) /
      bandCenterRatio x = alpha (theta x) * (((m x-k : ℕ) : ℝ)*g (m x-k)/B x)
  rw [alpha_theta_eq hB]
  unfold normalizedRenewal bandCenterRatio
  have hmn : (m x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hl : Real.log (B x) ≠ 0 := (Real.log_pos hB).ne'
  field_simp [hmn, hl, lam_pos.ne', (zero_lt_one.trans hB).ne']
  rw [← hpow]
  ring

lemma normalized_prefactor_limit (hford : FordRenewalInput) (H : ℕ) :
    Tendsto (fun x : ℝ => alpha (theta x)^H * G x (R x H)/G x (m x))
      atTop (nhds (rho^(H*(H-1)/2)*gamma^H)) := by
  have hh := tendsto_finsetProd (Finset.range H)
    (fun k _ => normalized_prefactor_step hford k)
  have hp : (∏ k ∈ Finset.range H, gamma*rho^k) = rho^(H*(H-1)/2)*gamma^H := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
      Finset.prod_pow_eq_pow_sum, Finset.sum_range_id]
    ring
  rw [hp] at hh
  apply hh.congr'
  filter_upwards [m_tendsto.eventually (eventually_ge_atTop H),
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with x hm hB
  rw [show R x H = m x-H from rfl, G_sub_eq_product hB (m x) H hm,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  field_simp [(G_pos hB (m x)).ne']

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
-- module Solutions.OAIQ233_TA.TotientFibers_FiniteFiber
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace TotientFibers

theorem totient_prime_prod {Q : Finset ℕ} (hQ : ∀ p ∈ Q, p.Prime) :
    Nat.totient (∏ p ∈ Q, p) = ∏ p ∈ Q, (p - 1) := by
  have hpos : 0 < ∏ p ∈ Q, p := Finset.prod_pos fun p hp => (hQ p hp).pos
  apply Nat.mul_right_cancel hpos
  simpa only [Nat.primeFactors_prod hQ, mul_comm] using
    Nat.totient_mul_prod_primeFactors (∏ p ∈ Q, p)

end TotientFibers

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTComparisonBridge
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Fixed-common-factor and fixed-left-tail arithmetic for Ford's comparison estimate.
Fixing the left tail `a` includes its totient in `D = d * φ(a)`, and the common
prime product `c` supplies the divisor `r = φ(c)`.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma ppt_totient_primeProduct {b : ℕ} (p : Fin b → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    (∏ i, p i).totient = shiftedProduct p := by
  classical
  have hprime : ∀ q ∈ Finset.univ.image p, q.Prime := by
    intro q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    exact hp i
  have hh := TotientFibers.totient_prime_prod hprime
  rw [Finset.prod_image (fun i _ j _ he => hinj he),
    Finset.prod_image (fun i _ j _ he => hinj he)] at hh
  exact hh

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FixedPrefixLower
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive comparison of a fixed prefix dimension with the natural scale. -/
noncomputable section
open scoped Topology
open Filter MeasureTheory
namespace TotientAsymptotic

theorem fixed_prefix_volume_lower (H : ℕ) : ∃ c : ℝ,0 < c ∧
    ∀ᶠ x : ℝ in atTop, c*G x (m x) ≤ G x (m x-H) := by
  let a := rho^(H*(H-1)/2)*gamma^H
  let b := (lam/rho)^H
  have ha : 0 < a := mul_pos (pow_pos rho_pos _) (pow_pos gamma_pos _)
  have hb : 0 < b := by dsimp [b]; exact pow_pos (div_pos lam_pos rho_pos) H
  refine ⟨a/(2*b),by positivity,?_⟩
  have hp := normalized_prefactor_limit fordRenewalInput H
  filter_upwards [hp.eventually (eventually_gt_nhds (show a/2 < a by linarith)),
    theta_eventually_mem,B_tendsto.eventually (eventually_gt_atTop (0:ℝ))]
    with x hx hphase hB
  have hg := G_pos hB (m x)
  have hratio : 0 ≤ G x (m x-H)/G x (m x) := div_nonneg (G_pos hB _).le hg.le
  have halpha : alpha (theta x)^H ≤ b :=
    pow_le_pow_left₀ (alpha_pos _).le (alpha_le _ hphase) H
  have hlo : a/2 ≤ b*(G x (m x-H)/G x (m x)) := by
    have hh := mul_le_mul_of_nonneg_right halpha hratio
    have hx' : a/2 ≤ alpha (theta x)^H*(G x (m x-H)/G x (m x)) := by
      simpa only [R,mul_div_assoc] using hx.le
    exact hx'.trans hh
  have hdiv : a/(2*b) ≤ G x (m x-H)/G x (m x) := by
    have hh : (a/2)/b ≤ G x (m x-H)/G x (m x) :=
      (div_le_iff₀ hb).mpr (by simpa only [mul_comm] using hlo)
    simpa only [div_div] using hh
  exact (le_div_iff₀ hg).mp hdiv

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FiniteCandidateRatio
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded totient ratio for the actual finite geometric candidate family. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma finite_reverse_geometric_sum {n m : ℕ} (hn : n ≤ m) :
    (∑ i : Fin n,rho^(m-i.val)) ≤ (1-rho)⁻¹ := by
  let s := Finset.univ.image (fun i : Fin n => m-i.val)
  have hinj : Function.Injective (fun i : Fin n => m-i.val) := by
    intro i j hij
    dsimp only at hij
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    omega
  have he : (∑ i : Fin n,rho^(m-i.val))=∑ k ∈ s,rho^k := by
    dsimp only [s]
    rw [Finset.sum_image (fun i _ j _ hij => hinj hij)]
  rw [he]
  simpa only [tsum_geometric_of_lt_one rho_pos.le rho_lt_one,one_div] using
    (summable_geometric_of_lt_one rho_pos.le rho_lt_one).sum_le_tsum s
      (fun _ _ => pow_nonneg rho_pos.le _)

lemma finite_geometric_prime_reciprocals {n m : ℕ} (hn : n ≤ m) {c : ℝ} (hc : 0 < c)
    (p : Fin n → ℕ) (hp : ∀ i,(p i).Prime)
    (hmin : ∀ i,c*(rho^(m-i.val))⁻¹ ≤ primePrefixCoord p i) :
    (∑ i : Fin n,(p i:ℝ)⁻¹) ≤ (1-rho)⁻¹/c := by
  have hpoint (i : Fin n) : (p i:ℝ)⁻¹ ≤ rho^(m-i.val)/c := by
    have hp1 : (1:ℝ) ≤ p i := by exact_mod_cast (hp i).one_le
    have hcoord : primePrefixCoord p i ≤ p i :=
      (Real.log_le_self (Real.log_nonneg hp1)).trans (Real.log_le_self (Nat.cast_nonneg _))
    have hlarge := (hmin i).trans hcoord
    have hh := inv_anti₀ (mul_pos hc (inv_pos.mpr (pow_pos rho_pos _))) hlarge
    simpa only [mul_inv_rev,inv_inv,div_eq_mul_inv,mul_comm] using hh
  calc
    _ ≤ ∑ i : Fin n,rho^(m-i.val)/c := Finset.sum_le_sum (fun i _ => hpoint i)
    _ = (∑ i : Fin n,rho^(m-i.val))/c := (Finset.sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right (finite_reverse_geometric_sum hn) hc.le

lemma prime_factor_ratio_exp {p : ℕ} (hp : p.Prime) :
    (p:ℝ)/(p-1) ≤ Real.exp (2/(p:ℝ)) := by
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0:ℝ) < p := by linarith only [hp2]
  have hp1 : (0:ℝ) < p-1 := by linarith only [hp2]
  have hfrac : 1/(p-1) ≤ 2/(p:ℝ) := by
    apply (div_le_div_iff₀ hp1 hp0).mpr
    linarith only [hp2]
  have he : (p:ℝ)/(p-1)=1+1/(p-1) := by field_simp <;> ring
  rw [he]
  have hh := Real.add_one_le_exp (2/(p:ℝ))
  linarith only [hfrac,hh]

theorem finite_candidate_ratio_bound {n m : ℕ} (hn : n ≤ m) {c : ℝ} (hc : 0 < c)
    (p : Fin n → ℕ) (hp : ∀ i,(p i).Prime) (horder : StrictAnti p)
    (hmin : ∀ i,c*(rho^(m-i.val))⁻¹ ≤ primePrefixCoord p i)
    {q : ℕ} (hq : q.Prime) (hqp : ∀ i,p i < q) :
    ((q*(∏ i,p i):ℕ):ℝ)/(q*(∏ i,p i)).totient ≤
      Real.exp (1+2*((1-rho)⁻¹/c)) := by
  have hr := finite_geometric_prime_reciprocals hn hc p hp hmin
  have hq2 : (2:ℝ) ≤ q := by exact_mod_cast hq.two_le
  have hqinv : (q:ℝ)⁻¹ ≤ 1/2 := by
    simpa only [one_div] using inv_anti₀ (by norm_num : (0:ℝ)<2) hq2
  have hratio : ((q*(∏ i,p i):ℕ):ℝ)/(q*(∏ i,p i)).totient =
      (q:ℝ)/(q-1)*(∏ i : Fin n,(p i:ℝ)/(p i-1)) := by
    rw [candidate_prime_extension_totient hp hq hqp,ppt_totient_primeProduct p hp horder.injective]
    simp only [Nat.cast_mul,Nat.cast_prod,shiftedProduct,Nat.cast_sub (hq.one_le),Nat.cast_one]
    have he : (∏ i : Fin n,((p i-1:ℕ):ℝ)) = ∏ i : Fin n,((p i:ℝ)-1) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [Nat.cast_sub (hp i).one_le,Nat.cast_one]
    rw [he]
    rw [Finset.prod_div_distrib]
    exact mul_div_mul_comm _ _ _ _
  rw [hratio]
  have htail : (∏ i : Fin n,(p i:ℝ)/(p i-1)) ≤
      Real.exp (2*∑ i : Fin n,(p i:ℝ)⁻¹) := by
    calc
      _ ≤ ∏ i : Fin n,Real.exp (2/(p i:ℝ)) := by
        apply Finset.prod_le_prod
        · intro i _
          have hh : (1:ℝ) < p i := by exact_mod_cast (hp i).one_lt
          exact div_nonneg (Nat.cast_nonneg _) (by linarith only [hh])
        · intro i _
          exact prime_factor_ratio_exp (hp i)
      _ = _ := by rw [←Real.exp_sum,Finset.mul_sum]; congr 1
  calc
    _ ≤ Real.exp (2/(q:ℝ))*Real.exp (2*∑ i : Fin n,(p i:ℝ)⁻¹) :=
      mul_le_mul (prime_factor_ratio_exp hq) htail
        (Finset.prod_nonneg (fun i _ => div_nonneg (Nat.cast_nonneg _)
          (sub_nonneg.mpr (by exact_mod_cast (hp i).one_le)))) (Real.exp_pos _).le
    _ = Real.exp (2*((q:ℝ)⁻¹+∑ i : Fin n,(p i:ℝ)⁻¹)) := by
      rw [←Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hr,hqinv])

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

theorem raw_candidate_ratio_bound {c : ℝ} (hc : 0 < c) (d : ℕ) (hd : 0 < d) :
    ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,∀ b ∈ rawCandidates x c d H,
      (b:ℝ)/b.totient ≤ Real.exp (1+2*((1-rho)⁻¹/(c/2))) := by
  filter_upwards [raw_candidate_prime_data hc d hd] with H hH
  filter_upwards [hH] with x hx
  intro b hb
  obtain ⟨p,q,rfl,hp,ho,hr,_,_,hq,hqp,_⟩ := hx b hb
  exact finite_candidate_ratio_bound (Nat.sub_le _ _) (half_pos hc) p hp ho
    hr.2.1 hq hqp

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

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalCandidateArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arithmetic properties of the candidates retained by the local construction. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma local_normal_candidate_pos {x c : ℝ} {d L H b : ℕ}
    (hb : b∈localNormalCandidates x c d L H) : 0<b := by
  obtain ⟨p,q,he,hp,_hq,hnormal,_htail⟩ := local_normal_candidate_representation hb
  rw [he]
  apply Nat.mul_pos hnormal.1.pos
  exact Finset.prod_pos (fun i _ => (local_regular_normality hp i i le_rfl).1.pos)

theorem local_normal_candidate_arithmetic {c : ℝ} (hc : 0 < c)
    (d : ℕ) (hd : 0<d) (L : ℕ) :
    ∃ K : ℝ,0<K ∧ ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∀ b∈localNormalCandidates x c d L H,
        0<b ∧ ((d*b.totient:ℕ):ℝ)≤x ∧ (b:ℝ)/b.totient≤K := by
  refine ⟨Real.exp (1+2*((1-rho)⁻¹/(c/2))),Real.exp_pos _,?_⟩
  filter_upwards [local_normal_candidate_normality_and_value hc d hd L,
    raw_candidate_ratio_bound hc d hd] with H hvalue hratio
  filter_upwards [hvalue,hratio] with x hvalue hratio
  intro b hb
  exact ⟨local_normal_candidate_pos hb,(hvalue b hb).1,
    hratio b (local_regular_candidates_subset (local_normal_candidates_subset hb))⟩

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalFullCandidateScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert a positive fixed-prefix family into the natural counting scale.
These finite-family bridges will be applied after the regular residual
comparison estimate has been proved. -/
noncomputable section
open scoped Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

/-- The fixed-prefix normalization differs from the natural scale by a positive
constant, and every retained candidate has the exact full-fiber property. -/
theorem full_fiber_scale_of_local_count_oai {c δ : ℝ} (hc : 0 < c) (hδ : 0<δ)
    (d : ℕ) (hd : 0<d) (L : ℕ)
    (hcount : ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      (δ/(16*d))*(x/Real.log x*G x (m x-H)) ≤
        ((localFullCandidates x c d L H).card:ℝ)) :
    ∃ a K : ℝ,0<a ∧ 0<K ∧ ∀ᶠ x : ℝ in atTop,
      0<x ∧ ∃ S : Finset ℕ,a*(x/Real.log x)*G x (m x) ≤ (S.card:ℝ) ∧
        ∀ b∈S,0<b ∧ ((d*b.totient:ℕ):ℝ)≤x ∧
          FullFiber d b ∧ (b:ℝ)/b.totient≤K := by
  obtain ⟨K,hK,harith⟩ := local_normal_candidate_arithmetic hc d hd L
  obtain ⟨H,hcount,harith⟩ := (hcount.and harith).exists
  obtain ⟨a,ha,hprefix⟩ := fixed_prefix_volume_lower H
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  refine ⟨δ/(16*d)*a,K,by positivity,hK,?_⟩
  filter_upwards [hcount,harith,hprefix,eventually_gt_atTop (1:ℝ)]
    with x hcount harith hprefix hx
  refine ⟨zero_lt_one.trans hx,localFullCandidates x c d L H,?_,?_⟩
  · have hscale : 0≤x/Real.log x :=
      div_nonneg (zero_lt_one.trans hx).le (Real.log_pos hx).le
    have hh := mul_le_mul_of_nonneg_left hprefix
      (mul_nonneg (by positivity : 0≤δ/(16*d)) hscale)
    apply le_trans _ hcount
    first | (convert hh using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (hh.trans (le_of_eq (by ring)))
  · intro b hb
    obtain ⟨hb,hfull⟩ := Finset.mem_filter.mp hb
    obtain ⟨hpos,hvalue,hratio⟩ := harith b hb
    exact ⟨hpos,hvalue,hfull,hratio⟩

end TotientAsymptotic

end

end OAI
end

theorem solution : type_of% @OAI.TotientAsymptotic.full_fiber_scale_of_local_count_oai := @OAI.TotientAsymptotic.full_fiber_scale_of_local_count_oai
