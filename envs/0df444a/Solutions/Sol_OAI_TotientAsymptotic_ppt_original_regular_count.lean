-- Prove2me | solution 1 for OAI.TotientAsymptotic.ppt_original_regular_count
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:37:10.912057+00:00
-- url     : https://prove2.me/submissions/3a95d2fc-625e-4a16-ac49-fbc1720886d9

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
import Theorems.Thm_OAI_TotientAsymptotic_ford_raw_count
import Theorems.Thm_OAI_TotientAsymptotic_ford_raw_count_one
import Theorems.Thm_OAI_TotientAsymptotic_ppt_regular_head_witness

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

lemma B_tendsto : Tendsto B atTop atTop :=
  Real.tendsto_log_atTop.comp Real.tendsto_log_atTop

lemma m_tendsto : Tendsto m atTop atTop :=
  tendsto_nat_floor_atTop.comp (psi_tendsto.comp B_tendsto)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CofactorMass
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reciprocal totient majorants, including repeated primes in the cofactor. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma totient_prime_product_lower {ι : Type*} (I : Finset ι) (p : ι → ℕ)
    (a : ℕ) (hp : ∀ i ∈ I, (p i).Prime) :
    a.totient*(∏ i ∈ I, (p i-1)) ≤ (a*∏ i ∈ I, p i).totient := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    have hrec := ih (fun j hj => hp j (Finset.mem_insert_of_mem hj))
    have hprime := hp i (Finset.mem_insert_self _ _)
    calc
      _ = (a.totient*(∏ j ∈ I, (p j-1)))*(p i-1) := by ring
      _ ≤ (a*∏ j ∈ I, p j).totient*(p i-1) := Nat.mul_le_mul_right _ hrec
      _ = (a*∏ j ∈ I, p j).totient*(p i).totient := by rw [Nat.totient_prime hprime]
      _ ≤ ((a*∏ j ∈ I, p j)*p i).totient := Nat.totient_super_multiplicative _ _
      _ = _ := by congr 1; ring

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

lemma omegaIn_eq_zero_of_largest_le {n : ℕ} {U T : ℝ}
    (hn : (largestPrimeFactor n : ℝ) ≤ U) : omegaIn n U T = 0 := by
  unfold omegaIn
  have he : n.primeFactorsList.filter
      (fun p : ℕ => decide (U < (p : ℝ) ∧ (p : ℝ) ≤ T)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro p hp
    simp only [Bool.not_eq_true, decide_eq_false_iff_not]
    intro h
    have hle : (p : ℝ) ≤ largestPrimeFactor n := by exact_mod_cast primeFactor_le_largest hp
    linarith [h.1]
  rw [he]
  rfl

lemma normality_interval_bounds {S U T ε : ℝ} {p : ℕ}
    (hp : IsNormalPrime S p) (hSU : S ≤ U) (hUT : U < T)
    (hTp : T ≤ (p-1 : ℕ)) (hε : Real.sqrt (B S * B T) ≤ ε) :
    B T-B U-ε ≤ (omegaIn (p-1) U T : ℝ) ∧
      (omegaIn (p-1) U T : ℝ) ≤ B T-B U+ε := by
  have h := abs_lt.mp (hp.2.2 U T hSU hUT hTp)
  constructor <;> linarith

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SuffixSize
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Deterministic size estimates for the complete remainder of a basic witness. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma m_le_log_B : ∀ᶠ x : ℝ in atTop, (m x : ℝ) ≤ Real.log (B x)/lam := by
  filter_upwards [B_tendsto.eventually (eventually_gt_atTop (Real.exp 1 : ℝ)),
    (psi_tendsto.comp B_tendsto).eventually (eventually_ge_atTop (0 : ℝ))] with x hB hpsi
  have hlog : 1 < Real.log (B x) := by rwa [Real.lt_log_iff_exp_lt ((Real.exp_pos 1).trans hB)]
  have hfloor := Nat.floor_le hpsi
  change (m x : ℝ) ≤ psi (B x) at hfloor
  exact hfloor.trans (by
    unfold psi
    exact div_le_div_of_nonneg_right (sub_le_self _ (Real.log_nonneg hlog.le)) lam_pos.le)

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalPrimeBands
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Largest-factor bands derived from normality, including the small-prime case. -/

noncomputable section

namespace TotientAsymptotic

lemma largestPrimeFactor_le_self {n : ℕ} (hn : 1 ≤ n) : largestPrimeFactor n ≤ n := by
  apply largestPrimeFactor_le_of_prime_divisors hn
  intro p _ hp hn0
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hp

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeFactorBands
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact arithmetic of the prime-factor bands in Ford's collision argument. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma partBelow_pos (n : ℕ) (V : ℝ) : 0 < partBelow n V := by
  apply List.prod_pos
  intro p hp
  exact (Nat.prime_of_mem_primeFactorsList (List.mem_filter.mp hp).1).pos

lemma partBetween_pos (n : ℕ) (U V : ℝ) : 0 < partBetween n U V := by
  apply List.prod_pos
  intro p hp
  exact (Nat.prime_of_mem_primeFactorsList (List.mem_filter.mp hp).1).pos

lemma partBelow_factors (n : ℕ) (V : ℝ) :
    (n.primeFactorsList.filter (fun p : ℕ => (p:ℝ) ≤ V)).Perm (partBelow n V).primeFactorsList := by
  apply Nat.primeFactorsList_unique rfl
  intro p hp
  exact Nat.prime_of_mem_primeFactorsList (List.mem_filter.mp hp).1

lemma partBetween_factors (n : ℕ) (U V : ℝ) :
    (n.primeFactorsList.filter (fun p : ℕ => U < (p:ℝ) ∧ (p:ℝ) ≤ V)).Perm
      (partBetween n U V).primeFactorsList := by
  apply Nat.primeFactorsList_unique rfl
  intro p hp
  exact Nat.prime_of_mem_primeFactorsList (List.mem_filter.mp hp).1

lemma partBetween_omega (n : ℕ) (U V : ℝ) :
    (partBetween n U V).primeFactorsList.length=omegaIn n U V :=
  (partBetween_factors n U V).length_eq.symm

lemma partBelow_band_split (n : ℕ) {U V : ℝ} (hUV : U ≤ V) :
    partBelow n U*partBetween n U V=partBelow n V := by
  have hh := List.prod_map_filter_mul_prod_map_filter_not
    (fun p : ℕ => (p:ℝ) ≤ U) id
    (n.primeFactorsList.filter (fun p : ℕ => (p:ℝ) ≤ V))
  have hleft : (n.primeFactorsList.filter (fun p : ℕ => (p:ℝ) ≤ V)).filter
      (fun p : ℕ => (p:ℝ) ≤ U)=n.primeFactorsList.filter (fun p : ℕ => (p:ℝ) ≤ U) := by
    simp only [List.filter_filter]
    congr 1
    funext p
    by_cases h : (p:ℝ) ≤ U
    · simp [h,h.trans hUV]
    · simp [h]
  have hright : (n.primeFactorsList.filter (fun p : ℕ => (p:ℝ) ≤ V)).filter
      (fun p : ℕ => ¬(p:ℝ) ≤ U)=
      n.primeFactorsList.filter (fun p : ℕ => U < (p:ℝ) ∧ (p:ℝ) ≤ V) := by
    simp only [List.filter_filter]
    congr 1
    funext p
    simp [not_le]
  simpa only [List.map_id,hleft,hright,partBelow,partBetween] using hh

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeBandProducts
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Multiplicative and nested-truncation identities for actual collision bands. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma partBelow_all_of_largest_le {n : ℕ} {V : ℝ} (hn : n ≠ 0)
    (hV : (largestPrimeFactor n:ℝ) ≤ V) : partBelow n V=n := by
  have hall : n.primeFactorsList.filter (fun p : ℕ => (p:ℝ) ≤ V)=n.primeFactorsList := by
    apply List.filter_eq_self.mpr
    intro p hp
    exact decide_eq_true ((show (p:ℝ) ≤ largestPrimeFactor n by
      exact_mod_cast primeFactor_le_largest hp).trans hV)
  simp only [partBelow,hall,Nat.prod_primeFactorsList hn]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeReciprocalBound
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The short reciprocal-prime bound needed for the unrestricted suffix. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma shifted_prime_reciprocal_le_log {p : ℕ} (hp : p.Prime) :
    ((p-1 : ℕ) : ℝ)⁻¹ ≤ 2*Real.log ((p : ℝ)/(p-1)) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hs : (0 : ℝ) < p-1 := by linarith
  have hc : ((p-1 : ℕ) : ℝ)=(p : ℝ)-1 := by
    rw [Nat.cast_sub hp.one_lt.le,Nat.cast_one]
  rw [hc]
  have ht0 : (0 : ℝ) < (p : ℝ)/(p-1) := div_pos hp0 hs
  have ht1 : (1 : ℝ) ≤ (p : ℝ)/(p-1) := (le_div_iff₀ hs).mpr (by linarith)
  have ht2 : (p : ℝ)/(p-1) ≤ 2 := (div_le_iff₀ hs).mpr (by linarith)
  have hlog := Real.one_sub_inv_le_log_of_pos ht0
  have hnon := Real.log_nonneg ht1
  have he : ((p-1 : ℝ))⁻¹=((p : ℝ)/(p-1))*(1-((p : ℝ)/(p-1))⁻¹) := by
    field_simp
    ring
  rw [he]
  exact (mul_le_mul_of_nonneg_left hlog ht0.le).trans
    (mul_le_mul_of_nonneg_right ht2 hnon)

lemma prime_reciprocal_mass_log_product (N : ℕ) :
    (∑ p ∈ Nat.primesLE N, ((p-1 : ℕ) : ℝ)⁻¹) ≤ 2*Real.log (primeEulerProduct N) := by
  have he : (Nat.primesLE N)=(Finset.Icc 2 N).filter Nat.Prime := by
    ext p
    simp only [Nat.mem_primesLE,Finset.mem_filter,Finset.mem_Icc]
    exact ⟨fun h => ⟨⟨h.2.two_le,h.1⟩,h.2⟩,fun h => ⟨h.1.2,h.2⟩⟩
  rw [primeEulerProduct,Real.log_prod (by
    intro p hp
    have hh := (Finset.mem_filter.mp hp).2.two_le
    have hh' : (2 : ℝ) ≤ p := by exact_mod_cast hh
    exact (div_pos (by linarith) (by linarith)).ne'),Finset.mul_sum,← he]
  exact Finset.sum_le_sum (fun p hp => shifted_prime_reciprocal_le_log (Nat.mem_primesLE.mp hp).2)

theorem prime_reciprocal_mass_bound (hmertens : MertensProductInput) :
    ∃ D : ℝ, 0 < D ∧ ∀ N : ℕ, 2 ≤ N → 0 ≤ B N →
      (∑ p ∈ Nat.primesLE N, ((p-1 : ℕ) : ℝ)⁻¹) ≤ D*(1+B N) := by
  obtain ⟨C,hC,hprod⟩ := hmertens
  refine ⟨2*(1+|Real.log C|),by positivity,?_⟩
  intro N hN hB
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hpos : 0 < primeEulerProduct N := by
    apply Finset.prod_pos
    intro p hp
    have hh : (1 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
    exact div_pos (by linarith) (by linarith)
  have hh := Real.log_le_log hpos (hprod N hN)
  rw [Real.log_mul hC.ne' hlog.ne'] at hh
  calc
    _ ≤ 2*Real.log (primeEulerProduct N) := prime_reciprocal_mass_log_product N
    _ ≤ 2*(Real.log C+B N) := mul_le_mul_of_nonneg_left hh (by norm_num)
    _ ≤ _ := by nlinarith [le_abs_self (Real.log C),abs_nonneg (Real.log C)]

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionSlack
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative strict slack in the published comparison exponent. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma comparison_log_power_saving {y E σ : ℝ} (hy : 1 ≤ Real.log y)
    (hE : E ≤ -1-σ) :
    (Real.log y)^E ≤ (Real.log y)⁻¹*Real.exp (-σ*B y) := by
  calc
    _ ≤ (Real.log y)^(-1-σ) := Real.rpow_le_rpow_of_exponent_le hy hE
    _ = (Real.log y)⁻¹*Real.exp (-σ*B y) := by
      rw [Real.rpow_def_of_pos (lt_of_lt_of_le zero_lt_one hy)]
      change Real.exp (B y*(-1-σ)) = _
      rw [mul_sub, mul_neg_one, Real.exp_sub, Real.exp_neg]
      rw [show Real.exp (B y) = Real.log y from
        Real.exp_log (lt_of_lt_of_le zero_lt_one hy)]
      rw [neg_mul, Real.exp_neg]
      simp [div_eq_mul_inv, mul_comm]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionGrid
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite interval choices for the paired normalized largest factors. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma collisionGridFamilies_card (δ : ℝ) (b : ℕ) :
    (collisionGridFamilies δ b).card = (⌊1/δ⌋₊+1)^b := by
  simp [collisionGridFamilies]

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalBandAllocation
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normality gives the factor-count caps required by the collision allocation bound. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma omegaIn_upper_truncate (n : ℕ) (U V : ℝ) :
    omegaIn n U V=omegaIn n U (min V n) := by
  unfold omegaIn
  congr 1
  apply List.filter_congr
  intro p hp
  have hpn : (p:ℝ) ≤ n := by exact_mod_cast Nat.le_of_mem_primeFactorsList hp
  simp only [le_min_iff,hpn,and_true]

lemma normality_band_upper {S U V : ℝ} {p : ℕ} (hp : IsNormalPrime S p)
    (hS : 1 < S) (hBS : 0 ≤ B S) (hSU : S ≤ U) (hUV : U < V) :
    (omegaIn (p-1) U V:ℝ) ≤ B V-B U+Real.sqrt (B S*B V) := by
  have hU1 : 1 < U := hS.trans_le hSU
  have hV1 : 1 < V := hU1.trans hUV
  have hBUV : B U ≤ B V :=
    Real.log_le_log (Real.log_pos hU1) (Real.log_le_log (by linarith) hUV.le)
  by_cases hn : (p-1:ℕ) ≤ U
  · have hp1 : 1 ≤ p-1 := by have := hp.1.two_le; omega
    have hlarge : (largestPrimeFactor (p-1):ℝ) ≤ U :=
      (show (largestPrimeFactor (p-1):ℝ) ≤ (p-1:ℕ) by
        exact_mod_cast largestPrimeFactor_le_self hp1).trans hn
    rw [omegaIn_eq_zero_of_largest_le hlarge,Nat.cast_zero]
    linarith [Real.sqrt_nonneg (B S*B V)]
  · have hn : U < (p-1:ℕ) := lt_of_not_ge hn
    let W := min V (p-1:ℕ)
    have hUW : U < W := lt_min hUV hn
    have hBW : B W ≤ B V := Real.log_le_log (Real.log_pos (hU1.trans hUW))
      (Real.log_le_log (by linarith) (min_le_left V (p-1:ℕ)))
    have hroot : Real.sqrt (B S*B W) ≤ Real.sqrt (B S*B V) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hBW hBS)
    have hb := (normality_interval_bounds hp hSU hUW (min_le_right V (p-1:ℕ)) hroot).2
    rw [omegaIn_upper_truncate]
    change (omegaIn (p-1) U W:ℝ) ≤ _
    linarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordBandGeometry
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual cutoff geometry for the application of Ford's interval sieve. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma ford_cutoff_antitone {b D r : ℕ} {y S : ℝ} {Y U : ℕ → ℝ}
    (h : FordComparisonParameters b y S D r Y U) {j l : ℕ} (hjl : j ≤ l) (hl : l ≤ b) :
    Y l ≤ Y j := by
  have hstep (a : ℕ) (ha : a < b) : Y (a+1) ≤ Y a :=
    ((h.2.2.2.2.1 a (Finset.mem_range.mpr ha)).1.trans (h.2.2.2.2.1 a (Finset.mem_range.mpr ha)).2).le
  induction l, hjl using Nat.le_induction with
  | base => rfl
  | succ l hjl ih => exact (hstep l (by omega)).trans (ih (by omega))

lemma ford_cutoff_ge_S {b D r : ℕ} {y S : ℝ} {Y U : ℕ → ℝ}
    (h : FordComparisonParameters b y S D r Y U) {j : ℕ} (hj : j ≤ b) : S ≤ Y j :=
  h.2.2.2.1.trans (ford_cutoff_antitone h hj le_rfl)

lemma ford_cutoff_le_y {b D r : ℕ} {y S : ℝ} {Y U : ℕ → ℝ}
    (h : FordComparisonParameters b y S D r Y U) {j : ℕ} (hj : j ≤ b) : Y j ≤ y := by
  simpa only [h.2.1] using ford_cutoff_antitone h (Nat.zero_le j) hj

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordBandSupports
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Support, equality and squarefreeness of the actual bands of a Ford tuple. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma ford_scale_bounds {b D r : ℕ} {y S : ℝ} {Y U : ℕ → ℝ}
    (h : FordComparisonParameters b y S D r Y U) : 1 < S ∧ 1 ≤ B S := by
  have hS := h.2.2.1
  have hS1 : 1 < S := (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)).trans_le hS
  have hlog := Real.log_le_log (Real.exp_pos (Real.exp 1)) hS
  rw [Real.log_exp] at hlog
  have hB := Real.log_le_log (Real.exp_pos 1) hlog
  rw [Real.log_exp] at hB
  exact ⟨hS1,hB⟩

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalTerminalFactors
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A normal shifted prime contributes few factors below the terminal cutoff. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma partBelow_omega (n : ℕ) (V : ℝ) :
    (partBelow n V).primeFactorsList.length=omegaIn n 1 V := by
  rw [← (partBelow_factors n V).length_eq]
  unfold omegaIn
  congr 1
  apply List.filter_congr
  intro p hp
  have hp1 : (1:ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactorsList hp).one_lt
  simp only [hp1,true_and]

lemma normal_terminal_omega {S V : ℝ} {p : ℕ} (hp : IsNormalPrime S p)
    (hS : 1 < S) (hBS : 0 ≤ B S) (hSV : S ≤ V) :
    ((partBelow (p-1) V).primeFactorsList.length:ℝ) ≤ 4*B V := by
  have hBV : B S ≤ B V := Real.log_le_log (Real.log_pos hS)
    (Real.log_le_log (by linarith) hSV)
  have hB0 : 0 ≤ B V := hBS.trans hBV
  by_cases he : S=V
  · rw [partBelow_omega,← he]
    linarith [hp.2.1]
  · have hlt : S < V := lt_of_le_of_ne hSV he
    have hsplit := congrArg (fun n : ℕ => n.primeFactorsList.length)
      (partBelow_band_split (p-1) hSV)
    rw [omega_count_mul (partBelow_pos (p-1) S).ne' (partBetween_pos (p-1) S V).ne',
      partBelow_omega,partBetween_omega] at hsplit
    have hsR : ((partBelow (p-1) V).primeFactorsList.length:ℝ)=
        (omegaIn (p-1) 1 S:ℝ)+(omegaIn (p-1) S V:ℝ) := by exact_mod_cast hsplit.symm
    have hband := normality_band_upper hp hS hBS le_rfl hlt
    have hroot : Real.sqrt (B S*B V) ≤ B V := Real.sqrt_le_iff.mpr
      ⟨hB0,by nlinarith [mul_le_mul_of_nonneg_right hBV hB0]⟩
    rw [hsR]
    linarith [hp.2.1]

lemma normal_terminal_product_omega {k : ℕ} (p : Fin k → ℕ) {S V : ℝ}
    (hp : ∀ j,IsNormalPrime S (p j)) (hS : 1 < S) (hBS : 0 ≤ B S) (hSV : S ≤ V) :
    ((∏ j,partBelow (p j-1) V).primeFactorsList.length:ℝ) ≤ 4*(k:ℝ)*B V := by
  rw [omega_count_prod _ _ (fun j _ => (partBelow_pos (p j-1) V).ne'),Nat.cast_sum]
  calc
    _ ≤ ∑ _j : Fin k,(4*B V) :=
      Finset.sum_le_sum (fun j _ => normal_terminal_omega (hp j) hS hBS hSV)
    _ = _ := by simp <;> ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordTerminalMass
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The terminal mass bounds for the actual Ford state families. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma ford_cutoff_two_le {b D r : ℕ} {y S : ℝ} {Y U : ℕ → ℝ}
    (hp : FordComparisonParameters b y S D r Y U) {k : ℕ} (hk : k ≤ b) : 2 ≤ Y k := by
  have hs : Real.exp (Real.exp 1) ≤ S := hp.2.2.1
  have h₁ := Real.add_one_le_exp (1:ℝ)
  have h₂ := Real.add_one_le_exp (Real.exp 1)
  linarith [ford_cutoff_ge_S hp hk]

lemma ford_cutoff_B_one_le {b D r : ℕ} {y S : ℝ} {Y U : ℕ → ℝ}
    (hp : FordComparisonParameters b y S D r Y U) {k : ℕ} (hk : k ≤ b) : 1 ≤ B (Y k) := by
  have hS := ford_scale_bounds hp
  exact hS.2.trans (Real.log_le_log (Real.log_pos hS.1)
    (Real.log_le_log (by linarith) (ford_cutoff_ge_S hp hk)))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordParameterBounds
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary quantitative consequences of Ford's separated cutoffs. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma sum_predecessor_diff {b : ℕ} (hb : 1 ≤ b) (v : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 2 b,(v (k-1)-v k))=v 1-v b := by
  induction b, hb using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ b+1)]
    simp only [Nat.add_sub_cancel]
    rw [ih]
    ring

lemma ford_band_count_le {b D r : ℕ} {y S : ℝ} {Y U : ℕ → ℝ}
    (hp : FordComparisonParameters b y S D r Y U) : (b:ℝ) ≤ B y := by
  have hb := hp.1
  have hBy := ford_cutoff_B_one_le hp (k:=0) (by omega)
  rw [hp.2.1] at hBy
  have hS := (ford_scale_bounds hp).2
  have hroot : 1 ≤ Real.sqrt (B S/B y)*B y := by
    have he : Real.sqrt (B S/B y)*B y=Real.sqrt (B S*B y) := by
      rw [Real.sqrt_div (by linarith : 0 ≤ B S),Real.sqrt_mul (by linarith : 0 ≤ B S)]
      have hsq := Real.sq_sqrt (by linarith : 0 ≤ B y)
      have hpos : Real.sqrt (B y) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
      field_simp
      rw [hsq]
    rw [he]
    exact Real.one_le_sqrt.mpr (by nlinarith)
  have hgap (k : ℕ) (hk : k ∈ Finset.Icc 2 b) : 1 ≤ B (Y (k-1))-B (Y k) := by
    have hh := hp.2.2.2.2.2.2.1 k hk
    have hh' := (mul_lt_mul_of_pos_right hh (by linarith : 0 < B y))
    have he : (B (Y (k-1))/B y-B (Y k)/B y)*B y=B (Y (k-1))-B (Y k) := by
      field_simp
    rw [he] at hh'
    nlinarith
  have hsum := Finset.sum_le_sum hgap
  have hcount : ((Finset.Icc 2 b).card:ℝ)=(b:ℝ)-1 := by
    simp only [Nat.card_Icc]
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have htotal : (b:ℝ)-1 ≤ B (Y 1)-B (Y b) := by
    simpa only [Finset.sum_const,nsmul_eq_mul,mul_one,hcount,sum_predecessor_diff hp.1 (fun j => B (Y j))]
      using hsum
  have hY : B (Y 1) ≤ B y := Real.log_le_log
    (Real.log_pos (by linarith [ford_cutoff_two_le hp hp.1]))
    (Real.log_le_log (by linarith [ford_cutoff_two_le hp hp.1]) (ford_cutoff_le_y hp hp.1))
  linarith [ford_cutoff_B_one_le hp (k:=b) le_rfl]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ComparisonThreshold
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed endpoint suffices for all quantitative band-sieve hypotheses. -/
noncomputable section
namespace TotientAsymptotic

lemma ford_comparison_threshold (R : ℝ) (hR : 0 < R) :
    ∃ y₀ : ℝ,1 < y₀ ∧ ∀ y : ℝ,y₀ ≤ y →
      Real.exp 2 ≤ y ∧ 1 ≤ B y ∧
      ∀ S : ℝ,1 ≤ B S → R ≤ Real.sqrt (B S*B y) := by
  let y₀ := Real.exp (Real.exp (R^2+2))
  have he : 2 ≤ Real.exp (R^2+2) := by nlinarith [Real.add_one_le_exp (R^2+2),sq_nonneg R]
  have hbase : Real.exp 2 ≤ y₀ := Real.exp_le_exp.mpr he
  have hy₀ : 1 < y₀ := (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<2)).trans_le hbase
  refine ⟨y₀,hy₀,?_⟩
  intro y hy
  have hB : R^2+2 ≤ B y := by
    have hh := Real.log_le_log (Real.log_pos hy₀) (Real.log_le_log (by linarith) hy)
    simpa only [y₀,B,Real.log_exp] using hh
  refine ⟨hbase.trans hy,by nlinarith [sq_nonneg R],?_⟩
  intro S hS
  have hBy : 0 ≤ B y := by nlinarith [sq_nonneg R]
  apply (Real.le_sqrt hR.le (mul_nonneg (by linarith) hBy)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hS (show 0 ≤ B y by nlinarith [sq_nonneg R])]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordBandExponent
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact telescoping of the band exponents into Ford's coefficients. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma fordBandWeight_succ (k : ℕ) :
    fordBandWeight (k+1)-fordBandWeight k-2=a k := by
  simp only [fordBandWeight,a,Nat.cast_add,Nat.cast_one]
  ring

lemma fordBandWeight_nonneg (k : ℕ) : 0 ≤ fordBandWeight k := by
  by_cases hk : k=0
  · simp [fordBandWeight,hk]
  · have hk1 : (1:ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    exact add_nonneg (mul_nonneg (by positivity) (Real.log_nonneg hk1)) (by positivity)

lemma ford_band_exponent_telescope {b : ℕ} (hb : 1 ≤ b) (v : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 2 b,fordBandWeight k*(v (k-1)-v k))-v 1-
      2*(∑ j ∈ Finset.Icc 1 (b-1),v j)=
    (∑ j ∈ Finset.Icc 1 (b-1),a j*v j)-fordBandWeight b*v b := by
  induction b, hb using Nat.le_induction with
  | base => simp [fordBandWeight]
  | succ b hb ih =>
    have hv : (∑ j ∈ Finset.Icc 1 b,v j)=
        (∑ j ∈ Finset.Icc 1 (b-1),v j)+v b := by
      conv_lhs => rw [← Nat.sub_add_cancel hb]
      rw [Finset.sum_Icc_succ_top (by omega)]
      simp only [Nat.sub_add_cancel hb]
    have ha : (∑ j ∈ Finset.Icc 1 b,a j*v j)=
        (∑ j ∈ Finset.Icc 1 (b-1),a j*v j)+a b*v b := by
      conv_lhs => rw [← Nat.sub_add_cancel hb]
      rw [Finset.sum_Icc_succ_top (by omega)]
      simp only [Nat.sub_add_cancel hb]
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ b+1)]
    simp only [Nat.add_sub_cancel]
    rw [hv,ha]
    have hw := congrArg (fun z : ℝ => z*v b) (fordBandWeight_succ b)
    nlinarith

lemma ford_band_exponent_identity {b : ℕ} (hb : 1 ≤ b)
    (y S : ℝ) (Y U : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 2 b,fordBandCap k y S Y*(Real.log k+1))-
      B (Y 1)-2*(∑ j ∈ Finset.Icc 1 (b-1),B (U j))=
    (∑ j ∈ Finset.Icc 1 (b-1),a j*B (Y j))+
      2*(∑ j ∈ Finset.Icc 1 (b-1),(B (Y j)-B (U j)))+
      Real.sqrt (B S*B y)*(∑ k ∈ Finset.Icc 2 b,fordBandWeight k)-
      fordBandWeight b*B (Y b) := by
  have hsplit : (∑ k ∈ Finset.Icc 2 b,fordBandCap k y S Y*(Real.log k+1))=
      (∑ k ∈ Finset.Icc 2 b,fordBandWeight k*(B (Y (k-1))-B (Y k)))+
      Real.sqrt (B S*B y)*(∑ k ∈ Finset.Icc 2 b,fordBandWeight k) := by
    rw [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    dsimp [fordBandCap,fordBandWeight]
    ring
  rw [hsplit,Finset.sum_sub_distrib]
  have hh := ford_band_exponent_telescope hb (fun k => B (Y k))
  linarith

lemma ford_comparison_error_mul {b : ℕ} {y S : ℝ} (hy : 0 < B y) (hS : 0 ≤ B S)
    (Y U : ℕ → ℝ) :
    comparisonError b y S Y U*B y=
      2*(∑ j ∈ Finset.Icc 1 (b-1),(B (Y j)-B (U j)))+
      Real.sqrt (B S*B y)*(∑ k ∈ Finset.Icc 2 b,fordBandWeight k) := by
  have hs : Real.sqrt (B S/B y)*B y=Real.sqrt (B S*B y) := by
    rw [Real.sqrt_div hS,Real.sqrt_mul hS]
    have hyroot : Real.sqrt (B y) ≠ 0 := (Real.sqrt_pos.2 hy).ne'
    have hsq := Real.sq_sqrt hy.le
    field_simp
    rw [hsq]
  unfold comparisonError
  rw [add_mul,mul_assoc,Finset.sum_mul]
  have he : (∑ j ∈ Finset.Icc 1 (b-1),(B (Y j)/B y-B (U j)/B y)*B y)=
      ∑ j ∈ Finset.Icc 1 (b-1),(B (Y j)-B (U j)) := by
    apply Finset.sum_congr rfl
    intro j _
    field_simp
  rw [he]
  change _+Real.sqrt (B S/B y)*(∑ k ∈ Finset.Icc 2 b,fordBandWeight k)*B y=_
  rw [mul_right_comm _ _ (B y),hs]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordLogProduct
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Product-to-exponent identities for the logarithmic band costs. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma sum_predecessor_values {b : ℕ} (hb : 1 ≤ b) (v : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 2 b,v (k-1))=∑ j ∈ Finset.Icc 1 (b-1),v j := by
  induction b, hb using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ b+1)]
    simp only [Nat.add_sub_cancel]
    rw [ih]
    conv_rhs => rw [← Nat.sub_add_cancel hb]
    rw [Finset.sum_Icc_succ_top (by omega)]
    simp only [Nat.sub_add_cancel hb]

lemma exp_two_B {U : ℝ} (hU : 1 < U) : Real.exp (2*B U)=(Real.log U)^2 := by
  simpa only [Nat.cast_ofNat,B,Real.exp_log (Real.log_pos hU)] using
    Real.exp_nat_mul (B U) 2

lemma ford_logarithmic_product {b : ℕ} (hb : 1 ≤ b)
    (y S : ℝ) (Y U : ℕ → ℝ) (hY : 1 < Y 1)
    (hU : ∀ j ∈ Finset.Icc 1 (b-1),1 < U j) :
    (Real.log (Y 1))⁻¹*
      (∏ k ∈ Finset.Icc 2 b,Real.exp (fordBandCap k y S Y*(Real.log k+1))/
        (Real.log (U (k-1)))^2)=
    Real.exp ((∑ k ∈ Finset.Icc 2 b,fordBandCap k y S Y*(Real.log k+1))-
      B (Y 1)-2*(∑ j ∈ Finset.Icc 1 (b-1),B (U j))) := by
  have he (k : ℕ) (hk : k ∈ Finset.Icc 2 b) :
      Real.exp (fordBandCap k y S Y*(Real.log k+1))/(Real.log (U (k-1)))^2=
      Real.exp (fordBandCap k y S Y*(Real.log k+1)-2*B (U (k-1))) := by
    rw [Real.exp_sub,exp_two_B (hU (k-1) (by obtain ⟨_,_⟩ := Finset.mem_Icc.mp hk; simp; omega))]
  rw [Finset.prod_congr rfl he,← Real.exp_sum]
  have hYexp : (Real.log (Y 1))⁻¹=Real.exp (-B (Y 1)) := by
    rw [Real.exp_neg,show Real.exp (B (Y 1))=Real.log (Y 1) by
      exact Real.exp_log (Real.log_pos hY)]
  rw [hYexp,← Real.exp_add,Finset.sum_sub_distrib,← Finset.mul_sum,
    sum_predecessor_values hb (fun j => B (U j))]
  congr 1
  ring

lemma ford_logarithmic_product_bound {b : ℕ} {y S : ℝ} (Y U : ℕ → ℝ)
    (hb : 1 ≤ b) (hy1 : 1 < y) (hy : 0 < B y) (hS : 0 ≤ B S) (hB : 0 ≤ B (Y b))
    (hY : 1 < Y 1) (hU : ∀ j ∈ Finset.Icc 1 (b-1),1 < U j) :
    (Real.log (Y 1))⁻¹*
      (∏ k ∈ Finset.Icc 2 b,Real.exp (fordBandCap k y S Y*(Real.log k+1))/
        (Real.log (U (k-1)))^2) ≤
    (Real.log y)^((∑ j ∈ Finset.Icc 1 (b-1),a j*(B (Y j)/B y))+
      comparisonError b y S Y U) := by
  have hlogy : 0 < Real.log y := Real.log_pos hy1
  rw [ford_logarithmic_product hb y S Y U hY hU,
    ford_band_exponent_identity hb y S Y U,Real.rpow_def_of_pos hlogy]
  apply Real.exp_le_exp.mpr
  have he : (∑ j ∈ Finset.Icc 1 (b-1),a j*(B (Y j)/B y))*B y=
      ∑ j ∈ Finset.Icc 1 (b-1),a j*B (Y j) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    field_simp
  have herr := ford_comparison_error_mul hy hS Y U (b:=b)
  have hn := mul_nonneg (fordBandWeight_nonneg b) hB
  change _ ≤ B y*((∑ j ∈ Finset.Icc 1 (b-1),a j*(B (Y j)/B y))+
    comparisonError b y S Y U)
  nlinarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordPolynomialBudget
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial costs of all bands fit in the published prefactor. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma ford_band_cost_split (C : ℝ) (k : ℕ) (y S : ℝ) (Y U : ℕ → ℝ) :
    fordBandCost C k y S Y U=
      (C*(k:ℝ)^2*(B y)^2)*
      (Real.exp (fordBandCap k y S Y*(Real.log k+1))/(Real.log (U (k-1)))^2) := by
  unfold fordBandCost
  ring

lemma ford_polynomial_budget {C A M B : ℝ} {b : ℕ}
    (hb : 1 ≤ b) (hB : 1 ≤ B) (hbB : (b:ℝ) ≤ B)
    (hC : 1 ≤ C) (_hA : 0 ≤ A) (hM : 0 ≤ M)
    (hAC : 216*A ≤ C) (hMC : M ≤ C) (hCb : 0 ≤ C) :
    (216*A)*M*B^5*(∏ k ∈ Finset.Icc 2 b,C*(k:ℝ)^2*B^2) ≤ (C*B)^(6*b) := by
  have hcount : (Finset.Icc 2 b).card=b-1 := by simp
  have hb0 : 0 ≤ B := by linarith
  have hprod : (∏ k ∈ Finset.Icc 2 b,C*(k:ℝ)^2*B^2) ≤ (C*B^4)^(b-1) := by
    calc
      _ ≤ ∏ _k ∈ Finset.Icc 2 b,C*B^4 := by
        apply Finset.prod_le_prod
        · intro k _; positivity
        · intro k hk
          have hkB : (k:ℝ) ≤ B := (Nat.cast_le.mpr (Finset.mem_Icc.mp hk).2).trans hbB
          have hh := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg k) hkB 2) hCb)
            (sq_nonneg B)
          convert hh using 1
          all_goals try with_reducible_and_instances rfl
          ring
      _ = _ := by simp only [Finset.prod_const,hcount]
  have hAM : (216*A)*M ≤ C^2 := by
    have hh := mul_le_mul hAC hMC hM hCb
    nlinarith
  have hpref := mul_le_mul_of_nonneg_right hAM (pow_nonneg hb0 5)
  have hall := mul_le_mul hpref hprod (Finset.prod_nonneg (fun k _ => by positivity)) (by positivity : 0 ≤ C^2*B^5)
  have he : C^2*B^5*(C*B^4)^(b-1)=C^(b+1)*B^(4*b+1) := by
    obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hb
    simp only [Nat.add_sub_cancel_left,mul_pow,pow_add,pow_mul]
    ring
  have hCbpow : C^(b+1) ≤ C^(6*b) := pow_le_pow_right₀ hC (by omega)
  have hBpow : B^(4*b+1) ≤ B^(6*b) := pow_le_pow_right₀ hB (by omega)
  calc
    _ ≤ C^2*B^5*(C*B^4)^(b-1) := hall
    _ = C^(b+1)*B^(4*b+1) := he
    _ ≤ C^(6*b)*B^(6*b) := mul_le_mul hCbpow hBpow (by positivity) (by positivity)
    _ = _ := (mul_pow C B (6*b)).symm

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordComparisonBudget
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The assembled counting bound has exactly the published Ford exponents. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma ford_comparison_budget {b D r : ℕ} {y S A M C K : ℝ} {Y U : ℕ → ℝ}
    (hp : FordComparisonParameters b y S D r Y U)
    (hy : 1 < y) (hA : 0 ≤ A) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hK : 1 ≤ K) (hAK : 216*A ≤ K) (hMK : M ≤ K) (hCK : C ≤ K) :
    ((216*A)*(y/(D*r:ℕ))*(B y)^5/(Real.log y)^2/Real.log (Y 1))*
      (∏ k ∈ Finset.Icc 2 b,fordBandCost C k y S Y U)*
      (M*(b+1:ℝ)^D.primeFactorsList.length*
        (Real.log (Y b))^(20*(b:ℝ)*Real.log b+1)) ≤
    fordComparisonBound K b y S D r Y U := by
  classical
  let P := ∏ k ∈ Finset.Icc 2 b,C*(k:ℝ)^2*(B y)^2
  let Q := ∏ k ∈ Finset.Icc 2 b,Real.exp (fordBandCap k y S Y*(Real.log k+1))/
    (Real.log (U (k-1)))^2
  let Z := (Real.log (Y b))^(20*(b:ℝ)*Real.log b+1)
  have hBy : 1 ≤ B y := by simpa only [hp.2.1] using ford_cutoff_B_one_le hp (k:=0) (by omega)
  have hy0 : 0 ≤ y := by linarith
  have hlog : 0 < Real.log y := Real.log_pos hy
  have hY : 1 < Y 1 := by linarith [ford_cutoff_two_le hp hp.1]
  have hU (j : ℕ) (hj : j ∈ Finset.Icc 1 (b-1)) : 1 < U j := by
    have hjb : j < b := by obtain ⟨_,_⟩ := Finset.mem_Icc.mp hj; omega
    have hh := hp.2.2.2.2.1 j (Finset.mem_range.mpr hjb)
    linarith [ford_cutoff_two_le hp (show j+1 ≤ b by omega)]
  have hlogY : 0 < Real.log (Y 1) := Real.log_pos hY
  have hlogYb : 0 < Real.log (Y b) := Real.log_pos (by linarith [ford_cutoff_two_le hp (k:=b) le_rfl])
  have hQ : 0 ≤ (Real.log (Y 1))⁻¹*Q := by dsimp [Q] <;> positivity
  have hPbound : (216*A)*M*(B y)^5*P ≤ (K*B y)^(6*b) := by
    have hmono : P ≤ ∏ k ∈ Finset.Icc 2 b,K*(k:ℝ)^2*(B y)^2 := by
      apply Finset.prod_le_prod
      · intro k _; positivity
      · intro k _
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCK (sq_nonneg _)) (sq_nonneg _)
    exact (mul_le_mul_of_nonneg_left hmono (by positivity)).trans
      (ford_polynomial_budget hp.1 hBy (ford_band_count_le hp) hK hA hM hAK hMK (by linarith))
  have hQbound := ford_logarithmic_product_bound (y:=y) (S:=S) Y U hp.1 hy (by linarith)
    (by linarith [(ford_scale_bounds hp).2])
    (by linarith [ford_cutoff_B_one_le hp (k:=b) le_rfl]) hY hU
  have hprod : (∏ k ∈ Finset.Icc 2 b,fordBandCost C k y S Y U)=P*Q := by
    simp_rw [ford_band_cost_split]
    exact Finset.prod_mul_distrib
  have hinv : (Real.log y)^(-2:ℝ)=((Real.log y)^2)⁻¹ := by
    rw [Real.rpow_neg hlog.le]
    norm_num only [Real.rpow_ofNat]
  have heq :
      ((216*A)*(y/(D*r:ℕ))*(B y)^5/(Real.log y)^2/Real.log (Y 1))*
        (∏ k ∈ Finset.Icc 2 b,fordBandCost C k y S Y U)*
        (M*(b+1:ℝ)^D.primeFactorsList.length*Z)=
      (y/(D*r:ℕ))*((216*A)*M*(B y)^5*P)*
        (b+1:ℝ)^D.primeFactorsList.length*Z*(Real.log y)^(-2:ℝ)*
        ((Real.log (Y 1))⁻¹*Q) := by
    rw [hprod,hinv]
    ring
  change _ ≤ _ at hQbound
  rw [heq]
  have hout : 0 ≤ (y/(D*r:ℕ))*(b+1:ℝ)^D.primeFactorsList.length*Z*(Real.log y)^(-2:ℝ) := by
    dsimp [Z] <;> positivity
  have hh := mul_le_mul hPbound hQbound hQ (by positivity : 0 ≤ (K*B y)^(6*b))
  have hh' := mul_le_mul_of_nonneg_left hh hout
  refine Eq.trans_le ?_ (hh'.trans_eq ?_)
  · ring
  · symm
    unfold fordComparisonBound
    have hpowe : (Real.log y)^(-2+(∑ j ∈ Finset.Icc 1 (b-1),a j*(B (Y j)/B y))+
        comparisonError b y S Y U)=
        (Real.log y)^(-2:ℝ)*(Real.log y)^((∑ j ∈ Finset.Icc 1 (b-1),a j*(B (Y j)/B y))+
          comparisonError b y S Y U) := by
      rw [← Real.rpow_add hlog]
      congr 1
      ring
    rw [hpowe]
    push_cast
    dsimp [Z]
    ring

lemma ford_comparison_budget_one {D r : ℕ} {y S A M K : ℝ} {Y U : ℕ → ℝ}
    (hp : FordComparisonParameters 1 y S D r Y U) (hy : 1 < y)
    (hA : 0 ≤ A) (hM : 0 ≤ M) (hK : 1 ≤ K)
    (hAK : 216*A ≤ K) (hMK : M ≤ K) :
    ((216*A)*(y/(D*r:ℕ))*(B y)^5/(Real.log y)^2/Real.log (Y 1))*
      (M*(2:ℝ)^D.primeFactorsList.length*(Real.log (Y 1))^2) ≤
    fordComparisonBound K 1 y S D r Y U := by
  have hBy : 1 ≤ B y := by simpa only [hp.2.1] using ford_cutoff_B_one_le hp (k:=0) (by decide)
  have hy0 : 0 ≤ y := by linarith
  have hlog : 0 < Real.log y := Real.log_pos hy
  have hlogY : 0 < Real.log (Y 1) := Real.log_pos (by linarith [ford_cutoff_two_le hp hp.1])
  have hpoly : (216*A)*M*(B y)^5 ≤ (K*B y)^6 := by
    simpa using ford_polynomial_budget (b:=1) (by decide) hBy (by simpa using hBy) hK hA hM hAK hMK (by linarith)
  have hfac : 0 ≤ (y/(D*r:ℕ))*(2:ℝ)^D.primeFactorsList.length*
      Real.log (Y 1)*((Real.log y)^2)⁻¹ := by positivity
  have hh := mul_le_mul_of_nonneg_left hpoly hfac
  have hinv : (Real.log y)^(-2:ℝ)=((Real.log y)^2)⁻¹ := by
    rw [Real.rpow_neg hlog.le]
    norm_num only [Real.rpow_ofNat]
  refine Eq.trans_le ?_ (hh.trans_eq ?_)
  · field_simp
  · symm
    norm_num [fordComparisonBound,comparisonError,hinv]
    ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionInput
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unconditional proof of the needed published Ford Lemma 5.1 specialization. -/
noncomputable section
namespace TotientAsymptotic

theorem fordLemma51Input : FordLemma51Input := by
  obtain ⟨A,C,M,R,hA,hC,hM,hR,hcount⟩ := ford_raw_count
  obtain ⟨A₁,M₁,hA₁,hM₁,hcount₁⟩ := ford_raw_count_one
  obtain ⟨y₀,hy₀,hthreshold⟩ := ford_comparison_threshold R hR
  let K := 1+216*A+216*A₁+M+M₁+C
  have hK : 1 ≤ K := by dsimp [K] <;> linarith
  have hAK : 216*A ≤ K := by dsimp [K] <;> linarith
  have hA₁K : 216*A₁ ≤ K := by dsimp [K] <;> linarith
  have hMK : M ≤ K := by dsimp [K] <;> linarith
  have hM₁K : M₁ ≤ K := by dsimp [K] <;> linarith
  have hCK : C ≤ K := by dsimp [K] <;> linarith
  refine ⟨K,y₀,by linarith,hy₀,?_⟩
  intro b y S D r Y U hy hp T hT
  have hy1 : 1 < y := hy₀.trans_le hy
  obtain ⟨hy2,hBy,hroot⟩ := hthreshold y hy
  by_cases hb : b=1
  · subst b
    exact (hcount₁ D r y S Y U hy2 hBy hp T hT).trans
      (ford_comparison_budget_one hp hy1 hA₁.le hM₁.le hK hA₁K hM₁K)
  · have hb2 : 2 ≤ b := by have := hp.1; omega
    exact (hcount b D r y S Y U hy2 hBy hb2 hp
      (hroot S (ford_scale_bounds hp).2) T hT).trans
      (ford_comparison_budget hp hy1 hA.le hM.le hC.le hK hAK hMK hCK)

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CandidateNormalMass
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normality prime-mass saving at the full-fiber construction's cutoff. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma candidate_total_prime_mass : ∃ D : ℝ,0 < D ∧ ∀ b : ℝ,2 ≤ b →
    (∑ p ∈ Nat.primesLE (discardPrimeBound b),((p-1:ℕ):ℝ)⁻¹) ≤ D*(2*b+2) := by
  obtain ⟨D,hD,hbound⟩ := prime_reciprocal_mass_bound mertensProductInput
  refine ⟨D,hD,?_⟩
  intro b hb
  obtain ⟨hN,hBN,hBU,_⟩ := discardPrimeBound_bounds hb
  apply (hbound _ (by omega) hBN).trans
  exact mul_le_mul_of_nonneg_left (by linarith only [hBU]) hD.le

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SubpowerCandidate
attribute [-simp] _root_.SelbergSieve.selbergBoundingSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The candidate tail is smaller than every fixed power of the ambient scale. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma subpower_log_eventually_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,(Real.log x)^(4/5:ℝ) ≤ ε*Real.log x := by
  filter_upwards [subpower_log_ratio.eventually (eventually_lt_nhds hε),
    eventually_gt_atTop (1:ℝ)] with x hx hx1
  exact (div_le_iff₀ (Real.log_pos hx1)).mp hx.le

lemma capped_tail_subpower {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,∀ n : ℕ,n ≤ m x → ∀ p : Fin n → ℕ,
      (∀ i,(p i).Prime) → (∀ i,primePrefixCoord p i ≤ (19/25:ℝ)*B x) →
      ((∏ i,p i:ℕ):ℝ) ≤ x^ε := by
  filter_upwards [capped_tail_denominator_budget 1,subpower_log_eventually_le hε,
    eventually_gt_atTop (1:ℝ)] with x hx hpower hx1
  intro n hn p hp hcap
  have hr : (0:ℝ) < (∏ i,p i:ℕ) := by
    exact_mod_cast Finset.prod_pos (fun i _ => (hp i).pos)
  have htail := prime_tail_log_bound p hp hcap
  have hdim := mul_le_mul_of_nonneg_right (show (n:ℝ) ≤ m x by exact_mod_cast hn)
    (Real.exp_pos ((19/25:ℝ)*B x)).le
  norm_num only [Nat.cast_one,Real.log_one,zero_add] at hx
  have hlog : Real.log ((∏ i,p i:ℕ):ℝ) ≤ ε*Real.log x :=
    htail.trans (hdim.trans (hx.trans hpower))
  have he := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hr] at he
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hx1)]
  simpa only [mul_comm] using he

lemma subpower_head_lower {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,∀ D : ℝ,1 ≤ D →
      Real.log D ≤ (Real.log x)^(4/5:ℝ) →
      ∀ q ∈ primeInterval (x/(2*D)) (x/D),x^(1-ε) < (q:ℝ) := by
  have hconst : Tendsto (fun x : ℝ => Real.log 2/Real.log x) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  filter_upwards [subpower_log_eventually_le (half_pos hε),
    hconst.eventually (eventually_lt_nhds (half_pos hε)),
    eventually_gt_atTop (1:ℝ)] with x hsmall hconst hx1
  intro D hD hlog q hq
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have htwo : Real.log 2 ≤ (ε/2)*Real.log x :=
    (div_le_iff₀ hlogx).mp hconst.le
  have hargument : (1-ε)*Real.log x ≤ Real.log (x/(2*D)) := by
    rw [Real.log_div hx0.ne' (mul_pos (by norm_num) hD0).ne',
      Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hD0.ne']
    linarith only [hsmall,hlog,htwo]
  have hp := Real.exp_le_exp.mpr hargument
  rw [Real.exp_log (div_pos hx0 (mul_pos (by norm_num) hD0))] at hp
  have hroot : x^(1-ε) ≤ x/(2*D) := by
    rw [Real.rpow_def_of_pos hx0]
    simpa only [mul_comm] using hp
  exact hroot.trans_lt (mem_head_prime_interval hx0.le hD0 hq).2.1

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalSuffixBounds
attribute [-instance] _root_.instMeasurableSpace
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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalOriginalComparisonData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original-head branch retains a geometric tail, a dominant head,
and normality for the same ordered representation. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem local_original_comparison_data {c : ℝ} (hc : 0 < c)
    (d : ℕ) (hd : 0<d) (L : ℕ) :
    ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∀ b∈localNormalCandidates x c d L H,
        ∃ (p : Fin (m x-H) → ℕ) (q : ℕ),
          b=q*(∏ i,p i) ∧ (∀ i,(p i).Prime) ∧ StrictAnti p ∧
          primePrefixCoord p ∈ relaxedGeometricFamily (m x) (m x-H) (B x) (c/2) ∧
          q.Prime ∧ (∀ i,p i<q) ∧
          ((∏ i,p i:ℕ):ℝ)≤x^(1/10:ℝ) ∧ x^(9/10:ℝ)<(q:ℝ) ∧
          IsNormalPrime (localNormalityScale (m x)) q ∧
          (∀ i,IsNormalPrime (localNormalityScale (m x)) (p i)) ∧
          3 ≤ q ∧ (∀ i,3 ≤ p i) ∧
          (∀ i,primePrefixCoord p i ≤ (19/25:ℝ)*B x) := by
  filter_upwards [raw_candidate_prime_data hc d hd,
    local_normal_candidate_normality_and_value hc d hd L,
    raw_candidate_rough hc d hd] with H hdata hnormal hrough
  filter_upwards [hdata,hnormal,hrough,
    capped_tail_subpower (by norm_num : (0:ℝ)<1/10),
    subpower_head_lower (by norm_num : (0:ℝ)<1/10)]
    with x hdata hnormal hrough htailbound hheadbound
  intro b hb
  have hbraw := local_regular_candidates_subset (local_normal_candidates_subset hb)
  obtain ⟨p,q,he,hp,ho,hgeom,hcap,hinterval,hq,hqp,hlog⟩ := hdata b hbraw
  have hD : (1:ℝ) ≤ ((d*(∏ i,p i).totient:ℕ):ℝ) := by
    exact_mod_cast Nat.mul_pos hd (Nat.totient_pos.mpr
      (Finset.prod_pos (fun i _ => (hp i).pos)))
  have htail := htailbound _ (Nat.sub_le _ _) p hp hcap
  have hhead := hheadbound _ hD hlog q hinterval
  have hqdiv : q∣b := by rw [he]; exact dvd_mul_right _ _
  have hpdiv (i) : p i∣b := by
    rw [he]
    exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem p (Finset.mem_univ i)) _
  have hn := (hnormal b hb).2
  refine ⟨p,q,he,hp,ho,hgeom,hq,hqp,htail,?_,hn q hq hqdiv,
    (fun i => hn (p i) (hp i) (hpdiv i)),?_,?_,hcap⟩
  · convert hhead using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  · have hh := hrough b hbraw q hq hqdiv
    omega
  · intro i
    have hh := hrough b hbraw (p i) (hp i) (hpdiv i)
    omega

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTTailParameters
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The factor-count cost of fixing the small left tail in the PPT application
of Ford's comparison lemma.  Normality bounds the count through the
terminal cutoff, rather than through the much larger size of the tail.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

theorem ppt_small_tail_totient_omega {h : ℕ} (p : Fin h → ℕ) {S V : ℝ}
    (hp : ∀ i, IsNormalPrime S (p i)) (hinj : Function.Injective p)
    (hS : 1 < S) (hBS : 0 ≤ B S) (hSV : S ≤ V)
    (hsmall : ∀ i, (largestPrimeFactor (p i-1) : ℝ) ≤ V) :
    (((∏ i, p i).totient).primeFactorsList.length : ℝ) ≤ 4*(h : ℝ)*B V := by
  have ht (i : Fin h) : partBelow (p i-1) V = p i-1 :=
    partBelow_all_of_largest_le
      (Nat.sub_pos_of_lt (hp i).1.one_lt).ne' (hsmall i)
  have hb := normal_terminal_product_omega p hp hS hBS hSV
  simpa only [ht, ppt_totient_primeProduct p (fun i => (hp i).1) hinj,
    shiftedProduct] using hb

/-- The seed contribution stays fixed; the tail contributes only through
its number of primes and the double logarithm of the terminal cutoff. -/
theorem ppt_small_tail_seed_omega {h d : ℕ} (p : Fin h → ℕ) {S V : ℝ}
    (hd : 0 < d) (hp : ∀ i, IsNormalPrime S (p i)) (hinj : Function.Injective p)
    (hS : 1 < S) (hBS : 0 ≤ B S) (hSV : S ≤ V)
    (hsmall : ∀ i, (largestPrimeFactor (p i-1) : ℝ) ≤ V) :
    ((d*(∏ i, p i).totient).primeFactorsList.length : ℝ) ≤
      d.primeFactorsList.length + 4*(h : ℝ)*B V := by
  have hpos : 0 < (∏ i, p i).totient := Nat.totient_pos.mpr
    (Finset.prod_pos (fun i _ => (hp i).1.pos))
  rw [omega_count_mul hd.ne' hpos.ne', Nat.cast_add]
  have htail := ppt_small_tail_totient_omega p hp hinj hS hBS hSV hsmall
  linarith only [htail]

/-- Explicit additional cost of using `D=d*φ(a)` in the `l=0`
specialization of the comparison estimate. -/
theorem ppt_small_tail_comparison_cost {h d : ℕ} (b : ℕ) (p : Fin h → ℕ) {S V : ℝ}
    (hd : 0 < d) (hp : ∀ i, IsNormalPrime S (p i)) (hinj : Function.Injective p)
    (hS : 1 < S) (hBS : 0 ≤ B S) (hSV : S ≤ V)
    (hsmall : ∀ i, (largestPrimeFactor (p i-1) : ℝ) ≤ V) :
    (b+1 : ℝ)^((d*(∏ i, p i).totient).primeFactorsList.length) ≤
      (b+1 : ℝ)^d.primeFactorsList.length *
        Real.exp (4*(h : ℝ)*B V*Real.log (b+1)) := by
  have hbase : (1 : ℝ) ≤ b+1 := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le b)
  have hpos : (0 : ℝ) < b+1 := by positivity
  have hΩ := ppt_small_tail_seed_omega p hd hp hinj hS hBS hSV hsmall
  calc
    _ ≤ (b+1 : ℝ)^((d.primeFactorsList.length : ℝ)+4*(h : ℝ)*B V) := by
      simpa only [Real.rpow_natCast] using
        Real.rpow_le_rpow_of_exponent_le hbase hΩ
    _ = _ := by
      rw [Real.rpow_add hpos, Real.rpow_natCast, Real.rpow_def_of_pos hpos]
      congr 2
      ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTComparisonSum
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite summation of the fixed-common-factor, fixed-left-tail comparison
blocks in Ford's proof of (5.23).  The published comparison predicates
remain explicit.  The extra factor from fixing the left tail is bounded
by its already proved normality estimate.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma ppt_comparison_scale_nonneg {C z W : ℝ} {b : ℕ} {Y U : ℕ → ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B z) (hz : 1 ≤ z) (hY : 1 ≤ Y b) :
    0 ≤ pptComparisonScale C b z W Y U := by
  have hlogz : 0 ≤ Real.log z := Real.log_nonneg hz
  have hlogY : 0 ≤ Real.log (Y b) := Real.log_nonneg hY
  unfold pptComparisonScale
  positivity

lemma ppt_comparison_bound_factor (C : ℝ) (b d c t : ℕ) (z W : ℝ)
    (Y U : ℕ → ℝ) :
    fordComparisonBound C b z W (d*t.totient) c.totient Y U =
      z/(d : ℝ) * pptComparisonScale C b z W Y U *
        (1/(c.totient : ℝ)) * (1/(t.totient : ℝ)) *
        (b+1 : ℝ)^((d*t.totient).primeFactorsList.length) := by
  simp only [fordComparisonBound, pptComparisonScale, Nat.cast_mul,
    div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTComparisonAssembly
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Assemble the pointwise conditions in Ford's comparison estimate after
the actual matched coordinates have been removed.  The right residual
is an integer multiplier in the shifted-product equation; no additional
representation of that multiplier as a totient is required.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

/-- Left-list recovery alone proves injectivity of a fixed comparison
block, even when its right residual is supplied directly as an integer. -/
lemma ppt_plain_comparison_injective {b c a : ℕ} (T : Finset ℕ)
    (t : ℕ → ShiftedPair b)
    (hreal : ∀ n ∈ T, n = c*a*∏ i, (t n).left i) :
    Set.InjOn t (T : Set ℕ) := by
  intro n hn m hm he
  have hleft := congrArg ShiftedPair.left he
  rw [hreal n hn, hreal m hm, hleft]

/-- The unconditional published estimate on a fixed common-factor and
left-tail block, with its actual integer right residual. -/
theorem ppt_plain_comparison_block_count :
    ∃ C z₀ : ℝ, 0 < C ∧ 1 < z₀ ∧
    ∀ (b d c a : ℕ) (z S : ℝ) (Y U : ℕ → ℝ),
      z₀ ≤ z → FordComparisonParameters b z S (d*a.totient) c.totient Y U →
      ∀ (T : Finset ℕ) (t : ℕ → ShiftedPair b),
        (∀ n ∈ T, n = c*a*∏ i, (t n).left i) →
        (∀ n ∈ T, FordComparisonConditions b z S (d*a.totient) c.totient Y U (t n)) →
        (T.card : ℝ) ≤ fordComparisonBound C b z S (d*a.totient) c.totient Y U := by
  classical
  obtain ⟨C, z₀, hC, hz₀, hford⟩ := fordLemma51Input
  refine ⟨C, z₀, hC, hz₀, ?_⟩
  intro b d c a z S Y U hz hparams T t hreal hconditions
  have hh := hford b z S (d*a.totient) c.totient Y U hz hparams (T.image t) (by
    intro v hv
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hv
    exact hconditions n hn)
  rwa [Finset.card_image_of_injOn (ppt_plain_comparison_injective T t hreal)] at hh

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTComparisonScaleDecay
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The literal Ford comparison prefactor in the PPT range.  The number of
high and low primes is logarithmic in `t`; the terminal cutoff has
double logarithm at most `2 t^(2/3)`.  All fixed-seed and finite-family
costs are retained before applying the proved strict-exponent decay.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

private lemma ppt_log_prefactor_bound {A L R X V M : ℝ} {b D h : ℕ}
    (hA : 0 ≤ A) (hL : 1 ≤ L) (hR : 1 ≤ R) (hb : 1 ≤ b)
    (hbL : (b : ℝ) ≤ A*L) (hhL : (h : ℝ) ≤ A*L)
    (hX : X ≤ 2*R) (hV0 : 0 ≤ V) (hV : V ≤ 2*R) :
    6*(b : ℝ)*(M+L)+(20*(b : ℝ)*Real.log b+1)*X+
      (D : ℝ)*Real.log (b+1)+4*(h : ℝ)*V*Real.log (b+1) ≤
        (6*A*(|M|+1)+48*A^2+(D : ℝ)*A+2)*R*L^2 := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg _
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hlogb0 : 0 ≤ Real.log b := Real.log_nonneg hb1
  have hlogb : Real.log b ≤ A*L := (Real.log_le_self hb0).trans hbL
  have hlogb1 : Real.log (b+1) ≤ A*L := by
    have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < b+1 by positivity)
    have hh' : Real.log (b+1) ≤ (b : ℝ) := by linarith only [hh]
    exact hh'.trans hbL
  have hlogb10 : 0 ≤ Real.log (b+1) :=
    Real.log_nonneg (show (1 : ℝ) ≤ (b : ℝ)+1 by linarith only [hb0])
  have hAL : 0 ≤ A*L := mul_nonneg hA hL0
  have hpair : (b : ℝ)*Real.log b ≤ A^2*L^2 := by
    have hh := mul_le_mul hbL hlogb hlogb0 hAL
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring_nf
  have hpair' : (h : ℝ)*Real.log (b+1) ≤ A^2*L^2 := by
    have hh := mul_le_mul hhL hlogb1 hlogb10 hAL
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring_nf
  have hLL : L ≤ L^2 := by nlinarith only [hL]
  have hRR : L^2 ≤ R*L^2 := by nlinarith only [hR, sq_nonneg L]
  have hML : M+L ≤ (|M|+1)*L := by
    have hm := mul_le_mul_of_nonneg_left hL (abs_nonneg M)
    nlinarith only [hm, le_abs_self M]
  have hfirst : 6*(b : ℝ)*(M+L) ≤ 6*A*(|M|+1)*R*L^2 := by
    calc
      _ ≤ 6*(b : ℝ)*((|M|+1)*L) :=
        mul_le_mul_of_nonneg_left hML (by positivity)
      _ ≤ 6*(A*L)*((|M|+1)*L) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbL (by norm_num))
          (by positivity)
      _ = 6*A*(|M|+1)*L^2 := by ring_nf
      _ ≤ _ := by
        nlinarith only [mul_le_mul_of_nonneg_left hRR
          (show 0 ≤ 6*A*(|M|+1) by positivity)]
  have hcoef0 : 0 ≤ 20*(b : ℝ)*Real.log b+1 := by positivity
  have hcoef : 20*(b : ℝ)*Real.log b+1 ≤ (20*A^2+1)*L^2 := by
    nlinarith only [hpair, hL, sq_nonneg L]
  have hsecond : (20*(b : ℝ)*Real.log b+1)*X ≤ (40*A^2+2)*R*L^2 := by
    calc
      _ ≤ (20*(b : ℝ)*Real.log b+1)*(2*R) :=
        mul_le_mul_of_nonneg_left hX hcoef0
      _ ≤ ((20*A^2+1)*L^2)*(2*R) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = _ := by ring_nf
  have hthird : (D : ℝ)*Real.log (b+1) ≤ (D : ℝ)*A*R*L^2 := by
    calc
      _ ≤ (D : ℝ)*(A*L) := mul_le_mul_of_nonneg_left hlogb1 (Nat.cast_nonneg _)
      _ ≤ (D : ℝ)*(A*L^2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hLL hA) (Nat.cast_nonneg _)
      _ = (D : ℝ)*A*L^2 := by ring_nf
      _ ≤ _ := by
        nlinarith only [mul_le_mul_of_nonneg_left hRR
          (show 0 ≤ (D : ℝ)*A by positivity)]
  have hfourth : 4*(h : ℝ)*V*Real.log (b+1) ≤ 8*A^2*R*L^2 := by
    calc
      _ = 4*V*((h : ℝ)*Real.log (b+1)) := by ring_nf
      _ ≤ 4*V*(A^2*L^2) := mul_le_mul_of_nonneg_left hpair' (by positivity)
      _ ≤ 4*(2*R)*(A^2*L^2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hV (by norm_num)) (by positivity)
      _ = _ := by ring_nf
  nlinarith only [hfirst, hsecond, hthird, hfourth]

/-- The complete positive prefactor is at most the required exponential
in `t^(2/3) (log t)^2`, uniformly in both prime-list lengths. -/
theorem ppt_full_prefactor_bound {C A t u V M : ℝ} {b D h : ℕ}
    (hC : 0 < C) (hA : 0 ≤ A) (ht : 1 ≤ Real.log t) (ht0 : 0 < t)
    (hb : 1 ≤ b) (hbL : (b : ℝ) ≤ A*Real.log t)
    (hhL : (h : ℝ) ≤ A*Real.log t) (hu : 0 < u)
    (huT : Real.log u ≤ 2*t^(2/3 : ℝ))
    (hV0 : 0 ≤ V) (hV : V ≤ 2*t^(2/3 : ℝ)) :
    pptFullComparisonPrefactor C t b D h u V M ≤
      Real.exp (pptPrefactorConstant C A M D*t^(2/3 : ℝ)*(Real.log t)^2) := by
  have ht1 : 1 ≤ t := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans
    ((Real.exp_le_exp.mpr ht).trans_eq (Real.exp_log ht0))
  have hR : 1 ≤ t^(2/3 : ℝ) := Real.one_le_rpow ht1 (by norm_num)
  have hraw := ppt_log_prefactor_bound (D := D) hA ht hR hb hbL hhL huT hV0 hV
    (M := Real.log C)
  have hmass : M*(Real.log t)^2 ≤ |M| * t^(2/3 : ℝ)*(Real.log t)^2 := by
    have hh := mul_le_mul_of_nonneg_left hR (abs_nonneg M)
    have hm : M ≤ |M| * t^(2/3 : ℝ) :=
      (le_abs_self M).trans (by simpa only [mul_one] using hh)
    exact mul_le_mul_of_nonneg_right hm (sq_nonneg _)
  have hCt : 0 < C*t := mul_pos hC ht0
  have hpower : (C*t)^(6*b) = Real.exp ((6*b : ℕ)*Real.log (C*t)) := by
    rw [Real.exp_nat_mul, Real.exp_log hCt]
  have hseed : (b+1 : ℝ)^D = Real.exp ((D : ℝ)*Real.log (b+1)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by positivity : (0 : ℝ) < b+1)]
  have heq : pptFullComparisonPrefactor C t b D h u V M =
      Real.exp (6*(b : ℝ)*(Real.log C+Real.log t)+
        (20*(b : ℝ)*Real.log b+1)*Real.log u+(D : ℝ)*Real.log (b+1)+
        4*(h : ℝ)*V*Real.log (b+1)+M*(Real.log t)^2) := by
    rw [pptFullComparisonPrefactor, hpower, Real.rpow_def_of_pos hu, hseed]
    rw [Real.log_mul hC.ne' ht0.ne']
    simp only [Real.exp_add, Nat.cast_mul, Nat.cast_ofNat]
    ring_nf
  rw [heq]
  apply Real.exp_le_exp.mpr
  unfold pptPrefactorConstant
  nlinarith only [hraw, hmass]

/-- The literal prefactor, seed cost, normal-tail cost and finite-family
mass are absorbed by the strict inverse-log-cube exponent saving. -/
theorem ppt_full_comparison_decay {C A γ M : ℝ} (hC : 0 < C) (hA : 0 ≤ A)
    (hγ : 0 < γ) (D : ℕ) (K : ℝ) :
    ∀ᶠ z : ℝ in atTop, ∀ (b h : ℕ) (u V E : ℝ),
      1 ≤ b → (b : ℝ) ≤ A*Real.log (B z) → (h : ℝ) ≤ A*Real.log (B z) →
      0 < u → Real.log u ≤ 2*(B z)^(2/3 : ℝ) →
      0 ≤ V → V ≤ 2*(B z)^(2/3 : ℝ) →
      E ≤ -1-γ/(Real.log (B z))^3 →
      pptFullComparisonPrefactor C (B z) b D h u V M*(Real.log z)^E ≤
        (Real.log z)⁻¹*(B z)^(-K) := by
  filter_upwards [ppt_comparison_exp_decay_at_scale (pptPrefactorConstant C A M D) K hγ,
    B_tendsto.eventually (eventually_gt_atTop (Real.exp 1)),
    eventually_gt_atTop (Real.exp 1)] with z hdecay hB hz
  intro b h u V E hb hbL hhL hu huT hV0 hV hE
  have hB0 : 0 < B z := (Real.exp_pos 1).trans hB
  have hlogB : 1 ≤ Real.log (B z) := by
    have hh := Real.log_le_log (Real.exp_pos 1) hB.le
    simpa only [Real.log_exp] using hh
  have hlogz : 1 ≤ Real.log z := by
    have hh := Real.log_le_log (Real.exp_pos 1) hz.le
    simpa only [Real.log_exp] using hh
  have hpre := ppt_full_prefactor_bound hC hA hlogB hB0 hb hbL hhL hu huT hV0 hV
    (D := D) (M := M)
  have hpow := comparison_log_power_saving hlogz hE
  have hpow0 : 0 ≤ (Real.log z)^E := Real.rpow_nonneg (zero_le_one.trans hlogz) _
  calc
    _ ≤ Real.exp (pptPrefactorConstant C A M D*(B z)^(2/3 : ℝ)*
        (Real.log (B z))^2)*((Real.log z)⁻¹*
          Real.exp (-(γ/(Real.log (B z))^3)*B z)) :=
      mul_le_mul hpre hpow hpow0 (Real.exp_pos _).le
    _ = (Real.log z)⁻¹*Real.exp (pptPrefactorConstant C A M D*(B z)^(2/3 : ℝ)*
        (Real.log (B z))^2-γ*B z/(Real.log (B z))^3) := by
      have he : -(γ/(Real.log (B z))^3)*B z = -(γ*B z/(Real.log (B z))^3) := by ring_nf
      rw [he, Real.exp_neg, Real.exp_sub]
      simp only [div_eq_mul_inv]
      ring_nf
    _ ≤ _ := mul_le_mul_of_nonneg_left hdecay (inv_nonneg.mpr (zero_le_one.trans hlogz))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTGridCount
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
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

/-- There are at most exponentially many grid labels in the square of
the logarithm of the local double-logarithmic scale. -/
theorem ppt_grid_card_bound {A t δ : ℝ} {b : ℕ}
    (ht0 : 0 < t) (ht : 1 ≤ Real.log t) (hδ : 0 < δ) (hmesh : 1/t ≤ δ)
    (hdim : (b : ℝ) ≤ A*Real.log t) :
    ((collisionGridFamilies δ b).card : ℝ) ≤
      Real.exp (2*A*(Real.log t)^2) := by
  have ht1 : 1 < t := (Real.log_pos_iff ht0.le).mp (zero_lt_one.trans_le ht)
  have hinverse : 1/δ ≤ t := by
    apply (div_le_iff₀ hδ).mpr
    have hh := (div_le_iff₀ ht0).mp hmesh
    nlinarith only [hh]
  have hbase : ((⌊1/δ⌋₊+1 : ℕ) : ℝ) ≤ 2*t := by
    have hf := Nat.floor_le (show 0 ≤ 1/δ by positivity)
    push_cast
    linarith only [hf, hinverse, ht1.le]
  have hlog : Real.log (2*t) ≤ 2*Real.log t := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ht0.ne']
    have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith only [htwo, ht]
  rw [collisionGridFamilies_card, Nat.cast_pow]
  calc
    _ ≤ (2*t)^b := pow_le_pow_left₀ (by positivity) hbase b
    _ = Real.exp ((b : ℝ)*Real.log (2*t)) := by
      rw [Real.exp_nat_mul, Real.exp_log (by positivity : 0 < 2*t)]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      calc
        (b : ℝ)*Real.log (2*t) ≤ (b : ℝ)*(2*Real.log t) :=
          mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)
        _ ≤ (A*Real.log t)*(2*Real.log t) :=
          mul_le_mul_of_nonneg_right hdim (by linarith only [ht])
        _ = 2*A*(Real.log t)^2 := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTResidualCount
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
All residual block labels are summed before the strict comparison
exponent is spent. This retains the exponential-square budget needed
for variable dimensions, grid labels, common factors, and small tails.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

/-- The literal Ford bound, normal small-tail estimate, and strict
exponent together control any finite family of actual residual blocks.
The only aggregate quantity is the explicit reciprocal-factor mass. -/
theorem ppt_finite_residual_block_decay (d : ℕ) (hd : 0 < d)
    {A γ M : ℝ} (hA : 0 ≤ A) (hγ : 0 < γ) (K : ℝ) :
    ∀ᶠ z : ℝ in atTop,
    ∀ (α : Type) (I : Finset α) (b h c a : α → ℕ) (W V : α → ℝ)
      (Y U : α → ℕ → ℝ) (tail : (i : α) → Fin (h i) → ℕ)
      (T : α → Finset ℕ) (t : (i : α) → ℕ → ShiftedPair (b i)),
      (∀ i ∈ I, 1 ≤ b i) →
      (∀ i ∈ I, (b i : ℝ) ≤ A*Real.log (B z)) →
      (∀ i ∈ I, (h i : ℝ) ≤ A*Real.log (B z)) →
      (∀ i ∈ I, 1 < W i ∧ 0 ≤ B (W i) ∧ W i ≤ V i) →
      (∀ i ∈ I, 1 < Y i (b i) ∧ B (Y i (b i)) ≤ 2*(B z)^(2/3 : ℝ)) →
      (∀ i ∈ I, 0 ≤ B (V i) ∧ B (V i) ≤ 2*(B z)^(2/3 : ℝ)) →
      (∑ i ∈ I, (1/((a i).totient : ℝ))*(1/((c i).totient : ℝ))) ≤
        Real.exp (M*(Real.log (B z))^2) →
      (∀ i ∈ I, a i = ∏ j, tail i j) →
      (∀ i ∈ I, Function.Injective (tail i)) →
      (∀ i ∈ I, ∀ j, IsNormalPrime (W i) (tail i j)) →
      (∀ i ∈ I, ∀ j, (largestPrimeFactor (tail i j-1) : ℝ) ≤ V i) →
      (∀ i ∈ I,
        -2+(∑ j ∈ Finset.Icc 1 (b i-1), TotientAsymptotic.a j*(B (Y i j)/B z))+
          comparisonError (b i) z (W i) (Y i) (U i) ≤
          -1-γ/(Real.log (B z))^3) →
      (∀ i ∈ I, FordComparisonParameters (b i) z (W i)
        (d*(a i).totient) (c i).totient (Y i) (U i)) →
      (∀ i ∈ I, ∀ n ∈ T i, n = c i*a i*∏ j, (t i n).left j) →
      (∀ i ∈ I, ∀ n ∈ T i, FordComparisonConditions (b i) z (W i)
        (d*(a i).totient) (c i).totient (Y i) (U i) (t i n)) →
      (∑ i ∈ I, ((T i).card : ℝ)) ≤ z/((d : ℝ)*Real.log z)*(B z)^(-K) := by
  classical
  obtain ⟨C, z₀, hC, _, hcount⟩ := ppt_plain_comparison_block_count
  filter_upwards [ppt_full_comparison_decay (M := M) hC hA hγ d.primeFactorsList.length K,
    eventually_ge_atTop z₀, eventually_gt_atTop (1 : ℝ),
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with z hdecay hz₀ hz hB
  intro α I b h c a W V Y U tail T t hb hbL hhL hW hY hV hmass
    htail hinj hnormal hsmall hE hparams hreal hconditions
  let Q : ℝ := Real.exp (M*(Real.log (B z))^2)
  let L : ℝ := (Real.log z)⁻¹*(B z)^(-K)
  have hQ : 0 < Q := Real.exp_pos _
  have hz0 : 0 < z := zero_lt_one.trans hz
  have hlogz : 0 < Real.log z := Real.log_pos hz
  have hL : 0 ≤ L := by dsimp only [L] <;> positivity
  have hscalar : 0 ≤ z/(d : ℝ)*L := mul_nonneg (by positivity) hL
  have hblock (i : α) (hi : i ∈ I) :
      ((T i).card : ℝ)*Q ≤
        (z/(d : ℝ)*L)*((1/((a i).totient : ℝ))*(1/((c i).totient : ℝ))) := by
    let E : ℝ := -2+
      (∑ j ∈ Finset.Icc 1 (b i-1), TotientAsymptotic.a j*(B (Y i j)/B z))+
      comparisonError (b i) z (W i) (Y i) (U i)
    let F : ℝ := (C*B z)^(6*b i)*(Real.log (Y i (b i)))^(20*(b i : ℝ)*Real.log (b i)+1)*
      (b i+1 : ℝ)^d.primeFactorsList.length *
      Real.exp (4*(h i : ℝ)*B (V i)*Real.log (b i+1))*(Real.log z)^E
    have hcost : (b i+1 : ℝ)^((d*(a i).totient).primeFactorsList.length) ≤
        (b i+1 : ℝ)^d.primeFactorsList.length *
          Real.exp (4*(h i : ℝ)*B (V i)*Real.log (b i+1)) := by
      rw [htail i hi]
      exact ppt_small_tail_comparison_cost (b i) (tail i) hd (hnormal i hi)
        (hinj i hi) (hW i hi).1 (hW i hi).2.1 (hW i hi).2.2 (hsmall i hi)
    have hsaved : F*Q ≤ L := by
      have hh := hdecay (b i) (h i) (Real.log (Y i (b i))) (B (V i)) E
        (hb i hi) (hbL i hi) (hhL i hi) (Real.log_pos (hY i hi).1)
        (hY i hi).2 (hV i hi).1 (hV i hi).2 (hE i hi)
      calc
        F*Q = pptFullComparisonPrefactor C (B z) (b i) d.primeFactorsList.length
            (h i) (Real.log (Y i (b i))) (B (V i)) M*(Real.log z)^E := by
          dsimp only [F, Q, pptFullComparisonPrefactor]
          ring
        _ ≤ L := hh
    have hscale : 0 ≤ pptComparisonScale C (b i) z (W i) (Y i) (U i) :=
      ppt_comparison_scale_nonneg hC.le hB.le hz.le (hY i hi).1.le
    have hcore : ((T i).card : ℝ) ≤
        (z/(d : ℝ))*((1/((a i).totient : ℝ))*(1/((c i).totient : ℝ)))*F := by
      have hraw := hcount (b i) d (c i) (a i) z (W i) (Y i) (U i)
        hz₀ (hparams i hi) (T i) (t i) (hreal i hi) (hconditions i hi)
      rw [ppt_comparison_bound_factor] at hraw
      have hmul := mul_le_mul_of_nonneg_left hcost
        (show 0 ≤ z/(d : ℝ)*pptComparisonScale C (b i) z (W i) (Y i) (U i)*
          (1/((c i).totient : ℝ))*(1/((a i).totient : ℝ)) by positivity)
      apply hraw.trans (hmul.trans_eq _)
      dsimp only [F, pptComparisonScale, E]
      ring
    calc
      ((T i).card : ℝ)*Q ≤
          ((z/(d : ℝ))*((1/((a i).totient : ℝ))*(1/((c i).totient : ℝ)))*F)*Q :=
        mul_le_mul_of_nonneg_right hcore hQ.le
      _ = (z/(d : ℝ))*((1/((a i).totient : ℝ))*(1/((c i).totient : ℝ)))*(F*Q) := by ring
      _ ≤ (z/(d : ℝ))*((1/((a i).totient : ℝ))*(1/((c i).totient : ℝ)))*L :=
        mul_le_mul_of_nonneg_left hsaved (by positivity)
      _ = _ := by ring
  have hsum : (∑ i ∈ I, ((T i).card : ℝ))*Q ≤ (z/(d : ℝ)*L)*Q := by
    calc
      _ = ∑ i ∈ I, ((T i).card : ℝ)*Q := Finset.sum_mul I _ Q
      _ ≤ ∑ i ∈ I, (z/(d : ℝ)*L)*
          ((1/((a i).totient : ℝ))*(1/((c i).totient : ℝ))) :=
        Finset.sum_le_sum hblock
      _ = (z/(d : ℝ)*L)*(∑ i ∈ I,
          (1/((a i).totient : ℝ))*(1/((c i).totient : ℝ))) := (Finset.mul_sum I _ _).symm
      _ ≤ (z/(d : ℝ)*L)*Q := mul_le_mul_of_nonneg_left hmass hscalar
  have hh := (mul_le_mul_iff_left₀ hQ).mp hsum
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [L]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- A finite cover by the actual comparison blocks suffices; the blocks
need not be disjoint. -/
lemma ppt_residual_block_cover {α : Type*} [DecidableEq α]
    (I : Finset α) (T : α → Finset ℕ) (R : Finset ℕ) {X : ℝ}
    (hcover : ∀ n ∈ R, ∃ i ∈ I, n ∈ T i)
    (hcount : (∑ i ∈ I, ((T i).card : ℝ)) ≤ X) : (R.card : ℝ) ≤ X := by
  classical
  have hsub : R ⊆ I.biUnion T := by
    intro n hn
    obtain ⟨i, hi, hni⟩ := hcover n hn
    exact Finset.mem_biUnion.mpr ⟨i, hi, hni⟩
  have hc := (Finset.card_le_card hsub).trans (Finset.card_biUnion_le)
  have hcr : (R.card : ℝ) ≤ ∑ i ∈ I, ((T i).card : ℝ) := by
    exact_mod_cast hc
  exact hcr.trans hcount

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTFactorLabels
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The actual finite label universe for the common prime product and the
small left tail. Products are counted as integers. Repeated prime lists
only enlarge the reciprocal-mass majorant.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma ppt_prime_product_family_mass (N h : ℕ) :
    (∑ n ∈ pptPrimeProductFamily N h, (n.totient : ℝ)⁻¹) ≤
      (∑ p ∈ Nat.primesLE N, ((p-1 : ℕ) : ℝ)⁻¹)^h := by
  classical
  let P := Fintype.piFinset (fun _ : Fin h => Nat.primesLE N)
  have himage := Finset.sum_image_le_of_nonneg (s := P) (g := fun p => ∏ i, p i)
    (f := fun n : ℕ => (n.totient : ℝ)⁻¹)
    (fun n _ => inv_nonneg.mpr (Nat.cast_nonneg n.totient))
  apply himage.trans
  calc
    _ ≤ ∑ p ∈ P, reciprocalShiftWeight p := by
      apply Finset.sum_le_sum
      intro p hp
      have hprime (i : Fin h) : (p i).Prime :=
        (Nat.mem_primesLE.mp (Fintype.mem_piFinset.mp hp i)).2
      have hnat := totient_prime_product_lower Finset.univ p 1 (fun i _ => hprime i)
      simp only [Nat.totient_one, one_mul] at hnat
      have hpos : (0 : ℝ) < (∏ i, (p i-1) : ℕ) := by
        exact_mod_cast Finset.prod_pos (fun i _ => Nat.sub_pos_of_lt (hprime i).one_lt)
      exact inv_anti₀ hpos (Nat.cast_le.mpr hnat)
    _ = ∏ _i : Fin h, ∑ p ∈ Nat.primesLE N, ((p-1 : ℕ) : ℝ)⁻¹ := by
      rw [Finset.prod_univ_sum]
      apply Finset.sum_congr rfl
      intro p _
      simp only [reciprocalShiftWeight, Nat.cast_prod, Finset.prod_inv_distrib]
    _ = _ := by simp

lemma ppt_all_factor_lengths_mass (N H : ℕ) :
    (∑ h ∈ Finset.range (H+1), ∑ n ∈ pptPrimeProductFamily N h, (n.totient : ℝ)⁻¹) ≤
      (H+1 : ℕ)*(max 1 (∑ p ∈ Nat.primesLE N, ((p-1 : ℕ) : ℝ)⁻¹))^H := by
  let P : ℝ := ∑ p ∈ Nat.primesLE N, ((p-1 : ℕ) : ℝ)⁻¹
  have hP : 0 ≤ P := Finset.sum_nonneg (fun p _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  calc
    _ ≤ ∑ h ∈ Finset.range (H+1), (max 1 P)^H := by
      apply Finset.sum_le_sum
      intro h hh
      have hhH : h ≤ H := Nat.lt_succ_iff.mp (Finset.mem_range.mp hh)
      exact (ppt_prime_product_family_mass N h).trans
        ((pow_le_pow_left₀ hP (le_max_right _ _) h).trans
          (pow_le_pow_right₀ (le_max_left _ _) hhH))
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; rfl

/-- Common and tail labels together with all lengths, all terminal
window indices, and all paired grid labels have a finite explicit mass.
No assertion about the number of bad integers enters this bound. -/
theorem ppt_all_residual_label_mass {A t δ : ℝ} {H N : ℕ}
    (ht0 : 0 < t) (ht : 1 ≤ Real.log t) (hδ : 0 < δ) (hmesh : 1/t ≤ δ)
    (hdim : (H : ℝ) ≤ A*Real.log t) :
    (∑ b ∈ Finset.range (H+1), ∑ _g ∈ collisionGridFamilies δ b,
      ∑ _j ∈ Finset.range (H+1),
      ∑ h ∈ Finset.range (H+1), ∑ a ∈ pptPrimeProductFamily N h,
      ∑ k ∈ Finset.range (H+1), ∑ c ∈ pptPrimeProductFamily N k,
        (a.totient : ℝ)⁻¹*(c.totient : ℝ)⁻¹) ≤
      ((H+1 : ℕ) : ℝ)^4 *
        (max 1 (∑ p ∈ Nat.primesLE N, ((p-1 : ℕ) : ℝ)⁻¹))^(2*H) *
          Real.exp (2*A*(Real.log t)^2) := by
  classical
  let F : ℝ := ∑ h ∈ Finset.range (H+1),
    ∑ a ∈ pptPrimeProductFamily N h, (a.totient : ℝ)⁻¹
  let P : ℝ := max 1 (∑ p ∈ Nat.primesLE N, ((p-1 : ℕ) : ℝ)⁻¹)
  let E : ℝ := Real.exp (2*A*(Real.log t)^2)
  have hF0 : 0 ≤ F := Finset.sum_nonneg (fun h _ =>
    Finset.sum_nonneg (fun a _ => inv_nonneg.mpr (Nat.cast_nonneg _)))
  have hF := ppt_all_factor_lengths_mass N H
  change F ≤ (H+1 : ℕ)*P^H at hF
  have hinner :
      (∑ h ∈ Finset.range (H+1), ∑ a ∈ pptPrimeProductFamily N h,
        ∑ k ∈ Finset.range (H+1), ∑ c ∈ pptPrimeProductFamily N k,
          (a.totient : ℝ)⁻¹*(c.totient : ℝ)⁻¹) = F*F := by
    simp only [← Finset.mul_sum, ← Finset.sum_mul, F]
  have hsum := Finset.sum_le_sum (s := Finset.range (H+1))
    (fun b hb => ppt_grid_card_bound ht0 ht hδ hmesh
      ((Nat.cast_le.mpr (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb))).trans hdim))
  have hgrid : (∑ b ∈ Finset.range (H+1), ((collisionGridFamilies δ b).card : ℝ)) ≤
      (H+1 : ℕ)*E := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, E] using hsum
  have hF2 : F^2 ≤ ((H+1 : ℕ)*P^H)^2 :=
    pow_le_pow_left₀ hF0 hF 2
  calc
    _ = (∑ b ∈ Finset.range (H+1), ((collisionGridFamilies δ b).card : ℝ))*
        ((H+1 : ℕ)*F^2) := by
      simp only [hinner, Finset.sum_const, Finset.card_range, nsmul_eq_mul, pow_two]
      exact (Finset.sum_mul _ _ _).symm
    _ ≤ ((H+1 : ℕ)*E)*((H+1 : ℕ)*((H+1 : ℕ)*P^H)^2) := by
      exact mul_le_mul hgrid (mul_le_mul_of_nonneg_left hF2 (Nat.cast_nonneg _))
        (by positivity) (by positivity)
    _ = _ := by rw [Nat.mul_comm 2 H, pow_mul]; ring

/-- The complete weighted label universe has exponential-square mass at
its actual local cutoff. This is the entropy budget consumed by
`ppt_finite_residual_block_decay`. -/
theorem ppt_residual_labels_exponential_mass {A : ℝ} (hA : 0 ≤ A) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ z : ℝ in atTop,
      ∀ (H : ℕ) (δ : ℝ),
        (H : ℝ) ≤ A*Real.log (B z) →
        0 < δ → 1/B z ≤ δ →
        (∑ b ∈ Finset.range (H+1), ∑ _g ∈ collisionGridFamilies δ b,
          ∑ _j ∈ Finset.range (H+1),
          ∑ h ∈ Finset.range (H+1), ∑ a ∈ pptPrimeProductFamily (discardPrimeBound (B z)) h,
          ∑ k ∈ Finset.range (H+1), ∑ c ∈ pptPrimeProductFamily (discardPrimeBound (B z)) k,
            (a.totient : ℝ)⁻¹*(c.totient : ℝ)⁻¹) ≤
          Real.exp (M*(Real.log (B z))^2) := by
  obtain ⟨D, hD, hprime⟩ := candidate_total_prime_mass
  let C : ℝ := 4*D+1
  let K₁ : ℝ := |Real.log (A+1)|+1
  let K₂ : ℝ := |Real.log C|+1
  let M : ℝ := 4*K₁+2*A*K₂+2*A
  have hK₁ : 0 < K₁ := by dsimp only [K₁] <;> positivity
  have hK₂ : 0 < K₂ := by dsimp only [K₂] <;> positivity
  have hC : 1 ≤ C := by dsimp only [C]; linarith only [hD]
  refine ⟨M, by dsimp only [M] <;> positivity, ?_⟩
  filter_upwards [B_tendsto.eventually (eventually_ge_atTop (2 : ℝ)),
    B_tendsto.eventually (eventually_ge_atTop (Real.exp 1))] with z ht2 hte
  intro H δ hdim hδ hmesh
  let t : ℝ := B z
  let P : ℝ := max 1 (∑ p ∈ Nat.primesLE (discardPrimeBound t), ((p-1 : ℕ) : ℝ)⁻¹)
  have ht : 0 < t := by dsimp only [t]; linarith only [ht2]
  have ht1 : 1 ≤ t := by dsimp only [t]; linarith only [ht2]
  have hlog : 1 ≤ Real.log t := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hte
  have hP1 : 1 ≤ P := le_max_left _ _
  have hP0 : 0 < P := zero_lt_one.trans_le hP1
  have hPC : P ≤ C*t := by
    apply max_le
    · exact one_le_mul_of_one_le_of_one_le hC ht1
    · have hp := hprime t ht2
      have hc : D*(2*t+2) ≤ C*t := by dsimp only [C]; nlinarith only [hD, ht1]
      exact hp.trans hc
  have hH : (H : ℝ)+1 ≤ (A+1)*t := by
    have hh := hdim.trans (mul_le_mul_of_nonneg_left (Real.log_le_self ht.le) hA)
    nlinarith only [hh, ht1]
  have hlogH : Real.log ((H : ℝ)+1) ≤ K₁*Real.log t := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < H+1) hH
    rw [Real.log_mul (by positivity : A+1 ≠ 0) ht.ne'] at hh
    have hk : Real.log (A+1) ≤ |Real.log (A+1)| * Real.log t :=
      (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hlog)
    dsimp only [K₁]
    nlinarith only [hh, hk]
  have hlogP : Real.log P ≤ K₂*Real.log t := by
    have hh := Real.log_le_log hP0 hPC
    rw [Real.log_mul (ne_of_gt (zero_lt_one.trans_le hC)) ht.ne'] at hh
    have hk : Real.log C ≤ |Real.log C| * Real.log t :=
      (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hlog)
    dsimp only [K₂]
    nlinarith only [hh, hk]
  have hlogH2 : 4*Real.log ((H : ℝ)+1) ≤ 4*K₁*(Real.log t)^2 := by
    have hh := le_mul_of_one_le_right (mul_nonneg hK₁.le (zero_le_one.trans hlog)) hlog
    nlinarith only [hlogH, hh]
  have hlogP2 : (2*(H : ℝ))*Real.log P ≤ 2*A*K₂*(Real.log t)^2 := by
    have hh := mul_le_mul hdim hlogP (Real.log_nonneg hP1)
      (mul_nonneg hA (zero_le_one.trans hlog))
    nlinarith only [hh]
  have hraw := ppt_all_residual_label_mass (N := discardPrimeBound t) ht hlog hδ hmesh hdim
  apply hraw.trans
  change ((H+1 : ℕ) : ℝ)^4*P^(2*H)*Real.exp (2*A*(Real.log t)^2) ≤ _
  rw [show ((H+1 : ℕ) : ℝ) = (H : ℝ)+1 by push_cast; rfl]
  rw [show ((H : ℝ)+1)^4 = Real.exp (4*Real.log ((H : ℝ)+1)) by
      have he := Real.exp_nat_mul (Real.log ((H : ℝ)+1)) 4
      rw [Real.exp_log (by positivity : (0 : ℝ) < H+1)] at he
      norm_num only [Nat.cast_ofNat] at he
      exact he.symm,
    show P^(2*H) = Real.exp ((2*(H : ℝ))*Real.log P) by
      rw [show 2*(H : ℝ) = ((2*H : ℕ) : ℝ) by push_cast; rfl,
        Real.exp_nat_mul, Real.exp_log hP0],
    ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  dsimp only [M]
  nlinarith only [hlogH2, hlogP2]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTFiniteLabels
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One finite label type for the actual residual comparison partition. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

lemma ppt_residual_labels_mass (N H : ℕ) (δ : ℝ) :
    (∑ l ∈ pptResidualLabels N H δ, pptLabelWeight l) =
      ∑ b ∈ Finset.range (H+1), ∑ _g ∈ collisionGridFamilies δ b,
        ∑ _j ∈ Finset.range (H+1),
        ∑ h ∈ Finset.range (H+1), ∑ a ∈ pptPrimeProductFamily N h,
        ∑ s ∈ Finset.range (H+1), ∑ c ∈ pptPrimeProductFamily N s,
          (a.totient : ℝ)⁻¹*(c.totient : ℝ)⁻¹ := by
  classical
  simp only [pptResidualLabels, Finset.product_eq_sprod, Finset.sum_sigma, Finset.sum_product,
    pptLabelWeight, pptLabelA, pptLabelC]

/-- Any selected subfamily, including the image of the actual residual
label map, obeys the same complete weighted entropy estimate. -/
theorem ppt_selected_labels_mass {A : ℝ} (hA : 0 ≤ A) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ z : ℝ in atTop,
      ∀ (H : ℕ) (δ : ℝ) (I : Finset PPTResidualLabel),
        (H : ℝ) ≤ A*Real.log (B z) → 0 < δ → 1/B z ≤ δ →
        I ⊆ pptResidualLabels (discardPrimeBound (B z)) H δ →
        (∑ l ∈ I, pptLabelWeight l) ≤ Real.exp (M*(Real.log (B z))^2) := by
  obtain ⟨M,hM,hbound⟩ := ppt_residual_labels_exponential_mass hA
  refine ⟨M,hM,?_⟩
  filter_upwards [hbound] with z hz
  intro H δ I hdim hδ hmesh hI
  calc
    _ ≤ ∑ l ∈ pptResidualLabels (discardPrimeBound (B z)) H δ, pptLabelWeight l :=
      Finset.sum_le_sum_of_subset_of_nonneg hI (fun _ _ _ => by unfold pptLabelWeight; positivity)
    _ ≤ _ := by rw [ppt_residual_labels_mass]; exact hz H δ hdim hδ hmesh

lemma ppt_residual_cells_cover (R : Finset ℕ) (label : ℕ → PPTResidualLabel) :
    ∀ n ∈ R, ∃ l ∈ R.image label, n ∈ pptResidualCell R label l := by
  classical
  intro n hn
  exact ⟨label n, Finset.mem_image.mpr ⟨n, hn, rfl⟩,
    Finset.mem_filter.mpr ⟨hn, rfl⟩⟩

lemma ppt_residual_cells_count_le (R : Finset ℕ) (label : ℕ → PPTResidualLabel) :
    (R.card : ℝ) ≤ ∑ l ∈ R.image label, ((pptResidualCell R label l).card : ℝ) := by
  classical
  exact ppt_residual_block_cover (R.image label) (pptResidualCell R label) R
    (ppt_residual_cells_cover R label) le_rfl

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTLabeledResidualCount
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum the actual residual partition using its finite arithmetic labels.
The reciprocal-factor entropy is a proved bound, not an additional input. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

/-- Once the pointwise grids have been assigned, the full finite label
space absorbs their entropy while retaining every inverse-power saving. -/
theorem ppt_labeled_residual_count (d : ℕ) (hd : 0 < d)
    {A γ : ℝ} (hA : 0 < A) (hγ : 0 < γ) (K : ℝ) :
    ∀ᶠ z : ℝ in atTop,
    ∀ (H : ℕ) (δ : ℝ) (R : Finset ℕ) (label : ℕ → PPTResidualLabel)
      (W V : PPTResidualLabel → ℝ) (Y U : PPTResidualLabel → ℕ → ℝ)
      (tail : (l : PPTResidualLabel) → Fin (pptLabelH l) → ℕ)
      (pair : (l : PPTResidualLabel) → ℕ → ShiftedPair (pptLabelB l)),
      (H : ℝ) ≤ A*Real.log (B z) → 0 < δ → 1/B z ≤ δ →
      (∀ n ∈ R, label n ∈ pptResidualLabels (discardPrimeBound (B z)) H δ) →
      (∀ l ∈ R.image label, 1 ≤ pptLabelB l ∧ pptLabelB l ≤ H ∧ pptLabelH l ≤ H) →
      (∀ l ∈ R.image label, 1 < W l ∧ 0 ≤ B (W l) ∧ W l ≤ V l) →
      (∀ l ∈ R.image label,
        1 < Y l (pptLabelB l) ∧ B (Y l (pptLabelB l)) ≤ 2*(B z)^(2/3 : ℝ)) →
      (∀ l ∈ R.image label, 0 ≤ B (V l) ∧ B (V l) ≤ 2*(B z)^(2/3 : ℝ)) →
      (∀ l ∈ R.image label, pptLabelA l = ∏ j, tail l j) →
      (∀ l ∈ R.image label, Function.Injective (tail l)) →
      (∀ l ∈ R.image label, ∀ j, IsNormalPrime (W l) (tail l j)) →
      (∀ l ∈ R.image label, ∀ j, (largestPrimeFactor (tail l j-1) : ℝ) ≤ V l) →
      (∀ l ∈ R.image label,
        -2+(∑ j ∈ Finset.Icc 1 (pptLabelB l-1),
          a j*(B (Y l j)/B z))+
          comparisonError (pptLabelB l) z (W l) (Y l) (U l) ≤ 
            -1-γ/(Real.log (B z))^3) →
      (∀ l ∈ R.image label, FordComparisonParameters (pptLabelB l) z (W l)
        (d*(pptLabelA l).totient) (pptLabelC l).totient (Y l) (U l)) →
      (∀ n ∈ R, n = pptLabelC (label n)*pptLabelA (label n)*
        ∏ j, (pair (label n) n).left j) →
      (∀ n ∈ R, FordComparisonConditions (pptLabelB (label n)) z (W (label n))
        (d*(pptLabelA (label n)).totient) (pptLabelC (label n)).totient
          (Y (label n)) (U (label n)) (pair (label n) n)) →
      (R.card : ℝ) ≤ z/((d : ℝ)*Real.log z)*(B z)^(-K) := by
  obtain ⟨M,hM,hmass⟩ := ppt_selected_labels_mass hA.le
  filter_upwards [hmass, ppt_finite_residual_block_decay d hd (M := M) hA.le hγ K]
    with z hmass hcount
  intro H δ R label W V Y U tail pair hdim hδ hmesh hlabels hlength hW hY hV
    htail hinj hnormal hsmall hexponent hparams hreal hconditions
  let I := R.image label
  have hI : I ⊆ pptResidualLabels (discardPrimeBound (B z)) H δ := by
    intro l hl
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hl
    exact hlabels n hn
  have hweights : (∑ l ∈ I,
      (1/((pptLabelA l).totient : ℝ))*(1/((pptLabelC l).totient : ℝ))) ≤ 
        Real.exp (M*(Real.log (B z))^2) := by
    simpa only [pptLabelWeight,one_div] using hmass H δ I hdim hδ hmesh hI
  have hgrouped := hcount PPTResidualLabel I pptLabelB pptLabelH pptLabelC pptLabelA
    W V Y U tail (pptResidualCell R label) pair
    (fun l hl => (hlength l hl).1)
    (fun l hl => (Nat.cast_le.mpr (hlength l hl).2.1).trans hdim)
    (fun l hl => (Nat.cast_le.mpr (hlength l hl).2.2).trans hdim)
    hW hY hV hweights htail hinj hnormal hsmall hexponent hparams
    (by
      intro l hl n hn
      change n ∈ R.filter (fun k=>label k=l) at hn
      obtain ⟨hnR,he⟩ := Finset.mem_filter.mp hn
      subst l
      exact hreal n hnR)
    (by
      intro l hl n hn
      change n ∈ R.filter (fun k=>label k=l) at hn
      obtain ⟨hnR,he⟩ := Finset.mem_filter.mp hn
      subst l
      exact hconditions n hnR)
  exact (ppt_residual_cells_count_le R label).trans hgrouped

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTWitnessCount
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite partition of actual regular residuals. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

/-- Partition any finite set of actual witnessed residuals, choose the
small tail only after fixing its integer label, and apply the saved Ford
bound. Witness multiplicities and alternative prime lists do not enter
the count. -/
theorem ppt_witnessed_residual_count (d : ℕ) (hd : 0 < d) {A : ℝ}
    (hA : 0 < A) (K : ℝ) :
    ∀ᶠ z : ℝ in atTop, ∀ (N H : ℕ) (S : ℝ) (R : Finset ℕ),
      (H:ℝ) ≤ A*Real.log (B z) → 1 < S → 0 ≤ B S →
      (∀ r∈R,Nonempty (PPTResidualGridWitness d N H z S A r)) →
      (R.card:ℝ) ≤ z/((d:ℝ)*Real.log z)*(B z)^(-K) := by
  classical
  have hγ : 0 < 1/(80*A^3) := by positivity
  filter_upwards [ppt_labeled_residual_count d hd hA hγ K,
    B_tendsto.eventually (eventually_gt_atTop (1:ℝ)),
    B_tendsto.eventually (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)))]
    with z hcount hB hlog
  intro N H S R hdim hS hBS hwitness
  let δ := 2*((Real.log (B z))^5/Real.sqrt (B z))
  have hδ : 0 < δ := by
    have hlog0 := Real.log_pos hB
    dsimp only [δ]
    positivity
  have hδrec : 1/B z ≤ δ := by
    have hh := ppt_mesh_reciprocal_lower (zero_lt_one.trans hB) hlog
    dsimp only [δ]
    have hm : 0 ≤ (Real.log (B z))^5/Real.sqrt (B z) := by
      have hlog0 := (Real.log_pos hB).le
      positivity
    linarith only [hh,hm]
  have hchoose : ∀ r : ℕ,∃ l : PPTResidualLabel,
      r∈R → ∃ w : PPTResidualGridWitness d N H z S A r,w.label=l := by
    intro r
    by_cases hr : r∈R
    · let w := Classical.choice (hwitness r hr)
      exact ⟨w.label,fun _ => ⟨w,rfl⟩⟩
    · exact ⟨pptResidualLabel 0 0 0 1 1 0 (fun i => Fin.elim0 i),fun h => (hr h).elim⟩
  choose label hlabel using hchoose
  let I := R.image label
  have hperlabel : ∀ l : PPTResidualLabel,∃ tail : Fin (pptLabelH l) → ℕ,
      l∈I →
        (1 ≤ pptLabelB l ∧ pptLabelB l ≤ H ∧ pptLabelH l ≤ H) ∧
        l∈pptResidualLabels (discardPrimeBound (B z)) H δ ∧
        (S ≤ pptLabelTerminal z N l) ∧
        (0 ≤ B (pptLabelTerminal z N l) ∧ B (pptLabelTerminal z N l) ≤ 2*(B z)^(2/3:ℝ)) ∧
        (comparisonCutoffs z (pptLabelUpper z N l) (pptLabelB l)=pptLabelTerminal z N l) ∧
        pptLabelA l=∏ i,tail i ∧ Function.Injective tail ∧
        (∀ i,IsNormalPrime S (tail i)) ∧
        (∀ i,(largestPrimeFactor (tail i-1):ℝ) ≤ pptLabelTerminal z N l) ∧
        FordComparisonParameters (pptLabelB l) z S (d*(pptLabelA l).totient)
          (pptLabelC l).totient (comparisonCutoffs z (pptLabelUpper z N l))
          (comparisonCutoffs z (pptLabelLower z l)) ∧
        -2+(∑ i ∈ Finset.Icc 1 (pptLabelB l-1),a i*(B (comparisonCutoffs z (pptLabelUpper z N l) i)/B z))+
          comparisonError (pptLabelB l) z S (comparisonCutoffs z (pptLabelUpper z N l))
            (comparisonCutoffs z (pptLabelLower z l)) ≤ -1-(1/(80*A^3))/(Real.log (B z))^3 := by
    intro l
    by_cases hl : l∈I
    · obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hl
      obtain ⟨w,hw⟩ := hlabel r hr
      rw [←hw]
      exact ⟨w.tail,fun _ => ⟨⟨w.length_pos,w.length_le,w.tail_length_le⟩,
        w.label_mem,w.terminal_normality,w.terminal_height,w.terminal_eq,w.tail_product,
        w.tail_injective,w.tail_normal,w.tail_smooth,w.parameters,w.exponent⟩⟩
    · exact ⟨fun _=>0,fun h=>(hl h).elim⟩
  choose tail htail using hperlabel
  have hpairs : ∀ (l : PPTResidualLabel) (r : ℕ),∃ pair : ShiftedPair (pptLabelB l),
      r∈pptResidualCell R label l →
        r=pptLabelC l*pptLabelA l*∏ i,pair.left i ∧
        FordComparisonConditions (pptLabelB l) z S (d*(pptLabelA l).totient)
          (pptLabelC l).totient (comparisonCutoffs z (pptLabelUpper z N l))
          (comparisonCutoffs z (pptLabelLower z l)) pair := by
    intro l r
    by_cases hr : r∈pptResidualCell R label l
    · change r ∈ R.filter (fun k=>label k=l) at hr
      obtain ⟨hrR,he⟩ := Finset.mem_filter.mp hr
      obtain ⟨w,hw⟩ := hlabel r hrR
      have hwl : w.label=l := hw.trans he
      rw [←hwl]
      exact ⟨w.pair,fun _=>⟨w.recovery,w.conditions⟩⟩
    · exact ⟨⟨fun _=>0,fun _=>0,1⟩,fun h=>(hr h).elim⟩
  choose pair hpair using hpairs
  apply hcount H δ R label (fun _=>S) (pptLabelTerminal z N)
    (fun l=>comparisonCutoffs z (pptLabelUpper z N l))
    (fun l=>comparisonCutoffs z (pptLabelLower z l)) tail pair hdim hδ hδrec
  · intro r hr
    exact (htail (label r) (Finset.mem_image.mpr ⟨r,hr,rfl⟩)).2.1
  · intro l hl
    exact (htail l hl).1
  · intro l hl
    exact ⟨hS,hBS,(htail l hl).2.2.1⟩
  · intro l hl
    rw [(htail l hl).2.2.2.2.1]
    exact ⟨Real.one_lt_exp_iff.mpr (Real.exp_pos _),(htail l hl).2.2.2.1.2⟩
  · intro l hl
    exact (htail l hl).2.2.2.1
  · intro l hl
    exact (htail l hl).2.2.2.2.2.1
  · intro l hl
    exact (htail l hl).2.2.2.2.2.2.1
  · intro l hl
    exact (htail l hl).2.2.2.2.2.2.2.1
  · intro l hl
    exact (htail l hl).2.2.2.2.2.2.2.2.1
  · intro l hl
    exact (htail l hl).2.2.2.2.2.2.2.2.2.2
  · intro l hl
    exact (htail l hl).2.2.2.2.2.2.2.2.2.1
  · intro r hr
    exact (hpair (label r) r (Finset.mem_filter.mpr ⟨hr,rfl⟩)).1
  · intro r hr
    exact (hpair (label r) r (Finset.mem_filter.mpr ⟨hr,rfl⟩)).2

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTOriginalRegular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual original-head regular class satisfies the finite comparison bound. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

theorem ppt_original_regular_count_oai {c : ℝ} (hc : 0 < c)
    (d : ℕ) (hd : 0 < d) (L : ℕ) :
    ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∀ F : ℕ→ℕ,let R:=localOriginalBad x c d L H
      (∀ r∈R,0 < F r ∧ (F r).totient=d*r.totient ∧ ¬r∣F r ∧
        largestPrimeFactor (F r)≠largestPrimeFactor r) →
      ((localWitnessRegular R F (m x)).card:ℝ) ≤ x/Real.log x*(B x)^(-4:ℝ) := by
  let A : ℝ := 1/lam+2
  have hA : 0 < A := by have hlam := lam_pos; dsimp only [A] <;> positivity
  filter_upwards [local_original_comparison_data hc d hd L,
    local_normal_candidate_normality_and_value hc d hd L] with H hdata hvalues
  filter_upwards [hdata,hvalues,ppt_regular_head_witness d hd hA,
    ppt_witnessed_residual_count d hd hA 4,m_le_log_B,
    m_tendsto.eventually (eventually_ge_atTop 1),
    (localNormalityScale_tendsto.comp m_tendsto).eventually
      (eventually_ge_atTop (largestPrimeFactor d:ℝ)),
    B_tendsto.eventually (eventually_ge_atTop (Real.exp 1)),
    eventually_gt_atTop (1:ℝ)]
    with x hdata hvalues hwitness hcount hdim hm hseed hB hx
  intro F R hF
  let T:=localWitnessRegular R F (m x)
  let S:=localNormalityScale (m x)
  have hx0 : 0 < x := zero_lt_one.trans hx
  have ht : 0 < B x := (Real.exp_pos 1).trans_le hB
  have hlog : 1 ≤ Real.log (B x) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hB
  have hdim' : ((m x+1:ℕ):ℝ) ≤ A*Real.log (B x) := by
    dsimp only [A]
    push_cast
    have he : (1/lam+2)*Real.log (B x)=Real.log (B x)/lam+2*Real.log (B x) := by ring
    rw [he]
    linarith only [hdim,hlog]
  have hS : Real.exp (Real.exp 1) ≤ S := by
    apply Real.exp_le_exp.mpr
    apply Real.exp_le_exp.mpr
    have hmr : (1:ℝ) ≤ m x := by exact_mod_cast hm
    exact one_le_pow₀ hmr
  have hS1 : 1 < S := (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)).trans_le hS
  have hBS : B S=(m x:ℝ)^4 := by simp only [S,localNormalityScale,B,Real.log_exp]
  have hBS0 : 0 ≤ B S := by rw [hBS]; positivity
  have hheight : B S ≤ ((m x+1:ℕ):ℝ)^4 := by
    rw [hBS]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by push_cast <;> linarith) 4
  have hTR : T⊆R := by intro r hr; exact (local_regular_witness_properties hr).1
  have hTN (r) (hr : r∈T) : r∈localNormalCandidates x c d L H :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp (hTR hr)).1).1
  have hsmall : (T.card:ℝ) ≤ x/((d:ℝ)*Real.log x)*(B x)^(-4:ℝ) := by
    apply hcount (m x-H+1) (m x+1) S T hdim' hS1 hBS0
    intro r hr
    obtain ⟨p,q,he,hp,ho,hgeom,hq,hqp,_htail,hhead,hqn,hpn,hq3,hp3,hcap⟩ :=
      hdata r (hTN r hr)
    let P : Fin (m x-H+1)→ℕ := Fin.cons q p
    let v := primePrefixCoord p
    let ι : Fin ((m x-H+1)-1)↪o Fin (m x-H) :=
      (Fin.castOrderIso (by omega)).toOrderEmbedding
    have hP (i) : IsNormalPrime S (P i) := by
      refine Fin.cases hqn (fun j=>hpn j) i
    have hP3 (i) : 3 ≤ P i := by
      refine Fin.cases hq3 (fun j=>hp3 j) i
    have hPo : StrictAnti P := (Fin.strictMono_cons (α:=OrderDual ℕ)).mpr ⟨hqp,ho⟩
    have hPp (i) : (P i).Prime := (hP i).1
    have hprod : r=∏ i,P i := by simpa only [P,Fin.prod_cons] using he
    have hrpos : 0 < r := by rw [hprod]; exact Finset.prod_pos (fun i _=>(hPp i).pos)
    have hpred (i) : (P i-1:ℕ) ≤ x := by
      have hdiv : P i∣r := by rw [hprod]; exact Finset.dvd_prod_of_mem P (Finset.mem_univ i)
      exact (Nat.cast_le.mpr (prime_predecessor_le_seed_totient hrpos (hPp i) hdiv hd)).trans
        (hvalues r (hTN r hr)).1
    have hcap' (i : Fin (m x-H+1)) (hi : 0 < i.val) : B (P i) ≤ (4/5:ℝ)*B x := by
      let j : Fin (m x-H) := ⟨i.val-1,by have := i.isLt; omega⟩
      have heq : j.succ=i := by
        apply Fin.ext
        change (i.val-1)+1=i.val
        omega
      rw [←heq]
      change B (p j) ≤ _
      exact (hcap j).trans (mul_le_mul_of_nonneg_right (by norm_num : (19/25:ℝ) ≤ 4/5) ht.le)
    have hcoords (i : Fin ((m x-H+1)-1)) : v (ι i)=B (P ⟨i.val+1,by omega⟩) := by
      let j : Fin (m x-H) := ι i
      have heq : j.succ=(⟨i.val+1,by omega⟩ : Fin (m x-H+1)) := by apply Fin.ext; rfl
      rw [←heq]
      rfl
    have hregular := local_regular_witness_properties hr
    have hvalue := hF r (hTR hr)
    apply hwitness (m x) (m x-H) (m x-H+1) (m x+1) (F r) r P v ι
      (B x) (c/2) S (by omega) (Nat.sub_le _ _) (by omega) hdim' le_rfl
      (by linarith) hgeom hcoords hcap' hS hheight hP hP3 hPo
      hvalue.1 hvalue.2.1 hprod hseed hregular.2.2.1 hregular.2.2.2 hregular.2.1
    · rw [←ordered_prime_product_largest (by omega) P hPp hPo,←hprod]
      exact hvalue.2.2.2
    · exact hpred
    · rw [hvalue.2.1]
      exact (hvalues r (hTN r hr)).1
    · change x^(9/10:ℝ) ≤ (q:ℝ)
      exact hhead.le
  apply hsmall.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht.le _)
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  apply div_le_div_of_nonneg_left hx0.le (Real.log_pos hx)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hd1 (Real.log_pos hx).le

end TotientAsymptotic

end

end OAI
end

theorem solution : type_of% @OAI.TotientAsymptotic.ppt_original_regular_count_oai := @OAI.TotientAsymptotic.ppt_original_regular_count_oai
