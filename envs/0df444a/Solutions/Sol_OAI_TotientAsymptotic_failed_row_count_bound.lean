-- Prove2me | solution 1 for OAI.TotientAsymptotic.failed_row_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:34:42.301649+00:00
-- url     : https://prove2.me/submissions/8c2579f2-840b-4315-a9e4-025bef19a4d8

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
import Theorems.Thm_OAI_TotientAsymptotic_counting_envelope_real_bound
import Theorems.Thm_OAI_TotientAsymptotic_exceptional_row_reciprocal_mass
import Theorems.Thm_OAI_TotientAsymptotic_failed_row_value_count

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_OmegaReciprocal
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete Euler-product moment for the remaining-factor exclusion.
The exponent three is sufficient for the application. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma omegaReciprocal_nonneg (n : ℕ) : 0 ≤ omegaReciprocal n := by
  change 0 ≤ (3/2 : ℝ)^n.primeFactorsList.length/(n : ℝ)
  positivity

lemma omegaReciprocal_prime {p : ℕ} (hp : p.Prime) : omegaReciprocal p=(3/2 : ℝ)/p := by
  simp [omegaReciprocal,Nat.primeFactorsList_prime hp]

lemma omegaReciprocal_prime_norm {p : ℕ} (hp : p.Prime) : ‖omegaReciprocal p‖ < 1 := by
  rw [Real.norm_eq_abs,abs_of_nonneg (omegaReciprocal_nonneg p),omegaReciprocal_prime hp]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  exact (div_lt_one (by linarith)).mpr (by linarith)

lemma omega_euler_factor_le {p : ℕ} (hp : p.Prime) :
    (1-omegaReciprocal p)⁻¹ ≤ ((p : ℝ)/(p-1))^3 := by
  rw [omegaReciprocal_prime hp]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hs : (0 : ℝ) < p-1 := by linarith
  have ht : (0 : ℝ) < p-3/2 := by linarith
  have he : (1-(3/2 : ℝ)/(p : ℝ))⁻¹=(p : ℝ)/(p-3/2) := by field_simp
  rw [he,div_pow]
  apply (div_le_div_iff₀ ht (pow_pos hs 3)).mpr
  nlinarith [sq_nonneg ((p : ℝ)-2)]

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SmoothCofactorMoment
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete Rankin moment for the smooth cofactor discarded in extraction. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma powerReciprocal_nonneg (σ : ℝ) (n : ℕ) : 0 ≤ powerReciprocal σ n := by
  change 0 ≤ (n : ℝ)^σ/(n : ℝ)
  positivity

lemma powerReciprocal_prime_norm {σ : ℝ} (hσ : σ < 1) {p : ℕ} (hp : p.Prime) :
    ‖powerReciprocal σ p‖ < 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  rw [Real.norm_eq_abs,abs_of_nonneg (powerReciprocal_nonneg σ p)]
  change (p : ℝ)^σ/(p : ℝ) < 1
  rw [div_lt_one (zero_lt_one.trans hp1)]
  simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt hp1 hσ

lemma powerReciprocal_euler_factor {σ : ℝ} (hσ : σ < 1) {p : ℕ} (hp : p.Prime)
    (hpow : (p : ℝ)^σ ≤ 3/2) :
    (1-powerReciprocal σ p)⁻¹ ≤ ((p : ℝ)/(p-1))^3 := by
  have hnorm := powerReciprocal_prime_norm hσ hp
  rw [Real.norm_eq_abs,abs_of_nonneg (powerReciprocal_nonneg σ p)] at hnorm
  have hb : powerReciprocal σ p ≤ omegaReciprocal p := by
    rw [omegaReciprocal_prime hp]
    exact div_le_div_of_nonneg_right hpow (Nat.cast_nonneg _)
  have hω := omegaReciprocal_prime_norm hp
  rw [Real.norm_eq_abs,abs_of_nonneg (omegaReciprocal_nonneg p)] at hω
  have hh := one_div_le_one_div_of_le (by linarith : 0 < 1-omegaReciprocal p)
    (sub_le_sub_left hb 1)
  rw [one_div,one_div] at hh
  exact hh.trans (omega_euler_factor_le hp)

lemma smooth_power_reciprocal_mass {σ : ℝ} (hσ : σ < 1) (N : ℕ) (Q : Finset ℕ)
    (hQ : ∀ n ∈ Q, 0 < n ∧ largestPrimeFactor n ≤ N)
    (hpow : ∀ p : ℕ, p.Prime → p ≤ N → (p : ℝ)^σ ≤ 3/2) :
    (∑ n ∈ Q, powerReciprocal σ n) ≤ (primeEulerProduct N)^3 := by
  classical
  let S := Finset.Icc 2 N
  have hm (n : ℕ) (hn : n ∈ Q) : n ∈ Nat.factoredNumbers S := by
    refine ⟨(hQ n hn).1.ne',?_⟩
    intro p hp
    exact Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactorsList hp).two_le,
      (primeFactor_le_largest hp).trans (hQ n hn).2⟩
  let e : {n // n ∈ Q} → Nat.factoredNumbers S := fun n => ⟨n.1,hm n.1 n.2⟩
  let T : Finset (Nat.factoredNumbers S) := Q.attach.image e
  have he : Function.Injective e := by
    intro n m h
    apply Subtype.ext
    exact congrArg (fun z : Nat.factoredNumbers S => z.val) h
  have hsum : (∑ n ∈ Q, powerReciprocal σ n) = ∑ n ∈ T, powerReciprocal σ n := by
    dsimp only [T]
    rw [Finset.sum_image (fun n _ m _ h => he h)]
    exact (Finset.sum_attach Q (fun n : ℕ => powerReciprocal σ n)).symm
  have hs := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := powerReciprocal σ) (fun {_} hp => powerReciprocal_prime_norm hσ hp) S
  calc
    _ = ∑ n ∈ T, powerReciprocal σ n := hsum
    _ ≤ ∑' n : Nat.factoredNumbers S, powerReciprocal σ n :=
      hs.1.of_norm.sum_le_tsum T (fun n _ => powerReciprocal_nonneg σ n)
    _ = ∏ p ∈ S with p.Prime, (1-powerReciprocal σ p)⁻¹ := hs.2.tsum_eq
    _ ≤ ∏ p ∈ S with p.Prime, ((p : ℝ)/(p-1))^3 := by
      apply Finset.prod_le_prod
      · intro p hp
        have hh := powerReciprocal_prime_norm hσ (Finset.mem_filter.mp hp).2
        rw [Real.norm_eq_abs,abs_of_nonneg (powerReciprocal_nonneg σ p)] at hh
        exact inv_nonneg.mpr (by linarith)
      · intro p hp
        exact powerReciprocal_euler_factor hσ (Finset.mem_filter.mp hp).2
          (hpow p (Finset.mem_filter.mp hp).2 (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2)
    _ = _ := by rw [Finset.prod_pow]; rfl

lemma totient_ratio_le_eulerProduct_of_smooth {n N : ℕ} (hn : 0 < n)
    (hs : largestPrimeFactor n ≤ N) : (n : ℝ)/n.totient ≤ primeEulerProduct N := by
  rw [totient_ratio_product hn]
  apply Finset.prod_le_prod_of_subset_of_one_le
  · intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hprime.two_le,
      (primeFactor_le_largest ((Nat.mem_primeFactorsList_iff_dvd hn.ne' hprime).mpr
        (Nat.dvd_of_mem_primeFactors hp))).trans hs⟩,hprime⟩
  · intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  · intro p hp _
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
    apply (le_div_iff₀ (by linarith : (0 : ℝ) < p-1)).mpr
    linarith

lemma quarter_log_power {N p : ℕ} (hN : 2 ≤ N) (hp : p.Prime) (hpN : p ≤ N) :
    (p : ℝ)^(1/(4*Real.log N)) ≤ 3/2 := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hl := Real.log_le_log hp0 (show (p : ℝ) ≤ N by exact_mod_cast hpN)
  rw [Real.rpow_def_of_pos hp0]
  have hexp : Real.exp (1/4 : ℝ) ≤ 3/2 := by
    have hh := Real.exp_bound_div_one_sub_of_interval (by norm_num : (0 : ℝ) ≤ 1/4)
      (by norm_num : (1/4 : ℝ) < 1)
    norm_num at hh
    linarith
  apply (Real.exp_le_exp.mpr ?_).trans hexp
  rw [mul_one_div]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4*Real.log N)).mpr
  convert hl using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma quarter_log_exponent_lt_one {N : ℕ} (hN : 2 ≤ N) : 1/(4*Real.log N) < (1 : ℝ) := by
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ)<2) (show (2 : ℝ) ≤ N by exact_mod_cast hN)
  have hlog2 := Real.log_two_gt_d9
  apply (div_lt_one (by nlinarith : (0 : ℝ)<4*Real.log N)).mpr
  nlinarith

/-- A coarse fourth power of the Mertens product suffices for the tail;
no asymptotic estimate for smooth integers is assumed. -/
theorem smooth_cofactor_power_mass {N : ℕ} (hN : 2 ≤ N) (Q : Finset ℕ)
    (hQ : ∀ n ∈ Q, 0 < n ∧ largestPrimeFactor n ≤ N) :
    (∑ n ∈ Q, (n : ℝ)^(1/(4*Real.log N))/(n.totient : ℝ)) ≤ (primeEulerProduct N)^4 := by
  let σ := 1/(4*Real.log N)
  have hE : 0 ≤ primeEulerProduct N := by
    apply Finset.prod_nonneg
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  calc
    _ ≤ primeEulerProduct N*∑ n ∈ Q, powerReciprocal σ n := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n hn
      have hn0 : (0 : ℝ)<n := by exact_mod_cast (hQ n hn).1
      have hb := mul_le_mul_of_nonneg_right
        (totient_ratio_le_eulerProduct_of_smooth (hQ n hn).1 (hQ n hn).2)
        (powerReciprocal_nonneg σ n)
      convert hb using 1
      all_goals try with_reducible_and_instances rfl
      dsimp [powerReciprocal,σ]
      field_simp
    _ ≤ primeEulerProduct N*(primeEulerProduct N)^3 :=
      mul_le_mul_of_nonneg_left
        (smooth_power_reciprocal_mass (quarter_log_exponent_lt_one hN) N Q hQ
          (fun p hp hpN => quarter_log_power hN hp hpN)) hE
    _ = _ := by ring

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SmoothSuffix
attribute [-instance] _root_.instMeasurableSpace
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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SmoothCofactorTail
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

/-- The exponential tail needed for the actual smooth-cofactor truncation. -/
theorem smooth_cofactor_rankin {N : ℕ} (hN : 2 ≤ N) (Z : ℝ) (Q : Finset ℕ)
    (hQ : ∀ n ∈ Q, 0 < n ∧ largestPrimeFactor n ≤ N ∧ Z < Real.log n) :
    (∑ n ∈ Q, (n.totient : ℝ)⁻¹) ≤
      Real.exp (-Z/(4*Real.log N))*(primeEulerProduct N)^4 := by
  let σ := 1/(4*Real.log N)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have hσ : 0 < σ := by dsimp [σ] <;> positivity
  calc
    _ ≤ Real.exp (-σ*Z)*∑ n ∈ Q, (n : ℝ)^σ/(n.totient : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n hn
      have hn0 : (0 : ℝ)<n := by exact_mod_cast (hQ n hn).1
      have hφ : 0 < (n.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (hQ n hn).1
      have hm : 1 ≤ Real.exp (-σ*Z)*(n : ℝ)^σ := by
        rw [Real.rpow_def_of_pos hn0,← Real.exp_add]
        exact Real.one_le_exp_iff.mpr (by nlinarith [(hQ n hn).2.2])
      have hh := mul_le_mul_of_nonneg_right hm (inv_pos.mpr hφ).le
      simpa only [one_mul,div_eq_mul_inv,mul_assoc] using hh
    _ ≤ Real.exp (-σ*Z)*(primeEulerProduct N)^4 :=
      mul_le_mul_of_nonneg_left (smooth_cofactor_power_mass hN Q (fun n hn =>
        ⟨(hQ n hn).1,(hQ n hn).2.1⟩)) (Real.exp_pos _).le
    _ = _ := by congr 2; dsimp [σ] <;> ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SmoothCountingSplit
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite counting version of the elementary smooth-number Rankin bound. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma card_le_endpoint_reciprocal (Q : Finset ℕ) (x : ℝ)
    (hQ : ∀ n ∈ Q,0 < n ∧ (n:ℝ) ≤ x) :
    (Q.card:ℝ) ≤ x*(∑ n ∈ Q,(n:ℝ)⁻¹) := by
  rw [Finset.mul_sum]
  calc
    (Q.card:ℝ) = ∑ _n ∈ Q,(1:ℝ) := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro n hn
      have hn0 : (0:ℝ) < n := by exact_mod_cast (hQ n hn).1
      exact (one_le_div hn0).mpr (hQ n hn).2

lemma smooth_counting_split {K : ℕ} (hK : 2 ≤ K) (N : ℕ) (Z : ℝ)
    (Q : Finset ℕ) (hQ : ∀ n ∈ Q,0 < n ∧ n ≤ N ∧ largestPrimeFactor n ≤ K) :
    (Q.card:ℝ) ≤ Real.exp Z+
      N*Real.exp (-Z/(4*Real.log K))*(primeEulerProduct K)^4 := by
  classical
  let A : Finset ℕ := Q.filter (fun n : ℕ => (n:ℝ) ≤ Real.exp Z)
  let D : Finset ℕ := Q.filter (fun n : ℕ => ¬(n:ℝ) ≤ Real.exp Z)
  have hA : (A.card:ℝ) ≤ Real.exp Z := by
    have hs : A ⊆ Finset.Icc 1 ⌊Real.exp Z⌋₊ := by
      intro n hn
      obtain ⟨hn,hh⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_Icc.mpr ⟨(hQ n hn).1,Nat.le_floor hh⟩
    have hh : A.card ≤ ⌊Real.exp Z⌋₊ := by simpa using Finset.card_le_card hs
    exact (show (A.card:ℝ) ≤ (⌊Real.exp Z⌋₊:ℝ) by exact_mod_cast hh).trans
      (Nat.floor_le (Real.exp_pos _).le)
  have hD := card_le_endpoint_reciprocal D N (by
    intro n hn
    have hh := hQ n (Finset.mem_filter.mp hn).1
    exact ⟨hh.1,by exact_mod_cast hh.2.1⟩)
  have hrec : (∑ n ∈ D,(n:ℝ)⁻¹) ≤ ∑ n ∈ D,(n.totient:ℝ)⁻¹ := by
    apply Finset.sum_le_sum
    intro n hn
    have hn0 := (hQ n (Finset.mem_filter.mp hn).1).1
    apply (inv_le_inv₀ (by exact_mod_cast hn0)
      (by exact_mod_cast Nat.totient_pos.mpr hn0)).mpr
    exact_mod_cast Nat.totient_le n
  have htail := smooth_cofactor_rankin hK Z D (by
    intro n hn
    obtain ⟨hn,hh⟩ := Finset.mem_filter.mp hn
    have hz : Real.exp Z < (n:ℝ) := lt_of_not_ge hh
    exact ⟨(hQ n hn).1,(hQ n hn).2.2,(Real.lt_log_iff_exp_lt (by exact_mod_cast (hQ n hn).1)).mpr hz⟩)
  have hcard : (Q.card:ℝ) = (A.card:ℝ)+(D.card:ℝ) := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not (s:=Q) (p:=fun n => (n:ℝ) ≤ Real.exp Z)).symm
  rw [hcard]
  have hh := mul_le_mul_of_nonneg_left (hrec.trans htail) (Nat.cast_nonneg N : (0:ℝ) ≤ N)
  calc
    _ ≤ Real.exp Z+(N*(Real.exp (-Z/(4*Real.log K))*(primeEulerProduct K)^4)) :=
      add_le_add hA (hD.trans hh)
    _ = _ := by ring

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FiniteDyadicCubic
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A convergent reciprocal tail from finite cubic-logarithmic count bounds. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma finite_reciprocal_cube_tail (K L : ℕ) (hK : 1 ≤ K) :
    (∑ k ∈ Finset.Icc K L,((k:ℝ)^3)⁻¹) ≤ 2/(K:ℝ)^2 := by
  have hK0 : (0:ℝ) < K := by exact_mod_cast hK
  have hsets : Finset.Icc K L=Finset.Ioo (K-1) (L+1) := by ext k; simp; omega
  have hs : (∑ k ∈ Finset.Icc K L,((k:ℝ)^2)⁻¹) ≤ 2/(K:ℝ) := by
    rw [hsets]
    have hh := sum_Ioo_inv_sq_le (α:=ℝ) (K-1) (L+1)
    have he : ((K-1:ℕ):ℝ)+1=K := by exact_mod_cast (show K-1+1=K by omega)
    rwa [he] at hh
  calc
    _ ≤ ∑ k ∈ Finset.Icc K L,(K:ℝ)⁻¹*((k:ℝ)^2)⁻¹ := by
      apply Finset.sum_le_sum
      intro k hk
      have hkK : (K:ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
      have hh := mul_le_mul_of_nonneg_right (inv_anti₀ hK0 hkK) (inv_nonneg.mpr (sq_nonneg (k:ℝ)))
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      ring
    _ = (K:ℝ)⁻¹*(∑ k ∈ Finset.Icc K L,((k:ℝ)^2)⁻¹) := (Finset.mul_sum ..).symm
    _ ≤ (K:ℝ)⁻¹*(2/K) := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hK0.le)
    _ = _ := by ring

lemma finite_dyadic_cubic_mass {α : Type*} (Q : Finset α)
    (n : α → ℕ) (v : α → ℝ) (K L : ℕ) (hK : 1 ≤ K) {A : ℝ} (hA : 0 ≤ A)
    (hn : ∀ a ∈ Q,n a ∈ Finset.Icc K L)
    (hlo : ∀ a ∈ Q,(2:ℝ)^(n a)/4 ≤ v a)
    (hcount : ∀ k ∈ Finset.Icc K L,((Q.filter (fun a => n a=k)).card:ℝ) ≤
      A*(2:ℝ)^k/(k:ℝ)^3) :
    (∑ a ∈ Q,(v a)⁻¹) ≤ 8*A/(K:ℝ)^2 := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to hn]
  have hf (k : ℕ) (hk : k ∈ Finset.Icc K L) :
      (∑ a ∈ Q.filter (fun a => n a=k),(v a)⁻¹) ≤ 4*A*((k:ℝ)^3)⁻¹ := by
    have hy : (0:ℝ) < (2:ℝ)^k := by positivity
    calc
      _ ≤ ∑ _a ∈ Q.filter (fun a => n a=k),4/(2:ℝ)^k := by
        apply Finset.sum_le_sum
        intro a ha
        obtain ⟨ha,he⟩ := Finset.mem_filter.mp ha
        have hh := hlo a ha
        rw [he] at hh
        simpa only [inv_div] using inv_anti₀ (div_pos hy (by norm_num)) hh
      _ = ((Q.filter (fun a => n a=k)).card:ℝ)*(4/(2:ℝ)^k) := by simp
      _ ≤ (A*(2:ℝ)^k/(k:ℝ)^3)*(4/(2:ℝ)^k) :=
        mul_le_mul_of_nonneg_right (hcount k hk) (by positivity)
      _ = _ := by field_simp
  calc
    _ ≤ ∑ k ∈ Finset.Icc K L,4*A*((k:ℝ)^3)⁻¹ := Finset.sum_le_sum hf
    _ = 4*A*(∑ k ∈ Finset.Icc K L,((k:ℝ)^3)⁻¹) := (Finset.mul_sum ..).symm
    _ ≤ 4*A*(2/(K:ℝ)^2) := mul_le_mul_of_nonneg_left (finite_reciprocal_cube_tail K L hK) (by positivity)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FiniteDyadicLogTail
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite partial summation for logarithmic sieve bounds. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma finite_dyadic_log_range (Q : Finset ℕ) (hQ : Q.Nonempty)
    {U : ℝ} (hU : 1 < U) (hlo : ∀ q ∈ Q,U ≤ q) :
    ∃ K L : ℕ, 1 ≤ K ∧ Real.log U ≤ (K:ℝ)*Real.log 2 ∧
      (∀ q ∈ Q,Nat.clog 2 q ∈ Finset.Icc K L) ∧
      (∀ q ∈ Q,(2:ℝ)^(Nat.clog 2 q)/4 ≤ q) := by
  classical
  let T := Q.image (Nat.clog 2)
  have hT : T.Nonempty := hQ.image _
  let K := T.min' hT
  obtain ⟨q,hq,heq⟩ := Finset.mem_image.mp (Finset.min'_mem T hT)
  have hq1 : 1 < q := by exact_mod_cast (hU.trans_le (hlo q hq))
  have hb := dyadic_nat_bounds hq1
  rw [heq] at hb
  refine ⟨K,Q.sup (Nat.clog 2),hb.1,?_,?_,?_⟩
  · calc
      Real.log U ≤ Real.log (q:ℝ) := Real.log_le_log (zero_lt_one.trans hU) (hlo q hq)
      _ ≤ Real.log ((2:ℝ)^K) := Real.log_le_log (by exact_mod_cast (show 0 < q by omega)) hb.2.2
      _ = _ := dyadic_endpoint_log K
  · intro q hq
    exact Finset.mem_Icc.mpr ⟨Finset.min'_le T _ (Finset.mem_image.mpr ⟨q,hq,rfl⟩),
      Finset.le_sup hq⟩
  · intro q hq
    have hq1 : 1 < q := by exact_mod_cast (hU.trans_le (hlo q hq))
    have hh := (dyadic_nat_bounds hq1).2.1
    have hp : 0 < (2:ℝ)^(Nat.clog 2 q) := by positivity
    linarith

lemma finite_dyadic_log_cube_tail (Q : Finset ℕ) {U A : ℝ}
    (hU : 1 < U) (hA : 0 ≤ A) (hlo : ∀ q ∈ Q,U ≤ q)
    (hc : ∀ k : ℕ,1 ≤ k → ((Q.filter (fun q => Nat.clog 2 q=k)).card:ℝ) ≤
      A*(2:ℝ)^k/(k:ℝ)^3) :
    (∑ q ∈ Q,(q:ℝ)⁻¹) ≤ 8*A*(Real.log 2)^2/(Real.log U)^2 := by
  classical
  by_cases hQ : Q.Nonempty
  · obtain ⟨K,L,hK,hlog,hn,hv⟩ := finite_dyadic_log_range Q hQ hU hlo
    have hh := finite_dyadic_cubic_mass Q (Nat.clog 2) (fun q => (q:ℝ))
      K L hK hA hn hv (fun k hk => hc k (hK.trans (Finset.mem_Icc.mp hk).1))
    have hK0 : (0:ℝ) < K := by exact_mod_cast hK
    have hLU : 0 < Real.log U := Real.log_pos hU
    have hs := pow_le_pow_left₀ hLU.le hlog 2
    apply hh.trans
    apply (div_le_div_iff₀ (sq_pos_of_pos hK0) (sq_pos_of_pos hLU)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hs (show 0 ≤ 8*A by positivity)]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hQ]
    simp only [Finset.sum_empty]
    have hLU : 0 < Real.log U := Real.log_pos hU
    have hlog : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
    positivity

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BootstrapSquareDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The square-divisor cutoff is much larger than every fixed logarithmic power. -/
noncomputable section
namespace TotientAsymptotic

lemma exp_quadratic_lower {u : ℝ} (hu : 0 ≤ u) : u^2/4 ≤ Real.exp u := by
  have he := Real.add_one_le_exp (u/2)
  have hhalf : 0 ≤ u/2 := by linarith
  have hs : (u/2)^2 ≤ (Real.exp (u/2))^2 :=
    pow_le_pow_left₀ hhalf (by linarith) 2
  have hid : (Real.exp (u/2))^2=Real.exp u := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  rw [hid] at hs
  nlinarith only [hs]

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BoundedTotientMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reciprocal mass of all totient values below a finite endpoint. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem bounded_totient_reciprocal_mass : ∃ C : ℝ,0 < C ∧ ∀ U : ℝ,4 ≤ U → 1 ≤ B U →
    ∀ Q : Finset ℕ,(∀ v ∈ Q,IsTotient v ∧ (v:ℝ) ≤ U) →
    (∑ v ∈ Q,(v:ℝ)⁻¹) ≤ C*Real.exp (10*(Real.log (B U+4))^2) := by
  obtain ⟨C,hC,henv⟩ := counting_envelope_real_bound
  refine ⟨1+4*C,by positivity,?_⟩
  intro U hU hBU Q hQ
  have hi := counting_dyadic_index_bounds hU
  let J := countingDyadicIndex U
  have hm := dyadic_totient_reciprocal_mass hi.1 Q (by
    intro v hv
    exact ⟨(hQ v hv).1,(hQ v hv).2.trans hi.2.1⟩)
  have hJ1 : (1:ℝ) ≤ J := by exact_mod_cast hi.1
  have hJ0 : (0:ℝ) < J := by linarith only [hJ1]
  have hlog0 : 0 ≤ 1+Real.log J := by linarith [Real.log_nonneg hJ1]
  have hlog : 1+Real.log J ≤ B U+4 := by
    have hh := Real.log_le_log hJ0 (show (J:ℝ) ≤ (J:ℝ)+1 by linarith)
    have ht := hi.2.2
    change 1+Real.log ((J:ℝ)+1) ≤ B U+4 at ht
    linarith only [hh,ht]
  have henvU := henv U hU
  have hp := mul_le_mul henvU hlog hlog0 (by positivity)
  have hbase : 0 < B U+4 := by linarith only [hBU]
  have hl : 1 ≤ Real.log (B U+4) := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ)<3) (show (3:ℝ) ≤ B U+4 by linarith)
    linarith [Real.log_three_gt_d9]
  have hgrow : Real.exp (9*(Real.log (B U+4))^2)*(B U+4) ≤
      Real.exp (10*(Real.log (B U+4))^2) := by
    calc
      _ = Real.exp (9*(Real.log (B U+4))^2+Real.log (B U+4)) := by
        rw [Real.exp_add,Real.exp_log hbase]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith only [hl])
  have hone : 1 ≤ Real.exp (10*(Real.log (B U+4))^2) := Real.one_le_exp (by positivity)
  have hh := mul_le_mul_of_nonneg_left hgrow hC.le
  nlinarith only [hm,hp,hh,hone]

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_DyadicCoordinateRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A relative row failure persists at the next dyadic endpoint. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma dyadic_coordinate_loss {v : ℕ} (hv : 2 ≤ v) :
    B ((2:ℝ)^(Nat.clog 2 v))-1 ≤ B (v:ℝ) := by
  have hd := dyadic_nat_bounds (show 1 < v by omega)
  have hx : (1:ℝ) < (2:ℝ)^(Nat.clog 2 v) :=
    one_lt_pow₀ (by norm_num) (by omega)
  have hmono : B ((2:ℝ)^(Nat.clog 2 v)) ≤ B (2*(v:ℝ)) := by
    apply Real.log_le_log (Real.log_pos hx)
    apply Real.log_le_log (by positivity)
    linarith only [hd.2.1]
  have hvR : (2:ℝ) ≤ v := by exact_mod_cast hv
  linarith only [hmono,double_log_double_le hvR]

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

lemma failed_row_cofactor {x ω : ℝ} {n L j : ℕ} (hjL : j ≤ L)
    (hxi : xi x j=1+ω)
    (hfail : xi x j*fordPrimeCoordinate n j < fordRowSum L (fordPrimeCoordinate n) j) :
    (1+ω)*fordPrimeCoordinate (fordCofactor n j) 0 <
      ∑ i : Fin (L-j), a (i.val+1)*fordPrimeCoordinate (fordCofactor n j) (i.val+1) := by
  rw [fordCofactor_coordinate,Nat.add_zero]
  rwa [hxi,fordRowSum_cofactor hjL] at hfail

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordLargestPrime
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The leading Ford prime is exactly the largest prime factor, with padding 1. -/
noncomputable section
namespace TotientAsymptotic

lemma fordPrime_zero_eq_largest (n : ℕ) : fordPrime n 0=largestPrimeFactor n := by
  apply le_antisymm
  · by_cases hi : 0 < n.primeFactorsList.length
    · rw [fordPrime_eq_get hi]
      exact primeFactor_le_largest (List.mem_reverse.mp (List.getElem_mem _))
    · have he : fordPrime n 0=1 := by
        unfold fordPrime
        rw [List.getElem?_eq_none (by simp only [List.length_reverse]; omega)]
        rfl
      rw [he]
      exact le_max_left _ _
  · apply largestPrimeFactor_le_of_prime_divisors (fordPrime_pos n 0)
    intro p hp hpn hn
    have hm : p ∈ n.primeFactorsList.reverse :=
      List.mem_reverse.mpr ((Nat.mem_primeFactorsList_iff_dvd hn hp).mpr hpn)
    obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hm
    have hi' : i < n.primeFactorsList.length := by simpa using hi
    simpa only [fordPrime_eq_get hi'] using fordPrime_antitone (by omega) hi' (Nat.zero_le i)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LargeHeadRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A failed row with a sufficiently large leading prime is a relative row failure. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma large_head_log_budget {b ω : ℝ} (hb : 1 ≤ b) (hω : 0 < ω)
    (hsize : (8000/ω)^2 ≤ b) : 4*Real.log (1000*b) ≤ ω*b := by
  have hb0 : 0 ≤ b := by linarith
  have hr : 1 ≤ Real.sqrt b := (Real.le_sqrt (by norm_num) hb0).mpr (by simpa using hb)
  have hl := Real.log_le_rpow_div hb0 (by norm_num : (0:ℝ)<1/2)
  rw [← Real.sqrt_eq_rpow] at hl
  have hs : 8000/ω ≤ Real.sqrt b := (Real.le_sqrt (by positivity) hb0).mpr hsize
  have hw : 8000 ≤ ω*Real.sqrt b := by
    have hh := (div_le_iff₀ hω).mp hs
    linarith only [hh]
  have hm := mul_le_mul_of_nonneg_right hw (Real.sqrt_nonneg b)
  rw [mul_assoc,Real.mul_self_sqrt hb0] at hm
  rw [Real.log_mul (by norm_num : (1000:ℝ)≠0) (by linarith : b≠0)]
  have hc := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<1000)
  nlinarith only [hl,hr,hm,hc]

lemma large_head_coordinate {v n : ℕ} (hv : 1 < v) (hB : 0 < B (v:ℝ))
    (hhead : Real.exp (Real.log v/(1000*B v)) ≤ (largestPrimeFactor n:ℝ)) :
    B v-Real.log (1000*B v) ≤ fordPrimeCoordinate n 0 := by
  rw [← fordPrime_zero_eq_largest n] at hhead
  have hvR : (1:ℝ) < v := by exact_mod_cast hv
  have ht : 0 < Real.log v/(1000*B v) := div_pos (Real.log_pos hvR) (by positivity)
  have hp : (0:ℝ) < fordPrime n 0 := (Real.exp_pos _).trans_le hhead
  have hl : Real.log v/(1000*B v) ≤ Real.log (fordPrime n 0) :=
    (Real.le_log_iff_exp_le hp).mpr hhead
  have hh := Real.log_le_log ht hl
  rw [Real.log_div (Real.log_pos hvR).ne' (by positivity : 1000*B (v:ℝ)≠0)] at hh
  exact hh.trans (le_max_right _ _)

lemma large_head_row_relative {v n k : ℕ} {ω : ℝ}
    (hv : 1 < v) (hB : 1 ≤ B (v:ℝ)) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hsize : (8000/ω)^2 ≤ B (v:ℝ))
    (hhead : Real.exp (Real.log v/(1000*B v)) ≤ (largestPrimeFactor n:ℝ))
    (hrow : (1+ω)*fordPrimeCoordinate n 0 <
      ∑ i : Fin k,a (i.val+1)*fordPrimeCoordinate n (i.val+1)) :
    (1+ω/2)*B v < ∑ i : Fin k,a (i.val+1)*fordPrimeCoordinate n (i.val+1) := by
  have hh := large_head_coordinate hv (by linarith) hhead
  have hbudget := large_head_log_budget hB hω hsize
  have hl : 0 ≤ Real.log (1000*B (v:ℝ)) := Real.log_nonneg (by linarith only [hB])
  have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ 1+ω by linarith)
  have he := mul_le_mul_of_nonneg_right hω1 hl
  nlinarith only [hm,he,hbudget,hrow]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SmoothTotientCount
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth-preimage counting directly bounds distinct totient values. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma smooth_totient_count_of_preimage {K N : ℕ} (hK : 2 ≤ K) (Z : ℝ)
    (Q : Finset ℕ)
    (hQ : ∀ v ∈ Q,∃ n : ℕ,0 < n ∧ n.totient=v ∧ n ≤ N ∧ largestPrimeFactor n ≤ K) :
    (Q.card:ℝ) ≤ Real.exp Z+
      N*Real.exp (-Z/(4*Real.log K))*(primeEulerProduct K)^4 := by
  classical
  choose f hf using fun v : {v // v ∈ Q} => hQ v.val v.property
  let E : Finset ℕ := Q.attach.image f
  have hE : ∀ n ∈ E,0 < n ∧ n ≤ N ∧ largestPrimeFactor n ≤ K := by
    intro n hn
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hn
    exact ⟨(hf v).1,(hf v).2.2⟩
  have hi : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    have hh := congrArg Nat.totient h
    rwa [(hf a).2.1,(hf b).2.1] at hh
  have he : E.card=Q.card := by simp only [E,Finset.card_image_of_injective _ hi,Finset.card_attach]
  have hh := smooth_counting_split hK N Z E hE
  rwa [he] at hh

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_MovingSmoothCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A slowly growing smoothness cutoff for the exceptional-cofactor count. -/
noncomputable section
namespace TotientAsymptotic

lemma moving_smooth_budget {x : ℝ} (hx : 1 < x) (hB : 10000 ≤ B x) :
    2 ≤ movingSmoothCutoff x ∧ 0 < Real.log (movingSmoothCutoff x) ∧
    Real.log (movingSmoothCutoff x) ≤ Real.log x ∧
    60*B x ≤ (Real.log x/2)/(4*Real.log (movingSmoothCutoff x)) ∧
    6*B x ≤ Real.log x := by
  have hl : 0 < Real.log x := Real.log_pos hx
  have hb : 0 < B x := by linarith
  have he : Real.exp (B x)=Real.log x := Real.exp_log hl
  have hquad := exp_quadratic_lower hb.le
  rw [he] at hquad
  have hmass : 2000*B x ≤ Real.log x := by nlinarith only [hquad,hB]
  have hdiv : 4 ≤ Real.log x/(500*B x) := (le_div_iff₀ (by positivity)).mpr (by linarith only [hmass])
  have hK : 2 ≤ movingSmoothCutoff x := by
    apply Nat.le_floor
    have hh := Real.add_one_le_exp (Real.log x/(500*B x))
    linarith only [hh,hdiv]
  have hK0 : (0:ℝ) < movingSmoothCutoff x := by exact_mod_cast (show 0 < movingSmoothCutoff x by omega)
  have hK1 : (1:ℝ) < movingSmoothCutoff x := by exact_mod_cast (show 1 < movingSmoothCutoff x by omega)
  have hlogK : 0 < Real.log (movingSmoothCutoff x) := Real.log_pos hK1
  have hlog : Real.log (movingSmoothCutoff x) ≤ Real.log x/(500*B x) := by
    have hh := Real.log_le_log hK0 (Nat.floor_le (Real.exp_pos _).le)
    simpa only [Real.log_exp,movingSmoothCutoff] using hh
  have hproduct : 500*B x*Real.log (movingSmoothCutoff x) ≤ Real.log x := by
    have hh := (le_div_iff₀ (show 0 < 500*B x by positivity)).mp hlog
    nlinarith only [hh]
  refine ⟨hK,hlogK,?_,?_,by linarith only [hmass,hb]⟩
  · have hscale : 1 ≤ 500*B x := by linarith only [hB]
    nlinarith only [hproduct,mul_le_mul_of_nonneg_right hscale hlogK.le]
  · apply (le_div_iff₀ (by positivity : 0 < 4*Real.log (movingSmoothCutoff x))).mpr
    nlinarith only [hproduct,mul_pos hb hlogK]

lemma moving_smooth_rankin_factor {x : ℝ} (hx : 1 < x) (hB : 10000 ≤ B x) :
    Real.exp (-(Real.log x/2)/(4*Real.log (movingSmoothCutoff x))) ≤ Real.exp (-60*B x) := by
  apply Real.exp_le_exp.mpr
  have hh := (moving_smooth_budget hx hB).2.2.2.1
  simpa only [neg_div,neg_mul] using neg_le_neg hh

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_MovingSmoothDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The elementary decay estimates in the moving-smooth counting bound. -/
noncomputable section
namespace TotientAsymptotic

lemma moving_smooth_decay {b : ℝ} (hb : 0 ≤ b) :
    b*Real.exp (-60*b)*(Real.exp b)^4 ≤ Real.exp (-3*b) := by
  have hh : b ≤ Real.exp b := by linarith only [Real.add_one_le_exp b]
  have hp : (Real.exp b)^4=Real.exp (4*b) := by
    simpa only [Nat.cast_ofNat] using (Real.exp_nat_mul b 4).symm
  calc
    _ ≤ Real.exp b*Real.exp (-60*b)*(Real.exp b)^4 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le) (by positivity)
    _ = Real.exp (-55*b) := by
      rw [hp,← Real.exp_add,← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

lemma exp_neg_triple_B {x : ℝ} (hx : 1 < x) :
    Real.exp (-3*B x) = ((Real.log x)^3)⁻¹ := by
  have hl : 0 < Real.log x := Real.log_pos hx
  rw [show -3*B x=-(3*B x) by ring,Real.exp_neg]
  have hh : Real.exp (3*B x)=(Real.log x)^3 := by
    simpa only [Nat.cast_ofNat,B,Real.exp_log hl] using Real.exp_nat_mul (B x) 3
  rw [hh]

lemma moving_smooth_small_part {x : ℝ} (hx : 1 < x) (hB : 10000 ≤ B x) :
    Real.exp (Real.log x/2) ≤ x/(Real.log x)^3 := by
  have hb := (moving_smooth_budget hx hB).2.2.2.2
  have hh : Real.log x/2 ≤ Real.log x-3*B x := by linarith only [hb]
  have he := Real.exp_le_exp.mpr hh
  rw [Real.exp_sub,Real.exp_log (by linarith : 0 < x)] at he
  have hpow : Real.exp (3*B x)=(Real.log x)^3 := by
    have hl := Real.log_pos hx
    simpa only [Nat.cast_ofNat,B,Real.exp_log hl] using Real.exp_nat_mul (B x) 3
  rwa [hpow] at he

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_MovingSmoothCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distinct totients with a very smooth preimage have a summable counting bound. -/
noncomputable section
namespace TotientAsymptotic

theorem moving_smooth_totient_count : ∃ C : ℝ,0 < C ∧ ∀ x : ℝ,
    Real.exp (Real.exp 1) ≤ x → 10000 ≤ B x → ∀ Q : Finset ℕ,
    (∀ v ∈ Q,∃ n : ℕ,0 < n ∧ n.totient=v ∧ (v:ℝ) ≤ x ∧
      largestPrimeFactor n ≤ movingSmoothCutoff x) →
    (Q.card:ℝ) ≤ C*x/(Real.log x)^3 := by
  obtain ⟨A,hA,hpreimage⟩ := preimage_loglog_bound
  obtain ⟨D,hD,hmertens⟩ := mertensProductInput
  refine ⟨1+A*D^4,by positivity,?_⟩
  intro x hx hB Q hQ
  have hx1 : 1 < x := (Real.one_lt_exp_iff.mpr (Real.exp_pos _)).trans_le hx
  have hx0 : 0 < x := by linarith only [hx1]
  have hl : 0 < Real.log x := Real.log_pos hx1
  have hb : 0 ≤ B x := by linarith only [hB]
  let K := movingSmoothCutoff x
  let N := ⌊A*x*B x⌋₊
  have hk := moving_smooth_budget hx1 hB
  have hcount := smooth_totient_count_of_preimage (K:=K) (N:=N) hk.1 (Real.log x/2) Q (by
    intro v hv
    obtain ⟨n,hn,hφ,hvx,hsmooth⟩ := hQ v hv
    refine ⟨n,hn,hφ,?_,hsmooth⟩
    apply Nat.le_floor
    exact hpreimage x hx n hn (by rwa [hφ]))
  have hN : (N:ℝ) ≤ A*x*B x := Nat.floor_le (by positivity)
  have heuler : (primeEulerProduct K)^4 ≤ D^4*(Real.log x)^4 := by
    have hh := (hmertens K hk.1).trans
      (mul_le_mul_of_nonneg_left hk.2.2.1 hD.le)
    have hp := pow_le_pow_left₀ (primeEulerProduct_pos K).le hh 4
    simpa only [mul_pow] using hp
  have hrankin := moving_smooth_rankin_factor hx1 hB
  have htail : (N:ℝ)*Real.exp (-(Real.log x/2)/(4*Real.log K))*(primeEulerProduct K)^4 ≤
      A*D^4*x/(Real.log x)^3 := by
    calc
      _ ≤ (A*x*B x)*Real.exp (-60*B x)*(D^4*(Real.log x)^4) := by
        exact mul_le_mul (mul_le_mul hN hrankin (Real.exp_pos _).le (by positivity))
          heuler (by positivity) (by positivity)
      _ = (A*D^4*x)*(B x*Real.exp (-60*B x)*(Real.exp (B x))^4) := by
        rw [B,Real.exp_log hl]
        ring
      _ ≤ (A*D^4*x)*Real.exp (-3*B x) :=
        mul_le_mul_of_nonneg_left (moving_smooth_decay hb) (by positivity)
      _ = _ := by rw [exp_neg_triple_B hx1]; ring
  have hsmall := moving_smooth_small_part hx1 hB
  apply hcount.trans
  change Real.exp (Real.log x/2)+(N:ℝ)*Real.exp (-(Real.log x/2)/(4*Real.log K))*
    (primeEulerProduct K)^4 ≤ _
  have hh := add_le_add hsmall htail
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

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

lemma relative_smooth_at_dyadic {v n : ℕ} (hv : 2 ≤ v) (hB : 1 ≤ B (v:ℝ))
    (hsmooth : (largestPrimeFactor n:ℝ) ≤ Real.exp (Real.log v/(1000*B v))) :
    largestPrimeFactor n ≤ movingSmoothCutoff ((2:ℝ)^(Nat.clog 2 v)) := by
  have hd := dyadic_nat_bounds (show 1 < v by omega)
  have hv1 : (1:ℝ) < v := by exact_mod_cast (show 1 < v by omega)
  have hBx := B_mono hv1 hd.2.2
  have hloss := dyadic_coordinate_loss hv
  have hl : Real.log (v:ℝ) ≤ Real.log ((2:ℝ)^(Nat.clog 2 v)) :=
    Real.log_le_log (by linarith) hd.2.2
  have hlogv : 0 ≤ Real.log (v:ℝ) := (Real.log_pos hv1).le
  have hBv : 0 < B (v:ℝ) := by linarith only [hB]
  have hBX : 0 < B ((2:ℝ)^(Nat.clog 2 v)) := hBv.trans_le hBx
  have hr : Real.log v/(1000*B v) ≤
      Real.log ((2:ℝ)^(Nat.clog 2 v))/(500*B ((2:ℝ)^(Nat.clog 2 v))) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hd : 500*B ((2:ℝ)^(Nat.clog 2 v)) ≤ 1000*B v := by linarith only [hloss,hB]
    exact mul_le_mul hl hd (by positivity) (by linarith)
  apply Nat.le_floor
  exact hsmooth.trans (Real.exp_le_exp.mpr hr)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_MovingSmoothMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reciprocal tail mass of values with very smooth preimages. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem moving_smooth_reciprocal_mass : ∃ C : ℝ,0 < C ∧ ∀ U : ℝ,
    512 ≤ U → Real.exp (Real.exp 1) ≤ U → 10000 ≤ B U → ∀ Q : Finset ℕ,
    (∀ v ∈ Q,U ≤ (v:ℝ) ∧ ∃ n : ℕ,0 < n ∧ n.totient=v ∧
      (largestPrimeFactor n:ℝ) ≤ Real.exp (Real.log v/(1000*B v))) →
    (∑ v ∈ Q,(v:ℝ)⁻¹) ≤ C/(Real.log U)^2 := by
  classical
  obtain ⟨C,hC,hcount⟩ := moving_smooth_totient_count
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  refine ⟨8*C/Real.log 2,by positivity,?_⟩
  intro U hU hUexp hBU Q hQ
  have hU1 : 1 < U := by linarith only [hU]
  have hA : 0 ≤ C/(Real.log 2)^3 := by positivity
  have hslices (j : ℕ) (hj : 1 ≤ j) :
      ((Q.filter (fun v => Nat.clog 2 v=j)).card:ℝ) ≤
        (C/(Real.log 2)^3)*(2:ℝ)^j/(j:ℝ)^3 := by
    let R := Q.filter (fun v => Nat.clog 2 v=j)
    change (R.card:ℝ) ≤ _
    by_cases hR : R.Nonempty
    · obtain ⟨v,hv⟩ := hR
      obtain ⟨hvQ,hvj⟩ := Finset.mem_filter.mp hv
      have hvU := (hQ v hvQ).1
      have hv2 : 2 ≤ v := by exact_mod_cast (show (2:ℝ) ≤ v by linarith only [hvU,hU])
      have hd := dyadic_nat_bounds (show 1 < v by omega)
      rw [hvj] at hd
      have hUx : U ≤ (2:ℝ)^j := hvU.trans hd.2.2
      have hcountR := hcount ((2:ℝ)^j) (hUexp.trans hUx)
        (hBU.trans (B_mono hU1 hUx)) R (by
          intro q hq
          obtain ⟨hqQ,hqj⟩ := Finset.mem_filter.mp hq
          obtain ⟨hqU,n,hn,hφ,hsmooth⟩ := hQ q hqQ
          have hq2 : 2 ≤ q := by exact_mod_cast (show (2:ℝ) ≤ q by linarith only [hqU,hU])
          have hBq : 1 ≤ B (q:ℝ) := (show (1:ℝ) ≤ B U by linarith only [hBU]).trans (B_mono hU1 hqU)
          have hqd := dyadic_nat_bounds (show 1 < q by omega)
          rw [hqj] at hqd
          refine ⟨n,hn,hφ,hqd.2.2,?_⟩
          simpa only [hqj] using relative_smooth_at_dyadic hq2 hBq hsmooth)
      apply hcountR.trans_eq
      rw [dyadic_endpoint_log,mul_pow]
      ring
    · rw [Finset.not_nonempty_iff_eq_empty.mp hR,Finset.card_empty,Nat.cast_zero]
      positivity
  have hm := finite_dyadic_log_cube_tail Q hU1 hA (fun v hv => (hQ v hv).1) hslices
  apply hm.trans_eq
  have hlogU : 0 < Real.log U := Real.log_pos hU1
  field_simp

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FailedRowMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reciprocal mass for an arbitrary failed first row: the leading prime may be
small or large, and the preimage may have any length. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem failed_row_reciprocal_mass : ∃ A C F : ℝ,0 < A ∧ 0 < C ∧ 0 < F ∧
    ∀ k : ℕ,∀ ω U : ℝ,0 < ω → ω ≤ 1 → 512 ≤ U → 2*Real.exp (Real.exp 1) ≤ U →
    10000 ≤ B U → (8000/ω)^2 ≤ B U →
    max 300000000 ((coordinateBudgetConstant F/coordinateDecay (ω/4) k)^(4/3:ℝ)) ≤ B U-1 →
    4 ≤ (ω/2)*B U → ∀ Q : Finset ℕ,
    (∀ v ∈ Q,U ≤ (v:ℝ) ∧ ∃ n : ℕ,0 < n ∧ n.totient=v ∧
      (1+ω)*fordPrimeCoordinate n 0 < ∑ i : Fin k,a (i.val+1)*fordPrimeCoordinate n (i.val+1)) →
    (∑ v ∈ Q,(v:ℝ)⁻¹) ≤ A/(Real.log U)^2+
      4*C*(Real.log 2)^(-1-coordinateDecay (ω/4) k)*(1+(coordinateDecay (ω/4) k)⁻¹)*
        Real.exp (-coordinateDecay (ω/4) k*B U) := by
  classical
  obtain ⟨A,hA,hsmooth⟩ := moving_smooth_reciprocal_mass
  obtain ⟨C,F,hC,hF,hrow⟩ := exceptional_row_reciprocal_mass
  refine ⟨A,C,F,hA,hC,hF,?_⟩
  intro k ω U hω hω1 hU hUexp hBU hhead hthreshold hlarge Q hQ
  let S := Q.filter (fun v => ∃ n : ℕ,0 < n ∧ n.totient=v ∧
    (largestPrimeFactor n:ℝ) ≤ Real.exp (Real.log v/(1000*B v)))
  let R := Q\S
  have hS := hsmooth U hU (by linarith only [hUexp,Real.exp_pos (Real.exp 1)]) hBU S (by
    intro v hv
    obtain ⟨hv,hn⟩ := Finset.mem_filter.mp hv
    exact ⟨(hQ v hv).1,hn⟩)
  have hR := hrow k (ω/2) U (by linarith) (by linarith) hU hUexp
    (by simpa only [show ω/2/2=ω/4 by ring] using hthreshold) hlarge R (by
      intro v hv
      obtain ⟨hv,hnot⟩ := Finset.mem_sdiff.mp hv
      obtain ⟨hvU,n,hn,hφ,hfailed⟩ := hQ v hv
      have hv1 : (1:ℝ) < v := by linarith only [hvU,hU]
      have hBv := B_mono (show 1 < U by linarith only [hU]) hvU
      have hcut : Real.exp (Real.log v/(1000*B v)) ≤ (largestPrimeFactor n:ℝ) := by
        by_contra hh
        apply hnot
        exact Finset.mem_filter.mpr ⟨hv,n,hn,hφ,le_of_not_ge hh⟩
      refine ⟨hvU,⟨n,hn,hφ⟩,n,hn,hφ,?_⟩
      exact large_head_row_relative (by exact_mod_cast hv1)
        (by linarith only [hBU,hBv]) hω hω1 (hhead.trans hBv) hcut hfailed)
  have hsplit : (∑ v ∈ Q,(v:ℝ)⁻¹) = (∑ v ∈ S,(v:ℝ)⁻¹)+(∑ v ∈ R,(v:ℝ)⁻¹) := by
    have hsub : S ⊆ Q := Finset.filter_subset _ _
    have hh := Finset.sum_sdiff hsub (f:=fun v : ℕ => (v:ℝ)⁻¹)
    change (∑ v ∈ R,(v:ℝ)⁻¹)+(∑ v ∈ S,(v:ℝ)⁻¹) = _ at hh
    linarith only [hh]
  rw [hsplit]
  simpa only [show ω/2/2=ω/4 by ring] using add_le_add hS hR

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FailedRowTailBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform absorption of the residual row tail beyond its effective threshold. -/
noncomputable section
namespace TotientAsymptotic

lemma logarithm_two_power_bound {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (Real.log 2)^(-1-δ) ≤ 4 := by
  have hl : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hh := Real.rpow_le_rpow_of_nonpos (by norm_num : (0:ℝ)<1/2) hl
    (show -1-δ ≤ 0 by linarith)
  have ht := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0:ℝ)<1/2)
    (by norm_num : (1/2:ℝ) ≤ 1) (show (-2:ℝ) ≤ -1-δ by linarith)
  have he : (1/2:ℝ)^(-2:ℝ)=4 := by norm_num
  exact hh.trans (ht.trans_eq he)

lemma row_tail_coefficient_bound {δ b : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsize : δ⁻¹ ≤ Real.exp (δ*b)) :
    4*(Real.log 2)^(-1-δ)*(1+δ⁻¹)*Real.exp (-δ*b) ≤ 32 := by
  have he : δ⁻¹ ≤ Real.exp (δ*b) := hsize
  have hi := inv_anti₀ (inv_pos.mpr hδ) he
  have hexp : Real.exp (-δ*b) ≤ δ := by
    simpa only [← Real.exp_neg,inv_inv,neg_mul] using hi
  have htail : (1+δ⁻¹)*Real.exp (-δ*b) ≤ 2 := by
    have hh := mul_le_mul_of_nonneg_left hexp (show 0 ≤ 1+δ⁻¹ by positivity)
    have hid : (1+δ⁻¹)*δ=1+δ := by field_simp <;> ring
    rw [hid] at hh
    linarith only [hh,hδ1]
  have hp := logarithm_two_power_bound hδ.le hδ1
  have hh := mul_le_mul hp htail (by positivity) (by norm_num : (0:ℝ)≤4)
  nlinarith only [hh]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FailedRowTotalMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A complete reciprocal-mass bound for the residual values in a failed row. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem failed_row_total_mass : ∃ C F : ℝ,0 < C ∧ 0 < F ∧
    ∀ k : ℕ,∀ ω U : ℝ,0 < ω → ω ≤ 1 → 512 ≤ U → 2*Real.exp (Real.exp 1) ≤ U →
    10000 ≤ B U → (8000/ω)^2 ≤ B U →
    max 300000000 ((coordinateBudgetConstant F/coordinateDecay (ω/4) k)^(4/3:ℝ)) ≤ B U-1 →
    4 ≤ (ω/2)*B U → (coordinateDecay (ω/4) k)⁻¹ ≤ Real.exp (coordinateDecay (ω/4) k*B U) →
    ∀ Q : Finset ℕ,
    (∀ v ∈ Q,∃ n : ℕ,0 < n ∧ n.totient=v ∧
      (1+ω)*fordPrimeCoordinate n 0 < ∑ i : Fin k,a (i.val+1)*fordPrimeCoordinate n (i.val+1)) →
    (∑ v ∈ Q,(v:ℝ)⁻¹) ≤ C*Real.exp (10*(Real.log (B U+4))^2) := by
  classical
  obtain ⟨P,hP,hsmall⟩ := bounded_totient_reciprocal_mass
  obtain ⟨A,C,F,hA,hC,hF,htail⟩ := failed_row_reciprocal_mass
  refine ⟨P+A+32*C,F,by positivity,hF,?_⟩
  intro k ω U hω hω1 hU hUexp hBU hhead hthreshold hlarge hinv Q hQ
  let S : Finset ℕ := Q.filter (fun v : ℕ => (v:ℝ) ≤ U)
  let R : Finset ℕ := Q\S
  have hS := hsmall U (by linarith only [hU]) (by linarith only [hBU]) S (by
    intro v hv
    obtain ⟨hv,hvU⟩ := Finset.mem_filter.mp hv
    obtain ⟨n,hn,hφ,_⟩ := hQ v hv
    exact ⟨⟨n,hn,hφ⟩,hvU⟩)
  have hR := htail k ω U hω hω1 hU hUexp hBU hhead hthreshold hlarge R (by
    intro v hv
    obtain ⟨hv,hnot⟩ := Finset.mem_sdiff.mp hv
    have hUv : U ≤ (v:ℝ) := by
      by_contra hh
      exact hnot (Finset.mem_filter.mpr ⟨hv,le_of_not_ge hh⟩)
    exact ⟨hUv,hQ v hv⟩)
  have hδ := coordinate_decay_bounds (k:=k) (show 0 ≤ ω/4 by linarith) (show ω/4 ≤ 1 by linarith)
  have hc := row_tail_coefficient_bound (coordinate_decay_pos (show 0 < ω/4 by linarith) k)
    (hδ.2.1.trans (by norm_num)) hinv
  have hc' := mul_le_mul_of_nonneg_left hc hC.le
  have hlog : 1 ≤ Real.log U := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ)<3) (show (3:ℝ) ≤ U by linarith only [hU])
    linarith [Real.log_three_gt_d9]
  have hA' : A/(Real.log U)^2 ≤ A := by
    apply (div_le_iff₀ (by positivity : 0 < (Real.log U)^2)).mpr
    have hh := mul_le_mul_of_nonneg_left (one_le_pow₀ (n:=2) hlog) hA.le
    simpa only [mul_one] using hh
  have hE : 1 ≤ Real.exp (10*(Real.log (B U+4))^2) := Real.one_le_exp (by positivity)
  have hbound : (∑ v ∈ R,(v:ℝ)⁻¹) ≤
      (A+32*C)*Real.exp (10*(Real.log (B U+4))^2) := by
    have hh := mul_le_mul_of_nonneg_left hE (show 0 ≤ A+32*C by positivity)
    nlinarith only [hR,hc',hA',hh]
  have hsplit := Finset.sum_sdiff (show S ⊆ Q from Finset.filter_subset _ _)
    (f:=fun v : ℕ => (v:ℝ)⁻¹)
  change (∑ v ∈ R,(v:ℝ)⁻¹)+(∑ v ∈ S,(v:ℝ)⁻¹)=(∑ v ∈ Q,(v:ℝ)⁻¹) at hsplit
  nlinarith only [hS,hbound,hsplit]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FailedRowCountBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! First-failed-row value counts with the residual mass fully bounded. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem failed_row_count_bound_oai : ∃ C F : ℝ, 0 < C ∧ 0 < F ∧
    ∀ᶠ x : ℝ in atTop, ∀ j : ℕ, 1 ≤ j → j ≤ m x →
    ∀ ω U : ℝ, xi x j=1+ω → FailedRowMassBudget F ω U (m x-j) →
    ∀ Q : Finset ℕ, ∀ n : ℕ → ℕ,
      (∀ v ∈ Q, 0 < n v ∧ (n v).totient=v ∧
        x^(1/4:ℝ) ≤ fordPrime (n v) 0 ∧ (v:ℝ) ≤ x ∧
        (∀ i < j, fordRowSum (m x) (fordPrimeCoordinate (n v)) i ≤
          xi x i*(if i=0 then B x else fordPrimeCoordinate (n v) i)) ∧
        xi x j*fordPrimeCoordinate (n v) j <
          fordRowSum (m x) (fordPrimeCoordinate (n v)) j) →
      (Q.card:ℝ) ≤ C*(x/Real.log x)*G x (j-1)*
        Real.exp (10*(Real.log (B U+4))^2) := by
  classical
  obtain ⟨A,hA,hcount⟩ := failed_row_value_count
  obtain ⟨D,F,hD,hF,hmass⟩ := failed_row_total_mass
  refine ⟨A*D,F,mul_pos hA hD,hF,?_⟩
  filter_upwards [hcount,eventually_gt_atTop (1:ℝ),
    B_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with x hx hx1 hB
  intro j hj hjm ω U hxi hbudget Q n hQ
  obtain ⟨hω,hω1,hU,hUexp,hBU,hhead,hthreshold,hlarge,hinv⟩ := hbudget
  let R := Q.image (fun v => (fordCofactor (n v) j).totient)
  have hR := hmass (m x-j) ω U hω hω1 hU hUexp hBU hhead hthreshold hlarge hinv R (by
    intro d hd
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hd
    refine ⟨fordCofactor (n v) j,fordCofactor_pos _ _,rfl,?_⟩
    exact failed_row_cofactor hjm hxi (hQ v hv).2.2.2.2.2)
  have hc := hx j hj hjm Q n hQ
  have hfac : 0 ≤ A*(x/Real.log x)*G x (j-1) :=
    mul_nonneg (mul_nonneg hA.le (div_nonneg (by linarith) (Real.log_pos hx1).le)) (G_pos hB _).le
  apply hc.trans
  have hh := mul_le_mul_of_nonneg_left hR hfac
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end TotientAsymptotic

end

end OAI
end

theorem solution : type_of% @OAI.TotientAsymptotic.failed_row_count_bound_oai := @OAI.TotientAsymptotic.failed_row_count_bound_oai
