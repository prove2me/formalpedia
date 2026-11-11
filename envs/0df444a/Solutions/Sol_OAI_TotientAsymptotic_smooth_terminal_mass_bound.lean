-- Prove2me | solution 1 for OAI.TotientAsymptotic.smooth_terminal_mass_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:31:59.767205+00:00
-- url     : https://prove2.me/submissions/c8b8c37c-3114-4ee9-b904-58b20bb22326

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
import Mathlib.Tactic.Bound
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Order.Compact
import Definitions.Def_TotientAsymptotic
import Definitions.Def_OAIQ233A000
import Theorems.Thm_OAI_TotientAsymptotic_bootstrap_good_value_discard

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SmoothResidualMass
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Euler product bounds the entire smooth residual-integer sum. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma prime_reciprocal_norm_lt_one {p : ℕ} (hp : p.Prime) : ‖reciprocalNatHom p‖ < 1 := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  simpa only [reciprocalNatHom,MonoidHom.coe_mk,OneHom.coe_mk,Real.norm_eq_abs,
    abs_inv,abs_of_nonneg (Nat.cast_nonneg p : (0 : ℝ) ≤ p)] using (inv_lt_one₀ (zero_lt_one.trans hpR)).mpr hpR

lemma reciprocal_prime_factor (p : ℕ) (hp : p.Prime) :
    (1-reciprocalNatHom p)⁻¹=(p : ℝ)/(p-1) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  change (1-(p : ℝ)⁻¹)⁻¹=(p : ℝ)/(p-1)
  field_simp

/-- Only positivity and smoothness are used; the residuals may repeat prime
factors and the upper cutoff on their size is arbitrary. -/
theorem smooth_residual_reciprocal_mass (N : ℕ) (Q : Finset ℕ)
    (hQ : ∀ n ∈ Q, 0 < n ∧ largestPrimeFactor n ≤ N) :
    (∑ n ∈ Q, (n : ℝ)⁻¹) ≤ primeEulerProduct N := by
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
  have hsum : (∑ n ∈ Q, (n : ℝ)⁻¹) = ∑ n ∈ T, reciprocalNatHom n := by
    dsimp only [T]
    rw [Finset.sum_image (fun n _ m _ h => he h)]
    change (∑ n ∈ Q, (n : ℝ)⁻¹) = ∑ n ∈ Q.attach, (n.val : ℝ)⁻¹
    exact (Finset.sum_attach Q (fun n : ℕ => (n : ℝ)⁻¹)).symm
  have hseries := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := reciprocalNatHom) (fun {_} hp => prime_reciprocal_norm_lt_one hp) S
  calc
    _ = ∑ n ∈ T, reciprocalNatHom n := hsum
    _ ≤ ∑' n : Nat.factoredNumbers S, reciprocalNatHom n := by
      apply hseries.1.of_norm.sum_le_tsum
      intro n _
      change 0 ≤ (n.val : ℝ)⁻¹
      positivity
    _ = ∏ p ∈ S with p.Prime, (1-reciprocalNatHom p)⁻¹ := hseries.2.tsum_eq
    _ = primeEulerProduct N := by
      apply Finset.prod_congr rfl
      intro p hp
      exact reciprocal_prime_factor p (Finset.mem_filter.mp hp).2

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalityGridMass
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite union of the normality grid cells. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace TotientAsymptotic

lemma reciprocal_sum_biUnion_le {α : Type*} (I : Finset α) (S : α → Finset ℕ) :
    (∑ n ∈ I.biUnion S,(n:ℝ)⁻¹) ≤ ∑ i ∈ I,∑ n ∈ S i,(n:ℝ)⁻¹ := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert a I ha ih =>
    rw [Finset.biUnion_insert,Finset.sum_insert ha]
    have he := Finset.sum_union_inter (s₁:=S a) (s₂:=I.biUnion S) (f:=fun n : ℕ => (n:ℝ)⁻¹)
    have hn : 0 ≤ ∑ n ∈ S a ∩ I.biUnion S,(n:ℝ)⁻¹ :=
      Finset.sum_nonneg (fun n _ => inv_nonneg.mpr (Nat.cast_nonneg n))
    linarith

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_QuarterPrimeCount
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The quarter-power prime interval used in Ford’s global counting argument.
Chebyshev's library theorem suffices for the upper bound; no PNT input is used here. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

/-- The largest-prime restriction makes the logarithm of every nonempty
counting interval comparable to `log x`, uniformly in its integer denominator. -/
theorem quarter_prime_count_upper :
    ∀ᶠ x : ℝ in atTop, ∀ D : ℕ, 0 < D → ∀ Q : Finset ℕ,
      (∀ p ∈ Q, p.Prime ∧ x^(1/4 : ℝ) ≤ p ∧ ((p-1)*D : ℕ) ≤ x) →
      (Q.card : ℝ) ≤ 32*x/((D : ℝ)*Real.log x) := by
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp (Chebyshev.eventually_primeCounting_le (by norm_num : (0 : ℝ)<1))
  have ht : Tendsto (fun x : ℝ => x^(1/4 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  filter_upwards [eventually_gt_atTop (1 : ℝ), ht.eventually (eventually_ge_atTop Y₀)] with x hx hxp
  intro D hD Q hQ
  have hD' : (0 : ℝ)<D := by exact_mod_cast hD
  have hx0 : 0<x := zero_lt_one.trans hx
  have hlogx : 0<Real.log x := Real.log_pos hx
  by_cases hne : Q.Nonempty
  · let Y := 1+x/D
    have hpY (p : ℕ) (hp : p ∈ Q) : (p : ℝ) ≤ Y := by
      have hh := hQ p hp
      have hpn := hh.1.one_lt.le
      have hval : ((p : ℝ)-1)*D ≤ x := by
        exact_mod_cast hh.2.2
      change _ ≤ 1+x/D
      have hh' := (le_div_iff₀ hD').mpr hval
      linarith
    obtain ⟨p, hp⟩ := hne
    have hlY : x^(1/4 : ℝ) ≤ Y := (hQ p hp).2.1.trans (hpY p hp)
    have hY0 : 0<Y := by dsimp [Y] <;> positivity
    have hYlarge : Y₀ ≤ Y := hxp.trans hlY
    have hlogY : (1/4 : ℝ)*Real.log x ≤ Real.log Y := by
      have hh := Real.log_le_log (Real.rpow_pos_of_pos hx0 _) hlY
      rw [Real.log_rpow hx0] at hh
      linarith
    have hlogYpos : 0<Real.log Y := lt_of_lt_of_le (by positivity) hlogY
    have hDx : (D : ℝ) ≤ x := by
      have hh := (hQ p hp).2.2
      have hp2 := (hQ p hp).1.two_le
      have hp1 : 1 ≤ p-1 := by omega
      have hnat : D ≤ (p-1)*D := by simpa only [one_mul] using Nat.mul_le_mul_right D hp1
      exact (by exact_mod_cast hnat : (D : ℝ) ≤ ((p-1)*D : ℕ)).trans hh
    have hYupper : Y ≤ 2*x/D := by
      change 1+x/D ≤ _
      have hone : (1 : ℝ) ≤ x/D := (le_div_iff₀ hD').mpr (by simpa using hDx)
      have he : 2*x/D = 2*(x/D) := by ring
      rw [he]
      linarith
    have hsub : Q ⊆ Nat.primesLE ⌊Y⌋₊ := by
      intro q hq
      exact Nat.mem_primesLE.mpr ⟨Nat.le_floor (hpY q hq), (hQ q hq).1⟩
    have hcard : (Q.card : ℝ) ≤ Nat.primeCounting ⌊Y⌋₊ := by
      exact_mod_cast (Finset.card_le_card hsub).trans_eq (Nat.primesLE_card_eq_primeCounting _)
    have hc : Real.log 4+1 ≤ (3 : ℝ) := by rw [Real.log_four_eq]; linarith [Real.log_two_lt_d9]
    calc
      _ ≤ (Real.log 4+1)*Y/Real.log Y := hcard.trans (hY₀ Y hYlarge)
      _ ≤ (3*(2*x/D))/((1/4 : ℝ)*Real.log x) := by
        apply div_le_div₀ (by positivity)
          ((mul_le_mul_of_nonneg_right hc hY0.le).trans (mul_le_mul_of_nonneg_left hYupper (by norm_num)))
          (by positivity) hlogY
      _ ≤ 32*x/((D : ℝ)*Real.log x) := by
        field_simp
        nlinarith
  · have hz : Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hz, Finset.card_empty, Nat.cast_zero]
    positivity

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeExtensionCount
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
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

lemma prime_extension_values_card (x : ℝ) (d : ℕ) :
    (primeExtensionValues x d).card ≤ 2*(quarterPrimes x d).card := by
  classical
  calc
    _ ≤ ∑ _p ∈ quarterPrimes x d,({(0:ℕ),1}:Finset ℕ).card :=
      Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun p _ => by simp; exact Finset.card_insert_le _ _))
    _ = _ := by simp; omega

theorem prime_extension_count_upper : ∀ᶠ x : ℝ in atTop,
    ∀ R : Finset ℕ,(∀ d ∈ R,0 < d) →
    ((R.biUnion (primeExtensionValues x)).card:ℝ) ≤
      (64*x/Real.log x)*(∑ d ∈ R,(d:ℝ)⁻¹) := by
  classical
  filter_upwards [quarter_prime_count_upper,eventually_gt_atTop (1:ℝ)] with x hx hx1
  intro R hR
  have hcount (d : ℕ) (hd : d ∈ R) :
      ((primeExtensionValues x d).card:ℝ) ≤ 64*x/(d*Real.log x) := by
    have hh := hx d (hR d hd) (quarterPrimes x d) (fun p hp => (mem_quarterPrimes (hR d hd)).mp hp)
    have hc : ((primeExtensionValues x d).card:ℝ) ≤ 2*(quarterPrimes x d).card :=
      by exact_mod_cast prime_extension_values_card x d
    calc
      _ ≤ 2*((quarterPrimes x d).card:ℝ) := hc
      _ ≤ 2*(32*x/(d*Real.log x)) := mul_le_mul_of_nonneg_left hh (by norm_num)
      _ = _ := by ring
  calc
    _ ≤ ∑ d ∈ R,((primeExtensionValues x d).card:ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le : (R.biUnion (primeExtensionValues x)).card ≤
        ∑ d ∈ R,(primeExtensionValues x d).card)
    _ ≤ ∑ d ∈ R,64*x/(d*Real.log x) := Finset.sum_le_sum hcount
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro d _; ring

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

lemma totient_mem_primeExtensionValues {x : ℝ} {n p : ℕ}
    (hn : 0 < n) (hp : p.Prime) (hpn : p ∣ n) (hpx : x^(1/4:ℝ) ≤ p)
    (hx : (n.totient:ℝ) ≤ x) :
    n.totient ∈ primeExtensionValues x (n/p).totient := by
  have hq : 0 < n/p := Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos
  have hd : 0 < (n/p).totient := Nat.totient_pos.mpr hq
  have hcases := totient_prime_extension_cases hp hpn
  have hsize : (((p-1)*(n/p).totient:ℕ):ℝ) ≤ x := by
    rcases hcases with h|h
    · rwa [← h]
    · exact (Nat.cast_le.mpr (Nat.mul_le_mul_right (n/p).totient (Nat.sub_le p 1))).trans (by rwa [← h])
  apply Finset.mem_biUnion.mpr
  refine ⟨p,(mem_quarterPrimes hd).mpr ⟨hp,hpx,hsize⟩,?_⟩
  rcases hcases with h|h <;> simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto

/-- The residual set consists of values, so repeated preimages incur no extra factor. -/
theorem large_prime_totient_count : ∀ᶠ x : ℝ in atTop,
    ∀ R Q : Finset ℕ,(∀ d ∈ R,0 < d) →
    (∀ v ∈ Q,∃ n p : ℕ,0 < n ∧ n.totient=v ∧ p.Prime ∧ p ∣ n ∧
      x^(1/4:ℝ) ≤ p ∧ (v:ℝ) ≤ x ∧ (n/p).totient ∈ R) →
    (Q.card:ℝ) ≤ (64*x/Real.log x)*(∑ d ∈ R,(d:ℝ)⁻¹) := by
  classical
  filter_upwards [prime_extension_count_upper] with x hx
  intro R Q hR hQ
  have hsub : Q ⊆ R.biUnion (primeExtensionValues x) := by
    intro v hv
    obtain ⟨n,p,hn,he,hp,hpn,hpx,hvx,hr⟩ := hQ v hv
    refine Finset.mem_biUnion.mpr ⟨(n/p).totient,hr,?_⟩
    rw [← he]
    exact totient_mem_primeExtensionValues hn hp hpn hpx (by rwa [he])
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hx R hR)

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

lemma dyadicTotientEnvelope_mono {I J : ℕ} (hIJ : I ≤ J) :
    dyadicTotientEnvelope I ≤ dyadicTotientEnvelope J := by
  unfold dyadicTotientEnvelope
  apply max_le_max le_rfl
  exact Finset.sup'_mono (s₁ := Finset.range (I+1)) (s₂ := Finset.range (J+1))
    (fun k : ℕ => V ((2:ℝ)^k)*(k:ℝ)/(2:ℝ)^k)
    (Finset.range_mono (Nat.add_le_add_right hIJ 1)) (by simp)

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CoarseTotientBounds
attribute [-simp] _root_.SelbergSieve.selbergBoundingSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coarse unconditional bounds used before the sharp counting-scale bootstrap. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma V_le_self {x : ℝ} (hx : 0 ≤ x) : V x ≤ x := by
  classical
  have hc : (totientValues x).card ≤ ⌊x⌋₊ := by
    have hh := Finset.card_le_card (Finset.filter_subset IsTotient (Finset.Icc 1 ⌊x⌋₊))
    simpa [totientValues] using hh
  exact (Nat.cast_le.mpr hc).trans (Nat.floor_le hx)

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

lemma fordCofactor_div (n k : ℕ) :
    fordCofactor n k / fordPrime n k = fordCofactor n (k+1) := by
  conv_lhs => rw [fordCofactor_step n k]
  exact Nat.mul_div_cancel_left _ (fordPrime_pos n k)

lemma ford_first_two_factorization {n : ℕ} (hn : 0 < n) :
    n=fordPrime n 0*fordPrime n 1*fordCofactor n 2 := by
  calc
    n = fordCofactor n 0 := (fordCofactor_zero hn).symm
    _ = _ := by
      rw [fordCofactor_step n 0,fordCofactor_step n 1]
      simp only [Nat.reduceAdd]
      ring

lemma fordCofactor_totient_cases (n k : ℕ) :
    (fordCofactor n k).totient=(fordCofactor n (k+1)).totient ∨
    ((fordPrime n k).Prime ∧
    ((fordCofactor n k).totient=(fordPrime n k-1)*(fordCofactor n (k+1)).totient ∨
     (fordCofactor n k).totient=fordPrime n k*(fordCofactor n (k+1)).totient)) := by
  by_cases hk : k < n.primeFactorsList.length
  · right
    have hp := fordPrime_prime hk
    refine ⟨hp,?_⟩
    have hd : fordPrime n k ∣ fordCofactor n k := by
      rw [fordCofactor_step n k]
      exact dvd_mul_right _ _
    simpa only [fordCofactor_div] using totient_prime_extension_cases hp hd
  · left
    have hp : fordPrime n k=1 := by
      unfold fordPrime
      rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hk)]
      rfl
    rw [fordCofactor_step n k,hp,one_mul]

lemma fordPrime_le_first (n k : ℕ) : fordPrime n k ≤ fordPrime n 0 := by
  by_cases hk : k < n.primeFactorsList.length
  · exact fordPrime_antitone (by omega) hk (Nat.zero_le k)
  · have hp : fordPrime n k=1 := by
      unfold fordPrime
      rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hk)]
      rfl
    rw [hp]
    exact fordPrime_pos n 0

lemma fordPrime_le_self {n : ℕ} (hn : 0 < n) (k : ℕ) : fordPrime n k ≤ n := by
  by_cases hk : k < n.primeFactorsList.length
  · exact Nat.le_of_dvd hn (Nat.dvd_of_mem_primeFactorsList
      (List.mem_reverse.mp (by rw [fordPrime_eq_get hk]; exact List.getElem_mem _)))
  · have hp : fordPrime n k=1 := by
      unfold fordPrime
      rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hk)]
      rfl
    omega

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

lemma quarter_fordPrime_prime {x : ℝ} {n : ℕ} (hx : 1 < x)
    (hp : x^(1/4:ℝ) ≤ fordPrime n 0) : (fordPrime n 0).Prime := by
  have hlarge : 1 < (fordPrime n 0:ℝ) := (Real.one_lt_rpow hx (by norm_num)).trans_le hp
  by_cases hi : 0 < n.primeFactorsList.length
  · exact fordPrime_prime hi
  · have he : fordPrime n 0=1 := by
      unfold fordPrime
      rw [List.getElem?_eq_none (by simp only [List.length_reverse]; omega)]
      rfl
    simp only [he,Nat.cast_one,lt_self_iff_false] at hlarge

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TwoPrimeResidualMass
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Residual values after one prime extension and their reciprocal mass. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma singlePrimeExtensions_pos {P M : Finset ℕ}
    (hP : ∀ p ∈ P,p.Prime) (hM : ∀ m ∈ M,0 < m) :
    ∀ d ∈ singlePrimeExtensions P M,0 < d := by
  classical
  intro d hd
  rcases Finset.mem_union.mp hd with hd|hd
  · exact hM d hd
  · obtain ⟨m,hm,p,hp,hd⟩ := by
      simpa only [Finset.mem_biUnion] using hd
    have hp2 := (hP p hp).two_le
    simp only [Finset.mem_insert,Finset.mem_singleton] at hd
    rcases hd with rfl|rfl <;> exact Nat.mul_pos (by omega) (hM m hm)

lemma singlePrimeExtensions_mass (P M : Finset ℕ) (hP : ∀ p ∈ P,p.Prime) :
    (∑ d ∈ singlePrimeExtensions P M,(d:ℝ)⁻¹) ≤
    (1+2*∑ p ∈ P,((p-1:ℕ):ℝ)⁻¹)*(∑ m ∈ M,(m:ℝ)⁻¹) := by
  classical
  have hpair (m p : ℕ) (hp : p ∈ P) :
      (∑ d ∈ ({(p-1)*m,p*m}:Finset ℕ),(d:ℝ)⁻¹) ≤
      2*((p-1:ℕ):ℝ)⁻¹*(m:ℝ)⁻¹ := by
    have hh : (∑ d ∈ ({(p-1)*m,p*m}:Finset ℕ),(d:ℝ)⁻¹) ≤
        (((p-1)*m:ℕ):ℝ)⁻¹+((p*m:ℕ):ℝ)⁻¹ := by
      by_cases he : (p-1)*m=p*m
      · simp only [he,Finset.insert_eq_of_mem (Finset.mem_singleton_self _),Finset.sum_singleton]
        have hi : (0:ℝ) ≤ ((p*m:ℕ):ℝ)⁻¹ := by positivity
        linarith
      · rw [Finset.sum_pair he]
    have hp0 : 0 < p-1 := by have := (hP p hp).two_le; omega
    have hp' : (p:ℝ)⁻¹ ≤ ((p-1:ℕ):ℝ)⁻¹ :=
      inv_anti₀ (by exact_mod_cast hp0) (by exact_mod_cast Nat.sub_le p 1)
    simp only [Nat.cast_mul,mul_inv_rev] at hh
    have hm0 : 0 ≤ (m:ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
    nlinarith only [hh,mul_le_mul_of_nonneg_left hp' hm0]
  have hmass : (∑ d ∈ M.biUnion (fun m => P.biUnion (fun p => {(p-1)*m,p*m})),(d:ℝ)⁻¹) ≤
      (2*∑ p ∈ P,((p-1:ℕ):ℝ)⁻¹)*(∑ m ∈ M,(m:ℝ)⁻¹) := by
    calc
      _ ≤ ∑ m ∈ M,∑ d ∈ P.biUnion (fun p => {(p-1)*m,p*m}),(d:ℝ)⁻¹ :=
        reciprocal_sum_biUnion_le _ _
      _ ≤ ∑ m ∈ M,∑ p ∈ P,2*((p-1:ℕ):ℝ)⁻¹*(m:ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro m _
        exact (reciprocal_sum_biUnion_le _ _).trans (Finset.sum_le_sum (hpair m))
      _ = _ := by
        simp only [← Finset.sum_mul,← Finset.mul_sum]
  have hu := Finset.sum_union_inter (s₁:=M)
    (s₂:=M.biUnion (fun m => P.biUnion (fun p => {(p-1)*m,p*m})))
    (f:=fun d : ℕ => (d:ℝ)⁻¹)
  have hn : 0 ≤ ∑ d ∈ M ∩ M.biUnion (fun m => P.biUnion (fun p => {(p-1)*m,p*m})),(d:ℝ)⁻¹ :=
    Finset.sum_nonneg (fun d _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  unfold singlePrimeExtensions
  nlinarith only [hu,hmass,hn]

lemma cofactor_singlePrimeExtensions {n k : ℕ} {P M : Finset ℕ}
    (hM : (fordCofactor n (k+1)).totient ∈ M)
    (hP : (fordPrime n k).Prime → fordPrime n k ∈ P) :
    (fordCofactor n k).totient ∈ singlePrimeExtensions P M := by
  classical
  rcases fordCofactor_totient_cases n k with he|⟨hp,he⟩
  · exact Finset.mem_union_left _ (he ▸ hM)
  · apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨(fordCofactor n (k+1)).totient,hM,?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨fordPrime n k,hP hp,?_⟩
    simpa only [Finset.mem_insert,Finset.mem_singleton] using he

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BootstrapResidualMass
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact residual-value set has mass controlled at the smaller endpoint. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma bootstrap_prime_endpoint {x : ℝ} (hx : Real.exp (Real.exp 1) ≤ x) :
    2 ≤ ⌊2*x^2⌋₊ ∧ 0 ≤ B (⌊2*x^2⌋₊:ℝ) ∧ B (⌊2*x^2⌋₊:ℝ) ≤ 3*B x := by
  have he : 2 ≤ Real.exp (1:ℝ) := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hx3 : 3 ≤ x := by
    have ht := Real.add_one_le_exp (Real.exp (1:ℝ))
    linarith
  have hfloor : 4 ≤ ⌊2*x^2⌋₊ := by
    apply Nat.le_floor
    norm_num only [Nat.cast_ofNat]
    nlinarith
  have hN4 : (4:ℝ) ≤ ⌊2*x^2⌋₊ := by exact_mod_cast hfloor
  have hN : (⌊2*x^2⌋₊:ℝ) ≤ 2*x^2 := Nat.floor_le (by positivity)
  have hlogN : 1 ≤ Real.log (⌊2*x^2⌋₊:ℝ) := by
    have ht := Real.log_le_log (by norm_num : (0:ℝ)<4) hN4
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow] at ht
    norm_num only [Nat.cast_ofNat] at ht
    linarith [Real.log_two_gt_d9]
  refine ⟨by omega,Real.log_nonneg hlogN,?_⟩
  have hmono : B (⌊2*x^2⌋₊:ℝ) ≤ B (2*x^2) :=
    Real.log_le_log (by linarith) (Real.log_le_log (by linarith) hN)
  exact hmono.trans (doubleLog_twice_square hx)

 theorem bootstrap_residual_mass : ∃ C : ℝ,0 < C ∧ ∀ x : ℝ,
    Real.exp (Real.exp 1) ≤ x → ∀ J : ℕ,1 ≤ J → ∀ M : Finset ℕ,
    (∀ m ∈ M,IsTotient m ∧ (m:ℝ) ≤ (2:ℝ)^J) →
    (∑ d ∈ singlePrimeExtensions (Nat.primesLE ⌊2*x^2⌋₊) M,(d:ℝ)⁻¹) ≤
      C*(1+B x)*dyadicTotientEnvelope J*(1+Real.log J) := by
  obtain ⟨D,hD,hmass⟩ := prime_reciprocal_mass_bound mertensProductInput
  refine ⟨5*(1+6*D),by positivity,?_⟩
  intro x hx J hJ M hM
  obtain ⟨hN,hBN,hBNx⟩ := bootstrap_prime_endpoint hx
  have hp := hmass _ hN hBN
  have hBx : 0 ≤ B x := by linarith
  have hlog : 0 ≤ Real.log (J:ℝ) := Real.log_nonneg (by exact_mod_cast hJ)
  have hE := dyadicTotientEnvelope_one_le J
  have hprime : 1+2*(∑ p ∈ Nat.primesLE ⌊2*x^2⌋₊,((p-1:ℕ):ℝ)⁻¹) ≤
      (1+6*D)*(1+B x) := by nlinarith
  have hM' := dyadic_totient_reciprocal_mass hJ M hM
  have hM'' : (∑ m ∈ M,(m:ℝ)⁻¹) ≤ 5*dyadicTotientEnvelope J*(1+Real.log J) := by nlinarith
  calc
    _ ≤ (1+2*∑ p ∈ Nat.primesLE ⌊2*x^2⌋₊,((p-1:ℕ):ℝ)⁻¹)*(∑ m ∈ M,(m:ℝ)⁻¹) :=
      singlePrimeExtensions_mass _ _ (fun p hp => (Nat.mem_primesLE.mp hp).2)
    _ ≤ ((1+6*D)*(1+B x))*(5*dyadicTotientEnvelope J*(1+Real.log J)) :=
      mul_le_mul hprime hM'' (Finset.sum_nonneg (fun m _ => inv_nonneg.mpr (Nat.cast_nonneg _))) (by positivity)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BootstrapGoodCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Count the surviving values by a large leading prime and smaller residual values. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem bootstrap_good_count : ∃ C : ℝ,0 < C ∧ ∀ᶠ x : ℝ in atTop,
    ∀ J : ℕ,1 ≤ J → Real.exp ((Real.log x)^(81/100:ℝ)) ≤ (2:ℝ)^J →
    ∀ Q : Finset ℕ,(∀ v ∈ Q,IsTotient v ∧ BootstrapGood x v ∧
      x^(3/4:ℝ) < (v:ℝ) ∧ (v:ℝ) ≤ x) →
    (Q.card:ℝ) ≤ C*(x/Real.log x)*(1+B x)*dyadicTotientEnvelope J*(1+Real.log J) := by
  classical
  obtain ⟨C,hC,hmass⟩ := bootstrap_residual_mass
  refine ⟨64*C,by positivity,?_⟩
  filter_upwards [large_prime_totient_count,bootstrap_cofactor_size,
    bootstrap_residual_quarter,eventually_ge_atTop (Real.exp (Real.exp 1)),
    eventually_gt_atTop (1:ℝ)] with x hcount hsize hquarter hx hx1
  intro J hJ hY Q hQ
  let M := totientValues ((2:ℝ)^J)
  let P := Nat.primesLE ⌊2*x^2⌋₊
  let R := singlePrimeExtensions P M
  have hM : ∀ m ∈ M,IsTotient m ∧ (m:ℝ) ≤ (2:ℝ)^J := by
    intro m hm
    obtain ⟨hm,hmt⟩ := Finset.mem_filter.mp hm
    exact ⟨hmt,(Nat.cast_le.mpr (Finset.mem_Icc.mp hm).2).trans (Nat.floor_le (by positivity))⟩
  have hR : ∀ d ∈ R,0 < d := singlePrimeExtensions_pos
    (fun p hp => (Nat.mem_primesLE.mp hp).2) (fun m hm => isTotient_pos (hM m hm).1)
  have hcover : ∀ v ∈ Q,∃ n p : ℕ,0 < n ∧ n.totient=v ∧ p.Prime ∧ p ∣ n ∧
      x^(1/4:ℝ) ≤ p ∧ (v:ℝ) ≤ x ∧ (n/p).totient ∈ R := by
    intro v hv
    obtain ⟨ht,hgood,hvlo,hvhi⟩ := hQ v hv
    obtain ⟨n,hn,hφ⟩ := ht
    have hΩ : (n.totient.primeFactorsList.length:ℝ) ≤ 5*B x := by
      rw [hφ]
      exact hgood.1.1
    have hs := hsize n hn hΩ (hgood.2 n hn hφ)
    have hp := quarter_prime_of_residual hx1 hn (hs.trans hquarter) (by rwa [hφ])
    have hprime := quarter_fordPrime_prime hx1 hp
    have hpn : fordPrime n 0 ∣ n := by
      refine ⟨fordPrime n 1*fordCofactor n 2,?_⟩
      exact (ford_first_two_factorization hn).trans (mul_assoc _ _ _)
    have hres : (n/fordPrime n 0).totient ∈ R := by
      have hd : n/fordPrime n 0=fordCofactor n 1 := by
        calc
          n/fordPrime n 0 = fordCofactor n 0/fordPrime n 0 := by rw [fordCofactor_zero hn]
          _ = _ := fordCofactor_div n 0
      rw [hd]
      apply cofactor_singlePrimeExtensions
      · have hmpos := Nat.totient_pos.mpr (fordCofactor_pos n 2)
        have hmle : ((fordCofactor n 2).totient:ℝ) ≤ (2:ℝ)^J :=
          (Nat.cast_le.mpr (Nat.totient_le _)).trans (hs.trans hY)
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hmpos,Nat.le_floor hmle⟩,
          ⟨fordCofactor n 2,fordCofactor_pos n 2,rfl⟩⟩
      · intro hp1
        apply Nat.mem_primesLE.mpr
        refine ⟨Nat.le_floor ?_,hp1⟩
        have hnBound : (n:ℝ) ≤ 2*x^2 := by
          have hnφ : (n:ℝ) ≤ 2*(n.totient:ℝ)^2 := by exact_mod_cast totient_preimage_quadratic hn
          have hv0 : (0:ℝ) ≤ v := Nat.cast_nonneg _
          rw [hφ] at hnφ
          exact hnφ.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hv0 hvhi 2) (by norm_num))
        exact (Nat.cast_le.mpr (fordPrime_le_self hn 1)).trans hnBound
    exact ⟨n,fordPrime n 0,hn,hφ,hprime,hpn,hp,hvhi,hres⟩
  have hh := hcount R Q hR hcover
  have hm := hmass x hx J hJ M hM
  have hlog : 0 < Real.log x := Real.log_pos hx1
  calc
    _ ≤ (64*x/Real.log x)*(∑ d ∈ R,(d:ℝ)⁻¹) := hh
    _ ≤ (64*x/Real.log x)*(C*(1+B x)*dyadicTotientEnvelope J*(1+Real.log J)) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BootstrapPointwise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-envelope bootstrap inequality at a single dyadic endpoint. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem bootstrap_pointwise : ∃ C : ℝ,0 < C ∧ ∃ ε : ℕ → ℝ,
    Tendsto ε atTop (nhds 0) ∧ ∀ᶠ J : ℕ in atTop,∀ K : ℕ,1 ≤ K →
    Real.exp ((Real.log ((2:ℝ)^J))^(81/100:ℝ)) ≤ (2:ℝ)^K →
    V ((2:ℝ)^J) ≤ ((2:ℝ)^J)^(3/4:ℝ)+
      ε J*(dyadicTotientEnvelope J*(2:ℝ)^J/Real.log ((2:ℝ)^J))+
      C*((2:ℝ)^J/Real.log ((2:ℝ)^J))*(1+B ((2:ℝ)^J))*
        dyadicTotientEnvelope K*(1+Real.log K) := by
  classical
  obtain ⟨C,hC,hgood⟩ := bootstrap_good_count
  obtain ⟨ε,hε,hbad⟩ := bootstrap_good_value_discard
  refine ⟨C,hC,ε,hε,?_⟩
  have hlim : Tendsto (fun J : ℕ => (2:ℝ)^J) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  filter_upwards [hlim.eventually hgood,hbad] with J hgood hbad
  intro K hK hsize
  let x := (2:ℝ)^J
  let T := totientValues x
  let A : Finset ℕ := T.filter (fun (v : ℕ) => (v:ℝ) ≤ x^(3/4:ℝ))
  let D : Finset ℕ := (T\A).filter (fun (v : ℕ) => ¬BootstrapGood x v)
  let Q : Finset ℕ := T\(A∪D)
  have hT (v : ℕ) (hv : v ∈ T) : IsTotient v ∧ (v:ℝ) ≤ x := by
    obtain ⟨hv,ht⟩ := Finset.mem_filter.mp hv
    exact ⟨ht,(Nat.cast_le.mpr (Finset.mem_Icc.mp hv).2).trans (Nat.floor_le (by positivity))⟩
  have hA : (A.card:ℝ) ≤ x^(3/4:ℝ) := by
    have hsub : A ⊆ totientValues (x^(3/4:ℝ)) := by
      intro v hv
      obtain ⟨hv,hs⟩ := Finset.mem_filter.mp hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨isTotient_pos (hT v hv).1,Nat.le_floor hs⟩,(hT v hv).1⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (V_le_self (by positivity))
  have hD := hbad D (by
    intro v hv
    obtain ⟨hv,hh⟩ := Finset.mem_filter.mp hv
    have h := hT v (Finset.mem_sdiff.mp hv).1
    refine ⟨h.1,?_,hh⟩
    have hh : (v:ℝ) ≤ (2:ℝ)^J := h.2
    exact_mod_cast hh)
  have hQ := hgood K hK hsize Q (by
    intro v hv
    obtain ⟨hv,hnot⟩ := Finset.mem_sdiff.mp hv
    have hnotA : v ∉ A := fun ha => hnot (Finset.mem_union_left _ ha)
    have hnotD : v ∉ D := fun hd => hnot (Finset.mem_union_right _ hd)
    have hlarge : x^(3/4:ℝ) < (v:ℝ) := by
      by_contra hh
      exact hnotA (Finset.mem_filter.mpr ⟨hv,le_of_not_gt hh⟩)
    have hg : BootstrapGood x v := by
      by_contra hh
      exact hnotD (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hv,hnotA⟩,hh⟩)
    exact ⟨(hT v hv).1,hg,hlarge,(hT v hv).2⟩)
  have hc : (T.card:ℝ) ≤ (A.card:ℝ)+(D.card:ℝ)+(Q.card:ℝ) := by
    have hsub : T ⊆ A∪D∪Q := by
      intro v hv
      by_cases ha : v ∈ A∪D
      · exact Finset.mem_union_left _ ha
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hv,ha⟩)
    have hu : (A∪D∪Q).card ≤ (A∪D).card+Q.card := Finset.card_union_le _ _
    have had : (A∪D).card ≤ A.card+D.card := Finset.card_union_le _ _
    have hh : T.card ≤ A.card+D.card+Q.card := by have := Finset.card_le_card hsub; omega
    exact_mod_cast hh
  exact hc.trans (add_le_add (add_le_add hA hD) hQ)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BootstrapIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete strictly smaller dyadic index for the counting bootstrap. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma bootstrap_index_bounds : ∀ᶠ J : ℕ in atTop,
    1 ≤ bootstrapIndex J ∧ bootstrapIndex J < J ∧
    Real.log (bootstrapIndex J:ℝ) ≤ (41/50:ℝ)*Real.log J ∧
    Real.exp ((Real.log ((2:ℝ)^J))^(81/100:ℝ)) ≤ (2:ℝ)^(bootstrapIndex J) := by
  have ht : Tendsto (fun J : ℕ => (J:ℝ)^(1/100:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/100)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop (3:ℝ)),eventually_ge_atTop (2:ℕ)] with J hJp hJ
  have hJ1 : (1:ℝ) < J := by exact_mod_cast (show 1 < J by omega)
  have hJ0 : (0:ℝ) < J := by linarith
  have h9 : 1 ≤ (J:ℝ)^(81/100:ℝ) := Real.one_le_rpow hJ1.le (by norm_num)
  have hprod : (J:ℝ)^(81/100:ℝ)*(J:ℝ)^(1/100:ℝ)=(J:ℝ)^(41/50:ℝ) := by
    rw [← Real.rpow_add hJ0]
    norm_num
  have h3 : 3*(J:ℝ)^(81/100:ℝ) ≤ (J:ℝ)^(41/50:ℝ) := by
    rw [← hprod]
    nlinarith only [mul_le_mul_of_nonneg_left hJp (by positivity : 0 ≤ (J:ℝ)^(81/100:ℝ))]
  have hKlo : 2*(J:ℝ)^(81/100:ℝ) ≤ (bootstrapIndex J:ℝ) := by
    have hf := Nat.sub_one_lt_floor ((J:ℝ)^(41/50:ℝ))
    change (J:ℝ)^(41/50:ℝ)-1 < (bootstrapIndex J:ℝ) at hf
    linarith
  have hK1 : 1 ≤ bootstrapIndex J := by
    have hh : (1:ℝ) ≤ bootstrapIndex J := by linarith
    exact_mod_cast hh
  have hK0 : (0:ℝ) < bootstrapIndex J := by exact_mod_cast (show 0 < bootstrapIndex J by omega)
  have hKhi : (bootstrapIndex J:ℝ) ≤ (J:ℝ)^(41/50:ℝ) := Nat.floor_le (by positivity)
  have hKlt : bootstrapIndex J < J := by
    have hh : (J:ℝ)^(41/50:ℝ) < J := by
      calc
        _ < (J:ℝ)^(1:ℝ) := Real.rpow_lt_rpow_of_exponent_lt hJ1 (by norm_num)
        _ = _ := Real.rpow_one _
    exact_mod_cast hKhi.trans_lt hh
  refine ⟨hK1,hKlt,?_,?_⟩
  · have hh := Real.log_le_log hK0 hKhi
    rwa [Real.log_rpow hJ0] at hh
  · have hlog2 : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hlog21 : Real.log (2:ℝ) ≤ 1 := by linarith [Real.log_two_lt_d9]
    have hlog : Real.log ((2:ℝ)^J) ≤ J := by
      rw [Real.log_pow]
      nlinarith only [mul_le_mul_of_nonneg_left hlog21 hJ0.le]
    have hpow : (Real.log ((2:ℝ)^J))^(81/100:ℝ) ≤ (J:ℝ)^(81/100:ℝ) :=
      Real.rpow_le_rpow (Real.log_nonneg (one_le_pow₀ (by norm_num))) hlog (by norm_num)
    have hb : (Real.log ((2:ℝ)^J))^(81/100:ℝ) ≤ (bootstrapIndex J:ℝ)*Real.log 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hlog2 hK0.le]
    calc
      _ ≤ Real.exp ((bootstrapIndex J:ℝ)*Real.log 2) := Real.exp_le_exp.mpr hb
      _ = _ := by rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BootstrapMajorant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete logarithmic majorant for the counting recurrence. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma bootstrapHeight_one_le (J : ℕ) : 1 ≤ bootstrapHeight J := by
  have hh := Real.log_nonneg (by have := Nat.cast_nonneg (α:=ℝ) J; linarith : (1:ℝ) ≤ (J:ℝ)+1)
  dsimp [bootstrapHeight]
  linarith

lemma bootstrapHeight_mono : Monotone bootstrapHeight := by
  intro I J hIJ
  change 1+Real.log ((I:ℝ)+1) ≤ 1+Real.log ((J:ℝ)+1)
  have hh : (I:ℝ) ≤ J := Nat.cast_le.mpr hIJ
  have hle : (I:ℝ)+1 ≤ (J:ℝ)+1 := by linarith
  have ht := Real.log_le_log (by positivity : 0 < (I:ℝ)+1) hle
  linarith

lemma bootstrapMajorant_one_le (J : ℕ) : 1 ≤ bootstrapMajorant J := Real.one_le_exp (by positivity)

lemma bootstrapMajorant_mono : Monotone bootstrapMajorant := by
  intro I J hIJ
  apply Real.exp_le_exp.mpr
  have hI : 0 ≤ Real.log (bootstrapHeight I) := Real.log_nonneg (bootstrapHeight_one_le I)
  have hh := Real.log_le_log (lt_of_lt_of_le zero_lt_one (bootstrapHeight_one_le I)) (bootstrapHeight_mono hIJ)
  nlinarith

lemma bootstrapHeight_tendsto : Tendsto bootstrapHeight atTop atTop := by
  have hi : Tendsto (fun J : ℕ => (J:ℝ)+1) atTop atTop :=
    by
      apply tendsto_atTop.mpr
      intro b
      filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (b-1))] with J hJ
      linarith
  exact tendsto_atTop_add_const_left _ 1 (Real.tendsto_log_atTop.comp hi)

lemma majorant_real_drop {b c : ℝ} (hc : 1 ≤ c) (hcb : c ≤ (83/100:ℝ)*b)
    (hlog : 5 ≤ Real.log b) :
    Real.exp (9*(Real.log c)^2)*b^3 ≤ Real.exp (9*(Real.log b)^2) := by
  have hb : 0 < b := by nlinarith
  have hc0 : 0 < c := by linarith
  have hlogc : 0 ≤ Real.log c := Real.log_nonneg hc
  have hh := Real.log_le_log hc0 hcb
  rw [Real.log_mul (by norm_num : (83/100:ℝ)≠0) hb.ne'] at hh
  have hr : Real.log (83/100:ℝ) ≤ -(17/100:ℝ) := by
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<83/100)
    linarith
  have hs : (Real.log c)^2 ≤ (Real.log b-17/100)^2 := by nlinarith
  have he : 9*(Real.log c)^2+3*Real.log b ≤ 9*(Real.log b)^2 := by nlinarith
  have hp : b^3=Real.exp (3*Real.log b) := by
    simpa only [Nat.cast_ofNat,Real.exp_log hb] using (Real.exp_nat_mul (Real.log b) 3).symm
  rw [hp,← Real.exp_add]
  exact Real.exp_le_exp.mpr he

lemma bootstrap_majorant_contraction (A : ℝ) : ∀ᶠ J : ℕ in atTop,
    A*(1+Real.log J)^2*bootstrapMajorant (bootstrapIndex J) ≤ bootstrapMajorant J/4 := by
  have hlarge : ∀ᶠ J : ℕ in atTop,100*(1+Real.log 2) ≤ Real.log (J:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  have hpow : ∀ᶠ J : ℕ in atTop,4*max A 0 ≤ bootstrapHeight J :=
    bootstrapHeight_tendsto.eventually (eventually_ge_atTop _)
  filter_upwards [bootstrap_index_bounds,hlarge,hpow,
    (Real.tendsto_log_atTop.comp bootstrapHeight_tendsto).eventually (eventually_ge_atTop (5:ℝ))] with J hidx hlarge hpow hlog
  obtain ⟨hK,hKJ,hLK,_⟩ := hidx
  have hJ : 0 < J := by omega
  have hJ0 : (0:ℝ) < J := by exact_mod_cast hJ
  have hK0 : (0:ℝ) < bootstrapIndex J := by exact_mod_cast (show 0 < bootstrapIndex J by omega)
  have hheight : bootstrapHeight (bootstrapIndex J) ≤ (83/100:ℝ)*bootstrapHeight J := by
    have hkplus : (bootstrapIndex J:ℝ)+1 ≤ 2*bootstrapIndex J := by
      have hh : (1:ℝ) ≤ bootstrapIndex J := by exact_mod_cast hK
      linarith
    have hl := Real.log_le_log (by positivity : 0 < (bootstrapIndex J:ℝ)+1) hkplus
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hK0.ne'] at hl
    have hjplus := Real.log_le_log hJ0 (by linarith : (J:ℝ) ≤ (J:ℝ)+1)
    dsimp [bootstrapHeight]
    linarith
  have hdrop := majorant_real_drop (bootstrapHeight_one_le _) hheight hlog
  have hb := bootstrapHeight_one_le J
  have hB : 0 < bootstrapHeight J := by linarith
  have hln : 0 ≤ 1+Real.log (J:ℝ) := by
    have hh : 0 ≤ Real.log (J:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ J by omega))
    linarith
  have hhl : 1+Real.log (J:ℝ) ≤ bootstrapHeight J := by
    have hj : (J:ℝ) ≤ (J:ℝ)+1 := by linarith
    dsimp [bootstrapHeight]
    linarith [Real.log_le_log hJ0 hj]
  have hcoeff : 4*A*(1+Real.log J)^2 ≤ (bootstrapHeight J)^3 := by
    have hs : (1+Real.log (J:ℝ))^2 ≤ (bootstrapHeight J)^2 := by nlinarith
    have hA : A ≤ max A 0 := le_max_left _ _
    have hA0 : 0 ≤ max A 0 := le_max_right _ _
    nlinarith [mul_le_mul_of_nonneg_left hs hA0,
      mul_le_mul_of_nonneg_right hpow (sq_nonneg (bootstrapHeight J))]
  have hG : 0 ≤ bootstrapMajorant (bootstrapIndex J) := (Real.exp_pos _).le
  change bootstrapMajorant (bootstrapIndex J)*(bootstrapHeight J)^3 ≤ bootstrapMajorant J at hdrop
  nlinarith [mul_le_mul_of_nonneg_right hcoeff hG]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BootstrapNormalized
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalize the pointwise bootstrap by the logarithmic counting scale. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma bootstrap_small_term : ∀ᶠ J : ℕ in atTop,
    (((2:ℝ)^J)^(3/4:ℝ))*(J:ℝ)/(2:ℝ)^J ≤ 1 := by
  have hl : 0 < Real.log (2:ℝ)/4 := by positivity
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1:ℝ) (Real.log 2/4) hl).comp
    tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with J hJ
  have he : (((2:ℝ)^J)^(3/4:ℝ))*(J:ℝ)/(2:ℝ)^J =
      (J:ℝ)*Real.exp (-(Real.log 2/4)*(J:ℝ)) := by
    have hp : (2:ℝ)^J = Real.exp ((J:ℝ)*Real.log 2) := by
      rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
    rw [hp,Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
    rw [div_eq_mul_inv,← Real.exp_neg]
    calc
      _ = (J:ℝ)*(Real.exp (((J:ℝ)*Real.log 2)*(3/4:ℝ))*Real.exp (-((J:ℝ)*Real.log 2))) := by ring
      _ = _ := by
        rw [← Real.exp_add]
        apply congrArg (fun t : ℝ => (J:ℝ)*Real.exp t)
        ring
  rw [he]
  simpa only [Function.comp_apply,Real.rpow_one] using hJ.le

 theorem bootstrap_normalized : ∃ A : ℝ,0 < A ∧ ∃ δ : ℕ → ℝ,
    Tendsto δ atTop (nhds 0) ∧ ∀ᶠ J : ℕ in atTop,
    1 ≤ bootstrapIndex J ∧ bootstrapIndex J < J ∧
    V ((2:ℝ)^J)*(J:ℝ)/(2:ℝ)^J ≤ 1+δ J*dyadicTotientEnvelope J+
      A*(1+Real.log J)^2*dyadicTotientEnvelope (bootstrapIndex J) := by
  obtain ⟨C,hC,ε,hε,hpoint⟩ := bootstrap_pointwise
  let δ := fun J => ε J/Real.log 2
  have hδ : Tendsto δ atTop (nhds 0) := by
    simpa only [zero_div] using hε.div_const (Real.log 2)
  refine ⟨C/Real.log 2,by positivity,δ,hδ,?_⟩
  filter_upwards [hpoint,bootstrap_index_bounds,bootstrap_small_term,eventually_ge_atTop (2:ℕ)] with J hp hidx hs hJ
  obtain ⟨hK,hKJ,hlogK,hsize⟩ := hidx
  refine ⟨hK,hKJ,?_⟩
  let x := (2:ℝ)^J
  have hx0 : 0 < x := by positivity
  have hJ0 : (0:ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hlog2 : 0 < Real.log (2:ℝ) := by positivity
  have hlog : Real.log x = (J:ℝ)*Real.log 2 := Real.log_pow _ _
  have hxlog : 0 < Real.log x := by rw [hlog]; positivity
  have hb : B x ≤ Real.log J := by
    unfold B
    rw [hlog,Real.log_mul hJ0.ne' hlog2.ne']
    have hh : Real.log (Real.log (2:ℝ)) ≤ 0 := Real.log_nonpos hlog2.le (by linarith [Real.log_two_lt_d9])
    linarith
  have hB0 : 0 ≤ B x := by
    have hj2 : (2:ℝ) ≤ J := by exact_mod_cast hJ
    have hl : 1 ≤ Real.log x := by rw [hlog]; nlinarith [Real.log_two_gt_d9]
    exact Real.log_nonneg hl
  have hlj : 0 ≤ Real.log (J:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ J by omega))
  have hKlog : 1+Real.log (bootstrapIndex J:ℝ) ≤ 1+Real.log J := by
    have hh : Real.log (bootstrapIndex J:ℝ) ≤ Real.log (J:ℝ) :=
      Real.log_le_log (by exact_mod_cast (show 0 < bootstrapIndex J by omega))
        (by exact_mod_cast hKJ.le)
    linarith
  have hh := mul_le_mul_of_nonneg_right (hp (bootstrapIndex J) hK hsize) (div_nonneg hJ0.le hx0.le)
  have hmain :
      C*(x/Real.log x)*(1+B x)*dyadicTotientEnvelope (bootstrapIndex J)*
        (1+Real.log (bootstrapIndex J))*(J:ℝ)/x ≤
      (C/Real.log 2)*(1+Real.log J)^2*dyadicTotientEnvelope (bootstrapIndex J) := by
    have hid : C*(x/Real.log x)*(1+B x)*dyadicTotientEnvelope (bootstrapIndex J)*
        (1+Real.log (bootstrapIndex J))*(J:ℝ)/x =
        (C/Real.log 2)*((1+B x)*(1+Real.log (bootstrapIndex J)))*dyadicTotientEnvelope (bootstrapIndex J) := by
      rw [hlog]
      field_simp
    rw [hid]
    apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans (dyadicTotientEnvelope_one_le _))
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa only [pow_two] using (mul_le_mul (by linarith : 1+B x ≤ 1+Real.log J) hKlog
      (by have := Real.log_nonneg (show (1:ℝ) ≤ bootstrapIndex J by exact_mod_cast hK); linarith)
      (by linarith))
  have herr : ε J*(dyadicTotientEnvelope J*x/Real.log x)*(J:ℝ)/x=δ J*dyadicTotientEnvelope J := by
    dsimp [δ]
    rw [hlog]
    field_simp
  have hout : V x*(J:ℝ)/x ≤ x^(3/4:ℝ)*(J:ℝ)/x+
      δ J*dyadicTotientEnvelope J+
      (C/Real.log 2)*(1+Real.log J)^2*dyadicTotientEnvelope (bootstrapIndex J) := by
    calc
      _ ≤ (x^(3/4:ℝ)+ε J*(dyadicTotientEnvelope J*x/Real.log x)+
          C*(x/Real.log x)*(1+B x)*dyadicTotientEnvelope (bootstrapIndex J)*
            (1+Real.log (bootstrapIndex J)))*((J:ℝ)/x) := by simpa only [mul_div_assoc] using hh
      _ = x^(3/4:ℝ)*(J:ℝ)/x+δ J*dyadicTotientEnvelope J+
          C*(x/Real.log x)*(1+B x)*dyadicTotientEnvelope (bootstrapIndex J)*
            (1+Real.log (bootstrapIndex J))*(J:ℝ)/x := by rw [add_mul,add_mul]; rw [← herr]; ring
      _ ≤ _ := add_le_add le_rfl hmain
  exact hout.trans (add_le_add (add_le_add hs le_rfl) le_rfl)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_DyadicEnvelopeMaximum
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite maxima for the dyadic counting envelope. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma dyadicTotientEnvelope_maximum (J : ℕ) :
    dyadicTotientEnvelope J=1 ∨ ∃ k ≤ J,
      dyadicTotientEnvelope J=V ((2:ℝ)^k)*(k:ℝ)/(2:ℝ)^k := by
  classical
  let f := fun k : ℕ => V ((2:ℝ)^k)*(k:ℝ)/(2:ℝ)^k
  have hne : (Finset.range (J+1)).Nonempty := by simp
  obtain ⟨k,hk,he⟩ := Finset.exists_mem_eq_sup' hne f
  by_cases h : (Finset.range (J+1)).sup' hne f ≤ 1
  · left
    exact max_eq_left h
  · right
    refine ⟨k,by simpa only [Finset.mem_range,Nat.lt_add_one_iff] using hk,?_⟩
    change max 1 ((Finset.range (J+1)).sup' hne f)=f k
    rw [max_eq_right (le_of_not_ge h)]
    exact he

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BootstrapEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The global counting bootstrap from the finite dyadic recurrence. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

theorem bootstrap_envelope_bound : ∃ C : ℝ,0 < C ∧ ∀ J : ℕ,
    dyadicTotientEnvelope J ≤ C*Real.exp (9*(Real.log (1+Real.log ((J:ℝ)+1)))^2) := by
  obtain ⟨A,hA,δ,hδ,hrec⟩ := bootstrap_normalized
  have hsmall := hδ.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1/4))
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hrec.and (hsmall.and (bootstrap_majorant_contraction A)))
  let C := max 4 (dyadicTotientEnvelope N)
  have hC4 : 4 ≤ C := le_max_left _ _
  have hC : 0 < C := by linarith
  refine ⟨C,hC,?_⟩
  have hbound : ∀ J : ℕ,dyadicTotientEnvelope J ≤ C*bootstrapMajorant J := by
    intro J
    induction J using Nat.strong_induction_on with
    | h J ih =>
      by_cases hJN : J ≤ N
      · calc
          _ ≤ dyadicTotientEnvelope N := dyadicTotientEnvelope_mono hJN
          _ ≤ C := le_max_right _ _
          _ ≤ _ := by nlinarith [bootstrapMajorant_one_le J]
      · have hNJ : N ≤ J := by omega
        obtain ⟨⟨hK,hKJ,hpoint⟩,hδJ,hcontract⟩ := hN J hNJ
        rcases dyadicTotientEnvelope_maximum J with he|⟨k,hk,he⟩
        · rw [he]
          nlinarith [bootstrapMajorant_one_le J]
        · by_cases hkJ : k < J
          · calc
              _ = V ((2:ℝ)^k)*(k:ℝ)/(2:ℝ)^k := he
              _ ≤ dyadicTotientEnvelope k := dyadicTotientEnvelope_term_le le_rfl
              _ ≤ C*bootstrapMajorant k := ih k hkJ
              _ ≤ _ := mul_le_mul_of_nonneg_left (bootstrapMajorant_mono hk) hC.le
          · have hkEq : k=J := by omega
            subst k
            rw [← he] at hpoint
            have hterm : A*(1+Real.log J)^2*dyadicTotientEnvelope (bootstrapIndex J) ≤
                C*bootstrapMajorant J/4 := by
              calc
                _ ≤ A*(1+Real.log J)^2*(C*bootstrapMajorant (bootstrapIndex J)) :=
                  mul_le_mul_of_nonneg_left (ih _ hKJ) (by positivity)
                _ = C*(A*(1+Real.log J)^2*bootstrapMajorant (bootstrapIndex J)) := by ring
                _ ≤ C*(bootstrapMajorant J/4) := mul_le_mul_of_nonneg_left hcontract hC.le
                _ = _ := by ring
            have hE : 0 ≤ dyadicTotientEnvelope J := zero_le_one.trans (dyadicTotientEnvelope_one_le J)
            have herror := mul_le_mul_of_nonneg_right hδJ.le hE
            have hG := bootstrapMajorant_one_le J
            nlinarith
  intro J
  exact hbound J

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SmoothTotientMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-set consequence of Ford, *The distribution of totients*,
Lemma 4.3 (2013 revision), proved from the counting bootstrap and Rankin tail. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma smooth_mass_log_budget : ∀ᶠ b : ℝ in atTop,
    0 < b ∧ 32 ≤ Real.log b ∧ Real.log (100*b)+4 ≤ b := by
  have hl := Real.isLittleO_log_id_atTop.bound (show (0:ℝ)<1/2 by norm_num)
  filter_upwards [hl,eventually_ge_atTop (2*(Real.log 100+4)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (32:ℝ)),
    eventually_gt_atTop (1:ℝ)] with b hb hbC hlog hb1
  have hb0 : 0 < b := by linarith
  have hh : Real.log b ≤ b/2 := by
    have ht := (le_abs_self (Real.log b)).trans (by
      simpa only [Real.norm_eq_abs,abs_of_pos hb0,id_eq] using hb)
    linarith
  refine ⟨hb0,hlog,?_⟩
  rw [Real.log_mul (by norm_num : (100:ℝ)≠0) hb0.ne']
  linarith

lemma smooth_mass_exponential {b : ℝ} (hb : 0 < b) (hlog : 32 ≤ Real.log b) :
    b*Real.exp (9*(Real.log (2*b))^2) ≤ Real.exp (10*(Real.log b)^2) := by
  have h2 : 0 ≤ Real.log (2:ℝ) := Real.log_nonneg (by norm_num)
  have h2' : Real.log (2:ℝ) ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hs : (Real.log (2*b))^2 ≤ (Real.log b+1)^2 := by
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hb.ne']
    nlinarith
  have he : Real.log b+9*(Real.log (2*b))^2 ≤ 10*(Real.log b)^2 := by nlinarith
  calc
    _ = Real.exp (Real.log b+9*(Real.log (2*b))^2) := by rw [Real.exp_add,Real.exp_log hb]
    _ ≤ _ := Real.exp_le_exp.mpr he

theorem smooth_totient_reciprocal_mass : ∃ C : ℝ,0 < C ∧ ∀ᶠ y : ℕ in atTop,
    ∀ Q : Finset ℕ,(∀ v ∈ Q,IsTotient v ∧ largestPrimeFactor v ≤ y) →
    (∑ v ∈ Q,(v:ℝ)⁻¹) ≤ C*Real.exp (10*(Real.log (B y))^2) := by
  classical
  obtain ⟨C,hC,hglobal⟩ := bootstrap_envelope_bound
  obtain ⟨D,hD,hmertens⟩ := mertensProductInput
  refine ⟨1+8*C+D^4,by positivity,?_⟩
  have hB : Tendsto (fun y : ℕ => B y) atTop atTop := B_tendsto.comp tendsto_natCast_atTop_atTop
  filter_upwards [hB.eventually smooth_mass_log_budget,hB.eventually (eventually_ge_atTop (2:ℝ)),
    eventually_ge_atTop (4:ℕ)] with y hbudget hby hy
  obtain ⟨hb,hlogb,hsmall⟩ := hbudget
  have hyl : 0 < Real.log (y:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  let Z := 100*B y*Real.log y
  let T := Real.exp Z
  let J := countingDyadicIndex T
  have hT4 : 4 ≤ T := by
    have hz : 3 ≤ Z := by
      have hylog : 1 ≤ Real.log (y:ℝ) := by
        have hh := Real.log_le_log (by norm_num : (0:ℝ)<4) (show (4:ℝ) ≤ y by exact_mod_cast hy)
        rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow] at hh
        norm_num only [Nat.cast_ofNat] at hh
        linarith [Real.log_two_gt_d9]
      dsimp [Z]
      nlinarith
    exact le_trans (by linarith : 4 ≤ Z+1) (Real.add_one_le_exp Z)
  obtain ⟨hJ,hTJ,hheight⟩ := counting_dyadic_index_bounds hT4
  have hBT : B T = B y+Real.log (100*B y) := by
    change Real.log (Real.log (Real.exp (100*B y*Real.log y))) = _
    rw [Real.log_exp,Real.log_mul (by positivity : 100*B y ≠ 0) hyl.ne']
    change Real.log (100*B y)+B y=B y+Real.log (100*B y)
    ring
  have hh : bootstrapHeight J ≤ 2*B y := by
    rw [hBT] at hheight
    linarith
  have hlogJ : 1+Real.log (J:ℝ) ≤ bootstrapHeight J := by
    have hp : (0:ℝ) < J := by exact_mod_cast (show 0 < J by omega)
    have hj := Real.log_le_log hp (show (J:ℝ) ≤ (J:ℝ)+1 by linarith)
    dsimp [bootstrapHeight]
    linarith
  have hE : dyadicTotientEnvelope J ≤ C*Real.exp (9*(Real.log (2*B y))^2) := by
    have hH := bootstrapHeight_one_le J
    have hlog := Real.log_le_log (by linarith) hh
    have hnon : 0 ≤ Real.log (bootstrapHeight J) := Real.log_nonneg hH
    have hp : Real.exp (9*(Real.log (bootstrapHeight J))^2) ≤ Real.exp (9*(Real.log (2*B y))^2) :=
      Real.exp_le_exp.mpr (by nlinarith)
    exact (hglobal J).trans (mul_le_mul_of_nonneg_left hp hC.le)
  intro Q hQ
  let A := Q.filter (fun v : ℕ => (v:ℝ) ≤ T)
  let E := Q.filter (fun v : ℕ => ¬(v:ℝ) ≤ T)
  have hA := dyadic_totient_reciprocal_mass hJ A (by
    intro v hv
    obtain ⟨hv,hvT⟩ := Finset.mem_filter.mp hv
    exact ⟨(hQ v hv).1,hvT.trans hTJ⟩)
  have hA' : (∑ v ∈ A,(v:ℝ)⁻¹) ≤ (1+8*C)*Real.exp (10*(Real.log (B y))^2) := by
    have hJlog : 0 ≤ 1+Real.log (J:ℝ) := by
      have ht := Real.log_nonneg (show (1:ℝ) ≤ J by exact_mod_cast hJ)
      linarith
    have hp := mul_le_mul hE (hlogJ.trans hh) hJlog (by positivity : 0 ≤ C*Real.exp (9*(Real.log (2*B y))^2))
    have hexp := smooth_mass_exponential hb hlogb
    have hone : 1 ≤ Real.exp (10*(Real.log (B y))^2) := Real.one_le_exp (by positivity)
    nlinarith
  have hE' : (∑ v ∈ E,(v:ℝ)⁻¹) ≤ D^4 := by
    have hr := smooth_cofactor_rankin (show 2 ≤ y by omega) Z E (by
      intro v hv
      obtain ⟨hv,hvT⟩ := Finset.mem_filter.mp hv
      have hv0 := isTotient_pos (hQ v hv).1
      refine ⟨hv0,(hQ v hv).2,?_⟩
      exact (Real.lt_log_iff_exp_lt (by exact_mod_cast hv0)).mpr (lt_of_not_ge hvT))
    have hrec : (∑ v ∈ E,(v:ℝ)⁻¹) ≤ ∑ v ∈ E,(v.totient:ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro v hv
      have hp := isTotient_pos (hQ v (Finset.mem_filter.mp hv).1).1
      exact inv_anti₀ (by exact_mod_cast Nat.totient_pos.mpr hp) (Nat.cast_le.mpr (Nat.totient_le v))
    have hprod := hmertens y (by omega)
    have hprod0 : 0 ≤ primeEulerProduct y := le_of_lt (by
      apply Finset.prod_pos
      intro p hp
      have hp1 : (1:ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
      exact div_pos (by linarith) (by linarith))
    have hbound := hr.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hprod0 hprod 4) (by positivity))
    have hid : Real.exp (-Z/(4*Real.log y))*(D*Real.log y)^4 = D^4*Real.exp (-21*B y) := by
      have hz : -Z/(4*Real.log y)= -25*B y := by dsimp [Z]; field_simp <;> ring
      have hpow : (Real.log (y:ℝ))^4=Real.exp (4*B y) := by
        simpa only [Nat.cast_ofNat,B,Real.exp_log hyl] using (Real.exp_nat_mul (B y) 4).symm
      rw [hz,mul_pow,hpow]
      rw [mul_left_comm,← Real.exp_add]
      congr 1
      congr 1
      ring
    rw [hid] at hbound
    exact hrec.trans (hbound.trans (mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr (by linarith))))
  have hsum : (∑ v ∈ Q,(v:ℝ)⁻¹)=(∑ v ∈ A,(v:ℝ)⁻¹)+(∑ v ∈ E,(v:ℝ)⁻¹) := by
    exact (Finset.sum_filter_add_sum_filter_not Q (fun v : ℕ => (v:ℝ) ≤ T) (fun v => (v:ℝ)⁻¹)).symm
  rw [hsum]
  have hone : 1 ≤ Real.exp (10*(Real.log (B y))^2) := Real.one_le_exp (by positivity)
  nlinarith [show 0 ≤ D^4 by positivity]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SmoothTerminalMassBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single all-endpoint smooth residual mass bound for terminal slices. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem smooth_terminal_mass_bound_oai : ∃ C : ℝ,0 < C ∧ ∀ t : ℝ,0 ≤ t →
    ∀ Q : Finset ℕ,(∀ v ∈ Q,IsTotient v ∧
      (largestPrimeFactor v:ℝ) ≤ Real.exp (Real.exp (t+1))) →
    (∑ v ∈ Q,(v:ℝ)⁻¹) ≤ C*Real.exp (10*(Real.log (t+5))^2) := by
  obtain ⟨C,hC,hmass⟩ := smooth_totient_reciprocal_mass
  have hB : Tendsto (fun y : ℕ => B y) atTop atTop := B_tendsto.comp tendsto_natCast_atTop_atTop
  obtain ⟨K,hK⟩ := eventually_atTop.mp
    (hmass.and ((hB.eventually (eventually_ge_atTop (1:ℝ))).and (eventually_ge_atTop (2:ℕ))))
  let D := primeEulerProduct K
  have hD : 0 < D := primeEulerProduct_pos K
  refine ⟨C+D,by positivity,?_⟩
  intro t ht Q hQ
  let y := ⌊Real.exp (Real.exp (t+1))⌋₊
  have hyQ (v) (hv : v ∈ Q) : largestPrimeFactor v ≤ y := Nat.le_floor (hQ v hv).2
  have he : 1 ≤ Real.exp (10*(Real.log (t+5))^2) := Real.one_le_exp (by positivity)
  by_cases hy : K ≤ y
  · obtain ⟨hmass,hBy,hy2⟩ := hK y hy
    have hypos : (0:ℝ) < y := by exact_mod_cast (show 0 < y by omega)
    have hlogy : 0 < Real.log (y:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
    have hyl : (y:ℝ) ≤ Real.exp (Real.exp (t+1)) := Nat.floor_le (Real.exp_pos _).le
    have hByupper : B y ≤ t+1 := by
      apply (Real.log_le_iff_le_exp hlogy).mpr
      exact (Real.log_le_iff_le_exp hypos).mpr hyl
    have hloglower : 0 ≤ Real.log (B y) := Real.log_nonneg hBy
    have hlogupper : Real.log (B y) ≤ Real.log (t+5) :=
      Real.log_le_log (zero_lt_one.trans_le hBy) (by linarith only [hByupper])
    have hs := hmass Q (fun v hv => ⟨(hQ v hv).1,hyQ v hv⟩)
    have hexp : Real.exp (10*(Real.log (B y))^2) ≤ Real.exp (10*(Real.log (t+5))^2) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [hloglower,hlogupper]
    exact (hs.trans (mul_le_mul_of_nonneg_left hexp hC.le)).trans
      (mul_le_mul_of_nonneg_right (by linarith only [hD]) (Real.exp_pos _).le)
  · have hs : (∑ v ∈ Q,(v:ℝ)⁻¹) ≤ D := by
      apply smooth_residual_reciprocal_mass
      intro v hv
      exact ⟨isTotient_pos (hQ v hv).1,(hyQ v hv).trans (by omega)⟩
    calc
      _ ≤ D := hs
      _ ≤ D*Real.exp (10*(Real.log (t+5))^2) := by nlinarith only [he,hD]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hC]) (Real.exp_pos _).le

end TotientAsymptotic

end

end OAI
end

theorem solution : type_of% @OAI.TotientAsymptotic.smooth_terminal_mass_bound_oai := @OAI.TotientAsymptotic.smooth_terminal_mass_bound_oai
