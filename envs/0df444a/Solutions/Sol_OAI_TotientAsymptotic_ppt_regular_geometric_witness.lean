-- Prove2me | solution 1 for OAI.TotientAsymptotic.ppt_regular_geometric_witness
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:37:13.724401+00:00
-- url     : https://prove2.me/submissions/678e0c38-fd89-43b1-ab10-f3be3d8db712

import Batteries.Tactic.Lemma
import Mathlib
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.MvPolynomial.Basic
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
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Squarefree
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
import Mathlib.NumberTheory.SelbergSieve
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
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_Phase
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
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

lemma B_exp_exp (b : ℝ) : B (Real.exp (Real.exp b)) = b := by
  simp only [B, Real.log_exp]

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PublishedComparison
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The published comparison input for the conditional collision proof.

Kevin Ford, *The distribution of totients*, Ramanujan J. 2 (1998), 67–151,
revised arXiv:1104.3264v2 (14 July 2013), Lemma 5.1, pp. 21–22.
The published statement permits `k ≥ 1`, including a single surviving
prime. The author-hosted copy also makes this endpoint explicit:
https://www.ford126.web.illinois.edu/wwwpapers/totients.pdf (Lemma 5.1).
We use its specialization with no auxiliary factors (`l = 0`) and with
the entire left shifted product squarefree above the terminal cutoff. The
latter is already part of the application’s good-witness conditions. All its
cutoff, small-remainder, small-cancelled-product and separation hypotheses
are retained here. Its larger smooth-factor exponent is sufficient for the
application; we do not assume the new comparison proposition of the manuscript.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma squarefreeAbove_of_dvd {m n : ℕ} {Z : ℝ}
    (hmn : m ∣ n) (hn : SquarefreeAbove n Z) : SquarefreeAbove m Z := by
  intro p hp hpZ hpm
  exact hn p hp hpZ (hpm.trans hmn)

lemma shifted_factor_dvd {b : ℕ} (p : Fin b → ℕ) (i : Fin b) :
    p i-1 ∣ shiftedProduct p :=
  Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

lemma squarefree_shifts_of_common_product {b D : ℕ} (t : ShiftedPair b) (Z : ℝ)
    (heq : D * shiftedProduct t.left = t.remainder * shiftedProduct t.right)
    (hsq : SquarefreeAbove (D * shiftedProduct t.left) Z) (i : Fin b) :
    SquarefreeAbove (t.left i-1) Z ∧ SquarefreeAbove (t.right i-1) Z := by
  constructor
  · exact squarefreeAbove_of_dvd ((shifted_factor_dvd t.left i).trans (dvd_mul_left _ _)) hsq
  · have hr : t.right i-1 ∣ t.remainder * shiftedProduct t.right :=
      (shifted_factor_dvd t.right i).trans (dvd_mul_left _ _)
    rw [← heq] at hr
    exact squarefreeAbove_of_dvd hr hsq

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalityAlignment
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
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

lemma omegaIn_prod {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, f i ≠ 0) (U T : ℝ) :
    omegaIn (∏ i ∈ s, f i) U T = ∑ i ∈ s, omegaIn (f i) U T := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [omegaIn]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      omegaIn_mul (hf i (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr (fun j hj => hf j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

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

/-- Taking a totient cannot introduce a prime larger than every prime of its
argument. This also covers `n = 0` under the existing largest-factor convention. -/
lemma largestPrimeFactor_totient_le (n : ℕ) :
    largestPrimeFactor n.totient ≤ largestPrimeFactor n := by
  by_cases hn : n = 0
  · subst n
    simp [largestPrimeFactor]
  apply largestPrimeFactor_le_of_prime_divisors (le_max_left _ _)
  intro q hq hqφ _
  have hdiv : q ∣ n*∏ p ∈ n.primeFactors, (p-1) := by
    rw [← Nat.totient_mul_prod_primeFactors]
    exact hqφ.trans (dvd_mul_right _ _)
  rcases hq.dvd_mul.mp hdiv with hqn | hqp
  · exact prime_dvd_le_largest hq hn hqn
  · obtain ⟨p, hp, hqp⟩ := hq.prime.dvd_finsetProd_iff (fun p : ℕ => p-1) |>.mp hqp
    have hpp := (Nat.mem_primeFactors.mp hp).1
    have hle := Nat.le_of_dvd (Nat.sub_pos_of_lt hpp.one_lt) hqp
    exact hle.trans ((Nat.sub_le _ _).trans
      (prime_dvd_le_largest hpp hn (Nat.mem_primeFactors.mp hp).2.1))

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionAlgebra
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cancellation and the strict-slack comparison for the surviving prime indices. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma log_le_a {j : ℕ} (hj : 1 ≤ j) : Real.log (j : ℝ) ≤ a j := by
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  rw [a_eq_integral]
  have hh := intervalIntegral.integral_mono_on (a := (j : ℝ)) (b := (j+1 : ℝ))
    (by linarith) (intervalIntegrable_const (c := Real.log (j : ℝ)))
    intervalIntegral.intervalIntegrable_log'
    (fun x hx => Real.log_le_log (by linarith) hx.1)
  simpa using hh

lemma a_monotone_positive {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) : a i ≤ a j := by
  rcases eq_or_lt_of_le hij with rfl | hij
  · rfl
  · exact (a_le_log hi).trans ((Real.log_le_log (by positivity)
      (by exact_mod_cast hij)).trans (log_le_a (by omega)))

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

lemma sum_a_Icc (n : ℕ) :
    (∑ j ∈ Finset.Icc 1 n, a j) = (n+1 : ℝ)*Real.log (n+1)-n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    simp only [a, Nat.cast_add, Nat.cast_one]
    ring

lemma comparisonError_le (b : ℕ) (y S : ℝ) (Y U : ℕ → ℝ) (w : ℝ)
    (hwidth : ∀ j ∈ Finset.Icc 1 (b-1), B (Y j)/B y-B (U j)/B y ≤ w) :
    comparisonError b y S Y U ≤
      2*(b-1 : ℕ)*w+Real.sqrt (B S/B y)*
        ∑ i ∈ Finset.Icc 2 b, ((i : ℝ)*Real.log i+i) := by
  unfold comparisonError
  have hh := Finset.sum_le_sum hwidth
  have hc : (∑ _j ∈ Finset.Icc 1 (b-1), w) = (b-1 : ℕ)*w := by simp
  rw [hc] at hh
  linarith

lemma comparisonExponent_le (b : ℕ) (y S : ℝ) (Y U : ℕ → ℝ)
    (σ e w : ℝ)
    (hweighted : (∑ j ∈ Finset.Icc 1 (b-1), a j*(B (Y j)/B y)) ≤
      1-σ+e*(∑ j ∈ Finset.Icc 1 (b-1), a j))
    (hwidth : ∀ j ∈ Finset.Icc 1 (b-1), B (Y j)/B y-B (U j)/B y ≤ w)
    (herror : e*(∑ j ∈ Finset.Icc 1 (b-1), a j)+2*(b-1 : ℕ)*w+
      Real.sqrt (B S/B y)*(∑ i ∈ Finset.Icc 2 b, ((i : ℝ)*Real.log i+i)) ≤ σ/2) :
    -2+(∑ j ∈ Finset.Icc 1 (b-1), a j*(B (Y j)/B y))+
      comparisonError b y S Y U ≤ -1-σ/2 := by
  have hh := comparisonError_le b y S Y U w hwidth
  linarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ComparisonErrorBudget
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit rounding and normality errors fit inside the strict-slack saving. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma sum_a_le_square (b : ℕ) : (∑ j ∈ Finset.Icc 1 b, a j) ≤ (b : ℝ)^2 := by
  rw [sum_a_Icc]
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have hl : Real.log (b+1 : ℝ) ≤ b := by
    simpa using Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < b+1)
  have hh := mul_le_mul_of_nonneg_left hl (show (0 : ℝ) ≤ b+1 by positivity)
  nlinarith

lemma comparison_log_sum_bound {b h : ℕ} (hbh : b ≤ h) (hh : 1 ≤ h) :
    (∑ j ∈ Finset.Icc 2 b, ((j : ℝ)*Real.log j+j)) ≤ 2*(h : ℝ)^3 := by
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hcount : (Finset.Icc 2 b).card ≤ h := by
    simp only [Nat.card_Icc]
    omega
  calc
    _ ≤ ∑ _j ∈ Finset.Icc 2 b, 2*(h : ℝ)^2 := by
      apply Finset.sum_le_sum
      intro j hj
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
      have hjh : (j : ℝ) ≤ h := by exact_mod_cast (Finset.mem_Icc.mp hj).2.trans hbh
      have hl := Real.log_le_self hj0
      have hp := mul_le_mul_of_nonneg_left hl hj0
      nlinarith [sq_nonneg ((h : ℝ)-j)]
    _ = ((Finset.Icc 2 b).card : ℝ)*(2*(h : ℝ)^2) := by simp
    _ ≤ (h : ℝ)*(2*(h : ℝ)^2) := mul_le_mul_of_nonneg_right
      (by exact_mod_cast hcount) (by positivity)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalitySize
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Total factor counts and largest-factor locations for normal shifts. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

private lemma interval_count_partition (l : List ℕ) (n : ℕ) (S : ℝ)
    (hl : ∀ p ∈ l, 1 < p ∧ p ≤ n) :
    (l.filter (fun p : ℕ => decide ((1 : ℝ) < p ∧ (p : ℝ) ≤ S))).length +
      (l.filter (fun p : ℕ => decide (S < p ∧ (p : ℝ) ≤ n))).length = l.length := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have hp := hl p (by simp)
    have h1 : (1 : ℝ) < p := by exact_mod_cast hp.1
    have hn : (p : ℝ) ≤ n := by exact_mod_cast hp.2
    have hh := ih (fun q hq => hl q (by simp [hq]))
    by_cases hS : (p : ℝ) ≤ S
    · rw [List.filter_cons_of_pos (by exact decide_eq_true ⟨h1, hS⟩),
        List.filter_cons_of_neg (by simpa only [decide_eq_true_eq] using
          (show ¬ (S < (p : ℝ) ∧ (p : ℝ) ≤ n) from fun h => (not_lt.mpr hS) h.1)),
        List.length_cons]
      simp only [List.length_cons]
      omega
    · have hS' : S < (p : ℝ) := lt_of_not_ge hS
      rw [List.filter_cons_of_neg (by simpa only [decide_eq_true_eq] using
          (show ¬ ((1 : ℝ) < p ∧ (p : ℝ) ≤ S) from fun h => hS h.2)),
        List.filter_cons_of_pos (by exact decide_eq_true ⟨hS', hn⟩),
        List.length_cons]
      simp only [List.length_cons]
      omega

lemma omegaIn_partition (n : ℕ) (S : ℝ) :
    omegaIn n 1 S + omegaIn n S n = n.primeFactorsList.length := by
  apply interval_count_partition
  intro p hp
  exact ⟨(Nat.prime_of_mem_primeFactorsList hp).one_lt, Nat.le_of_mem_primeFactorsList hp⟩

/-- Ford normality controls the full number of prime occurrences of a shift. -/
lemma normality_total_bound {S : ℝ} {p : ℕ} (hp : IsNormalPrime S p)
    (hS : 1 < S) (hSn : S < (p-1 : ℕ)) (hBS : 0 ≤ B S) :
    (p-1).primeFactorsList.length ≤ 3*B (p-1 : ℕ) := by
  have hn : (1 : ℝ) < (p-1 : ℕ) := hS.trans hSn
  have hB : B S ≤ B (p-1 : ℕ) := by
    apply Real.log_le_log (Real.log_pos hS)
    exact Real.log_le_log (zero_lt_one.trans hS) hSn.le
  have hBn : 0 ≤ B (p-1 : ℕ) := hBS.trans hB
  have hsqrt : Real.sqrt (B S*B (p-1 : ℕ)) ≤ B (p-1 : ℕ) := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨hBn, by nlinarith⟩
  have hc := hp.2.2 S (p-1 : ℕ) le_rfl hSn le_rfl
  have hh := (abs_lt.mp hc).2
  have he := congrArg (fun n : ℕ => (n : ℝ)) (omegaIn_partition (p-1) S)
  push_cast at he
  linarith [hp.2.1]

lemma self_le_largest_pow_length {n : ℕ} (hn : n ≠ 0) :
    n ≤ (largestPrimeFactor n)^n.primeFactorsList.length := by
  calc
    n = n.primeFactorsList.prod := (Nat.prod_primeFactorsList hn).symm
    _ ≤ _ := List.prod_le_pow_card _ _ (fun p hp => primeFactor_le_largest hp)

lemma one_lt_largestPrimeFactor {n : ℕ} (hn : 2 ≤ n) : 1 < largestPrimeFactor n := by
  have h1 : 1 ≤ largestPrimeFactor n := le_max_left _ _
  have hpow := self_le_largest_pow_length (show n ≠ 0 by omega)
  by_contra hh
  have he : largestPrimeFactor n = 1 := by omega
  rw [he, one_pow] at hpow
  omega

/-- A bound for `Ω(n)` puts the largest prime factor within a logarithmic
distance of the double logarithm of `n`. -/
lemma largest_factor_doubleLog_lower {n : ℕ} {K : ℝ} (hn : 2 ≤ n) (hK : 0 < K)
    (hΩ : (n.primeFactorsList.length : ℝ) ≤ K) :
    B n - Real.log K ≤ B (largestPrimeFactor n) := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hA : (1 : ℝ) < largestPrimeFactor n := by
    exact_mod_cast one_lt_largestPrimeFactor hn
  have hp : (n : ℝ) ≤ (largestPrimeFactor n : ℝ)^n.primeFactorsList.length := by
    exact_mod_cast self_le_largest_pow_length (show n ≠ 0 by omega)
  have hl := Real.log_le_log (zero_lt_one.trans hnR) hp
  rw [Real.log_pow] at hl
  have hlu : Real.log (n : ℝ) ≤ K*Real.log (largestPrimeFactor n : ℝ) :=
    hl.trans (mul_le_mul_of_nonneg_right hΩ (Real.log_pos hA).le)
  have hdiv : Real.log (n : ℝ)/K ≤ Real.log (largestPrimeFactor n : ℝ) :=
    (div_le_iff₀ hK).mpr (by simpa [mul_comm] using hlu)
  have hh := Real.log_le_log (div_pos (Real.log_pos hnR) hK) hdiv
  simpa only [B, Real.log_div (Real.log_pos hnR).ne' hK.ne'] using hh

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalPrimeBands
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
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

lemma normality_total_uniform {S b : ℝ} {p : ℕ} (hp : IsNormalPrime S p)
    (hS : 1 < S) (hBS : 0 ≤ B S) (hSb : B S ≤ b) (hpb : B (p-1 : ℕ) ≤ b) :
    ((p-1).primeFactorsList.length : ℝ) ≤ 3*b := by
  by_cases hSn : S < (p-1 : ℕ)
  · exact (normality_total_bound hp hS hSn hBS).trans (by linarith)
  · have hpn : 1 ≤ p-1 := by have := hp.1.two_le; omega
    have hs : (largestPrimeFactor (p-1) : ℝ) ≤ S := by
      have hl : (largestPrimeFactor (p-1) : ℝ) ≤ (p-1 : ℕ) := by
        exact_mod_cast largestPrimeFactor_le_self hpn
      exact hl.trans (le_of_not_gt hSn)
    have hz := omegaIn_eq_zero_of_largest_le (T := (p-1 : ℕ)) hs
    have he := congrArg (fun n : ℕ => (n : ℝ)) (omegaIn_partition (p-1) S)
    rw [hz,Nat.add_zero] at he
    linarith [hp.2.1]

lemma shifted_doubleLog_lower {p : ℕ} (hp : 3 ≤ p) :
    B p-1 ≤ B (p-1 : ℕ) := by
  have hn : 2 ≤ p-1 := by omega
  have hnR : (1 : ℝ) < (p-1 : ℕ) := by exact_mod_cast hn
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hpn : (p : ℝ) ≤ ((p-1 : ℕ) : ℝ)^2 := by
    have he : p-1+1=p := by omega
    have hs : p ≤ (p-1)^2 := by nlinarith
    exact_mod_cast hs
  have hl := Real.log_le_log hpR hpn
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hh := Real.log_le_log (Real.log_pos (show (1 : ℝ) < p by exact_mod_cast (show 1 < p by omega))) hl
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.log_pos hnR).ne'] at hh
  change Real.log (Real.log (p : ℝ))-1 ≤ Real.log (Real.log ((p-1 : ℕ) : ℝ))
  linarith [Real.log_two_lt_d9]

lemma normal_prime_largest_band {S b lo hi : ℝ} {p : ℕ}
    (hp : IsNormalPrime S p) (hp3 : 3 ≤ p) (hS : 1 < S)
    (hBS : 0 ≤ B S) (hSb : B S ≤ b) (hb : 0 < b)
    (hpb : B (p-1 : ℕ) ≤ b) (hlo : lo ≤ B p) (hhi : B p ≤ hi) :
    lo-1-Real.log (3*b) ≤ B (largestPrimeFactor (p-1)) ∧
      B (largestPrimeFactor (p-1)) ≤ hi := by
  have hn : 2 ≤ p-1 := by omega
  constructor
  · have hlow := largest_factor_doubleLog_lower hn (by positivity : 0 < 3*b)
      (normality_total_uniform hp hS hBS hSb hpb)
    linarith [shifted_doubleLog_lower hp3]
  · apply le_trans _ hhi
    have hl : (1 : ℝ) < largestPrimeFactor (p-1) := by
      exact_mod_cast one_lt_largestPrimeFactor hn
    apply Real.log_le_log (Real.log_pos hl)
    apply Real.log_le_log (zero_lt_one.trans hl)
    exact_mod_cast (largestPrimeFactor_le_self (by omega : 1 ≤ p-1)).trans (Nat.sub_le _ _)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ComparisonSizes
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer size and large-prime-part bounds for Ford's comparison hypotheses. -/

noncomputable section

namespace TotientAsymptotic

lemma partBelow_mul_partAbove {n : ℕ} (hn : n ≠ 0) (Z : ℝ) :
    partBelow n Z*partAbove n Z=n := by
  have hh := List.prod_map_filter_mul_prod_map_filter_not
    (fun p : ℕ => (p : ℝ) ≤ Z) id n.primeFactorsList
  simpa only [partBelow,partAbove,List.map_id,not_le,Nat.prod_primeFactorsList hn] using hh

lemma partBelow_bound (n : ℕ) {Z : ℝ} (hZ : 1 ≤ Z) :
    (partBelow n Z : ℝ) ≤ Z^n.primeFactorsList.length := by
  let l := n.primeFactorsList.filter (fun p : ℕ => (p : ℝ) ≤ Z)
  have hb (l : List ℕ) (hl : ∀ p ∈ l, (p : ℝ) ≤ Z) :
      (l.map (fun p : ℕ => (p : ℝ))).prod ≤ Z^l.length := by
    induction l with
    | nil => simp
    | cons p l ih =>
      have hp := hl p (by simp)
      have ht := ih (fun q hq => hl q (by simp [hq]))
      have hn : 0 ≤ (l.map (fun p : ℕ => (p : ℝ))).prod :=
        List.prod_nonneg (by simp)
      simpa only [List.map_cons,List.prod_cons,List.length_cons,pow_succ,mul_comm] using
        mul_le_mul hp ht hn (zero_le_one.trans hZ)
  have hp : ((l.map (fun p : ℕ => (p : ℝ))).prod) ≤ Z^l.length := by
    apply hb
    intro p hp
    simpa only [decide_eq_true_eq] using (List.mem_filter.mp hp).2
  have hc : (partBelow n Z : ℝ)=(l.map (fun p : ℕ => (p : ℝ))).prod := by
    exact Nat.cast_list_prod l
  rw [hc]
  exact hp.trans (pow_le_pow_right₀ hZ (List.length_filter_le _ _))

lemma partAbove_log_lower {n : ℕ} {Z K : ℝ} (hn : 0 < n) (hZ : 1 ≤ Z)
    (hΩ : (n.primeFactorsList.length : ℝ) ≤ K) :
    Real.log (n : ℝ)-K*Real.log Z ≤ Real.log (partAbove n Z : ℝ) := by
  have he := partBelow_mul_partAbove hn.ne' Z
  have hb : 0 < partBelow n Z := Nat.pos_of_ne_zero (by intro hz; simp [hz] at he; omega)
  have ha : 0 < partAbove n Z := Nat.pos_of_ne_zero (by intro hz; simp [hz] at he; omega)
  have hl := Real.log_le_log (by exact_mod_cast hb : (0 : ℝ) < partBelow n Z)
    (partBelow_bound n hZ)
  rw [Real.log_pow] at hl
  have hk := mul_le_mul_of_nonneg_right hΩ (Real.log_nonneg hZ)
  have he' := congrArg (fun z : ℕ => Real.log (z : ℝ)) he
  rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hb.ne') (by exact_mod_cast ha.ne')] at he'
  linarith

lemma partAbove_gt_sqrt {n : ℕ} {Z K y : ℝ} (hn : 0 < n) (hZ : 1 ≤ Z)
    (hΩ : (n.primeFactorsList.length : ℝ) ≤ K) (hy : 0 < y)
    (hsize : Real.log y/2 < Real.log (n : ℝ)-K*Real.log Z) :
    Real.sqrt y < (partAbove n Z : ℝ) := by
  have he := partBelow_mul_partAbove hn.ne' Z
  have ha : 0 < partAbove n Z := Nat.pos_of_ne_zero (by intro hz; simp [hz] at he; omega)
  apply (Real.log_lt_log_iff (Real.sqrt_pos.mpr hy) (by exact_mod_cast ha)).mp
  rw [Real.log_sqrt hy.le]
  exact hsize.trans_le (partAbove_log_lower hn hZ hΩ)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionGrid
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite interval choices for the paired normalized largest factors. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma collision_grid_lower_bounds {δ u v : ℝ} (hδ : 0 < δ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    collisionGridLower δ (collisionGridIndex δ u v) ≤ min u v ∧
    min u v < collisionGridLower δ (collisionGridIndex δ u v)+δ := by
  have hmin : 0 ≤ min u v := le_min hu hv
  have hlo := Nat.floor_le (div_nonneg hmin hδ.le)
  have hhi := Nat.lt_floor_add_one (min u v/δ)
  constructor
  · simpa only [collisionGridLower,collisionGridIndex,mul_comm] using (le_div_iff₀ hδ).mp hlo
  · have hh := (div_lt_iff₀ hδ).mp hhi
    rw [add_mul,one_mul] at hh
    simpa only [collisionGridLower,collisionGridIndex,mul_comm] using hh

/-- The paired largest factors fit in one of finitely many grid intervals.
The width retains the full alignment error and one rounding cell. -/
theorem collision_grid_enclosure {δ u v : ℝ} {J : ℕ}
    (hδ : 0 < δ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hclose : |u-v| ≤ (2*(J : ℝ)+1)*δ) :
    let n := collisionGridIndex δ u v
    collisionGridLower δ n ≤ u ∧ collisionGridLower δ n ≤ v ∧
    u < collisionGridUpper δ J n ∧ v < collisionGridUpper δ J n ∧
    collisionGridUpper δ J n ≤ u+(2*(J : ℝ)+3)*δ := by
  dsimp only
  obtain ⟨hlo,hhi⟩ := collision_grid_lower_bounds hδ hu hv
  have hmax : max u v ≤ min u v+(2*(J : ℝ)+1)*δ := by
    rcases le_total u v with h | h
    · rw [min_eq_left h,max_eq_right h]
      linarith [(abs_le.mp hclose).1]
    · rw [min_eq_right h,max_eq_left h]
      linarith [(abs_le.mp hclose).2]
  have he : collisionGridUpper δ J (collisionGridIndex δ u v) =
      collisionGridLower δ (collisionGridIndex δ u v)+(2*(J : ℝ)+3)*δ := by
    simp only [collisionGridUpper,collisionGridLower,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    ring
  rw [he]
  exact ⟨hlo.trans (min_le_left _ _),hlo.trans (min_le_right _ _),
    by linarith [le_max_left u v],by linarith [le_max_right u v],
    by linarith [min_le_left u v]⟩

lemma collisionGridIndex_le {δ u v : ℝ} (hδ : 0 < δ) (hu : u ≤ 1) :
    collisionGridIndex δ u v ≤ ⌊1/δ⌋₊ := by
  exact Nat.floor_mono (div_le_div_of_nonneg_right ((min_le_left u v).trans hu) hδ.le)

/-- Disjoint largest-factor bands remain strictly ordered after gridding,
provided their gap exceeds the explicit alignment and rounding costs. -/
lemma collision_grid_separated {δ u v u' v' : ℝ} {J : ℕ}
    (hδ : 0 < δ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hu' : 0 ≤ u') (hv' : 0 ≤ v')
    (hclose' : |u'-v'| ≤ (2*(J : ℝ)+1)*δ)
    (hgap : max u' v'+(2*(J : ℝ)+4)*δ < min u v) :
    collisionGridUpper δ J (collisionGridIndex δ u' v') <
      collisionGridLower δ (collisionGridIndex δ u v) := by
  have hprev := (collision_grid_lower_bounds hδ hu hv).2
  have hnext := (collision_grid_enclosure hδ hu' hv' hclose').2.2.2.2
  linarith [le_max_left u' v']

lemma collisionGridFamilies_mem {δ : ℝ} {b : ℕ} (hδ : 0 < δ) (u v : Fin b → ℝ)
    (hu : ∀ j, u j ≤ 1) :
    (fun j => collisionGridIndex δ (u j) (v j)) ∈ collisionGridFamilies δ b := by
  apply Fintype.mem_piFinset.mpr
  intro j
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (collisionGridIndex_le hδ (hu j)))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalizedComparison
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ford's cutoff restrictions in the normalized coordinates of the finite grid. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma comparisonCutoffs_doubleLog {y : ℝ} (hB : B y ≠ 0) (ν : ℕ → ℝ) (j : ℕ) :
    B (comparisonCutoffs y ν j)/B y=ν j := by
  simp only [comparisonCutoffs,B,Real.log_exp]
  exact mul_div_cancel_left₀ _ hB

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PairedComparisonGrid
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual paired intervals, including the ungridded top and smooth bottom. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma paired_grid_width {b : ℕ} (δ ζ : ℝ) (n : Fin b → ℕ)
    {j : ℕ} (hj : j ∈ Finset.Icc 1 (b-1)) :
    pairedGridUpper δ ζ n j-pairedGridLower δ n j=(2*(j : ℝ)+3)*δ := by
  have hj0 : j ≠ 0 := by have := (Finset.mem_Icc.mp hj).1; omega
  have hjb : j<b := by have := (Finset.mem_Icc.mp hj).2; omega
  simp only [pairedGridUpper,pairedGridLower,hj0,ite_false, if_false,dite_eq_left hjb,
    collisionGridUpper,collisionGridLower,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  ring

lemma paired_grid_approximation {b : ℕ} {δ ζ : ℝ} (hδ : 0 < δ)
    (u v : Fin b → ℝ) (hu : ∀ j, 0 ≤ u j) (hv : ∀ j, 0 ≤ v j)
    (halign : ∀ j, |u j-v j| ≤ (2*(j.val : ℝ)+1)*δ)
    {j : ℕ} (hj : j ∈ Finset.Icc 1 (b-1)) :
    pairedGridUpper δ ζ (fun j => collisionGridIndex δ (u j) (v j)) j ≤
      u ⟨j,by have := Finset.mem_Icc.mp hj; omega⟩+(2*(b : ℝ)+3)*δ := by
  have hj0 : j ≠ 0 := by have := (Finset.mem_Icc.mp hj).1; omega
  have hjb : j<b := by have := (Finset.mem_Icc.mp hj).2; omega
  have he := (collision_grid_enclosure hδ (hu ⟨j,hjb⟩) (hv ⟨j,hjb⟩)
    (halign ⟨j,hjb⟩)).2.2.2.2
  simp only [pairedGridUpper,hj0,ite_false, if_false,dite_eq_left hjb]
  apply he.trans
  have hle : (j : ℝ) ≤ b := by exact_mod_cast hjb.le
  have ha := mul_le_mul_of_nonneg_right
    (show 2*(j : ℝ)+3≤2*(b : ℝ)+3 by linarith) hδ.le
  exact add_le_add le_rfl ha

lemma paired_grid_gaps {b : ℕ} {δ ζ : ℝ} (hb : 1 ≤ b) (hδ : 0 < δ)
    (u v : Fin b → ℝ) (hu : ∀ j, 0 ≤ u j) (hv : ∀ j, 0 ≤ v j)
    (halign : ∀ j, |u j-v j| ≤ (2*(j.val : ℝ)+1)*δ)
    (hnext : ∀ j : Fin b, ∀ hj : j.val+1<b,
      max (u ⟨j.val+1,hj⟩) (v ⟨j.val+1,hj⟩)+(2*(j.val+1 : ℕ)+6 : ℝ)*δ <
        min (u j) (v j))
    (hbottom : ζ+3*δ < min (u ⟨b-1,by omega⟩) (v ⟨b-1,by omega⟩)) :
    ∀ j ∈ Finset.Icc 2 b,
      2*δ < pairedGridUpper δ ζ (fun j => collisionGridIndex δ (u j) (v j)) (j-1)-
        pairedGridUpper δ ζ (fun j => collisionGridIndex δ (u j) (v j)) j := by
  intro j hj
  have hj2 := (Finset.mem_Icc.mp hj).1
  have hjb := (Finset.mem_Icc.mp hj).2
  have hp : j-1<b := by omega
  have hp0 : j-1 ≠ 0 := by omega
  have heprev := collision_grid_enclosure hδ (hu ⟨j-1,hp⟩) (hv ⟨j-1,hp⟩)
    (halign ⟨j-1,hp⟩)
  simp only [pairedGridUpper,hp0,ite_false, if_false,dite_eq_left hp]
  by_cases hjlt : j<b
  · have hj0 : j ≠ 0 := by omega
    simp only [hj0,ite_false, if_false,dite_eq_left hjlt]
    have he := (collision_grid_enclosure hδ (hu ⟨j,hjlt⟩) (hv ⟨j,hjlt⟩)
      (halign ⟨j,hjlt⟩)).2.2.2.2
    have hidx : j-1+1=j := by omega
    have hg := hnext ⟨j-1,hp⟩ (by change j-1+1<b; omega)
    simp only [hidx] at hg
    have hmin := min_le_left (u ⟨j-1,hp⟩) (v ⟨j-1,hp⟩)
    have hmax := le_max_left (u ⟨j,hjlt⟩) (v ⟨j,hjlt⟩)
    linarith [heprev.2.2.1]
  · have hjeq : j=b := by omega
    have hj0 : j ≠ 0 := by omega
    simp only [hj0,ite_false, if_false,dite_eq_right hjlt]
    have hg : ζ+3*δ < min (u ⟨j-1,hp⟩) (v ⟨j-1,hp⟩) := by
      simpa only [hjeq] using hbottom
    linarith [min_le_left (u ⟨j-1,hp⟩) (v ⟨j-1,hp⟩),heprev.2.2.1]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ActualComparisonCutoffs
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit finite cutoffs for the actual collision comparison. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma exp_exp_doubleLog {w : ℝ} (hw : 1< w) : Real.exp (Real.exp (B w))=w := by
  rw [B,Real.exp_log (Real.log_pos hw),Real.exp_log (zero_lt_one.trans hw)]


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

lemma partBetween_dvd {n : ℕ} (hn : n ≠ 0) (U V : ℝ) : partBetween n U V ∣ n := by
  have hh := (List.filter_sublist (p:=fun p : ℕ => decide (U < (p:ℝ) ∧ (p:ℝ) ≤ V))
    (l:=n.primeFactorsList)).prod_dvd_prod
  obtain ⟨c,hc⟩ := hh
  exact ⟨c,by simpa only [partBetween,Nat.prod_primeFactorsList hn] using hc⟩

lemma partBetween_squarefree {n : ℕ} (hn : n ≠ 0) {U V : ℝ}
    (hsq : SquarefreeAbove n U) : Squarefree (partBetween n U V) := by
  apply Nat.squarefree_iff_prime_squarefree.mpr
  intro p hp hd
  have hpband : p ∈ (partBetween n U V).primeFactorsList :=
    (Nat.mem_primeFactorsList_iff_dvd (partBetween_pos n U V).ne' hp).mpr
      ((dvd_mul_right p p).trans hd)
  have hpf := (partBetween_factors n U V).mem_iff.mpr hpband
  have hbound : U < (p:ℝ) ∧ (p:ℝ) ≤ V := of_decide_eq_true (List.mem_filter.mp hpf).2
  have hpU := hbound.1
  apply hsq p hp hpU
  simpa only [pow_two] using hd.trans (partBetween_dvd hn U V)

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ResidualFactorCount
attribute [-instance] _root_.instMeasurableSpace
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

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalTerminalFactors
attribute [-instance] _root_.instMeasurableSpace
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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTCancelCoordinates
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Cancel matching coordinates after the high-prime lists have been aligned.
The first mismatch is retained, so the large-head condition is preserved.
The canceled integer prime product is retained for the later reciprocal
totient summation.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma ppt_coordinate_embedding_mem {k : ℕ} (p q : Fin k → ℕ)
    (i : Fin (pptUnequalCoordinates p q).card) :
    pptCoordinateEmbedding p q i ∈ pptUnequalCoordinates p q :=
  (pptUnequalCoordinates p q).orderEmbOfFin_mem rfl i

lemma ppt_product_coordinate_embedding {k : ℕ} (p q : Fin k → ℕ)
    (f : Fin k → ℕ) :
    (∏ i : Fin (pptUnequalCoordinates p q).card,
      f (pptCoordinateEmbedding p q i)) =
      ∏ i ∈ pptUnequalCoordinates p q, f i := by
  calc
    _ = ∏ j ∈ Finset.univ.image (pptCoordinateEmbedding p q), f j := by
      rw [Finset.prod_image]
      intro i _ j _ he
      exact (pptCoordinateEmbedding p q).injective he
    _ = _ := by
      rw [show Finset.univ.image (pptCoordinateEmbedding p q) =
          pptUnequalCoordinates p q from
        (pptUnequalCoordinates p q).image_orderEmbOfFin_univ rfl]

lemma ppt_shifted_product_coordinate_embedding {k : ℕ} (p q f : Fin k → ℕ) :
    shiftedProduct (f ∘ pptCoordinateEmbedding p q) =
      ∏ i ∈ pptUnequalCoordinates p q, (f i-1) := by
  exact ppt_product_coordinate_embedding p q (fun i => f i-1)

lemma ppt_canceled_prime_product_totient {k : ℕ} (p q : Fin k → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    (pptCanceledPrimeProduct p q).totient =
      ∏ i ∈ pptEqualCoordinates p q, (p i-1) := by
  have hprime : ∀ r ∈ (pptEqualCoordinates p q).image p, r.Prime := by
    intro r hr
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
    exact hp i
  have hh := TotientFibers.totient_prime_prod hprime
  rw [Finset.prod_image (fun i _ j _ he => hinj he),
    Finset.prod_image (fun i _ j _ he => hinj he)] at hh
  exact hh

lemma ppt_canceled_prime_product_split {k : ℕ} (p q : Fin k → ℕ) :
    pptCanceledPrimeProduct p q *
      (∏ i, p (pptCoordinateEmbedding p q i)) = ∏ i, p i := by
  rw [ppt_product_coordinate_embedding]
  exact Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun i => p i = q i) p

lemma ppt_canceled_prime_product_pos {k : ℕ} (p q : Fin k → ℕ)
    (hp : ∀ i, (p i).Prime) : 0 < pptCanceledPrimeProduct p q :=
  Finset.prod_pos (fun i _ => (hp i).pos)

lemma ppt_canceled_totient_split {k : ℕ} (p q : Fin k → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    (pptCanceledPrimeProduct p q).totient *
      shiftedProduct (p ∘ pptCoordinateEmbedding p q) = shiftedProduct p := by
  rw [ppt_canceled_prime_product_totient p q hp hinj]
  rw [ppt_shifted_product_coordinate_embedding]
  unfold shiftedProduct
  exact Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun i => p i = q i) (fun i => p i-1)

/-- The same canceled factor which enters the reciprocal mass also
supplies the divisor in the published comparison size bound. -/
lemma ppt_canceled_comparison_size {k D : ℕ} (p q : Fin k → ℕ) {z : ℝ}
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (hsize : ((D*shiftedProduct p : ℕ) : ℝ) ≤ z) :
    ((D*shiftedProduct (p ∘ pptCoordinateEmbedding p q) : ℕ) : ℝ) ≤
      z/(pptCanceledPrimeProduct p q).totient := by
  have hc := Nat.totient_pos.mpr (ppt_canceled_prime_product_pos p q hp)
  apply (le_div_iff₀ (by exact_mod_cast hc)).mpr
  have he : (D*shiftedProduct (p ∘ pptCoordinateEmbedding p q))*
      (pptCanceledPrimeProduct p q).totient = D*shiftedProduct p := by
    calc
      _ = D*((pptCanceledPrimeProduct p q).totient *
        shiftedProduct (p ∘ pptCoordinateEmbedding p q)) := by ring
      _ = _ := by rw [ppt_canceled_totient_split p q hp hinj]
  exact (by exact_mod_cast he :
    ((D*shiftedProduct (p ∘ pptCoordinateEmbedding p q) : ℕ) : ℝ)*
      (pptCanceledPrimeProduct p q).totient = (D*shiftedProduct p : ℕ)).le.trans hsize

lemma ppt_cancel_matching_coordinates {k D E : ℕ} (p q : Fin k → ℕ)
    (hp : ∀ i, (p i).Prime)
    (heq : D*shiftedProduct p = E*shiftedProduct q) :
    D*shiftedProduct (p ∘ pptCoordinateEmbedding p q) =
      E*shiftedProduct (q ∘ pptCoordinateEmbedding p q) := by
  let c := ∏ i ∈ pptEqualCoordinates p q, (p i-1)
  have hc : 0 < c := Finset.prod_pos
    (fun i _ => Nat.sub_pos_of_lt (hp i).one_lt)
  have hcommon : (∏ i ∈ pptEqualCoordinates p q, (q i-1)) = c := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  have hleft : c*shiftedProduct (p ∘ pptCoordinateEmbedding p q) = shiftedProduct p := by
    rw [ppt_shifted_product_coordinate_embedding]
    unfold shiftedProduct
    exact Finset.prod_filter_mul_prod_filter_not Finset.univ
      (fun i => p i = q i) (fun i => p i-1)
  have hright : c*shiftedProduct (q ∘ pptCoordinateEmbedding p q) = shiftedProduct q := by
    rw [← hcommon]
    rw [ppt_shifted_product_coordinate_embedding]
    unfold shiftedProduct
    exact Finset.prod_filter_mul_prod_filter_not Finset.univ
      (fun i => p i = q i) (fun i => q i-1)
  apply Nat.eq_of_mul_eq_mul_left hc
  calc
    _ = D*(c*shiftedProduct (p ∘ pptCoordinateEmbedding p q)) := by ring
    _ = D*shiftedProduct p := by rw [hleft]
    _ = E*shiftedProduct q := heq
    _ = E*(c*shiftedProduct (q ∘ pptCoordinateEmbedding p q)) := by rw [hright]
    _ = _ := by ring

lemma ppt_coordinate_first_survives {k : ℕ} (hk : 0 < k) (p q : Fin k → ℕ)
    (hfirst : p ⟨0, hk⟩ ≠ q ⟨0, hk⟩) :
    ∃ hb : 0 < (pptUnequalCoordinates p q).card,
      pptCoordinateEmbedding p q ⟨0, hb⟩ = ⟨0, hk⟩ := by
  have hzero : (⟨0, hk⟩ : Fin k) ∈ pptUnequalCoordinates p q :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfirst⟩
  have hb := Finset.card_pos.mpr ⟨_, hzero⟩
  refine ⟨hb, ?_⟩
  rw [pptCoordinateEmbedding, Finset.orderEmbOfFin_zero rfl hb]
  apply le_antisymm
  · exact Finset.min'_le _ _ hzero
  · exact Nat.zero_le _

lemma ppt_surviving_coordinates_unequal {k : ℕ} (p q : Fin k → ℕ)
    (i : Fin (pptUnequalCoordinates p q).card) :
    p (pptCoordinateEmbedding p q i) ≠ q (pptCoordinateEmbedding p q i) :=
  (Finset.mem_filter.mp (ppt_coordinate_embedding_mem p q i)).2

lemma ppt_surviving_coordinates_strictAnti {k : ℕ} (p q : Fin k → ℕ)
    (hp : StrictAnti p) (hq : StrictAnti q) :
    StrictAnti (p ∘ pptCoordinateEmbedding p q) ∧
      StrictAnti (q ∘ pptCoordinateEmbedding p q) := by
  exact ⟨hp.comp_strictMono (pptCoordinateEmbedding p q).strictMono,
    hq.comp_strictMono (pptCoordinateEmbedding p q).strictMono⟩

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTLargePart
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The leading shift in the PPT construction satisfies the large-prime-part
condition of Ford's comparison lemma directly from normality.  The sharp
bound `Ω(p-1) ≤ 3 B(z)` leaves a strict margin at the published cutoff
`Y₁ ≤ z^(1/(10 B(z)))`.
-/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

private lemma ppt_prime_shift_log_strict : ∀ᶠ z : ℝ in atTop,
    ∀ p : ℕ, p.Prime → z^(9/10 : ℝ) ≤ p →
      (4/5 : ℝ)*Real.log z < Real.log (p-1 : ℕ) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (10*Real.log 2))]
    with z hz hlog
  intro p hp hlo
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp' : (p : ℝ)-1 = (p-1 : ℕ) := by
    rw [Nat.cast_sub hp.one_lt.le]
    norm_num
  have hhalf : z^(9/10 : ℝ)/2 ≤ (p-1 : ℕ) := by
    rw [← hp']
    linarith
  have hh := Real.log_le_log
    (div_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hz) _) (by norm_num)) hhalf
  rw [Real.log_div (Real.rpow_pos_of_pos (zero_lt_one.trans hz) _).ne'
      (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_rpow (zero_lt_one.trans hz)] at hh
  linarith

lemma ppt_cutoff_log_cost {z Y : ℝ} (hz : 1 < z) (hB : 0 < B z)
    (hY : 1 ≤ Y) (hYu : Y ≤ z^(1/(10*B z))) :
    (3*B z)*Real.log Y ≤ (3/10 : ℝ)*Real.log z := by
  have hl := Real.log_le_log (zero_lt_one.trans_le hY) hYu
  rw [Real.log_rpow (zero_lt_one.trans hz)] at hl
  have hh := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 3*B z)
  have he : (3*B z)*(1/(10*B z)) = (3/10 : ℝ) := by
    field_simp
  rwa [← mul_assoc, he] at hh

/-- The literal cutoff from Ford's comparison parameters suffices for the
large-prime-part requirement on a leading candidate prime. -/
theorem ppt_comparison_large_part : ∀ᶠ z : ℝ in atTop,
    ∀ p : ℕ, ∀ Y : ℝ, p.Prime → z^(9/10 : ℝ) ≤ p →
      1 ≤ Y → Y ≤ z^(1/(10*B z)) →
      ((p-1).primeFactorsList.length : ℝ) ≤ 3*B z →
      Real.sqrt z < (partAbove (p-1) Y : ℝ) := by
  filter_upwards [ppt_prime_shift_log_strict, eventually_gt_atTop (1 : ℝ),
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))]
    with z hshift hz hB
  intro p Y hp hlo hY hYu hΩ
  apply partAbove_gt_sqrt (Nat.sub_pos_of_lt hp.one_lt) hY hΩ (zero_lt_one.trans hz)
  have hcost := ppt_cutoff_log_cost hz hB hY hYu
  have hlog := hshift p hp hlo
  linarith

/-- Normality supplies the sharp total-factor bound uniformly below `z`.
No separate smooth-divisor exclusion is needed for this conclusion. -/
theorem ppt_normal_comparison_large_part : ∀ᶠ z : ℝ in atTop,
    ∀ (p : ℕ) (S Y : ℝ), 1 < S → 0 ≤ B S → S ≤ z →
      IsNormalPrime S p → z^(9/10 : ℝ) ≤ p → (p-1 : ℕ) ≤ z →
      1 ≤ Y → Y ≤ z^(1/(10*B z)) →
      Real.sqrt z < (partAbove (p-1) Y : ℝ) := by
  filter_upwards [ppt_comparison_large_part,
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))]
    with z hlarge hBz
  intro p S Y hS hBS hSz hp hlo hpz hY hYu
  have hBSz : B S ≤ B z := Real.log_le_log (Real.log_pos hS)
    (Real.log_le_log (zero_lt_one.trans hS) hSz)
  have hpred : B (p-1 : ℕ) ≤ B z := by
    by_cases hp3 : 3 ≤ p
    · have hp1 : (1 : ℝ) < (p-1 : ℕ) := by
        exact_mod_cast (show 1 < p-1 by omega)
      exact Real.log_le_log (Real.log_pos hp1)
        (Real.log_le_log (zero_lt_one.trans hp1) hpz)
    · have hp2 : p = 2 := by have := hp.1.two_le; omega
      simpa only [hp2, Nat.reduceSub, Nat.cast_one, B, Real.log_one,
        Real.log_zero] using hBz.le
  exact hlarge p Y hp.1 hlo hY hYu
    (normality_total_uniform hp hS hBS hBSz hpred)

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTUnequalAlignment
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The unequal-length factor-count argument needed before matching the two
lists in the PPT construction.  A prefix of `j+1` left shifts reaching an
interval cannot be balanced by only `j` right shifts unless that interval
has small double-logarithmic length.  Consequently the required right
index exists before any equal-length `ShiftedPair` is formed.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

/-- The right list may have arbitrary length, and its first `j` shifts
need not reach the top of the interval.  Normality's upper bound handles
these truncated intervals. -/
theorem ppt_unequal_normality_gap {k l D E : ℕ}
    (p : Fin k → ℕ) (q : Fin l → ℕ) (j : Fin k)
    {S U T ε : ℝ} (hS : 1 < S) (hBS : 0 ≤ B S)
    (hD : D ≠ 0) (hE : E ≠ 0)
    (hp : ∀ i, IsNormalPrime S (p i)) (hq : ∀ i, IsNormalPrime S (q i))
    (heq : D*shiftedProduct p = E*shiftedProduct q)
    (hDU : (largestPrimeFactor D : ℝ) ≤ U)
    (hEU : (largestPrimeFactor E : ℝ) ≤ U)
    (hSU : S ≤ U) (hUT : U < T)
    (hε : Real.sqrt (B S*B T) ≤ ε)
    (hpT : ∀ i ≤ j, T ≤ (p i-1 : ℕ))
    (hqsmall : ∀ i : Fin l, j.val ≤ i.val → (largestPrimeFactor (q i-1) : ℝ) ≤ U) :
    B T-B U ≤ (2*(j.val : ℝ)+1)*ε := by
  classical
  have hp0 (i : Fin k) : p i-1 ≠ 0 := by have := (hp i).1.two_le; omega
  have hq0 (i : Fin l) : q i-1 ≠ 0 := by have := (hq i).1.two_le; omega
  have hcount : (∑ i : Fin k, omegaIn (p i-1) U T) =
      ∑ i : Fin l, omegaIn (q i-1) U T := by
    have hh := congrArg (fun n => omegaIn n U T) heq
    unfold shiftedProduct at hh
    rw [omegaIn_mul hD (Finset.prod_ne_zero_iff.mpr (fun i _ => hp0 i)),
      omegaIn_mul hE (Finset.prod_ne_zero_iff.mpr (fun i _ => hq0 i)),
      omegaIn_eq_zero_of_largest_le hDU, omegaIn_eq_zero_of_largest_le hEU,
      zero_add, zero_add] at hh
    simpa only [omegaIn_prod _ _ (fun i _ => hp0 i),
      omegaIn_prod _ _ (fun i _ => hq0 i)] using hh
  have hcountR : (∑ i : Fin k, (omegaIn (p i-1) U T : ℝ)) =
      ∑ i : Fin l, (omegaIn (q i-1) U T : ℝ) := by exact_mod_cast hcount
  have hlo : ((j.val : ℝ)+1)*(B T-B U-ε) ≤
      ∑ i : Fin k, (omegaIn (p i-1) U T : ℝ) := by
    calc
      _ = ∑ _i ∈ Finset.Iic j, (B T-B U-ε) := by simp [Fin.card_Iic] <;> ring
      _ ≤ ∑ i ∈ Finset.Iic j, (omegaIn (p i-1) U T : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact (normality_interval_bounds (hp i) hSU hUT (hpT i (Finset.mem_Iic.mp hi)) hε).1
      _ ≤ ∑ i : Fin k, (omegaIn (p i-1) U T : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun i _ _ => Nat.cast_nonneg _)
  let I : Finset (Fin l) := Finset.univ.filter (fun i => i.val < j.val)
  have hIcard : I.card ≤ j.val := by
    dsimp only [I]
    rw [Fin.card_filter_val_lt]
    exact min_le_right _ _
  have hε0 : 0 ≤ ε := (Real.sqrt_nonneg _).trans hε
  have hBU : B U ≤ B T := Real.log_le_log (Real.log_pos (hS.trans_le hSU))
    (Real.log_le_log (zero_lt_one.trans (hS.trans_le hSU)) hUT.le)
  have hupper0 : 0 ≤ B T-B U+ε := by linarith
  have hhi : (∑ i : Fin l, (omegaIn (q i-1) U T : ℝ)) ≤
      (j.val : ℝ)*(B T-B U+ε) := by
    calc
      _ = ∑ i ∈ I, (omegaIn (q i-1) U T : ℝ) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i _ hi
        have hji : j.val ≤ i.val := by
          by_contra hh
          exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩)
        rw [omegaIn_eq_zero_of_largest_le (hqsmall i hji), Nat.cast_zero]
      _ ≤ ∑ _i ∈ I, (B T-B U+ε) := by
        apply Finset.sum_le_sum
        intro i _
        have hh := normality_band_upper (hq i) hS hBS hSU hUT
        linarith
      _ = (I.card : ℝ)*(B T-B U+ε) := by simp <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hIcard) hupper0
  rw [hcountR] at hlo
  nlinarith

/-- A wide enough interval forces a right prime at rank at least `j`.
This proves the existence of that index; it does not assume the two lists
have the same length. -/
theorem ppt_right_index_exists {k l D E : ℕ}
    (p : Fin k → ℕ) (q : Fin l → ℕ) (j : Fin k)
    {S U T ε : ℝ} (hS : 1 < S) (hBS : 0 ≤ B S)
    (hD : D ≠ 0) (hE : E ≠ 0)
    (hp : ∀ i, IsNormalPrime S (p i)) (hq : ∀ i, IsNormalPrime S (q i))
    (heq : D*shiftedProduct p = E*shiftedProduct q)
    (hDU : (largestPrimeFactor D : ℝ) ≤ U)
    (hEU : (largestPrimeFactor E : ℝ) ≤ U)
    (hSU : S ≤ U) (hUT : U < T)
    (hε : Real.sqrt (B S*B T) ≤ ε)
    (hpT : ∀ i ≤ j, T ≤ (p i-1 : ℕ))
    (hgap : (2*(j.val : ℝ)+1)*ε < B T-B U) :
    j.val < l ∧ ∃ i : Fin l, j.val ≤ i.val ∧ U < (largestPrimeFactor (q i-1) : ℝ) := by
  have hex : ∃ i : Fin l, j.val ≤ i.val ∧ U < (largestPrimeFactor (q i-1) : ℝ) := by
    by_contra hn
    have hsmall (i : Fin l) (hji : j.val ≤ i.val) :
        (largestPrimeFactor (q i-1) : ℝ) ≤ U := by
      exact le_of_not_gt (fun h => hn ⟨i, hji, h⟩)
    exact (not_lt_of_ge (ppt_unequal_normality_gap p q j hS hBS hD hE hp hq heq
      hDU hEU hSU hUT hε hpT hsmall)) hgap
  obtain ⟨i, hji, hi⟩ := hex
  exact ⟨hji.trans_lt i.isLt, i, hji, hi⟩

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTCoordinateAlignment
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Apply the unequal-list count to the actual ordering by prime size.  This
proves existence of a right prime at the required index, and then compares
the largest factors of the two prime predecessors.  The additive `log K`
is the explicit cost of passing from a predecessor to its largest factor
when its total number of prime factors is at most `K`.
-/

noncomputable section

namespace TotientAsymptotic

private theorem ppt_ordered_alignment_side {k l D E : ℕ}
    (p : Fin k → ℕ) (q : Fin l → ℕ) (j : Fin k) (j' : Fin l)
    (hindex : j.val = j'.val) {S ε K : ℝ}
    (hS : 1 < S) (hBS : 0 ≤ B S) (hK : 0 < K)
    (hD : D ≠ 0) (hE : E ≠ 0)
    (hp : ∀ i, IsNormalPrime S (p i)) (hq : ∀ i, IsNormalPrime S (q i))
    (hpa : Antitone p) (hqa : Antitone q)
    (heq : D*shiftedProduct p = E*shiftedProduct q)
    (hp3 : 3 ≤ p j) (hq3 : 3 ≤ q j')
    (hDS : (largestPrimeFactor D : ℝ) ≤ (q j'-1 : ℕ))
    (hES : (largestPrimeFactor E : ℝ) ≤ (q j'-1 : ℕ))
    (hSsmall : S ≤ (q j'-1 : ℕ))
    (hΩ : ((q j'-1).primeFactorsList.length : ℝ) ≤ K)
    (hε : Real.sqrt (B S*B (largestPrimeFactor (p j-1))) ≤ ε) :
    B (largestPrimeFactor (p j-1))-B (largestPrimeFactor (q j'-1)) ≤
      (2*(j.val : ℝ)+1)*ε+Real.log K := by
  let U : ℝ := (q j'-1 : ℕ)
  let T : ℝ := largestPrimeFactor (p j-1)
  have hε0 : 0 ≤ ε := (Real.sqrt_nonneg _).trans hε
  have hcoef : 0 ≤ (2*(j.val : ℝ)+1)*ε := by positivity
  have hT : 1 < T := by
    dsimp only [T]
    exact_mod_cast one_lt_largestPrimeFactor (show 2 ≤ p j-1 by omega)
  have hpT (i : Fin k) (hij : i ≤ j) : T ≤ (p i-1 : ℕ) := by
    have hsmall : largestPrimeFactor (p j-1) ≤ p j-1 :=
      largestPrimeFactor_le_self (by omega)
    exact Nat.cast_le.mpr (hsmall.trans (Nat.sub_le_sub_right (hpa hij) 1))
  have hqsmall (i : Fin l) (hji : j.val ≤ i.val) :
      (largestPrimeFactor (q i-1) : ℝ) ≤ U := by
    have hqone : 1 ≤ q i-1 := by have := (hq i).1.two_le; omega
    have hqij : q i ≤ q j' := hqa (show j' ≤ i from by change j'.val ≤ i.val; omega)
    exact Nat.cast_le.mpr ((largestPrimeFactor_le_self hqone).trans
      (Nat.sub_le_sub_right hqij 1))
  have hgap : B T-B U ≤ (2*(j.val : ℝ)+1)*ε := by
    by_cases hUT : U < T
    · exact ppt_unequal_normality_gap p q j hS hBS hD hE hp hq heq
        hDS hES hSsmall hUT hε hpT hqsmall
    · have hmono : B T ≤ B U := Real.log_le_log (Real.log_pos hT)
        (Real.log_le_log (zero_lt_one.trans hT) (le_of_not_gt hUT))
      linarith
  have hlower := largest_factor_doubleLog_lower (show 2 ≤ q j'-1 by omega) hK hΩ
  change B T-B (largestPrimeFactor (q j'-1)) ≤ _
  change B U-Real.log K ≤ B (largestPrimeFactor (q j'-1)) at hlower
  linarith

/-- Ordered prime lists need not have equal total lengths.  Once index `j`
exists on both sides, normality aligns their largest predecessor factors
with an explicit additive error. -/
theorem ppt_ordered_coordinate_alignment {k l D E j : ℕ}
    (p : Fin k → ℕ) (q : Fin l → ℕ) (hjk : j < k) (hjl : j < l)
    {S ε K : ℝ} (hS : 1 < S) (hBS : 0 ≤ B S) (hK : 0 < K)
    (hD : D ≠ 0) (hE : E ≠ 0)
    (hp : ∀ i, IsNormalPrime S (p i)) (hq : ∀ i, IsNormalPrime S (q i))
    (hpa : Antitone p) (hqa : Antitone q)
    (heq : D*shiftedProduct p = E*shiftedProduct q)
    (hp3 : 3 ≤ p ⟨j,hjk⟩) (hq3 : 3 ≤ q ⟨j,hjl⟩)
    (hDS : (largestPrimeFactor D : ℝ) ≤
      min ((p ⟨j,hjk⟩-1 : ℕ) : ℝ) ((q ⟨j,hjl⟩-1 : ℕ) : ℝ))
    (hES : (largestPrimeFactor E : ℝ) ≤
      min ((p ⟨j,hjk⟩-1 : ℕ) : ℝ) ((q ⟨j,hjl⟩-1 : ℕ) : ℝ))
    (hSsmall : S ≤ min ((p ⟨j,hjk⟩-1 : ℕ) : ℝ) ((q ⟨j,hjl⟩-1 : ℕ) : ℝ))
    (hΩp : ((p ⟨j,hjk⟩-1).primeFactorsList.length : ℝ) ≤ K)
    (hΩq : ((q ⟨j,hjl⟩-1).primeFactorsList.length : ℝ) ≤ K)
    (hεp : Real.sqrt (B S*B (largestPrimeFactor (p ⟨j,hjk⟩-1))) ≤ ε)
    (hεq : Real.sqrt (B S*B (largestPrimeFactor (q ⟨j,hjl⟩-1))) ≤ ε) :
    |B (largestPrimeFactor (p ⟨j,hjk⟩-1))-B (largestPrimeFactor (q ⟨j,hjl⟩-1))| ≤
      (2*(j : ℝ)+1)*ε+Real.log K := by
  have hleft := ppt_ordered_alignment_side p q ⟨j,hjk⟩ ⟨j,hjl⟩ rfl hS hBS hK hD hE
    hp hq hpa hqa heq hp3 hq3 (hDS.trans (min_le_right _ _))
    (hES.trans (min_le_right _ _)) (hSsmall.trans (min_le_right _ _)) hΩq hεp
  have hright := ppt_ordered_alignment_side q p ⟨j,hjl⟩ ⟨j,hjk⟩ rfl hS hBS hK hE hD
    hq hp hqa hpa heq.symm hq3 hp3 (hES.trans (min_le_left _ _))
    (hDS.trans (min_le_left _ _)) (hSsmall.trans (min_le_left _ _)) hΩp hεq
  exact abs_le.mpr ⟨by linarith, hleft⟩

/-- Normality supplies the factor-count and square-root error bounds.  The
remaining logarithmic error is explicit after normalization by `B z`. -/
theorem ppt_normalized_coordinate_alignment {k l D E j : ℕ}
    (p : Fin k → ℕ) (q : Fin l → ℕ) (hjk : j < k) (hjl : j < l)
    {S z : ℝ} (hS : 1 < S) (hBS : 0 ≤ B S) (hBz : 0 < B z) (hSz : S ≤ z)
    (hD : D ≠ 0) (hE : E ≠ 0)
    (hp : ∀ i, IsNormalPrime S (p i)) (hq : ∀ i, IsNormalPrime S (q i))
    (hpa : Antitone p) (hqa : Antitone q)
    (heq : D*shiftedProduct p = E*shiftedProduct q)
    (hp3 : 3 ≤ p ⟨j,hjk⟩) (hq3 : 3 ≤ q ⟨j,hjl⟩)
    (hpz : (p ⟨j,hjk⟩-1 : ℕ) ≤ z) (hqz : (q ⟨j,hjl⟩-1 : ℕ) ≤ z)
    (hDS : (largestPrimeFactor D : ℝ) ≤
      min ((p ⟨j,hjk⟩-1 : ℕ) : ℝ) ((q ⟨j,hjl⟩-1 : ℕ) : ℝ))
    (hES : (largestPrimeFactor E : ℝ) ≤
      min ((p ⟨j,hjk⟩-1 : ℕ) : ℝ) ((q ⟨j,hjl⟩-1 : ℕ) : ℝ))
    (hSsmall : S ≤ min ((p ⟨j,hjk⟩-1 : ℕ) : ℝ) ((q ⟨j,hjl⟩-1 : ℕ) : ℝ)) :
    |B (largestPrimeFactor (p ⟨j,hjk⟩-1))/B z-
      B (largestPrimeFactor (q ⟨j,hjl⟩-1))/B z| ≤
      (2*(j : ℝ)+1)*Real.sqrt (B S/B z)+Real.log (3*B z)/B z := by
  have hBSz : B S ≤ B z := Real.log_le_log (Real.log_pos hS)
    (Real.log_le_log (zero_lt_one.trans hS) hSz)
  have hpred (r : ℕ) (hr : 3 ≤ r) (hrz : (r-1 : ℕ) ≤ z) : B (r-1 : ℕ) ≤ B z := by
    have hr1 : (1 : ℝ) < (r-1 : ℕ) := by exact_mod_cast (show 1 < r-1 by omega)
    exact Real.log_le_log (Real.log_pos hr1)
      (Real.log_le_log (zero_lt_one.trans hr1) hrz)
  have hlarge (r : ℕ) (hr : 3 ≤ r) (hrz : (r-1 : ℕ) ≤ z) :
      B (largestPrimeFactor (r-1)) ≤ B z := by
    have hl1 : (1 : ℝ) < largestPrimeFactor (r-1) := by
      exact_mod_cast one_lt_largestPrimeFactor (show 2 ≤ r-1 by omega)
    apply Real.log_le_log (Real.log_pos hl1)
    apply Real.log_le_log (zero_lt_one.trans hl1)
    exact (Nat.cast_le.mpr (largestPrimeFactor_le_self (by omega))).trans hrz
  have hΩp := normality_total_uniform (hp ⟨j,hjk⟩) hS hBS hBSz (hpred _ hp3 hpz)
  have hΩq := normality_total_uniform (hq ⟨j,hjl⟩) hS hBS hBSz (hpred _ hq3 hqz)
  have hεp := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hlarge _ hp3 hpz) hBS)
  have hεq := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hlarge _ hq3 hqz) hBS)
  have hraw := ppt_ordered_coordinate_alignment p q hjk hjl hS hBS
    (show 0 < 3*B z by positivity) hD hE hp hq hpa hqa heq hp3 hq3
    hDS hES hSsmall hΩp hΩq hεp hεq
  have hsqrt : Real.sqrt (B S*B z)/B z = Real.sqrt (B S/B z) := by
    calc
      _ = Real.sqrt (B S)*(Real.sqrt (B z)/B z) := by
        rw [Real.sqrt_mul hBS]
        ring
      _ = Real.sqrt (B S)*(Real.sqrt (B z))⁻¹ := by rw [Real.sqrt_div_self]
      _ = _ := by rw [Real.sqrt_div hBS, div_eq_mul_inv]
  calc
    _ = |B (largestPrimeFactor (p ⟨j,hjk⟩-1))-
        B (largestPrimeFactor (q ⟨j,hjl⟩-1))|/B z := by
      rw [← sub_div, abs_div, abs_of_pos hBz]
    _ ≤ ((2*(j : ℝ)+1)*Real.sqrt (B S*B z)+Real.log (3*B z))/B z :=
      div_le_div_of_nonneg_right hraw hBz.le
    _ = _ := by rw [add_div, mul_div_assoc, hsqrt]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTNormalizedParameters
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The PPT construction has a first normalized cutoff approaching one.  Its
inverse-log-cube loss still implies the literal first-cutoff power bound
in Ford's comparison lemma.  No fixed bound such as `ν₁ ≤ 4/5` is needed.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma ppt_comparison_cutoff_power_of_log_loss {z ν : ℝ} (hz : 1 < z)
    (hB : 0 < B z) (hloss : Real.log (10*B z) ≤ B z*(1-ν)) :
    Real.exp (Real.exp (B z*ν)) ≤ z^(1/(10*B z)) := by
  have hscale : 0 < 10*B z := by positivity
  have hinner : Real.exp (B z*ν) ≤ Real.log z/(10*B z) := by
    apply (le_div_iff₀ hscale).mpr
    calc
      _ = Real.exp (Real.log (10*B z)+B z*ν) := by
        rw [Real.exp_add, Real.exp_log hscale]
        ring
      _ ≤ Real.exp (B z) := Real.exp_le_exp.mpr (by nlinarith)
      _ = Real.log z := Real.exp_log (Real.log_pos hz)
  conv_rhs => rw [Real.rpow_def_of_pos (zero_lt_one.trans hz)]
  exact Real.exp_le_exp.mpr (by simpa only [div_eq_mul_inv, one_mul] using hinner)

lemma ppt_inverse_log_cube_cutoff_loss {γ : ℝ} (hγ : 0 < γ) :
    ∀ᶠ t : ℝ in atTop, Real.log (10*t) ≤ γ*t/(Real.log t)^3 := by
  have h₃ : Tendsto (fun t : ℝ => (Real.log t)^3/t) atTop (𝓝 0) :=
    Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero
  have h₄ : Tendsto (fun t : ℝ => (Real.log t)^4/t) atTop (𝓝 0) :=
    Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero
  have hsum : Tendsto (fun t : ℝ =>
      Real.log 10*((Real.log t)^3/t)+(Real.log t)^4/t) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add] using (h₃.const_mul (Real.log 10)).add h₄
  filter_upwards [hsum.eventually (eventually_lt_nhds hγ),
    eventually_gt_atTop (1 : ℝ)] with t ht ht1
  have ht0 : 0 < t := zero_lt_one.trans ht1
  have hlog : 0 < Real.log t := Real.log_pos ht1
  have he : Real.log (10*t)*(Real.log t)^3/t =
      Real.log 10*((Real.log t)^3/t)+(Real.log t)^4/t := by
    rw [Real.log_mul (by norm_num : (10 : ℝ) ≠ 0) ht0.ne']
    ring
  rw [← he] at ht
  have hm := (div_lt_iff₀ ht0).mp ht
  exact (le_div_iff₀ (pow_pos hlog 3)).mpr hm.le

/-- The first normalized cutoff is controlled by its actual logarithmic
loss.  All other assumptions are the literal Ford parameter restrictions
expressed through normalized coordinates. -/
theorem ppt_ford_parameters_of_normalized_grid {z : ℝ} (hz : 1 < z)
    (hB : 0 < B z) (b D r : ℕ) (S : ℝ) (ν μ : ℕ → ℝ)
    (hb : 1 ≤ b) (hν : ν 0=1) (hS : Real.exp (Real.exp 1) ≤ S)
    (hSb : S ≤ comparisonCutoffs z ν b)
    (horder : ∀ j ∈ Finset.range b, ν (j+1) < μ j ∧ μ j < ν j)
    (hfirst : Real.log (10*B z) ≤ B z*(1-ν 1))
    (hgap : ∀ j ∈ Finset.Icc 2 b,
      2*Real.sqrt (B S/B z) < ν (j-1)-ν j)
    (hD : 1 ≤ D) (hDz : (D : ℝ) ≤ z^(1/100 : ℝ))
    (hDs : (largestPrimeFactor D : ℝ) ≤ comparisonCutoffs z ν b)
    (hr : 1 ≤ r) (hrz : (r : ℝ) ≤ z^(1/10 : ℝ)) :
    FordComparisonParameters b z S D r
      (comparisonCutoffs z ν) (comparisonCutoffs z μ) := by
  refine ⟨hb, ?_, hS, hSb, ?_, ?_, ?_, hD, hDz, hDs, hr, hrz⟩
  · simp only [comparisonCutoffs, hν, mul_one, B,
      Real.exp_log (Real.log_pos hz), Real.exp_log (zero_lt_one.trans hz)]
  · intro j hj
    exact ⟨Real.exp_lt_exp.mpr (Real.exp_lt_exp.mpr
      (mul_lt_mul_of_pos_left (horder j hj).1 hB)),
      Real.exp_lt_exp.mpr (Real.exp_lt_exp.mpr
      (mul_lt_mul_of_pos_left (horder j hj).2 hB))⟩
  · exact ppt_comparison_cutoff_power_of_log_loss hz hB hfirst
  · intro j hj
    simpa only [comparisonCutoffs_doubleLog hB.ne'] using hgap j hj

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTComparisonGrid
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The PPT first cutoff approaches the head coordinate.  Its lower head
edge must therefore vary with the available inverse-cube gap.  Interior
grid intervals and their finite labels are the same as in the ordinary
comparison grid.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

/-- Every adaptive interval contains both actual coordinates.  The
top lower edge is chosen inside the true head-to-tail gap. -/
theorem ppt_grid_intervals {b : ℕ} {δ ζ θ : ℝ} (hb : 1 ≤ b) (hδ : 0 < δ)
    (u v : Fin b → ℝ) (hu : ∀ j, 0 ≤ u j) (hv : ∀ j, 0 ≤ v j)
    (halign : ∀ j, |u j-v j| ≤ (2*(j.val : ℝ)+1)*δ)
    (htop : max (u ⟨0,hb⟩) (v ⟨0,hb⟩) ≤ 1)
    (hhead : θ ≤ min (u ⟨0,hb⟩) (v ⟨0,hb⟩)) (hθ : θ < 1)
    (hfirst : pairedGridUpper δ ζ (fun j => collisionGridIndex δ (u j) (v j)) 1 < θ)
    (hnext : ∀ j : Fin b, ∀ hj : j.val+1 < b,
      max (u ⟨j.val+1,hj⟩) (v ⟨j.val+1,hj⟩)+(2*(j.val+1 : ℕ)+4 : ℝ)*δ <
        min (u j) (v j))
    (hbottom : ζ+δ < min (u ⟨b-1,by omega⟩) (v ⟨b-1,by omega⟩)) :
    let n := fun j => collisionGridIndex δ (u j) (v j)
    pairedGridUpper δ ζ n 0 = 1 ∧ pairedGridUpper δ ζ n b = ζ ∧
    (∀ j : Fin b, pptGridLower δ θ n j ≤ u j ∧ pptGridLower δ θ n j ≤ v j ∧
      u j ≤ pairedGridUpper δ ζ n j ∧ v j ≤ pairedGridUpper δ ζ n j) ∧
    (∀ j ∈ Finset.range b,
      pairedGridUpper δ ζ n (j+1) < pptGridLower δ θ n j ∧
        pptGridLower δ θ n j < pairedGridUpper δ ζ n j) := by
  dsimp only
  let n := fun j => collisionGridIndex δ (u j) (v j)
  have henc (j : Fin b) := collision_grid_enclosure hδ (hu j) (hv j) (halign j)
  have hlo (j : Fin b) := collision_grid_lower_bounds hδ (hu j) (hv j)
  refine ⟨by simp [pairedGridUpper],
    by simp [pairedGridUpper, show b ≠ 0 by omega], ?_, ?_⟩
  · intro j
    by_cases hj0 : j.val = 0
    · have he : j = ⟨0,hb⟩ := Fin.ext hj0
      subst j
      simp only [pptGridLower, pairedGridUpper, ite_true, if_true]
      exact ⟨hhead.trans (min_le_left _ _), hhead.trans (min_le_right _ _),
        (le_max_left _ _).trans htop, (le_max_right _ _).trans htop⟩
    · simp only [pptGridLower, pairedGridLower, pairedGridUpper, hj0, ite_false, if_false,
        dite_eq_left j.isLt]
      exact ⟨(henc j).1, (henc j).2.1, (henc j).2.2.1.le, (henc j).2.2.2.1.le⟩
  · intro j hj
    have hjb := Finset.mem_range.mp hj
    by_cases hj0 : j = 0
    · subst j
      simp only [pptGridLower, pairedGridUpper, ite_true, if_true]
      exact ⟨hfirst, hθ⟩
    · simp only [pptGridLower, pairedGridLower, hj0, ite_false, if_false, dite_eq_left hjb]
      constructor
      · by_cases hjn : j+1 < b
        · have he := collision_grid_separated hδ (hu ⟨j,hjb⟩) (hv ⟨j,hjb⟩)
            (hu ⟨j+1,hjn⟩) (hv ⟨j+1,hjn⟩) (halign ⟨j+1,hjn⟩)
            (hnext ⟨j,hjb⟩ hjn)
          simpa only [pairedGridUpper, Nat.add_eq_zero_iff, one_ne_zero,
            and_false, ite_false, if_false, dite_eq_left hjn] using he
        · have hlast : j = b-1 := by omega
          have heq : (⟨b-1,by omega⟩ : Fin b) = ⟨j,hjb⟩ := Fin.ext hlast.symm
          have hh : ζ+δ < min (u ⟨j,hjb⟩) (v ⟨j,hjb⟩) := by
            simpa only [heq] using hbottom
          have he : ζ < collisionGridLower δ (n ⟨j,hjb⟩) := by
            dsimp [n]
            linarith [(hlo ⟨j,hjb⟩).2]
          simpa only [pairedGridUpper, Nat.add_eq_zero_iff, one_ne_zero,
            and_false, ite_false, if_false, dite_eq_right hjn] using he
      · have hh := (henc ⟨j,hjb⟩).1.trans_lt (henc ⟨j,hjb⟩).2.2.1
        simpa only [pairedGridUpper, hj0, ite_false, if_false, dite_eq_left hjb] using hh

lemma ppt_grid_width {b : ℕ} (δ ζ θ : ℝ) (n : Fin b → ℕ)
    {j : ℕ} (hj : j ∈ Finset.Icc 1 (b-1)) :
    pairedGridUpper δ ζ n j-pptGridLower δ θ n j = (2*(j : ℝ)+3)*δ := by
  have hj0 : j ≠ 0 := by have := (Finset.mem_Icc.mp hj).1; omega
  simpa only [pptGridLower, ite_eq_right hj0] using paired_grid_width δ ζ n hj

/-- The constructed finite intervals satisfy the literal published
parameter restrictions once their actual first-cutoff loss and scalar
size bounds are known. -/
theorem ppt_ford_parameters_from_grid {b : ℕ} {z S δ ζ θ : ℝ}
    (hb : 1 ≤ b) (hz : 1 < z) (hB : 0 < B z) (D r : ℕ)
    (n : Fin b → ℕ) (hS : Real.exp (Real.exp 1) ≤ S)
    (hSb : S ≤ comparisonCutoffs z (pairedGridUpper δ ζ n) b)
    (horder : ∀ j ∈ Finset.range b,
      pairedGridUpper δ ζ n (j+1) < pptGridLower δ θ n j ∧
        pptGridLower δ θ n j < pairedGridUpper δ ζ n j)
    (hfirst : Real.log (10*B z) ≤ B z*(1-pairedGridUpper δ ζ n 1))
    (hgap : ∀ j ∈ Finset.Icc 2 b,
      2*Real.sqrt (B S/B z) < pairedGridUpper δ ζ n (j-1)-pairedGridUpper δ ζ n j)
    (hD : 1 ≤ D) (hDz : (D : ℝ) ≤ z^(1/100 : ℝ))
    (hDs : (largestPrimeFactor D : ℝ) ≤ comparisonCutoffs z (pairedGridUpper δ ζ n) b)
    (hr : 1 ≤ r) (hrz : (r : ℝ) ≤ z^(1/10 : ℝ)) :
    FordComparisonParameters b z S D r
      (comparisonCutoffs z (pairedGridUpper δ ζ n))
      (comparisonCutoffs z (pptGridLower δ θ n)) := by
  exact ppt_ford_parameters_of_normalized_grid hz hB b D r S
    (pairedGridUpper δ ζ n) (pptGridLower δ θ n) hb
    (by simp [pairedGridUpper]) hS hSb horder hfirst hgap hD hDz hDs hr hrz

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTRowMargin
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The relaxed geometric family retains the row and adjacent-coordinate
margins required by the PPT comparison construction.  A bounded change
of the normalizing head coordinate consumes only part of that margin.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma ppt_half_row_error_bounds (r : ℕ) :
    0 < rowContractionError r/2 ∧ rowContractionError r/2 ≤ 1 := by
  have hr : (1 : ℝ) ≤ (r : ℝ)+1 := by
    linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
  have hp : (1 : ℝ) ≤ ((r : ℝ)+1)^3 := one_le_pow₀ hr
  unfold rowContractionError
  constructor
  · positivity
  · rw [div_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 5*((r : ℝ)+1)^3*2)).mpr
    nlinarith

lemma ppt_row_budget_after_head_error {R H T e ω : ℝ} (hT : 0 < T)
    (hω : 0 < ω) (hω1 : ω ≤ 1) (hrow : R ≤ H/(1+ω))
    (hhead : H ≤ T+e) (herr : 4*e ≤ ω*T) :
    R ≤ (1-ω/4)*T := by
  have hden : 0 < 1+ω := by linarith
  apply hrow.trans
  apply (div_le_div_of_nonneg_right hhead hden.le).trans
  apply (div_le_iff₀ hden).mpr
  have hsq : ω^2 ≤ ω := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hsq hT.le
  nlinarith

/-- The explicit inverse-cube row budget is retained under a head error
of at most a quarter of the relaxed row margin. -/
theorem ppt_relaxed_row_budget {m n : ℕ} {B c T e : ℝ} {v : Fin n → ℝ}
    (hv : v ∈ relaxedGeometricFamily m n B c) (i : Fin n)
    (hT : 0 < T) (hhead : v i ≤ T+e)
    (herr : 4*e ≤ (rowContractionError (m-(i.val+1))/2)*T) :
    (∑ j : Fin n, if i < j then a (j.val-i.val)*v j else 0) ≤
      (1-rowContractionError (m-(i.val+1))/8)*T := by
  have hω := ppt_half_row_error_bounds (m-(i.val+1))
  have hh := ppt_row_budget_after_head_error hT hω.1 hω.2
    (hv.1.2.2.1 i) hhead herr
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTSurvivingSlack
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The comparison simplex after a maximal-prefix choice and cancellation.
The surviving coordinates retain their order, so their smaller renewal
weights preserve the actual inverse-cube row margin.  Grid and normality
errors are charged explicitly to this margin.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

private lemma ppt_fin_embedding_offset {b n : ℕ} (ι : Fin b ↪o Fin n)
    (hb : 0 < b) (r : Fin b) :
    (ι ⟨0,hb⟩).val+r.val ≤ (ι r).val := by
  have hall : ∀ k (hk : k < b),
      (ι ⟨0,hb⟩).val+k ≤ (ι ⟨k,hk⟩).val := by
    intro k
    induction k with
    | zero => intro hk; simp
    | succ k ih =>
      intro hk
      have hk' : k < b := by omega
      have hp := ih hk'
      have hs := ι.strictMono
        (show (⟨k,hk'⟩ : Fin b) < ⟨k+1,hk⟩ from Nat.lt_succ_self k)
      change (ι ⟨k,hk'⟩).val < (ι ⟨k+1,hk⟩).val at hs
      omega
  exact hall r.val r.isLt

private lemma ppt_sum_positive_fin_indices (b : ℕ) (f : ℕ → ℝ) :
    (∑ r ∈ Finset.Icc 1 (b-1), f r) =
      ∑ r : Fin b, if 0 < r.val then f r.val else 0 := by
  classical
  calc
    _ = ∑ r ∈ Finset.univ.filter (fun r : Fin b => 0 < r.val), f r.val := by
      symm
      apply Finset.sum_bij (fun r _ => r.val)
      · intro r hr
        have hpos := (Finset.mem_filter.mp hr).2
        exact Finset.mem_Icc.mpr ⟨hpos, by omega⟩
      · intro r hr s hs hrs
        exact Fin.ext hrs
      · intro k hk
        have hk' := Finset.mem_Icc.mp hk
        have hkb : k < b := by omega
        refine ⟨⟨k,hkb⟩, ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk'.1⟩
      · intro r hr
        rfl
    _ = _ := by rw [Finset.sum_filter]

/-- Removing ordered coordinates decreases the renewal-weighted row. -/
lemma ppt_surviving_row_sum_le {b n : ℕ} (ι : Fin b ↪o Fin n)
    (hb : 0 < b) (v : Fin n → ℝ) (hv : ∀ j, 0 ≤ v j) :
    (∑ r : Fin b, if 0 < r.val then a r.val*v (ι r) else 0) ≤
      ∑ j : Fin n, if ι ⟨0,hb⟩ < j then
        a (j.val-(ι ⟨0,hb⟩).val)*v j else 0 := by
  classical
  let R : Fin n → ℝ := fun j => if ι ⟨0,hb⟩ < j then
    a (j.val-(ι ⟨0,hb⟩).val)*v j else 0
  have hR (j : Fin n) : 0 ≤ R j := by
    dsimp only [R]
    split_ifs with hj
    · have hidx : 1 ≤ j.val-(ι ⟨0,hb⟩).val := by
        change (ι ⟨0,hb⟩).val < j.val at hj
        omega
      exact mul_nonneg (a_pos hidx).le (hv j)
    · exact le_rfl
  calc
    _ ≤ ∑ r : Fin b, R (ι r) := by
      apply Finset.sum_le_sum
      intro r hr
      by_cases hpos : 0 < r.val
      · have hlt : ι ⟨0,hb⟩ < ι r :=
          ι.strictMono (show (⟨0,hb⟩ : Fin b) < r from hpos)
        simp only [ite_eq_left hpos, R, ite_eq_left hlt]
        apply mul_le_mul_of_nonneg_right _ (hv (ι r))
        apply a_monotone_positive hpos
        have hh := ppt_fin_embedding_offset ι hb r
        omega
      · have hr0 : r = ⟨0,hb⟩ := by
          apply Fin.ext
          change r.val = 0
          omega
        simp [hr0, R]
    _ = ∑ j ∈ Finset.univ.image ι, R j := by
      rw [Finset.sum_image]
      exact fun r _ s _ hrs => ι.injective hrs
    _ ≤ ∑ j : Fin n, R j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro j hj hj'
      exact hR j

/-- The actual order embedding supplies the reindexing, while each grid
coordinate pays only its stated additive error. -/
lemma ppt_gridded_surviving_row {b n : ℕ} (ι : Fin b ↪o Fin n)
    (hb : 0 < b) (v : Fin n → ℝ) (ν : ℕ → ℝ) {T σ e : ℝ}
    (hT : 0 < T) (hv : ∀ j, 0 ≤ v j)
    (hrow : (∑ j : Fin n, if ι ⟨0,hb⟩ < j then
      a (j.val-(ι ⟨0,hb⟩).val)*v j else 0) ≤ (1-σ)*T)
    (hgrid : ∀ r : Fin b, 0 < r.val → ν r.val ≤ v (ι r)/T+e) :
    (∑ r ∈ Finset.Icc 1 (b-1), a r*ν r) ≤
      1-σ+e*(∑ r ∈ Finset.Icc 1 (b-1), a r) := by
  let u : ℕ → ℝ := fun r => if hr : r < b then v (ι ⟨r,hr⟩) else 0
  have hmass : (∑ r ∈ Finset.Icc 1 (b-1), a r*u r) ≤ (1-σ)*T := by
    rw [ppt_sum_positive_fin_indices]
    have hh := (ppt_surviving_row_sum_le ι hb v hv).trans hrow
    simpa only [u, Fin.isLt, dite_true] using hh
  have hgrid' (r : ℕ) (hr : r ∈ Finset.Icc 1 (b-1)) : ν r ≤ u r/T+e := by
    have hr' := Finset.mem_Icc.mp hr
    have hrb : r < b := by omega
    simpa only [u, dite_eq_left hrb] using hgrid ⟨r,hrb⟩ hr'.1
  calc
    _ ≤ ∑ r ∈ Finset.Icc 1 (b-1), a r*(u r/T+e) := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_left (hgrid' r hr)
        (a_pos (Finset.mem_Icc.mp hr).1).le
    _ = (∑ r ∈ Finset.Icc 1 (b-1), a r*u r)/T+
        e*(∑ r ∈ Finset.Icc 1 (b-1), a r) := by
      simp only [mul_add, Finset.sum_add_distrib]
      congr 1
      · rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro r hr
        ring
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        ring
    _ ≤ _ := by
      have hh := (div_le_iff₀ hT).mpr hmass
      linarith only [hh]

/-- The inverse-cube margin comes from membership in the constructed
geometric family, before matching coordinates are removed. -/
theorem ppt_relaxed_surviving_slack {m n b : ℕ} {B c T headError e : ℝ}
    {v : Fin n → ℝ} (hv : v ∈ relaxedGeometricFamily m n B c)
    (ι : Fin b ↪o Fin n) (hb : 0 < b) (ν : ℕ → ℝ)
    (hT : 0 < T) (hhead : v (ι ⟨0,hb⟩) ≤ T+headError)
    (herr : 4*headError ≤
      (rowContractionError (m-((ι ⟨0,hb⟩).val+1))/2)*T)
    (hgrid : ∀ r : Fin b, 0 < r.val → ν r.val ≤ v (ι r)/T+e) :
    (∑ r ∈ Finset.Icc 1 (b-1), a r*ν r) ≤
      1-rowContractionError (m-((ι ⟨0,hb⟩).val+1))/8+
        e*(∑ r ∈ Finset.Icc 1 (b-1), a r) := by
  exact ppt_gridded_surviving_row ι hb v ν hT hv.1.1
    (ppt_relaxed_row_budget hv (ι ⟨0,hb⟩) hT hhead herr) hgrid

/-- After charging the grid widths and normality discrepancy, the
published comparison exponent retains half the concrete row margin. -/
theorem ppt_relaxed_surviving_exponent {m n b : ℕ} {budget c T headError e w S z : ℝ}
    {v : Fin n → ℝ} (hv : v ∈ relaxedGeometricFamily m n budget c)
    (ι : Fin b ↪o Fin n) (hb : 0 < b) (ν μ : ℕ → ℝ)
    (hT : 0 < T) (hBz : B z ≠ 0)
    (hhead : v (ι ⟨0,hb⟩) ≤ T+headError)
    (herr : 4*headError ≤
      (rowContractionError (m-((ι ⟨0,hb⟩).val+1))/2)*T)
    (hgrid : ∀ r : Fin b, 0 < r.val → ν r.val ≤ v (ι r)/T+e)
    (hwidth : ∀ r ∈ Finset.Icc 1 (b-1), ν r-μ r ≤ w)
    (herror : e*(∑ r ∈ Finset.Icc 1 (b-1), a r)+2*(b-1 : ℕ)*w+
      Real.sqrt (B S/B z)*(∑ i ∈ Finset.Icc 2 b, ((i : ℝ)*Real.log i+i)) ≤
        rowContractionError (m-((ι ⟨0,hb⟩).val+1))/16) :
    -2+(∑ r ∈ Finset.Icc 1 (b-1),
      a r*(B (comparisonCutoffs z ν r)/B z))+
      comparisonError b z S (comparisonCutoffs z ν) (comparisonCutoffs z μ) ≤
        -1-rowContractionError (m-((ι ⟨0,hb⟩).val+1))/16 := by
  have hslack := ppt_relaxed_surviving_slack hv ι hb ν hT hhead herr hgrid
  have hh := comparisonExponent_le b z S (comparisonCutoffs z ν) (comparisonCutoffs z μ)
    (rowContractionError (m-((ι ⟨0,hb⟩).val+1))/8) e w
    (by simpa only [comparisonCutoffs_doubleLog hBz] using hslack)
    (by simpa only [comparisonCutoffs_doubleLog hBz] using hwidth)
    (by
      convert herror using 1
      all_goals try with_reducible_and_instances rfl
      ring)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

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

/-- A direct bound for the three terms charged to the comparison
exponent.  The two grid widths may differ, as in Ford's PPT construction. -/
lemma ppt_grid_error_polynomial_bound {b H : ℕ} {e w η δ : ℝ}
    (hH : 1 ≤ H) (hbH : b ≤ H) (hδ : 0 ≤ δ)
    (he : e ≤ (2*(b : ℝ)+4)*δ) (hw : w ≤ (4*(b : ℝ)+3)*δ)
    (hη : η ≤ δ) :
    e*(∑ j ∈ Finset.Icc 1 (b-1), a j)+2*(b-1 : ℕ)*w+
      η*(∑ i ∈ Finset.Icc 2 b, ((i : ℝ)*Real.log i+i)) ≤
        32*(H : ℝ)^3*δ := by
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hbR : (b : ℝ) ≤ H := by exact_mod_cast hbH
  have hb' : b-1 ≤ H := (Nat.sub_le b 1).trans hbH
  have hb'R : ((b-1 : ℕ) : ℝ) ≤ H := by exact_mod_cast hb'
  have hsa0 : 0 ≤ ∑ j ∈ Finset.Icc 1 (b-1), a j :=
    Finset.sum_nonneg fun j hj => (a_pos (Finset.mem_Icc.mp hj).1).le
  have hsa : (∑ j ∈ Finset.Icc 1 (b-1), a j) ≤ (H : ℝ)^2 :=
    (sum_a_le_square (b-1)).trans
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hb'R 2)
  have he' : e ≤ 6*(H : ℝ)*δ :=
    he.trans (mul_le_mul_of_nonneg_right (by linarith) hδ)
  have hw' : w ≤ 7*(H : ℝ)*δ :=
    hw.trans (mul_le_mul_of_nonneg_right (by linarith) hδ)
  have hfirst : e*(∑ j ∈ Finset.Icc 1 (b-1), a j) ≤ 6*(H : ℝ)^3*δ := by
    calc
      _ ≤ (6*(H : ℝ)*δ)*(H : ℝ)^2 :=
        mul_le_mul he' hsa hsa0 (by positivity)
      _ = _ := by ring
  have hsecond : 2*(b-1 : ℕ)*w ≤ 14*(H : ℝ)^2*δ := by
    calc
      _ ≤ (2*((b-1 : ℕ) : ℝ))*(7*(H : ℝ)*δ) :=
        mul_le_mul_of_nonneg_left hw' (by positivity)
      _ ≤ (2*(H : ℝ))*(7*(H : ℝ)*δ) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by ring
  have hlog0 : 0 ≤ ∑ i ∈ Finset.Icc 2 b, ((i : ℝ)*Real.log i+i) := by
    apply Finset.sum_nonneg
    intro i hi
    have hiR : (1 : ℝ) ≤ i := by
      have hi2 := (Finset.mem_Icc.mp hi).1
      exact_mod_cast (show 1 ≤ i by omega)
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hiR))
      (Nat.cast_nonneg _)
  have hthird : η*(∑ i ∈ Finset.Icc 2 b, ((i : ℝ)*Real.log i+i)) ≤
      2*(H : ℝ)^3*δ := by
    calc
      _ ≤ δ*(2*(H : ℝ)^3) :=
        mul_le_mul hη (comparison_log_sum_bound hbH hH) hlog0 hδ
      _ = _ := by ring
  have hpow : (H : ℝ)^2 ≤ (H : ℝ)^3 := by nlinarith
  have hpowδ := mul_le_mul_of_nonneg_right hpow hδ
  have hnonneg : 0 ≤ (H : ℝ)^3*δ := by positivity
  nlinarith only [hfirst, hsecond, hthird, hpowδ, hnonneg]

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTGridMargins
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The quantitative margins for the actual PPT paired grid.  The last
retained coordinates have size at least `t^(-1/3)`; their inverse-cube
relative gaps dominate the normality mesh when the dimension is
logarithmic in `t`.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

/-- A left-coordinate gap survives both alignment errors and the stated
grid padding. -/
lemma ppt_paired_gap_of_left_gap {u v u' v' A B padding : ℝ}
    (hprev : |u-v| ≤ A) (hnext : |u'-v'| ≤ B)
    (hgap : u'+A+B+padding < u) :
    max u' v'+padding < min u v := by
  have hA : 0 ≤ A := (abs_nonneg _).trans hprev
  have hB : 0 ≤ B := (abs_nonneg _).trans hnext
  have hmin : u-A ≤ min u v := le_min (by linarith) (by linarith [(abs_le.mp hprev).2])
  have hmax : max u' v' ≤ u'+B := max_le (by linarith) (by linarith [(abs_le.mp hnext).1])
  linarith

lemma ppt_contraction_gap {u v e ω : ℝ} (hu : 0 ≤ u) (hω : 0 < ω)
    (hω1 : ω ≤ 1) (hcontract : v ≤ u/(1+ω)+e) :
    ω*u/2-e ≤ u-v := by
  have hden : 0 < 1+ω := by linarith
  have hrec : 1/(1+ω) ≤ 1-ω/2 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hh := mul_le_mul_of_nonneg_right hrec hu
  have hbound : u/(1+ω) ≤ (1-ω/2)*u := by
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using hh
  nlinarith

/-- The entire grid-padding cost is smaller than a fixed fraction of the
last retained coordinate's inverse-cube gap, uniformly in the dimension. -/
theorem ppt_log_dimension_separation {C : ℝ} (_hC : 0 < C) :
    ∀ᶠ t : ℝ in atTop, ∀ H : ℕ,
      1 ≤ H → (H : ℝ) ≤ C*Real.log t →
      (8*(H : ℝ)+20)*(2*(Real.log t)^5/Real.sqrt t) <
        1/(40*(H : ℝ)^3*t^(1/3 : ℝ)) := by
  have hlim : Tendsto (fun t : ℝ => (Real.log t)^9/t^(1/6 : ℝ)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (9 : ℕ)
        (show (0 : ℝ) < 1/6 by norm_num)).tendsto_div_nhds_zero
  have hscaled : Tendsto (fun t : ℝ =>
      2240*C^4*((Real.log t)^9/t^(1/6 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hlim.const_mul (2240*C^4)
  filter_upwards [hscaled.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop (1 : ℝ)] with t ht ht1
  intro H hH hdim
  have ht0 : 0 < t := zero_lt_one.trans ht1
  have hlog : 0 < Real.log t := Real.log_pos ht1
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hH0 : (0 : ℝ) < H := zero_lt_one.trans_le hHR
  have hthird : 0 < t^(1/3 : ℝ) := Real.rpow_pos_of_pos ht0 _
  have hsixth : 0 < t^(1/6 : ℝ) := Real.rpow_pos_of_pos ht0 _
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  have hprod : t^(1/3 : ℝ)*t^(1/6 : ℝ) = Real.sqrt t := by
    rw [← Real.rpow_add ht0, Real.sqrt_eq_rpow]
    norm_num
  have hratio : t^(1/3 : ℝ)/Real.sqrt t = 1/t^(1/6 : ℝ) := by
    apply (div_eq_div_iff hsqrt.ne' hsixth.ne').mpr
    simpa only [one_mul] using hprod
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg H) hdim 4
  apply (lt_div_iff₀ (by positivity : 0 < 40*(H : ℝ)^3*t^(1/3 : ℝ))).mpr
  calc
    _ ≤ (28*(H : ℝ))*(2*(Real.log t)^5/Real.sqrt t)*
        (40*(H : ℝ)^3*t^(1/3 : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = 2240*(H : ℝ)^4*(Real.log t)^5/t^(1/6 : ℝ) := by
      calc
        _ = 2240*(H : ℝ)^4*(Real.log t)^5*(t^(1/3 : ℝ)/Real.sqrt t) := by ring
        _ = _ := by rw [hratio]; ring
    _ ≤ 2240*(C*Real.log t)^4*(Real.log t)^5/t^(1/6 : ℝ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num))
          (by positivity)) hsixth.le
    _ = 2240*C^4*((Real.log t)^9/t^(1/6 : ℝ)) := by ring
    _ < 1 := ht

/-- The additive logarithmic factor-count error can be included by
doubling the square-root mesh. -/
theorem ppt_logarithmic_alignment_error :
    ∀ᶠ t : ℝ in atTop,
      Real.log (3*t)/t ≤ (Real.log t)^5/Real.sqrt t := by
  have hlog : Tendsto (fun t : ℝ => Real.log t/Real.sqrt t) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow, Real.rpow_natCast, pow_one] using
      (isLittleO_log_rpow_rpow_atTop (1 : ℕ)
        (show (0 : ℝ) < 1/2 by norm_num)).tendsto_div_nhds_zero
  have hconst : Tendsto (fun t : ℝ => Real.log 3/Real.sqrt t) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (tendsto_const_nhds.div_atTop (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)))
  have hsum : Tendsto (fun t : ℝ => (Real.log 3+Real.log t)/Real.sqrt t)
      atTop (𝓝 0) := by
    simpa only [← add_div, zero_add] using hconst.add hlog
  filter_upwards [hsum.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_gt_atTop (1 : ℝ)] with t ht htlog ht1
  have ht0 : 0 < t := zero_lt_one.trans ht1
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  have hlog3 : Real.log (3*t) = Real.log 3+Real.log t :=
    Real.log_mul (by norm_num) ht0.ne'
  have hnum : Real.log (3*t) ≤ Real.sqrt t := by
    rw [hlog3]
    exact ((div_lt_one hsqrt).mp ht).le
  have hpower : (1 : ℝ) ≤ (Real.log t)^5 := one_le_pow₀ htlog
  calc
    _ ≤ Real.sqrt t/t := div_le_div_of_nonneg_right hnum ht0.le
    _ = 1/Real.sqrt t := by rw [Real.sqrt_div_self, one_div]
    _ ≤ (Real.log t)^5/Real.sqrt t := div_le_div_of_nonneg_right hpower hsqrt.le

/-- The doubled mesh also fits in the inverse-cube exponent margin. -/
theorem ppt_grid_error_absorbed_two_mesh {C : ℝ} (hC : 0 < C) :
    ∀ᶠ t : ℝ in atTop, ∀ (b H r : ℕ) (e w η δ : ℝ),
      1 ≤ H → b ≤ H → r+1 ≤ H → (H : ℝ) ≤ C*Real.log t →
      0 ≤ δ → δ ≤ 2*((Real.log t)^5/Real.sqrt t) →
      e ≤ (2*(b : ℝ)+4)*δ → w ≤ (4*(b : ℝ)+3)*δ → η ≤ δ →
      e*(∑ j ∈ Finset.Icc 1 (b-1), a j)+2*(b-1 : ℕ)*w+
        η*(∑ i ∈ Finset.Icc 2 b, ((i : ℝ)*Real.log i+i)) ≤
          rowContractionError r/16 := by
  filter_upwards [ppt_log_dimension_mesh_budget (C := 2*C) (by positivity),
    eventually_gt_atTop (1 : ℝ)] with t ht ht1
  intro b H r e w η δ hH hbH hrH hdim hδ hδmax he hw hη
  have hlog : 0 < Real.log t := Real.log_pos ht1
  have hmesh : 0 ≤ (Real.log t)^5/Real.sqrt t := by positivity
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hdim' : ((2*H : ℕ) : ℝ) ≤ (2*C)*Real.log t := by
    push_cast
    linarith
  have hbudget := ht (2*H) (by omega) hdim'
  apply (ppt_grid_error_polynomial_bound hH hbH hδ he hw hη).trans
  calc
    _ ≤ 32*(H : ℝ)^3*(2*((Real.log t)^5/Real.sqrt t)) :=
      mul_le_mul_of_nonneg_left hδmax (by positivity)
    _ ≤ 32*((2*H : ℕ) : ℝ)^3*((Real.log t)^5/Real.sqrt t) := by
      push_cast
      have hp : 0 ≤ (H : ℝ)^3*((Real.log t)^5/Real.sqrt t) := by positivity
      nlinarith only [hp]
    _ ≤ 1/(80*((2*H : ℕ) : ℝ)^3) := hbudget
    _ ≤ 1/(80*(r+1 : ℝ)^3) := by
      have hr : (r+1 : ℝ) ≤ ((2*H : ℕ) : ℝ) := by exact_mod_cast (show r+1 ≤ 2*H by omega)
      exact one_div_le_one_div_of_le (by positivity)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hr 3) (by norm_num))
    _ = rowContractionError r/16 := by
      unfold rowContractionError
      rw [div_div]
      congr 1
      ring

/-- The indexed local choice `B S = h^4` fits the same PPT mesh whenever
the remaining length is logarithmic in the comparison double logarithm.
The cutoff itself is a parameter, so no global normality transfer is used. -/
theorem ppt_local_normality_error_mesh {A : ℝ} (_hA : 0 < A) :
    ∀ᶠ t : ℝ in atTop, ∀ (h : ℕ) (S : ℝ),
      (h : ℝ) ≤ A*Real.log t → 0 ≤ B S → B S ≤ (h : ℝ)^4 →
      Real.sqrt (B S/t) ≤ (Real.log t)^5/Real.sqrt t := by
  filter_upwards [Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (max 1 (A^2)))] with t ht
  intro h S hdim hBS hcutoff
  have hlog1 : 1 ≤ Real.log t := (le_max_left _ _).trans ht
  have hAlog : A^2 ≤ Real.log t := (le_max_right _ _).trans ht
  have hsqrt : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hlog3 : A^2 ≤ (Real.log t)^3 := by
    apply hAlog.trans
    simpa only [pow_one] using
      (pow_le_pow_right₀ hlog1 (show 1 ≤ 3 by omega))
  have hdim2 : (h : ℝ)^2 ≤ A^2*(Real.log t)^2 := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg h) hdim 2
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hdim5 : (h : ℝ)^2 ≤ (Real.log t)^5 := by
    apply hdim2.trans
    calc
      A^2*(Real.log t)^2 ≤ (Real.log t)^3*(Real.log t)^2 :=
        mul_le_mul_of_nonneg_right hlog3 (sq_nonneg _)
      _ = _ := by ring
  have hroot : Real.sqrt (B S) ≤ (h : ℝ)^2 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨sq_nonneg _, ?_⟩
    convert hcutoff using 1
    all_goals try with_reducible_and_instances rfl
    ring
  rw [Real.sqrt_div hBS]
  exact (div_le_div_of_nonneg_right hroot hsqrt).trans
    (div_le_div_of_nonneg_right hdim5 hsqrt)

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

/-- A bounded change of head coordinate consumes less than the allowed
quarter-row margin, uniformly for every logarithmic local dimension. -/
theorem ppt_local_head_error_absorbed {A E : ℝ} (_hA : 0 < A) (hE : 0 ≤ E) :
    ∀ᶠ t : ℝ in atTop, ∀ H r : ℕ,
      (H : ℝ) ≤ A*Real.log t → r+1 ≤ H →
      4*E ≤ (rowContractionError r/2)*t := by
  have hlim : Tendsto (fun t : ℝ => (Real.log t)^3/t) atTop (𝓝 0) :=
    Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero
  have hscaled : Tendsto (fun t : ℝ => 40*E*A^3*((Real.log t)^3/t))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using hlim.const_mul (40*E*A^3)
  filter_upwards [hscaled.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop (1 : ℝ)] with t hsmall ht
  intro H r hdim hrH
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hHR : (r+1 : ℝ) ≤ H := by exact_mod_cast hrH
  have hpH := pow_le_pow_left₀ (Nat.cast_nonneg H) hdim 3
  have hpr := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ r+1) hHR 3
  have hbound : 40*E*(r+1 : ℝ)^3 ≤ t := by
    calc
      _ ≤ 40*E*(H : ℝ)^3 :=
        mul_le_mul_of_nonneg_left hpr (by positivity)
      _ ≤ 40*E*(A*Real.log t)^3 :=
        mul_le_mul_of_nonneg_left hpH (by positivity)
      _ = (40*E*A^3*((Real.log t)^3/t))*t := by
        rw [mul_assoc (40*E*A^3), div_mul_cancel₀ _ ht0.ne']
        ring
      _ ≤ t := by
        have hh := mul_le_mul_of_nonneg_right hsmall.le ht0.le
        simpa only [one_mul] using hh
  have hdiv : 4*E ≤ t/(10*(r+1 : ℝ)^3) := by
    apply (le_div_iff₀ (by positivity : 0 < 10*(r+1 : ℝ)^3)).mpr
    nlinarith only [hbound]
  calc
    4*E ≤ t/(10*(r+1 : ℝ)^3) := hdiv
    _ = (rowContractionError r/2)*t := by
      unfold rowContractionError
      rw [div_div]
      ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTResidualComparison
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Pointwise comparison data for a residual PPT collision.  The prime lists
and shifted-product equation are the actual residual ones.  Cancellation
preserves that equation, normality supplies the paired-coordinate error,
and the geometric candidate row supplies the strict comparison exponent.
The squarefree target and the small integer residual remain explicit
arithmetic hypotheses; no counting conclusion is assumed here.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma ppt_normalized_factor_interval {z w l u : ℝ}
    (hz : 0 < B z) (hw : 1 < w)
    (hl : l ≤ B w/B z) (hu : B w/B z ≤ u) :
    Real.exp (Real.exp (B z*l)) ≤ w ∧
      w ≤ Real.exp (Real.exp (B z*u)) := by
  have hwl : B z*l ≤ B w := by
    have hh := (le_div_iff₀ hz).mp hl
    simpa only [mul_comm] using hh
  have hwu : B w ≤ B z*u := by
    have hh := (div_le_iff₀ hz).mp hu
    simpa only [mul_comm] using hh
  have he : Real.exp (Real.exp (B w)) = w := by
    rw [B, Real.exp_log (Real.log_pos hw), Real.exp_log (zero_lt_one.trans hw)]
  exact ⟨(Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hwl)).trans_eq he,
    he.symm.trans_le (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hwu))⟩

/-- The proved local normality height bound absorbs both terms of the
actual alignment estimate in the doubled paired-grid mesh. -/
theorem ppt_local_alignment_in_paired_mesh {A : ℝ} (hA : 0 < A) :
    ∀ᶠ t : ℝ in atTop, ∀ (h i : ℕ) (S u v : ℝ),
      (h : ℝ) ≤ A*Real.log t → 0 ≤ B S → B S ≤ (h : ℝ)^4 →
      |u-v| ≤ (2*(i : ℝ)+1)*Real.sqrt (B S/t)+Real.log (3*t)/t →
      |u-v| ≤ (2*(i : ℝ)+1)*(2*((Real.log t)^5/Real.sqrt t)) := by
  filter_upwards [ppt_local_normality_error_mesh hA, ppt_logarithmic_alignment_error,
    eventually_gt_atTop (1 : ℝ)] with t hmesh hlog ht
  intro h i S u v hdim hBS hheight halign
  have hsqrt := hmesh h S hdim hBS hheight
  have hmesh0 : 0 ≤ (Real.log t)^5/Real.sqrt t := by
    have hlog0 : 0 < Real.log t := Real.log_pos ht
    positivity
  have hcoef : 0 ≤ 2*(i : ℝ)+1 := by positivity
  have hh := mul_le_mul_of_nonneg_left hsqrt hcoef
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  nlinarith only [halign, hh, hlog, hmesh0, mul_nonneg hi hmesh0]

/-- The actual paired label supplies both errors used by the row
estimate, with one common bound.  These are conclusions about the grid,
not additional hypotheses on its rounded coordinates. -/
lemma ppt_paired_grid_row_errors {b : ℕ} {δ ζ θ : ℝ}
    (hδ : 0 < δ) (u v : Fin b → ℝ)
    (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (halign : ∀ i, |u i-v i| ≤ (2*(i.val : ℝ)+1)*δ) :
    let label := fun i => collisionGridIndex δ (u i) (v i)
    (∀ i : Fin b, 0 < i.val →
      pairedGridUpper δ ζ label i ≤ u i+(2*(b : ℝ)+3)*δ) ∧
    (∀ i ∈ Finset.Icc 1 (b-1),
      pairedGridUpper δ ζ label i-pptGridLower δ θ label i ≤ (2*(b : ℝ)+3)*δ) := by
  dsimp only
  constructor
  · intro i hi
    have hi' : i.val ∈ Finset.Icc 1 (b-1) :=
      Finset.mem_Icc.mpr ⟨hi, by have := i.isLt; omega⟩
    exact paired_grid_approximation hδ u v hu hv halign hi'
  · intro i hi
    rw [ppt_grid_width δ ζ θ _ hi]
    apply mul_le_mul_of_nonneg_right _ hδ.le
    have hib : i ≤ b := (Finset.mem_Icc.mp hi).2.trans (Nat.sub_le _ _)
    have hir : (i : ℝ) ≤ b := by exact_mod_cast hib
    linarith only [hir]

/-- Convert the concrete inverse-cube margin to the fixed
inverse-log-cube saving used by the comparison-block sum. -/
lemma ppt_residual_inverse_log_saving {A t : ℝ} {H r : ℕ}
    (_hA : 0 < A) (_ht : 0 < Real.log t)
    (hrH : r+1 ≤ H) (hdim : (H : ℝ) ≤ A*Real.log t) :
    1/(80*A^3)/(Real.log t)^3 ≤ rowContractionError r/16 := by
  have hr : (r+1 : ℝ) ≤ A*Real.log t := by
    have hh : (r+1 : ℝ) ≤ H := by exact_mod_cast hrH
    exact hh.trans hdim
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ r+1) hr 3
  have hh : 1/(80*(A*Real.log t)^3) ≤ 1/(80*(r+1 : ℝ)^3) :=
    one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_left hp (by norm_num))
  calc
    _ = 1/(80*(A*Real.log t)^3) := by rw [div_div, mul_pow]; ring
    _ ≤ 1/(80*(r+1 : ℝ)^3) := hh
    _ = rowContractionError r/16 := by unfold rowContractionError; rw [div_div]; ring

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

/-- Uniform replacement of a normal prime by the largest factor of its
predecessor, on the local comparison scale. -/
theorem ppt_normal_factor_loss_mesh : ∀ᶠ z : ℝ in atTop,
    ∀ (p : ℕ) (S : ℝ), 3 ≤ p → 1 < S → 0 ≤ B S → S ≤ z →
      IsNormalPrime S p → (p-1 : ℕ) ≤ z →
      B p/B z-2*((Real.log (B z))^5/Real.sqrt (B z)) ≤
        B (largestPrimeFactor (p-1))/B z ∧
      B (largestPrimeFactor (p-1))/B z ≤ B p/B z := by
  filter_upwards [B_tendsto.eventually ppt_logarithmic_alignment_error,
    B_tendsto.eventually (eventually_ge_atTop (Real.exp 1))] with z herror hB
  intro p S hp3 hS hBS hSz hp hpz
  have hB0 : 0 < B z := (Real.exp_pos 1).trans_le hB
  have hp1 : (1 : ℝ) < (p-1 : ℕ) := by
    exact_mod_cast (show 1 < p-1 by omega)
  have hpred : B (p-1 : ℕ) ≤ B z :=
    Real.log_le_log (Real.log_pos hp1)
      (Real.log_le_log (zero_lt_one.trans hp1) hpz)
  have hBSz : B S ≤ B z :=
    Real.log_le_log (Real.log_pos hS)
      (Real.log_le_log (zero_lt_one.trans hS) hSz)
  have hband := normal_prime_largest_band hp hp3 hS hBS hBSz hB0 hpred le_rfl le_rfl
  have hlog : 1 ≤ Real.log (3*B z) := by
    have hmul : Real.exp 1 ≤ 3*B z := by linarith only [hB, Real.exp_pos 1]
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hmul
  have hloss : (1+Real.log (3*B z))/B z ≤
      2*((Real.log (B z))^5/Real.sqrt (B z)) := by
    have hh := div_le_div_of_nonneg_right
      (show 1+Real.log (3*B z) ≤ 2*Real.log (3*B z) by linarith only [hlog]) hB0.le
    have hh' : (1+Real.log (3*B z))/B z ≤ 2*(Real.log (3*B z)/B z) := by
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      ring
    linarith only [hh', herror]
  constructor
  · have hh := div_le_div_of_nonneg_right hband.1 hB0.le
    have he : (B p-1-Real.log (3*B z))/B z =
        B p/B z-(1+Real.log (3*B z))/B z := by ring
    rw [he] at hh
    linarith only [hh, hloss]
  · exact div_le_div_of_nonneg_right hband.2 hB0.le

/-- A geometric contraction of prime coordinates gives a quantitative
gap after replacing them by predecessor-factor coordinates. -/
lemma ppt_contracted_factor_gap {t u u' v v' ω δ : ℝ} {H : ℕ}
    (ht : 0 < t) (hH : 1 ≤ H)
    (hlower : 1/t^(1/3 : ℝ) ≤ u)
    (hω : 1/(10*(H : ℝ)^3) ≤ ω) (hω1 : ω ≤ 1)
    (hcontract : u' ≤ u/(1+ω))
    (hfactor : u-δ ≤ v) (hfactor' : v' ≤ u') :
    1/(20*(H : ℝ)^3*t^(1/3 : ℝ))-δ ≤ v-v' := by
  have hHr : (0 : ℝ) < H := by exact_mod_cast (zero_lt_one.trans_le hH)
  have htroot : 0 < t^(1/3 : ℝ) := Real.rpow_pos_of_pos ht _
  have hω0 : 0 < ω := (by positivity : 0 < 1/(10*(H : ℝ)^3)).trans_le hω
  have hu : 0 ≤ u := (one_div_pos.mpr htroot).le.trans hlower
  have hgap := ppt_contraction_gap hu hω0 hω1
    (show u' ≤ u/(1+ω)+(0 : ℝ) by simpa only [add_zero] using hcontract)
  have hprod := mul_le_mul hω hlower (one_div_pos.mpr htroot).le hω0.le
  have hsmall : 1/(20*(H : ℝ)^3*t^(1/3 : ℝ)) ≤ ω*u/2 := by
    have hh := div_le_div_of_nonneg_right hprod (by norm_num : (0 : ℝ) ≤ 2)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  linarith only [hgap, hsmall, hfactor, hfactor']

/-- The same gap pays for both normality alignment errors and the
larger padding that also gives the published adjacent-cutoff gap. -/
lemma ppt_paired_gap_of_inverse_cube {u u' v v' δ G : ℝ} {H j : ℕ}
    (hδ : 0 ≤ δ) (hG : 0 < G) (hj : j ≤ H)
    (hsmall : (8*(H : ℝ)+20)*δ < G)
    (hgap : 2*G-δ ≤ u-u')
    (halign : |u-v| ≤ (2*(j : ℝ)+1)*δ)
    (halign' : |u'-v'| ≤ (2*(j : ℝ)+3)*δ) :
    max u' v'+(2*(j : ℝ)+8)*δ < min u v := by
  have hjR : (j : ℝ) ≤ H := by exact_mod_cast hj
  have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hcost : (6*(j : ℝ)+13)*δ < G := by
    apply lt_of_le_of_lt _ hsmall
    exact mul_le_mul_of_nonneg_right (by linarith only [hjR, hH0]) hδ
  apply ppt_paired_gap_of_left_gap halign halign'
  linarith only [hcost, hgap, hG]

/-- Uniform geometric and normality estimates imply the actual paired
grid separation for every retained adjacent coordinate. -/
theorem ppt_local_contracted_grid_separation {A : ℝ} (hA : 0 < A) :
    ∀ᶠ t : ℝ in atTop, ∀ (H j : ℕ) (u u' v v' ω : ℝ),
      1 ≤ H → (H : ℝ) ≤ A*Real.log t → j ≤ H →
      1/t^(1/3 : ℝ) ≤ u →
      1/(10*(H : ℝ)^3) ≤ ω → ω ≤ 1 → u' ≤ u/(1+ω) →
      u-2*((Real.log t)^5/Real.sqrt t) ≤ v → v' ≤ u' →
      ∀ (w w' : ℝ),
        |v-w| ≤ (2*(j : ℝ)+1)*(2*((Real.log t)^5/Real.sqrt t)) →
        |v'-w'| ≤ (2*(j : ℝ)+3)*(2*((Real.log t)^5/Real.sqrt t)) →
        max v' w'+(2*(j : ℝ)+8)*(2*((Real.log t)^5/Real.sqrt t)) < min v w := by
  filter_upwards [ppt_log_dimension_separation hA,
    eventually_gt_atTop (1 : ℝ)] with t hsmall ht
  intro H j u u' v v' ω hH hdim hj hlower hω hω1 hcontract hfactor hfactor'
    w w' halign halign'
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hδ : 0 ≤ 2*((Real.log t)^5/Real.sqrt t) := by
    have hlog : 0 < Real.log t := Real.log_pos ht
    positivity
  have hHr : (0 : ℝ) < H := by exact_mod_cast (zero_lt_one.trans_le hH)
  have hG : 0 < 1/(40*(H : ℝ)^3*t^(1/3 : ℝ)) := by
    exact one_div_pos.mpr (mul_pos (by positivity) (Real.rpow_pos_of_pos ht0 _))
  have hgap := ppt_contracted_factor_gap ht0 hH hlower hω hω1 hcontract hfactor hfactor'
  have hgap' : 2*(1/(40*(H : ℝ)^3*t^(1/3 : ℝ)))-
      2*((Real.log t)^5/Real.sqrt t) ≤ v-v' := by
    convert hgap using 1
    all_goals try with_reducible_and_instances rfl
    ring
  exact ppt_paired_gap_of_inverse_cube hδ hG hj
    (by simpa only [mul_div_assoc] using hsmall H hH hdim) hgap' halign halign'

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTResidualFamily
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Fixed residual families in the PPT pruning argument.  Their members are
actual integers recovered from a common prime product, a small left tail,
and the surviving left prime list.  The counting conclusion retains both
reciprocal totient weights for the subsequent prefix and suffix sums.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma ppt_squarefreeAbove_mono {n : ℕ} {U V : ℝ}
    (hUV : U ≤ V) (hn : SquarefreeAbove n U) : SquarefreeAbove n V := by
  intro p hp hVp
  exact hn p hp (hUV.trans_lt hVp)

/-- The literal pointwise comparison conditions for an already canceled
pair follow from its arithmetic equation and normalized factor bands.
The large-part condition is proved from the actual left head. -/
theorem ppt_normalized_pair_conditions : ∀ᶠ z : ℝ in atTop,
    ∀ (b D r : ℕ) (S : ℝ) (ν μ : ℕ → ℝ) (t : ShiftedPair b),
      ∀ hb : 0 < b,
      0 < B z → 1 < S → 0 ≤ B S → S ≤ z →
      (∀ i, IsNormalPrime S (t.left i)) →
      (∀ i, IsNormalPrime S (t.right i)) →
      (∀ i, 3 ≤ t.left i) → (∀ i, 3 ≤ t.right i) →
      (∀ i, t.left i ≠ t.right i) →
      0 < t.remainder → D*shiftedProduct t.left = t.remainder*shiftedProduct t.right →
      ((D*shiftedProduct t.left : ℕ) : ℝ) ≤ z/r →
      SquarefreeAbove (D*shiftedProduct t.left) (comparisonCutoffs z ν b) →
      (largestPrimeFactor t.remainder : ℝ) ≤ comparisonCutoffs z ν b →
      (∀ i : Fin b,
        μ i ≤ B (largestPrimeFactor (t.left i-1))/B z ∧
        B (largestPrimeFactor (t.left i-1))/B z ≤ ν i ∧
        μ i ≤ B (largestPrimeFactor (t.right i-1))/B z ∧
        B (largestPrimeFactor (t.right i-1))/B z ≤ ν i) →
      z^(9/10 : ℝ) ≤ t.left ⟨0,hb⟩ → (t.left ⟨0,hb⟩-1 : ℕ) ≤ z →
      1 ≤ comparisonCutoffs z ν 1 →
      comparisonCutoffs z ν 1 ≤ z^(1/(10*B z)) →
      FordComparisonConditions b z S D r
        (comparisonCutoffs z ν) (comparisonCutoffs z μ) t := by
  filter_upwards [ppt_normal_comparison_large_part] with z hlarge
  intro b D r S ν μ t hb hB hS hBS hSz hp hq hp3 hq3 hne hE heq hsize
    hsq hEs hinterval hhead hpz hY hYpower
  refine ⟨hE, ?_, heq, hsize, hEs, ?_, ?_⟩
  · intro i
    have hpone : (1 : ℝ) < largestPrimeFactor (t.left i-1) := by
      exact_mod_cast one_lt_largestPrimeFactor (show 2 ≤ t.left i-1 by have := hp3 i; omega)
    have hqone : (1 : ℝ) < largestPrimeFactor (t.right i-1) := by
      exact_mod_cast one_lt_largestPrimeFactor (show 2 ≤ t.right i-1 by have := hq3 i; omega)
    have hpi := ppt_normalized_factor_interval hB hpone (hinterval i).1 (hinterval i).2.1
    have hqi := ppt_normalized_factor_interval hB hqone (hinterval i).2.2.1 (hinterval i).2.2.2
    have hsides := squarefree_shifts_of_common_product t (comparisonCutoffs z ν b) heq hsq i
    exact ⟨hp i, hq i, hne i, hpi.1, hpi.2, hqi.1, hqi.2, hsides.1, hsides.2⟩
  · intro hb'
    exact hlarge (t.left ⟨0,hb'⟩) S (comparisonCutoffs z ν 1)
      hS hBS hSz (hp _) hhead hpz hY hYpower
  · exact squarefreeAbove_of_dvd (dvd_mul_left _ _) hsq

/-- The exponent of an already canceled pair is controlled by its
actual embedding in the constructed geometric candidate family. -/
theorem ppt_geometric_pair_exponent {A : ℝ} (hA : 0 < A) :
    ∀ᶠ z : ℝ in atTop,
    ∀ (m n b H : ℕ) (budget c S e w δ : ℝ)
      (t : ShiftedPair b) (v : Fin n → ℝ) (ι : Fin b ↪o Fin n) (ν μ : ℕ → ℝ),
      ∀ hb : 0 < b,
      v ∈ relaxedGeometricFamily m n budget c → (∀ i, 3 ≤ t.left i) →
      (t.left ⟨0,hb⟩-1 : ℕ) ≤ z → (∀ i, v (ι i) = B (t.left i)) →
      1 ≤ H → b ≤ H → m-((ι ⟨0,hb⟩).val+1)+1 ≤ H →
      (H : ℝ) ≤ A*Real.log (B z) →
      0 ≤ δ → δ ≤ 2*((Real.log (B z))^5/Real.sqrt (B z)) →
      e ≤ (2*(b : ℝ)+4)*δ → w ≤ (4*(b : ℝ)+3)*δ → Real.sqrt (B S/B z) ≤ δ →
      (∀ i : Fin b, 0 < i.val → ν i ≤ B (largestPrimeFactor (t.left i-1))/B z+e) →
      (∀ i ∈ Finset.Icc 1 (b-1), ν i-μ i ≤ w) →
      -2+(∑ i ∈ Finset.Icc 1 (b-1), a i*(B (comparisonCutoffs z ν i)/B z))+
        comparisonError b z S (comparisonCutoffs z ν) (comparisonCutoffs z μ) ≤
        -1-(1/(80*A^3))/(Real.log (B z))^3 := by
  filter_upwards [B_tendsto.eventually (ppt_local_head_error_absorbed hA (by norm_num : (0 : ℝ) ≤ 1)),
    B_tendsto.eventually (ppt_grid_error_absorbed_two_mesh hA),
    B_tendsto.eventually (eventually_gt_atTop (1 : ℝ)),
    eventually_ge_atTop (Real.exp 1)] with z hheaderr hgriderr hB hz
  intro m n b H budget c S e w δ t v ι ν μ hb hv hp3 hpz hcoords
    hH hbH hrH hdim hδ hδmax he hw hη hν hwidth
  have hB0 : 0 < B z := zero_lt_one.trans hB
  have hhead : v (ι ⟨0,hb⟩) ≤ B z+1 := by
    rw [hcoords]
    exact prime_coordinate_endpoint_bound (hp3 _) hz hpz
  have hround (i : Fin b) (hi : 0 < i.val) : ν i ≤ v (ι i)/B z+e := by
    have hl : (1 : ℝ) < largestPrimeFactor (t.left i-1) := by
      exact_mod_cast one_lt_largestPrimeFactor (show 2 ≤ t.left i-1 by have := hp3 i; omega)
    have hnat : largestPrimeFactor (t.left i-1) ≤ t.left i :=
      (largestPrimeFactor_le_self (by have := hp3 i; omega)).trans (Nat.sub_le _ _)
    have hmono : B (largestPrimeFactor (t.left i-1)) ≤ B (t.left i) :=
      Real.log_le_log (Real.log_pos hl)
        (Real.log_le_log (zero_lt_one.trans hl) (Nat.cast_le.mpr hnat))
    have hh := div_le_div_of_nonneg_right hmono hB0.le
    rw [← hcoords i] at hh
    apply (hν i hi).trans
    linarith only [hh]
  have hrow := ppt_relaxed_surviving_exponent hv ι hb ν μ hB0 hB0.ne' hhead
    (hheaderr H (m-((ι ⟨0,hb⟩).val+1)) hdim hrH) hround hwidth
    (hgriderr b H (m-((ι ⟨0,hb⟩).val+1)) e w (Real.sqrt (B S/B z)) δ
      hH hbH hrH hdim hδ hδmax he hw hη)
  have hsaving := ppt_residual_inverse_log_saving hA (Real.log_pos hB) hrH hdim
  linarith only [hrow, hsaving]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTFactorLabels
attribute [-instance] _root_.instMeasurableSpace
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

lemma mem_pptPrimeProductFamily {N h n : ℕ} :
    n ∈ pptPrimeProductFamily N h ↔
      ∃ p : Fin h → ℕ, (∀ i, p i ≤ N ∧ (p i).Prime) ∧ n = ∏ i, p i := by
  classical
  simp only [pptPrimeProductFamily, Finset.mem_image, Fintype.mem_piFinset, Nat.mem_primesLE]
  constructor
  · rintro ⟨p, hp, he⟩
    exact ⟨p, hp, he.symm⟩
  · rintro ⟨p, hp, he⟩
    exact ⟨p, hp, he.symm⟩

/-- Each prime sublist of a candidate gives an actual label in this
finite universe, retaining its exact length. -/
lemma ppt_prime_sublist_label {k N : ℕ} (p : Fin k → ℕ) (I : Finset (Fin k))
    (hp : ∀ i, p i ≤ N ∧ (p i).Prime) :
    (∏ i ∈ I, p i) ∈ pptPrimeProductFamily N I.card := by
  classical
  let e : Fin I.card ↪o Fin k := I.orderEmbOfFin rfl
  apply mem_pptPrimeProductFamily.mpr
  refine ⟨p ∘ e, fun i => hp (e i), ?_⟩
  have he : Finset.univ.image e = I := I.image_orderEmbOfFin_univ rfl
  calc
    _ = ∏ i ∈ Finset.univ.image e, p i := by rw [he]
    _ = _ := by
      rw [Finset.prod_image]
      · rfl
      · exact fun i _ j _ hij => e.injective hij

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTTailAlignment
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The right-tail smoothness argument following Ford (5.35).  If the left
tail is smooth, an additional right prime with a large predecessor factor
would force too many normal shifts across the intervening interval.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

theorem ppt_right_tail_smooth {k l D E J : ℕ}
    (p : Fin k → ℕ) (q : Fin l → ℕ) {S U V z ε : ℝ}
    (hS : 1 < S) (hBS : 0 ≤ B S) (hSU : S ≤ U) (hUV : U < V)
    (hD : D ≠ 0) (hE : E ≠ 0)
    (hp : ∀ i, IsNormalPrime S (p i)) (hq : ∀ i, IsNormalPrime S (q i))
    (hqa : Antitone q) (heq : D*shiftedProduct p = E*shiftedProduct q)
    (hDU : (largestPrimeFactor D : ℝ) ≤ U)
    (hEU : (largestPrimeFactor E : ℝ) ≤ U)
    (hleft : ∀ i : Fin k, J ≤ i.val → (largestPrimeFactor (p i-1) : ℝ) ≤ U)
    (hqz : ∀ i : Fin l, (q i-1 : ℕ) ≤ z)
    (hε : Real.sqrt (B S*B z) ≤ ε)
    (hgap : (2*(J : ℝ)+1)*ε < B V-B U) :
    ∀ i : Fin l, J ≤ i.val → (largestPrimeFactor (q i-1) : ℝ) ≤ V := by
  intro i hJi
  by_contra hbad
  have hVT : V < (largestPrimeFactor (q i-1) : ℝ) := lt_of_not_ge hbad
  let T : ℝ := largestPrimeFactor (q i-1)
  have hV : 1 < V := (hS.trans_le hSU).trans hUV
  have hT : 1 < T := hV.trans hVT
  have hqi : 1 ≤ q i-1 := by have := (hq i).1.two_le; omega
  have hTpred : T ≤ (q i-1 : ℕ) := Nat.cast_le.mpr (largestPrimeFactor_le_self hqi)
  have hTz : T ≤ z := hTpred.trans (hqz i)
  have hBTz : B T ≤ B z := Real.log_le_log (Real.log_pos hT)
    (Real.log_le_log (zero_lt_one.trans hT) hTz)
  have hBVT : B V ≤ B T := Real.log_le_log (Real.log_pos hV)
    (Real.log_le_log (zero_lt_one.trans hV) hVT.le)
  have hJT : J < l := hJi.trans_lt i.isLt
  let j : Fin l := ⟨J, hJT⟩
  have hqT (r : Fin l) (hrj : r ≤ j) : T ≤ (q r-1 : ℕ) := by
    have hrJ : r.val ≤ J := hrj
    have hri : r ≤ i := hrJ.trans hJi
    exact hTpred.trans (Nat.cast_le.mpr (Nat.sub_le_sub_right (hqa hri) 1))
  have hεT : Real.sqrt (B S*B T) ≤ ε :=
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hBTz hBS)).trans hε
  have hbound := ppt_unequal_normality_gap q p j hS hBS hE hD hq hp heq.symm
    hEU hDU hSU (hUV.trans hVT) hεT hqT hleft
  change B T-B U ≤ (2*(J : ℝ)+1)*ε at hbound
  linarith

/-- The actual remaining shifted product, not an additional smoothness
hypothesis for an unrelated integer. -/
lemma ppt_right_low_factor_smooth {l E J : ℕ} (q : Fin l → ℕ) {V : ℝ}
    (hV : 1 ≤ V) (hE : (largestPrimeFactor E : ℝ) ≤ V)
    (htail : ∀ i : Fin l, J ≤ i.val → (largestPrimeFactor (q i-1) : ℝ) ≤ V) :
    (largestPrimeFactor (pptRightLowFactor q E J) : ℝ) ≤ V := by
  have hnat : largestPrimeFactor (pptRightLowFactor q E J) ≤ ⌊V⌋₊ := by
    apply largestPrimeFactor_mul_le (Nat.le_floor hE)
    apply largestPrimeFactor_prod_le _ _ (Nat.le_floor (by simpa only [Nat.cast_one] using hV))
    intro i hi
    exact Nat.le_floor (htail i (Finset.mem_filter.mp hi).2)
  exact (Nat.cast_le.mpr hnat).trans (Nat.floor_le (zero_le_one.trans hV))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTPrefixEquation
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Truncate the two actual prime lists to the same high-prefix length.  The
left residual multiplier is exactly the seed times the totient of the
removed prime tail; the right multiplier is the smooth factor already
estimated in `PPTTailAlignment`.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma ppt_prefix_product {k J : ℕ} (f : Fin k → ℕ) (hJ : J ≤ k) :
    (∏ i : Fin J, f (i.castLE hJ)) =
      ∏ i ∈ Finset.univ.filter (fun i : Fin k => i.val < J), f i := by
  apply Finset.prod_bij (fun i _ => i.castLE hJ)
  · intro i _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.isLt⟩
  · intro i _ j _ he
    exact Fin.ext (congrArg (fun v : Fin k => v.val) he)
  · intro j hj
    have hjJ := (Finset.mem_filter.mp hj).2
    exact ⟨⟨j.val, hjJ⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro i _
    rfl

lemma ppt_prime_prefix_tail_split {k J : ℕ} (p : Fin k → ℕ) (hJ : J ≤ k) :
    pptPrimeTailProduct p J * (∏ i, pptPrimePrefix p hJ i) = ∏ i, p i := by
  rw [show (∏ i, pptPrimePrefix p hJ i) =
      ∏ i ∈ Finset.univ.filter (fun i : Fin k => i.val < J), p i from
    ppt_prefix_product p hJ]
  have he := Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun i : Fin k => i.val < J) p
  simp only [not_lt] at he
  simpa only [pptPrimeTailProduct, mul_comm] using he

lemma ppt_shifted_prefix_tail_split {k J : ℕ} (p : Fin k → ℕ) (hJ : J ≤ k) :
    (∏ i ∈ Finset.univ.filter (fun i : Fin k => J ≤ i.val), (p i-1)) *
      shiftedProduct (pptPrimePrefix p hJ) = shiftedProduct p := by
  have he := ppt_prime_prefix_tail_split (fun i => p i-1) hJ
  exact he

lemma ppt_prime_tail_totient {k J : ℕ} (p : Fin k → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    (pptPrimeTailProduct p J).totient =
      ∏ i ∈ Finset.univ.filter (fun i : Fin k => J ≤ i.val), (p i-1) := by
  let I := Finset.univ.filter (fun i : Fin k => J ≤ i.val)
  have hprime : ∀ r ∈ I.image p, r.Prime := by
    intro r hr
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
    exact hp i
  have hh := TotientFibers.totient_prime_prod hprime
  rw [Finset.prod_image (fun i _ j _ he => hinj he),
    Finset.prod_image (fun i _ j _ he => hinj he)] at hh
  exact hh

/-- The fixed left tail enters the scalar `D`, exactly as required by
the available `l=0` specialization of Ford's comparison lemma. -/
theorem ppt_equal_prefix_equation {k l J d E : ℕ}
    (p : Fin k → ℕ) (q : Fin l → ℕ) (hJp : J ≤ k) (hJq : J ≤ l)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (heq : d*shiftedProduct p = E*shiftedProduct q) :
    (d*(pptPrimeTailProduct p J).totient)*shiftedProduct (pptPrimePrefix p hJp) =
      pptRightLowFactor q E J*shiftedProduct (pptPrimePrefix q hJq) := by
  rw [ppt_prime_tail_totient p hp hinj]
  calc
    _ = d*((∏ i ∈ Finset.univ.filter (fun i : Fin k => J ≤ i.val), (p i-1))*
      shiftedProduct (pptPrimePrefix p hJp)) := by ring
    _ = d*shiftedProduct p := by rw [ppt_shifted_prefix_tail_split p hJp]
    _ = E*shiftedProduct q := heq
    _ = E*((∏ i ∈ Finset.univ.filter (fun i : Fin l => J ≤ i.val), (q i-1))*
      shiftedProduct (pptPrimePrefix q hJq)) := by rw [ppt_shifted_prefix_tail_split q hJq]
    _ = _ := by unfold pptRightLowFactor; ring

lemma ppt_prime_prefix_strictAnti {k J : ℕ} (p : Fin k → ℕ) (hJ : J ≤ k)
    (hp : StrictAnti p) : StrictAnti (pptPrimePrefix p hJ) := by
  intro i j hij
  exact hp (show i.castLE hJ < j.castLE hJ from hij)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTActualResidual
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual residual data after choosing the terminal prefix and canceling
matching coordinates. This keeps the candidate integer, both finite
factor labels, and the exact shifted-product equation together.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma ppt_tail_list_product {k : ℕ} (p : Fin k → ℕ) (J : ℕ) :
    (∏ i, pptTailList p J i) = pptPrimeTailProduct p J := by
  classical
  let e := (pptTailIndices k J).orderEmbOfFin rfl
  have he : Finset.univ.image e = pptTailIndices k J :=
    (pptTailIndices k J).image_orderEmbOfFin_univ rfl
  calc
    _ = ∏ i ∈ Finset.univ.image e, p i := by
      rw [Finset.prod_image]
      · rfl
      · exact fun i _ j _ hij => e.injective hij
    _ = _ := by rw [he]; rfl

lemma ppt_tail_list_mem {k : ℕ} (p : Fin k → ℕ) (J : ℕ)
    (i : Fin (pptTailIndices k J).card) :
    ∃ j : Fin k, J ≤ j.val ∧ pptTailList p J i = p j := by
  let e := (pptTailIndices k J).orderEmbOfFin rfl
  exact ⟨e i, (Finset.mem_filter.mp
    ((pptTailIndices k J).orderEmbOfFin_mem rfl i)).2, rfl⟩

/-- The residual pair and both factor labels are built from the actual
lists. The first prime survives cancellation, and the target size is
divided by the totient of precisely the canceled product. -/
theorem ppt_actual_truncated_block {k l J d n E N : ℕ}
    (p : Fin k → ℕ) (q : Fin l → ℕ) (hJp : J ≤ k) (hJq : J ≤ l)
    (hJ : 0 < J) {W V z K : ℝ}
    (hp : ∀ i, IsNormalPrime W (p i)) (hq : ∀ i, IsNormalPrime W (q i))
    (hpa : StrictAnti p) (hqa : StrictAnti q)
    (hp3 : ∀ i, 3 ≤ p i) (hq3 : ∀ i, 3 ≤ q i)
    (hfirst : p ⟨0,hJ.trans_le hJp⟩ ≠ q ⟨0,hJ.trans_le hJq⟩)
    (hn : n = ∏ i, p i)
    (heq : d*shiftedProduct p = E*shiftedProduct q)
    (hE : 0 < E) (hV : 1 ≤ V) (hEV : (largestPrimeFactor E : ℝ) ≤ V)
    (hptail : ∀ i : Fin k, J ≤ i.val → (largestPrimeFactor (p i-1) : ℝ) ≤ V)
    (hqtail : ∀ i : Fin l, J ≤ i.val → (largestPrimeFactor (q i-1) : ℝ) ≤ V)
    (hsize : ((d*n.totient : ℕ) : ℝ) ≤ z)
    (hsq : SquarefreeAbove (d*n.totient) K)
    (hpN : ∀ i, p i ≤ N) :
    ∃ (b h s c a : ℕ) (t : ShiftedPair b) (tail : Fin h → ℕ),
      0 < b ∧ b ≤ J ∧ h ≤ k ∧ s ≤ J ∧
      0 < c ∧ 0 < a ∧ n = c*a*∏ i, t.left i ∧
      c ∈ pptPrimeProductFamily N s ∧ a ∈ pptPrimeProductFamily N h ∧
      a = ∏ i, tail i ∧ Function.Injective tail ∧
      (∀ i, IsNormalPrime W (tail i) ∧ (largestPrimeFactor (tail i-1) : ℝ) ≤ V) ∧
      (∀ i, ∃ j : Fin k, J ≤ j.val ∧ tail i = p j) ∧
      (∀ i, IsNormalPrime W (t.left i) ∧ IsNormalPrime W (t.right i) ∧
        3 ≤ t.left i ∧ 3 ≤ t.right i ∧ t.left i ≠ t.right i) ∧
      StrictAnti t.left ∧ StrictAnti t.right ∧
      0 < t.remainder ∧ (largestPrimeFactor t.remainder : ℝ) ≤ V ∧
      (d*a.totient)*shiftedProduct t.left = t.remainder*shiftedProduct t.right ∧
      (((d*a.totient)*shiftedProduct t.left : ℕ) : ℝ) ≤ z/c.totient ∧
      SquarefreeAbove ((d*a.totient)*shiftedProduct t.left) K ∧
      c = pptCanceledPrimeProduct (pptPrimePrefix p hJp) (pptPrimePrefix q hJq) ∧
      (∃ e : Fin b ↪o Fin J, ∀ i,
        t.left i = p ((e i).castLE hJp) ∧ t.right i = q ((e i).castLE hJq)) ∧
      (∃ ι : Fin b ↪o Fin k, ∀ i, t.left i = p (ι i)) ∧
      ∃ hb : 0 < b, t.left ⟨0,hb⟩ = p ⟨0,hJ.trans_le hJp⟩ := by
  classical
  let P := pptPrimePrefix p hJp
  let Q := pptPrimePrefix q hJq
  let c := pptCanceledPrimeProduct P Q
  let a := pptPrimeTailProduct p J
  let R := pptRightLowFactor q E J
  let b := (pptUnequalCoordinates P Q).card
  let s := (pptEqualCoordinates P Q).card
  let h := (pptTailIndices k J).card
  let t : ShiftedPair b := pptCanceledPair P Q R
  have hP (i : Fin J) : IsNormalPrime W (P i) := hp _
  have hQ (i : Fin J) : IsNormalPrime W (Q i) := hq _
  have hPa : StrictAnti P := ppt_prime_prefix_strictAnti p hJp hpa
  have hQa : StrictAnti Q := ppt_prime_prefix_strictAnti q hJq hqa
  have hPQ : P ⟨0,hJ⟩ ≠ Q ⟨0,hJ⟩ := hfirst
  obtain ⟨hb, hzero⟩ := ppt_coordinate_first_survives hJ P Q hPQ
  have hprefixeq : (d*a.totient)*shiftedProduct P = R*shiftedProduct Q :=
    ppt_equal_prefix_equation p q hJp hJq (fun i => (hp i).1) hpa.injective heq
  have hprefixvalue : (d*a.totient)*shiftedProduct P = d*n.totient := by
    rw [hn, ppt_totient_primeProduct p (fun i => (hp i).1) hpa.injective]
    dsimp only [a]
    rw [ppt_prime_tail_totient p (fun i => (hp i).1) hpa.injective]
    have hh := ppt_shifted_prefix_tail_split p hJp
    dsimp only [P]
    rw [mul_assoc, hh]
  have hprefixsize : (((d*a.totient)*shiftedProduct P : ℕ) : ℝ) ≤ z := by
    rw [hprefixvalue]
    exact hsize
  have hshiftdiv : shiftedProduct t.left ∣ shiftedProduct P := by
    rw [← ppt_canceled_totient_split P Q (fun i => (hP i).1) hPa.injective]
    exact dvd_mul_left _ _
  have htargetdiv : (d*a.totient)*shiftedProduct t.left ∣ d*n.totient := by
    rw [← hprefixvalue]
    exact Nat.mul_dvd_mul_left _ hshiftdiv
  have hR : 0 < R := by
    dsimp only [R, pptRightLowFactor]
    apply Nat.mul_pos hE
    apply Finset.prod_pos
    intro i _
    exact Nat.sub_pos_of_lt (hq i).1.one_lt
  have htailreal : a = ∏ i, pptTailList p J i := (ppt_tail_list_product p J).symm
  have htailinj : Function.Injective (pptTailList p J) :=
    hpa.injective.comp ((pptTailIndices k J).orderEmbOfFin rfl).injective
  have hreal : n = c*a*∏ i, t.left i := by
    rw [hn, ← ppt_prime_prefix_tail_split p hJp,
      ← ppt_canceled_prime_product_split P Q]
    dsimp only [a, c, t, pptCanceledPair, Function.comp_apply]
    ring
  refine ⟨b, h, s, c, a, t, pptTailList p J, hb, ?_, ?_, ?_,
    ppt_canceled_prime_product_pos P Q (fun i => (hP i).1), ?_, hreal,
    ?_, ?_, htailreal, htailinj, ?_, ppt_tail_list_mem p J, ?_, ?_, ?_, hR, ?_, ?_, ?_,
    squarefreeAbove_of_dvd htargetdiv hsq, rfl, ?_, ?_, ?_⟩
  · exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)
  · exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)
  · exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)
  · apply Finset.prod_pos
    intro i _
    exact (hp i).1.pos
  · exact ppt_prime_sublist_label P (pptEqualCoordinates P Q)
      (fun i => ⟨hpN _, (hP i).1⟩)
  · exact ppt_prime_sublist_label p (pptTailIndices k J)
      (fun i => ⟨hpN i, (hp i).1⟩)
  · intro i
    obtain ⟨j, hj, he⟩ := ppt_tail_list_mem p J i
    rw [he]
    exact ⟨hp j, hptail j hj⟩
  · intro i
    exact ⟨hP _, hQ _, hp3 _, hq3 _, ppt_surviving_coordinates_unequal P Q i⟩
  · exact (ppt_surviving_coordinates_strictAnti P Q hPa hQa).1
  · exact (ppt_surviving_coordinates_strictAnti P Q hPa hQa).2
  · exact ppt_right_low_factor_smooth q hV hEV hqtail
  · exact ppt_cancel_matching_coordinates P Q (fun i => (hP i).1) hprefixeq
  · exact ppt_canceled_comparison_size P Q (fun i => (hP i).1) hPa.injective hprefixsize
  · exact ⟨pptCoordinateEmbedding P Q, fun _ => ⟨rfl,rfl⟩⟩
  · exact ⟨(pptCoordinateEmbedding P Q).trans (Fin.castLEOrderEmb hJp), fun _ => rfl⟩
  · refine ⟨hb, ?_⟩
    change P (pptCoordinateEmbedding P Q ⟨0,hb⟩) = _
    rw [hzero]
    rfl

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

lemma ppt_residual_label_mem {N H b h s c a j : ℕ} {δ : ℝ} {g : Fin b → ℕ}
    (hb : b ≤ H) (hh : h ≤ H) (hs : s ≤ H) (hj : j ≤ H)
    (hg : g ∈ collisionGridFamilies δ b)
    (ha : a ∈ pptPrimeProductFamily N h) (hc : c ∈ pptPrimeProductFamily N s) :
    pptResidualLabel b h s c a j g ∈ pptResidualLabels N H δ := by
  classical
  simp only [pptResidualLabel, pptResidualLabels, Finset.product_eq_sprod,
    Finset.mem_sigma, Finset.mem_product,
    Finset.mem_range, Nat.lt_succ_iff]
  exact ⟨hb, hg, hj, hh, ha, hs, hc⟩

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTHeadEdge
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
A single lower endpoint for all leading prime factors in a local PPT
comparison block.  It depends only on the comparison scale, so the
finite grid count does not require any continuously varying labels.
-/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

/-- Every normal large head lies above the same normalized endpoint.
The hypotheses are local to `z`, including the normality cutoff. -/
theorem ppt_normal_head_uniform_edge : ∀ᶠ z : ℝ in atTop,
    ∀ (p : ℕ) (S : ℝ), 1 < S → 0 ≤ B S → S ≤ z →
      IsNormalPrime S p → z^(9/10 : ℝ) ≤ p → (p-1 : ℕ) ≤ z →
      pptUniformHeadEdge (B z) ≤ B (largestPrimeFactor (p-1))/B z ∧
      B (largestPrimeFactor (p-1))/B z ≤ 1 := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ)),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 9/10)).eventually
      (eventually_gt_atTop (2 : ℝ))] with z hz hB hpow
  intro p S hS hBS hSz hp hhead hsize
  have hp3 : 3 ≤ p := by
    have hh : (2 : ℝ) < p := hpow.trans_le hhead
    exact_mod_cast hh
  have hp1 : (1 : ℝ) < (p-1 : ℕ) := by
    exact_mod_cast (show 1 < p-1 by omega)
  have hpred : B (p-1 : ℕ) ≤ B z :=
    Real.log_le_log (Real.log_pos hp1)
      (Real.log_le_log (zero_lt_one.trans hp1) hsize)
  have hBSz : B S ≤ B z := Real.log_le_log (Real.log_pos hS)
    (Real.log_le_log (zero_lt_one.trans hS) hSz)
  have hband := normal_prime_largest_band hp hp3 hS hBS hBSz hB hpred
    (le_refl (B p)) (le_refl (B p))
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos (zero_lt_one.trans hz) _) hhead
  rw [Real.log_rpow (zero_lt_one.trans hz)] at hlog
  have hdouble := Real.log_le_log
    (mul_pos (by norm_num : (0 : ℝ) < 9/10) (Real.log_pos hz)) hlog
  rw [Real.log_mul (by norm_num : (9/10 : ℝ) ≠ 0) (Real.log_pos hz).ne'] at hdouble
  change Real.log (9/10 : ℝ)+B z ≤ B p at hdouble
  have hlogfrac : -1 ≤ Real.log (9/10 : ℝ) := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 9/10)
    norm_num only [inv_div, div_self] at hh
    linarith only [hh]
  have hlower : B z-(2+Real.log (3*B z)) ≤ B (largestPrimeFactor (p-1)) := by
    linarith only [hband.1, hdouble, hlogfrac]
  constructor
  · apply (le_div_iff₀ hB).mpr
    unfold pptUniformHeadEdge
    calc
      (1-(2+Real.log (3*B z))/B z)*B z = B z-(2+Real.log (3*B z)) := by
        rw [sub_mul, one_mul, div_mul_cancel₀ _ hB.ne']
      _ ≤ _ := hlower
  · apply (div_le_one hB).mpr
    have hlp : (1 : ℝ) < largestPrimeFactor (p-1) := by
      exact_mod_cast one_lt_largestPrimeFactor (show 2 ≤ p-1 by omega)
    apply Real.log_le_log (Real.log_pos hlp)
    apply Real.log_le_log (zero_lt_one.trans hlp)
    exact (Nat.cast_le.mpr (largestPrimeFactor_le_self (by omega))).trans hsize

lemma ppt_uniform_head_edge_lt_one {t : ℝ} (ht : 1 ≤ t) :
    pptUniformHeadEdge t < 1 := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hlog : 0 ≤ Real.log (3*t) := Real.log_nonneg (by linarith)
  have herror : 0 < (2+Real.log (3*t))/t := div_pos (by linarith) ht0
  unfold pptUniformHeadEdge
  linarith only [herror]

/-- Only the left head needs a large-prime size estimate.  Alignment
places both heads above one common endpoint without imposing that size
estimate separately on the arbitrary right preimage. -/
lemma ppt_aligned_heads_uniform_edge {t u v η : ℝ}
    (ht : 1 ≤ t) (hu : pptUniformHeadEdge t ≤ u) (halign : |u-v| ≤ η) :
    pptUniformHeadEdge t-η ≤ min u v ∧ pptUniformHeadEdge t-η < 1 := by
  have hη : 0 ≤ η := (abs_nonneg _).trans halign
  constructor
  · exact le_min (by linarith only [hu, hη])
      (by linarith only [hu, (abs_le.mp halign).2])
  · have hh := ppt_uniform_head_edge_lt_one ht
    linarith only [hh, hη]

/-- The uniform head loss is smaller than every fixed inverse-log-cube
margin, so the same lower edge works for every pair in a grid class. -/
theorem ppt_first_cutoff_below_uniform_head {γ : ℝ} (hγ : 0 < γ) :
    ∀ᶠ t : ℝ in atTop, ∀ ν : ℝ,
      ν ≤ 1-γ/(Real.log t)^3 → ν < pptUniformHeadEdge t := by
  have h₃ : Tendsto (fun t : ℝ => (Real.log t)^3/t) atTop (𝓝 0) :=
    Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero
  have h₄ : Tendsto (fun t : ℝ => (Real.log t)^4/t) atTop (𝓝 0) :=
    Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero
  have hsum : Tendsto (fun t : ℝ =>
      (2+Real.log 3)*((Real.log t)^3/t)+(Real.log t)^4/t) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add] using (h₃.const_mul (2+Real.log 3)).add h₄
  filter_upwards [hsum.eventually (eventually_lt_nhds hγ),
    eventually_gt_atTop (1 : ℝ)] with t hsmall ht
  intro ν hν
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hlog : 0 < Real.log t := Real.log_pos ht
  have heq : (2+Real.log (3*t))*(Real.log t)^3/t =
      (2+Real.log 3)*((Real.log t)^3/t)+(Real.log t)^4/t := by
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) ht0.ne']
    ring
  rw [← heq] at hsmall
  have hm := (div_lt_iff₀ ht0).mp hsmall
  have hloss : (2+Real.log (3*t))/t < γ/(Real.log t)^3 :=
    (div_lt_div_iff₀ ht0 (pow_pos hlog 3)).mpr hm
  unfold pptUniformHeadEdge
  linarith only [hν, hloss]

/-- The same head endpoint still lies above the first cutoff after the
uniform alignment allowance used by the doubled PPT mesh. -/
theorem ppt_first_cutoff_below_aligned_head {γ : ℝ} (hγ : 0 < γ) :
    ∀ᶠ t : ℝ in atTop, ∀ ν η : ℝ,
      ν ≤ 1-γ/(Real.log t)^3 →
      η ≤ 2*((Real.log t)^5/Real.sqrt t) →
      ν < pptUniformHeadEdge t-η := by
  have hlim : Tendsto (fun t : ℝ => 2*((Real.log t)^8/Real.sqrt t))
      atTop (𝓝 0) := by
    have hh : Tendsto (fun t : ℝ => (Real.log t)^8/Real.sqrt t)
        atTop (𝓝 0) := by
      simpa only [Real.sqrt_eq_rpow, Real.rpow_natCast] using
        (isLittleO_log_rpow_rpow_atTop (8 : ℕ)
          (show (0 : ℝ) < 1/2 by norm_num)).tendsto_div_nhds_zero
    simpa only [mul_zero] using hh.const_mul 2
  filter_upwards [ppt_first_cutoff_below_uniform_head (show 0 < γ/2 by positivity),
    hlim.eventually (eventually_lt_nhds (show (0 : ℝ) < γ/2 by positivity)),
    eventually_gt_atTop (1 : ℝ)] with t hhead hsmall ht
  intro ν η hν hη
  have hlog : 0 < Real.log t := Real.log_pos ht
  have hhead' := hhead (1-(γ/2)/(Real.log t)^3) le_rfl
  have hmesh : 2*((Real.log t)^5/Real.sqrt t) < (γ/2)/(Real.log t)^3 := by
    apply (lt_div_iff₀ (pow_pos hlog 3)).mpr
    convert hsmall using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hη' := hη.trans_lt hmesh
  have he : γ/(Real.log t)^3 = (γ/2)/(Real.log t)^3+(γ/2)/(Real.log t)^3 := by
    ring
  rw [he] at hν
  linarith only [hν, hhead', hη']

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTPreimageSplit
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The actual low/high factorization of a chosen preimage in the PPT
construction.  Large square factors have already been excluded; the high
factor therefore has a strictly decreasing prime list.  No conclusion
about a mismatch with a second prime list is asserted here.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

private lemma ppt_partAbove_eq_partBetween (n : ℕ) (S : ℝ) :
    partAbove n S = partBetween n S n := by
  unfold partAbove partBetween
  congr 1
  apply List.filter_congr
  intro p hp
  have hpn : (p : ℝ) ≤ n := Nat.cast_le.mpr (Nat.le_of_mem_primeFactorsList hp)
  simp only [hpn, and_true]

lemma ppt_partAbove_pos (n : ℕ) (S : ℝ) : 0 < partAbove n S := by
  rw [ppt_partAbove_eq_partBetween]
  exact partBetween_pos n S n

lemma ppt_partAbove_dvd {n : ℕ} (hn : 0 < n) (S : ℝ) : partAbove n S ∣ n := by
  rw [ppt_partAbove_eq_partBetween]
  exact partBetween_dvd hn.ne' S n

lemma ppt_partAbove_prime_gt {n p : ℕ} {S : ℝ}
    (hp : p.Prime) (hpn : p ∣ partAbove n S) : S < (p : ℝ) := by
  have hm := (Nat.mem_primeFactorsList_iff_dvd (ppt_partAbove_pos n S).ne' hp).mpr hpn
  rw [ppt_partAbove_eq_partBetween] at hm
  have hf := (partBetween_factors n S n).mem_iff.mpr hm
  exact (of_decide_eq_true (List.mem_filter.mp hf).2).1

lemma ppt_partBelow_prime_le {n p : ℕ} {S : ℝ}
    (hp : p.Prime) (hpn : p ∣ partBelow n S) : (p : ℝ) ≤ S := by
  have hm := (Nat.mem_primeFactorsList_iff_dvd (partBelow_pos n S).ne' hp).mpr hpn
  have hf := (partBelow_factors n S).mem_iff.mpr hm
  exact of_decide_eq_true (List.mem_filter.mp hf).2

lemma ppt_low_high_coprime (n : ℕ) (S : ℝ) :
    (partBelow n S).Coprime (partAbove n S) := by
  apply Nat.coprime_of_dvd'
  intro p hp hlo hhi
  exact False.elim ((not_lt_of_ge (ppt_partBelow_prime_le hp hlo))
    (ppt_partAbove_prime_gt hp hhi))

lemma ppt_low_totient_smooth (n : ℕ) {S : ℝ} (hS : 1 ≤ S) :
    (largestPrimeFactor (partBelow n S).totient : ℝ) ≤ S := by
  have hl : largestPrimeFactor (partBelow n S) ≤ ⌊S⌋₊ := by
    apply largestPrimeFactor_le_of_prime_divisors
      (Nat.le_floor (by simpa only [Nat.cast_one] using hS))
    intro p hp hpn _
    exact Nat.le_floor (ppt_partBelow_prime_le hp hpn)
  exact (Nat.cast_le.mpr ((largestPrimeFactor_totient_le _).trans hl)).trans
    (Nat.floor_le (zero_le_one.trans hS))

lemma ppt_high_squarefree {n : ℕ} (hn : 0 < n) {S : ℝ}
    (hsq : SquarefreeAbove n S) : Squarefree (partAbove n S) := by
  rw [ppt_partAbove_eq_partBetween]
  exact partBetween_squarefree hn.ne' hsq

/-- The residual low totient and the ordered high primes give the exact
equation used for unequal-list alignment. Normality is inherited from the
actual preimage, and all high primes are strictly above the cutoff. -/
theorem ppt_preimage_prime_split_full {n : ℕ} {S : ℝ} (hn : 0 < n) (hS : 1 ≤ S)
    (hsq : SquarefreeAbove n S)
    (hnormal : ∀ p : ℕ, p.Prime → p ∣ n → IsNormalPrime S p) :
    ∃ (h : ℕ) (p : Fin h → ℕ) (s : ℕ),
      0 < s ∧ n = s*∏ i, p i ∧ s.Coprime (∏ i, p i) ∧
      (largestPrimeFactor s.totient : ℝ) ≤ S ∧ StrictAnti p ∧
      (∀ i, IsNormalPrime S (p i) ∧ S < (p i : ℝ)) ∧
      n.totient = s.totient*shiftedProduct p ∧ s = partBelow n S := by
  classical
  let Q := (partAbove n S).primeFactors
  let e : Fin Q.card ↪o ℕ := Q.orderEmbOfFin rfl
  let p : Fin Q.card → ℕ := fun i => e i.rev
  have hpQ (i : Fin Q.card) : p i ∈ Q := Q.orderEmbOfFin_mem rfl i.rev
  have hpinj : Function.Injective p := e.injective.comp Fin.rev_injective
  have hanti : StrictAnti p := by
    intro i j hij
    exact e.strictMono (Fin.rev_lt_rev.mpr hij)
  have himage : Finset.univ.image p = Q := by
    ext r
    constructor
    · intro hr
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
      exact hpQ i
    · intro hr
      have hr' : r ∈ Finset.univ.image e := by
        change r ∈ Finset.univ.image (Q.orderEmbOfFin rfl)
        rwa [Q.image_orderEmbOfFin_univ rfl]
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hr'
      obtain ⟨j, hj⟩ := Fin.rev_surjective i
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, by simpa only [p, hj] using hi⟩
  have hprodQ : (∏ i, p i) = ∏ r ∈ Q, r := by
    conv_rhs => rw [← himage, Finset.prod_image (fun i _ j _ he => hpinj he)]
  have hshiftQ : shiftedProduct p = ∏ r ∈ Q, (r-1) := by
    unfold shiftedProduct
    conv_rhs => rw [← himage, Finset.prod_image (fun i _ j _ he => hpinj he)]
  have hprod : (∏ i, p i) = partAbove n S :=
    hprodQ.trans (Nat.prod_primeFactors_of_squarefree (ppt_high_squarefree hn hsq))
  have hQprime : ∀ r ∈ Q, r.Prime := fun r hr => Nat.prime_of_mem_primeFactors hr
  have hφ : (∏ i, p i).totient = shiftedProduct p := by
    rw [hprodQ, hshiftQ]
    exact TotientFibers.totient_prime_prod hQprime
  have hfactor : n = partBelow n S*∏ i, p i := by
    rw [hprod]
    exact (partBelow_mul_partAbove hn.ne' S).symm
  have hcop : (partBelow n S).Coprime (∏ i, p i) := by
    rw [hprod]
    exact ppt_low_high_coprime n S
  refine ⟨Q.card, p, partBelow n S, partBelow_pos n S, hfactor, hcop,
    ppt_low_totient_smooth n hS, hanti, ?_, ?_, rfl⟩
  · intro i
    have hi := Nat.dvd_of_mem_primeFactors (hpQ i)
    have hip := hQprime (p i) (hpQ i)
    exact ⟨hnormal (p i) hip (hi.trans (ppt_partAbove_dvd hn S)),
      ppt_partAbove_prime_gt hip hi⟩
  · calc
      n.totient = (partBelow n S*∏ i, p i).totient := congrArg Nat.totient hfactor
      _ = (partBelow n S).totient*(∏ i, p i).totient := Nat.totient_mul hcop
      _ = _ := by rw [hφ]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTLeadingMismatch
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Transport the actual largest-prime mismatch into the ordered high-prime
list used in the comparison equation.  Retaining the canonical low part
is essential here: smoothness of its totient alone would not suffice.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma ppt_largestPrimeFactor_mono_dvd {a b : ℕ} (hb : 0 < b) (hab : a ∣ b) :
    largestPrimeFactor a ≤ largestPrimeFactor b := by
  apply largestPrimeFactor_le_of_prime_divisors (le_max_left _ _)
  intro r hr hra _
  exact prime_dvd_le_largest hr hb.ne' (hra.trans hab)

/-- A normal shifted prime dividing the target forces an actual prime
above the low cutoff as soon as its interval has positive normality
mass. -/
lemma ppt_preimage_largest_above_normal_shift {n r : ℕ} {S T : ℝ}
    (hn : 0 < n) (hr : IsNormalPrime S r) (hdiv : r-1 ∣ n.totient)
    (hST : S < T) (hTr : T ≤ (r-1 : ℕ))
    (hgap : Real.sqrt (B S*B T) < B T-B S) :
    S < (largestPrimeFactor n : ℝ) := by
  by_contra hh
  have hnsmall : (largestPrimeFactor n : ℝ) ≤ S := le_of_not_gt hh
  have hshift : (largestPrimeFactor (r-1) : ℝ) ≤ S := by
    exact (Nat.cast_le.mpr ((ppt_largestPrimeFactor_mono_dvd
      (Nat.totient_pos.mpr hn) hdiv).trans (largestPrimeFactor_totient_le n))).trans hnsmall
  have hz := omegaIn_eq_zero_of_largest_le (T := T) hshift
  have hb := (normality_interval_bounds hr le_rfl hST hTr le_rfl).1
  rw [hz, Nat.cast_zero] at hb
  linarith

lemma ppt_actual_preimage_largest_above_of_gap {k d n : ℕ} (p : Fin k → ℕ)
    (j : Fin k) {S T : ℝ} (hn : 0 < n)
    (hp : ∀ i, (p i).Prime) (hpinj : Function.Injective p)
    (hvalue : n.totient = d*(∏ i, p i).totient)
    (hj : IsNormalPrime S (p j)) (hST : S < T) (hTj : T ≤ (p j-1 : ℕ))
    (hgap : Real.sqrt (B S*B T) < B T-B S) :
    S < (largestPrimeFactor n : ℝ) := by
  have hdiv : p j-1 ∣ n.totient := by
    rw [hvalue, ppt_totient_primeProduct p hp hpinj]
    exact (Finset.dvd_prod_of_mem (fun i => p i-1) (Finset.mem_univ j)).trans
      (dvd_mul_left _ _)
  exact ppt_preimage_largest_above_normal_shift hn hj hdiv hST hTj hgap

lemma ppt_partBelow_largest_le (n : ℕ) {S : ℝ} (hS : 1 ≤ S) :
    (largestPrimeFactor (partBelow n S) : ℝ) ≤ S := by
  have hn : largestPrimeFactor (partBelow n S) ≤ ⌊S⌋₊ := by
    apply largestPrimeFactor_le_of_prime_divisors
      (Nat.le_floor (by simpa only [Nat.cast_one] using hS))
    intro p hp hpn _
    exact Nat.le_floor (ppt_partBelow_prime_le hp hpn)
  exact (Nat.cast_le.mpr hn).trans (Nat.floor_le (zero_le_one.trans hS))

lemma ppt_leading_prime_of_split {l n s : ℕ} (hl : 0 < l) (q : Fin l → ℕ)
    {S : ℝ} (hs : 0 < s) (hreal : n = s*∏ i, q i)
    (hsmall : (largestPrimeFactor s : ℝ) ≤ S)
    (hprime : ∀ i, (q i).Prime) (hanti : StrictAnti q)
    (hhigh : S < (q ⟨0, hl⟩ : ℝ)) :
    largestPrimeFactor n = q ⟨0, hl⟩ := by
  have hqpos : 0 < ∏ i, q i := Finset.prod_pos (fun i _ => (hprime i).pos)
  have hn : n ≠ 0 := by rw [hreal]; exact (Nat.mul_pos hs hqpos).ne'
  have hqbound (i : Fin l) : q i ≤ q ⟨0, hl⟩ :=
    hanti.antitone (show (⟨0, hl⟩ : Fin l) ≤ i from Nat.zero_le i.val)
  have hslow : largestPrimeFactor s ≤ q ⟨0, hl⟩ := by
    exact_mod_cast hsmall.trans hhigh.le
  apply le_antisymm
  · rw [hreal]
    apply largestPrimeFactor_mul_le hslow
    apply largestPrimeFactor_prod_le _ _ (hprime ⟨0, hl⟩).one_lt.le
    intro i _
    rw [largestPrimeFactor_prime (hprime i)]
    exact hqbound i
  · apply prime_dvd_le_largest (hprime ⟨0, hl⟩) hn
    rw [hreal]
    exact (Finset.dvd_prod_of_mem q (Finset.mem_univ ⟨0, hl⟩)).trans
      (dvd_mul_left _ _)

/-- An actual preimage with a prime above `S` has a nonempty high list,
and its first entry is its largest prime. -/
theorem ppt_preimage_split_largest {n : ℕ} {S : ℝ} (hn : 0 < n) (hS : 1 ≤ S)
    (hsq : SquarefreeAbove n S)
    (hnormal : ∀ p : ℕ, p.Prime → p ∣ n → IsNormalPrime S p)
    (hlarge : S < (largestPrimeFactor n : ℝ)) :
    ∃ (l : ℕ) (hl : 0 < l) (q : Fin l → ℕ) (s : ℕ),
      0 < s ∧ n = s*∏ i, q i ∧
      (largestPrimeFactor s.totient : ℝ) ≤ S ∧ StrictAnti q ∧
      (∀ i, IsNormalPrime S (q i) ∧ S < (q i : ℝ)) ∧
      n.totient = s.totient*shiftedProduct q ∧
      largestPrimeFactor n = q ⟨0, hl⟩ := by
  obtain ⟨l, q, s, hs, hreal, _, hsmall, hanti, hq, hφ, hslow⟩ :=
    ppt_preimage_prime_split_full hn hS hsq hnormal
  have hsmooth : (largestPrimeFactor s : ℝ) ≤ S := by
    rw [hslow]
    exact ppt_partBelow_largest_le n hS
  have hl : 0 < l := by
    by_contra hh
    have hl0 : l = 0 := Nat.eq_zero_of_not_pos hh
    have hprod : (∏ i, q i) = 1 := by subst l; simp
    have hns : n = s := by simpa only [hprod, mul_one] using hreal
    exact (not_lt_of_ge (hns.symm ▸ hsmooth)) hlarge
  refine ⟨l, hl, q, s, hs, hreal, hsmall, hanti, hq, hφ, ?_⟩
  exact ppt_leading_prime_of_split hl q hs hreal hsmooth
    (fun i => (hq i).1.1) hanti (hq ⟨0, hl⟩).2

/-- The mismatch supplied by the maximal common-prefix argument now
holds for the first displayed high prime in the literal comparison
equation, rather than being an additional assumption about that list. -/
theorem ppt_actual_preimage_leading_mismatch {k d n r : ℕ} (p : Fin k → ℕ)
    {S : ℝ} (hn : 0 < n) (hS : 1 ≤ S)
    (hp : ∀ i, (p i).Prime) (hpinj : Function.Injective p)
    (hvalue : n.totient = d*(∏ i, p i).totient)
    (hsq : SquarefreeAbove n S)
    (hnormal : ∀ q : ℕ, q.Prime → q ∣ n → IsNormalPrime S q)
    (hlarge : S < (largestPrimeFactor n : ℝ))
    (hmismatch : largestPrimeFactor n ≠ r) :
    ∃ (l : ℕ) (hl : 0 < l) (q : Fin l → ℕ) (E : ℕ),
      0 < E ∧ (largestPrimeFactor E : ℝ) ≤ S ∧ StrictAnti q ∧
      (∀ i, IsNormalPrime S (q i) ∧ S < (q i : ℝ)) ∧
      d*shiftedProduct p = E*shiftedProduct q ∧ q ⟨0, hl⟩ ≠ r := by
  obtain ⟨l, hl, q, s, hs, _, hsmall, hanti, hq, hφ, hlead⟩ :=
    ppt_preimage_split_largest hn hS hsq hnormal hlarge
  refine ⟨l, hl, q, s.totient, Nat.totient_pos.mpr hs, hsmall, hanti, hq, ?_, ?_⟩
  · calc
      d*shiftedProduct p = d*(∏ i, p i).totient := by
        rw [ppt_totient_primeProduct p hp hpinj]
      _ = n.totient := hvalue.symm
      _ = s.totient*shiftedProduct q := hφ
  · exact hlead ▸ hmismatch

/-- Version with the high-prime existence derived from the concrete
normality gap on one candidate shift. -/
theorem ppt_actual_preimage_leading_mismatch_of_gap {k d n r : ℕ}
    (p : Fin k → ℕ) (j : Fin k) {S T : ℝ} (hn : 0 < n) (hS : 1 ≤ S)
    (hp : ∀ i, (p i).Prime) (hpinj : Function.Injective p)
    (hvalue : n.totient = d*(∏ i, p i).totient)
    (hsq : SquarefreeAbove n S)
    (hnormal : ∀ q : ℕ, q.Prime → q ∣ n → IsNormalPrime S q)
    (hj : IsNormalPrime S (p j)) (hST : S < T) (hTj : T ≤ (p j-1 : ℕ))
    (hgap : Real.sqrt (B S*B T) < B T-B S)
    (hmismatch : largestPrimeFactor n ≠ r) :
    ∃ (l : ℕ) (hl : 0 < l) (q : Fin l → ℕ) (E : ℕ),
      0 < E ∧ (largestPrimeFactor E : ℝ) ≤ S ∧ StrictAnti q ∧
      (∀ i, IsNormalPrime S (q i) ∧ S < (q i : ℝ)) ∧
      d*shiftedProduct p = E*shiftedProduct q ∧ q ⟨0, hl⟩ ≠ r := by
  exact ppt_actual_preimage_leading_mismatch p hn hS hp hpinj hvalue hsq hnormal
    (ppt_actual_preimage_largest_above_of_gap p j hn hp hpinj hvalue hj hST hTj hgap)
    hmismatch

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTPreimageTerminal
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Match the chosen terminal prefix to the actual high-prime preimage list. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

/-- The unequal-list normality estimate gives every needed right index
above the middle cutoff, while the right tail is smooth below it. The
right list and first mismatch come from the actual preimage. -/
theorem ppt_preimage_terminal_prefix {k J d F : ℕ}
    (p : Fin k → ℕ) (hJ : 0 < J) (hJk : J ≤ k)
    {S U V T z ε ε' : ℝ}
    (hd : 0 < d) (hF : 0 < F)
    (hS : 2 ≤ S) (hBS : 0 ≤ B S)
    (hSU : S ≤ U) (hUV : U < V) (hVT : V < T)
    (hp : ∀ i, IsNormalPrime S (p i)) (hpa : StrictAnti p)
    (hvalue : F.totient = d*(∏ i, p i).totient)
    (hDS : (largestPrimeFactor d : ℝ) ≤ S)
    (hsq : SquarefreeAbove F S)
    (hnormal : ∀ q : ℕ, q.Prime → q ∣ F → IsNormalPrime S q)
    (hmismatch : largestPrimeFactor F ≠ p ⟨0,by omega⟩)
    (hlast : T ≤ (p ⟨J-1,by omega⟩-1 : ℕ))
    (hlow : ∀ i : Fin k, J ≤ i.val → (largestPrimeFactor (p i-1) : ℝ) ≤ U)
    (hsize : (F.totient : ℝ) ≤ z)
    (hε : Real.sqrt (B S*B T) ≤ ε)
    (hε' : Real.sqrt (B S*B z) ≤ ε')
    (hindexgap : (2*((J-1 : ℕ) : ℝ)+1)*ε < B T-B V)
    (htailgap : (2*(J : ℝ)+1)*ε' < B V-B U) :
    ∃ (l : ℕ) (q : Fin l → ℕ) (E : ℕ) (hJl : J ≤ l),
      0 < E ∧ (largestPrimeFactor E : ℝ) ≤ S ∧ StrictAnti q ∧
      (∀ i, IsNormalPrime S (q i) ∧ 3 ≤ q i) ∧
      d*shiftedProduct p = E*shiftedProduct q ∧
      p ⟨0,by omega⟩ ≠ q ⟨0,by omega⟩ ∧
      (∀ i : Fin l, i.val < J → V < (q i-1 : ℕ)) ∧
      (∀ i : Fin l, J ≤ i.val → (largestPrimeFactor (q i-1) : ℝ) ≤ V) ∧
      (∀ i : Fin l, (q i-1 : ℕ) ≤ z) := by
  have hS1 : 1 < S := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hS
  have hSV : S ≤ V := hSU.trans hUV.le
  have hST : S < T := hSV.trans_lt hVT
  have hBV : B S ≤ B V := Real.log_le_log (Real.log_pos hS1)
    (Real.log_le_log (zero_lt_one.trans hS1) hSV)
  have hε0 : 0 ≤ ε := (Real.sqrt_nonneg _).trans hε
  have hcoef : ε ≤ (2*((J-1 : ℕ) : ℝ)+1)*ε := by
    have hj : (0 : ℝ) ≤ (J-1 : ℕ) := Nat.cast_nonneg _
    nlinarith only [hj, hε0]
  have hstartgap : Real.sqrt (B S*B T) < B T-B S := by
    linarith only [hε, hcoef, hindexgap, hBV]
  obtain ⟨l, hl, q, E, hE, hES, hqa, hq, heq, hfirst⟩ :=
    ppt_actual_preimage_leading_mismatch_of_gap p ⟨J-1,by omega⟩ hF hS1.le
      (fun i => (hp i).1) hpa.injective hvalue hsq hnormal
      (hp _) hST hlast hstartgap hmismatch
  have hprefixT (i : Fin k) (hi : i ≤ ⟨J-1,by omega⟩) : T ≤ (p i-1 : ℕ) :=
    hlast.trans (Nat.cast_le.mpr (Nat.sub_le_sub_right (hpa.antitone hi) 1))
  obtain ⟨hjl, r, hrj, hVr⟩ := ppt_right_index_exists p q ⟨J-1,by omega⟩
    hS1 hBS hd.ne' hE.ne' hp (fun i => (hq i).1) heq
    (hDS.trans hSV) (hES.trans hSV) hSV hVT hε hprefixT hindexgap
  have hJl : J ≤ l := by
    change J-1<l at hjl
    omega
  have hVlast : V < (q ⟨J-1,hjl⟩-1 : ℕ) := by
    have hr1 : 1 ≤ q r-1 := by have := (hq r).1.1.two_le; omega
    have hrr := largestPrimeFactor_le_self hr1
    have hmon := Nat.sub_le_sub_right (hqa.antitone
      (show (⟨J-1,hjl⟩ : Fin l) ≤ r from hrj)) 1
    exact hVr.trans_le (Nat.cast_le.mpr (hrr.trans hmon))
  have hqz (i : Fin l) : (q i-1 : ℕ) ≤ z := by
    have hdiv : q i-1 ∣ F.totient := by
      rw [hvalue, ppt_totient_primeProduct p (fun i => (hp i).1) hpa.injective, heq]
      exact (Finset.dvd_prod_of_mem (fun i => q i-1) (Finset.mem_univ i)).trans
        (dvd_mul_left _ _)
    exact (Nat.cast_le.mpr (Nat.le_of_dvd (Nat.totient_pos.mpr hF) hdiv)).trans hsize
  have htail := ppt_right_tail_smooth p q hS1 hBS hSU hUV hd.ne' hE.ne'
    hp (fun i => (hq i).1) hqa.antitone heq (hDS.trans hSU) (hES.trans hSU)
    hlow hqz hε' htailgap
  refine ⟨l, q, E, hJl, hE, hES, hqa, ?_, heq, hfirst.symm, ?_, htail, hqz⟩
  · intro i
    have hqi : (2 : ℝ) < q i := hS.trans_lt (hq i).2
    have hqi' : 2 < q i := by exact_mod_cast hqi
    exact ⟨(hq i).1, by omega⟩
  · intro i hi
    have hij : i ≤ (⟨J-1,hjl⟩ : Fin l) := by change i.val ≤ J-1; omega
    exact hVlast.trans_le (Nat.cast_le.mpr (Nat.sub_le_sub_right (hqa.antitone hij) 1))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTTerminalGap
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
A vacant terminal window is chosen from the actual finite list of left
prime heights. Its width remains larger than the local normality error,
so the comparison's last upper cutoff can be placed inside that window.
-/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

/-- Among `n+1` disjoint closed windows, one misses all `n` coordinates. -/
lemma ppt_empty_separated_window {n : ℕ} (x : Fin n → ℝ) {T δ : ℝ}
    (hδ : 0 < δ) :
    ∃ j : Fin (n+1), ∀ i : Fin n,
      ¬(T+2*(j.val : ℝ)*δ ≤ x i ∧ x i ≤ T+(2*(j.val : ℝ)+1)*δ) := by
  classical
  by_contra hnone
  push Not at hnone
  choose f hf using hnone
  have hsep {j k : Fin (n+1)} (hjk : j < k) :
      T+(2*(j.val : ℝ)+1)*δ < T+2*(k.val : ℝ)*δ := by
    have hc : (j.val : ℝ)+1 ≤ k.val := by
      exact_mod_cast (Nat.succ_le_of_lt hjk)
    nlinarith only [hc, hδ]
  have hinj : Function.Injective f := by
    intro j k heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hjk | hkj
    · have hh := hsep hjk
      have hj := (hf j).2
      have hk := (hf k).1
      rw [heq] at hj
      linarith only [hh, hj, hk]
    · have hh := hsep hkj
      have hj := (hf j).1
      have hk := (hf k).2
      rw [heq] at hj
      linarith only [hh, hj, hk]
  have hc := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin] at hc
  omega

/-- An empty height window splits a decreasing list into a high prefix
and a low suffix; equality at either endpoint is excluded. -/
lemma ppt_antitone_split_at_empty_window {n : ℕ} (x : Fin n → ℝ)
    (hx : Antitone x) {L U : ℝ}
    (hempty : ∀ i, ¬(L ≤ x i ∧ x i ≤ U)) :
    ∃ J : ℕ, J ≤ n ∧
      (∀ i : Fin n, i.val < J → U < x i) ∧
      (∀ i : Fin n, J ≤ i.val → x i < L) := by
  classical
  by_cases hex : ∃ j : ℕ, ∃ hj : j < n, x ⟨j,hj⟩ ≤ U
  · obtain ⟨hJn, hJU⟩ := Nat.find_spec hex
    have hJL : x ⟨Nat.find hex,hJn⟩ < L := by
      by_contra hn
      exact hempty _ ⟨le_of_not_gt hn, hJU⟩
    refine ⟨Nat.find hex, hJn.le, ?_, ?_⟩
    · intro i hi
      by_contra hn
      exact Nat.find_min hex hi ⟨i.isLt, le_of_not_gt hn⟩
    · intro i hi
      exact (hx (show (⟨Nat.find hex,hJn⟩ : Fin n) ≤ i from hi)).trans_lt hJL
  · refine ⟨n, le_rfl, ?_, ?_⟩
    · intro i hi
      by_contra hn
      exact hex ⟨i.val, i.isLt, le_of_not_gt hn⟩
    · intro i hi
      omega

/-- Normality errors fit inside a reciprocal-dimension fraction of the
terminal height range. This is stronger than a fixed-fraction gap. -/
theorem ppt_terminal_normality_budget {A η : ℝ} (_hA : 0 < A) (hη : 0 < η) :
    ∀ᶠ t : ℝ in atTop, ∀ (H J : ℕ) (s X : ℝ),
      1 ≤ H → J ≤ H → (H : ℝ) ≤ A*Real.log t →
      0 ≤ s → s ≤ (H : ℝ)^4 → 0 ≤ X → X ≤ t →
      (2*(J : ℝ)+1)*Real.sqrt (s*X)+s < η*t^(2/3 : ℝ)/((H : ℝ)+1) := by
  have h₄ : Tendsto (fun t : ℝ => (Real.log t)^4/t^(1/6 : ℝ)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (4 : ℕ)
        (by norm_num : (0 : ℝ) < 1/6)).tendsto_div_nhds_zero
  have h₅ : Tendsto (fun t : ℝ => (Real.log t)^5/t^(2/3 : ℝ)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (5 : ℕ)
        (by norm_num : (0 : ℝ) < 2/3)).tendsto_div_nhds_zero
  have hsum : Tendsto (fun t : ℝ =>
      6*A^4*((Real.log t)^4/t^(1/6 : ℝ))+2*A^5*((Real.log t)^5/t^(2/3 : ℝ)))
      atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add] using (h₄.const_mul (6*A^4)).add (h₅.const_mul (2*A^5))
  filter_upwards [hsum.eventually (eventually_lt_nhds hη),
    eventually_gt_atTop (0 : ℝ)] with t hbudget ht
  intro H J s X hH hJ hdim hs0 hs hX0 hX
  have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hJr : (J : ℝ) ≤ H := by exact_mod_cast hJ
  have ht23 : 0 < t^(2/3 : ℝ) := Real.rpow_pos_of_pos ht _
  have hsqrt : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hroot : Real.sqrt (s*X) ≤ (H : ℝ)^2*Real.sqrt t := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      s*X ≤ (H : ℝ)^4*t := mul_le_mul hs hX hX0 (by positivity)
      _ = ((H : ℝ)^2*Real.sqrt t)^2 := by
        rw [mul_pow, Real.sq_sqrt ht.le]
        ring
  have hleft : (2*(J : ℝ)+1)*Real.sqrt (s*X)+s ≤
      3*(H : ℝ)^3*Real.sqrt t+(H : ℝ)^4 := by
    have hmul := mul_le_mul_of_nonneg_left hroot
      (show 0 ≤ 2*(J : ℝ)+1 by positivity)
    have hcoef := mul_le_mul_of_nonneg_right
      (show 2*(J : ℝ)+1 ≤ 3*(H : ℝ) by linarith only [hJr, hHr])
      (show 0 ≤ (H : ℝ)^2*Real.sqrt t by positivity)
    nlinarith only [hmul, hcoef, hs]
  have hweighted :
      ((2*(J : ℝ)+1)*Real.sqrt (s*X)+s)*((H : ℝ)+1) ≤
        6*(H : ℝ)^4*Real.sqrt t+2*(H : ℝ)^5 := by
    have hmul := mul_le_mul_of_nonneg_right hleft
      (show 0 ≤ (H : ℝ)+1 by positivity)
    have hcoef := mul_le_mul_of_nonneg_left
      (show (H : ℝ)+1 ≤ 2*(H : ℝ) by linarith only [hHr])
      (show 0 ≤ 3*(H : ℝ)^3*Real.sqrt t+(H : ℝ)^4 by positivity)
    nlinarith only [hmul, hcoef]
  have hH4 := pow_le_pow_left₀ hH0 hdim 4
  have hH5 := pow_le_pow_left₀ hH0 hdim 5
  have hscale : 6*(H : ℝ)^4*Real.sqrt t+2*(H : ℝ)^5 ≤
      6*(A*Real.log t)^4*Real.sqrt t+2*(A*Real.log t)^5 := by
    exact add_le_add (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hH4 (by norm_num)) hsqrt)
      (mul_le_mul_of_nonneg_left hH5 (by norm_num))
  have hratio : Real.sqrt t/t^(2/3 : ℝ) = 1/t^(1/6 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub ht,
      show (1/2 : ℝ)-(2/3 : ℝ) = -(1/6 : ℝ) by norm_num,
      Real.rpow_neg ht.le]
    simp only [one_div]
  have he : (6*(A*Real.log t)^4*Real.sqrt t+2*(A*Real.log t)^5)/t^(2/3 : ℝ) =
      6*A^4*((Real.log t)^4/t^(1/6 : ℝ))+2*A^5*((Real.log t)^5/t^(2/3 : ℝ)) := by
    rw [add_div, mul_div_assoc, hratio]
    ring
  have htop : 6*(A*Real.log t)^4*Real.sqrt t+2*(A*Real.log t)^5 < η*t^(2/3 : ℝ) := by
    apply (div_lt_iff₀ ht23).mp
    rwa [he]
  apply (lt_div_iff₀ (show 0 < (H : ℝ)+1 by positivity)).mpr
  exact hweighted.trans_lt (hscale.trans_lt htop)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTTerminalSelection
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite terminal-window label with enough room for alignment and grid errors. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

/-- The terminal cutoff is selected from `N+1` explicit windows. The
entire normality and paired-grid budget fits inside a quarter of the
chosen vacant interval. -/
theorem ppt_select_terminal_window {A : ℝ} (hA : 0 < A) :
    ∀ᶠ t : ℝ in atTop, ∀ (N H : ℕ) (x : Fin N → ℝ) (s : ℝ),
      ∀ hN : 0 < N,
      Antitone x → N ≤ H → 1 ≤ H → (H : ℝ) ≤ A*Real.log t →
      0 ≤ s → s ≤ (H : ℝ)^4 → 2*t^(2/3 : ℝ) < x ⟨0,hN⟩ →
      ∃ j : Fin (N+1), ∃ J : ℕ,
        let L := t^(2/3 : ℝ)+2*(j.val : ℝ)*(t^(2/3 : ℝ)/(2*((N : ℝ)+1)))
        let U := t^(2/3 : ℝ)+(2*(j.val : ℝ)+1)*(t^(2/3 : ℝ)/(2*((N : ℝ)+1)))
        t^(2/3 : ℝ) ≤ L ∧ U ≤ 2*t^(2/3 : ℝ) ∧
        0 < J ∧ J ≤ N ∧
        (∀ i : Fin N, i.val < J → U < x i) ∧
        (∀ i : Fin N, J ≤ i.val → x i < L) ∧
        (2*(H : ℝ)+1)*Real.sqrt (s*t)+s+
          (8*(H : ℝ)+20)*(2*((Real.log t)^5/Real.sqrt t))*t < (U-L)/4 := by
  filter_upwards [ppt_terminal_normality_budget hA (by norm_num : (0 : ℝ) < 1/16),
    ppt_log_dimension_separation hA, eventually_gt_atTop (0 : ℝ)]
    with t hnormal hgrid ht
  intro N H x s hN hx hNH hH hdim hs0 hs hhead
  let T : ℝ := t^(2/3 : ℝ)
  let δ : ℝ := T/(2*((N : ℝ)+1))
  have hT : 0 < T := Real.rpow_pos_of_pos ht _
  have hdenN : 0 < 2*((N : ℝ)+1) := by positivity
  have hδ : 0 < δ := div_pos hT hdenN
  obtain ⟨j, hj⟩ := ppt_empty_separated_window (T := T) x hδ
  let L : ℝ := T+2*(j.val : ℝ)*δ
  let U : ℝ := T+(2*(j.val : ℝ)+1)*δ
  obtain ⟨J, hJN, hhigh, hlow⟩ := ppt_antitone_split_at_empty_window x hx hj
  have hj0 : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
  have hjN : (j.val : ℝ) ≤ N := by
    exact_mod_cast (Nat.lt_succ_iff.mp j.isLt)
  have hδscale : (2*((N : ℝ)+1))*δ = T := by dsimp only [δ]; field_simp
  have hL : T ≤ L := by
    have hh : 0 ≤ 2*(j.val : ℝ)*δ := by positivity
    dsimp only [L]
    linarith only [hh]
  have hU : U ≤ 2*T := by dsimp only [U]; nlinarith only [hδscale, hjN, hδ]
  have hwidth : U-L = δ := by dsimp only [U, L] <;> ring
  have hJ : 0 < J := by
    by_contra hh
    have hJ0 : J = 0 := Nat.eq_zero_of_not_pos hh
    have hl := hlow ⟨0,hN⟩ (by omega)
    have hLU : L < U := by rw [← sub_pos, hwidth]; exact hδ
    change 2*T < x ⟨0,hN⟩ at hhead
    linarith only [hl, hLU, hU, hhead]
  have hwide : T/(2*((H : ℝ)+1)) ≤ U-L := by
    rw [hwidth]
    exact div_le_div_of_nonneg_left hT.le hdenN
      (by exact_mod_cast (show 2*(N+1) ≤ 2*(H+1) by omega))
  have hnormal' : (2*(H : ℝ)+1)*Real.sqrt (s*t)+s < T/(16*((H : ℝ)+1)) := by
    have hh := hnormal H H s t hH le_rfl hdim hs0 hs ht.le le_rfl
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [T]
    field_simp
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hH0 : (0 : ℝ) < H := zero_lt_one.trans_le hHr
  have hH3 : (H : ℝ) ≤ (H : ℝ)^3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hHr (show 1 ≤ 3 by omega)
  have hden : 16*((H : ℝ)+1) ≤ 40*(H : ℝ)^3 := by nlinarith only [hHr, hH3]
  have hgrid' :
      (8*(H : ℝ)+20)*(2*((Real.log t)^5/Real.sqrt t))*t < T/(16*((H : ℝ)+1)) := by
    have hg0 : (8*(H : ℝ)+20)*(2*((Real.log t)^5/Real.sqrt t)) <
        1/(40*(H : ℝ)^3*t^(1/3 : ℝ)) := by
      simpa only [mul_div_assoc] using hgrid H hH hdim
    have hg := mul_lt_mul_of_pos_right hg0 ht
    have hprod : t^(1/3 : ℝ)*T = t := by
      dsimp only [T]
      rw [← Real.rpow_add ht]
      norm_num
    have hquot : (1/(40*(H : ℝ)^3*t^(1/3 : ℝ)))*t = T/(40*(H : ℝ)^3) := by
      have ht13 : 0 < t^(1/3 : ℝ) := Real.rpow_pos_of_pos ht _
      calc
        _ = (1/(40*(H : ℝ)^3*t^(1/3 : ℝ)))*(t^(1/3 : ℝ)*T) := by rw [hprod]
        _ = _ := by field_simp
    rw [hquot] at hg
    exact hg.trans_le (div_le_div_of_nonneg_left hT.le (by positivity) hden)
  refine ⟨j, J, hL, hU, hJ, hJN, hhigh, hlow, ?_⟩
  have hw : 8*(T/(16*((H : ℝ)+1))) ≤ U-L := by
    convert hwide using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
    norm_num
  linarith only [hnormal', hgrid', hw]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTTerminalPreimage
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert the chosen vacant height window into the actual preimage prefix. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

/-- A vacant prime-height window with its proved error budget supplies
all cutoffs for the actual unequal-list preimage truncation. -/
theorem ppt_terminal_window_preimage : ∀ᶠ z : ℝ in atTop,
    ∀ (N H J d F : ℕ) (p : Fin N → ℕ) (S L U : ℝ),
      ∀ hJ : 0 < J, ∀ hJN : J ≤ N,
      0 < d → 0 < F → N ≤ H → 2 ≤ S → 0 ≤ B S →
      (∀ i, IsNormalPrime S (p i)) → (∀ i, 3 ≤ p i) → StrictAnti p →
      F.totient = d*(∏ i, p i).totient →
      (largestPrimeFactor d : ℝ) ≤ S → SquarefreeAbove F S →
      (∀ q : ℕ, q.Prime → q ∣ F → IsNormalPrime S q) →
      largestPrimeFactor F ≠ p ⟨0,by omega⟩ →
      (∀ i : Fin N, (p i-1 : ℕ) ≤ z) → (F.totient : ℝ) ≤ z →
      (B z)^(2/3 : ℝ) ≤ L → U ≤ 2*(B z)^(2/3 : ℝ) → L < U →
      2*(B z)^(2/3 : ℝ) ≤ B z →
      (∀ i : Fin N, i.val < J → U < B (p i)) →
      (∀ i : Fin N, J ≤ i.val → B (p i) < L) →
      (2*(H : ℝ)+1)*Real.sqrt (B S*B z)+B S+
        (8*(H : ℝ)+20)*(2*((Real.log (B z))^5/Real.sqrt (B z)))*B z < (U-L)/4 →
      let V := Real.exp (Real.exp ((L+U)/2))
      ∃ (l : ℕ) (q : Fin l → ℕ) (E : ℕ) (hJl : J ≤ l),
        S ≤ Real.exp (Real.exp L) ∧ 0 < E ∧
        (largestPrimeFactor E : ℝ) ≤ S ∧ StrictAnti q ∧
        (∀ i, IsNormalPrime S (q i) ∧ 3 ≤ q i) ∧
        d*shiftedProduct p = E*shiftedProduct q ∧
        p ⟨0,by omega⟩ ≠ q ⟨0,by omega⟩ ∧
        (∀ i : Fin N, J ≤ i.val → (largestPrimeFactor (p i-1) : ℝ) ≤ V) ∧
        (∀ i : Fin l, i.val < J → V < (q i-1 : ℕ)) ∧
        (∀ i : Fin l, J ≤ i.val → (largestPrimeFactor (q i-1) : ℝ) ≤ V) ∧
        (∀ i : Fin l, (q i-1 : ℕ) ≤ z) := by
  filter_upwards [ppt_normal_factor_loss_mesh,
    B_tendsto.eventually (eventually_gt_atTop (1 : ℝ)),
    eventually_gt_atTop (1 : ℝ)] with z hloss hB hz
  intro N H J d F p S L U hJ hJN hd hF hNH hS hBS hp hp3 hpa hvalue
    hDS hsq hnormal hmismatch hpz hsize hL hU hLU hUt hhigh hlow hbudget
  dsimp only
  let t := B z
  let δ := 2*((Real.log t)^5/Real.sqrt t)
  let M := (L+U)/2
  let Q := (L+3*U)/4
  let V := Real.exp (Real.exp M)
  let T := Real.exp (Real.exp Q)
  let W := Real.exp (Real.exp L)
  let ε := Real.sqrt (B S*t)
  have ht : 0 < t := zero_lt_one.trans hB
  have hδ : 0 ≤ δ := by
    have hlog : 0 < Real.log t := Real.log_pos hB
    dsimp only [δ]
    positivity
  have hε : 0 ≤ ε := Real.sqrt_nonneg _
  have hL0 : 0 < L := (Real.rpow_pos_of_pos ht (2/3 : ℝ)).trans_le hL
  have hwidth : U-L ≤ L := by linarith only [hL, hU]
  have hgrid0 : 0 ≤ (8*(H : ℝ)+20)*δ*t := by positivity
  have hnormalBudget : (2*(H : ℝ)+1)*ε+B S < (U-L)/4 := by
    change (2*(H : ℝ)+1)*ε+B S+(8*(H : ℝ)+20)*δ*t < _ at hbudget
    linarith only [hbudget, hgrid0]
  have hsL : B S < L := by
    have hh : 0 ≤ (2*(H : ℝ)+1)*ε := by positivity
    linarith only [hnormalBudget, hh, hwidth, hL0]
  have hSW : S ≤ W := by
    have hS1 : 1 < S := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hS
    have hh := Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hsL.le)
    simpa only [exp_exp_doubleLog hS1, W] using hh
  have hWM : W < V := Real.exp_lt_exp.mpr (Real.exp_lt_exp.mpr (by dsimp only [M] <;> linarith))
  have hVQ : V < T := Real.exp_lt_exp.mpr (Real.exp_lt_exp.mpr (by dsimp only [M,Q] <;> linarith))
  have hQt : Q ≤ t := by dsimp only [Q,t]; linarith only [hLU.le, hU, hUt]
  have hTz : T ≤ z := by
    have hh := Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hQt)
    simpa only [T,t,exp_exp_doubleLog hz] using hh
  have hSz : S ≤ z := hSW.trans (hWM.le.trans (hVQ.le.trans hTz))
  have hcost : δ*t < (U-L)/4 := by
    have hcoef : 1 ≤ 8*(H : ℝ)+20 := by
      have hh : (0 : ℝ) ≤ H := Nat.cast_nonneg H
      linarith only [hh]
    have hh := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hδ ht.le)
    have hnorm0 : 0 ≤ (2*(H : ℝ)+1)*ε+B S := by positivity
    change (2*(H : ℝ)+1)*ε+B S+(8*(H : ℝ)+20)*δ*t < _ at hbudget
    nlinarith only [hh, hnorm0, hbudget]
  have hlast : T ≤ (p ⟨J-1,by omega⟩-1 : ℕ) := by
    let i : Fin N := ⟨J-1,by omega⟩
    have hi : i.val < J := by dsimp only [i]; omega
    have hband := (hloss (p i) S (hp3 i)
      (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hS) hBS hSz (hp i) (hpz i)).1
    have hh := mul_le_mul_of_nonneg_right hband ht.le
    change (B (p i)/t-δ)*t ≤ (B (largestPrimeFactor (p i-1))/t)*t at hh
    rw [sub_mul, div_mul_cancel₀ _ ht.ne', div_mul_cancel₀ _ ht.ne'] at hh
    have hheight : Q < B (largestPrimeFactor (p i-1)) := by
      have hii := hhigh i hi
      dsimp only [Q]
      linarith only [hh, hii, hcost]
    have hr : (1 : ℝ) < largestPrimeFactor (p i-1) := by
      exact_mod_cast one_lt_largestPrimeFactor (show 2 ≤ p i-1 by have := hp3 i; omega)
    have hb := Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hheight.le)
    rw [exp_exp_doubleLog hr] at hb
    exact hb.trans (Nat.cast_le.mpr (largestPrimeFactor_le_self (by have := hp3 i; omega)))
  have hleftlow (i : Fin N) (hi : J ≤ i.val) :
      (largestPrimeFactor (p i-1) : ℝ) ≤ W := by
    have hp1 : (1 : ℝ) < p i := by exact_mod_cast (hp i).1.one_lt
    have hb := Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (hlow i hi).le)
    rw [exp_exp_doubleLog hp1] at hb
    exact (Nat.cast_le.mpr ((largestPrimeFactor_le_self
      (by have := hp3 i; omega)).trans (Nat.sub_le _ _))).trans hb
  have hεQ : Real.sqrt (B S*B T) ≤ ε := by
    have hQT : B T = Q := B_exp_exp Q
    rw [hQT]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hQt hBS)
  have hindexgap : (2*((J-1 : ℕ) : ℝ)+1)*ε < B T-B V := by
    have hJH : (J-1 : ℕ) ≤ H := (Nat.sub_le _ _).trans (hJN.trans hNH)
    have hjr : ((J-1 : ℕ) : ℝ) ≤ H := by exact_mod_cast hJH
    have hh := mul_le_mul_of_nonneg_right
      (show 2*((J-1 : ℕ) : ℝ)+1 ≤ 2*(H : ℝ)+1 by linarith only [hjr]) hε
    rw [show B T=Q from B_exp_exp Q, show B V=M from B_exp_exp M]
    dsimp only [Q,M]
    linarith only [hh, hnormalBudget, hBS]
  have htailgap : (2*(J : ℝ)+1)*ε < B V-B W := by
    have hjr : (J : ℝ) ≤ H := by exact_mod_cast (hJN.trans hNH)
    have hh := mul_le_mul_of_nonneg_right
      (show 2*(J : ℝ)+1 ≤ 2*(H : ℝ)+1 by linarith only [hjr]) hε
    rw [show B V=M from B_exp_exp M, show B W=L from B_exp_exp L]
    dsimp only [M]
    linarith only [hh, hnormalBudget, hBS, hLU]
  obtain ⟨l,q,E,hJl,hE,hES,hqa,hq,heq,hfirst,hqhigh,hqlow,hqz⟩ :=
    ppt_preimage_terminal_prefix p hJ hJN hd hF hS hBS hSW hWM hVQ hp hpa
      hvalue hDS hsq hnormal hmismatch hlast hleftlow hsize hεQ le_rfl hindexgap htailgap
  exact ⟨l,q,E,hJl,hSW,hE,hES,hqa,hq,heq,hfirst,
    fun i hi => (hleftlow i hi).trans hWM.le,hqhigh,hqlow,hqz⟩

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTPointwiseGrid
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual residual lists determine one of the finite comparison grids.
The hypotheses below are arithmetic and geometric properties of those lists;
the published comparison conditions and parameters are conclusions. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma ppt_B_mono {x y : ℝ} (hx : 1<x) (hxy : x≤y) : B x≤B y :=
  Real.log_le_log (Real.log_pos hx) (Real.log_le_log (zero_lt_one.trans hx) hxy)

/-- A predecessor bounded by the comparison endpoint gives an upper
bound on its normalized largest-factor coordinate. -/
lemma ppt_factor_coordinate_upper {p : ℕ} {z : ℝ}
    (hp : 3 ≤ p) (hB : 0 < B z) (hpz : (p-1 : ℕ) ≤ z) :
    B (largestPrimeFactor (p-1))/B z ≤ 1 := by
  have hlp : (1 : ℝ) < largestPrimeFactor (p-1) := by
    exact_mod_cast one_lt_largestPrimeFactor (show 2 ≤ p-1 by omega)
  apply (div_le_one hB).mpr
  exact ppt_B_mono hlp
    ((Nat.cast_le.mpr (largestPrimeFactor_le_self (by omega))).trans hpz)

/-- The vacant terminal interval pays for normality alignment at every
retained index, including the full bottom-grid padding. -/
lemma ppt_terminal_coordinate_padding {j H : ℕ} {t L U δ u v w : ℝ}
    (hj : j ≤ H) (ht : 0 < t) (hδ : 0 ≤ δ)
    (hhigh : U < w) (hfactor : w/t-δ ≤ u)
    (halign : |u-v| ≤ (2*(j : ℝ)+1)*δ)
    (hbudget : (8*(H : ℝ)+20)*δ*t < (U-L)/4) :
    (L+U)/(2*t)+3*δ < min u v := by
  have hjr : (j : ℝ) ≤ H := by exact_mod_cast hj
  have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hcost : (2*(j : ℝ)+5)*δ*t < (U-L)/2 := by
    have hc : (2*(j : ℝ)+5)*δ*t ≤ (8*(H : ℝ)+20)*δ*t :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith only [hjr,hH0]) hδ) ht.le
    have hw : 0 < U-L := by
      have hh : 0 ≤ (8*(H : ℝ)+20)*δ*t := by positivity
      linarith only [hbudget,hh]
    linarith only [hc,hbudget,hw]
  have hhigh' : U/t < w/t := div_lt_div_of_pos_right hhigh ht
  have hdiff : (L+U)/(2*t)+3*δ+(2*(j : ℝ)+1)*δ+δ < U/t := by
    apply (lt_div_iff₀ ht).mpr
    have he : ((L+U)/(2*t)+3*δ+(2*(j : ℝ)+1)*δ+δ)*t =
        (L+U)/2+(2*(j : ℝ)+5)*δ*t := by field_simp <;> ring
    rw [he]
    linarith only [hcost]
  apply lt_min
  · have hc : 0 ≤ (2*(j : ℝ)+1)*δ := by positivity
    linarith only [hdiff,hhigh',hfactor,hc]
  · linarith only [hdiff,hhigh',hfactor,(abs_le.mp halign).2]

/-- Normality aligns the actual lists after cancellation.  Smoothness
of both integer multipliers is used only below their retained predecessors. -/
theorem ppt_pair_alignment_in_mesh {A : ℝ} (hA : 0 < A) :
    ∀ᶠ z : ℝ in atTop, ∀ (b H D : ℕ) (S V : ℝ) (p : ShiftedPair b),
      (H : ℝ) ≤ A*Real.log (B z) →
      1 < S → 0 ≤ B S → B S ≤ (H : ℝ)^4 → S ≤ V → V ≤ z →
      0 < D → 0 < p.remainder →
      (∀ i, IsNormalPrime S (p.left i) ∧ IsNormalPrime S (p.right i)) →
      (∀ i, 3 ≤ p.left i ∧ 3 ≤ p.right i) →
      Antitone p.left → Antitone p.right →
      D*shiftedProduct p.left = p.remainder*shiftedProduct p.right →
      (largestPrimeFactor D : ℝ) ≤ V → (largestPrimeFactor p.remainder : ℝ) ≤ V →
      (∀ i, V ≤ (p.left i-1 : ℕ) ∧ V ≤ (p.right i-1 : ℕ)) →
      (∀ i, (p.left i-1 : ℕ) ≤ z ∧ (p.right i-1 : ℕ) ≤ z) →
      ∀ i : Fin b,
        |B (largestPrimeFactor (p.left i-1))/B z-
          B (largestPrimeFactor (p.right i-1))/B z| ≤
          (2*(i.val : ℝ)+1)*(2*((Real.log (B z))^5/Real.sqrt (B z))) := by
  filter_upwards [B_tendsto.eventually (ppt_local_alignment_in_paired_mesh hA),
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with z hmesh hB
  intro b H D S V p hdim hS hBS hheight hSV hVz hD hE hp hp3 hpa hqa heq
    hDV hEV hsmall hsize i
  apply hmesh H i.val S _ _ hdim hBS hheight
  exact ppt_normalized_coordinate_alignment p.left p.right i.isLt i.isLt
    hS hBS hB (hSV.trans hVz) hD.ne' hE.ne'
    (fun j => (hp j).1) (fun j => (hp j).2) hpa hqa heq
    (hp3 i).1 (hp3 i).2 (hsize i).1 (hsize i).2
    (le_min (hDV.trans (hsmall i).1) (hDV.trans (hsmall i).2))
    (le_min (hEV.trans (hsmall i).1) (hEV.trans (hsmall i).2))
    (le_min (hSV.trans (hsmall i).1) (hSV.trans (hsmall i).2))

/-- All literal grid intervals, parameters, and comparison conditions
for an actual residual pair.  The first cutoff and the adjacent separation
are the quantitative prime-row conclusions established before grouping. -/
theorem ppt_pointwise_grid_realization {A γ : ℝ} (hA : 0 < A) (hγ : 0 < γ) :
    ∀ᶠ z : ℝ in atTop,
    ∀ (b H D c : ℕ) (S V L U : ℝ) (p : ShiftedPair b), ∀ hb : 0 < b,
      b ≤ H → (H : ℝ) ≤ A*Real.log (B z) →
      Real.exp (Real.exp 1) ≤ S → B S ≤ (H : ℝ)^4 →
      V = Real.exp (Real.exp ((L+U)/2)) → S ≤ V → V ≤ z →
      0 < D → 0 < c → 0 < p.remainder →
      (D : ℝ) ≤ z^(1/100 : ℝ) → (c.totient : ℝ) ≤ z^(1/10 : ℝ) →
      (∀ i, IsNormalPrime S (p.left i) ∧ IsNormalPrime S (p.right i)) →
      (∀ i, 3 ≤ p.left i ∧ 3 ≤ p.right i ∧ p.left i ≠ p.right i) →
      Antitone p.left → Antitone p.right →
      D*shiftedProduct p.left = p.remainder*shiftedProduct p.right →
      ((D*shiftedProduct p.left : ℕ) : ℝ) ≤ z/c.totient →
      SquarefreeAbove (D*shiftedProduct p.left) V →
      (largestPrimeFactor D : ℝ) ≤ V → (largestPrimeFactor p.remainder : ℝ) ≤ V →
      (∀ i, V ≤ (p.left i-1 : ℕ) ∧ V ≤ (p.right i-1 : ℕ)) →
      (∀ i, (p.left i-1 : ℕ) ≤ z ∧ (p.right i-1 : ℕ) ≤ z) →
      z^(9/10 : ℝ) ≤ p.left ⟨0,hb⟩ →
      0 ≤ L → U < B (p.left ⟨b-1,by omega⟩) →
      (8*(H : ℝ)+20)*(2*((Real.log (B z))^5/Real.sqrt (B z)))*B z < (U-L)/4 →
      let δ := 2*((Real.log (B z))^5/Real.sqrt (B z))
      let u := fun i => B (largestPrimeFactor (p.left i-1))/B z
      let v := fun i => B (largestPrimeFactor (p.right i-1))/B z
      let label := fun i => collisionGridIndex δ (u i) (v i)
      let ζ := (L+U)/(2*B z)
      let θ := pptUniformHeadEdge (B z)-δ
      let ν := pairedGridUpper δ ζ label
      let μ := pptGridLower δ θ label
      ν 1 ≤ 1-γ/(Real.log (B z))^3 →
      (∀ i : Fin b, ∀ hi : i.val+1 < b,
        max (u ⟨i.val+1,hi⟩) (v ⟨i.val+1,hi⟩)+
          (2*(i.val : ℝ)+8)*δ < min (u i) (v i)) →
      label ∈ collisionGridFamilies δ b ∧
      FordComparisonParameters b z S D c.totient
        (comparisonCutoffs z ν) (comparisonCutoffs z μ) ∧
      FordComparisonConditions b z S D c.totient
        (comparisonCutoffs z ν) (comparisonCutoffs z μ) p ∧
      (∀ i : Fin b, 0 < i.val → ν i ≤ u i+(2*(b : ℝ)+3)*δ) ∧
      (∀ i ∈ Finset.Icc 1 (b-1), ν i-μ i ≤ (2*(b : ℝ)+3)*δ) := by
  filter_upwards [ppt_pair_alignment_in_mesh hA, ppt_normal_factor_loss_mesh,
    ppt_normal_head_uniform_edge, ppt_normalized_pair_conditions,
    B_tendsto.eventually (ppt_first_cutoff_below_aligned_head hγ),
    B_tendsto.eventually (ppt_inverse_log_cube_cutoff_loss hγ),
    B_tendsto.eventually (ppt_local_normality_error_mesh hA),
    B_tendsto.eventually (eventually_gt_atTop (1 : ℝ)),
    eventually_gt_atTop (1 : ℝ)] with z halign hfactor hhead hconditions hfirst
      hlogloss hmesh hB hz
  intro b H D c S V L U p hb hbH hdim hS hheight hV hSV hVz hD hc hE hDz hcz
    hp hp3 hpa hqa heq hsize hsq hDV hEV hsmall hpred hlarge hL hhigh hbudget
  dsimp only
  let δ := 2*((Real.log (B z))^5/Real.sqrt (B z))
  let u := fun i => B (largestPrimeFactor (p.left i-1))/B z
  let v := fun i => B (largestPrimeFactor (p.right i-1))/B z
  let label := fun i => collisionGridIndex δ (u i) (v i)
  let ζ := (L+U)/(2*B z)
  let θ := pptUniformHeadEdge (B z)-δ
  let ν := pairedGridUpper δ ζ label
  let μ := pptGridLower δ θ label
  intro hν hnext
  have hB0 : 0 < B z := zero_lt_one.trans hB
  have hlog : 0 < Real.log (B z) := Real.log_pos hB
  have hδ : 0 < δ := by dsimp only [δ] <;> positivity
  have hS1 : 1 < S :=
    (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)).trans_le hS
  have hBS : 0 ≤ B S := by
    have hh := ppt_B_mono (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)) hS
    have hh' : (1 : ℝ) ≤ B S := by simpa only [B,Real.log_exp] using hh
    exact (by norm_num : (0 : ℝ) ≤ 1).trans hh'
  have hSz := hSV.trans hVz
  have hclose : ∀ i : Fin b, |u i-v i| ≤ (2*(i.val : ℝ)+1)*δ :=
    halign b H D S V p hdim hS1 hBS hheight hSV hVz hD hE hp
      (fun i => ⟨(hp3 i).1,(hp3 i).2.1⟩) hpa hqa heq hDV hEV hsmall hpred
  have hU : L < U := by
    have hh : 0 ≤ (8*(H : ℝ)+20)*δ*B z := by positivity
    linarith only [hbudget,hh]
  have hζ : 0 ≤ ζ := by
    dsimp only [ζ]
    exact div_nonneg (by linarith only [hL,hU]) (by positivity)
  have hpadding (i : Fin b) : ζ+3*δ < min (u i) (v i) := by
    have hilast : i ≤ (⟨b-1,by omega⟩ : Fin b) := by
      change i.val ≤ b-1
      omega
    have hmono : B (p.left ⟨b-1,by omega⟩) ≤ B (p.left i) :=
      ppt_B_mono (by exact_mod_cast (show 1 < p.left ⟨b-1,by omega⟩ by
        have := (hp3 ⟨b-1,by omega⟩).1; omega))
        (Nat.cast_le.mpr (hpa hilast))
    exact ppt_terminal_coordinate_padding (show i.val ≤ H by omega) hB0 hδ.le
      (hhigh.trans_le hmono)
      (hfactor (p.left i) S (hp3 i).1 hS1 hBS hSz (hp i).1 (hpred i).1).1
      (hclose i) hbudget
  have hu (i : Fin b) : 0 ≤ u i ∧ u i ≤ 1 :=
    ⟨(by have := (hpadding i).trans_le (min_le_left _ _); linarith only [this,hζ,hδ]),
      ppt_factor_coordinate_upper (hp3 i).1 hB0 (hpred i).1⟩
  have hv (i : Fin b) : 0 ≤ v i ∧ v i ≤ 1 :=
    ⟨(by have := (hpadding i).trans_le (min_le_right _ _); linarith only [this,hζ,hδ]),
      ppt_factor_coordinate_upper (hp3 i).2.1 hB0 (hpred i).2⟩
  have hbottom := hpadding ⟨b-1,by omega⟩
  have hheadL := hhead (p.left ⟨0,hb⟩) S hS1 hBS hSz (hp _).1 hlarge (hpred _).1
  have hθ := ppt_aligned_heads_uniform_edge hB.le hheadL.1 (hclose ⟨0,hb⟩)
  have hθ' : θ ≤ min (u ⟨0,hb⟩) (v ⟨0,hb⟩) ∧ θ < 1 := by
    simpa [θ,u,v] using hθ
  have hνθ : ν 1 < θ := hfirst (ν 1) δ hν le_rfl
  have hnext4 (i : Fin b) (hi : i.val+1 < b) :
      max (u ⟨i.val+1,hi⟩) (v ⟨i.val+1,hi⟩)+
        (2*(i.val+1 : ℕ)+4 : ℝ)*δ < min (u i) (v i) := by
    have hh := hnext i hi
    push_cast
    linarith only [hh,hδ]
  have hnext6 (i : Fin b) (hi : i.val+1 < b) :
      max (u ⟨i.val+1,hi⟩) (v ⟨i.val+1,hi⟩)+
        (2*(i.val+1 : ℕ)+6 : ℝ)*δ < min (u i) (v i) := by
    have he : (2*(i.val+1 : ℕ)+6 : ℝ) = 2*(i.val : ℝ)+8 := by
      push_cast
      ring
    rw [he]
    exact hnext i hi
  have hinterval := ppt_grid_intervals hb hδ u v (fun i => (hu i).1)
    (fun i => (hv i).1) hclose (max_le (hu _).2 (hv _).2) hθ'.1 hθ'.2 hνθ hnext4
    (lt_of_le_of_lt (by linarith only [hδ] : ζ+δ ≤ ζ+3*δ) hbottom)
  have hgaps := paired_grid_gaps hb hδ u v (fun i => (hu i).1)
    (fun i => (hv i).1) hclose hnext6 hbottom
  have hη : Real.sqrt (B S/B z) ≤ δ := by
    have hh := hmesh H S hdim hBS hheight
    dsimp only [δ]
    have hm : 0 ≤ (Real.log (B z))^5/Real.sqrt (B z) := by positivity
    linarith only [hh,hm]
  have hVeq : comparisonCutoffs z ν b = V := by
    have he : ν b = ζ := by simp [ν,pairedGridUpper,show b ≠ 0 by omega]
    rw [comparisonCutoffs,he,hV]
    congr 2
    dsimp only [ζ]
    field_simp
  have hfirstlog : Real.log (10*B z) ≤ B z*(1-ν 1) := by
    have hh := mul_le_mul_of_nonneg_left
      (show γ/(Real.log (B z))^3 ≤ 1-ν 1 by linarith only [hν]) hB0.le
    have he : B z*(γ/(Real.log (B z))^3) = γ*B z/(Real.log (B z))^3 := by ring
    rw [he] at hh
    exact hlogloss.trans hh
  have hparams : FordComparisonParameters b z S D c.totient
      (comparisonCutoffs z ν) (comparisonCutoffs z μ) :=
    ppt_ford_parameters_from_grid hb hz hB0 D c.totient label hS
      (hVeq.symm ▸ hSV) hinterval.2.2.2 hfirstlog
      (fun j hj => (mul_le_mul_of_nonneg_left hη (by norm_num : (0 : ℝ) ≤ 2)).trans_lt
        (hgaps j hj)) hD hDz (hVeq.symm ▸ hDV) (Nat.totient_pos.mpr hc) hcz
  refine ⟨collisionGridFamilies_mem hδ u v (fun i => (hu i).2),hparams,?_,?_⟩
  · apply hconditions b D c.totient S ν μ p hb hB0 hS1 hBS hSz
      (fun i => (hp i).1) (fun i => (hp i).2)
      (fun i => (hp3 i).1) (fun i => (hp3 i).2.1) (fun i => (hp3 i).2.2)
      hE heq hsize (hVeq.symm ▸ hsq) (hVeq.symm ▸ hEV)
    · intro i
      exact ⟨(hinterval.2.2.1 i).1,(hinterval.2.2.1 i).2.2.1,
        (hinterval.2.2.1 i).2.1,(hinterval.2.2.1 i).2.2.2⟩
    · exact hlarge
    · exact (hpred _).1
    · exact (Real.one_lt_exp_iff.mpr (Real.exp_pos _)).le
    · exact ppt_comparison_cutoff_power_of_log_loss hz hB0 hfirstlog
  · exact ppt_paired_grid_row_errors hδ u v (fun i => (hu i).1)
      (fun i => (hv i).1) hclose

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTGeometricGrid
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prime-coordinate contraction supplies the two geometric hypotheses
of the actual residual-grid theorem, including its singleton case. -/

noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma ppt_terminal_first_cutoff_loss {γ : ℝ} (_hγ : 0 < γ) :
    ∀ᶠ t : ℝ in atTop, ∀ L U : ℝ,
      L ≤ U → U ≤ 2*t^(2/3 : ℝ) →
      (L+U)/(2*t) ≤ 1-γ/(Real.log t)^3 := by
  filter_upwards [(tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/3)).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/4)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 (2*γ))),
    eventually_gt_atTop (0 : ℝ)] with t hsmall hlog ht
  intro L U hLU hU
  have hlog1 : 1 ≤ Real.log t := (le_max_left _ _).trans hlog
  have hlogγ : 2*γ ≤ Real.log t := (le_max_right _ _).trans hlog
  have hlog0 : 0 < Real.log t := zero_lt_one.trans_le hlog1
  have hp : Real.log t ≤ (Real.log t)^3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hlog1 (show 1 ≤ 3 by omega)
  have hγsmall : γ/(Real.log t)^3 ≤ 1/2 := by
    apply (div_le_iff₀ (pow_pos hlog0 3)).mpr
    linarith only [hlogγ,hp]
  have he : t^(2/3 : ℝ)/t = t^(-(1/3 : ℝ)) := by
    calc
      _ = t^(2/3 : ℝ)/t^(1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_sub ht]; norm_num
  have hbound : (L+U)/(2*t) ≤ 2*(t^(2/3 : ℝ)/t) := by
    apply (div_le_iff₀ (show 0 < 2*t by positivity)).mpr
    have heq : (2*(t^(2/3 : ℝ)/t))*(2*t) = 4*t^(2/3 : ℝ) := by field_simp <;> norm_num
    rw [heq]
    linarith only [hLU,hU]
  rw [he] at hbound
  linarith only [hbound,hsmall,hγsmall]

/-- Passing to an ordered sublist retains one common inverse-cube
contraction, measured by the remaining length at its first coordinate. -/
lemma ppt_geometric_embedded_contraction {m n b H : ℕ} {budget c : ℝ}
    {v : Fin n → ℝ} (hv : v ∈ relaxedGeometricFamily m n budget c)
    (hnm : n ≤ m) (ι : Fin b ↪o Fin n) (hb : 0 < b)
    (hH : m-(ι ⟨0,hb⟩).val ≤ H) :
    1/(10*(H : ℝ)^3) ≤ 1 ∧
      ∀ i j : Fin b, i < j →
        v (ι j) ≤ v (ι i)/(1+1/(10*(H : ℝ)^3)) := by
  have hrem (i : Fin b) : 1 ≤ m-(ι i).val := by
    have hi := (ι i).isLt
    omega
  have hremH (i : Fin b) : m-(ι i).val ≤ H := by
    have hi := ι.monotone (show (⟨0,hb⟩ : Fin b) ≤ i from Nat.zero_le _)
    change (ι ⟨0,hb⟩).val ≤ (ι i).val at hi
    omega
  have hHpos : 1 ≤ H := (hrem ⟨0,hb⟩).trans (hremH ⟨0,hb⟩)
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hHpos
  have hH0 : (0 : ℝ) < H := zero_lt_one.trans_le hHr
  constructor
  · apply (div_le_iff₀ (by positivity : 0 < 10*(H : ℝ)^3)).mpr
    have hh : (1 : ℝ) ≤ (H : ℝ)^3 := one_le_pow₀ hHr
    linarith only [hh]
  · intro i j hij
    have hactual := hv.2.2 (ι i) (ι j) (ι.strictMono hij)
    have hidentity : rowContractionError (m-((ι i).val+1))/2 =
        1/(10*((m-(ι i).val : ℕ) : ℝ)^3) := by
      have he : m-((ι i).val+1)+1 = m-(ι i).val := by
        have hi := (ι i).isLt
        omega
      have her : ((m-((ι i).val+1) : ℕ) : ℝ)+1 = ((m-(ι i).val : ℕ) : ℝ) := by
        exact_mod_cast he
      dsimp only [rowContractionError]
      rw [her]
      ring
    rw [hidentity] at hactual
    apply hactual.trans
    have hrem0 : (0 : ℝ) < (m-(ι i).val : ℕ) := by
      exact_mod_cast (zero_lt_one.trans_le (hrem i))
    have hp := pow_le_pow_left₀ hrem0.le (Nat.cast_le.mpr (hremH i)) 3
    have hrec : 1/(10*(H : ℝ)^3) ≤ 1/(10*((m-(ι i).val : ℕ) : ℝ)^3) :=
      one_div_le_one_div_of_le (by positivity)
        (mul_le_mul_of_nonneg_left hp (by norm_num))
    exact div_le_div_of_nonneg_left (hv.1.1 (ι i)) (by positivity)
      (by linarith only [hrec])

/-- An actual prime row gives both the first-cutoff loss and all paired
grid gaps.  No coordinate separation is assumed after taking largest
factors: those errors are supplied by normality and the doubled mesh. -/
theorem ppt_geometric_pair_grid {A : ℝ} (hA : 0 < A) :
    ∀ᶠ z : ℝ in atTop,
    ∀ (b H : ℕ) (S L U ω : ℝ) (p : ShiftedPair b), ∀ _hb : 0 < b,
      b ≤ H → (H : ℝ) ≤ A*Real.log (B z) →
      1 < S → 0 ≤ B S → S ≤ z →
      (∀ i, IsNormalPrime S (p.left i)) →
      (∀ i, 3 ≤ p.left i) →
      (∀ i, (p.left i-1 : ℕ) ≤ z) →
      1/(10*(H : ℝ)^3) ≤ ω → ω ≤ 1 →
      (∀ i : Fin b, (B z)^(2/3 : ℝ) ≤ B (p.left i)) →
      (∀ i : Fin b, ∀ hi : i.val+1 < b,
        B (p.left ⟨i.val+1,hi⟩) ≤ B (p.left i)/(1+ω)) →
      L ≤ U → U ≤ 2*(B z)^(2/3 : ℝ) →
      let δ := 2*((Real.log (B z))^5/Real.sqrt (B z))
      let u := fun i => B (largestPrimeFactor (p.left i-1))/B z
      let v := fun i => B (largestPrimeFactor (p.right i-1))/B z
      (∀ i, |u i-v i| ≤ (2*(i.val : ℝ)+1)*δ) →
      let label := fun i => collisionGridIndex δ (u i) (v i)
      pairedGridUpper δ ((L+U)/(2*B z)) label 1 ≤ 
        1-(1/(80*A^3))/(Real.log (B z))^3 ∧
      (∀ i : Fin b, ∀ hi : i.val+1 < b,
        max (u ⟨i.val+1,hi⟩) (v ⟨i.val+1,hi⟩)+
          (2*(i.val : ℝ)+8)*δ < min (u i) (v i)) := by
  have hγ : 0 < 1/(80*A^3) := by positivity
  filter_upwards [ppt_normal_factor_loss_mesh,
    B_tendsto.eventually (ppt_local_contracted_grid_separation hA),
    B_tendsto.eventually (ppt_local_contracted_first_loss hA),
    B_tendsto.eventually (ppt_terminal_first_cutoff_loss hγ),
    B_tendsto.eventually (ppt_log_dimension_separation hA),
    B_tendsto.eventually (eventually_gt_atTop (1 : ℝ)),
    eventually_ge_atTop (Real.exp 1)] with z hfactor hgap hfirst hterminal hseparation hB hz
  intro b H S L U ω p hb hbH hdim hS hBS hSz hp hp3 hpz hω hω1 hlarge
    hcontract hLU hU
  dsimp only
  let δ := 2*((Real.log (B z))^5/Real.sqrt (B z))
  let u := fun i => B (largestPrimeFactor (p.left i-1))/B z
  let v := fun i => B (largestPrimeFactor (p.right i-1))/B z
  intro halign
  let label := fun i => collisionGridIndex δ (u i) (v i)
  have hB0 : 0 < B z := zero_lt_one.trans hB
  have hH : 1 ≤ H := by omega
  have hδ : 0 < δ := by
    have hlog : 0 < Real.log (B z) := Real.log_pos hB
    dsimp only [δ]
    positivity
  have hH0 : (0 : ℝ) < H := by exact_mod_cast (zero_lt_one.trans_le hH)
  have hω0 : 0 < ω := (by positivity : 0 < 1/(10*(H : ℝ)^3)).trans_le hω
  have hden : 0 < 1+ω := by linarith only [hω0]
  have hfactor' (i : Fin b) : B (p.left i)/B z-δ ≤ u i ∧ u i ≤ B (p.left i)/B z :=
    hfactor (p.left i) S (hp3 i) hS hBS hSz (hp i) (hpz i)
  have hcontract' (i : Fin b) (hi : i.val+1 < b) :
      B (p.left ⟨i.val+1,hi⟩)/B z ≤ (B (p.left i)/B z)/(1+ω) := by
    have hh := div_le_div_of_nonneg_right (hcontract i hi) hB0.le
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hnormalizedLower (i : Fin b) : 1/(B z)^(1/3 : ℝ) ≤ B (p.left i)/B z := by
    have he : (B z)^(2/3 : ℝ)/B z = 1/(B z)^(1/3 : ℝ) := by
      calc
        _ = (B z)^(2/3 : ℝ)/(B z)^(1 : ℝ) := by rw [Real.rpow_one]
        _ = (B z)^(-(1/3 : ℝ)) := by rw [← Real.rpow_sub hB0]; norm_num
        _ = _ := by rw [Real.rpow_neg hB0.le]; simp only [one_div]
    rw [← he]
    exact div_le_div_of_nonneg_right (hlarge i) hB0.le
  have hnonneg (i : Fin b) : 0 ≤ u i ∧ 0 ≤ v i := by
    have hiH : (i.val : ℝ) ≤ H := by exact_mod_cast (show i.val ≤ H by omega)
    have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
    have hcube : 1 ≤ (H : ℝ)^3 := one_le_pow₀ hHr
    have hthird : 0 < (B z)^(1/3 : ℝ) := Real.rpow_pos_of_pos hB0 _
    have hsmall : (2*(i.val : ℝ)+2)*δ < 1/(B z)^(1/3 : ℝ) := by
      have hsep : (8*(H : ℝ)+20)*δ < 1/(40*(H : ℝ)^3*(B z)^(1/3 : ℝ)) := by
        simpa only [mul_div_assoc] using hseparation H hH hdim
      have hfrac : 1/(40*(H : ℝ)^3*(B z)^(1/3 : ℝ)) ≤ 1/(B z)^(1/3 : ℝ) :=
        one_div_le_one_div_of_le hthird
          (by
            have hh := mul_le_mul_of_nonneg_right hcube hthird.le
            nlinarith only [hh,hthird])
      exact (mul_le_mul_of_nonneg_right (by linarith only [hiH,hHr]) hδ.le).trans_lt
        (hsep.trans_le hfrac)
    have hleft := (hfactor' i).1
    have hlower := hnormalizedLower i
    have hpair := (abs_le.mp (halign i)).2
    have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
    constructor <;> nlinarith only [hsmall,hleft,hlower,hpair,hδ,hi0]
  constructor
  · by_cases hb2 : 1 < b
    · have hhead := prime_coordinate_endpoint_bound (hp3 ⟨0,hb⟩) hz (hpz ⟨0,hb⟩)
      have hhead' : B (p.left ⟨0,hb⟩)/B z ≤ 1+1/B z := by
        apply (div_le_iff₀ hB0).mpr
        have he : (1+1/B z)*B z = B z+1 := by field_simp
        rw [he]
        exact hhead
      have hfirstPrime : B (p.left ⟨1,hb2⟩)/B z ≤ (1+1/B z)/(1+ω) :=
        (hcontract' ⟨0,hb⟩ hb2).trans (div_le_div_of_nonneg_right hhead' hden.le)
      have hround := (collision_grid_enclosure hδ (hnonneg ⟨1,hb2⟩).1
        (hnonneg ⟨1,hb2⟩).2 (halign ⟨1,hb2⟩)).2.2.2.2
      have hrounded : pairedGridUpper δ ((L+U)/(2*B z)) label 1 ≤ 
          B (p.left ⟨1,hb2⟩)/B z+(2*(H : ℝ)+3)*δ := by
        have hcoeff : (5 : ℝ) ≤ 2*(H : ℝ)+3 := by
          have hh : (1 : ℝ) ≤ H := by exact_mod_cast hH
          linarith only [hh]
        have hc := mul_le_mul_of_nonneg_right hcoeff hδ.le
        have hf := (hfactor' ⟨1,hb2⟩).2
        simp only [pairedGridUpper,one_ne_zero,ite_false, if_false,dite_eq_left hb2]
        dsimp only [label] at hround ⊢
        norm_num only [Nat.cast_one] at hround
        linarith only [hround,hf,hc]
      exact hfirst H ω (B (p.left ⟨1,hb2⟩)/B z)
        (pairedGridUpper δ ((L+U)/(2*B z)) label 1)
        hH hdim hω hω1 hfirstPrime hrounded
    · have he : pairedGridUpper δ ((L+U)/(2*B z)) label 1 = (L+U)/(2*B z) := by
        simp only [pairedGridUpper,one_ne_zero,ite_false, if_false,dite_eq_right hb2]
      rw [he]
      exact hterminal L U hLU hU
  · intro i hi
    have hlower := hnormalizedLower i
    have halign' : |u ⟨i.val+1,hi⟩-v ⟨i.val+1,hi⟩| ≤ 
        (2*(i.val : ℝ)+3)*δ := by
      have hh := halign ⟨i.val+1,hi⟩
      change |u ⟨i.val+1,hi⟩-v ⟨i.val+1,hi⟩| ≤ (2*((i.val+1:ℕ):ℝ)+1)*δ at hh
      have he : 2*((i.val+1:ℕ):ℝ)+1=2*(i.val:ℝ)+3 := by push_cast <;> ring
      rw [he] at hh
      exact hh
    exact hgap H i.val (B (p.left i)/B z) (B (p.left ⟨i.val+1,hi⟩)/B z)
      (u i) (u ⟨i.val+1,hi⟩) ω hH hdim (show i.val ≤ H by omega)
      hlower hω hω1 (hcontract' i hi) (hfactor' i).1 (hfactor' _).2
      (v i) (v ⟨i.val+1,hi⟩) (halign i) halign'

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

/-- The same strict coordinate gap makes the seed-multiplied totient
small, for the fixed seed and any prescribed positive power. -/
theorem ppt_seed_totient_subpower_of_gap (d : ℕ) {A γ ε : ℝ}
    (hA : 0 ≤ A) (hγ : 0 < γ) (hε : 0 < ε) :
    ∀ᶠ z : ℝ in atTop, ∀ (n : ℕ) (p : Fin n → ℕ),
      (∀ i, (p i).Prime) → (n : ℝ) ≤ A*Real.log (B z) →
      (∀ i, B (p i) ≤ B z-γ*B z/(Real.log (B z))^3) →
      ((d*(∏ i, p i).totient : ℕ) : ℝ) ≤ z^ε := by
  filter_upwards [ppt_prime_product_subpower_of_gap hA hγ (half_pos hε),
    (tendsto_rpow_atTop (half_pos hε)).eventually (eventually_ge_atTop (d : ℝ)),
    eventually_gt_atTop (0 : ℝ)] with z hprod hd hz
  intro n p hp hdim hcoords
  have hφ : ((∏ i, p i).totient : ℝ) ≤ z^(ε/2) :=
    (Nat.cast_le.mpr (Nat.totient_le _)).trans (hprod n p hp hdim hcoords)
  calc
    _ = (d : ℝ)*((∏ i, p i).totient : ℝ) := Nat.cast_mul _ _
    _ ≤ z^(ε/2)*z^(ε/2) := mul_le_mul hd hφ (Nat.cast_nonneg _) (Real.rpow_pos_of_pos hz _).le
    _ = z^ε := by rw [← Real.rpow_add hz]; congr 1; ring

/-- A normal prime whose predecessor is smooth at `V` has double
logarithm at most `6 B(V)`.  No bound on the prime itself is assumed. -/
lemma ppt_normal_smooth_prime_coordinate {p : ℕ} {S V : ℝ}
    (hp : IsNormalPrime S p) (hp3 : 3 ≤ p) (hS : 1 < S)
    (hBS : 0 ≤ B S) (hSV : S ≤ V) (hBV : 1 ≤ B V)
    (hsmooth : (largestPrimeFactor (p-1) : ℝ) ≤ V) : B p ≤ 6*B V := by
  have hparts : partBelow (p-1) V = p-1 :=
    partBelow_all_of_largest_le (Nat.sub_pos_of_lt hp.1.one_lt).ne' hsmooth
  have hΩ : ((p-1).primeFactorsList.length : ℝ) ≤ 4*B V := by
    simpa only [hparts] using normal_terminal_omega hp hS hBS hSV
  have hBV0 : 0 < B V := zero_lt_one.trans_le hBV
  have hfactor : B (largestPrimeFactor (p-1)) ≤ B V := by
    have hpone : (1 : ℝ) < largestPrimeFactor (p-1) := by
      exact_mod_cast one_lt_largestPrimeFactor (show 2 ≤ p-1 by omega)
    exact Real.log_le_log (Real.log_pos hpone)
      (Real.log_le_log (zero_lt_one.trans hpone) hsmooth)
  have hlower := largest_factor_doubleLog_lower (show 2 ≤ p-1 by omega)
    (show 0 < 4*B V by positivity) hΩ
  have hlog := Real.log_le_self (show 0 ≤ 4*B V by positivity)
  have hshift := shifted_doubleLog_lower hp3
  linarith only [hlower, hfactor, hlog, hshift, hBV]

/-- The smooth-tail coordinate scale is eventually below half of the
comparison double logarithm. -/
theorem ppt_smooth_height_half_scale : ∀ᶠ t : ℝ in atTop,
    ∀ V : ℝ, B V ≤ 2*t^(2/3 : ℝ) → 6*B V ≤ t/2 := by
  filter_upwards [(tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/3)).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/24)),
    eventually_gt_atTop (0 : ℝ)] with t hsmall ht
  intro V hV
  have he : t^(2/3 : ℝ)/t = t^(-(1/3 : ℝ)) := by
    calc
      _ = t^(2/3 : ℝ)/t^(1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_sub ht]; norm_num
  rw [← he] at hsmall
  have hh := (div_lt_iff₀ ht).mp hsmall
  linarith only [hV, hh]

lemma ppt_half_scale_below_gap : ∀ᶠ t : ℝ in atTop,
    t/2 ≤ t-t/(Real.log t)^3 := by
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2 : ℝ)),
    eventually_gt_atTop (0 : ℝ)] with t hlog ht
  have hlog0 : 0 < Real.log t := by linarith only [hlog]
  have hp : (2 : ℝ) ≤ (Real.log t)^3 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hlog 3
    norm_num at hh ⊢
    linarith only [hh]
  have hfrac : t/(Real.log t)^3 ≤ t/2 := by
    apply (div_le_div_iff₀ (pow_pos hlog0 3) (by norm_num : (0 : ℝ) < 2)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hp ht.le]
  linarith only [hfrac]

/-- A normal small left tail supplies the actual `D=d*φ(a)` power
restriction in Ford's comparison parameters. -/
theorem ppt_normal_small_tail_subpower (d : ℕ) {A ε : ℝ}
    (hA : 0 ≤ A) (hε : 0 < ε) :
    ∀ᶠ z : ℝ in atTop, ∀ (n : ℕ) (p : Fin n → ℕ) (S V : ℝ),
      (n : ℝ) ≤ A*Real.log (B z) → 1 < S → 0 ≤ B S → S ≤ V →
      1 ≤ B V → B V ≤ 2*(B z)^(2/3 : ℝ) →
      (∀ i, IsNormalPrime S (p i)) → (∀ i, 3 ≤ p i) →
      (∀ i, (largestPrimeFactor (p i-1) : ℝ) ≤ V) →
      ((d*(∏ i, p i).totient : ℕ) : ℝ) ≤ z^ε := by
  filter_upwards [ppt_seed_totient_subpower_of_gap d hA (by norm_num : (0 : ℝ) < 1) hε,
    B_tendsto.eventually ppt_smooth_height_half_scale,
    B_tendsto.eventually ppt_half_scale_below_gap] with z hsmall hhalf hgap
  intro n p S V hdim hS hBS hSV hBV hV hp hp3 hsmooth
  apply hsmall n p (fun i => (hp i).1) hdim
  intro i
  have hh := (ppt_normal_smooth_prime_coordinate (hp i) (hp3 i) hS hBS hSV hBV
    (hsmooth i)).trans ((hhalf V hV).trans hgap)
  simpa only [one_mul] using hh

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTTruncatedCoordinates
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Preserve the actual terminal-prefix coordinates through cancellation. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

/-- The common canceled factor contains no leading prime. Its size is
bounded by the actual nonleading prime product, before any asymptotic estimate. -/
lemma ppt_canceled_prefix_factor_le_tail {k l J : ℕ}
    (p : Fin k → ℕ) (q : Fin l → ℕ) (hJp : J ≤ k) (hJq : J ≤ l)
    (hJ : 0 < J) (hp : ∀ i, 1 ≤ p i)
    (hfirst : p ⟨0,hJ.trans_le hJp⟩ ≠ q ⟨0,hJ.trans_le hJq⟩) :
    pptCanceledPrimeProduct (pptPrimePrefix p hJp) (pptPrimePrefix q hJq) ≤ 
      ∏ i ∈ Finset.univ.filter (fun i : Fin k => 0 < i.val), p i := by
  classical
  let I := pptEqualCoordinates (pptPrimePrefix p hJp) (pptPrimePrefix q hJq)
  let e : Fin J ↪o Fin k := Fin.castLEOrderEmb hJp
  have hsub : I.image e ⊆ Finset.univ.filter (fun i : Fin k => 0 < i.val) := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    by_contra hbad
    have hj0 : j.val = 0 := by change ¬0 < j.val at hbad; omega
    have hjz : j = ⟨0,hJ⟩ := Fin.ext hj0
    have heq := (Finset.mem_filter.mp hj).2
    apply hfirst
    rw [hjz] at heq
    change p ((⟨0,hJ⟩ : Fin J).castLE hJp)=q ((⟨0,hJ⟩ : Fin J).castLE hJq) at heq
    have hp0 : (⟨0,hJ⟩ : Fin J).castLE hJp=⟨0,hJ.trans_le hJp⟩ := Fin.ext rfl
    have hq0 : (⟨0,hJ⟩ : Fin J).castLE hJq=⟨0,hJ.trans_le hJq⟩ := Fin.ext rfl
    rwa [hp0,hq0] at heq
  have hprod : pptCanceledPrimeProduct (pptPrimePrefix p hJp) (pptPrimePrefix q hJq) =
      ∏ i ∈ I.image e, p i := by
    rw [Finset.prod_image]
    · rfl
    · exact fun i _ j _ hij => e.injective hij
  rw [hprod]
  exact Finset.prod_le_prod_of_subset_of_one_le hsub (fun _ _ => Nat.zero_le _)
    (fun i _ _ => hp i)

/-- Choose the finite terminal-window label and the actual unequal-list
preimage prefix together. This is applied to a regular chosen preimage;
it does not posit an alternative factorization or a comparison count. -/
theorem ppt_regular_preimage_terminal {A : ℝ} (hA : 0 < A) :
    ∀ᶠ z : ℝ in atTop,
    ∀ (N H d F : ℕ) (p : Fin N → ℕ) (S : ℝ), ∀ hN : 0 < N,
      0 < d → 0 < F → N ≤ H → (H : ℝ) ≤ A*Real.log (B z) →
      2 ≤ S → 0 ≤ B S → B S ≤ (H : ℝ)^4 →
      (∀ i, IsNormalPrime S (p i)) → (∀ i, 3 ≤ p i) → StrictAnti p →
      F.totient = d*(∏ i, p i).totient → (largestPrimeFactor d : ℝ) ≤ S →
      SquarefreeAbove F S →
      (∀ q : ℕ, q.Prime → q ∣ F → IsNormalPrime S q) →
      largestPrimeFactor F ≠ p ⟨0,hN⟩ →
      (∀ i, (p i-1 : ℕ) ≤ z) → (F.totient : ℝ) ≤ z →
      2*(B z)^(2/3 : ℝ) < B (p ⟨0,hN⟩) →
      ∃ j : Fin (N+1), ∃ J : ℕ,
        let L := (B z)^(2/3 : ℝ)+2*(j.val : ℝ)*
          ((B z)^(2/3 : ℝ)/(2*((N : ℝ)+1)))
        let U := (B z)^(2/3 : ℝ)+(2*(j.val : ℝ)+1)*
          ((B z)^(2/3 : ℝ)/(2*((N : ℝ)+1)))
        let V := Real.exp (Real.exp ((L+U)/2))
        (B z)^(2/3 : ℝ) ≤ L ∧ U ≤ 2*(B z)^(2/3 : ℝ) ∧
        (0 < J ∧ J ≤ N) ∧ L < U ∧
        (∀ i : Fin N, i.val < J → U < B (p i)) ∧
        (∀ i : Fin N, J ≤ i.val → B (p i) < L) ∧
        (2*(H : ℝ)+1)*Real.sqrt (B S*B z)+B S+
          (8*(H : ℝ)+20)*(2*((Real.log (B z))^5/Real.sqrt (B z)))*B z < (U-L)/4 ∧
        ∃ (l : ℕ) (q : Fin l → ℕ) (E : ℕ) (hJl : J ≤ l),
          S ≤ Real.exp (Real.exp L) ∧ 0 < E ∧
          (largestPrimeFactor E : ℝ) ≤ S ∧ StrictAnti q ∧
          (∀ i, IsNormalPrime S (q i) ∧ 3 ≤ q i) ∧
          d*shiftedProduct p = E*shiftedProduct q ∧
          (∀ hJ : 0 < J, p ⟨0,hN⟩ ≠
            q ⟨0,hJ.trans_le hJl⟩) ∧
          (∀ i : Fin N, J ≤ i.val → (largestPrimeFactor (p i-1) : ℝ) ≤ V) ∧
          (∀ i : Fin l, i.val < J → V < (q i-1 : ℕ)) ∧
          (∀ i : Fin l, J ≤ i.val → (largestPrimeFactor (q i-1) : ℝ) ≤ V) ∧
          (∀ i : Fin l, (q i-1 : ℕ) ≤ z) := by
  filter_upwards [B_tendsto.eventually (ppt_select_terminal_window hA),
    ppt_terminal_window_preimage,
    B_tendsto.eventually ppt_smooth_height_half_scale,
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))]
    with z hwindow hpreimage hsmall hB
  intro N H d F p S hN hd hF hNH hdim hS hBS hheight hp hp3 hpa hvalue hDS
    hsq hnormal hmismatch hpz hsize hhead
  have hH : 1 ≤ H := by omega
  have hanti : Antitone (fun i => B (p i)) := by
    intro i j hij
    exact ppt_B_mono (by exact_mod_cast (show 1 < p j by have := hp3 j; omega))
      (Nat.cast_le.mpr (hpa.antitone hij))
  obtain ⟨j,J,hL,hU,hJ,hJN,hhigh,hlow,hbudget⟩ :=
    hwindow N H (fun i => B (p i)) (B S) hN hanti hNH hH hdim hBS hheight hhead
  let L := (B z)^(2/3 : ℝ)+2*(j.val : ℝ)*
    ((B z)^(2/3 : ℝ)/(2*((N : ℝ)+1)))
  let U := (B z)^(2/3 : ℝ)+(2*(j.val : ℝ)+1)*
    ((B z)^(2/3 : ℝ)/(2*((N : ℝ)+1)))
  have hLU : L < U := by
    have hwidth : U-L = (B z)^(2/3 : ℝ)/(2*((N : ℝ)+1)) := by dsimp only [L,U] <;> ring
    rw [← sub_pos,hwidth]
    positivity
  have hUt : 2*(B z)^(2/3 : ℝ) ≤ B z := by
    have hT : 0 ≤ (B z)^(2/3 : ℝ) := Real.rpow_nonneg hB.le _
    have hh := hsmall (Real.exp (Real.exp ((B z)^(2/3 : ℝ))))
      (by rw [B_exp_exp]; linarith only [hT])
    rw [B_exp_exp] at hh
    linarith only [hh,hB,hT]
  obtain ⟨l,q,E,hJl,hSW,hE,hES,hqa,hq,heq,hfirst,hptail,hqhigh,hqtail,hqz⟩ :=
    hpreimage N H J d F p S L U hJ hJN hd hF hNH hS hBS hp hp3 hpa hvalue
      hDS hsq hnormal hmismatch hpz hsize hL hU hLU hUt hhigh hlow hbudget
  refine ⟨j,J,hL,hU,⟨hJ,hJN⟩,hLU,hhigh,hlow,hbudget,l,q,E,hJl,
    hSW,hE,hES,hqa,hq,heq,?_,hptail,hqhigh,hqtail,hqz⟩
  intro hJ'
  exact hfirst

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTSelectedGrid
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct the actual finite comparison label after terminal selection. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

lemma ppt_seed_tail_largest_le {d h : ℕ} (tail : Fin h → ℕ) {S V : ℝ}
    (hV : 1 ≤ V) (hSV : S ≤ V) (hseed : (largestPrimeFactor d : ℝ) ≤ S)
    (hp : ∀ i, (tail i).Prime) (hinj : Function.Injective tail)
    (hsmall : ∀ i, (largestPrimeFactor (tail i-1) : ℝ) ≤ V) :
    (largestPrimeFactor (d*(∏ i,tail i).totient) : ℝ) ≤ V := by
  have hnat : largestPrimeFactor (d*(∏ i,tail i).totient) ≤ ⌊V⌋₊ := by
    apply largestPrimeFactor_mul_le (Nat.le_floor (hseed.trans hSV))
    rw [ppt_totient_primeProduct tail hp hinj]
    apply largestPrimeFactor_prod_le _ _ (Nat.le_floor (by simpa only [Nat.cast_one] using hV))
    intro i _
    exact Nat.le_floor (hsmall i)
  exact (Nat.cast_le.mpr hnat).trans (Nat.floor_le (zero_le_one.trans hV))

/-- A retained prime above the vacant window has predecessor above
the middle cutoff. This does not require any right-coordinate alignment. -/
theorem ppt_terminal_retained_predecessor : ∀ᶠ z : ℝ in atTop,
    ∀ (p H : ℕ) (S L U : ℝ), 3 ≤ p → 1 < S → 0 ≤ B S → S ≤ z →
      IsNormalPrime S p → (p-1 : ℕ) ≤ z → U < B p →
      (8*(H : ℝ)+20)*(2*((Real.log (B z))^5/Real.sqrt (B z)))*B z < (U-L)/4 →
      Real.exp (Real.exp ((L+U)/2)) ≤ (p-1 : ℕ) := by
  filter_upwards [ppt_normal_factor_loss_mesh,
    B_tendsto.eventually (eventually_gt_atTop (1 : ℝ))] with z hfactor hB
  intro p H S L U hp3 hS hBS hSz hp hpz hhigh hbudget
  let δ := 2*((Real.log (B z))^5/Real.sqrt (B z))
  have hB0 : 0 < B z := zero_lt_one.trans hB
  have hδ : 0 ≤ δ := by
    have hlog : 0 < Real.log (B z) := Real.log_pos hB
    dsimp only [δ]
    positivity
  have hc : δ*B z < (U-L)/4 := by
    have hh : 1 ≤ 8*(H : ℝ)+20 := by
      have := Nat.cast_nonneg (α := ℝ) H
      linarith only [this]
    have hle := mul_le_mul_of_nonneg_right hh (mul_nonneg hδ hB0.le)
    change (8*(H : ℝ)+20)*δ*B z < _ at hbudget
    nlinarith only [hle,hbudget]
  have hh := mul_le_mul_of_nonneg_right (hfactor p S hp3 hS hBS hSz hp hpz).1 hB0.le
  change (B p/B z-δ)*B z ≤ (B (largestPrimeFactor (p-1))/B z)*B z at hh
  rw [sub_mul,div_mul_cancel₀ _ hB0.ne',div_mul_cancel₀ _ hB0.ne'] at hh
  have hm : (L+U)/2 < B (largestPrimeFactor (p-1)) := by
    have hp : 0 ≤ δ*B z := mul_nonneg hδ hB0.le
    linarith only [hh,hhigh,hc,hp]
  have hlp : (1 : ℝ) < largestPrimeFactor (p-1) := by
    exact_mod_cast one_lt_largestPrimeFactor (show 2 ≤ p-1 by omega)
  have he := Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hm.le)
  rw [exp_exp_doubleLog hlp] at he
  exact he.trans (Nat.cast_le.mpr (largestPrimeFactor_le_self (by omega)))

/-- The selected actual prefix yields a finite arithmetic label and the
literal comparison data, including its strict exponent. All size,
normality and geometric assumptions concern the original candidate and
the chosen preimage; no bound for a residual family is assumed. -/
theorem ppt_selected_grid_data (d : ℕ) (hd : 0 < d) {A : ℝ} (hA : 0 < A) :
    ∀ᶠ z : ℝ in atTop,
    ∀ (m n N Q J H E r j : ℕ) (p : Fin N → ℕ) (q : Fin Q → ℕ)
      (v : Fin n → ℝ) (ι : Fin N ↪o Fin n) (budget g S L U V : ℝ),
      ∀ hJ : 0 < J, ∀ hJN : J ≤ N, ∀ hJQ : J ≤ Q,
      n ≤ m → N ≤ H → j ≤ H → (H : ℝ) ≤ A*Real.log (B z) →
      m-(ι ⟨0,hJ.trans_le hJN⟩).val ≤ H →
      v ∈ relaxedGeometricFamily m n budget g → (∀ i,v (ι i)=B (p i)) →
      Real.exp (Real.exp 1) ≤ S → B S ≤ (H : ℝ)^4 →
      V=Real.exp (Real.exp ((L+U)/2)) → S ≤ V → V ≤ z →
      (B z)^(2/3 : ℝ) ≤ L → L < U → U ≤ 2*(B z)^(2/3 : ℝ) →
      (largestPrimeFactor d : ℝ) ≤ S →
      (∀ i, IsNormalPrime S (p i)) → (∀ i, IsNormalPrime S (q i)) →
      (∀ i, 3 ≤ p i) → (∀ i, 3 ≤ q i) → StrictAnti p → StrictAnti q →
      p ⟨0,hJ.trans_le hJN⟩ ≠ q ⟨0,hJ.trans_le hJQ⟩ →
      r=∏ i,p i → d*shiftedProduct p=E*shiftedProduct q → 0 < E →
      (largestPrimeFactor E : ℝ) ≤ S →
      (∀ i : Fin N,i.val < J → U < B (p i)) →
      (∀ i : Fin Q,i.val < J → V ≤ (q i-1 : ℕ)) →
      (∀ i : Fin N,J ≤ i.val → (largestPrimeFactor (p i-1):ℝ) ≤ V) →
      (∀ i : Fin Q,J ≤ i.val → (largestPrimeFactor (q i-1):ℝ) ≤ V) →
      (∀ i,(p i-1:ℕ) ≤ z) → (∀ i,(q i-1:ℕ) ≤ z) →
      ((d*r.totient:ℕ):ℝ) ≤ z → SquarefreeAbove (d*r.totient) S →
      (∀ i,p i ≤ discardPrimeBound (B z)) →
      (((∏ i ∈ Finset.univ.filter (fun i : Fin N => 0 < i.val),p i):ℕ):ℝ) ≤ z^(1/10:ℝ) →
      z^(9/10:ℝ) ≤ p ⟨0,hJ.trans_le hJN⟩ →
      (8*(H:ℝ)+20)*(2*((Real.log (B z))^5/Real.sqrt (B z)))*B z < (U-L)/4 →
      let δ := 2*((Real.log (B z))^5/Real.sqrt (B z))
      let ζ := (L+U)/(2*B z)
      let θ := pptUniformHeadEdge (B z)-δ
      ∃ (b h s c a : ℕ) (pair : ShiftedPair b) (tail : Fin h → ℕ) (grid : Fin b → ℕ),
        let ν := pairedGridUpper δ ζ grid
        let μ := pptGridLower δ θ grid
        0 < b ∧ b ≤ H ∧ h ≤ H ∧
        pptResidualLabel b h s c a j grid ∈
          pptResidualLabels (discardPrimeBound (B z)) H δ ∧
        a=∏ i,tail i ∧ Function.Injective tail ∧
        (∀ i,IsNormalPrime S (tail i) ∧ (largestPrimeFactor (tail i-1):ℝ) ≤ V) ∧
        r=c*a*∏ i,pair.left i ∧
        FordComparisonParameters b z S (d*a.totient) c.totient
          (comparisonCutoffs z ν) (comparisonCutoffs z μ) ∧
        FordComparisonConditions b z S (d*a.totient) c.totient
          (comparisonCutoffs z ν) (comparisonCutoffs z μ) pair ∧
        -2+(∑ i ∈ Finset.Icc 1 (b-1),TotientAsymptotic.a i*(B (comparisonCutoffs z ν i)/B z))+
          comparisonError b z S (comparisonCutoffs z ν) (comparisonCutoffs z μ) ≤ 
          -1-(1/(80*A^3))/(Real.log (B z))^3 := by
  have hγ : 0 < 1/(80*A^3) := by positivity
  filter_upwards [ppt_terminal_retained_predecessor, ppt_pair_alignment_in_mesh hA,
    ppt_geometric_pair_grid hA, ppt_pointwise_grid_realization hA hγ,
    ppt_geometric_pair_exponent hA,
    ppt_normal_small_tail_subpower d hA.le (by norm_num : (0:ℝ) < 1/100),
    B_tendsto.eventually (ppt_local_normality_error_mesh hA),
    B_tendsto.eventually (eventually_gt_atTop (1:ℝ))]
    with z hretained halign hgeometry hgrid hexponent hsmall hmesh hB
  intro m n N Q J H E r j p q v ι budget g S L U V hJ hJN hJQ hnm hNH hjH
    hdim hremaining hgeom hcoords hS hheight hV hSV hVz hL hLU hU hseed hp hq
    hp3 hq3 hpa hqa hfirst hr heq hE hES hpHigh hqHigh hpLow hqLow hpz hqz
    hsize hsq hpBound hcommon hhead hbudget
  dsimp only
  have hB0 : 0 < B z := zero_lt_one.trans hB
  have hS1 : 1 < S := (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)).trans_le hS
  have hBS : 0 ≤ B S := by
    have hh := ppt_B_mono (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)) hS
    have hh' : (1 : ℝ) ≤ B S := by simpa only [B,Real.log_exp] using hh
    exact (by norm_num : (0 : ℝ) ≤ 1).trans hh'
  have hV1 : 1 < V := hS1.trans_le hSV
  have hBV : B V=(L+U)/2 := by rw [hV,B_exp_exp]
  have hL1 : 1 ≤ L := by
    have hh : 1 ≤ (B z)^(2/3:ℝ) := Real.one_le_rpow hB.le (by norm_num)
    exact hh.trans hL
  have hBV1 : 1 ≤ B V := by rw [hBV]; linarith only [hL1,hLU]
  have hBVupper : B V ≤ 2*(B z)^(2/3:ℝ) := by rw [hBV]; linarith only [hLU,hU]
  have hpV (i : Fin N) (hi : i.val < J) : V ≤ (p i-1:ℕ) := by
    rw [hV]
    exact hretained (p i) H S L U (hp3 i) hS1 hBS (hSV.trans hVz)
      (hp i) (hpz i) (hpHigh i hi) hbudget
  obtain ⟨b,h,s,c,a,pair,tail,hb,hbJ,hhN,hsJ,hc,ha,hreal,hclabel,halabel,
    hatail,htailinj,htail,htailindices,hpair,hpairAnti,hpairAnti',hrem,hremV,
    hequation,hpairSize,hpairSq,hcdef,hembed,_hleftEmbed,hheadData⟩ :=
    ppt_actual_truncated_block p q hJN hJQ hJ hp hq hpa hqa hp3 hq3 hfirst hr heq
      hE hV1.le (hES.trans hSV) hpLow hqLow hsize hsq hpBound
  let e := hembed.choose
  have he := hembed.choose_spec
  have hheadEq : pair.left ⟨0,hb⟩=p ⟨0,hJ.trans_le hJN⟩ := hheadData.choose_spec
  have hbH : b ≤ H := hbJ.trans (hJN.trans hNH)
  have hhH : h ≤ H := hhN.trans hNH
  have hsH : s ≤ H := hsJ.trans (hJN.trans hNH)
  have hpairPred (i : Fin b) : (pair.left i-1:ℕ) ≤ z ∧ (pair.right i-1:ℕ) ≤ z := by
    rw [(he i).1,(he i).2]
    exact ⟨hpz _,hqz _⟩
  have hpairV (i : Fin b) : V ≤ (pair.left i-1:ℕ) ∧ V ≤ (pair.right i-1:ℕ) := by
    rw [(he i).1,(he i).2]
    exact ⟨hpV _ (e i).isLt,hqHigh _ (e i).isLt⟩
  have hpairHigh (i : Fin b) : U < B (pair.left i) := by
    rw [(he i).1]
    exact hpHigh _ (e i).isLt
  have htail3 (i : Fin h) : 3 ≤ tail i := by
    obtain ⟨k,_,hk⟩ := htailindices i
    rw [hk]
    exact hp3 k
  have hDsmall : ((d*a.totient:ℕ):ℝ) ≤ z^(1/100:ℝ) := by
    rw [hatail]
    exact hsmall h tail S V ((Nat.cast_le.mpr hhH).trans hdim) hS1 hBS hSV hBV1
      hBVupper (fun i => (htail i).1) htail3 (fun i => (htail i).2)
  have hDV : (largestPrimeFactor (d*a.totient):ℝ) ≤ V := by
    rw [hatail]
    exact ppt_seed_tail_largest_le tail hV1.le hSV hseed
      (fun i => (htail i).1.1) htailinj (fun i => (htail i).2)
  have hcsmall : (c.totient:ℝ) ≤ z^(1/10:ℝ) := by
    apply (Nat.cast_le.mpr (Nat.totient_le c)).trans
    apply le_trans _ hcommon
    rw [hcdef]
    exact Nat.cast_le.mpr (ppt_canceled_prefix_factor_le_tail p q hJN hJQ hJ
      (fun i => (hp i).1.one_le) hfirst)
  let f : Fin b ↪o Fin n := (e.trans (Fin.castLEOrderEmb hJN)).trans ι
  have hfcoords (i : Fin b) : v (f i)=B (pair.left i) := by
    rw [(he i).1]
    exact hcoords _
  have hezero : (e ⟨0,hb⟩).val=0 := by
    have hx : p ((e ⟨0,hb⟩).castLE hJN)=p ⟨0,hJ.trans_le hJN⟩ := by
      rw [←(he ⟨0,hb⟩).1]
      exact hheadEq
    have hh := congrArg Fin.val (hpa.injective hx)
    exact hh
  have hfremaining : m-(f ⟨0,hb⟩).val ≤ H := by
    have hfzero : f ⟨0,hb⟩=ι ⟨0,hJ.trans_le hJN⟩ := by
      apply congrArg ι
      exact Fin.ext hezero
    rw [hfzero]
    exact hremaining
  have hcontract := ppt_geometric_embedded_contraction hgeom hnm f hb hfremaining
  let ω : ℝ := 1/(10*(H:ℝ)^3)
  have hleftContract (i : Fin b) (hi : i.val+1 < b) :
      B (pair.left ⟨i.val+1,hi⟩) ≤ B (pair.left i)/(1+ω) := by
    have hh := hcontract.2 i ⟨i.val+1,hi⟩ (by change i.val < i.val+1; omega)
    simpa only [hfcoords] using hh
  have hpairAlign := halign b H (d*a.totient) S V pair hdim hS1 hBS hheight hSV hVz
    (Nat.mul_pos hd (Nat.totient_pos.mpr ha)) hrem
    (fun i => ⟨(hpair i).1,(hpair i).2.1⟩)
    (fun i => ⟨(hpair i).2.2.1,(hpair i).2.2.2.1⟩)
    hpairAnti.antitone hpairAnti'.antitone hequation hDV hremV hpairV hpairPred
  obtain ⟨hfirstGrid,hgaps⟩ := hgeometry b H S L U ω pair hb hbH hdim hS1 hBS
    (hSV.trans hVz) (fun i => (hpair i).1) (fun i => (hpair i).2.2.1)
    (fun i => (hpairPred i).1) le_rfl hcontract.1
    (fun i => hL.trans (hLU.le.trans (hpairHigh i).le)) hleftContract hLU.le hU hpairAlign
  let δ := 2*((Real.log (B z))^5/Real.sqrt (B z))
  let u := fun i => B (largestPrimeFactor (pair.left i-1))/B z
  let w := fun i => B (largestPrimeFactor (pair.right i-1))/B z
  let grid := fun i => collisionGridIndex δ (u i) (w i)
  let ν := pairedGridUpper δ ((L+U)/(2*B z)) grid
  let μ := pptGridLower δ (pptUniformHeadEdge (B z)-δ) grid
  have hgridData := hgrid b H (d*a.totient) c S V L U pair hb hbH hdim hS hheight
    hV hSV hVz (Nat.mul_pos hd (Nat.totient_pos.mpr ha)) hc hrem hDsmall hcsmall
    (fun i => ⟨(hpair i).1,(hpair i).2.1⟩)
    (fun i => ⟨(hpair i).2.2.1,(hpair i).2.2.2⟩)
    hpairAnti.antitone hpairAnti'.antitone hequation hpairSize
    (ppt_squarefreeAbove_mono hSV hpairSq) hDV hremV hpairV hpairPred
    (by rw [hheadEq]; exact hhead) (zero_le_one.trans hL1) (hpairHigh _)
    hbudget hfirstGrid hgaps
  obtain ⟨hgridmem,hparams,hconditions,hround,hwidth⟩ := hgridData
  have hδ : 0 ≤ δ := by
    have hlog : 0 ≤ Real.log (B z) := (Real.log_pos hB).le
    dsimp only [δ]
    positivity
  have hη : Real.sqrt (B S/B z) ≤ δ := by
    have hh := hmesh H S hdim hBS hheight
    dsimp only [δ]
    have hm : 0 ≤ (Real.log (B z))^5/Real.sqrt (B z) := by
      have hlog0 := (Real.log_pos hB).le
      positivity
    linarith only [hh,hm]
  have hrow : m-((f ⟨0,hb⟩).val+1)+1 ≤ H := by
    have hi := (f ⟨0,hb⟩).isLt
    omega
  have hExp := hexponent m n b H budget g S ((2*(b:ℝ)+3)*δ) ((2*(b:ℝ)+3)*δ)
    δ pair v f ν μ hb hgeom (fun i => (hpair i).2.2.1) (hpairPred _).1
    hfcoords (by omega) hbH hrow hdim hδ le_rfl
    (by nlinarith only [hδ]) (by have hb0 : (0:ℝ) ≤ b := Nat.cast_nonneg b; nlinarith only [hδ,hb0])
    hη hround hwidth
  refine ⟨b,h,s,c,a,pair,tail,grid,hb,hbH,hhH,?_,hatail,htailinj,htail,hreal,
    hparams,hconditions,hExp⟩
  exact ppt_residual_label_mem hbH hhH hsH hjH hgridmem halabel hclabel

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTRegularWitness
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Build a counted grid witness from an actual regular totient preimage. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

/-- The large-head conclusion used by the comparison also places the
first prime above every terminal window. -/
theorem ppt_large_head_above_terminal : ∀ᶠ z : ℝ in atTop,
    ∀ p : ℕ, z^(9/10:ℝ) ≤ p → 2*(B z)^(2/3:ℝ) < B p := by
  filter_upwards [B_tendsto.eventually ppt_smooth_height_half_scale,
    B_tendsto.eventually (eventually_ge_atTop (2:ℝ)),eventually_gt_atTop (1:ℝ)]
    with z hsmall hB hz
  intro p hhead
  have hz0 : 0 < z := zero_lt_one.trans hz
  have ht : 0 < B z := (by norm_num : (0:ℝ) < 2).trans_le hB
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos hz0 _) hhead
  rw [Real.log_rpow hz0] at hlog
  have hdouble := Real.log_le_log (mul_pos (by norm_num : (0:ℝ) < 9/10) (Real.log_pos hz)) hlog
  rw [Real.log_mul (by norm_num : (9/10:ℝ)≠0) (Real.log_pos hz).ne'] at hdouble
  change Real.log (9/10:ℝ)+B z ≤ B p at hdouble
  have hlogfrac : -1 ≤ Real.log (9/10:ℝ) := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 9/10)
    norm_num at hh ⊢
    linarith only [hh]
  have hT : 1 ≤ (B z)^(2/3:ℝ) := Real.one_le_rpow (by linarith only [hB]) (by norm_num)
  have hh := hsmall (Real.exp (Real.exp ((B z)^(2/3:ℝ))))
    (by rw [B_exp_exp]; linarith only [hT])
  rw [B_exp_exp] at hh
  linarith only [hh,hT,hdouble,hlogfrac]

/-- The finite label cutoff contains every actual prime whose
predecessor divides a value in the current comparison interval. -/
theorem ppt_prime_in_label_range : ∀ᶠ z : ℝ in atTop,
    ∀ p : ℕ, 3 ≤ p → (p-1:ℕ) ≤ z → p ≤ discardPrimeBound (B z) := by
  filter_upwards [B_tendsto.eventually (eventually_ge_atTop (5:ℝ)),
    eventually_ge_atTop (Real.exp 1)] with z hB hz
  intro p hp hpz
  have hcoord := prime_coordinate_endpoint_bound hp hz hpz
  have hlp : (1:ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hcut := (discardPrimeBound_bounds (by linarith only [hB])).2.2.2
  have hheight : B p ≤ (6/5:ℝ)*B z := by linarith only [hcoord,hB]
  have hh := Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hheight)
  rw [exp_exp_doubleLog hlp] at hh
  exact_mod_cast hh.trans hcut

lemma ppt_nonhead_product_succ {k : ℕ} (p : Fin (k+1) → ℕ) :
    (∏ i ∈ Finset.univ.filter (fun i : Fin (k+1) => 0 < i.val),p i)=∏ i:Fin k,p i.succ := by
  classical
  symm
  apply Finset.prod_bij (fun i _=>i.succ)
  · intro i _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp⟩
  · intro i _ j _ hij
    exact Fin.succ_injective _ hij
  · intro j hj
    have hj0 : 0 < j.val := (Finset.mem_filter.mp hj).2
    refine ⟨j.pred (by intro h; subst j; simp at hj0),Finset.mem_univ _,?_⟩
    exact Fin.succ_pred _ _
  · intro i _
    rfl

/-- Every nonleading product in the actual contracting list is a small
power of the local endpoint. This pays for the common canceled factor. -/
theorem ppt_contracted_nonhead_product {A : ℝ} (hA : 0 < A) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ z : ℝ in atTop,∀ (N H : ℕ) (p : Fin N → ℕ) (ω : ℝ),∀ hN : 0 < N,
      (∀ i,(p i).Prime) → (∀ i,3 ≤ p i) → 1 ≤ H → N ≤ H →
      (H:ℝ) ≤ A*Real.log (B z) → 1/(10*(H:ℝ)^3) ≤ ω → ω ≤ 1 →
      (∀ i:Fin N,0 < i.val → B (p i) ≤ B (p ⟨0,hN⟩)/(1+ω)) →
      (p ⟨0,hN⟩-1:ℕ) ≤ z →
      (((∏ i ∈ Finset.univ.filter (fun i:Fin N=>0 < i.val),p i):ℕ):ℝ) ≤ z^ε := by
  have hγ : 0 < 1/(80*A^3) := by positivity
  filter_upwards [B_tendsto.eventually (ppt_local_contracted_first_loss hA),
    ppt_prime_product_subpower_of_gap hA.le hγ hε,
    B_tendsto.eventually (eventually_gt_atTop (1:ℝ)),
    eventually_ge_atTop (Real.exp 1)] with z hgap hsmall hB hz
  intro N H p ω hN hp hp3 hH hNH hdim hω hω1 hcontract hpred
  cases N with
  | zero => omega
  | succ k =>
    have ht : 0 < B z := zero_lt_one.trans hB
    have hH0 : (0:ℝ) < H := by exact_mod_cast (zero_lt_one.trans_le hH)
    have hω0 : 0 < ω := (by positivity : 0 < 1/(10*(H:ℝ)^3)).trans_le hω
    have hden : 0 < 1+ω := by linarith only [hω0]
    have hhead := prime_coordinate_endpoint_bound (hp3 0) hz hpred
    rw [ppt_nonhead_product_succ]
    apply hsmall k (fun i=>p i.succ) (fun i=>hp i.succ)
      ((Nat.cast_le.mpr (show k ≤ H by omega)).trans hdim)
    intro i
    have hu : B (p i.succ)/B z ≤ (1+1/B z)/(1+ω) := by
      calc
        _ ≤ (B (p 0)/(1+ω))/B z :=
          div_le_div_of_nonneg_right (hcontract i.succ (by simp)) ht.le
        _ ≤ ((B z+1)/(1+ω))/B z :=
          div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hhead hden.le) ht.le
        _ = _ := by field_simp
    have hpad : B (p i.succ)/B z ≤ B (p i.succ)/B z+
        (2*(H:ℝ)+3)*(2*((Real.log (B z))^5/Real.sqrt (B z))) := by
      have hl : 0 ≤ Real.log (B z) := (Real.log_pos hB).le
      have he : 0 ≤ (2*(H:ℝ)+3)*(2*((Real.log (B z))^5/Real.sqrt (B z))) := by positivity
      linarith only [he]
    have hh := hgap H ω (B (p i.succ)/B z) (B (p i.succ)/B z)
      hH hdim hω hω1 hu hpad
    have hh' := (div_le_iff₀ ht).mp hh
    convert hh' using 1
    all_goals try with_reducible_and_instances rfl
    ring

/-- An actual regular alternative preimage produces the finite grid
witness consumed by the counting theorem. This is the suffix case, in
which the candidate head itself belongs to the geometric row. -/
theorem ppt_regular_geometric_witness_oai (d : ℕ) (hd : 0 < d) {A : ℝ} (hA : 0 < A) :
    ∀ᶠ z : ℝ in atTop,
    ∀ (m n N H F r : ℕ) (p : Fin N → ℕ) (v : Fin n → ℝ)
      (ι : Fin N ↪o Fin n) (budget c S : ℝ),∀ hN : 0 < N,
      n ≤ m → N ≤ H → (H:ℝ) ≤ A*Real.log (B z) → m-(ι ⟨0,hN⟩).val ≤ H →
      v∈relaxedGeometricFamily m n budget c → (∀ i,v (ι i)=B (p i)) →
      Real.exp (Real.exp 1) ≤ S → B S ≤ (H:ℝ)^4 →
      (∀ i,IsNormalPrime S (p i)) → (∀ i,3 ≤ p i) → StrictAnti p →
      0 < F → F.totient=d*r.totient → r=∏ i,p i →
      (largestPrimeFactor d:ℝ) ≤ S → SquarefreeAbove F S → SquarefreeAbove F.totient S →
      (∀ q:ℕ,q.Prime → q∣F → IsNormalPrime S q) →
      largestPrimeFactor F≠p ⟨0,hN⟩ → (∀ i,(p i-1:ℕ) ≤ z) → (F.totient:ℝ) ≤ z →
      z^(9/10:ℝ) ≤ p ⟨0,hN⟩ → Nonempty (PPTResidualGridWitness d N H z S A r) := by
  filter_upwards [ppt_regular_preimage_terminal hA, ppt_selected_grid_data d hd hA,
    ppt_large_head_above_terminal,ppt_prime_in_label_range,
    ppt_contracted_nonhead_product hA (1/10) (by norm_num),
    B_tendsto.eventually ppt_smooth_height_half_scale,
    B_tendsto.eventually (eventually_gt_atTop (1:ℝ))]
    with z hterminal hselected hheadLarge hprimeRange hnonhead hsmall hB
  intro m n N H F r p v ι budget c S hN hnm hNH hdim hremaining hgeom hcoords
    hS hheight hp hp3 hpa hF hvalue hr hseed hsqF hsqPhi hnormal hmismatch hpz hsize hhead
  have ht : 0 < B z := zero_lt_one.trans hB
  have hH : 1 ≤ H := by omega
  have hS1 : 1 < S := (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)).trans_le hS
  have hS2 : 2 ≤ S := by
    have he : 2 < Real.exp 1 := by linarith only [Real.add_one_lt_exp (by norm_num : (1:ℝ)≠0)]
    have hexp : Real.exp 1 < Real.exp (Real.exp 1) := Real.exp_lt_exp.mpr (by linarith only [he])
    exact (he.trans hexp).le.trans hS
  have hBS : 0 ≤ B S := by
    have hh := ppt_B_mono (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)) hS
    have hh' : (1 : ℝ) ≤ B S := by simpa only [B,Real.log_exp] using hh
    exact (by norm_num : (0 : ℝ) ≤ 1).trans hh'
  have hvalue' : F.totient=d*(∏ i,p i).totient := by rw [←hr]; exact hvalue
  obtain ⟨j,J,hL,hU,⟨hJ,hJN⟩,hLU,hhigh,hlow,hbudget,
    Q,q,E,hJQ,hSL,hE,hES,hqa,hq,heq,hfirst,hptail,hqhigh,hqtail,hqz⟩ :=
    hterminal N H d F p S hN hd hF hNH hdim hS2 hBS hheight hp hp3 hpa
      hvalue' hseed hsqF hnormal hmismatch hpz hsize (hheadLarge _ hhead)
  let L := (B z)^(2/3:ℝ)+2*(j.val:ℝ)*((B z)^(2/3:ℝ)/(2*((N:ℝ)+1)))
  let U := (B z)^(2/3:ℝ)+(2*(j.val:ℝ)+1)*((B z)^(2/3:ℝ)/(2*((N:ℝ)+1)))
  let V := Real.exp (Real.exp ((L+U)/2))
  have hSV : S ≤ V := hSL.trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr
    (by linarith only [hLU])))
  have hUt : 2*(B z)^(2/3:ℝ) ≤ B z := by
    have hT : 0 ≤ (B z)^(2/3:ℝ) := Real.rpow_nonneg ht.le _
    have hh := hsmall (Real.exp (Real.exp ((B z)^(2/3:ℝ))))
      (by rw [B_exp_exp]; linarith only [hT])
    rw [B_exp_exp] at hh
    linarith only [hh,ht,hT]
  have hVz : V ≤ z := by
    have hh : (L+U)/2 ≤ B z := by linarith only [hLU,hU,hUt]
    have he := Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hh)
    have hz1 : 1 < z := by
      have hh := (hpz ⟨0,hN⟩)
      have hp0 := hp3 ⟨0,hN⟩
      have htwo : (2:ℝ) ≤ (p ⟨0,hN⟩-1:ℕ) := by exact_mod_cast (show 2 ≤ p ⟨0,hN⟩-1 by omega)
      linarith only [hh,htwo]
    simpa only [V,exp_exp_doubleLog hz1] using he
  have hcontract := ppt_geometric_embedded_contraction hgeom hnm ι hN hremaining
  let ω : ℝ := 1/(10*(H:ℝ)^3)
  have hnonheadContract (i : Fin N) (hi : 0 < i.val) :
      B (p i) ≤ B (p ⟨0,hN⟩)/(1+ω) := by
    have hh := hcontract.2 ⟨0,hN⟩ i (show (⟨0,hN⟩:Fin N) < i from hi)
    simpa only [hcoords] using hh
  have hnonheadBound := hnonhead N H p ω hN (fun i=>(hp i).1) hp3 hH hNH hdim le_rfl
    hcontract.1 hnonheadContract (hpz ⟨0,hN⟩)
  have htargetSize : ((d*r.totient:ℕ):ℝ) ≤ z := by rw [←hvalue]; exact hsize
  have htargetSq : SquarefreeAbove (d*r.totient) S := by rw [←hvalue]; exact hsqPhi
  have hdiscard : 0 ≤ (2*(H:ℝ)+1)*Real.sqrt (B S*B z)+B S := by positivity
  have hgridBudget : (8*(H:ℝ)+20)*(2*((Real.log (B z))^5/Real.sqrt (B z)))*B z < (U-L)/4 := by
    linarith only [hbudget,hdiscard]
  obtain ⟨b,h,s,cc,a,pair,tail,grid,hb,hbH,hhH,hmem,hatail,htailinj,htail,
    hreal,hparams,hconditions,hExp⟩ :=
    hselected m n N Q J H E r j.val p q v ι budget c S L U V hJ hJN hJQ
      hnm hNH ((Nat.lt_succ_iff.mp j.isLt).trans hNH) hdim hremaining hgeom hcoords
      hS hheight rfl hSV hVz hL hLU hU hseed hp (fun i=>(hq i).1) hp3 (fun i=>(hq i).2)
      hpa hqa (hfirst hJ) hr heq hE hES hhigh (fun i hi=>(hqhigh i hi).le)
      hptail hqtail hpz hqz htargetSize htargetSq (fun i=>hprimeRange _ (hp3 i) (hpz i))
      hnonheadBound hhead hgridBudget
  let ell := pptResidualLabel b h s cc a j.val grid
  have hterm : pptLabelTerminal z N ell=V := rfl
  have htermheight : 0 ≤ B (pptLabelTerminal z N ell) ∧
      B (pptLabelTerminal z N ell) ≤ 2*(B z)^(2/3:ℝ) := by
    rw [hterm]
    change 0 ≤ B (Real.exp (Real.exp ((L+U)/2))) ∧ _
    rw [B_exp_exp]
    have hL0 : 0 ≤ L := (Real.rpow_nonneg ht.le _).trans hL
    constructor <;> linarith only [hL0,hLU,hU]
  have hterminalEq : comparisonCutoffs z (pptLabelUpper z N ell) (pptLabelB ell)=
      pptLabelTerminal z N ell := by
    change comparisonCutoffs z
      (pairedGridUpper (2*((Real.log (B z))^5/Real.sqrt (B z))) ((L+U)/(2*B z)) grid) b=V
    rw [comparisonCutoffs,show pairedGridUpper (2*((Real.log (B z))^5/Real.sqrt (B z)))
      ((L+U)/(2*B z)) grid b=(L+U)/(2*B z) by
        simp [pairedGridUpper,show b≠0 by omega]]
    dsimp only [V]
    congr 2
    field_simp
  exact ⟨{
    label := ell
    length_pos := hb
    length_le := hbH
    tail_length_le := hhH
    label_mem := hmem
    terminal_normality := hSV
    terminal_height := htermheight
    terminal_eq := hterminalEq
    tail := tail
    tail_product := hatail
    tail_injective := htailinj
    tail_normal := fun i=>(htail i).1
    tail_smooth := fun i=>(htail i).2
    pair := pair
    recovery := hreal
    parameters := hparams
    conditions := hconditions
    exponent := hExp
  }⟩

end TotientAsymptotic

end

end OAI
end

theorem solution : type_of% @OAI.TotientAsymptotic.ppt_regular_geometric_witness_oai := @OAI.TotientAsymptotic.ppt_regular_geometric_witness_oai
