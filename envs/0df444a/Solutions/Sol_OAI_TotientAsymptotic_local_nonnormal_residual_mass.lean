-- Prove2me | solution 1 for OAI.TotientAsymptotic.local_nonnormal_residual_mass
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:35:24.155241+00:00
-- url     : https://prove2.me/submissions/078177aa-badb-46d0-af88-b7e38d4d83da

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
import Mathlib.RingTheory.PowerSeries.Inverse
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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_GeometricLowerBudget
attribute [-instance] _root_.instMeasurableSpace
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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalNormalityReciprocalMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual nonnormal-witness counts summed over residual dyadic layers. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem local_nonnormal_witness_mass_rate {A : ℝ} (hA : 0 ≤ A) (K : ℕ) :
    ∀ᶠ h : ℕ in atTop,∀ (d q L : ℕ),0 < d →
      ∀ (R Q : Finset ℕ) (F : ℕ → ℕ),Q ⊆ R →
      (∀ r ∈ Q,1 < d*r.totient ∧ ((d*r.totient:ℕ):ℝ) ≤ (2:ℝ)^L) →
      (∀ r ∈ Q,let z := (2:ℝ)^(Nat.clog 2 (d*r.totient));
        256 ≤ z ∧ 0 ≤ B z ∧ Real.log (B z+4) ≤ A*h) →
      (∀ r ∈ R,∀ p : ℕ,p.Prime → p ∣ r → IsNormalPrime (localNormalityScale h) p) →
      (∀ p : ℕ,p.Prime → p ∣ q → IsNormalPrime (localNormalityScale h) p) →
      (∀ r ∈ R,(∃ s ∈ R,s≠r ∧ s.totient=r.totient) → ∃ s ∈ R,F r=s*q) →
      (∀ r ∈ Q,∃ p : ℕ,p.Prime ∧ p ∣ F r ∧ ¬IsNormalPrime (localNormalityScale h) p) →
      (∀ r ∈ Q,0<F r ∧ (F r).totient=d*r.totient) →
      (∑ r ∈ Q,(r.totient:ℝ)⁻¹) ≤
        (4*d/Real.log 2)*rho^(K*h)*(1+Real.log L) := by
  classical
  filter_upwards [local_nonnormal_witness_count_rate hA K] with h hc
  intro d q L hd R Q F hQR hrange hlocal hR hq hbranch hbad hF
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA' : 0 ≤ rho^(K*h)/Real.log 2 := div_nonneg (pow_pos rho_pos _).le hlog2.le
  have hcount (k : ℕ) (hk : k ∈ Finset.Icc 1 L) :
      ((Q.filter (fun r => Nat.clog 2 (d*r.totient)=k)).card:ℝ) ≤
        (rho^(K*h)/Real.log 2)*(2:ℝ)^k/k := by
    let T := Q.filter (fun r => Nat.clog 2 (d*r.totient)=k)
    by_cases hQ : T.Nonempty
    · obtain ⟨r,hr⟩ := hQ
      have hkr := (Finset.mem_filter.mp hr).2
      have hz := hlocal r (Finset.mem_filter.mp hr).1
      dsimp only at hz
      rw [hkr] at hz
      have hbound := hc ((2:ℝ)^k) d q hz.1 hz.2.1 hz.2.2 hd R T F
        (fun r hr => hQR (Finset.mem_filter.mp hr).1) hR hq hbranch
        (fun r hr => hbad r (Finset.mem_filter.mp hr).1) (by
          intro r hr
          obtain ⟨hr,he⟩ := Finset.mem_filter.mp hr
          refine ⟨(hF r hr).1,(hF r hr).2,?_⟩
          have hh := (dyadic_nat_bounds (hrange r hr).1).2.2
          rwa [he] at hh)
      apply hbound.trans_eq
      rw [dyadic_endpoint_log]
      ring
    · have he : T=∅ := Finset.not_nonempty_iff_eq_empty.mp hQ
      change (T.card:ℝ) ≤ _
      rw [he]
      simp only [Finset.card_empty,Nat.cast_zero]
      positivity
  have hm := residual_dyadic_mass Q d L hA' hrange hcount
  apply hm.trans_eq
  ring

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalExceptionalResidualMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two exceptional witness classes have summable reciprocal mass at
the actual geometric residual scale. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem local_nonnormal_residual_mass_oai {c A : ℝ} (hc : 0 < c) (hA : 0 < A)
    (d q L : ℕ) (hd : 0 < d) :
    ∀ᶠ h : ℕ in atTop,∀ (R Q : Finset ℕ) (F : ℕ → ℕ),Q ⊆ R →
      (∀ r ∈ Q,∃ p : ℕ,p.Prime ∧ p-1 ≤ d*r.totient ∧
        c*(rho^h)⁻¹ ≤ B p ∧ ((d*r.totient:ℕ):ℝ) ≤
          Real.exp (Real.exp (localPrimeHeight A L h))) →
      (∀ r ∈ R,∀ p : ℕ,p.Prime → p ∣ r → IsNormalPrime (localNormalityScale h) p) →
      (∀ p : ℕ,p.Prime → p ∣ q → IsNormalPrime (localNormalityScale h) p) →
      (∀ r ∈ R,(∃ s ∈ R,s≠r ∧ s.totient=r.totient) → ∃ s ∈ R,F r=s*q) →
      (∀ r ∈ Q,∃ p : ℕ,p.Prime ∧ p ∣ F r ∧ ¬IsNormalPrime (localNormalityScale h) p) →
      (∀ r ∈ Q,0<F r ∧ (F r).totient=d*r.totient) →
      (∑ r ∈ Q,(r.totient:ℝ)⁻¹) ≤ rho^h := by
  obtain ⟨D,hD,hlayers⟩ := local_residual_layer_bounds hc hA L
  let C : ℝ := 12*d/Real.log 2
  have hC : 0 ≤ C := by dsimp [C] <;> positivity
  filter_upwards [hlayers 256,local_nonnormal_witness_mass_rate hD.le 3,
    local_residual_mass_decay hA.le hC L] with h hdata hmass hdecay
  intro R Q F hQR hvalues hR hq hbranch hbad hF
  let U := localPrimeHeight A L h
  let J := discardExponent U
  have hpoint (r) (hr : r∈Q) :
      1<d*r.totient ∧ d*r.totient≤2^J ∧
      let z := (2:ℝ)^(Nat.clog 2 (d*r.totient))
      max 256 256 ≤ z ∧ (c/2)*(rho^h)⁻¹≤B z ∧ 0≤B z ∧
        Real.log (B z+4)≤D*h ∧ (localSquareCutoff z:ℝ)≤localNormalityScale h := by
    obtain ⟨p,hp,hpv,hgeo,hu⟩ := hvalues r hr
    exact hdata p (d*r.totient) hp hpv hgeo hu
  have hm := hmass d q J hd R Q F hQR
    (fun r hr => ⟨(hpoint r hr).1,by exact_mod_cast (hpoint r hr).2.1⟩)
    (fun r hr => ⟨by simpa only [max_self] using (hpoint r hr).2.2.1,
      (hpoint r hr).2.2.2.2.1,(hpoint r hr).2.2.2.2.2.1⟩)
    hR hq hbranch hbad hF
  have hU := localPrimeHeight_ge_two hA.le L h
  have hJ : 1+Real.log J ≤ 3*U := by
    have hh := (discardExponent_bounds hU).2
    dsimp only [J]
    linarith only [hh,hU]
  calc
    _ ≤ (4*d/Real.log 2)*rho^(3*h)*(1+Real.log J) := hm
    _ ≤ (4*d/Real.log 2)*rho^(3*h)*(3*U) :=
      mul_le_mul_of_nonneg_left hJ
        (mul_nonneg (by positivity) (pow_pos rho_pos _).le)
    _ = C*U*rho^(3*h) := by dsimp [C] <;> ring
    _ ≤ rho^h := hdecay

end TotientAsymptotic

end

end OAI
end

theorem solution : type_of% @OAI.TotientAsymptotic.local_nonnormal_residual_mass_oai := @OAI.TotientAsymptotic.local_nonnormal_residual_mass_oai
