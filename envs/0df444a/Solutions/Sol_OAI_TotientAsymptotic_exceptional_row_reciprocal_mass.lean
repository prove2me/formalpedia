-- Prove2me | solution 1 for OAI.TotientAsymptotic.exceptional_row_reciprocal_mass
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:37:47.894377+00:00
-- url     : https://prove2.me/submissions/e5588bc4-03cc-4866-aaf0-822c00402efe

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
import Theorems.Thm_OAI_TotientAsymptotic_real_coordinate_deviation

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_DyadicSuffix
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The integral comparison for reciprocal-weighted dyadic collision slices. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

lemma dyadicSuffixWeight_eq {σ : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    dyadicSuffixWeight σ n = (Real.log 2)^(-1-σ)*(n : ℝ)^(-1-σ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp : 0 < (n : ℝ)*Real.log 2 := mul_pos hnR htwo
  rw [← Real.mul_rpow htwo.le hnR.le, mul_comm (Real.log 2), Real.rpow_def_of_pos hp]
  have he : Real.log ((n : ℝ)*Real.log 2)*(-1-σ) =
      -σ*Real.log ((n : ℝ)*Real.log 2)-Real.log ((n : ℝ)*Real.log 2) := by ring
  rw [he, Real.exp_sub, Real.exp_log hp]
  rfl

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FiniteDyadicLogTail
attribute [-instance] _root_.instMeasurableSpace
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

lemma coordinate_decay_pos {ω : ℝ} (hω : 0 < ω) (k : ℕ) :
    0 < coordinateDecay ω k := by unfold coordinateDecay; positivity

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

lemma relative_row_at_dyadic {v k : ℕ} {ω : ℝ} (hv : 2 ≤ v)
    (hω : 0 ≤ ω) (hω1 : ω ≤ 1) (hsize : 4 ≤ ω*B ((2:ℝ)^(Nat.clog 2 v)))
    {n : ℕ} (hrow : (1+ω)*B (v:ℝ) <
      ∑ i : Fin k,a (i.val+1)*fordPrimeCoordinate n (i.val+1)) :
    (1+ω/2)*B ((2:ℝ)^(Nat.clog 2 v)) ≤
      ∑ i : Fin k,a (i.val+1)*fordPrimeCoordinate n (i.val+1) := by
  have hh := mul_le_mul_of_nonneg_left (dyadic_coordinate_loss hv)
    (show 0 ≤ 1+ω by linarith)
  nlinarith only [hh,hrow,hsize,hω1]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FinitePowerTail
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite partial-summation bound for a logarithmic power saving. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma finite_power_tail (K L : ℕ) (hK : 1 ≤ K) {δ : ℝ} (hδ : 0 < δ) :
    (∑ k ∈ Finset.Icc K L,(k:ℝ)^(-1-δ)) ≤ (1+δ⁻¹)*(K:ℝ)^(-δ) := by
  by_cases hKL : K ≤ L
  · have hK0 : (0:ℝ) < K := by exact_mod_cast (show 0 < K by omega)
    have hsum : (∑ k ∈ Finset.Icc K L,(k:ℝ)^(-1-δ)) =
        (K:ℝ)^(-1-δ)+∑ k ∈ Finset.Ico K L,((k+1:ℕ):ℝ)^(-1-δ) := by
      induction L, hKL using Nat.le_induction with
      | base => simp
      | succ L hKL ih =>
        rw [Finset.sum_Icc_succ_top (by omega),Finset.sum_Ico_succ_top hKL,ih]
        ring
    have hL0 : (0:ℝ) < L := by exact_mod_cast (show 0 < L by omega)
    have hant : AntitoneOn (fun x : ℝ => x^(-1-δ)) (Set.Icc (K:ℝ) L) := by
      intro x hx y hy hxy
      exact Real.rpow_le_rpow_of_nonpos (hK0.trans_le hx.1) hxy (by linarith)
    have hint := hant.sum_le_integral_Ico hKL
    have hzero : (0:ℝ) ∉ Set.uIcc (K:ℝ) L := by
      rw [Set.uIcc_of_le (by exact_mod_cast hKL)]
      intro h
      exact (not_le_of_gt hK0) h.1
    have he := integral_rpow (a:=(K:ℝ)) (b:=(L:ℝ))
      (r:=-1-δ) (Or.inr ⟨by linarith,hzero⟩)
    have hpow : -1-δ+1 = -δ := by ring
    rw [hpow] at he
    have htail : (∑ k ∈ Finset.Ico K L,((k+1:ℕ):ℝ)^(-1-δ)) ≤ (K:ℝ)^(-δ)/δ := by
      apply hint.trans
      rw [he]
      have hn := Real.rpow_nonneg (Nat.cast_nonneg L) (-δ)
      have hd : δ ≠ 0 := hδ.ne'
      field_simp
      nlinarith only [hn]
    have hhead : (K:ℝ)^(-1-δ) ≤ (K:ℝ)^(-δ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hK)
      linarith
    rw [hsum]
    have hh := add_le_add hhead htail
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · rw [Finset.Icc_eq_empty (by omega),Finset.sum_empty]
    positivity

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FiniteDyadicPowerMass
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reciprocal mass of a finite set with a logarithmic power saving in its count. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma finite_dyadic_power_mass (Q : Finset ℕ) (K L : ℕ) (hK : 1 ≤ K)
    {A δ : ℝ} (hA : 0 ≤ A) (hδ : 0 < δ)
    (hn : ∀ q ∈ Q,Nat.clog 2 q ∈ Finset.Icc K L)
    (hlo : ∀ q ∈ Q,(2:ℝ)^(Nat.clog 2 q)/4 ≤ q)
    (hcount : ∀ j ∈ Finset.Icc K L,((Q.filter (fun q => Nat.clog 2 q=j)).card:ℝ) ≤
      A*(2:ℝ)^j*(j:ℝ)^(-1-δ)) :
    (∑ q ∈ Q,(q:ℝ)⁻¹) ≤ 4*A*(1+δ⁻¹)*(K:ℝ)^(-δ) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to hn]
  have hf (j : ℕ) (hj : j ∈ Finset.Icc K L) :
      (∑ q ∈ Q.filter (fun q => Nat.clog 2 q=j),(q:ℝ)⁻¹) ≤ 4*A*(j:ℝ)^(-1-δ) := by
    have hy : (0:ℝ) < 2^j := by positivity
    calc
      _ ≤ ∑ _q ∈ Q.filter (fun q => Nat.clog 2 q=j),4/(2:ℝ)^j := by
        apply Finset.sum_le_sum
        intro q hq
        obtain ⟨hq,he⟩ := Finset.mem_filter.mp hq
        have hh := hlo q hq
        rw [he] at hh
        simpa only [inv_div] using inv_anti₀ (div_pos hy (by norm_num)) hh
      _ = ((Q.filter (fun q => Nat.clog 2 q=j)).card:ℝ)*(4/(2:ℝ)^j) := by simp
      _ ≤ (A*(2:ℝ)^j*(j:ℝ)^(-1-δ))*(4/(2:ℝ)^j) :=
        mul_le_mul_of_nonneg_right (hcount j hj) (by positivity)
      _ = _ := by field_simp
  calc
    _ ≤ ∑ j ∈ Finset.Icc K L,4*A*(j:ℝ)^(-1-δ) := Finset.sum_le_sum hf
    _ = 4*A*(∑ j ∈ Finset.Icc K L,(j:ℝ)^(-1-δ)) := (Finset.mul_sum ..).symm
    _ ≤ 4*A*((1+δ⁻¹)*(K:ℝ)^(-δ)) :=
      mul_le_mul_of_nonneg_left (finite_power_tail K L hK hδ) (by positivity)
    _ = _ := by ring

lemma finite_dyadic_log_power_tail (Q : Finset ℕ) {U A δ : ℝ}
    (hU : 1 < U) (hA : 0 ≤ A) (hδ : 0 < δ) (hlo : ∀ q ∈ Q,U ≤ q)
    (hc : ∀ j : ℕ,1 ≤ j → ((Q.filter (fun q => Nat.clog 2 q=j)).card:ℝ) ≤
      A*(2:ℝ)^j*(j:ℝ)^(-1-δ)) :
    (∑ q ∈ Q,(q:ℝ)⁻¹) ≤ 4*A*(1+δ⁻¹)*(Real.log U)^(-δ) := by
  classical
  by_cases hQ : Q.Nonempty
  · obtain ⟨K,L,hK,hlog,hn,hv⟩ := finite_dyadic_log_range Q hQ hU hlo
    have hh := finite_dyadic_power_mass Q K L hK hA hδ hn hv
      (fun j hj => hc j (hK.trans (Finset.mem_Icc.mp hj).1))
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hlogU : 0 < Real.log U := Real.log_pos hU
    have hlog2 : Real.log (2:ℝ) ≤ 1 := by linarith [Real.log_two_lt_d9]
    have hK0 : 0 ≤ (K:ℝ) := Nat.cast_nonneg _
    have hk : Real.log U ≤ K := by nlinarith only [hlog,mul_le_mul_of_nonneg_left hlog2 hK0]
    exact Real.rpow_le_rpow_of_nonpos hlogU hk (by linarith)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hQ,Finset.sum_empty]
    have hlogU : 0 < Real.log U := Real.log_pos hU
    positivity

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ExceptionalRowMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite reciprocal mass of totients with a relative coordinate-row failure. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem exceptional_row_reciprocal_mass_oai : ∃ C F : ℝ,0 < C ∧ 0 < F ∧
    ∀ k : ℕ,∀ ω U : ℝ,0 < ω → ω ≤ 1 → 512 ≤ U → 2*Real.exp (Real.exp 1) ≤ U →
    max 300000000 ((coordinateBudgetConstant F/coordinateDecay (ω/2) k)^(4/3:ℝ)) ≤ B U-1 →
    4 ≤ ω*B U → ∀ Q : Finset ℕ,
    (∀ v ∈ Q,U ≤ (v:ℝ) ∧ IsTotient v ∧
      ∃ n : ℕ,0 < n ∧ n.totient=v ∧
        (1+ω)*B v < ∑ i : Fin k,a (i.val+1)*fordPrimeCoordinate n (i.val+1)) →
    (∑ v ∈ Q,(v:ℝ)⁻¹) ≤
      4*C*(Real.log 2)^(-1-coordinateDecay (ω/2) k)*(1+(coordinateDecay (ω/2) k)⁻¹)*
        Real.exp (-coordinateDecay (ω/2) k*B U) := by
  classical
  obtain ⟨C,F,hC,hF,hcount⟩ := real_coordinate_deviation
  refine ⟨C,F,hC,hF,?_⟩
  intro k ω U hω hω1 hU hUexp hthreshold hlarge Q hQ
  let δ := coordinateDecay (ω/2) k
  have hδ : 0 < δ := coordinate_decay_pos (by linarith) k
  have hU1 : 1 < U := by linarith
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hA : 0 ≤ C*(Real.log 2)^(-1-δ) := by positivity
  have hslices (j : ℕ) (hj : 1 ≤ j) :
      ((Q.filter (fun v => Nat.clog 2 v=j)).card:ℝ) ≤
        (C*(Real.log 2)^(-1-δ))*(2:ℝ)^j*(j:ℝ)^(-1-δ) := by
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
      have hx1 : (1:ℝ) < (2:ℝ)^j := hU1.trans_le hUx
      have hBU : B U ≤ B ((2:ℝ)^j) :=
        Real.log_le_log (Real.log_pos hU1)
          (Real.log_le_log (by linarith) hUx)
      have hsize : 4 ≤ ω*B ((2:ℝ)^j) :=
        hlarge.trans (mul_le_mul_of_nonneg_left hBU hω.le)
      have hc := hcount ((2:ℝ)^j) (hU.trans hUx) (hUexp.trans hUx) k (ω/2)
        (by linarith) (by linarith) (by linarith only [hthreshold,hBU]) R (by
          intro q hq
          obtain ⟨hqQ,hqj⟩ := Finset.mem_filter.mp hq
          obtain ⟨hqU,hqt,n,hn,hφ,hrow⟩ := hQ q hqQ
          have hq2 : 2 ≤ q := by exact_mod_cast (show (2:ℝ) ≤ q by linarith only [hqU,hU])
          have hqd := dyadic_nat_bounds (show 1 < q by omega)
          rw [hqj] at hqd
          refine ⟨hqt,hqd.2.2,n,hn,hφ,?_⟩
          have hh := relative_row_at_dyadic hq2 hω.le hω1 (by simpa only [hqj] using hsize) hrow
          simpa only [hqj] using hh)
      calc
        _ ≤ C*(2:ℝ)^j/Real.log ((2:ℝ)^j)*Real.exp (-δ*B ((2:ℝ)^j)) := hc
        _ = C*(2:ℝ)^j*dyadicSuffixWeight δ j := by
          rw [dyadic_endpoint_log,dyadic_endpoint_B,dyadicSuffixWeight]
          ring
        _ = _ := by rw [dyadicSuffixWeight_eq hj]; ring
    · rw [Finset.not_nonempty_iff_eq_empty.mp hR,Finset.card_empty,Nat.cast_zero]
      positivity
  have hm := finite_dyadic_log_power_tail Q hU1 hA hδ (fun v hv => (hQ v hv).1) hslices
  have he : (Real.log U)^(-δ)=Real.exp (-δ*B U) := by
    rw [Real.rpow_def_of_pos (Real.log_pos hU1)]
    unfold B
    congr 1
    ring
  rw [he] at hm
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  ring

end TotientAsymptotic

end

end OAI
end

theorem solution : type_of% @OAI.TotientAsymptotic.exceptional_row_reciprocal_mass_oai := @OAI.TotientAsymptotic.exceptional_row_reciprocal_mass_oai
