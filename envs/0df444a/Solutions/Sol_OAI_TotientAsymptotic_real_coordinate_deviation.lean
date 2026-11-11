-- Prove2me | solution 1 for OAI.TotientAsymptotic.real_coordinate_deviation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:37:50.656516+00:00
-- url     : https://prove2.me/submissions/9eaac061-9e47-4c6a-9d4b-2e0ea532b19f

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
import Theorems.Thm_OAI_TotientAsymptotic_coordinate_violation_count
import Theorems.Thm_OAI_TotientAsymptotic_counting_envelope_real_bound

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LoglogGrid
attribute [-simp] _root_.SelbergSieve.selbergBoundingSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer cutoffs on the unit log-log grid used in Ford's counting argument. -/
noncomputable section
namespace TotientAsymptotic

lemma loglogCutoff_bounds {b : ℝ} (hb : 2 ≤ b) :
    2 ≤ loglogCutoff b ∧ b-1 ≤ B (loglogCutoff b) ∧ B (loglogCutoff b) ≤ b ∧
      Real.log (loglogCutoff b) ≤ Real.exp b := by
  have he : 3 ≤ Real.exp b := by linarith [Real.add_one_le_exp b]
  have he4 : 4 ≤ Real.exp (Real.exp b) := by linarith [Real.add_one_le_exp (Real.exp b)]
  have hf := log_floor_lower he4
  change 2 ≤ loglogCutoff b ∧ _ at hf
  have hn1 : (1:ℝ) < loglogCutoff b := by exact_mod_cast (show 1 < loglogCutoff b by omega)
  have hl0 : 0 < Real.log (loglogCutoff b) := Real.log_pos hn1
  have hlu : Real.log (loglogCutoff b) ≤ Real.exp b := by
    have hh := Real.log_le_log (by linarith : (0:ℝ)<loglogCutoff b)
      (Nat.floor_le (Real.exp_pos (Real.exp b)).le)
    simpa only [Real.log_exp] using hh
  have hll : Real.exp b/2 ≤ Real.log (loglogCutoff b) := by
    simpa only [Real.log_exp,loglogCutoff] using hf.2
  have hBl : b-Real.log 2 ≤ B (loglogCutoff b) := by
    have hh := Real.log_le_log (by positivity : 0 < Real.exp b/2) hll
    simpa only [Real.log_div (Real.exp_ne_zero b) (by norm_num : (2:ℝ)≠0),Real.log_exp,B] using hh
  have hl2 : Real.log (2:ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh
    exact hh
  have hBu : B (loglogCutoff b) ≤ b := by
    have hh := Real.log_le_log hl0 hlu
    simpa only [B,Real.log_exp] using hh
  exact ⟨hf.1,by linarith,hBu,hlu⟩

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BootstrapCutoffs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed cutoffs for the initial two-coordinate counting bootstrap. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma bootstrap_cutoff_bounds {b : ℝ} (hb : 300000000 ≤ b)
    (hl : Real.log (20*b)+2 ≤ b/10000) :
    2 ≤ bootstrapBottom b ∧ bootstrapBottom b ≤ bootstrapTop b ∧
      (bootstrapBottom b:ℝ)+2 ≤ b/2 ∧ (bootstrapTop b:ℝ) ≤ b ∧
      b-Real.log (20*b)-2 ≤ bootstrapTop b ∧
      Real.exp (bootstrapTop b) ≤ Real.exp b/(20*b) := by
  have hb0 : 0 < b := by linarith
  have hlog0 : 0 ≤ Real.log (20*b) := Real.log_nonneg (by linarith)
  have ht : 2 ≤ b-Real.log (20*b) := by linarith
  have hfloor2 : 2 ≤ ⌊b-Real.log (20*b)⌋₊ := Nat.le_floor ht
  have hbot2 : 2 ≤ bootstrapBottom b := by
    apply Nat.le_floor
    linarith
  have hbotup : (bootstrapBottom b:ℝ) ≤ b/100000000 := Nat.floor_le (by positivity)
  have htopup : (bootstrapTop b:ℝ) ≤ b-Real.log (20*b) := by
    have hs : bootstrapTop b ≤ ⌊b-Real.log (20*b)⌋₊ := Nat.sub_le _ _
    exact (Nat.cast_le.mpr hs).trans (Nat.floor_le (by linarith))
  have htoplow : b-Real.log (20*b)-2 ≤ bootstrapTop b := by
    dsimp [bootstrapTop]
    rw [Nat.cast_sub (by omega : 1 ≤ ⌊b-Real.log (20*b)⌋₊),Nat.cast_one]
    linarith [Nat.sub_one_lt_floor (b-Real.log (20*b))]
  refine ⟨hbot2,?_,by linarith,by linarith,htoplow,?_⟩
  · exact_mod_cast (show (bootstrapBottom b:ℝ) ≤ bootstrapTop b by linarith)
  · calc
      _ ≤ Real.exp (b-Real.log (20*b)) := Real.exp_le_exp.mpr htopup
      _ = _ := by rw [Real.exp_sub,Real.exp_log (by positivity : 0 < 20*b)]

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CoordinateErrorBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative absorption of the finite-grid error in a coordinate violation. -/
noncomputable section
namespace TotientAsymptotic

lemma coordinate_root_budget {b ω u t m : ℝ}
    (hb : 0 ≤ b) (hω : 0 ≤ ω) (hu : 0 ≤ u) (ht : 0 ≤ t) (htb : t ≤ b)
    (hm : 0 ≤ m) (hsmall : u*m^6 ≤ ω^2*b/1000000) :
    m^3*Real.sqrt (u*t) ≤ ω*b/1000 := by
  have hsqrt := Real.sq_sqrt (mul_nonneg hu ht)
  have hs : (m^3*Real.sqrt (u*t))^2 ≤ (ω*b/1000)^2 := by
    calc
      _ = (u*m^6)*t := by rw [mul_pow,hsqrt]; ring
      _ ≤ (ω^2*b/1000000)*b :=
        mul_le_mul hsmall htb ht (by positivity)
      _ = _ := by ring
  have hleft : 0 ≤ m^3*Real.sqrt (u*t) := by positivity
  have hright : 0 ≤ ω*b/1000 := by positivity
  nlinarith

lemma coordinate_linear_budget {b ω L m : ℝ}
    (hb : 0 ≤ b) (hω : 0 ≤ ω) (hω1 : ω ≤ 1) (hL : 0 ≤ L) (hm : 1 ≤ m)
    (hsmall : L*m^6 ≤ ω^2*b/1000000) :
    L*m^2 ≤ ω*b/1000000 := by
  have hpow : m^2 ≤ m^6 := pow_le_pow_right₀ hm (by norm_num)
  have h1 := mul_le_mul_of_nonneg_left hpow hL
  have hωsq : ω^2 ≤ ω := by nlinarith
  have h2 := mul_le_mul_of_nonneg_right hωsq hb
  linarith

lemma coordinate_exponent_budget {b ω D L u : ℝ} {k K : ℕ}
    (hb : 1 ≤ b) (hω : 0 ≤ ω) (hω1 : ω ≤ 1) (_hD : 0 ≤ D)
    (hL : 0 ≤ L) (hu : 0 ≤ u) (huL : u ≤ L)
    (hK : (K:ℝ) ≤ b) (hKlo : b-Real.log (20*b)-2 ≤ K)
    (hsmall : L*((k:ℝ)+2)^6 ≤ ω^2*b/1000000)
    (hbudget : (Real.log (20*b)+9+D+Real.log (b+1))*((k:ℝ)+2)^2 ≤ ω*b/100) :
    Real.log ((k:ℝ)+1)+(k:ℝ)*Real.log ((K:ℝ)+1)-(1+ω)*b+
      (b+L+6-K)*(k:ℝ)^2+((k:ℝ)+2)^2*u+D*((k:ℝ)+2)^2+
      ((k:ℝ)+2)^3*Real.sqrt (u*K) ≤ -(1+ω/2)*b := by
  have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg _
  have hKn : 0 ≤ (K:ℝ) := Nat.cast_nonneg _
  have hm : 1 ≤ (k:ℝ)+2 := by linarith
  have hlinear := coordinate_linear_budget (by linarith) hω hω1 hL hm hsmall
  have husmall : u*((k:ℝ)+2)^6 ≤ ω^2*b/1000000 :=
    (mul_le_mul_of_nonneg_right huL (by positivity)).trans hsmall
  have hroot := coordinate_root_budget (by linarith) hω hu hKn hK (by positivity) husmall
  have hlog0 : 0 ≤ Real.log (b+1) := Real.log_nonneg (by linarith)
  have hlogK : Real.log ((K:ℝ)+1) ≤ Real.log (b+1) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlogk : Real.log ((k:ℝ)+1) ≤ k := by
    simpa only [add_sub_cancel_right] using Real.log_le_sub_one_of_pos (show 0 < (k:ℝ)+1 by positivity)
  have hprefactor : Real.log ((k:ℝ)+1)+(k:ℝ)*Real.log ((K:ℝ)+1) ≤
      ((k:ℝ)+2)^2*(1+Real.log (b+1)) := by
    have hp := mul_le_mul_of_nonneg_left hlogK hk
    have hkm : (k:ℝ) ≤ ((k:ℝ)+2)^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hkm hlog0]
  have hlog20 : 0 ≤ Real.log (20*b)+8 := by
    have ht : 0 ≤ Real.log (20*b) := Real.log_nonneg (by nlinarith)
    linarith
  have hfirst : (b+6-K)*(k:ℝ)^2 ≤ (Real.log (20*b)+8)*((k:ℝ)+2)^2 := by
    have ha : b+6-K ≤ Real.log (20*b)+8 := by linarith
    have hs : (k:ℝ)^2 ≤ ((k:ℝ)+2)^2 := by nlinarith
    exact (mul_le_mul_of_nonneg_right ha (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hs hlog20)
  have hLterm : L*(k:ℝ)^2 ≤ L*((k:ℝ)+2)^2 :=
    mul_le_mul_of_nonneg_left (by nlinarith) hL
  have huterm : ((k:ℝ)+2)^2*u ≤ L*((k:ℝ)+2)^2 := by
    nlinarith only [mul_le_mul_of_nonneg_right huL (sq_nonneg ((k:ℝ)+2))]
  nlinarith only [hprefactor,hfirst,hLterm,huterm,hlinear,hroot,hbudget]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CoordinateCutoffs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete integer parameters for the coordinate-deviation estimate. -/
noncomputable section
namespace TotientAsymptotic

lemma coordinate_bottom_bounds {b ω : ℝ} {k : ℕ}
    (hb : 0 ≤ b) (hω : 0 ≤ ω) (hω1 : ω ≤ 1)
    (hlarge : 4 ≤ ω^2*b/(1000000*((k:ℝ)+2)^6)) :
    3 ≤ coordinateBottom b ω k ∧
    (coordinateBottom b ω k:ℝ) ≤ b/1000000 ∧
    (coordinateBottom b ω k:ℝ)*((k:ℝ)+2)^6 ≤ ω^2*b/1000000 ∧
    ω^2*b/(1000000*((k:ℝ)+2)^6)-1 < coordinateBottom b ω k := by
  have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg _
  have hp : 0 < ((k:ℝ)+2)^6 := by positivity
  have hp1 : 1 ≤ ((k:ℝ)+2)^6 := one_le_pow₀ (by linarith)
  have hωsq : ω^2 ≤ 1 := by nlinarith
  have ht : 0 ≤ ω^2*b/(1000000*((k:ℝ)+2)^6) := by positivity
  have hf : (coordinateBottom b ω k:ℝ) ≤ ω^2*b/(1000000*((k:ℝ)+2)^6) := Nat.floor_le ht
  have htup : ω^2*b/(1000000*((k:ℝ)+2)^6) ≤ b/1000000 := by
    apply (div_le_iff₀ (by positivity : 0 < 1000000*((k:ℝ)+2)^6)).mpr
    have h1 := mul_le_mul_of_nonneg_right hωsq hb
    have h2 := mul_le_mul_of_nonneg_left hp1 hb
    nlinarith only [h1,h2]
  refine ⟨?_,hf.trans htup,?_,Nat.sub_one_lt_floor _⟩
  · exact (show 3 ≤ 4 by omega).trans (Nat.le_floor hlarge)
  · have hh := mul_le_mul_of_nonneg_right hf hp.le
    have he : ω^2*b/(1000000*((k:ℝ)+2)^6)*((k:ℝ)+2)^6 = ω^2*b/1000000 := by
      field_simp
    rwa [he] at hh

lemma coordinate_cutoff_bounds {b ω F : ℝ} {k : ℕ}
    (hb : 300000000 ≤ b) (hω : 0 ≤ ω) (hω1 : ω ≤ 1) (hF : 0 ≤ F)
    (hlog : Real.log (20*b)+2 ≤ b/10000)
    (hlarge : 4 ≤ ω^2*b/(1000000*((k:ℝ)+2)^6))
    (hbudget : (Real.log (20*b)+9+F+Real.log (b+1))*((k:ℝ)+2)^2 ≤ ω*b/100) :
    3 ≤ coordinateBottom b ω k ∧ coordinateBottom b ω k ≤ bootstrapTop b ∧
    (bootstrapTop b:ℝ) ≤ b ∧ b-Real.log (20*b)-2 ≤ bootstrapTop b ∧
    Real.exp (bootstrapTop b) ≤ Real.exp b/(20*b) ∧
    (coordinateBottom b ω k:ℝ)*((k:ℝ)+2)^6 ≤ ω^2*b/1000000 ∧
    ((coordinateBottom b ω k:ℝ)+1)*(k:ℝ)^2 < (1+ω)*b := by
  have hb0 : 0 < b := by linarith
  have hbot := coordinate_bottom_bounds hb0.le hω hω1 hlarge
  have htop := bootstrap_cutoff_bounds hb hlog
  have hLK : coordinateBottom b ω k ≤ bootstrapTop b := by
    have hlower : b-b/10000 ≤ (bootstrapTop b:ℝ) := by linarith [htop.2.2.2.2.1]
    exact_mod_cast (show (coordinateBottom b ω k:ℝ) ≤ bootstrapTop b by linarith [hbot.2.1])
  refine ⟨hbot.1,hLK,htop.2.2.2.1,htop.2.2.2.2.1,htop.2.2.2.2.2,hbot.2.2.1,?_⟩
  have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg _
  have hm : 1 ≤ (k:ℝ)+2 := by linarith
  have hlin := coordinate_linear_budget hb0.le hω hω1
    (Nat.cast_nonneg (coordinateBottom b ω k)) hm hbot.2.2.1
  have hlogs : 0 ≤ Real.log (20*b) := Real.log_nonneg (by linarith)
  have hlogb : 0 ≤ Real.log (b+1) := Real.log_nonneg (by linarith)
  have hbase : 9*((k:ℝ)+2)^2 ≤ ω*b/100 := by
    have hmul := mul_le_mul_of_nonneg_right
      (show 9 ≤ Real.log (20*b)+9+F+Real.log (b+1) by linarith) (sq_nonneg ((k:ℝ)+2))
    exact hmul.trans hbudget
  have hsq : (k:ℝ)^2 ≤ ((k:ℝ)+2)^2 := by nlinarith
  have hlin' : (coordinateBottom b ω k:ℝ)*(k:ℝ)^2 ≤ ω*b/1000000 :=
    (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _)).trans hlin
  have hωb := mul_le_mul_of_nonneg_right hω1 hb0.le
  nlinarith only [hbase,hsq,hlin',hωb,hb0]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CoordinateCutoffDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Decay of the square-divisor and normality errors at the chosen cutoff. -/
noncomputable section
namespace TotientAsymptotic

lemma loglog_cutoff_reciprocal {L : ℕ} {b : ℝ} (hL : 3 ≤ L)
    (hsize : 3*b ≤ Real.exp ((L:ℝ)-1)) :
    (1:ℝ)/(loglogCutoff L+1:ℕ) ≤ Real.exp (-3*b) := by
  have hLR : (2:ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by omega)
  have hc := loglogCutoff_bounds hLR
  have hS0 : (0:ℝ) < loglogCutoff L := by exact_mod_cast (show 0 < loglogCutoff L by omega)
  have hlog : 0 < Real.log (loglogCutoff L) := Real.log_pos (by
    exact_mod_cast (show 1 < loglogCutoff L by omega))
  have hexp := Real.exp_le_exp.mpr hc.2.1
  rw [B,Real.exp_log hlog] at hexp
  have hlarge := Real.exp_le_exp.mpr (hsize.trans hexp)
  rw [Real.exp_log hS0] at hlarge
  calc
    _ ≤ (1:ℝ)/Real.exp (3*b) := by
      apply one_div_le_one_div_of_le (Real.exp_pos _)
      push_cast
      linarith
    _ = _ := by rw [one_div,← Real.exp_neg]; congr 1; ring

lemma loglog_cutoff_normality_factor {L : ℕ} (hL : 3 ≤ L) :
    (Real.log (loglogCutoff L))^(-1/6:ℝ) ≤ Real.exp (-((L:ℝ)-1)/6) := by
  have hLR : (2:ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by omega)
  have hc := loglogCutoff_bounds hLR
  have hlog : 0 < Real.log (loglogCutoff L) := Real.log_pos (by
    exact_mod_cast (show 1 < loglogCutoff L by omega))
  rw [Real.rpow_def_of_pos hlog]
  apply Real.exp_le_exp.mpr
  change B (loglogCutoff L)*(-1/6:ℝ) ≤ -((L:ℝ)-1)/6
  linarith [hc.2.1]

lemma coordinate_normality_factor {b ω : ℝ} {k : ℕ}
    (hb : 0 ≤ b) (hω : 0 ≤ ω) (hω1 : ω ≤ 1)
    (hlarge : 4 ≤ ω^2*b/(1000000*((k:ℝ)+2)^6)) :
    (Real.log (loglogCutoff (coordinateBottom b ω k)))^(-1/6:ℝ) ≤
      Real.exp (1/3:ℝ)*Real.exp (-ω^2*b/(6000000*((k:ℝ)+2)^6)) := by
  have hc := coordinate_bottom_bounds hb hω hω1 hlarge
  apply (loglog_cutoff_normality_factor hc.1).trans
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := hc.2.2.2
  have he : -ω^2*b/(6000000*((k:ℝ)+2)^6) =
      -(ω^2*b/(1000000*((k:ℝ)+2)^6))/6 := by field_simp <;> ring
  rw [he]
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

lemma coordinate_decay_identity (b ω : ℝ) (k : ℕ) :
    -ω^2*b/(6000000*((k:ℝ)+2)^6) = -2*coordinateDecay ω k*b := by
  unfold coordinateDecay
  field_simp
  ring

lemma coordinate_bootstrap_absorption {b δ : ℝ} (hb : 0 ≤ b)
    (hbudget : 9*(Real.log (b+4))^2+6*Real.log (b+4) ≤ δ*b) :
    (b+4)^6*Real.exp (9*(Real.log (b+4))^2)*Real.exp (-2*δ*b) ≤
      Real.exp (-δ*b) := by
  have hp : 0 < b+4 := by linarith
  have hid : (b+4)^6 = Real.exp (6*Real.log (b+4)) := by
    simpa only [Nat.cast_ofNat,Real.exp_log hp] using (Real.exp_nat_mul (Real.log (b+4)) 6).symm
  rw [hid,← Real.exp_add,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

lemma log_normalized_exponential {x : ℝ} (hx : 1 < x) (t : ℝ) :
    x/Real.log x*Real.exp t = x*Real.exp (t-B x) := by
  have hl : 0 < Real.log x := Real.log_pos hx
  rw [Real.exp_sub,B,Real.exp_log hl]
  ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CoordinateErrorAbsorption
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar estimates for the four contributions to the deviation count. -/
noncomputable section
namespace TotientAsymptotic

lemma coordinate_power_error {u b δ : ℝ} (hu : 0 < u) (hb : 0 ≤ b)
    (he : Real.log u=b) (hδ : δ ≤ 1/4) :
    u^(-5/4:ℝ) ≤ u⁻¹*Real.exp (-δ*b) := by
  have hlog := Real.exp_log hu
  rw [Real.rpow_def_of_pos hu,he,← hlog,← Real.exp_neg,← Real.exp_add,he]
  apply Real.exp_le_exp.mpr
  nlinarith only [mul_le_mul_of_nonneg_right hδ hb]

lemma coordinate_square_error {b δ D : ℝ} (hD : 0 ≤ D) (hb : 0 ≤ b)
    (hδ : δ ≤ 1) :
    (2+D*b)*Real.exp (-3*b) ≤ (2+D)*Real.exp (-(1+δ)*b) := by
  have hexp1 : 1 ≤ Real.exp b := Real.one_le_exp hb
  have hexpb : b ≤ Real.exp b := by linarith only [Real.add_one_le_exp b]
  have hp : 2+D*b ≤ (2+D)*Real.exp b := by
    nlinarith only [mul_le_mul_of_nonneg_left hexpb hD,hexp1]
  calc
    _ ≤ ((2+D)*Real.exp b)*Real.exp (-3*b) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = (2+D)*Real.exp (-2*b) := by
      rw [mul_assoc,← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by linarith)
      nlinarith only [mul_le_mul_of_nonneg_right hδ hb]

lemma coordinate_power_contribution {C x : ℝ} (hC : 0 ≤ C) (hx : 1 < x)
    {δ : ℝ} (hb : 0 ≤ B x) (hδ : δ ≤ 1/4) :
    C*x*(Real.log x)^(-5/4:ℝ) ≤ C*(x/Real.log x*Real.exp (-δ*B x)) := by
  have hh := coordinate_power_error (Real.log_pos hx) hb (show Real.log (Real.log x)=B x from rfl) hδ
  have hp := mul_le_mul_of_nonneg_left hh (show 0 ≤ C*x by positivity)
  simpa only [div_eq_mul_inv,mul_assoc] using hp

lemma coordinate_square_contribution {D x b δ r : ℝ} (hD : 0 ≤ D) (hx : 1 < x)
    (hb : 0 ≤ b) (he : b=B x) (hδ : δ ≤ 1) (_hr : 0 ≤ r)
    (hrecip : 1/r ≤ Real.exp (-3*b)) :
    (2*x+D*x*b)/r ≤ (2+D)*(x/Real.log x*Real.exp (-δ*b)) := by
  have hs := coordinate_square_error hD hb hδ
  calc
    _ = x*(2+D*b)*(1/r) := by ring
    _ ≤ x*((2+D*b)*Real.exp (-3*b)) := by
      have hh := mul_le_mul_of_nonneg_left hrecip (show 0 ≤ x*(2+D*b) by positivity)
      simpa only [mul_assoc] using hh
    _ ≤ x*((2+D)*Real.exp (-(1+δ)*b)) :=
      mul_le_mul_of_nonneg_left hs (by linarith)
    _ = _ := by
      rw [log_normalized_exponential hx]
      rw [← he]
      have hh : -δ*b-b=-(1+δ)*b := by ring
      rw [hh]
      ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CoordinateExponentialCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exponential form of the weighted-coordinate count. The hypotheses record
only numerical budgets, so the dimension and the excess may vary with X. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma coordinate_grid_prefactor (k K : ℕ) :
    (k:ℝ)*(K+1:ℕ)^k ≤
      Real.exp (Real.log ((k:ℝ)+1)+(k:ℝ)*Real.log ((K:ℝ)+1)) := by
  rw [Real.exp_add,Real.exp_log (by positivity : 0 < (k:ℝ)+1),
    Real.exp_nat_mul,Real.exp_log (by positivity : 0 < (K:ℝ)+1)]
  push_cast
  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

theorem coordinate_exponential_count : ∃ C D A F : ℝ,
    0 < C ∧ 0 < D ∧ 0 < A ∧ 0 < F ∧
    ∀ X k K L J : ℕ,256 ≤ X → Real.exp (Real.exp 1) ≤ X → 1 ≤ B X →
    3 ≤ L → L ≤ K → (K:ℝ) ≤ B X →
    B X-Real.log (20*B X)-2 ≤ K →
    Real.exp K ≤ Real.log X/(20*B X) → 1 ≤ J → (X:ℝ) ≤ (2:ℝ)^J →
    ∀ ω : ℝ,0 ≤ ω → ω ≤ 1 →
    (L:ℝ)*((k:ℝ)+2)^6 ≤ ω^2*B X/1000000 →
    (Real.log (20*B X)+9+F+Real.log (B X+1))*((k:ℝ)+2)^2 ≤ ω*B X/100 →
    ((L:ℝ)+1)*(k:ℝ)^2 < (1+ω)*B X →
    ∀ Q : Finset ℕ,(∀ v ∈ Q,IsTotient v ∧ v ≤ X ∧
      ∃ n : ℕ,0 < n ∧ n.totient=v ∧
        (1+ω)*B X ≤ ∑ j : Fin k,a (j.val+1)*fordPrimeCoordinate n (j.val+1)) →
    (Q.card:ℝ) ≤ C*X*(Real.log X)^(-5/4:ℝ)+(2*X+D*X*B X)/(loglogCutoff L+1:ℕ)+
      A*dyadicTotientEnvelope J*X/Real.log X*(B (2*X))^5*(1+Real.log J)*
        (Real.log (loglogCutoff L))^(-1/6:ℝ)+
      F*X*Real.exp (-(1+ω/2)*B X) := by
  obtain ⟨C,D,A,F,hC,hD,hA,hF,hcount⟩ := coordinate_violation_count
  refine ⟨C,D,A,F,hC,hD,hA,hF,?_⟩
  intro X k K L J hX hx hB hL hLK hK hKlo hgrid hJ hxJ ω hω hω1 hsmall hbudget hT Q hQ
  have hcut := loglogCutoff_bounds (show (2:ℝ) ≤ L by exact_mod_cast (show 2 ≤ L by omega))
  have hu : 0 ≤ B (loglogCutoff L) := by
    have hLR : (3:ℝ) ≤ L := by exact_mod_cast hL
    linarith [hcut.2.1]
  have he := coordinate_exponent_budget hB hω hω1 hF.le (Nat.cast_nonneg L)
    hu hcut.2.2.1 hK hKlo hsmall hbudget
  have hp := coordinate_grid_prefactor k K
  have hlast : F*X*k*(K+1:ℕ)^k*Real.exp
      (-(1+ω)*B X+(B X+L+6-K)*(k:ℝ)^2+((k:ℝ)+2)^2*B (loglogCutoff L)+
        F*((k:ℝ)+2)^2+((k:ℝ)+2)^3*Real.sqrt (B (loglogCutoff L)*K)) ≤
      F*X*Real.exp (-(1+ω/2)*B X) := by
    calc
      _ = (F*X)*((k:ℝ)*(K+1:ℕ)^k)*Real.exp _ := by ring
      _ ≤ (F*X)*Real.exp (Real.log ((k:ℝ)+1)+(k:ℝ)*Real.log ((K:ℝ)+1))*Real.exp _ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hp (by positivity)) (Real.exp_pos _).le
      _ = F*X*Real.exp
          (Real.log ((k:ℝ)+1)+(k:ℝ)*Real.log ((K:ℝ)+1)-(1+ω)*B X+
            (B X+L+6-K)*(k:ℝ)^2+((k:ℝ)+2)^2*B (loglogCutoff L)+
            F*((k:ℝ)+2)^2+((k:ℝ)+2)^3*Real.sqrt (B (loglogCutoff L)*K)) := by
        rw [mul_assoc,← Real.exp_add]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity)
  exact (hcount X k K L J hX hx hB hL hLK (by linarith) hgrid hJ hxJ
    ((1+ω)*B X) hT Q hQ).trans (add_le_add le_rfl (by simpa only [neg_mul] using hlast))

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CoordinateDeviationCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform exceptional-value bound for a failed weighted-coordinate row.
All hypotheses beyond the actual row failure are explicit numerical budgets. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem coordinate_deviation_count : ∃ C F : ℝ,0 < C ∧ 0 < F ∧
    ∀ X k : ℕ,256 ≤ X → Real.exp (Real.exp 1) ≤ X → 300000000 ≤ B X →
    ∀ ω : ℝ,0 ≤ ω → ω ≤ 1 →
    Real.log (20*B X)+2 ≤ B X/10000 →
    4 ≤ ω^2*B X/(1000000*((k:ℝ)+2)^6) →
    (Real.log (20*B X)+9+F+Real.log (B X+1))*((k:ℝ)+2)^2 ≤ ω*B X/100 →
    3*B X ≤ Real.exp ((coordinateBottom (B X) ω k:ℝ)-1) →
    9*(Real.log (B X+4))^2+6*Real.log (B X+4) ≤ coordinateDecay ω k*B X →
    ∀ Q : Finset ℕ,(∀ v ∈ Q,IsTotient v ∧ v ≤ X ∧
      ∃ n : ℕ,0 < n ∧ n.totient=v ∧
        (1+ω)*B X ≤ ∑ j : Fin k,a (j.val+1)*fordPrimeCoordinate n (j.val+1)) →
    (Q.card:ℝ) ≤ C*X/Real.log X*Real.exp (-coordinateDecay ω k*B X) := by
  obtain ⟨C,D,A,F,hC,hD,hA,hF,hcount⟩ := coordinate_exponential_count
  obtain ⟨E,hE,henv⟩ := counting_envelope_real_bound
  refine ⟨C+(2+D)+A*E*Real.exp (1/3:ℝ)+F,F,by positivity,hF,?_⟩
  intro X k hX hx hB ω hω hω1 hlog hlarge hbudget hsize habsorb Q hQ
  let b := B X
  let δ := coordinateDecay ω k
  let L := coordinateBottom b ω k
  let J := countingDyadicIndex X
  have hX4 : (4:ℝ) ≤ X := by exact_mod_cast (show 4 ≤ X by omega)
  have hX1 : (1:ℝ) < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos hX1
  have hb : 0 ≤ b := by dsimp [b] <;> linarith
  have hc := coordinate_cutoff_bounds hB hω hω1 hF.le hlog hlarge hbudget
  have hJ := counting_dyadic_index_bounds hX4
  have htop : Real.exp (bootstrapTop b) ≤ Real.log X/(20*b) := by
    have hh := hc.2.2.2.2.1
    dsimp only [b]
    simpa only [B,Real.exp_log hlogX] using hh
  have hmain := hcount X k (bootstrapTop b) L J hX hx (by dsimp [b] at hb <;> linarith)
    hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 htop hJ.1 hJ.2.1 ω hω hω1
    hc.2.2.2.2.2.1 hbudget hc.2.2.2.2.2.2 Q hQ
  have hδ := coordinate_decay_bounds (k:=k) hω hω1
  have hz : (X:ℝ)/Real.log X*Real.exp (-δ*b) = X*Real.exp (-(1+δ)*b) := by
    rw [log_normalized_exponential hX1]
    dsimp [b]
    congr 2
    ring
  have hfirst := coordinate_power_contribution hC.le hX1 hb hδ.2.1
  have hsq := loglog_cutoff_reciprocal hc.1 hsize
  have hsquare := coordinate_square_contribution hD.le hX1 hb (show b=B X from rfl)
    (show δ ≤ 1 by linarith only [hδ.2.1])
    (show (0:ℝ) ≤ (loglogCutoff L+1:ℕ) by positivity) hsq
  have hpoly := counting_normality_polynomial hX4 hb
  have henvX := henv X hX4
  have henvpoly : dyadicTotientEnvelope J*((B (2*X))^5*(1+Real.log J)) ≤
      E*Real.exp (9*(Real.log (b+4))^2)*(b+4)^6 := by
    apply mul_le_mul henvX hpoly
    · have hj1 : (1:ℝ) ≤ J := by exact_mod_cast hJ.1
      have hlogJ : 0 ≤ Real.log J := Real.log_nonneg hj1
      have hb2 : 0 ≤ B (2*X) := by
        have hmono : B X ≤ B (2*X) := Real.log_le_log hlogX
          (Real.log_le_log (by positivity) (by linarith : (X:ℝ) ≤ 2*X))
        exact hb.trans hmono
      positivity
    · positivity
  have hnormal := coordinate_normality_factor hb hω hω1 hlarge
  rw [coordinate_decay_identity] at hnormal
  have hthird : A*dyadicTotientEnvelope J*X/Real.log X*(B (2*X))^5*(1+Real.log J)*
      (Real.log (loglogCutoff L))^(-1/6:ℝ) ≤
      (A*E*Real.exp (1/3:ℝ))*(X/Real.log X*Real.exp (-δ*b)) := by
    have he := coordinate_bootstrap_absorption hb habsorb
    calc
      _ = (A*(X/Real.log X))*(dyadicTotientEnvelope J*((B (2*X))^5*(1+Real.log J)))*
          (Real.log (loglogCutoff L))^(-1/6:ℝ) := by ring
      _ ≤ (A*(X/Real.log X))*(E*Real.exp (9*(Real.log (b+4))^2)*(b+4)^6)*
          (Real.exp (1/3:ℝ)*Real.exp (-2*δ*b)) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left henvpoly (by positivity)
        · exact hnormal
        · positivity
        · positivity
      _ = (A*E*Real.exp (1/3:ℝ))*(X/Real.log X)*
          ((b+4)^6*Real.exp (9*(Real.log (b+4))^2)*Real.exp (-2*δ*b)) := by ring
      _ ≤ _ := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left he
          (show 0 ≤ (A*E*Real.exp (1/3:ℝ))*(X/Real.log X) by positivity)
  have hfourth : F*X*Real.exp (-(1+ω/2)*b) ≤ F*(X/Real.log X*Real.exp (-δ*b)) := by
    rw [hz]
    have he : -(1+ω/2)*b ≤ -(1+δ)*b := by nlinarith only [mul_le_mul_of_nonneg_right hδ.2.2 hb]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he)
      (show 0 ≤ F*X by positivity)
  have hh := add_le_add (add_le_add (add_le_add hfirst hsquare) hthird) hfourth
  apply hmain.trans
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [b,L,J,δ]
  ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CoordinateUniformBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single numerical threshold implies all budgets in the deviation count. -/
noncomputable section
namespace TotientAsymptotic

lemma coordinate_decay_small {ω : ℝ} {k : ℕ} (hω : 0 ≤ ω) (hω1 : ω ≤ 1) :
    coordinateDecay ω k ≤ 1/12000000 := by
  have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg _
  have hp : 1 ≤ ((k:ℝ)+2)^6 := one_le_pow₀ (by linarith)
  have hsq : ω^2 ≤ 1 := by nlinarith
  unfold coordinateDecay
  apply (div_le_iff₀ (by positivity : 0 < 12000000*((k:ℝ)+2)^6)).mpr
  nlinarith only [hsq,hp]

lemma coordinate_decay_scaled (b ω : ℝ) (k : ℕ) :
    coordinateDecay ω k*b*((k:ℝ)+2)^6=ω^2*b/12000000 := by
  unfold coordinateDecay
  field_simp

lemma coordinate_uniform_budget {b ω F : ℝ} {k : ℕ}
    (hb : 300000000 ≤ b) (hω : 0 ≤ ω) (hω1 : ω ≤ 1) (hF : 0 ≤ F)
    (hbudget : 100*(Real.log (b+4)+F+30)^2 ≤ coordinateDecay ω k*b) :
    Real.log (20*b)+2 ≤ b/10000 ∧
    4 ≤ ω^2*b/(1000000*((k:ℝ)+2)^6) ∧
    (Real.log (20*b)+9+F+Real.log (b+1))*((k:ℝ)+2)^2 ≤ ω*b/100 ∧
    3*b ≤ Real.exp ((coordinateBottom b ω k:ℝ)-1) ∧
    9*(Real.log (b+4))^2+6*Real.log (b+4) ≤ coordinateDecay ω k*b := by
  let l := Real.log (b+4)
  let S := l+F+30
  let d := coordinateDecay ω k*b
  have hb0 : 0 < b := by linarith
  have hl : 0 ≤ l := Real.log_nonneg (by linarith)
  have hS : 30 ≤ S := by dsimp [S] <;> linarith
  have h2S : 2*S ≤ d := by
    change 100*S^2 ≤ d at hbudget
    nlinarith only [hbudget,hS]
  have hsmall : d ≤ b/12000000 := by
    have hh := mul_le_mul_of_nonneg_right (coordinate_decay_small (k:=k) hω hω1) hb0.le
    change coordinateDecay ω k*b ≤ _
    linarith only [hh]
  have hlogb : Real.log b ≤ l := Real.log_le_log hb0 (by linarith)
  have hlogb1 : Real.log (b+1) ≤ l := Real.log_le_log (by linarith) (by linarith)
  have hlog20 : Real.log (20*b) ≤ l+19 := by
    rw [Real.log_mul (by norm_num : (20:ℝ)≠0) hb0.ne']
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<20)
    linarith only [hh,hlogb]
  have hcoefficient : Real.log (20*b)+9+F+Real.log (b+1) ≤ 2*S := by
    dsimp [S]
    linarith only [hlog20,hlogb1,hF]
  have hlogbudget : Real.log (20*b)+2 ≤ b/10000 := by
    have hh : Real.log (20*b)+2 ≤ 2*S := by dsimp [S]; linarith only [hlog20,hl,hF]
    linarith only [hh,h2S,hsmall,hb0]
  have htwelve : ω^2*b/(1000000*((k:ℝ)+2)^6)=12*d := by
    dsimp [d,coordinateDecay]
    field_simp
    ring
  have hlarge : 4 ≤ ω^2*b/(1000000*((k:ℝ)+2)^6) := by
    rw [htwelve]
    linarith only [h2S,hS]
  have hdm : d*((k:ℝ)+2)^6 ≤ ω^2*b/1000000 := by
    rw [show d*((k:ℝ)+2)^6=ω^2*b/12000000 from coordinate_decay_scaled b ω k]
    have hn : 0 ≤ ω^2*b := by positivity
    linarith only [hn]
  have hd0 : 0 ≤ d := by dsimp [d]; exact mul_nonneg (coordinate_decay_bounds (k:=k) hω hω1).1 hb0.le
  have hlin := coordinate_linear_budget hb0.le hω hω1 hd0
    (show 1 ≤ (k:ℝ)+2 by have hk := Nat.cast_nonneg (α:=ℝ) k; linarith) hdm
  have hgrid : (Real.log (20*b)+9+F+Real.log (b+1))*((k:ℝ)+2)^2 ≤ ω*b/100 := by
    have hh := mul_le_mul_of_nonneg_right (hcoefficient.trans h2S) (sq_nonneg ((k:ℝ)+2))
    have hn := mul_nonneg hω hb0.le
    linarith only [hh,hlin,hn]
  have hsize : 3*b ≤ Real.exp ((coordinateBottom b ω k:ℝ)-1) := by
    have hbot := (coordinate_bottom_bounds hb0.le hω hω1 hlarge).2.2.2
    rw [htwelve] at hbot
    have hlog3 : Real.log (3*b) ≤ l+2 := by
      rw [Real.log_mul (by norm_num : (3:ℝ)≠0) hb0.ne']
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
      linarith only [hh,hlogb]
    have hh : Real.log (3*b) ≤ (coordinateBottom b ω k:ℝ)-1 := by
      dsimp [S] at h2S hS
      linarith only [hlog3,hbot,h2S,hS,hF,hl]
    exact (Real.exp_log (by positivity : 0 < 3*b)) ▸ Real.exp_le_exp.mpr hh
  refine ⟨hlogbudget,hlarge,hgrid,hsize,?_⟩
  change 100*S^2 ≤ d at hbudget
  change 9*l^2+6*l ≤ d
  have hSl : l ≤ S := by dsimp [S] <;> linarith
  have hsquares : l^2 ≤ S^2 := by nlinarith only [hl,hS,hSl]
  nlinarith only [hbudget,hsquares,hl,hS,hSl]

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CoordinateThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An effective threshold for the logarithmic budget in the row estimate. -/
noncomputable section
namespace TotientAsymptotic

lemma coordinate_threshold_budget {b F δ : ℝ} (hb : 1 ≤ b) (hF : 0 ≤ F) (hδ : 0 < δ)
    (hthreshold : (coordinateBudgetConstant F/δ)^(4/3:ℝ) ≤ b) :
    100*(Real.log (b+4)+F+30)^2 ≤ δ*b :=
  four_thirds_threshold_budget hb hF hδ hthreshold

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_EffectiveCoordinateCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Effective, uniform form of the coordinate-violation estimate. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem effective_coordinate_count : ∃ C F : ℝ,0 < C ∧ 0 < F ∧
    ∀ X k : ℕ,256 ≤ X → Real.exp (Real.exp 1) ≤ X →
    ∀ ω : ℝ,0 < ω → ω ≤ 1 →
    max 300000000 ((coordinateBudgetConstant F/coordinateDecay ω k)^(4/3:ℝ)) ≤ B X →
    ∀ Q : Finset ℕ,(∀ v ∈ Q,IsTotient v ∧ v ≤ X ∧
      ∃ n : ℕ,0 < n ∧ n.totient=v ∧
        (1+ω)*B X ≤ ∑ j : Fin k,a (j.val+1)*fordPrimeCoordinate n (j.val+1)) →
    (Q.card:ℝ) ≤ C*X/Real.log X*Real.exp (-coordinateDecay ω k*B X) := by
  obtain ⟨C,F,hC,hF,hcount⟩ := coordinate_deviation_count
  refine ⟨C,F,hC,hF,?_⟩
  intro X k hX hx ω hω hω1 hthreshold Q hQ
  have hbig := (le_max_left 300000000 _).trans hthreshold
  have hsq := (le_max_right 300000000 _).trans hthreshold
  have hbudget := coordinate_threshold_budget (by linarith : 1 ≤ B X) hF.le
    (coordinate_decay_pos hω k) hsq
  obtain ⟨hlog,hlarge,hgrid,hsize,habsorb⟩ :=
    coordinate_uniform_budget hbig hω.le hω1 hF.le hbudget
  exact hcount X k hX hx hbig ω hω.le hω1 hlog hlarge hgrid hsize habsorb Q hQ

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RealCoordinateDeviation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The effective row-deviation estimate for arbitrary real endpoints. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem real_coordinate_deviation_oai : ∃ C F : ℝ,0 < C ∧ 0 < F ∧
    ∀ x : ℝ,512 ≤ x → 2*Real.exp (Real.exp 1) ≤ x → ∀ k : ℕ,
    ∀ ω : ℝ,0 < ω → ω ≤ 1 →
    max 300000000 ((coordinateBudgetConstant F/coordinateDecay ω k)^(4/3:ℝ)) ≤ B x-1 →
    ∀ Q : Finset ℕ,(∀ v ∈ Q,IsTotient v ∧ (v:ℝ) ≤ x ∧
      ∃ n : ℕ,0 < n ∧ n.totient=v ∧
        (1+ω)*B x ≤ ∑ j : Fin k,a (j.val+1)*fordPrimeCoordinate n (j.val+1)) →
    (Q.card:ℝ) ≤ C*x/Real.log x*Real.exp (-coordinateDecay ω k*B x) := by
  obtain ⟨C,F,hC,hF,hcount⟩ := effective_coordinate_count
  refine ⟨2*Real.exp 1*C,F,by positivity,hF,?_⟩
  intro x hx hxexp k ω hω hω1 hthreshold Q hQ
  have hx4 : 4 ≤ x := by linarith
  have hf := coordinate_floor_bounds hx4
  have hN : 256 ≤ ⌊x⌋₊ := Nat.le_floor (by linarith : (256:ℝ) ≤ x)
  have hNexp : Real.exp (Real.exp 1) ≤ (⌊x⌋₊:ℝ) := by linarith only [hf.2.1,hxexp]
  have hNat := hcount ⌊x⌋₊ k hN hNexp ω hω hω1
    (hthreshold.trans hf.2.2.2.2.1) Q (by
      intro v hv
      obtain ⟨ht,hvX,n,hn,hφ,hscore⟩ := hQ v hv
      refine ⟨ht,Nat.le_floor hvX,n,hn,hφ,?_⟩
      have hh := mul_le_mul_of_nonneg_left hf.2.2.2.2.2 (show 0 ≤ 1+ω by linarith)
      exact hh.trans hscore)
  have hδ := coordinate_decay_bounds (k:=k) hω.le hω1
  have hround := coordinate_floor_normalization hx4 hδ.1 (hδ.2.1.trans (by norm_num))
  calc
    _ ≤ C*((⌊x⌋₊:ℝ)/Real.log (⌊x⌋₊:ℝ)*Real.exp (-coordinateDecay ω k*B (⌊x⌋₊:ℝ))) := by
      simpa only [div_eq_mul_inv,mul_assoc] using hNat
    _ ≤ C*(2*Real.exp 1*(x/Real.log x*Real.exp (-coordinateDecay ω k*B x))) :=
      mul_le_mul_of_nonneg_left hround hC.le
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

theorem solution : type_of% @OAI.TotientAsymptotic.real_coordinate_deviation_oai := @OAI.TotientAsymptotic.real_coordinate_deviation_oai
