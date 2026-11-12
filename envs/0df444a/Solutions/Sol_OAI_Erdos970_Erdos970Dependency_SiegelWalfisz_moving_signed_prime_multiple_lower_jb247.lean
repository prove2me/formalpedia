-- Prove2me | solution 1 for OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.moving_signed_prime_multiple_lower_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:57:21.671158+00:00
-- url     : https://prove2.me/submissions/7995d0af-9f7e-49ea-a08b-f3a5b119f819

import Batteries.Tactic.Lemma
import Mathlib
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Group.Support
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Logic.Equiv.Prod
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Tactic
import Mathlib.Tactic.Bound
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.MetricSpace.Basic
import Definitions.Def_OAIQ247J008
import Theorems.Thm_OAI_Erdos970_Erdos970Dependency_SiegelWalfisz_exists_uniform_riesz_contour_bound_jb247

section
-- module Solutions.OAIQ247_JB.Erdos970_Consequences
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

namespace Erdos970
open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Real
open scoped Topology

lemma continuousOn_log0 :
    ContinuousOn (fun x ↦ -1 / (x * log x ^ 2)) {0, 1, -1}ᶜ := by
  refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  fun_prop (disch := simp_all)

lemma integral_log_inv (a b : ℝ) (ha : 2 ≤ a) (hb : a ≤ b) :
    ∫ t in a..b, (log t)⁻¹ =
    ((log b)⁻¹ * b) - ((log a)⁻¹ * a) +
      ∫ t in a..b, ((log t)^2)⁻¹ := by
  rw [le_iff_lt_or_eq] at hb
  rcases hb with hb | rfl; swap
  · simp only [intervalIntegral.integral_same, sub_self, add_zero]
  · have := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := fun x => (log x)⁻¹)
      (u' := fun x => -1 / (x * (log x)^2))
      (v := fun x => x)
      (v' := fun _ => 1) (a := a) (b := b)
      (fun x hx => by
        rw [Set.uIcc_eq_union, Set.Icc_eq_empty (lt_iff_not_ge |>.1 hb), Set.union_empty] at hx
        obtain ⟨hx1, _⟩ := hx
        rw [show (-1 / (x * log x ^ 2)) = (-1 / log x ^ 2) * (x⁻¹) by
          rw [mul_comm x]; field_simp]
        apply HasDerivAt.comp
          (h := fun t => log t) (h₂ := fun t => t⁻¹) (x := x)
        · simpa using! HasDerivAt.inv (c := fun t : ℝ => t) (c' := 1) (x := log x)
            (hasDerivAt_id' (log x))
            (by simp only [ne_eq, log_eq_zero, not_or]; refine ⟨?_, ?_, ?_⟩ <;> linarith)
        · apply hasDerivAt_log; linarith)
      (fun x _ => hasDerivAt_id' x)
      (by
        rw [intervalIntegrable_iff_integrableOn_Icc_of_le (le_of_lt hb)]
        apply ContinuousOn.integrableOn_Icc
        refine continuousOn_log0.mono fun x hx ↦ ?_
        simp only [Set.mem_Icc, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
          not_or] at hx ⊢
        refine ⟨?_, ?_, ?_⟩ <;> linarith)
      (by
        constructor <;>
        apply MeasureTheory.integrable_const)
    simp only [mul_one] at this
    rw [this]
    simp_rw [neg_div, neg_mul]
    rw [sub_eq_add_neg]
    congr 1
    rw [intervalIntegral.integral_of_le (le_of_lt hb),
      intervalIntegral.integral_of_le (le_of_lt hb),
      ← MeasureTheory.integral_neg]
    simp_rw [neg_neg]
    refine integral_congr_ae ?_
    · rw [ae_restrict_eq, eventuallyEq_inf_principal_iff]
      · refine .of_forall fun x hx => ?_
        simp only [Set.mem_Ioc, one_div, mul_inv_rev, mul_assoc] at hx ⊢
        rw [inv_mul_cancel₀, mul_one]
        linarith
      exact measurableSet_Ioc

end Erdos970
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_NonquadraticZeroFree
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz

lemma modulusHeight_ge_one (q : ℕ) [NeZero q] (t : ℝ) : 1 ≤ modulusHeight q t := by
  have hq : (1:ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlq := Real.log_nonneg hq
  have ht := abs_nonneg t
  have hlt : 1 < Real.log (|t|+6) :=
    (Real.lt_log_iff_exp_lt (by linarith)).mpr (Real.exp_one_lt_three.trans (by linarith))
  unfold modulusHeight
  linarith

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_RieszMellinKernel
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Set _root_.Filter
open scoped Topology
attribute [local instance] Classical.propDecidable

lemma rieszWeight_eq_zero {x : ℝ} (hx : 1 ≤ x) : rieszWeight x = 0 :=
  max_eq_right (sub_nonpos.mpr hx)

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_RieszIntegrand
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.MeasureTheory
open scoped BigOperators

lemma tsum_riesz_eq_finite (f : ℕ → ℂ) {X : ℝ} (hX : 0 < X) :
    (∑' n:ℕ, f n*(rieszWeight ((n:ℝ)/X):ℂ)) = rieszSum f X := by
  unfold rieszSum
  apply tsum_eq_sum
  intro n hn
  have hn' : ⌊X⌋₊ < n := by simp only [Finset.mem_range] at hn; omega
  have hXn : X < (n:ℝ) := (Nat.floor_lt hX.le).mp hn'
  have hw : rieszWeight ((n:ℝ)/X) = 0 := rieszWeight_eq_zero
    ((le_div_iff₀ hX).mpr (by linarith))
  rw [hw,Complex.ofReal_zero,mul_zero]

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_RecoveryScale
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

lemma rpow_perron_sigma {X : ℝ} (hX : 1 < X) :
    X^(1+(Real.log X)⁻¹) = X*Real.exp 1 := by
  rw [Real.rpow_def_of_pos (by linarith : 0 < X),mul_add,mul_one,
    mul_inv_cancel₀ (Real.log_pos hX).ne',Real.exp_add,Real.exp_log (by linarith : 0 < X)]

lemma rpow_rieszContourLeft {X : ℝ} (hX : 0 < X) (a : ℝ) (q : ℕ) (T : ℝ) :
    X^(rieszContourLeft a q T) = X*Real.exp (-a*Real.log X/(modulusHeight q T)^2) := by
  rw [Real.rpow_def_of_pos hX]
  have he : Real.log X*rieszContourLeft a q T =
      Real.log X+(-a*Real.log X/(modulusHeight q T)^2) := by unfold rieszContourLeft; ring
  rw [he,Real.exp_add,Real.exp_log hX]

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz

lemma rieszWeight_scaled {delta : ℝ} (hd : 0 < delta) (u : ℝ) :
    (1+delta)*rieszWeight (u/(1+delta)) = max (1+delta-u) 0 := by
  have hp : 0 < 1+delta := by linarith
  by_cases hu : u ≤ 1+delta
  · have hratio : u/(1+delta) ≤ 1 := (div_le_iff₀ hp).mpr (by linarith)
    simp only [rieszWeight,max_eq_left (sub_nonneg.mpr hratio),max_eq_left (sub_nonneg.mpr hu)]
    field_simp
  · have hratio : 1 ≤ u/(1+delta) := (le_div_iff₀ hp).mpr (by linarith)
    simp only [rieszWeight,max_eq_right (sub_nonpos.mpr hratio),
      max_eq_right (show 1+delta-u ≤ 0 by linarith),mul_zero]

lemma rieszDifferenceWeight_eq {delta : ℝ} (hd : 0 < delta) (u : ℝ) :
    rieszDifferenceWeight delta u =
      ((1+delta)*rieszWeight (u/(1+delta))-rieszWeight u)/delta := by
  rw [rieszWeight_scaled hd]
  rfl

lemma rieszDifferenceWeight_nonneg {delta : ℝ} (hd : 0 < delta) (u : ℝ) :
    0 ≤ rieszDifferenceWeight delta u := by
  unfold rieszDifferenceWeight
  apply div_nonneg _ hd.le
  exact sub_nonneg.mpr (max_le_max (by linarith) le_rfl)

lemma rieszDifferenceWeight_le_one {delta : ℝ} (hd : 0 < delta) (u : ℝ) :
    rieszDifferenceWeight delta u ≤ 1 := by
  have hm : max (1+delta-u) 0 ≤ max (1-u) 0+delta := by
    apply max_le
    · have h := le_max_left (1-u) 0
      linarith
    · have h := le_max_right (1-u) 0
      linarith
  unfold rieszDifferenceWeight
  exact (div_le_iff₀ hd).mpr (by linarith)

lemma rieszDifferenceWeight_eq_one {delta u : ℝ} (hd : 0 < delta) (hu : u ≤ 1) :
    rieszDifferenceWeight delta u = 1 := by
  unfold rieszDifferenceWeight
  rw [max_eq_left (show 0 ≤ 1+delta-u by linarith),max_eq_left (show 0 ≤ 1-u by linarith)]
  have he : 1+delta-u-(1-u) = delta := by ring
  rw [he,div_self hd.ne']

lemma riesz_rescaled_difference {delta X : ℝ} (hd : 0 < delta) (_hX : 0 < X) (n : ℝ) :
    ((1+delta)*rieszWeight (n/((1+delta)*X))-rieszWeight (n/X))/delta =
      rieszDifferenceWeight delta (n/X) := by
  rw [rieszDifferenceWeight_eq hd]
  have he : n/((1+delta)*X) = (n/X)/(1+delta) := by
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [he]




open scoped BigOperators

lemma rieszSum_extend (f : ℕ → ℂ) {X Y : ℝ} (hX : 0 < X) (hXY : X ≤ Y) :
    rieszSum f X = ∑ n ∈ Finset.range (⌊Y⌋₊+1), f n*(rieszWeight ((n:ℝ)/X):ℂ) := by
  rw [← tsum_riesz_eq_finite f hX]
  apply tsum_eq_sum
  intro n hn
  have hn' : ⌊Y⌋₊ < n := by simp only [Finset.mem_range] at hn; omega
  have hYn : Y < (n:ℝ) := (Nat.floor_lt (hX.le.trans hXY)).mp hn'
  have hw := rieszWeight_eq_zero (x := (n:ℝ)/X) ((le_div_iff₀ hX).mpr (by linarith))
  rw [hw,Complex.ofReal_zero,mul_zero]

lemma rieszRecovery_eq_sum (f : ℕ → ℂ) {X delta : ℝ} (hX : 0 < X) (hd : 0 < delta) :
    rieszRecovery f X delta =
      ∑ n ∈ Finset.range (⌊(1+delta)*X⌋₊+1), f n*(rieszDifferenceWeight delta ((n:ℝ)/X):ℂ) := by
  have hXY : X ≤ (1+delta)*X := by nlinarith [mul_pos hd hX]
  unfold rieszRecovery
  rw [rieszSum_extend f hX hXY]
  unfold rieszSum
  rw [Finset.mul_sum,← Finset.sum_sub_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n _
  have hw := congrArg Complex.ofReal (riesz_rescaled_difference hd hX (n:ℝ))
  push_cast at hw
  calc
    _ = f n * ((((1+delta:ℝ):ℂ)*(rieszWeight ((n:ℝ)/((1+delta)*X)):ℂ)-
        (rieszWeight ((n:ℝ)/X):ℂ))/(delta:ℂ)) := by ring
    _ = _ := by push_cast; rw [hw]

lemma rieszRecovery_sub_sharp (f : ℕ → ℂ) {X delta : ℝ} (hX : 0 < X) (hd : 0 < delta) :
    rieszRecovery f X delta-sharpSum f X =
      ∑ n ∈ Finset.Ico (⌊X⌋₊+1) (⌊(1+delta)*X⌋₊+1),
        f n*(rieszDifferenceWeight delta ((n:ℝ)/X):ℂ) := by
  have hXY : X ≤ (1+delta)*X := by nlinarith [mul_pos hd hX]
  have hfloor : ⌊X⌋₊+1 ≤ ⌊(1+delta)*X⌋₊+1 := Nat.add_le_add_right (Nat.floor_mono hXY) 1
  have hprefix : (∑ n ∈ Finset.range (⌊X⌋₊+1),
      f n*(rieszDifferenceWeight delta ((n:ℝ)/X):ℂ)) = sharpSum f X := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn' : n ≤ ⌊X⌋₊ := by simp only [Finset.mem_range] at hn; omega
    have hnX : (n:ℝ) ≤ X := (show (n:ℝ) ≤ (⌊X⌋₊:ℝ) by exact_mod_cast hn').trans (Nat.floor_le hX.le)
    rw [rieszDifferenceWeight_eq_one hd ((div_le_iff₀ hX).mpr (by linarith)),Complex.ofReal_one,mul_one]
  have hs := Finset.sum_range_add_sum_Ico (fun n:ℕ => f n*(rieszDifferenceWeight delta ((n:ℝ)/X):ℂ)) hfloor
  rw [hprefix] at hs
  rw [rieszRecovery_eq_sum f hX hd,← hs,add_sub_cancel_left]

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open scoped BigOperators

theorem norm_rieszRecovery_sub_sharp (f : ℕ → ℂ)
    (hcoeff : ∀ n : ℕ, 0 < n → ‖f n‖ ≤ Real.log (n:ℝ))
    {X delta : ℝ} (hX : 1 ≤ X) (hd : 0 < delta) :
    ‖rieszRecovery f X delta-sharpSum f X‖ ≤ (delta*X+1)*Real.log ((1+delta)*X) := by
  have hXp : 0 < X := by linarith
  let Y : ℝ := (1+delta)*X
  have hXY : X ≤ Y := by dsimp only [Y] <;> nlinarith [mul_pos hd hXp]
  have hY1 : 1 ≤ Y := hX.trans hXY
  have hYp : 0 < Y := by linarith
  have hfloor : ⌊X⌋₊ ≤ ⌊Y⌋₊ := Nat.floor_mono hXY
  let S := Finset.Ico (⌊X⌋₊+1) (⌊Y⌋₊+1)
  have hcard : (S.card:ℝ) ≤ delta*X+1 := by
    dsimp only [S]
    rw [Nat.card_Ico,Nat.cast_sub (Nat.add_le_add_right hfloor 1)]
    push_cast
    have hy := Nat.floor_le hYp.le
    have hx := Nat.lt_floor_add_one X
    dsimp only [Y] at hy
    nlinarith
  have hpoint (n:ℕ) (hn : n ∈ S) :
      ‖f n*(rieszDifferenceWeight delta ((n:ℝ)/X):ℂ)‖ ≤ Real.log Y := by
    have hn' := Finset.mem_Ico.mp hn
    have hnp : 0 < n := by omega
    have hnf : n ≤ ⌊Y⌋₊ := by omega
    have hnY : (n:ℝ) ≤ Y := (show (n:ℝ) ≤ (⌊Y⌋₊:ℝ) by exact_mod_cast hnf).trans (Nat.floor_le hYp.le)
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (rieszDifferenceWeight_nonneg hd _)]
    calc
      _ ≤ ‖f n‖ := by
        have h := mul_le_mul_of_nonneg_left (rieszDifferenceWeight_le_one hd ((n:ℝ)/X)) (norm_nonneg (f n))
        simpa only [mul_one] using h
      _ ≤ Real.log (n:ℝ) := hcoeff n hnp
      _ ≤ Real.log Y := Real.log_le_log (by exact_mod_cast hnp) hnY
  rw [rieszRecovery_sub_sharp f hXp hd]
  change ‖∑ n ∈ S, f n*(rieszDifferenceWeight delta ((n:ℝ)/X):ℂ)‖ ≤ (delta*X+1)*Real.log Y
  calc
    _ ≤ ∑ n ∈ S, ‖f n*(rieszDifferenceWeight delta ((n:ℝ)/X):ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ S, Real.log Y := Finset.sum_le_sum hpoint
    _ = (S.card:ℝ)*Real.log Y := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (Real.log_nonneg hY1)

lemma norm_rieszRecovery_le (f : ℕ → ℂ) (X : ℝ) {delta : ℝ} (hd : 0 < delta) :
    ‖rieszRecovery f X delta‖ ≤
      ((1+delta)*‖rieszSum f ((1+delta)*X)‖+‖rieszSum f X‖)/delta := by
  unfold rieszRecovery
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd]
  apply div_le_div_of_nonneg_right _ hd.le
  calc
    _ ≤ ‖((1+delta:ℝ):ℂ)*rieszSum f ((1+delta)*X)‖+‖rieszSum f X‖ := norm_sub_le _ _
    _ = _ := by rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith : 0 < 1+delta)]

theorem sharpSum_norm_le_riesz (f : ℕ → ℂ)
    (hcoeff : ∀ n : ℕ, 0 < n → ‖f n‖ ≤ Real.log (n:ℝ))
    {X delta : ℝ} (hX : 1 ≤ X) (hd : 0 < delta) :
    ‖sharpSum f X‖ ≤
      ((1+delta)*‖rieszSum f ((1+delta)*X)‖+‖rieszSum f X‖)/delta +
        (delta*X+1)*Real.log ((1+delta)*X) := by
  have he := norm_rieszRecovery_sub_sharp f hcoeff hX hd
  have hr := norm_rieszRecovery_le f X hd
  have ht := norm_add_le (sharpSum f X-rieszRecovery f X delta) (rieszRecovery f X delta)
  rw [sub_add_cancel,norm_sub_rev] at ht
  linarith

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

lemma character_vonMangoldt_norm_le {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (n : ℕ) :
    ‖chi n*(ArithmeticFunction.vonMangoldt n:ℂ)‖ ≤ Real.log (n:ℝ) := by
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n))]
  calc
    _ ≤ ArithmeticFunction.vonMangoldt n := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (chi.norm_le_one n)
        (ArithmeticFunction.vonMangoldt_nonneg (n := n))
    _ ≤ _ := ArithmeticFunction.vonMangoldt_le_log

end Erdos970Dependency.SiegelWalfisz


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrincipalPrimePowers
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma principalDifference_norm_le (q : ℕ) [NeZero q] (n : ℕ) :
    ‖principalDifference q n‖ ≤ ArithmeticFunction.vonMangoldt n := by
  unfold principalDifference
  by_cases hu : IsUnit (n:ZMod q)
  · rw [MulChar.one_apply hu,one_mul,sub_self,norm_zero]
    exact ArithmeticFunction.vonMangoldt_nonneg
  · rw [MulChar.map_nonunit _ hu,zero_mul,zero_sub,norm_neg,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n))]

lemma excluded_primePower_dvd_power (q : ℕ) [NeZero q] {N n : ℕ}
    (hn : n ≤ N) (hLambda : ArithmeticFunction.vonMangoldt n ≠ 0)
    (hu : ¬IsUnit (n:ZMod q)) : n ∣ q^(Nat.log 2 N) := by
  obtain ⟨p,k,hp,hk,he⟩ := (isPrimePow_nat_iff n).mp
    (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hLambda)
  have hpq : p ∣ q := by
    by_contra h
    apply hu
    rw [← he,Nat.cast_pow]
    exact ((ZMod.isUnit_prime_iff_not_dvd hp).mpr h).pow k
  have h2 : 2^k ≤ n := by rw [← he]; gcongr; exact hp.two_le
  have hkN : k ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by decide) (h2.trans hn)
  rw [← he]
  exact (pow_dvd_pow p hkN).trans (pow_dvd_pow_of_dvd hpq _)

lemma principalDifference_eq_zero_of_not_dvd (q : ℕ) [NeZero q] {N n : ℕ}
    (hn : n ≤ N) (hnd : ¬n ∣ q^(Nat.log 2 N)) : principalDifference q n = 0 := by
  by_cases hl : ArithmeticFunction.vonMangoldt n = 0
  · simp only [principalDifference,hl,Complex.ofReal_zero,mul_zero,sub_self]
  · by_cases hu : IsUnit (n:ZMod q)
    · simp only [principalDifference,MulChar.one_apply hu,one_mul,sub_self]
    · exact (hnd (excluded_primePower_dvd_power q hn hl hu)).elim

theorem norm_principal_sharp_difference (q : ℕ) [NeZero q] (X : ℝ) :
    ‖sharpSum (fun n:ℕ => (1:DirichletCharacter ℂ q) n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-
      sharpSum (fun n:ℕ => (ArithmeticFunction.vonMangoldt n:ℂ)) X‖ ≤
      (Nat.log 2 ⌊X⌋₊:ℝ)*Real.log (q:ℝ) := by
  let K : ℕ := Nat.log 2 ⌊X⌋₊
  let N := Finset.range (⌊X⌋₊+1)
  let D := (q^K).divisors
  let S := N ∩ D
  have hqpow : q^K ≠ 0 := pow_ne_zero _ (NeZero.ne q)
  have hsub : S ⊆ N := Finset.inter_subset_left
  have hsum : (∑ n ∈ S, principalDifference q n) = ∑ n ∈ N, principalDifference q n := by
    apply Finset.sum_subset hsub
    intro n hn hnS
    have hn' : n ≤ ⌊X⌋₊ := by simpa only [N,Finset.mem_range,Nat.lt_add_one_iff] using hn
    apply principalDifference_eq_zero_of_not_dvd q hn'
    intro hd
    apply hnS
    exact Finset.mem_inter.mpr ⟨hn,Nat.mem_divisors.mpr ⟨hd,hqpow⟩⟩
  unfold sharpSum
  rw [← Finset.sum_sub_distrib]
  change ‖∑ n ∈ N, principalDifference q n‖ ≤ (K:ℝ)*Real.log (q:ℝ)
  rw [← hsum]
  calc
    _ ≤ ∑ n ∈ S, ‖principalDifference q n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ S, ArithmeticFunction.vonMangoldt n := Finset.sum_le_sum (fun n _ => principalDifference_norm_le q n)
    _ ≤ ∑ n ∈ D, ArithmeticFunction.vonMangoldt n :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun n _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    _ = Real.log ((q^K:ℕ):ℝ) := ArithmeticFunction.vonMangoldt_sum
    _ = _ := by rw [Nat.cast_pow,Real.log_pow]

lemma natLog_floor_le_realLog {X : ℝ} (hX : 1 ≤ X) :
    (Nat.log 2 ⌊X⌋₊:ℝ) ≤ Real.log X/Real.log 2 := by
  have hfloor : ⌊X⌋₊ ≠ 0 := by
    intro hz
    have h := Nat.lt_floor_add_one X
    rw [hz] at h
    norm_num at h
    linarith
  have hNat := Nat.pow_log_le_self 2 hfloor
  have hp : (2:ℝ)^(Nat.log 2 ⌊X⌋₊) ≤ X :=
    (show (2:ℝ)^(Nat.log 2 ⌊X⌋₊) ≤ (⌊X⌋₊:ℝ) by exact_mod_cast hNat).trans
      (Nat.floor_le (by linarith))
  have hlog := Real.log_le_log (by positivity : (0:ℝ) < 2^(Nat.log 2 ⌊X⌋₊)) hp
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))).mpr hlog

theorem norm_principal_sharp_difference_real (q : ℕ) [NeZero q] {X : ℝ} (hX : 1 ≤ X) :
    ‖sharpSum (fun n:ℕ => (1:DirichletCharacter ℂ q) n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-
      sharpSum (fun n:ℕ => (ArithmeticFunction.vonMangoldt n:ℂ)) X‖ ≤
      (Real.log X/Real.log 2)*Real.log (q:ℝ) := by
  apply (norm_principal_sharp_difference q X).trans
  exact mul_le_mul_of_nonneg_right (natLog_floor_le_realLog hX)
    (Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)))

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_PrincipalLogPower
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

lemma sharpSum_vonMangoldt_eq {X : ℝ} (hX : 0 ≤ X) :
    sharpSum (fun n:ℕ => (ArithmeticFunction.vonMangoldt n:ℂ)) X = (_root_.Erdos970.ChebyshevPsi X:ℂ) := by
  unfold sharpSum _root_.Erdos970.ChebyshevPsi
  rw [Nat.floor_add_one hX,Complex.ofReal_sum]

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeCountAbel
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosPrimeInputs.PrimeCountAbel

open _root_.Set _root_.Filter _root_.MeasureTheory
open _root_.Erdos970.Set _root_.Erdos970.Filter _root_.Erdos970.MeasureTheory
open scoped Topology

lemma mainKernel_continuous {a b : ℝ} (ha : 2 ≤ a) : ContinuousOn mainKernel (Icc a b) := by
  intro t ht
  have ht1 : 1 < t := by linarith [ht.1]
  have ht0 : t ≠ 0 := ne_of_gt (by linarith)
  have hlt0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht1)
  apply ContinuousAt.continuousWithinAt
  unfold mainKernel
  fun_prop (disch := simp [hlt0])

lemma mainKernel_integrable {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable mainKernel volume a b :=
  (mainKernel_continuous ha).intervalIntegrable_of_Icc hab

end ErdosPrimeInputs.PrimeCountAbel

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_ResidueSqrtSplit
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology BigOperators

lemma residuePsi_character_sum {q : ℕ} [NeZero q] (a : ZMod q) (ha : IsUnit a) (X : ℝ) :
    (residuePsi a X:ℂ) = (q.totient:ℂ)⁻¹ *
      ∑ chi : DirichletCharacter ℂ q, chi a⁻¹ *
        sharpSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X := by
  classical
  unfold residuePsi
  rw [Complex.ofReal_sum]
  simp_rw [ArithmeticFunction.vonMangoldt.residueClass_apply ha]
  rw [← Finset.mul_sum,Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro chi _
  unfold sharpSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

lemma residuePsi_error_le {q : ℕ} [NeZero q] (a : ZMod q) (ha : IsUnit a) (X E : ℝ)
    (herror : ∀ chi : DirichletCharacter ℂ q,
      ‖sharpSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-
        (if chi=1 then (X:ℂ) else 0)‖ ≤ E) :
    ‖(residuePsi a X:ℂ)-(X:ℂ)/(q.totient:ℂ)‖ ≤ E := by
  classical
  have hai : IsUnit a⁻¹ := isUnit_of_dvd_one ⟨a,(ZMod.inv_mul_of_unit a ha).symm⟩
  have hmain : (∑ chi : DirichletCharacter ℂ q,
      chi a⁻¹ * (if chi=1 then (X:ℂ) else 0)) = (X:ℂ) := by
    simp [MulChar.one_apply hai]
  have hsum : (∑ chi : DirichletCharacter ℂ q, chi a⁻¹ *
      (sharpSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-
        (if chi=1 then (X:ℂ) else 0))) =
      (∑ chi : DirichletCharacter ℂ q, chi a⁻¹ *
        sharpSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X)-(X:ℂ) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib,hmain]
  have he : (residuePsi a X:ℂ)-(X:ℂ)/(q.totient:ℂ) =
      (q.totient:ℂ)⁻¹ * ∑ chi : DirichletCharacter ℂ q, chi a⁻¹ *
      (sharpSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-
        (if chi=1 then (X:ℂ) else 0)) := by
    rw [residuePsi_character_sum a ha X,hsum]
    ring
  have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    simpa only [Nat.card_eq_fintype_card] using
      (DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q)
  have hphi : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hterm (chi : DirichletCharacter ℂ q) :
      ‖chi a⁻¹ * (sharpSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-
        (if chi=1 then (X:ℂ) else 0))‖ ≤ E := by
    rw [norm_mul]
    have h := mul_le_mul_of_nonneg_right (chi.norm_le_one a⁻¹)
      (norm_nonneg (sharpSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-
        (if chi=1 then (X:ℂ) else 0)))
    simp only [one_mul] at h
    exact h.trans (herror chi)
  have hnorm : ‖∑ chi : DirichletCharacter ℂ q, chi a⁻¹ *
      (sharpSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-
        (if chi=1 then (X:ℂ) else 0))‖ ≤ (q.totient:ℝ)*E := by
    calc
      _ ≤ ∑ chi : DirichletCharacter ℂ q, ‖chi a⁻¹ *
          (sharpSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-
            (if chi=1 then (X:ℂ) else 0))‖ := norm_sum_le _ _
      _ ≤ ∑ _chi : DirichletCharacter ℂ q, E := Finset.sum_le_sum (fun chi _ => hterm chi)
      _ = _ := by simp [hcard]
  rw [he,norm_mul,norm_inv,Complex.norm_natCast]
  calc
    _ ≤ (q.totient:ℝ)⁻¹*((q.totient:ℝ)*E) := mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = E := by rw [← mul_assoc,inv_mul_cancel₀ hphi.ne',one_mul]

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology BigOperators

lemma residuePrimeWeight_eq {q : ℕ} (a : ZMod q) (n : ℕ) :
    residuePrimeWeight a n = if n.Prime ∧ (n:ZMod q)=a then Real.log n else 0 := by
  classical
  by_cases hp : n.Prime
  · by_cases ha : (n:ZMod q)=a
    · simp [residuePrimeWeight,ArithmeticFunction.vonMangoldt.residueClass,hp,ha,
        ArithmeticFunction.vonMangoldt_apply_prime hp]
    · simp [residuePrimeWeight,ArithmeticFunction.vonMangoldt.residueClass,hp,ha]
  · simp [residuePrimeWeight,hp]

lemma residuePsi_sub_theta_bounds {q : ℕ} (a : ZMod q) (X : ℝ) :
    0 ≤ residuePsi a X-residueTheta a X ∧
    residuePsi a X-residueTheta a X ≤ Chebyshev.psi X-Chebyshev.theta X := by
  classical
  rw [residuePsi,residueTheta,← Finset.sum_sub_distrib]
  constructor
  · apply Finset.sum_nonneg
    intro n _
    unfold residuePrimeWeight
    split_ifs
    · simp only [sub_self,le_refl]
    · simpa only [sub_zero] using ArithmeticFunction.vonMangoldt.residueClass_nonneg a n
  · rw [Chebyshev.psi_eq_sum_Icc,Chebyshev.theta_eq_sum_Icc,Finset.sum_filter,
      ← Finset.sum_sub_distrib,← Nat.range_succ_eq_Icc_zero]
    apply Finset.sum_le_sum
    intro n _
    unfold residuePrimeWeight
    by_cases hp : n.Prime
    · simp [hp,ArithmeticFunction.vonMangoldt_apply_prime hp]
    · simpa only [hp,ite_false, if_false,sub_zero] using ArithmeticFunction.vonMangoldt.residueClass_le a n

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Finset _root_.MeasureTheory
open scoped Topology BigOperators

lemma intervalPrimes_zero_eq {X : ℝ} (hX : 0 ≤ X) (q : ℕ) (r : ℤ) :
    intervalPrimes 0 X q r = (range (⌊X⌋₊+1)).filter
      (fun n:ℕ => n.Prime ∧ (n:ZMod q)=(r:ZMod q)) := by
  classical
  ext n
  have hm : (n:ZMod q)=(r:ZMod q) ↔ Int.ModEq (q:ℤ) (n:ℤ) r := by
    simpa using (ZMod.intCast_eq_intCast_iff (n:ℤ) r q)
  rw [mem_intervalPrimes,mem_filter,mem_range,hm]
  constructor
  · rintro ⟨hp,_,hn,hr⟩
    refine ⟨Nat.lt_succ_of_le ((Nat.le_floor_iff hX).mpr ?_),hp,hr⟩
    simpa only [zero_add] using hn
  · rintro ⟨hn,hp,hr⟩
    refine ⟨hp,by exact_mod_cast hp.pos,?_,hr⟩
    simpa only [zero_add] using (Nat.le_floor_iff hX).mp (Nat.le_of_lt_succ hn)

lemma intervalPrimes_card_eq_sum_weight {X : ℝ} (hX : 0 ≤ X) (q : ℕ) (r : ℤ) :
    ((intervalPrimes 0 X q r).card:ℝ) =
      ∑ n ∈ Icc 0 ⌊X⌋₊, (Real.log n)⁻¹ * residuePrimeWeight (r:ZMod q) n := by
  classical
  rw [intervalPrimes_zero_eq hX,card_eq_sum_ones,Nat.range_succ_eq_Icc_zero,sum_filter]
  push_cast
  apply sum_congr rfl
  intro n _
  rw [residuePrimeWeight_eq]
  by_cases hp : n.Prime ∧ (n:ZMod q)=(r:ZMod q)
  · have hl : Real.log (n:ℝ) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one
      (by exact_mod_cast hp.1.pos) (by exact_mod_cast hp.1.ne_one)
    simp [hp,hl]
  · simp [hp]

lemma residueTheta_kernel_integrable (q : ℕ) (a : ZMod q) (X : ℝ) :
    IntegrableOn (fun t => residueTheta a t/(t*Real.log t^2)) (Set.Icc 2 X) volume := by
  conv => arg 1; ext; rw [residueTheta,Nat.range_succ_eq_Icc_zero,div_eq_mul_one_div,mul_comm]
  refine integrableOn_mul_sum_Icc _ (by norm_num) <| ContinuousOn.integrableOn_Icc ?_
  intro x hx
  have hx0 : x ≠ 0 := by linarith [hx.1]
  have hl0 : Real.log x ≠ 0 := (Real.log_pos (by linarith [hx.1])).ne'
  have hd : x*Real.log x^2 ≠ 0 := mul_ne_zero hx0 (pow_ne_zero 2 hl0)
  exact ContinuousAt.continuousWithinAt (by fun_prop)

theorem intervalPrimes_card_eq_theta {X : ℝ} (hX : 2 ≤ X) (q : ℕ) (r : ℤ) :
    ((intervalPrimes 0 X q r).card:ℝ) =
      residueTheta (r:ZMod q) X/Real.log X +
        ∫ t in 2..X, residueTheta (r:ZMod q) t/(t*Real.log t^2) := by
  rw [intervalPrimes_card_eq_sum_weight (by linarith) q r]
  rw [sum_mul_eq_sub_integral_mul₁ (residuePrimeWeight (r:ZMod q))
    (f := fun n => (Real.log n)⁻¹) (by simp [residuePrimeWeight])
    (by simp [residuePrimeWeight]),← intervalIntegral.integral_of_le hX]
  · have hi (f : ℝ → ℝ) :
        ∫ u in 2..X, deriv (fun x => (Real.log x)⁻¹) u*f u =
        ∫ u in 2..X, f u * -(u*Real.log u^2)⁻¹ :=
      intervalIntegral.integral_congr fun u _ => by simp [field]
    rw [hi]
    simp only [residueTheta,Nat.range_succ_eq_Icc_zero,div_eq_mul_inv,mul_neg,
      intervalIntegral.integral_neg,sub_neg_eq_add]
    ring
  · intro z hz
    have hz0 : z ≠ 0 := by linarith [hz.1]
    have hl0 : Real.log z ≠ 0 := (Real.log_pos (by linarith [hz.1])).ne'
    fun_prop
  · refine ContinuousOn.integrableOn_Icc fun z hz => ContinuousWithinAt.congr ?_
      (fun _ _ => Real.deriv_inv_log_apply) Real.deriv_inv_log_apply
    have hz0 : z ≠ 0 := by linarith [hz.1]
    have hl0 : Real.log z^2 ≠ 0 := pow_ne_zero 2 (Real.log_pos (by linarith [hz.1])).ne'
    exact ContinuousAt.continuousWithinAt (by fun_prop)

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.MeasureTheory
open scoped Topology BigOperators
open ErdosPrimeInputs.PrimeCountAbel (logarithmicIntegral mainKernel)

lemma residueErrorKernel_integrable {q : ℕ} (a : ZMod q) {u v : ℝ}
    (hu : 2 ≤ u) (huv : u ≤ v) : IntervalIntegrable (residueErrorKernel a) volume u v := by
  apply IntervalIntegrable.sub
  · apply (intervalIntegrable_iff_integrableOn_Icc_of_le huv).mpr
    exact (residueTheta_kernel_integrable q a v).mono_set (Set.Icc_subset_Icc_left hu)
  · exact (ErdosPrimeInputs.PrimeCountAbel.mainKernel_integrable hu huv).div_const _

lemma residueErrorKernel_eq {q : ℕ} (a : ZMod q) {t : ℝ} (ht : 0 < t) :
    residueErrorKernel a t = (residueTheta a t-t/(q.totient:ℝ))/(t*Real.log t^2) := by
  unfold residueErrorKernel mainKernel
  field_simp

theorem intervalPrimes_error_eq {X : ℝ} (hX : 2 ≤ X) (q : ℕ) (r : ℤ) :
    ((intervalPrimes 0 X q r).card:ℝ)-logarithmicIntegral X/(q.totient:ℝ) =
      2/((q.totient:ℝ)*Real.log 2) +
        (residueTheta (r:ZMod q) X-X/(q.totient:ℝ))/Real.log X +
          ∫ t in 2..X, residueErrorKernel (r:ZMod q) t := by
  have hli := _root_.Erdos970.integral_log_inv 2 X (by norm_num) hX
  have hi : (∫ t in 2..X, residueErrorKernel (r:ZMod q) t) =
      (∫ t in 2..X, residueTheta (r:ZMod q) t/(t*Real.log t^2)) -
        (∫ t in 2..X, mainKernel t)/(q.totient:ℝ) := by
    unfold residueErrorKernel
    rw [intervalIntegral.integral_sub,
      intervalIntegral.integral_div]
    · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hX).mpr
        (residueTheta_kernel_integrable q _ X)
    · exact (ErdosPrimeInputs.PrimeCountAbel.mainKernel_integrable (by norm_num) hX).div_const _
  rw [intervalPrimes_card_eq_theta hX,hi]
  unfold logarithmicIntegral mainKernel
  simp only [one_div]
  rw [hli]
  ring

lemma residueTheta_nonneg {q : ℕ} (a : ZMod q) (t : ℝ) : 0 ≤ residueTheta a t := by
  apply Finset.sum_nonneg
  intro n _
  unfold residuePrimeWeight
  split_ifs
  · exact ArithmeticFunction.vonMangoldt.residueClass_nonneg a n
  · exact le_refl 0

lemma residueTheta_le_theta {q : ℕ} (a : ZMod q) (t : ℝ) :
    residueTheta a t ≤ Chebyshev.theta t := by
  classical
  rw [residueTheta,Chebyshev.theta_eq_sum_Icc,Finset.sum_filter,Nat.range_succ_eq_Icc_zero]
  apply Finset.sum_le_sum
  intro n _
  unfold residuePrimeWeight
  by_cases hp : n.Prime
  · simpa only [hp,ite_true, if_true,ArithmeticFunction.vonMangoldt_apply_prime hp] using
      ArithmeticFunction.vonMangoldt.residueClass_le a n
  · simp [hp]

lemma residueErrorKernel_coarse {q : ℕ} [NeZero q] (a : ZMod q) {t : ℝ} (ht : 2 ≤ t) :
    |residueErrorKernel a t| ≤ (Real.log 4+1)/(Real.log 2)^2 := by
  have ht0 : 0 < t := by linarith
  have hl : 0 < Real.log t := Real.log_pos (by linarith)
  have hphi : (1:ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hdiv : t/(q.totient:ℝ) ≤ t := div_le_self ht0.le hphi
  have hnum : |residueTheta a t-t/(q.totient:ℝ)| ≤ (Real.log 4+1)*t := by
    calc
      _ ≤ |residueTheta a t|+|t/(q.totient:ℝ)| := abs_sub _ _
      _ = residueTheta a t+t/(q.totient:ℝ) := by rw [abs_of_nonneg (residueTheta_nonneg a t),abs_of_nonneg (by positivity)]
      _ ≤ Real.log 4*t+t := add_le_add ((residueTheta_le_theta a t).trans
        (Chebyshev.theta_le_log4_mul_x ht0.le)) hdiv
      _ = _ := by ring
  rw [residueErrorKernel_eq a ht0,abs_div,abs_of_pos (by positivity : 0 < t*Real.log t^2)]
  calc
    _ ≤ ((Real.log 4+1)*t)/(t*Real.log t^2) := div_le_div_of_nonneg_right hnum (by positivity)
    _ = (Real.log 4+1)/Real.log t^2 := by field_simp
    _ ≤ _ := by
      have hlog : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (sq_le_sq₀ (Real.log_pos (by norm_num : (1:ℝ)<2)).le hl.le |>.mpr hlog)

lemma residueErrorKernel_low_integral {q : ℕ} [NeZero q] (a : ZMod q) {Y : ℝ} (hY : 2 ≤ Y) :
    |∫ t in 2..Y, residueErrorKernel a t| ≤ (Real.log 4+1)/(Real.log 2)^2*Y := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a:=2) (b:=Y)
    (f:=residueErrorKernel a) (C:=(Real.log 4+1)/(Real.log 2)^2) (fun t ht => by
      rw [Set.uIoc_of_le hY] at ht
      simpa only [Real.norm_eq_abs] using residueErrorKernel_coarse a ht.1.le)
  rw [Real.norm_eq_abs,abs_of_nonneg (by linarith : 0 ≤ Y-2)] at h
  exact h.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SiegelWalfisz
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter _root_.MeasureTheory
open scoped Topology
open ErdosPrimeInputs.PrimeCountAbel (logarithmicIntegral)

lemma isUnit_intCast_of_isCoprime {q : ℕ} {r : ℤ} (hr : IsCoprime r (q:ℤ)) :
    IsUnit (r:ZMod q) := by
  obtain ⟨u,v,huv⟩ := hr
  have hc : (u:ZMod q)*(r:ZMod q)+(v:ZMod q)*(q:ZMod q)=1 := by
    have h := congrArg (fun z:ℤ => (z:ZMod q)) huv
    push_cast at h
    exact h
  simp only [ZMod.natCast_self,mul_zero,add_zero] at hc
  apply isUnit_of_dvd_one
  exact ⟨(u:ZMod q),by simpa only [mul_comm] using hc.symm⟩

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_LargeModulusSiegelWalfisz
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

lemma cubeHeight_pos {X : ℝ} (hX : 1 < X) : 0 < cubeHeight X :=
  Real.rpow_pos_of_pos (Real.log_pos hX) _

lemma cubeHeight_pow_three {X : ℝ} (hX : 1 ≤ X) : (cubeHeight X)^3 = Real.log X := by
  unfold cubeHeight
  rw [← Real.rpow_mul_natCast (Real.log_nonneg hX)]
  norm_num

lemma cubeHeight_mono {X Y : ℝ} (hX : 1 < X) (hXY : X ≤ Y) : cubeHeight X ≤ cubeHeight Y :=
  Real.rpow_le_rpow (Real.log_pos hX).le (Real.log_le_log (by linarith) hXY) (by norm_num)

lemma cubeHeight_tendsto : Tendsto cubeHeight atTop atTop :=
  (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/3)).comp Real.tendsto_log_atTop

lemma eventually_polynomial_le_exp (K : ℝ) (n : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ h : ℝ in atTop, 1 ≤ h ∧ K*h^n ≤ Real.exp (c*h) := by
  have hl : Tendsto (fun h:ℝ => K*h^n*Real.exp (-c*h)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast,mul_assoc,mul_zero] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n:ℝ) c hc).const_mul K
  filter_upwards [eventually_ge_atTop (1:ℝ),hl.eventually (gt_mem_nhds zero_lt_one)] with h hh hsmall
  refine ⟨hh,?_⟩
  have hm := mul_le_mul_of_nonneg_right hsmall.le (Real.exp_pos (c*h)).le
  have he : Real.exp (-c*h)*Real.exp (c*h)=1 := by rw [← Real.exp_add,show -c*h+c*h=0 by ring,Real.exp_zero]
  simpa only [mul_assoc,he,mul_one,one_mul] using hm

lemma exponential_height_bound {h : ℝ} (hh : Real.log 7 ≤ h) (q : ℕ) [NeZero q]
    (hq : (q:ℝ) ≤ Real.exp h) : modulusHeight q (Real.exp h) ≤ 3*h := by
  have hh0 : 0 < h := (Real.log_pos (by norm_num : (1:ℝ)<7)).trans_le hh
  have hT : 1 ≤ Real.exp h := Real.one_le_exp_iff.mpr hh0.le
  have hq0 : (0:ℝ) < q := by exact_mod_cast NeZero.pos q
  have hql : Real.log (q:ℝ) ≤ h := by
    have he := Real.log_le_log hq0 hq
    simpa only [Real.log_exp] using he
  have hsum : Real.exp h+6 ≤ 7*Real.exp h := by linarith
  have hl : Real.log (Real.exp h+6) ≤ Real.log 7+h := by
    have he := Real.log_le_log (by positivity : 0 < Real.exp h+6) hsum
    rwa [Real.log_mul (by norm_num : (7:ℝ)≠0) (Real.exp_ne_zero h),Real.log_exp] at he
  unfold modulusHeight
  rw [abs_of_pos (Real.exp_pos h)]
  linarith

lemma exponential_left_saving {a X : ℝ} (ha : 0 < a) (hX : 1 < X)
    (hh : Real.log 7 ≤ cubeHeight X) (q : ℕ) [NeZero q]
    (hq : (q:ℝ) ≤ Real.exp (cubeHeight X)) :
    Real.exp (-a*Real.log X/(modulusHeight q (Real.exp (cubeHeight X)))^2) ≤
      Real.exp (-(a/9)*cubeHeight X) := by
  let h := cubeHeight X
  let H := modulusHeight q (Real.exp h)
  have hh0 : 0 < h := cubeHeight_pos hX
  have hH : 0 < H := lt_of_lt_of_le zero_lt_one (modulusHeight_ge_one q _)
  have hHle : H ≤ 3*h := exponential_height_bound hh q hq
  have hsq : H^2 ≤ 9*h^2 := by nlinarith [sq_nonneg (3*h-H)]
  have hcube : h^3 = Real.log X := cubeHeight_pow_three hX.le
  apply Real.exp_le_exp.mpr
  change -a*Real.log X/H^2 ≤ -(a/9)*h
  apply (div_le_iff₀ (sq_pos_of_pos hH)).mpr
  rw [← hcube]
  have hm := mul_le_mul_of_nonneg_left hsq (show 0 ≤ (a/9)*h by positivity)
  nlinarith

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

lemma eventually_exponential_contour_savings {a : ℝ} (ha : 0 < a) (ha100 : a ≤ 1/100) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1/2 ∧ ∀ᶠ X : ℝ in atTop,
      3 ≤ X ∧ 1 ≤ Real.log X ∧ ∀ (q : ℕ) [NeZero q],
      (q:ℝ) ≤ Real.exp (cubeHeight X) →
      let T := Real.exp (cubeHeight X)
      let H := modulusHeight q T
      H^3*Real.exp (-a*Real.log X/H^2) ≤ Real.exp (-c*cubeHeight X) ∧
      H^3/(1+T^2) ≤ Real.exp (-c*cubeHeight X) ∧
      Real.log X/T ≤ Real.exp (-c*cubeHeight X) := by
  let c : ℝ := a/18
  have hc : 0 < c := by dsimp [c] <;> positivity
  have hc2 : c ≤ 1/2 := by dsimp [c] <;> linarith
  refine ⟨c,hc,hc2,?_⟩
  filter_upwards [eventually_ge_atTop (3:ℝ),
    cubeHeight_tendsto.eventually (eventually_ge_atTop (Real.log 7)),
    cubeHeight_tendsto.eventually (eventually_polynomial_le_exp 27 3 hc)] with X hX hh7 hhpoly
  have hx1 : 1 < X := by linarith
  have hx0 : 0 < X := by linarith
  have hL : 1 ≤ Real.log X :=
    ((Real.lt_log_iff_exp_lt hx0).mpr (Real.exp_one_lt_three.trans_le hX)).le
  refine ⟨hX,hL,?_⟩
  intro q _ hq
  let h := cubeHeight X
  let T := Real.exp h
  let H := modulusHeight q T
  have hh : 0 < h := cubeHeight_pos hx1
  have hH : 0 < H := lt_of_lt_of_le zero_lt_one (modulusHeight_ge_one q _)
  have hHle : H ≤ 3*h := exponential_height_bound hh7 q hq
  have hHp : H^3 ≤ Real.exp (c*h) := by
    have hp := pow_le_pow_left₀ hH.le hHle 3
    calc
      _ ≤ (3*h)^3 := hp
      _ = 27*h^3 := by ring
      _ ≤ _ := hhpoly.2
  have hLp : Real.log X ≤ Real.exp (c*h) := by
    calc
      _ = h^3 := (cubeHeight_pow_three hx1.le).symm
      _ ≤ 27*h^3 := by nlinarith [pow_nonneg hh.le 3]
      _ ≤ _ := hhpoly.2
  have hs := exponential_left_saving ha hx1 hh7 q hq
  have hT2 : T^2 = Real.exp (2*h) := by
    dsimp [T]
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  refine ⟨?_,?_,?_⟩
  · calc
      _ ≤ Real.exp (c*h)*Real.exp (-(a/9)*h) :=
        mul_le_mul hHp hs (Real.exp_pos _).le (Real.exp_pos _).le
      _ = Real.exp (-c*h) := by rw [← Real.exp_add]; congr 1; dsimp [c] <;> ring
  · calc
      _ ≤ H^3/T^2 := div_le_div_of_nonneg_left (by positivity) (by dsimp [T] <;> positivity) (by linarith)
      _ ≤ Real.exp (c*h)/T^2 := div_le_div_of_nonneg_right hHp (sq_nonneg _)
      _ = Real.exp (c*h-2*h) := by rw [hT2,Real.exp_sub]
      _ ≤ Real.exp (-c*h) := Real.exp_le_exp.mpr (by nlinarith)
  · calc
      _ ≤ Real.exp (c*h)/T := div_le_div_of_nonneg_right hLp (by dsimp [T] <;> positivity)
      _ = Real.exp (c*h-h) := by dsimp [T]; rw [Real.exp_sub]
      _ ≤ Real.exp (-c*h) := Real.exp_le_exp.mpr (by nlinarith)

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

theorem riesz_character_exponential :
    ∃ c K : ℝ, 0 < c ∧ c ≤ 1/2 ∧ 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q), chi ≠ 1 →
      (q:ℝ) ≤ Real.exp (cubeHeight X) →
      ‖rieszSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X‖ ≤
        K*X*Real.exp (-c*cubeHeight X) := by
  obtain ⟨a,ha,ha100,C,hC,B,hB,hcontour⟩ := exists_uniform_riesz_contour_bound_jb247
  obtain ⟨c,hc,hc2,hsavings⟩ := eventually_exponential_contour_savings ha ha100
  let P : ℝ := 4*Real.pi*C+16*C*Real.exp 1+8*(B+1)*Real.exp 1
  let K : ℝ := (1/(2*Real.pi))*P
  have hP : 0 < P := by dsimp only [P] <;> positivity
  have hK : 0 < K := by dsimp only [K] <;> positivity
  refine ⟨c,K,hc,hc2,hK,?_⟩
  filter_upwards [hsavings] with X hX
  intro q _ chi hchi hq
  obtain ⟨hX3,hL1,hSavings⟩ := hX
  obtain ⟨hleft,hhor,hratio⟩ := hSavings q hq
  let L : ℝ := Real.log X
  let T : ℝ := Real.exp (cubeHeight X)
  let R : ℝ := Real.exp (-c*cubeHeight X)
  let H : ℝ := modulusHeight q T
  let sigma : ℝ := 1+L⁻¹
  have hXp : 0 < X := by linarith
  have hX1 : 1 < X := by linarith
  have hLp : 0 < L := by linarith
  have hTp : 0 < T := Real.exp_pos _
  have hs1 : 1 < sigma := by
    have hi : 0 < L⁻¹ := inv_pos.mpr hLp
    dsimp only [sigma]
    linarith
  have hs2 : sigma ≤ 2 := by
    have hinv : L⁻¹ ≤ 1 := by rw [← one_div]; exact (div_le_iff₀ hLp).mpr (by linarith)
    dsimp only [sigma]
    linarith
  have h := hcontour q chi hchi X sigma T (by linarith) hs1 hs2 hTp
  have hrightpow : X^sigma = X*Real.exp 1 := rpow_perron_sigma hX1
  have hleftpow : X^(rieszContourLeft a q T) = X*Real.exp (-a*L/H^2) := rpow_rieszContourLeft hXp a q T
  have hinv : (sigma-1)⁻¹ = L := by dsimp only [sigma]; rw [add_sub_cancel_left,inv_inv]
  rw [hrightpow,hleftpow,hinv] at h
  change H^3*Real.exp (-a*L/H^2) ≤ R at hleft
  change H^3/(1+T^2) ≤ R at hhor
  change L/T ≤ R at hratio
  have hBL := mul_le_mul_of_nonneg_left (show 1 ≤ L by linarith) hB
  have hLB : L+B ≤ (B+1)*L := by nlinarith only [hBL]
  have htail : (L+B)/T ≤ (B+1)*R := by
    calc
      _ ≤ ((B+1)*L)/T := div_le_div_of_nonneg_right hLB hTp.le
      _ = (B+1)*(L/T) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hratio (by linarith)
  have h1 := mul_le_mul_of_nonneg_left hleft (show 0 ≤ 4*Real.pi*C*X by positivity)
  have h2 := mul_le_mul_of_nonneg_left hhor (show 0 ≤ 16*C*Real.exp 1*X by positivity)
  have h3 := mul_le_mul_of_nonneg_left htail (show 0 ≤ 8*Real.exp 1*X by positivity)
  have he : 4*Real.pi*C*H^3*(X*Real.exp (-a*L/H^2)) +
      16*C*H^3*(X*Real.exp 1)/(1+T^2)+8*(L+B)*(X*Real.exp 1)/T ≤ P*X*R := by
    calc
      _ = (4*Real.pi*C*X)*(H^3*Real.exp (-a*L/H^2)) +
          (16*C*Real.exp 1*X)*(H^3/(1+T^2))+(8*Real.exp 1*X)*((L+B)/T) := by ring
      _ ≤ (4*Real.pi*C*X)*R+(16*C*Real.exp 1*X)*R+
          (8*Real.exp 1*X)*((B+1)*R) := add_le_add (add_le_add h1 h2) h3
      _ = _ := by dsimp only [P] <;> ring
  apply h.trans
  calc
    _ ≤ (1/(2*Real.pi))*(P*X*R) := mul_le_mul_of_nonneg_left he (by positivity)
    _ = K*X*Real.exp (-c*cubeHeight X) := by dsimp only [K,R] <;> ring

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

lemma cubeHeight_le_log {X : ℝ} (hX : 1 ≤ X) (hh : 1 ≤ cubeHeight X) :
    cubeHeight X ≤ Real.log X := by
  have hp : 1 ≤ (cubeHeight X)^2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hp (show 0 ≤ cubeHeight X by linarith)
  rw [← cubeHeight_pow_three hX]
  nlinarith

lemma exponential_recovery_scale {d X : ℝ} (hd : 0 < d) (hd1 : d ≤ 1)
    (hX : 3 ≤ X) (hh : 1 ≤ cubeHeight X) :
    let delta := Real.exp (-d*cubeHeight X)
    let Y := (1+delta)*X
    0 < delta ∧ delta ≤ 1 ∧ 1 ≤ delta*X ∧ X ≤ Y ∧ Y ≤ 2*X ∧
      cubeHeight X ≤ cubeHeight Y ∧ Real.log Y ≤ 2*Real.log X := by
  let delta := Real.exp (-d*cubeHeight X)
  let Y := (1+delta)*X
  have hx0 : 0 < X := by linarith
  have hx1 : 1 < X := by linarith
  have hh0 : 0 < cubeHeight X := cubeHeight_pos hx1
  have hdpos : 0 < delta := Real.exp_pos _
  have hdle : delta ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hsmall : d*cubeHeight X ≤ Real.log X := by
    calc
      _ ≤ cubeHeight X := by nlinarith
      _ ≤ _ := cubeHeight_le_log hx1.le hh
  have hpower : Real.exp (d*cubeHeight X) ≤ X := by
    simpa only [Real.exp_log hx0] using Real.exp_le_exp.mpr hsmall
  have hid : delta*Real.exp (d*cubeHeight X)=1 := by
    dsimp [delta]
    rw [← Real.exp_add,show -d*cubeHeight X+d*cubeHeight X=0 by ring,Real.exp_zero]
  have hdX : 1 ≤ delta*X := by
    have hm := mul_le_mul_of_nonneg_left hpower hdpos.le
    rwa [hid] at hm
  have hXY : X ≤ Y := by dsimp [Y] <;> nlinarith
  have hY2 : Y ≤ 2*X := by dsimp [Y] <;> nlinarith
  have hY0 : 0 < Y := hx0.trans_le hXY
  have hhY : cubeHeight X ≤ cubeHeight Y := cubeHeight_mono hx1 hXY
  have hlog2 : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) (by linarith)
  have hlogY : Real.log Y ≤ 2*Real.log X := by
    have h := Real.log_le_log hY0 hY2
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hx0.ne'] at h
    linarith
  exact ⟨hdpos,hdle,hdX,hXY,hY2,hhY,hlogY⟩

lemma exponential_recovery_tail {c X : ℝ} (hc : 0 < c) (hc2 : c ≤ 1/2)
    (hX : 3 ≤ X) (hh : 1 ≤ cubeHeight X)
    (hpoly : (cubeHeight X)^3 ≤ Real.exp ((c/4)*cubeHeight X)) :
    let delta := Real.exp (-(c/2)*cubeHeight X)
    (delta*X+1)*Real.log ((1+delta)*X) ≤ 4*X*Real.exp (-(c/4)*cubeHeight X) := by
  let delta := Real.exp (-(c/2)*cubeHeight X)
  obtain ⟨hd,_,hdX,hXY,_,_,hlogY⟩ := exponential_recovery_scale (d:=c/2)
    (by positivity) (by linarith) hX hh
  have hx0 : 0 < X := by linarith
  have hY0 : 0 < (1+delta)*X := by positivity
  have hlogY0 : 0 ≤ Real.log ((1+delta)*X) := Real.log_nonneg (by linarith)
  have hprod : delta*Real.log X ≤ Real.exp (-(c/4)*cubeHeight X) := by
    calc
      _ = delta*(cubeHeight X)^3 := by rw [cubeHeight_pow_three (by linarith : 1≤X)]
      _ ≤ delta*Real.exp ((c/4)*cubeHeight X) := mul_le_mul_of_nonneg_left hpoly hd.le
      _ = _ := by dsimp [delta]; rw [← Real.exp_add]; congr 1; ring
  calc
    _ ≤ (2*delta*X)*(2*Real.log X) := mul_le_mul (by nlinarith) hlogY hlogY0 (by positivity)
    _ = 4*X*(delta*Real.log X) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod (by positivity)

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

theorem sharp_character_exponential :
    ∃ c K : ℝ, 0 < c ∧ c ≤ 1/2 ∧ 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q), chi ≠ 1 →
      (q:ℝ) ≤ Real.exp (cubeHeight X) →
      ‖sharpSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X‖ ≤
        K*X*Real.exp (-c*cubeHeight X) := by
  obtain ⟨c,C,hc,hc2,hC,hRiesz⟩ := riesz_character_exponential
  obtain ⟨X0,hX0⟩ := eventually_atTop.mp hRiesz
  refine ⟨c/4,5*C+4,by positivity,by linarith,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop X0,eventually_ge_atTop (3:ℝ),
    cubeHeight_tendsto.eventually (eventually_polynomial_le_exp 1 3 (by positivity : 0 < c/4))]
    with X hthreshold hX hpoly
  intro q _ chi hchi hq
  let h := cubeHeight X
  let delta := Real.exp (-(c/2)*h)
  let Y := (1+delta)*X
  let f : ℕ → ℂ := fun n => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)
  have hx0 : 0 < X := by linarith
  have hx1 : 1 < X := by linarith
  have hh0 : 0 < h := cubeHeight_pos hx1
  obtain ⟨hd,hd1,hdX,hXY,hY2,hhY,_⟩ := exponential_recovery_scale (d:=c/2)
    (by positivity) (by linarith) hX hpoly.1
  have hqY : (q:ℝ) ≤ Real.exp (cubeHeight Y) := hq.trans (Real.exp_le_exp.mpr hhY)
  have hx := hX0 X hthreshold q chi hchi hq
  have hy := hX0 Y (hthreshold.trans hXY) q chi hchi hqY
  have hdecay : Real.exp (-c*cubeHeight Y) ≤ Real.exp (-c*h) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hy' : ‖rieszSum f Y‖ ≤ 2*C*X*Real.exp (-c*h) := by
    calc
      _ ≤ C*Y*Real.exp (-c*cubeHeight Y) := hy
      _ ≤ C*Y*Real.exp (-c*h) := mul_le_mul_of_nonneg_left hdecay (by positivity)
      _ ≤ C*(2*X)*Real.exp (-c*h) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hY2 hC.le) (Real.exp_pos _).le
      _ = _ := by ring
  have hnum : (1+delta)*‖rieszSum f Y‖+‖rieszSum f X‖ ≤ 5*C*X*Real.exp (-c*h) := by
    have h1 := mul_le_mul_of_nonneg_left hy' (show 0 ≤ 1+delta by linarith)
    have h2 := mul_le_mul_of_nonneg_right (show 1+delta ≤ 2 by linarith)
      (show 0 ≤ 2*C*X*Real.exp (-c*h) by positivity)
    apply (add_le_add (h1.trans h2) hx).trans_eq
    ring
  have hterm : ((1+delta)*‖rieszSum f Y‖+‖rieszSum f X‖)/delta ≤
      5*C*X*Real.exp (-(c/4)*h) := by
    calc
      _ ≤ (5*C*X*Real.exp (-c*h))/delta := div_le_div_of_nonneg_right hnum hd.le
      _ = 5*C*X*Real.exp (-(c/2)*h) := by
        dsimp [delta]
        rw [mul_div_assoc,← Real.exp_sub]
        congr 1
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by positivity)
  have htail := exponential_recovery_tail hc hc2 hX hpoly.1 (by simpa only [one_mul] using hpoly.2)
  have hcoeff : ∀ n : ℕ, 0 < n → ‖f n‖ ≤ Real.log (n:ℝ) :=
    fun n _ => character_vonMangoldt_norm_le chi n
  have hsharp := sharpSum_norm_le_riesz f hcoeff (show 1 ≤ X by linarith) hd
  apply (hsharp.trans (add_le_add hterm htail)).trans_eq
  ring

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

lemma eventually_polynomial_le_X_exp (K : ℝ) (n : ℕ) (d : ℝ) :
    ∀ᶠ X : ℝ in atTop, K*(cubeHeight X)^n ≤ X*Real.exp (-d*cubeHeight X) := by
  filter_upwards [eventually_ge_atTop (3:ℝ),
    cubeHeight_tendsto.eventually (eventually_ge_atTop (d+1)),
    cubeHeight_tendsto.eventually (eventually_polynomial_le_exp K n (by norm_num : (0:ℝ)<1))]
    with X hX hd hp
  let h := cubeHeight X
  have hh : 0 ≤ h := by linarith [hp.1]
  have hh2 : h ≤ h^2 := by nlinarith [hp.1]
  have hsq : d+1 ≤ h^2 := hd.trans hh2
  have hm := mul_le_mul_of_nonneg_right hsq hh
  have hcube : h^3=Real.log X := cubeHeight_pow_three (by linarith)
  have he : h ≤ Real.log X-d*h := by rw [← hcube]; nlinarith
  calc
    _ ≤ Real.exp h := by simpa only [one_mul] using hp.2
    _ ≤ Real.exp (Real.log X-d*h) := Real.exp_le_exp.mpr he
    _ = X*Real.exp (-d*h) := by rw [sub_eq_add_neg,Real.exp_add,Real.exp_log (by linarith : 0<X)]; congr 1; congr 1; ring

lemma eventually_sqrt_le_X_exp (d : ℝ) :
    ∀ᶠ X : ℝ in atTop, Real.sqrt X ≤ X*Real.exp (-d*cubeHeight X) := by
  filter_upwards [eventually_ge_atTop (3:ℝ),
    cubeHeight_tendsto.eventually (eventually_ge_atTop (max 1 (2*d)))] with X hX hh
  let h := cubeHeight X
  have hh1 : 1 ≤ h := (le_max_left _ _).trans hh
  have hhd : 2*d ≤ h := (le_max_right _ _).trans hh
  have hsq : 2*d ≤ h^2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hsq (show 0 ≤ h by linarith)
  have hcube : h^3=Real.log X := cubeHeight_pow_three (by linarith)
  have he : Real.log X*((1:ℝ)/2) ≤ Real.log X-d*h := by rw [← hcube]; nlinarith
  rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos (by linarith : 0<X)]
  calc
    _ ≤ Real.exp (Real.log X-d*h) := Real.exp_le_exp.mpr he
    _ = X*Real.exp (-d*h) := by rw [sub_eq_add_neg,Real.exp_add,Real.exp_log (by linarith : 0<X)]; congr 1; congr 1; ring

lemma eventually_exp_sqrt_log_le {a d : ℝ} (ha : 0 < a) (hd : 0 < d) :
    ∀ᶠ X : ℝ in atTop,
      Real.exp (-a*Real.sqrt (Real.log X)) ≤ Real.exp (-d*cubeHeight X) := by
  filter_upwards [eventually_ge_atTop (3:ℝ),
    cubeHeight_tendsto.eventually (eventually_ge_atTop (max 1 ((d/a)^2)))] with X hX hh
  let h := cubeHeight X
  have hh1 : 1 ≤ h := (le_max_left _ _).trans hh
  have hh0 : 0 ≤ h := by linarith
  have hsq : (d/a)^2 ≤ h := (le_max_right _ _).trans hh
  have hda : d/a ≤ Real.sqrt h := (Real.le_sqrt (by positivity) hh0).mpr hsq
  have hmul : d ≤ a*Real.sqrt h := by
    have he := (div_le_iff₀ ha).mp hda
    simpa only [mul_comm] using he
  have hsqrt : Real.sqrt (Real.log X) = h*Real.sqrt h := by
    rw [← cubeHeight_pow_three (by linarith : 1≤X),show (cubeHeight X)^3=(cubeHeight X)^2*cubeHeight X by ring,
      Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hh0]
  have hm := mul_le_mul_of_nonneg_right hmul hh0
  apply Real.exp_le_exp.mpr
  rw [hsqrt]
  nlinarith

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

lemma ordinary_psi_exponential {d : ℝ} (hd : 0 < d) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ‖sharpSum (fun n:ℕ => (ArithmeticFunction.vonMangoldt n:ℂ)) X-(X:ℂ)‖ ≤
        K*X*Real.exp (-d*cubeHeight X) := by
  obtain ⟨a,ha,hPNT⟩ := _root_.Erdos970.Strong_PNT
  obtain ⟨K,hK,hbound⟩ := hPNT.exists_pos
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound.bound,eventually_exp_sqrt_log_le ha hd,
    eventually_ge_atTop (3:ℝ)] with X hb he hX
  have hx0 : 0 < X := by linarith
  change ‖_root_.Erdos970.ChebyshevPsi X-X‖ ≤ K*‖X*Real.exp (-a*(Real.log X)^(1/2:ℝ))‖ at hb
  rw [sharpSum_vonMangoldt_eq hx0.le,← Complex.ofReal_sub,Complex.norm_real]
  simp only [Real.norm_eq_abs] at hb ⊢
  rw [abs_of_nonneg (by positivity : 0≤X*Real.exp (-a*(Real.log X)^(1/2:ℝ))),
    ← Real.sqrt_eq_rpow] at hb
  calc
    _ ≤ K*(X*Real.exp (-a*Real.sqrt (Real.log X))) := hb
    _ ≤ K*(X*Real.exp (-d*cubeHeight X)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he hx0.le) hK.le
    _ = _ := by ring

lemma principal_difference_exponential (d : ℝ) :
    ∀ᶠ X : ℝ in atTop, ∀ (q : ℕ) [NeZero q], (q:ℝ) ≤ Real.exp (cubeHeight X) →
      ‖sharpSum (fun n:ℕ => (1:DirichletCharacter ℂ q) n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-
        sharpSum (fun n:ℕ => (ArithmeticFunction.vonMangoldt n:ℂ)) X‖ ≤ X*Real.exp (-d*cubeHeight X) := by
  filter_upwards [eventually_ge_atTop (3:ℝ),eventually_polynomial_le_X_exp (1/Real.log 2) 4 d]
    with X hX hpoly
  intro q _ hq
  have hx1 : 1 < X := by linarith
  have hL : 0 ≤ Real.log X := (Real.log_pos hx1).le
  have hq0 : (0:ℝ) < q := by exact_mod_cast NeZero.pos q
  have hql : Real.log (q:ℝ) ≤ cubeHeight X := by
    have he := Real.log_le_log hq0 hq
    simpa only [Real.log_exp] using he
  calc
    _ ≤ (Real.log X/Real.log 2)*Real.log (q:ℝ) := norm_principal_sharp_difference_real q hx1.le
    _ ≤ (Real.log X/Real.log 2)*cubeHeight X := mul_le_mul_of_nonneg_left hql (by positivity)
    _ = (1/Real.log 2)*(cubeHeight X)^4 := by rw [← cubeHeight_pow_three hx1.le]; ring
    _ ≤ _ := hpoly

theorem principal_character_exponential {d : ℝ} (hd : 0 < d) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop, ∀ (q : ℕ) [NeZero q],
      (q:ℝ) ≤ Real.exp (cubeHeight X) →
      ‖sharpSum (fun n:ℕ => (1:DirichletCharacter ℂ q) n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-(X:ℂ)‖ ≤
        K*X*Real.exp (-d*cubeHeight X) := by
  obtain ⟨K,hK,hOrd⟩ := ordinary_psi_exponential hd
  refine ⟨1+K,by positivity,?_⟩
  filter_upwards [principal_difference_exponential d,hOrd] with X hDiff hOrd
  intro q _ hq
  have hn := norm_add_le
    (sharpSum (fun n:ℕ => (1:DirichletCharacter ℂ q) n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-
      sharpSum (fun n:ℕ => (ArithmeticFunction.vonMangoldt n:ℂ)) X)
    (sharpSum (fun n:ℕ => (ArithmeticFunction.vonMangoldt n:ℂ)) X-(X:ℂ))
  rw [sub_add_sub_cancel] at hn
  apply (hn.trans (add_le_add (hDiff q hq) hOrd)).trans_eq
  ring

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

theorem all_character_exponential :
    ∃ c K : ℝ, 0 < c ∧ c ≤ 1/2 ∧ 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
      (q:ℝ) ≤ Real.exp (cubeHeight X) →
      ‖sharpSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-
        (if chi=1 then (X:ℂ) else 0)‖ ≤ K*X*Real.exp (-c*cubeHeight X) := by
  classical
  obtain ⟨c,C,hc,hc2,hC,hNon⟩ := sharp_character_exponential
  obtain ⟨D,hD,hPrin⟩ := principal_character_exponential hc
  refine ⟨c,C+D,hc,hc2,by positivity,?_⟩
  filter_upwards [hNon,hPrin,eventually_ge_atTop (3:ℝ)] with X hNon hPrin hX
  intro q _ chi hq
  have hx0 : 0 ≤ X := by linarith
  have hcb : C*X*Real.exp (-c*cubeHeight X) ≤ (C+D)*X*Real.exp (-c*cubeHeight X) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hx0) (Real.exp_pos _).le
  have hdb : D*X*Real.exp (-c*cubeHeight X) ≤ (C+D)*X*Real.exp (-c*cubeHeight X) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hx0) (Real.exp_pos _).le
  by_cases hchi : chi=1
  · subst chi
    simpa using! (hPrin q hq).trans hdb
  · simpa [hchi] using! (hNon q chi hchi hq).trans hcb

theorem residuePsi_exponential :
    ∃ c K : ℝ, 0 < c ∧ c ≤ 1/2 ∧ 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (a : ZMod q), IsUnit a →
      (q:ℝ) ≤ Real.exp (cubeHeight X) →
      |residuePsi a X-X/(q.totient:ℝ)| ≤ K*X*Real.exp (-c*cubeHeight X) := by
  obtain ⟨c,K,hc,hc2,hK,hall⟩ := all_character_exponential
  refine ⟨c,K,hc,hc2,hK,?_⟩
  filter_upwards [hall] with X hX
  intro q _ a ha hq
  have h := residuePsi_error_le a ha X (K*X*Real.exp (-c*cubeHeight X)) (fun chi => hX q chi hq)
  have he : ‖(residuePsi a X:ℂ)-(X:ℂ)/(q.totient:ℂ)‖ =
      |residuePsi a X-X/(q.totient:ℝ)| := by
    rw [show (q.totient:ℂ) = ((q.totient:ℝ):ℂ) by simp,
      ← Complex.ofReal_div,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  rwa [he] at h

theorem residueTheta_exponential :
    ∃ c K : ℝ, 0 < c ∧ c ≤ 1/2 ∧ 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (a : ZMod q), IsUnit a →
      (q:ℝ) ≤ Real.exp (cubeHeight X) →
      |residueTheta a X-X/(q.totient:ℝ)| ≤ K*X*Real.exp (-c*cubeHeight X) := by
  obtain ⟨c,K,hc,hc2,hK,hpsi⟩ := residuePsi_exponential
  obtain ⟨D,hD⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let C : ℝ := max D 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨c,K+C,hc,hc2,by positivity,?_⟩
  filter_upwards [hpsi,eventually_sqrt_le_X_exp c] with X hX hsqrt
  intro q _ a ha hq
  have hgap := residuePsi_sub_theta_bounds a X
  have hb : residuePsi a X-residueTheta a X ≤ C*X*Real.exp (-c*cubeHeight X) := by
    calc
      _ ≤ D*Real.sqrt X := hgap.2.trans (hD X)
      _ ≤ C*Real.sqrt X := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
      _ ≤ C*(X*Real.exp (-c*cubeHeight X)) := mul_le_mul_of_nonneg_left hsqrt hC.le
      _ = _ := by ring
  calc
    _ ≤ |residuePsi a X-X/(q.totient:ℝ)|+|residuePsi a X-residueTheta a X| := by
      have h := abs_sub_le (residueTheta a X) (residuePsi a X) (X/(q.totient:ℝ))
      rw [abs_sub_comm (residueTheta a X) (residuePsi a X),add_comm] at h
      exact h
    _ ≤ K*X*Real.exp (-c*cubeHeight X)+C*X*Real.exp (-c*cubeHeight X) := by
      rw [abs_of_nonneg hgap.1]
      exact add_le_add (hX q a ha hq) hb
    _ = _ := by ring

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter _root_.MeasureTheory
open scoped Topology

lemma cubeHeight_above_sqrt {X t : ℝ} (hX : 3 ≤ Real.sqrt X) (ht : Real.sqrt X ≤ t) :
    cubeHeight X/2 ≤ cubeHeight t := by
  have hs : 0 < Real.sqrt X := by linarith
  have hx0 : 0 < X := Real.sqrt_pos.mp hs
  have hx1 : 1 < X := by nlinarith [Real.sq_sqrt hx0.le]
  have ht1 : 1 < t := by linarith
  have hhX : 0 < cubeHeight X := cubeHeight_pos hx1
  have hht : 0 < cubeHeight t := cubeHeight_pos ht1
  have hcompare : Real.log X ≤ 2*Real.log t := by
    have he := Real.log_le_log hs ht
    rw [Real.log_sqrt hx0.le] at he
    linarith
  apply (pow_le_pow_iff_left₀ (show 0 ≤ cubeHeight X/2 by positivity) hht.le (by decide : (3:ℕ)≠0)).mp
  rw [show (cubeHeight X/2)^3=(cubeHeight X)^3/8 by ring,
    cubeHeight_pow_three hx1.le,cubeHeight_pow_three ht1.le]
  have hlog := Real.log_pos hx1
  linarith

lemma modulus_exponential_above_sqrt {c X t : ℝ} (hc : c ≤ 1/2)
    (hX : 3 ≤ Real.sqrt X) (ht : Real.sqrt X ≤ t) {q : ℕ}
    (hq : (q:ℝ) ≤ Real.exp (c*cubeHeight X)) :
    (q:ℝ) ≤ Real.exp (cubeHeight t) := by
  have hx0 : 0 < X := Real.sqrt_pos.mp (by linarith)
  have hhX : 0 < cubeHeight X := cubeHeight_pos (by nlinarith [Real.sq_sqrt hx0.le])
  apply hq.trans (Real.exp_le_exp.mpr ?_)
  calc
    _ ≤ cubeHeight X/2 := by nlinarith
    _ ≤ _ := cubeHeight_above_sqrt hX ht

lemma residueErrorKernel_exp_upper {q : ℕ} (a : ZMod q) {K d X t : ℝ}
    (hK : 0 ≤ K) (hd : 0 < d) (hX : 3 ≤ Real.sqrt X) (ht : Real.sqrt X ≤ t)
    (herror : |residueTheta a t-t/(q.totient:ℝ)| ≤ K*t*Real.exp (-d*cubeHeight t)) :
    |residueErrorKernel a t| ≤ K*Real.exp (-(d/2)*cubeHeight X) := by
  have ht3 : 3 ≤ t := hX.trans ht
  have ht0 : 0 < t := by linarith
  have hl1 : 1 ≤ Real.log t :=
    ((Real.lt_log_iff_exp_lt ht0).mpr (Real.exp_one_lt_three.trans_le ht3)).le
  have hcompare := cubeHeight_above_sqrt hX ht
  rw [residueErrorKernel_eq a ht0,abs_div,abs_of_pos (by positivity : 0<t*Real.log t^2)]
  calc
    _ ≤ (K*t*Real.exp (-d*cubeHeight t))/(t*Real.log t^2) :=
      div_le_div_of_nonneg_right herror (by positivity)
    _ = (K*Real.exp (-d*cubeHeight t))/(Real.log t)^2 := by field_simp
    _ ≤ K*Real.exp (-d*cubeHeight t) := div_le_self (by positivity) (by nlinarith)
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hK

lemma residueErrorKernel_exp_high_integral {q : ℕ} (a : ZMod q) {K d X : ℝ}
    (hK : 0 ≤ K) (hd : 0 < d) (hX : 3 ≤ Real.sqrt X)
    (herror : ∀ t, Real.sqrt X ≤ t →
      |residueTheta a t-t/(q.totient:ℝ)| ≤ K*t*Real.exp (-d*cubeHeight t)) :
    |∫ t in Real.sqrt X..X, residueErrorKernel a t| ≤
      K*X*Real.exp (-(d/2)*cubeHeight X) := by
  have hs : 0 < Real.sqrt X := by linarith
  have hx0 : 0 < X := Real.sqrt_pos.mp hs
  have hsX : Real.sqrt X ≤ X := by nlinarith [Real.sq_sqrt hx0.le]
  have he := intervalIntegral.norm_integral_le_of_norm_le_const (a:=Real.sqrt X) (b:=X)
    (f:=residueErrorKernel a) (C:=K*Real.exp (-(d/2)*cubeHeight X)) (fun t ht => by
      rw [Set.uIoc_of_le hsX] at ht
      simpa only [Real.norm_eq_abs] using
        residueErrorKernel_exp_upper a hK hd hX ht.1.le (herror t ht.1.le))
  rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hsX)] at he
  calc
    _ ≤ K*Real.exp (-(d/2)*cubeHeight X)*(X-Real.sqrt X) := he
    _ ≤ K*Real.exp (-(d/2)*cubeHeight X)*X :=
      mul_le_mul_of_nonneg_left (sub_le_self _ (Real.sqrt_nonneg _)) (by positivity)
    _ = _ := by ring

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter _root_.MeasureTheory
open scoped Topology
open ErdosPrimeInputs.PrimeCountAbel (logarithmicIntegral)

lemma large_modulus_siegel_walfisz_eventually :
    ∃ c C : ℝ, 0 < c ∧ c ≤ 1/2 ∧ 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (r : ℤ), IsUnit (r:ZMod q) →
      (q:ℝ) ≤ Real.exp (c*cubeHeight X) →
      |((intervalPrimes 0 X q r).card:ℝ)-logarithmicIntegral X/(q.totient:ℝ)| ≤
        C*X*Real.exp (-c*cubeHeight X) := by
  obtain ⟨d,K,hd,hd2,hK,hθ⟩ := residueTheta_exponential
  obtain ⟨b,hb⟩ := eventually_atTop.mp hθ
  let c : ℝ := d/2
  have hc : 0 < c := by dsimp [c] <;> positivity
  have hc2 : c ≤ 1/2 := by dsimp [c] <;> linarith
  let D : ℝ := (Real.log 4+1)/(Real.log 2)^2
  let E : ℝ := 2/Real.log 2
  have hD : 0 < D := by dsimp [D] <;> positivity
  have hE : 0 < E := by dsimp [E] <;> positivity
  refine ⟨c,E+2*K+D,hc,hc2,by positivity,?_⟩
  filter_upwards [Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop (max 3 b)),
    eventually_ge_atTop (3:ℝ),eventually_sqrt_le_X_exp c,
    eventually_polynomial_le_X_exp 1 0 c] with X hs hX hroot hscale
  intro q _ r hr hq
  have hs3 : 3 ≤ Real.sqrt X := (le_max_left _ _).trans hs
  have hsb : b ≤ Real.sqrt X := (le_max_right _ _).trans hs
  have hx0 : 0 < X := by linarith
  have hsX : Real.sqrt X ≤ X := by nlinarith [Real.sq_sqrt hx0.le]
  have hhX : 0 < cubeHeight X := cubeHeight_pos (by linarith)
  have hL1 : 1 ≤ Real.log X :=
    ((Real.lt_log_iff_exp_lt hx0).mpr (Real.exp_one_lt_three.trans_le hX)).le
  have hL : 0 < Real.log X := by linarith
  have hscale1 : 1 ≤ X*Real.exp (-c*cubeHeight X) := by simpa only [pow_zero,mul_one] using hscale
  have herror : ∀ t, Real.sqrt X ≤ t →
      |residueTheta (r:ZMod q) t-t/(q.totient:ℝ)| ≤ K*t*Real.exp (-d*cubeHeight t) := by
    intro t ht
    exact hb t (hsb.trans ht) q (r:ZMod q) hr
      (modulus_exponential_above_sqrt hc2 hs3 ht hq)
  have hdecay : Real.exp (-d*cubeHeight X) ≤ Real.exp (-c*cubeHeight X) :=
    Real.exp_le_exp.mpr (by dsimp [c] <;> nlinarith)
  have hend : |(residueTheta (r:ZMod q) X-X/(q.totient:ℝ))/Real.log X| ≤
      K*X*Real.exp (-c*cubeHeight X) := by
    rw [abs_div,abs_of_pos hL]
    calc
      _ ≤ (K*X*Real.exp (-d*cubeHeight X))/Real.log X :=
        div_le_div_of_nonneg_right (herror X hsX) hL.le
      _ ≤ K*X*Real.exp (-d*cubeHeight X) := div_le_self (by positivity) hL1
      _ ≤ _ := mul_le_mul_of_nonneg_left hdecay (by positivity)
  have hlo : |∫ t in 2..Real.sqrt X, residueErrorKernel (r:ZMod q) t| ≤
      D*X*Real.exp (-c*cubeHeight X) := by
    calc
      _ ≤ D*Real.sqrt X := residueErrorKernel_low_integral _ (by linarith)
      _ ≤ D*(X*Real.exp (-c*cubeHeight X)) := mul_le_mul_of_nonneg_left hroot hD.le
      _ = _ := by ring
  have hhi := residueErrorKernel_exp_high_integral (r:ZMod q) hK.le hd hs3 herror
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (residueErrorKernel_integrable (r:ZMod q) (by norm_num) (by linarith : (2:ℝ)≤Real.sqrt X))
    (residueErrorKernel_integrable (r:ZMod q) (by linarith : (2:ℝ)≤Real.sqrt X) hsX)
  have hint : |∫ t in 2..X, residueErrorKernel (r:ZMod q) t| ≤
      D*X*Real.exp (-c*cubeHeight X)+K*X*Real.exp (-c*cubeHeight X) := by
    rw [← hsplit]
    exact (abs_add_le _ _).trans (add_le_add hlo hhi)
  have hphi : (1:ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hconst : |2/((q.totient:ℝ)*Real.log 2)| ≤ E*X*Real.exp (-c*cubeHeight X) := by
    rw [abs_of_nonneg (by positivity)]
    calc
      _ = E/(q.totient:ℝ) := by dsimp [E] <;> ring
      _ ≤ E := div_le_self hE.le hphi
      _ ≤ E*(X*Real.exp (-c*cubeHeight X)) := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hscale1 hE.le
      _ = _ := by ring
  rw [intervalPrimes_error_eq (by linarith) q r]
  calc
    _ ≤ |2/((q.totient:ℝ)*Real.log 2)|+
        |(residueTheta (r:ZMod q) X-X/(q.totient:ℝ))/Real.log X|+
        |∫ t in 2..X, residueErrorKernel (r:ZMod q) t| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ E*X*Real.exp (-c*cubeHeight X)+K*X*Real.exp (-c*cubeHeight X)+
        (D*X*Real.exp (-c*cubeHeight X)+K*X*Real.exp (-c*cubeHeight X)) :=
      add_le_add (add_le_add hconst hend) hint
    _ = _ := by ring

theorem large_modulus_siegel_walfisz :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ 3 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ (q : ℕ) (r : ℤ), 0 < q → IsCoprime r (q:ℤ) →
      (q:ℝ) ≤ Real.exp (c*(Real.log X)^((1:ℝ)/3)) →
      |((intervalPrimes 0 X q r).card:ℝ)-logarithmicIntegral X/(q.totient:ℝ)| ≤
        C*X*Real.exp (-c*(Real.log X)^((1:ℝ)/3)) := by
  obtain ⟨c,C,hc,_hc2,hC,h⟩ := large_modulus_siegel_walfisz_eventually
  obtain ⟨b,hb⟩ := eventually_atTop.mp h
  refine ⟨c,C,max 3 b,hc,hC,le_max_left _ _,?_⟩
  intro X hX q r hq hr hbound
  let _ : NeZero q := ⟨hq.ne'⟩
  exact hb X ((le_max_right _ _).trans hX) q r (isUnit_intCast_of_isCoprime hr) hbound

end Erdos970Dependency.SiegelWalfisz


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeIntervalFlags
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Finset _root_.MeasureTheory
open scoped Topology
open ErdosPrimeInputs.PrimeCountAbel (logarithmicIntegral)

lemma intervalPrimes_eq_sdiff {u v : ℝ} (hu : 0 ≤ u) (q : ℕ) (r : ℤ) :
    intervalPrimes u (v-u) q r = intervalPrimes 0 v q r \ intervalPrimes 0 u q r := by
  ext p
  simp only [mem_sdiff,mem_intervalPrimes,zero_add,add_sub_cancel]
  constructor
  · rintro ⟨hp,hlo,hhi,hm⟩
    refine ⟨⟨hp,by linarith,hhi,hm⟩,?_⟩
    rintro ⟨_,_,hpu,_⟩
    linarith
  · rintro ⟨⟨hp,h0,hhi,hm⟩,hnot⟩
    refine ⟨hp,?_,hhi,hm⟩
    by_contra h
    exact hnot ⟨hp,h0,le_of_not_gt h,hm⟩

lemma intervalPrimes_count_sub {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (q : ℕ) (r : ℤ) :
    ((intervalPrimes u (v-u) q r).card:ℝ) =
      ((intervalPrimes 0 v q r).card:ℝ)-((intervalPrimes 0 u q r).card:ℝ) := by
  have hs : intervalPrimes 0 u q r ⊆ intervalPrimes 0 v q r := by
    intro p hp
    obtain ⟨hpr,h0,hpu,hm⟩ := (mem_intervalPrimes _ _ _ _ _).mp hp
    exact (mem_intervalPrimes _ _ _ _ _).mpr ⟨hpr,h0,by linarith,hm⟩
  rw [intervalPrimes_eq_sdiff hu,card_sdiff_of_subset hs,Nat.cast_sub (card_le_card hs)]

lemma inv_log_intervalIntegrable {u v : ℝ} (hu : 2 ≤ u) (huv : u ≤ v) :
    IntervalIntegrable (fun t:ℝ => 1/Real.log t) volume u v := by
  apply ContinuousOn.intervalIntegrable_of_Icc huv
  intro t ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have hl0 : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
  exact ContinuousAt.continuousWithinAt (by fun_prop)

lemma logarithmicIntegral_sub {u v : ℝ} (hu : 2 ≤ u) (huv : u ≤ v) :
    logarithmicIntegral v-logarithmicIntegral u = ∫ t in u..v, 1/Real.log t := by
  have h := intervalIntegral.integral_add_adjacent_intervals
    (inv_log_intervalIntegrable (by norm_num) hu) (inv_log_intervalIntegrable hu huv)
  unfold logarithmicIntegral
  linarith

lemma logarithmicIntegral_sub_lower {u v : ℝ} (hu : 2 ≤ u) (huv : u ≤ v) :
    (v-u)/Real.log v ≤ logarithmicIntegral v-logarithmicIntegral u := by
  have hv1 : 1 < v := by linarith
  rw [logarithmicIntegral_sub hu huv]
  calc
    _ = ∫ _t in u..v, 1/Real.log v := by simp <;> ring
    _ ≤ _ := intervalIntegral.integral_mono_on huv (by simp)
      (inv_log_intervalIntegrable hu huv) (fun t ht => by
        have ht1 : 1 < t := by linarith [ht.1]
        have hl : Real.log t ≤ Real.log v := Real.log_le_log (by linarith) ht.2
        exact one_div_le_one_div_of_le (Real.log_pos ht1) hl)

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology
open ErdosPrimeInputs.PrimeCountAbel (logarithmicIntegral)

lemma ordinary_prime_count_exponential :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ 3 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      |((intervalPrimes 0 X 1 0).card:ℝ)-logarithmicIntegral X| ≤
        C*X*Real.exp (-c*cubeHeight X) := by
  obtain ⟨c,C,X0,hc,hC,hX0,h⟩ := large_modulus_siegel_walfisz
  refine ⟨c,C,X0,hc,hC,hX0,?_⟩
  intro X hX
  have hx1 : 1 < X := by linarith
  have hq : (1:ℝ) ≤ Real.exp (c*cubeHeight X) :=
    Real.one_le_exp_iff.mpr (mul_nonneg hc.le (cubeHeight_pos hx1).le)
  have he := h X hX 1 0 (by norm_num) (by norm_num) (by simpa only [Nat.cast_one,cubeHeight] using! hq)
  simpa only [Nat.totient_one,Nat.cast_one,div_one,cubeHeight] using! he

lemma prime_interval_lower_of_errors {c C u v : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hu : 2 ≤ u) (huv : u ≤ v)
    (heU : |((intervalPrimes 0 u 1 0).card:ℝ)-logarithmicIntegral u| ≤ C*u*Real.exp (-c*cubeHeight u))
    (heV : |((intervalPrimes 0 v 1 0).card:ℝ)-logarithmicIntegral v| ≤ C*v*Real.exp (-c*cubeHeight v)) :
    (v-u)/Real.log v-2*C*v*Real.exp (-c*cubeHeight u) ≤
      ((intervalPrimes u (v-u) 1 0).card:ℝ) := by
  have hu0 : 0 ≤ u := by linarith
  have hv0 : 0 ≤ v := hu0.trans huv
  have hh := cubeHeight_mono (by linarith : 1<u) huv
  have hdecay : Real.exp (-c*cubeHeight v) ≤ Real.exp (-c*cubeHeight u) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hV : C*v*Real.exp (-c*cubeHeight v) ≤ C*v*Real.exp (-c*cubeHeight u) :=
    mul_le_mul_of_nonneg_left hdecay (mul_nonneg hC hv0)
  have hU : C*u*Real.exp (-c*cubeHeight u) ≤ C*v*Real.exp (-c*cubeHeight u) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left huv hC) (Real.exp_pos _).le
  have hUupper := (abs_le.mp heU).2
  have hVlower := (abs_le.mp heV).1
  have hli := logarithmicIntegral_sub_lower hu huv
  rw [intervalPrimes_count_sub hu0 huv]
  linarith

lemma exponential_log_cube_tendsto {K : ℝ} (hK : 0 < K) :
    Tendsto (fun w:ℝ => Real.exp (K*(Real.log w)^3)) atTop atTop :=
  Real.tendsto_exp_atTop.comp
    (Filter.Tendsto.const_mul_atTop hK ((tendsto_pow_atTop (by decide : (3:ℕ)≠0)).comp Real.tendsto_log_atTop))

lemma cubeHeight_lower_of_exp_cube {R w u : ℝ} (hR : 0 < R) (hw : 1 < w) (hu : 1 ≤ u)
    (hbound : Real.exp (R^3*(Real.log w)^3) ≤ u) :
    R*Real.log w ≤ cubeHeight u := by
  have hlogw : 0 < Real.log w := Real.log_pos hw
  have hlog : R^3*(Real.log w)^3 ≤ Real.log u := by
    have h := Real.log_le_log (Real.exp_pos _) hbound
    simpa only [Real.log_exp] using h
  apply (pow_le_pow_iff_left₀ (mul_nonneg hR.le hlogw.le)
    (Real.rpow_nonneg (Real.log_nonneg hu) _) (by decide : (3:ℕ)≠0)).mp
  change (R*Real.log w)^3 ≤ (cubeHeight u)^3
  rw [cubeHeight_pow_three hu,mul_pow]
  exact hlog

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

lemma moving_prime_interval_error_budget {c C D R L eps w u v : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) (hR : 0 < R) (heps : 0 < eps)
    (hRate : c*R=D+3) (hw : 3 ≤ w) (hu : 2 ≤ u) (huv : u ≤ v)
    (hlo : Real.exp (R^3*(Real.log w)^3) ≤ u)
    (hhi : v ≤ Real.exp (L*(Real.log w)^3))
    (hlen : v/w^D ≤ v-u)
    (hpoly : 2*C*L*(Real.log w)^3 ≤ eps*w^3) :
    2*C*v*Real.exp (-c*cubeHeight u) ≤ eps*(v-u)/Real.log v := by
  have hw0 : 0 < w := by linarith
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := hu0.trans_le huv
  have hlogv : 0 < Real.log v := Real.log_pos (by linarith)
  have hh := cubeHeight_lower_of_exp_cube hR (by linarith) (by linarith) hlo
  have hrate : (D+3)*Real.log w ≤ c*cubeHeight u := by
    have he := mul_le_mul_of_nonneg_left hh hc.le
    rw [← mul_assoc,hRate] at he
    exact he
  have hlogupper : Real.log v ≤ L*(Real.log w)^3 := by
    have he := Real.log_le_log hv0 hhi
    simpa only [Real.log_exp] using he
  let W : ℝ := w^D
  let Z : ℝ := w^3
  let decay : ℝ := Real.exp (-c*cubeHeight u)
  have hW : 0 < W := Real.rpow_pos_of_pos hw0 _
  have hZ : 0 < Z := pow_pos hw0 _
  have hdecay : 0 < decay := Real.exp_pos _
  have hpower : W*Z = Real.exp ((D+3)*Real.log w) := by
    dsimp [W,Z]
    rw [← Real.rpow_natCast w 3,← Real.rpow_add hw0,Real.rpow_def_of_pos hw0]
    congr 1
    push_cast
    ring
  have hcancel : decay*W*Z ≤ 1 := by
    rw [mul_assoc,hpower]
    dsimp [decay]
    rw [← Real.exp_add]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hlen' : v ≤ (v-u)*W := (div_le_iff₀ hW).mp hlen
  have hbound : ((2*C*v*decay)*Real.log v)*W ≤ (eps*(v-u))*W := by
    calc
      _ = (2*C*Real.log v)*(v*decay*W) := by ring
      _ ≤ (2*C*(L*(Real.log w)^3))*(v*decay*W) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogupper (by positivity)) (by positivity)
      _ = (2*C*L*(Real.log w)^3)*(v*decay*W) := by ring
      _ ≤ (eps*Z)*(v*decay*W) := mul_le_mul_of_nonneg_right hpoly (by positivity)
      _ = (eps*v)*(decay*W*Z) := by ring
      _ ≤ eps*v := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hcancel (by positivity : 0≤eps*v)
      _ ≤ eps*((v-u)*W) := mul_le_mul_of_nonneg_left hlen' heps.le
      _ = _ := by ring
  apply (le_div_iff₀ hlogv).mpr
  exact le_of_mul_le_mul_right hbound hW

lemma eventually_interval_polynomial_budget {C L eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ w : ℝ in atTop, 3 ≤ w ∧ 2*C*L*(Real.log w)^3 ≤ eps*w^3 := by
  filter_upwards [eventually_ge_atTop (3:ℝ),
    Real.tendsto_log_atTop.eventually
      (eventually_polynomial_le_exp (2*C*L/eps) 3 (by norm_num : (0:ℝ)<1))]
    with w hw hp
  have hw0 : 0 < w := by linarith
  have hfirst : 2*C*L*(Real.log w)^3 ≤ eps*w := by
    have he := mul_le_mul_of_nonneg_right hp.2 heps.le
    rw [one_mul,Real.exp_log hw0] at he
    calc
      _ = ((2*C*L/eps)*(Real.log w)^3)*eps := by field_simp
      _ ≤ w*eps := he
      _ = _ := mul_comm _ _
  have hw3 : w ≤ w^3 := by nlinarith [sq_nonneg (w-1)]
  exact ⟨hw,hfirst.trans (mul_le_mul_of_nonneg_left hw3 heps.le)⟩

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

theorem moving_prime_interval_lower (D : ℝ) (hD : 0 < D) :
    ∃ K : ℝ, 0 < K ∧ ∀ L : ℝ, 0 < L → ∀ eps : ℝ, 0 < eps →
      ∃ w₀ : ℝ, 3 ≤ w₀ ∧ ∀ w : ℝ, w₀ ≤ w → ∀ u v : ℝ, u ≤ v →
        Real.exp (K*(Real.log w)^3) ≤ u → v ≤ Real.exp (L*(Real.log w)^3) →
        v/w^D ≤ v-u →
        (1-eps)*(v-u)/Real.log v ≤ ((intervalPrimes u (v-u) 1 0).card:ℝ) := by
  obtain ⟨c,C,X0,hc,hC,hX0,hcount⟩ := ordinary_prime_count_exponential
  let R : ℝ := (D+3)/c
  let K : ℝ := R^3
  have hR : 0 < R := by dsimp [R] <;> positivity
  have hK : 0 < K := pow_pos hR _
  have hRate : c*R=D+3 := by dsimp [R]; field_simp
  refine ⟨K,hK,?_⟩
  intro L _hL eps heps
  have hev : ∀ᶠ w : ℝ in atTop, 3 ≤ w ∧ ∀ u v : ℝ, u ≤ v →
      Real.exp (K*(Real.log w)^3) ≤ u → v ≤ Real.exp (L*(Real.log w)^3) →
      v/w^D ≤ v-u →
      (1-eps)*(v-u)/Real.log v ≤ ((intervalPrimes u (v-u) 1 0).card:ℝ) := by
    filter_upwards [eventually_interval_polynomial_budget (C:=C) (L:=L) heps,
      (exponential_log_cube_tendsto hK).eventually (eventually_ge_atTop X0)]
      with w hpoly hlarge
    refine ⟨hpoly.1,?_⟩
    intro u v huv hlo hhi hlen
    have hXu : X0 ≤ u := hlarge.trans hlo
    have hXv : X0 ≤ v := hXu.trans huv
    have hu2 : 2 ≤ u := by linarith
    have herr := moving_prime_interval_error_budget hc hC.le hR heps hRate hpoly.1 hu2 huv hlo hhi hlen hpoly.2
    have hlower := prime_interval_lower_of_errors hc.le hC.le hu2 huv (hcount u hXu) (hcount v hXv)
    calc
      _ = (v-u)/Real.log v-eps*(v-u)/Real.log v := by ring
      _ ≤ (v-u)/Real.log v-2*C*v*Real.exp (-c*cubeHeight u) := sub_le_sub_left herr _
      _ ≤ _ := hlower
  obtain ⟨b,hb⟩ := eventually_atTop.mp hev
  refine ⟨max 3 b,le_max_left _ _,?_⟩
  intro w hw u v huv hlo hhi hlen
  exact (hb w ((le_max_right _ _).trans hw)).2 u v huv hlo hhi hlen

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Finset
open scoped Topology

lemma mem_primeIntervalFlags (includeLower includeUpper : Bool) (u v : ℝ) (p : ℕ) :
    p ∈ primeIntervalFlags includeLower includeUpper u v ↔ p.Prime ∧
      (if includeLower then u ≤ (p:ℝ) else u < (p:ℝ)) ∧
      (if includeUpper then (p:ℝ) ≤ v else (p:ℝ) < v) := by
  constructor
  · intro hp
    exact (mem_filter.mp hp).2
  · intro hp
    have hv : (p:ℝ) ≤ v := by
      cases includeUpper
      · exact (show (p:ℝ)<v by simpa using hp.2.2).le
      · simpa using hp.2.2
    refine mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le ?_),hp⟩
    exact (Nat.le_floor_iff (le_max_right v 0)).mpr (hv.trans (le_max_left _ _))

lemma primeIntervalFlags_lower_card (includeLower includeUpper : Bool) (u v : ℝ) :
    (intervalPrimes u (v-u) 1 0).card ≤ (primeIntervalFlags includeLower includeUpper u v).card+1 := by
  classical
  have hs : intervalPrimes u (v-u) 1 0 ⊆ primeIntervalFlags includeLower includeUpper u v ∪ {⌊v⌋₊} := by
    intro p hp
    obtain ⟨hpr,hlo,hhi,_⟩ := (mem_intervalPrimes _ _ _ _ _).mp hp
    have hpv : (p:ℝ) ≤ v := by linarith
    by_cases heq : (p:ℝ)=v
    · apply mem_union_right
      apply mem_singleton.mpr
      rw [← heq,Nat.floor_natCast]
    · apply mem_union_left
      apply (mem_primeIntervalFlags _ _ _ _ _).mpr
      refine ⟨hpr,?_,?_⟩
      · cases includeLower
        · simpa using hlo
        · simpa using hlo.le
      · have hvlt : (p:ℝ)<v := lt_of_le_of_ne hpv heq
        cases includeUpper
        · simpa using hvlt
        · simpa using hpv
  have hc := (card_le_card hs).trans (card_union_le _ _)
  simpa only [card_singleton] using hc

theorem moving_prime_interval_lower_flags (D : ℝ) (hD : 0 < D) :
    ∃ K : ℝ, 0 < K ∧ ∀ L : ℝ, 0 < L → ∀ eps : ℝ, 0 < eps →
      ∃ w₀ : ℝ, 3 ≤ w₀ ∧ ∀ w : ℝ, w₀ ≤ w → ∀ u v : ℝ, u ≤ v →
        Real.exp (K*(Real.log w)^3) ≤ u → v ≤ Real.exp (L*(Real.log w)^3) →
        v/w^D ≤ v-u → ∀ includeLower includeUpper : Bool,
        (1-eps)*(v-u)/Real.log v-1 ≤ ((primeIntervalFlags includeLower includeUpper u v).card:ℝ) := by
  obtain ⟨K,hK,h⟩ := moving_prime_interval_lower D hD
  refine ⟨K,hK,?_⟩
  intro L hL eps heps
  obtain ⟨w0,hw0,hw⟩ := h L hL eps heps
  refine ⟨w0,hw0,?_⟩
  intro w hww u v huv hlo hhi hlen includeLower includeUpper
  have he := hw w hww u v huv hlo hhi hlen
  have hc : ((intervalPrimes u (v-u) 1 0).card:ℝ) ≤
      ((primeIntervalFlags includeLower includeUpper u v).card:ℝ)+1 := by
    exact_mod_cast primeIntervalFlags_lower_card includeLower includeUpper u v
  linarith

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_SignedIntervalGeometry
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz

lemma retainedLength_lower (a b t : ℝ) (ht : 0 ≤ t) :
    max (b-a) 0-t ≤ retainedLength a b t := by
  unfold retainedLength
  split_ifs with h
  · rw [max_eq_left (by linarith : 0 ≤ b-a)]
    linarith
  · have hm : max (b-a) 0 ≤ t := by apply max_le <;> linarith
    linarith

lemma signed_trim_length {x y t : ℝ} (hxy : x ≤ y) (ht : 0 ≤ t) :
    y-x ≤ max (y-max x t) 0+max (-x-max (-y) t) 0+2*t := by
  simp only [max_def]
  split_ifs <;> linarith

lemma signed_retained_length {x y t : ℝ} (hxy : x ≤ y) (ht : 0 ≤ t) :
    y-x-4*t ≤ retainedLength (max x t) y t + retainedLength (max (-y) t) (-x) t := by
  have hp := retainedLength_lower (max x t) y t ht
  have hn := retainedLength_lower (max (-y) t) (-x) t ht
  have htrim := signed_trim_length hxy ht
  linarith

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_WeightedPrimeMultiplePairs
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace Erdos970Dependency.SiegelWalfisz
open _root_.Finset
open scoped Topology

lemma mem_primeMultiplesIn (d : ℕ) (P x y : ℝ) (m : ℤ) :
    m ∈ primeMultiplesIn d P x y ↔ x < (m:ℝ) ∧ (m:ℝ) < y ∧
      ∃ ell : ℕ, ell.Prime ∧ P < (ell:ℝ) ∧ (m=(d:ℤ)*ell ∨ m= -((d:ℤ)*ell)) := by
  classical
  constructor
  · intro hm
    exact (mem_filter.mp hm).2
  · intro hm
    apply mem_filter.mpr
    exact ⟨mem_Icc.mpr ⟨Int.ceil_le.mpr hm.1.le,Int.le_floor.mpr hm.2.1.le⟩,hm⟩

lemma prime_multiple_pos_injective {d : ℕ} (hd : 0 < d) :
    Function.Injective (fun ell:ℕ => (d:ℤ)*(ell:ℤ)) := by
  intro a b hab
  have hd0 : (d:ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  have he := mul_left_cancel₀ hd0 hab
  exact_mod_cast he

lemma prime_multiple_neg_injective {d : ℕ} (hd : 0 < d) :
    Function.Injective (fun ell:ℕ => -((d:ℤ)*(ell:ℤ))) := by
  intro a b hab
  exact prime_multiple_pos_injective hd (neg_injective hab)

lemma signed_prime_sets_card_le {d : ℕ} (hd : 0 < d) {P x y : ℝ} (A B : Finset ℕ)
    (hA : ∀ ell ∈ A, ell.Prime ∧ P < (ell:ℝ) ∧ x < (d:ℝ)*ell ∧ (d:ℝ)*ell < y)
    (hB : ∀ ell ∈ B, ell.Prime ∧ P < (ell:ℝ) ∧ x < -((d:ℝ)*ell) ∧ -((d:ℝ)*ell) < y) :
    A.card+B.card ≤ (primeMultiplesIn d P x y).card := by
  classical
  let pos : ℕ → ℤ := fun ell => (d:ℤ)*ell
  let neg : ℕ → ℤ := fun ell => -((d:ℤ)*ell)
  have hsub : A.image pos ∪ B.image neg ⊆ primeMultiplesIn d P x y := by
    intro m hm
    rcases mem_union.mp hm with hm|hm
    · obtain ⟨ell,he,rfl⟩ := mem_image.mp hm
      obtain ⟨hp,hP,hlo,hhi⟩ := hA ell he
      apply (mem_primeMultiplesIn _ _ _ _ _).mpr
      refine ⟨?_,?_,ell,hp,hP,Or.inl rfl⟩
      · simpa [pos] using hlo
      · simpa [pos] using hhi
    · obtain ⟨ell,he,rfl⟩ := mem_image.mp hm
      obtain ⟨hp,hP,hlo,hhi⟩ := hB ell he
      apply (mem_primeMultiplesIn _ _ _ _ _).mpr
      refine ⟨?_,?_,ell,hp,hP,Or.inr rfl⟩
      · simpa [neg] using hlo
      · simpa [neg] using hhi
  have hdisj : Disjoint (A.image pos) (B.image neg) := by
    apply disjoint_left.mpr
    intro m hmA hmB
    obtain ⟨a,ha,ham⟩ := mem_image.mp hmA
    obtain ⟨b,hb,hbm⟩ := mem_image.mp hmB
    have hdZ : (0:ℤ) < d := by exact_mod_cast hd
    have hapos : 0 < pos a := mul_pos hdZ (by exact_mod_cast (hA a ha).1.pos)
    have hbpos : 0 < (d:ℤ)*(b:ℤ) := mul_pos hdZ (by exact_mod_cast (hB b hb).1.pos)
    have he : pos a = -((d:ℤ)*(b:ℤ)) := ham.trans hbm.symm
    linarith
  have he := card_le_card hsub
  rw [card_union_of_disjoint hdisj,card_image_of_injective _ (prime_multiple_pos_injective hd),
    card_image_of_injective _ (prime_multiple_neg_injective hd)] at he
  exact he

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz

lemma prime_multiple_d_le_P {P d : ℝ} (hP : 1 ≤ P) (hd : d ≤ P^(19/20:ℝ)) : d ≤ P := by
  calc
    _ ≤ P^(19/20:ℝ) := hd
    _ ≤ P^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hP (by norm_num)
    _ = P := Real.rpow_one P

lemma prime_multiple_P_sq_le {P s : ℝ} (hP : 1 ≤ P) (hs : 2 ≤ s) : P^2 ≤ P^s := by
  calc
    _ = P^(2:ℝ) := (Real.rpow_natCast P 2).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hP hs

lemma prime_multiple_piece_bounds {Cs w P s H d a b : ℝ}
    (hCs : 0 ≤ Cs) (hw : 4 ≤ w) (hP : 3 ≤ P) (hs : 203/100 ≤ s)
    (hd1 : 1 ≤ d) (hd : d ≤ P^(19/20:ℝ))
    (hH : P^s/2 ≤ H) (hheight : 2*w^(Cs+2) ≤ P^(1/50:ℝ))
    (ha : H/w ≤ a) (hlen : H/w ≤ b-a) (hb : b ≤ 2*w^(Cs+2)*P^s) :
    P ≤ a/d ∧ a/d ≤ b/d ∧ b/d ≤ P^(s+1/50) ∧
      (b/d)/w^(Cs+4) ≤ b/d-a/d ∧ Real.log (b/d) ≤ (s+1/50)*Real.log P := by
  have hw0 : 0 < w := by linarith
  have hP0 : 0 < P := by linarith
  have hP1 : 1 ≤ P := by linarith
  have hd0 : 0 < d := by linarith
  have hPs : 0 < P^s := Real.rpow_pos_of_pos hP0 _
  have hH0 : 0 < H := by linarith
  have ht0 : 0 < H/w := div_pos hH0 hw0
  have ha0 : 0 < a := ht0.trans_le ha
  have hlen0 : 0 < b-a := ht0.trans_le hlen
  have hb0 : 0 < b := by linarith
  have hwp : 0 < w^(Cs+2) := Real.rpow_pos_of_pos hw0 _
  have hW : 0 < w^(Cs+4) := Real.rpow_pos_of_pos hw0 _
  have hwle : w ≤ w^(Cs+2) := by
    calc
      _ = w^(1:ℝ) := (Real.rpow_one w).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h2w : 2*w ≤ P^(1/20:ℝ) := by
    calc
      _ ≤ 2*w^(Cs+2) := mul_le_mul_of_nonneg_left hwle (by norm_num)
      _ ≤ P^(1/50:ℝ) := hheight
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hP1 (by norm_num)
  have h2wd : 2*w*d ≤ P := by
    calc
      _ ≤ P^(1/20:ℝ)*P^(19/20:ℝ) := mul_le_mul h2w hd hd0.le (by positivity)
      _ = P := by rw [← Real.rpow_add hP0]; norm_num
  have hP2 : P^2 ≤ P^s := prime_multiple_P_sq_le hP1 (by linarith)
  have hPd : P*d ≤ H/w := by
    apply (le_div_iff₀ hw0).mpr
    calc
      _ = (P/2)*(2*w*d) := by ring
      _ ≤ (P/2)*P := mul_le_mul_of_nonneg_left h2wd (by positivity)
      _ = P^2/2 := by ring
      _ ≤ P^s/2 := div_le_div_of_nonneg_right hP2 (by norm_num)
      _ ≤ H := hH
  have hlo : P ≤ a/d := (le_div_iff₀ hd0).mpr (hPd.trans ha)
  have hab : a/d ≤ b/d := div_le_div_of_nonneg_right (by linarith) hd0.le
  have hhi : b/d ≤ P^(s+1/50) := by
    calc
      _ ≤ b := div_le_self hb0.le hd1
      _ ≤ 2*w^(Cs+2)*P^s := hb
      _ ≤ P^(1/50:ℝ)*P^s := mul_le_mul_of_nonneg_right hheight hPs.le
      _ = _ := by rw [← Real.rpow_add hP0]; congr 1; ring
  have hHlen : H ≤ w*(b-a) := by
    have he := (div_le_iff₀ hw0).mp hlen
    simpa only [mul_comm] using he
  have hpower : w^(Cs+4) = w^(Cs+2)*w^2 := by
    rw [← Real.rpow_natCast w 2,← Real.rpow_add hw0]
    congr 1
    ring
  have hwidth : b ≤ w^(Cs+4)*(b-a) := by
    calc
      _ ≤ 2*w^(Cs+2)*P^s := hb
      _ ≤ 2*w^(Cs+2)*(2*H) := mul_le_mul_of_nonneg_left (by linarith : P^s≤2*H) (by positivity)
      _ = 4*w^(Cs+2)*H := by ring
      _ ≤ 4*w^(Cs+2)*(w*(b-a)) := mul_le_mul_of_nonneg_left hHlen (by positivity)
      _ = (4*w)*(w^(Cs+2)*(b-a)) := by ring
      _ ≤ w^2*(w^(Cs+2)*(b-a)) := mul_le_mul_of_nonneg_right (by nlinarith : 4*w≤w^2) (by positivity)
      _ = _ := by rw [hpower]; ring
  have hrel : (b/d)/w^(Cs+4) ≤ b/d-a/d := by
    apply (div_le_iff₀ hW).mpr
    calc
      _ ≤ (w^(Cs+4)*(b-a))/d := div_le_div_of_nonneg_right hwidth hd0.le
      _ = _ := by ring
  have hlog := Real.log_le_log (hP0.trans_le (hlo.trans hab)) hhi
  rw [Real.log_rpow hP0] at hlog
  exact ⟨hlo,hab,hhi,hrel,hlog⟩

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

lemma prime_multiple_height_eventually {Cs K : ℝ} (_hCs : 0 ≤ Cs) (hK : 0 < K) :
    ∀ᶠ w : ℝ in atTop, 4 ≤ w ∧ ∀ P : ℝ,
      Real.exp (K*(Real.log w)^3) ≤ P → 3 ≤ P ∧ 2*w^(Cs+2) ≤ P^(1/50:ℝ) := by
  let a : ℝ := K/50
  let B : ℝ := Real.log 2+Cs+2
  have ha : 0 < a := by dsimp [a] <;> positivity
  filter_upwards [eventually_ge_atTop (4:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 (B/a))),
    (exponential_log_cube_tendsto hK).eventually (eventually_ge_atTop (3:ℝ))]
    with w hw hh hlarge
  refine ⟨hw,?_⟩
  intro P hP
  have hP3 : 3 ≤ P := hlarge.trans hP
  have hP0 : 0 < P := by linarith
  have hw0 : 0 < w := by linarith
  let h := Real.log w
  have hh1 : 1 ≤ h := (le_max_left _ _).trans hh
  have hhb : B/a ≤ h := (le_max_right _ _).trans hh
  have hB : B ≤ a*h := by
    have he := (div_le_iff₀ ha).mp hhb
    simpa only [mul_comm] using he
  have hhsq : h ≤ h^2 := by nlinarith
  have hBsq : B ≤ a*h^2 := hB.trans (mul_le_mul_of_nonneg_left hhsq ha.le)
  have hBcube := mul_le_mul_of_nonneg_right hBsq (show 0 ≤ h by linarith)
  have hlog2 : Real.log 2 ≤ Real.log 2*h := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hh1 (Real.log_pos (by norm_num : (1:ℝ)<2)).le
  have hlin : Real.log 2+(Cs+2)*h ≤ a*h^3 := by dsimp [B] at hBcube <;> nlinarith
  have hlogP : K*h^3 ≤ Real.log P := by
    have he := Real.log_le_log (Real.exp_pos _) hP
    simpa only [Real.log_exp] using he
  have he : Real.log 2+(Cs+2)*h ≤ Real.log P*(1/50) := by
    dsimp [a] at hlin
    nlinarith
  refine ⟨hP3,?_⟩
  calc
    _ = Real.exp (Real.log 2+(Cs+2)*h) := by
      rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2),Real.rpow_def_of_pos hw0]
      congr 1
      congr 1
      ring
    _ ≤ Real.exp (Real.log P*(1/50)) := Real.exp_le_exp.mpr he
    _ = _ := (Real.rpow_def_of_pos hP0 _).symm

lemma prime_multiple_endpoint_loss {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ P : ℝ in atTop, 3 ≤ P ∧ ∀ s d H : ℝ,
      203/100 ≤ s → s ≤ 219/100 → 1 ≤ d → d ≤ P^(19/20:ℝ) → P^s/2 ≤ H →
      2 ≤ (eps/2)*H/(d*(s+1/50)*Real.log P) := by
  filter_upwards [eventually_ge_atTop (3:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_polynomial_le_exp (24/eps) 1 (by norm_num : (0:ℝ)<1))]
    with P hP hp
  refine ⟨hP,?_⟩
  intro s d H hs hsUpper hd1 hd hH
  have hP0 : 0 < P := by linarith
  have hP1 : 1 ≤ P := by linarith
  have hd0 : 0 < d := by linarith
  have hs0 : 0 < s+1/50 := by linarith
  have hlog : 0 < Real.log P := Real.log_pos (by linarith)
  have h24 : 24*Real.log P ≤ eps*P := by
    have he := mul_le_mul_of_nonneg_right hp.2 heps.le
    rw [one_mul,pow_one,Real.exp_log hP0] at he
    calc
      _ = ((24/eps)*Real.log P)*eps := by field_simp
      _ ≤ P*eps := he
      _ = _ := mul_comm _ _
  have hdP := prime_multiple_d_le_P hP1 hd
  have hP2 := prime_multiple_P_sq_le hP1 (show 2 ≤ s by linarith)
  have hden : d*(s+1/50)*Real.log P ≤ 3*P*Real.log P := by
    have hm := mul_le_mul hdP (show s+1/50≤3 by linarith) hs0.le hP0.le
    have hn := mul_le_mul_of_nonneg_right hm hlog.le
    nlinarith only [hn]
  have hm := mul_le_mul_of_nonneg_right h24 (show 0≤P/4 by positivity)
  have hl := mul_le_mul_of_nonneg_left (show P^2≤2*H by linarith) (show 0≤eps/4 by positivity)
  apply (le_div_iff₀ (by positivity : 0<d*(s+1/50)*Real.log P)).mpr
  nlinarith only [hden,hm,hl]

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Finset

lemma mem_retainedPrimes (d : ℕ) (a b t : ℝ) (ell : ℕ) :
    ell ∈ retainedPrimes d a b t ↔ t ≤ b-a ∧ ell.Prime ∧ a/(d:ℝ) < ell ∧ (ell:ℝ) < b/(d:ℝ) := by
  unfold retainedPrimes
  by_cases h : t ≤ b-a
  · simp [h,mem_primeIntervalFlags]
  · simp [h]

lemma retained_positive_data {d : ℕ} (hd : 0 < d) {P x y t : ℝ}
    (hstart : t ≤ y-max x t → P ≤ (max x t)/(d:ℝ)) :
    ∀ ell ∈ retainedPrimes d (max x t) y t,
      ell.Prime ∧ P < (ell:ℝ) ∧ x < (d:ℝ)*ell ∧ (d:ℝ)*ell < y := by
  intro ell he
  obtain ⟨hret,hpr,hlo,hhi⟩ := (mem_retainedPrimes _ _ _ _ _).mp he
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have h1 := (div_lt_iff₀ hd0).mp hlo
  have h2 := (lt_div_iff₀ hd0).mp hhi
  refine ⟨hpr,(hstart hret).trans_lt hlo,?_,?_⟩
  · have hx := le_max_left x t
    nlinarith
  · nlinarith

lemma retained_negative_data {d : ℕ} (hd : 0 < d) {P x y t : ℝ}
    (hstart : t ≤ -x-max (-y) t → P ≤ (max (-y) t)/(d:ℝ)) :
    ∀ ell ∈ retainedPrimes d (max (-y) t) (-x) t,
      ell.Prime ∧ P < (ell:ℝ) ∧ x < -((d:ℝ)*ell) ∧ -((d:ℝ)*ell) < y := by
  intro ell he
  obtain ⟨hret,hpr,hlo,hhi⟩ := (mem_retainedPrimes _ _ _ _ _).mp he
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have h1 := (div_lt_iff₀ hd0).mp hlo
  have h2 := (lt_div_iff₀ hd0).mp hhi
  refine ⟨hpr,(hstart hret).trans_lt hlo,?_,?_⟩
  · nlinarith
  · have hy := le_max_left (-y) t
    nlinarith

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter _root_.Finset
open scoped Topology


private lemma retained_count_lower {eps delta H t len den count : ℝ}
    (hdelta : delta = eps / 4) (hdelta1 : delta < 1)
    (hH : 0 ≤ H) (hden : 0 < den)
    (htrim : 4 * t ≤ delta * H) (hretained : H - 4 * t ≤ len)
    (hsum : (1 - delta) * len / den - 2 ≤ count)
    (hLoss : 2 ≤ (eps / 2) * H / den) :
    (1 - eps) * H / den ≤ count := by
  have hkeep : H * (1 - delta) ≤ len := by nlinarith
  have hfactor : 1 - eps / 2 ≤ (1 - delta) ^ 2 := by
    rw [hdelta]
    nlinarith [sq_nonneg eps]
  have hmass : (1 - eps / 2) * H ≤ (1 - delta) * len := by
    calc
      _ ≤ (1 - delta) ^ 2 * H := mul_le_mul_of_nonneg_right hfactor hH
      _ = (1 - delta) * (H * (1 - delta)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hkeep (by linarith)
  calc
    _ = (1 - eps / 2) * H / den - (eps / 2) * H / den := by ring
    _ ≤ (1 - eps / 2) * H / den - 2 := sub_le_sub_left hLoss _
    _ ≤ (1 - delta) * len / den - 2 :=
      sub_le_sub_right (div_le_div_of_nonneg_right hmass hden.le) 2
    _ ≤ _ := hsum

theorem moving_signed_prime_multiple_lower_jb247_oai (Cs : ℝ) (hCs : 0 ≤ Cs) :
    ∃ K : ℝ, 0 < K ∧ ∀ rho : ℝ, 1 < rho → ∀ eps : ℝ, 0 < eps → eps < 1 →
      ∃ w₀ : ℝ, 4 ≤ w₀ ∧ ∀ w : ℝ, w₀ ≤ w → ∀ P s x y : ℝ, ∀ d : ℕ,
        Real.exp (K*(Real.log w)^3) ≤ P → P ≤ Real.exp (rho*K*(Real.log w)^3) →
        203/100 ≤ s → s ≤ 219/100 → P^s/2 ≤ y-x →
        max |x| |y| ≤ 2*w^(Cs+2)*P^s → 0 < d → (d:ℝ) ≤ P^(19/20:ℝ) →
        (1-eps)*(y-x)/((d:ℝ)*(s+1/50)*Real.log P) ≤ ((primeMultiplesIn d P x y).card:ℝ) := by
  obtain ⟨K,hK,hFamily⟩ := moving_prime_interval_lower_flags (Cs+4) (by linarith)
  refine ⟨K,hK,?_⟩
  intro rho hrho eps heps heps1
  let delta : ℝ := eps/4
  let L : ℝ := 3*rho*K
  have hdelta : 0 < delta := by dsimp [delta] <;> positivity
  have hdelta1 : delta < 1 := by dsimp [delta] <;> linarith
  have hL : 0 < L := by dsimp [L] <;> positivity
  obtain ⟨wF,hwF,hF⟩ := hFamily L hL delta hdelta
  obtain ⟨P0,hP0⟩ := eventually_atTop.mp (prime_multiple_endpoint_loss heps)
  have hev : ∀ᶠ w : ℝ in atTop, 4 ≤ w ∧ ∀ P s x y : ℝ, ∀ d : ℕ,
      Real.exp (K*(Real.log w)^3) ≤ P → P ≤ Real.exp (rho*K*(Real.log w)^3) →
      203/100 ≤ s → s ≤ 219/100 → P^s/2 ≤ y-x →
      max |x| |y| ≤ 2*w^(Cs+2)*P^s → 0 < d → (d:ℝ) ≤ P^(19/20:ℝ) →
      (1-eps)*(y-x)/((d:ℝ)*(s+1/50)*Real.log P) ≤ ((primeMultiplesIn d P x y).card:ℝ) := by
    filter_upwards [prime_multiple_height_eventually hCs hK,eventually_ge_atTop wF,
      eventually_ge_atTop (16/eps),
      (exponential_log_cube_tendsto hK).eventually (eventually_ge_atTop P0)]
      with w hwHeight hwFamily hwBudget hwP
    refine ⟨hwHeight.1,?_⟩
    intro P s x y d hPlower hPupper hs hsUpper hH hMax hd hdSmall
    obtain ⟨hP3,hheight⟩ := hwHeight.2 P hPlower
    have hPpos : 0 < P := by linarith
    have hP1 : 1 ≤ P := by linarith
    have hw0 : 0 < w := by linarith [hwHeight.1]
    have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
    have hd0 : (0:ℝ) < d := by exact_mod_cast hd
    have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
    let H : ℝ := y-x
    let t : ℝ := H/w
    let Den : ℝ := (s+1/50)*Real.log P
    let A := retainedPrimes d (max x t) y t
    let B := retainedPrimes d (max (-y) t) (-x) t
    have hPs : 0 < P^s := Real.rpow_pos_of_pos hPpos _
    have hH0 : 0 < H := by dsimp [H] <;> linarith
    have ht0 : 0 < t := div_pos hH0 hw0
    have hDen : 0 < Den := by dsimp [Den] <;> positivity
    have hden : 0 < (d:ℝ)*Den := mul_pos hd0 hDen
    have hy : y ≤ 2*w^(Cs+2)*P^s := (le_abs_self y).trans ((le_max_right _ _).trans hMax)
    have hnx : -x ≤ 2*w^(Cs+2)*P^s := (neg_le_abs x).trans ((le_max_left _ _).trans hMax)
    have hlogUpper : Real.log P ≤ rho*K*(Real.log w)^3 := by
      have he := Real.log_le_log hPpos hPupper
      simpa only [Real.log_exp] using he
    have htop : P^(3:ℝ) ≤ Real.exp (L*(Real.log w)^3) := by
      rw [Real.rpow_def_of_pos hPpos]
      apply Real.exp_le_exp.mpr
      dsimp [L]
      nlinarith
    have hEach (a b : ℝ) (ha : t ≤ a) (hb : b ≤ 2*w^(Cs+2)*P^s) :
        (1-delta)*retainedLength a b t/((d:ℝ)*Den)-1 ≤ ((retainedPrimes d a b t).card:ℝ) := by
      by_cases hret : t ≤ b-a
      · obtain ⟨hlo,hab,hhi,hrel,hlog⟩ := prime_multiple_piece_bounds hCs hwHeight.1 hP3 hs
          hd1 hdSmall hH hheight ha hret hb
        have hV : b/(d:ℝ) ≤ Real.exp (L*(Real.log w)^3) := hhi.trans
          ((Real.rpow_le_rpow_of_exponent_le hP1 (show s+1/50 ≤ (3:ℝ) by linarith)).trans htop)
        have hprime := hF w hwFamily (a/(d:ℝ)) (b/(d:ℝ)) hab (hPlower.trans hlo) hV hrel false false
        have hlogv : 0 < Real.log (b/(d:ℝ)) := Real.log_pos (by linarith)
        have hlen : 0 ≤ b-a := by linarith
        have hrat : (1-delta)*(b-a)/((d:ℝ)*Den) ≤
            (1-delta)*(b/(d:ℝ)-a/(d:ℝ))/Real.log (b/(d:ℝ)) := by
          calc
            _ = ((1-delta)*((b-a)/(d:ℝ)))/Den := by ring_nf
            _ ≤ ((1-delta)*((b-a)/(d:ℝ)))/Real.log (b/(d:ℝ)) :=
              div_le_div_of_nonneg_left (by positivity) hlogv hlog
            _ = _ := by ring
        simpa only [retainedPrimes,retainedLength,hret,ite_true, if_true] using
          (sub_le_sub_right hrat 1).trans hprime
      · norm_num [retainedPrimes,retainedLength,hret]
    have hpCount := hEach (max x t) y (le_max_right _ _) hy
    have hnCount := hEach (max (-y) t) (-x) (le_max_right _ _) hnx
    have hA := retained_positive_data (P:=P) (x:=x) (y:=y) (t:=t) hd (fun hret =>
      (prime_multiple_piece_bounds hCs hwHeight.1 hP3 hs hd1 hdSmall hH hheight (le_max_right _ _) hret hy).1)
    have hB := retained_negative_data (P:=P) (x:=x) (y:=y) (t:=t) hd (fun hret =>
      (prime_multiple_piece_bounds hCs hwHeight.1 hP3 hs hd1 hdSmall hH hheight (le_max_right _ _) hret hnx).1)
    have hcard : (A.card:ℝ)+(B.card:ℝ) ≤ ((primeMultiplesIn d P x y).card:ℝ) := by
      exact_mod_cast signed_prime_sets_card_le hd A B hA hB
    let len : ℝ := retainedLength (max x t) y t+retainedLength (max (-y) t) (-x) t
    have hsum : (1-delta)*len/((d:ℝ)*Den)-2 ≤ ((primeMultiplesIn d P x y).card:ℝ) := by
      calc
        _ = ((1-delta)*retainedLength (max x t) y t/((d:ℝ)*Den)-1)+
            ((1-delta)*retainedLength (max (-y) t) (-x) t/((d:ℝ)*Den)-1) := by dsimp [len] <;> ring
        _ ≤ (A.card:ℝ)+(B.card:ℝ) := add_le_add hpCount hnCount
        _ ≤ _ := hcard
    have htrim : 4*t ≤ delta*H := by
      have hweps := (div_le_iff₀ heps).mp hwBudget
      have hfrac : 4/w ≤ delta := (div_le_iff₀ hw0).mpr (by dsimp [delta] <;> nlinarith)
      calc
        _ = (4/w)*H := by dsimp [t] <;> ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hfrac hH0.le
    have hretained := signed_retained_length (show x ≤ y by dsimp [H] at hH0 <;> linarith) ht0.le
    change H-4*t ≤ len at hretained
    have hLoss := (hP0 P (hwP.trans hPlower)).2 s (d:ℝ) H hs hsUpper hd1 hdSmall hH
    have hLoss' : 2 ≤ (eps/2)*H/((d:ℝ)*Den) := by simpa only [Den,mul_assoc] using hLoss
    simpa only [H, Den, mul_assoc] using
      retained_count_lower (show delta = eps / 4 from rfl) hdelta1 hH0.le hden
        htrim hretained hsum hLoss'
  obtain ⟨b,hb⟩ := eventually_atTop.mp hev
  refine ⟨max 4 b,le_max_left _ _,?_⟩
  intro w hw P s x y d hPlower hPupper hs hsUpper hH hMax hd hdSmall
  exact (hb w ((le_max_right _ _).trans hw)).2 P s x y d hPlower hPupper hs hsUpper hH hMax hd hdSmall

end Erdos970Dependency.SiegelWalfisz



open _root_.Filter


end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.moving_signed_prime_multiple_lower_jb247_oai := @OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.moving_signed_prime_multiple_lower_jb247_oai
