-- Prove2me | solution 1 for OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.exists_uniform_riesz_contour_bound_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:57:20.267635+00:00
-- url     : https://prove2.me/submissions/960d30be-81e2-45d1-ab29-cdc47609fca4

import Batteries.Tactic.Lemma
import Mathlib
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Support
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Asymptotics.Defs
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
import Mathlib.Analysis.Real.Pi.Bounds
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
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
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
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Order.SuccPred.IntervalSucc
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
import Theorems.Thm_OAI_Erdos970_Erdos970Dependency_SiegelWalfisz_exists_primitive_real_zero_free_disk_jb247

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_E
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section AnalyticAssemblyScope
open scoped BigOperators Topology
section

open _root_.Complex _root_.Filter
open scoped Topology ComplexConjugate

namespace RealCharacterAnalysis

theorem real_values_iff_quadratic {q : ℕ}
    (χ : DirichletCharacter ℂ q) :
    (∀ a : ZMod q, (χ a).im = 0) ↔ χ.IsQuadratic := by
  constructor
  · intro h
    have hc : star χ = χ := by
      ext a
      exact Complex.conj_eq_iff_im.mpr (h a)
    have hi : χ⁻¹ = χ := (MulChar.star_eq_inv χ).symm.trans hc
    apply MulChar.isQuadratic_iff_sq_eq_one.mpr
    calc
      χ ^ 2 = χ * χ := sq χ
      _ = χ * χ⁻¹ := congrArg (χ * ·) hi.symm
      _ = 1 := mul_inv_cancel χ
  · intro h a
    rcases h a with h | h | h <;> simp [h]

end RealCharacterAnalysis
end

end AnalyticAssemblyScope
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_NormLogDerivLFunctionNegLogDerivZeta
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace WeightedTorusJets
open _root_.ArithmeticFunction DirichletCharacter
open scoped LSeries.notation BigOperators ComplexOrder
theorem norm_logDeriv_LFunction_le_neg_logDeriv_zeta {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    ‖deriv (LFunction χ) s / LFunction χ s‖ ≤
      (-deriv riemannZeta (s.re : ℂ) / riemannZeta (s.re : ℂ)).re := by
  have htw := LSeriesSummable_twist_vonMangoldt χ hs
  have hΛ := LSeriesSummable_vonMangoldt (show 1 < (s.re : ℂ).re from hs)
  calc
    ‖deriv (LFunction χ) s / LFunction χ s‖ = ‖LSeries (↗χ * ↗Λ) s‖ := by
      rw [LSeries_twist_vonMangoldt_eq χ hs,
        deriv_LFunction_eq_deriv_LSeries χ hs, LFunction_eq_LSeries χ hs]
      simp [neg_div]
    _ ≤ ∑' n, ‖LSeries.term (↗χ * ↗Λ) s n‖ := norm_tsum_le_tsum_norm htw.norm
    _ ≤ ∑' n, ‖LSeries.term ↗Λ (s.re : ℂ) n‖ := by
      apply htw.norm.tsum_le_tsum _ hΛ.norm
      intro n
      have hcoeff : ‖(↗χ * ↗Λ) n‖ ≤ ‖(↗Λ n : ℂ)‖ := by
        simpa using mul_le_of_le_one_left (norm_nonneg (vonMangoldt n : ℂ))
          (χ.norm_le_one (n : ZMod q))
      simpa only [LSeries.norm_term_eq, Complex.ofReal_re] using
        (LSeries.norm_term_le (f := ↗χ * ↗Λ) (g := ↗Λ) (n := n) s hcoeff)
    _ = (LSeries ↗Λ (s.re : ℂ)).re := by
      rw [LSeries, Complex.re_tsum hΛ]
      apply tsum_congr
      intro n
      have hn : 0 ≤ LSeries.term ↗Λ (s.re : ℂ) n :=
        LSeries.term_nonneg (by exact_mod_cast (vonMangoldt_nonneg (n := n))) s.re
      simpa using congrArg Complex.re (RCLike.norm_of_nonneg' hn)
    _ = (-deriv riemannZeta (s.re : ℂ) / riemannZeta (s.re : ℂ)).re :=
      congrArg Complex.re (LSeries_vonMangoldt_eq_deriv_riemannZeta_div (show 1 < (s.re : ℂ).re from hs))

end WeightedTorusJets

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_SumCharacterPeriodZero
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section IntroDependency0

section GrowthDependency0

namespace WeightedTorusJets

open _root_.Finset _root_.MeasureTheory
open scoped Fin.NatCast

theorem sum_character_period_eq_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∑ k ∈ range q, χ (k : ZMod q) = 0 := by
  classical
  rw [← Fin.sum_univ_eq_sum_range]
  have heq : ∀ a : Fin q, (ZMod.finEquiv q).toEquiv a = (a : ℕ) := by
    intro a
    cases q with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ q =>
      change a = ((a : ℕ) : Fin (q + 1))
      exact (Fin.cast_val_eq_self a).symm
  have hsum := Equiv.sum_comp (ZMod.finEquiv q).toEquiv (fun a => χ a)
  simpa only [heq, MulChar.sum_eq_zero_of_ne_one hχ] using hsum

theorem norm_sum_character_range_lt {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) :
    ‖∑ k ∈ range n, χ (k : ZMod q)‖ < q := by
  classical
  have hperiod : Function.Periodic (fun n => ∑ k ∈ range n, χ (k : ZMod q)) q := by
    intro n
    change (∑ k ∈ range (n + q), χ (k : ZMod q)) = ∑ k ∈ range n, χ (k : ZMod q)
    rw [Nat.add_comm n q, Finset.sum_range_add, sum_character_period_eq_zero χ hχ]
    simp
  rw [← hperiod.map_mod_nat n]
  have hbound : ‖∑ k ∈ range (n % q), χ (k : ZMod q)‖ ≤ (n % q : ℕ) := by
    calc
      _ ≤ ∑ k ∈ range (n % q), ‖χ (k : ZMod q)‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ range (n % q), (1 : ℝ) := sum_le_sum fun k _ => χ.norm_le_one k
      _ = (n % q : ℕ) := by simp
  exact hbound.trans_lt (by exact_mod_cast Nat.mod_lt n (NeZero.pos q))

theorem norm_sum_character_Icc_lt {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) :
    ‖∑ k ∈ Icc 1 n, χ (k : ZMod q)‖ < q := by
  have hzero : χ 0 = 0 := χ.map_zero' (hχ ∘ χ.level_one')
  have hbound := norm_sum_character_range_lt χ hχ (n + 1)
  rw [sum_range_eq_add_Ico _ (Nat.succ_pos n), Nat.cast_zero, hzero, zero_add,
    Nat.succ_eq_add_one, Ico_add_one_right_eq_Icc] at hbound
  exact hbound

theorem isBigO_sum_character_Icc_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    Asymptotics.IsBigO Filter.atTop (fun n : ℕ => ∑ k ∈ Icc 1 n, χ (k : ZMod q))
      (fun _ => (1 : ℝ)) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨q, Filter.Eventually.of_forall fun n => ?_⟩
  simpa using (norm_sum_character_Icc_lt χ hχ n).le

theorem mellin_partial_sum_neg {q : ℕ}
    (χ : DirichletCharacter ℂ q) (s : ℂ) :
    mellin (fun t : ℝ => ∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q)) (-s) =
      ∫ t : ℝ in Set.Ioi 1,
        (∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q)) * (t : ℂ) ^ (-(s + 1)) := by
  unfold mellin
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Set.Ici_subset_Ioi.mpr zero_lt_one) ?_]
  · rw [integral_Ici_eq_integral_Ioi]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only [smul_eq_mul, neg_add, sub_eq_add_neg]
    exact mul_comm _ _
  · intro t ht
    have ht1 : t < 1 := lt_of_not_ge ht.2
    simp [Nat.floor_eq_zero.mpr ht1]

theorem differentiableAt_partial_sum_integral {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun z => z * ∫ t : ℝ in Set.Ioi 1,
      (∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q)) * (t : ℂ) ^ (-(z + 1))) s := by
  have hmeas : Measurable (fun t : ℝ => ∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q)) :=
    (measurable_from_nat (f := fun n : ℕ => ∑ k ∈ Icc 1 n, χ (k : ZMod q))).comp
      Nat.measurable_floor
  have hmem : MemLp (fun t : ℝ => ∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q)) ⊤ :=
    memLp_top_of_bound hmeas.aestronglyMeasurable q
      (Filter.Eventually.of_forall fun t => (norm_sum_character_Icc_lt χ hχ ⌊t⌋₊).le)
  have htop : Asymptotics.IsBigO Filter.atTop
      (fun t : ℝ => ∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q)) (fun t => t ^ (-(0 : ℝ))) := by
    refine Asymptotics.isBigO_iff.mpr ⟨q, Filter.Eventually.of_forall fun t => ?_⟩
    simpa using (norm_sum_character_Icc_lt χ hχ ⌊t⌋₊).le
  have hbot : Asymptotics.IsBigO (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (fun t : ℝ => ∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q))
      (fun t => t ^ (-(-s.re - 1))) := by
    refine Asymptotics.isBigO_iff.mpr ⟨0, ?_⟩
    filter_upwards [(eventually_lt_nhds (show (0 : ℝ) < 1 from zero_lt_one)).filter_mono
      nhdsWithin_le_nhds] with t ht
    simp [Nat.floor_eq_zero.mpr ht]
  have hm : DifferentiableAt ℂ
      (mellin (fun t : ℝ => ∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q))) (-s) := by
    apply mellin_differentiableAt_of_isBigO_rpow
      ((hmem.locallyIntegrable le_top).locallyIntegrableOn _) htop
      (by simpa using neg_neg_of_pos hs) hbot
    simp only [Complex.neg_re]
    linarith
  have hfun : (fun z : ℂ => z * ∫ t : ℝ in Set.Ioi 1,
      (∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q)) * (t : ℂ) ^ (-(z + 1))) =
      (fun z : ℂ => z * mellin (fun t : ℝ => ∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q)) (-z)) := by
    funext z
    rw [mellin_partial_sum_neg]
  rw [hfun]
  exact differentiableAt_id.mul (hm.comp s differentiableAt_id.neg)

theorem LFunction_eq_partial_sum_integral {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction χ s = s * ∫ t : ℝ in Set.Ioi 1,
      (∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q)) * (t : ℂ) ^ (-(s + 1)) := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  apply LSeries_eq_mul_integral (r := 0) _ le_rfl (zero_lt_one.trans hs)
  · exact DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs
  · simpa using isBigO_sum_character_Icc_one χ hχ

end WeightedTorusJets

namespace WeightedTorusJets

open _root_.Finset _root_.MeasureTheory
open scoped Topology

theorem LFunction_eq_partial_sum_integral_of_re_pos {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunction χ s = s * ∫ t : ℝ in Set.Ioi 1,
      (∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q)) * (t : ℂ) ^ (-(s + 1)) := by
  let U : Set ℂ := {z | 0 < z.re}
  let F := DirichletCharacter.LFunction χ
  let G : ℂ → ℂ := fun z => z * ∫ t : ℝ in Set.Ioi 1,
    (∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q)) * (t : ℂ) ^ (-(z + 1))
  have hUo : IsOpen U := Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  have hUc : IsPreconnected U :=
    ((convex_Ioi (0 : ℝ)).linear_preimage Complex.reCLM.toLinearMap).isPreconnected
  have hF : AnalyticOnNhd ℂ F U :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd hUo
  have hG : AnalyticOnNhd ℂ G U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUo
    exact (differentiableAt_partial_sum_integral χ hχ hz).differentiableWithinAt
  have hV : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
    (Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by norm_num)
  have hFG : F =ᶠ[𝓝 (2 : ℂ)] G := by
    filter_upwards [hV] with z hz
    exact LFunction_eq_partial_sum_integral χ hχ hz
  exact hF.eqOn_of_preconnected_of_eventuallyEq hG hUc (by norm_num [U]) hFG hs

end WeightedTorusJets

end GrowthDependency0

section GrowthDependency1

open _root_.MeasureTheory _root_.Set

namespace WeightedTorusJets

 theorem integrableOn_min_mul_rpow {q r : ℝ} (hq : 0 ≤ q) (hr : r < -1) :
    IntegrableOn (fun x : ℝ => min x q * x ^ r) (Ioi 1) := by
  have hcont : ContinuousOn (fun x : ℝ => min x q * x ^ r) (Ioi 1) :=
    (continuous_id.min continuous_const).continuousOn.mul
      (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt (lt_trans zero_lt_one hx))))
  apply ((integrableOn_Ioi_rpow_of_lt hr zero_lt_one).const_mul q).mono'
    (hcont.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 ≤ x := (lt_trans zero_lt_one hx).le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_min hx0 hq) (Real.rpow_nonneg hx0 _))]
  exact mul_le_mul_of_nonneg_right (min_le_right x q) (Real.rpow_nonneg hx0 _)

 theorem integral_min_mul_rpow_exact {q η : ℝ} (hq : 1 ≤ q) (hη : 0 < η) (hη1 : η < 1) :
    (∫ x : ℝ in Ioi 1, min x q * x ^ (η - 2)) =
      (q ^ η - 1) / η + q ^ η / (1 - η) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hr : η - 2 < -1 := by linarith
  have hint := integrableOn_min_mul_rpow hq0.le hr
  have hfirst : (∫ x : ℝ in 1..q, min x q * x ^ (η - 2)) = (q ^ η - 1) / η := by
    calc
      _ = ∫ x : ℝ in 1..q, x ^ (η - 1) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hq] at hx
        have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
        dsimp only
        rw [min_eq_left hx.2]
        calc
          _ = x ^ (1 + (η - 2)) := by rw [Real.rpow_add hx0, Real.rpow_one]
          _ = _ := by congr 1; ring
      _ = _ := by
        rw [integral_rpow (Or.inl (by linarith : -1 < η - 1))]
        simp only [show η - 1 + 1 = η by ring, Real.one_rpow]
  have htail : (∫ x : ℝ in Ioi q, min x q * x ^ (η - 2)) = q ^ η / (1 - η) := by
    calc
      _ = ∫ x : ℝ in Ioi q, q * x ^ (η - 2) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        dsimp only
        rw [min_eq_right hx.le]
      _ = q * (-q ^ (η - 2 + 1) / (η - 2 + 1)) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt hr hq0]
      _ = _ := by
        have hp : q * q ^ (η - 1) = q ^ η := by
          calc
            _ = q ^ (1 + (η - 1)) := by rw [Real.rpow_add hq0, Real.rpow_one]
            _ = _ := by congr 1; ring
        rw [show η - 2 + 1 = η - 1 by ring]
        have hηn : η - 1 ≠ 0 := by linarith
        have hηn' : 1 - η ≠ 0 := by linarith
        field_simp
        nlinarith [hp]
  have hsplit := intervalIntegral.integral_interval_add_Ioi hint
    (hint.mono_set (Ioi_subset_Ioi hq))
  rw [hfirst, htail] at hsplit
  exact hsplit.symm

 theorem integral_min_mul_rpow_le {q η σ : ℝ} (hq : 1 ≤ q) (hη : 0 < η)
    (hηhalf : η ≤ 1 / 2) (hσ : 1 - η ≤ σ) :
    (∫ x : ℝ in Ioi 1, min x q * x ^ (-σ - 1)) ≤ q ^ η * (1 / η + 2) := by
  have hq0 : 0 ≤ q := le_trans zero_le_one hq
  have hσ0 : 0 < σ := by linarith
  have hη1 : η < 1 := by linarith
  have hint := integrableOn_min_mul_rpow hq0 (by linarith : -σ - 1 < -1)
  have henv := integrableOn_min_mul_rpow hq0 (by linarith : η - 2 < -1)
  calc
    _ ≤ ∫ x : ℝ in Ioi 1, min x q * x ^ (η - 2) := by
      apply integral_mono_ae hint henv
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith))
        (le_min (le_trans zero_le_one hx.le) hq0)
    _ = (q ^ η - 1) / η + q ^ η / (1 - η) := integral_min_mul_rpow_exact hq hη hη1
    _ ≤ q ^ η * (1 / η + 2) := by
      have hp : 0 ≤ q ^ η := Real.rpow_nonneg hq0 _
      have hfirst : (q ^ η - 1) / η ≤ q ^ η / η :=
        div_le_div_of_nonneg_right (by linarith) hη.le
      have htail : q ^ η / (1 - η) ≤ 2 * q ^ η := by
        apply (div_le_iff₀ (by linarith : 0 < 1 - η)).mpr
        nlinarith
      calc
        _ ≤ q ^ η / η + 2 * q ^ η := add_le_add hfirst htail
        _ = _ := by ring

end WeightedTorusJets

end GrowthDependency1

namespace WeightedTorusJets

open _root_.Finset _root_.MeasureTheory

theorem norm_sum_character_Icc_le_min {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {t : ℝ} (ht : 0 ≤ t) :
    ‖∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q)‖ ≤ min t (q : ℝ) := by
  apply le_min
  · calc
      ‖∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q)‖ ≤
          ∑ k ∈ Icc 1 ⌊t⌋₊, ‖χ (k : ZMod q)‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Icc 1 ⌊t⌋₊, (1 : ℝ) := sum_le_sum fun k _ => χ.norm_le_one k
      _ = (⌊t⌋₊ : ℝ) := by simp
      _ ≤ t := Nat.floor_le ht
  · exact (norm_sum_character_Icc_lt χ hχ ⌊t⌋₊).le

end WeightedTorusJets

end IntroDependency0

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_UniformDirichletBasepoint
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.MeasureTheory _root_.Set _root_.Finset _root_.Complex
open scoped Topology
namespace Erdos970Dependency.SiegelWalfisz
open WeightedTorusJets

theorem norm_LFunction_modulus_height {eta : ℝ} (heta : 0 < eta) (heta_half : eta ≤ 1 / 2)
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {s : ℂ} (hre : 1 - eta ≤ s.re) :
    ‖DirichletCharacter.LFunction chi s‖ ≤ (1 / eta + 2) * ‖s‖ * (q : ℝ) ^ eta := by
  have hs : 0 < s.re := by linarith
  have hq1 : (1 : ℝ) ≤ q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hint := integrableOn_min_mul_rpow (Nat.cast_nonneg q)
    (by linarith : -s.re - 1 < -1)
  have hI : ‖∫ t : ℝ in Ioi 1,
      (∑ k ∈ Icc 1 ⌊t⌋₊, chi (k : ZMod q)) * (t : ℂ) ^ (-(s + 1))‖ ≤
      ∫ t : ℝ in Ioi 1, min t (q : ℝ) * t ^ (-s.re - 1) := by
    apply norm_integral_le_of_norm_le hint
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have he : (-(s + 1)).re = -s.re - 1 := by simp <;> ring
    rw [he]
    exact mul_le_mul_of_nonneg_right (norm_sum_character_Icc_le_min chi hchi ht0.le)
      (Real.rpow_nonneg ht0.le _)
  have hbound := hI.trans (integral_min_mul_rpow_le hq1 heta heta_half hre)
  rw [LFunction_eq_partial_sum_integral_of_re_pos chi hchi hs, norm_mul]
  calc
    ‖s‖ * _ ≤ ‖s‖ * ((q : ℝ) ^ eta * (1 / eta + 2)) :=
      mul_le_mul_of_nonneg_left hbound (norm_nonneg s)
    _ = _ := by ring

theorem norm_LFunction_half_strip {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖DirichletCharacter.LFunction chi s‖ ≤ 4 * ‖s‖ * (q : ℝ) ^ (1 / 2 : ℝ) := by
  have h := norm_LFunction_modulus_height (eta := (1 / 2 : ℝ)) (s := s)
    (by norm_num) (by norm_num) chi hchi (by linarith)
  norm_num at h
  exact h

end Erdos970Dependency.SiegelWalfisz

end

section

open _root_.Complex
namespace Erdos970Dependency.SiegelWalfisz

theorem LFunction_ne_zero_right {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) : DirichletCharacter.LFunction chi s ≠ 0 := by
  rw [DirichletCharacter.LFunction_eq_LSeries chi hs]
  exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re chi hs

theorem uniform_log_derivative_right :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q) (s : ℂ),
      1 < s.re → ‖deriv (DirichletCharacter.LFunction chi) s / DirichletCharacter.LFunction chi s‖ ≤
        (s.re - 1)⁻¹ + C := by
  obtain ⟨C, hC, hbound⟩ := _root_.Erdos970.strongPnt_triv_bound_zeta
  refine ⟨C, hC, ?_⟩
  intro q _ chi s hs
  have hz := hbound s.re 0 hs
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hz
  exact (WeightedTorusJets.norm_logDeriv_LFunction_le_neg_logDeriv_zeta chi hs).trans
    ((Complex.re_le_norm _).trans hz)

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz
open scoped BigOperators

lemma absoluteZetaTwo_summable :
    Summable (fun n : ℕ => ‖LSeries.term (fun _ => 1) (2 : ℂ) n‖) := by
  apply Summable.norm
  exact LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (by intro n hn; simp) (by norm_num)

lemma one_le_absoluteZetaTwo : 1 ≤ absoluteZetaTwo := by
  have h := absoluteZetaTwo_summable.le_tsum 1 (fun n _ => norm_nonneg (LSeries.term (fun _ => 1) (2 : ℂ) n))
  simpa [LSeries.term, absoluteZetaTwo] using h

lemma norm_LSeries_le_absoluteZetaTwo (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    {s : ℂ} (hs : 2 ≤ s.re) : ‖LSeries f s‖ ≤ absoluteZetaTwo := by
  have hsum : LSeriesSummable f s :=
    LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => hf n) (by linarith)
  apply (norm_tsum_le_tsum_norm hsum.norm).trans
  apply Summable.tsum_le_tsum _ hsum.norm absoluteZetaTwo_summable
  intro n
  exact (LSeries.norm_term_le s (show ‖f n‖ ≤ ‖(1 : ℂ)‖ by simpa using hf n)).trans
    (LSeries.norm_term_le_of_re_le_re (fun _ => (1 : ℂ)) (by simpa using hs) n)

lemma norm_inv_LFunction_le_absoluteZetaTwo {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {s : ℂ} (hs : 2 ≤ s.re) :
    ‖(DirichletCharacter.LFunction chi s)⁻¹‖ ≤ absoluteZetaTwo := by
  let f : ℕ → ℂ := fun n => chi n * (ArithmeticFunction.moebius n : ℂ)
  have hf (n : ℕ) : ‖f n‖ ≤ 1 := by
    have hm : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast, ← Int.cast_abs]
      exact_mod_cast (show |ArithmeticFunction.moebius n| ≤ 1 from ArithmeticFunction.abs_moebius_le_one)
    change ‖chi n * (ArithmeticFunction.moebius n : ℂ)‖ ≤ 1
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (chi.norm_le_one n) (norm_nonneg _)).trans (by simpa using hm)
  have hs1 : 1 < s.re := by linarith
  have hp : DirichletCharacter.LFunction chi s * LSeries f s = 1 := by
    rw [DirichletCharacter.LFunction_eq_LSeries chi hs1]
    exact DirichletCharacter.LSeries.mul_mu_eq_one chi hs1
  have hn := LFunction_ne_zero_right chi hs1
  have hinv : (DirichletCharacter.LFunction chi s)⁻¹ = LSeries f s := by
    apply mul_left_cancel₀ hn
    rw [mul_inv_cancel₀ hn, hp]
  rw [hinv]
  exact norm_LSeries_le_absoluteZetaTwo f hf hs

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_LocalZeroLogDerivative
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
open scoped Topology BigOperators

theorem exists_local_zero_log_derivative_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℝ), 1 < B → ∀ f : ℂ → ℂ,
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z) →
      f 0 = 1 → (∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖f z‖ ≤ B) →
      ∃ S : Finset ℂ, (∀ z, z ∈ S ↔ ‖z‖ ≤ 19/20 ∧ f z = 0) ∧
        ∀ z : ℂ, ‖z‖ ≤ 17/20 → f z ≠ 0 →
          ‖deriv f z / f z - ∑ rho ∈ S, (analyticOrderAt f rho).toNat / (z-rho)‖ ≤
            C * Real.log B := by
  classical
  let K : ℝ := 16 * (9/10)^2 / (((9/10)-(17/20))^3) +
    1 / (((39/40)^2/(19/20)-(19/20)) * Real.log ((39/40)/(19/20)))
  refine ⟨max 1 K, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro B hB f hf hf0 hfB
  have hfne : f 0 ≠ 0 := by rw [hf0]; norm_num
  have hfinite : (_root_.Erdos970.zerosetKfR (19/20) (by norm_num) f).Finite :=
    _root_.Erdos970.lem_Contra_finiteKR (19/20) (by norm_num) (by norm_num) f hf ⟨0, by simp, hfne⟩
  have hex (rho : ℂ) : ∃ g : ℂ → ℂ,
      rho ∈ _root_.Erdos970.zerosetKfR (19/20) (by norm_num) f →
      AnalyticAt ℂ g rho ∧ g rho ≠ 0 ∧
      ∀ᶠ z in 𝓝 rho, f z = (z-rho)^(analyticOrderAt f rho).toNat * g z := by
    by_cases hr : rho ∈ _root_.Erdos970.zerosetKfR (19/20) (by norm_num) f
    · obtain ⟨g, hg⟩ := _root_.Erdos970.lem_analytic_zero_factor (39/40) (19/20)
        (by norm_num) (by norm_num) (by norm_num) f hf hfne rho hr
      exact ⟨g, fun _ => hg⟩
    · exact ⟨fun _ => 1, fun h => (hr h).elim⟩
  choose g hg using hex
  refine ⟨hfinite.toFinset, ?_, ?_⟩
  · intro z
    simp only [Set.Finite.mem_toFinset, _root_.Erdos970.zerosetKfR, Set.mem_ofPred_eq,
      Metric.mem_closedBall, dist_zero_right]
  · intro z hz hzne
    have hz' : z ∈ Metric.closedBall (0 : ℂ) (17/20) \
        _root_.Erdos970.zerosetKfR (19/20) (by norm_num) f := by
      refine ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using hz, ?_⟩
      intro h
      exact hzne h.2
    have h := _root_.Erdos970.final_ineq1 B hB (17/20) (9/10) (39/40) (19/20)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      f hf hf0 hfinite hg
      (fun w hw => hfB w ((Metric.closedBall_subset_closedBall (by norm_num : (39/40:ℝ) ≤ 1)) hw)) z hz'
    apply h.trans
    exact mul_le_mul_of_nonneg_right (le_max_right (1:ℝ) K) (Real.log_pos hB).le

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_DirichletZeroPenalty
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

theorem dirichletDiskPoint_half_strip (t : ℝ) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    1/2 ≤ (dirichletDiskPoint t w).re := by
  have h := (abs_le.mp ((Complex.abs_re_le_norm w).trans hw)).1
  rw [dirichletDiskPoint_re]
  linarith

theorem dirichletDiskPoint_norm (t : ℝ) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖dirichletDiskPoint t w‖ ≤ |t|+6 := by
  have hc : ‖dirichletCenter t‖ ≤ 3+|t| := by
    simpa [dirichletCenter, norm_mul] using
      (norm_add_le (3 : ℂ) ((t : ℂ)*Complex.I))
  have h := norm_add_le (dirichletCenter t) ((5/2 : ℂ)*w)
  have hn : ‖(5/2:ℂ)*w‖ = (5/2:ℝ)*‖w‖ := by rw [norm_mul]; norm_num
  rw [hn] at h
  change ‖dirichletDiskPoint t w‖ ≤ _ at h
  linarith

theorem normalizedDirichlet_zero {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (t : ℝ) : normalizedDirichlet chi t 0 = 1 := by
  unfold normalizedDirichlet dirichletDiskPoint
  simp only [mul_zero, add_zero]
  exact div_self (LFunction_ne_zero_right chi (by simp))

theorem normalizedDirichlet_analytic {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) (t : ℝ) (w : ℂ) :
    AnalyticAt ℂ (normalizedDirichlet chi t) w := by
  have hL := DirichletCharacter.differentiable_LFunction hchi
  have hd : Differentiable ℂ (normalizedDirichlet chi t) := by
    unfold normalizedDirichlet dirichletDiskPoint
    fun_prop
  exact hd.analyticAt w

theorem normalizedDirichlet_bound {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) (t : ℝ) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖normalizedDirichlet chi t w‖ ≤ dirichletDiskEnvelope q t := by
  have hu := norm_LFunction_half_strip chi hchi (dirichletDiskPoint_half_strip t hw)
  have hi := norm_inv_LFunction_le_absoluteZetaTwo chi (s := dirichletCenter t) (by norm_num)
  have hZ : 0 ≤ absoluteZetaTwo := zero_le_one.trans one_le_absoluteZetaTwo
  unfold normalizedDirichlet
  rw [div_eq_mul_inv, norm_mul]
  calc
    _ ≤ (4 * ‖dirichletDiskPoint t w‖ * (q : ℝ)^(1/2:ℝ)) * absoluteZetaTwo :=
      mul_le_mul hu hi (norm_nonneg _) (by positivity)
    _ ≤ (4 * (|t|+6) * (q : ℝ)^(1/2:ℝ)) * absoluteZetaTwo := by
      gcongr
      exact dirichletDiskPoint_norm t hw
    _ = dirichletDiskEnvelope q t := by unfold dirichletDiskEnvelope; ring

theorem dirichletDiskEnvelope_gt_one (q : ℕ) [NeZero q] (t : ℝ) :
    1 < dirichletDiskEnvelope q t := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hp : (1 : ℝ) ≤ (q : ℝ)^(1/2:ℝ) := Real.one_le_rpow hq (by norm_num)
  have hZ := one_le_absoluteZetaTwo
  have ht := abs_nonneg t
  unfold dirichletDiskEnvelope
  have h1 : 24 ≤ 4 * absoluteZetaTwo * (|t|+6) := by nlinarith
  have h2 := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 4 * absoluteZetaTwo * (|t|+6))
  nlinarith

theorem normalizedDirichlet_zero_re_lt {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) (t : ℝ) {w : ℂ}
    (hw : normalizedDirichlet chi t w = 0) : w.re < -4/5 := by
  have hn := LFunction_ne_zero_right chi (s := dirichletCenter t) (by simp)
  have hz : DirichletCharacter.LFunction chi (dirichletDiskPoint t w) = 0 :=
    (div_eq_zero_iff.mp hw).resolve_right hn
  by_contra! h
  have hr : 1 ≤ (dirichletDiskPoint t w).re := by rw [dirichletDiskPoint_re]; linarith
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re chi (Or.inl hchi) hr hz

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz
open scoped BigOperators

theorem log_dirichletDiskEnvelope_bound (q : ℕ) [NeZero q] (t : ℝ) :
    Real.log (dirichletDiskEnvelope q t) ≤
      (Real.log (4 * absoluteZetaTwo)+1) * (Real.log (q : ℝ)+Real.log (|t|+6)) := by
  have hZ := one_le_absoluteZetaTwo
  have hZp : 0 < 4 * absoluteZetaTwo := by linarith
  have ht := abs_nonneg t
  have htp : 0 < |t|+6 := by linarith
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hqp : (0 : ℝ) < q := by linarith
  have hlogq := Real.log_nonneg hq
  have hlogZ : 0 ≤ Real.log (4 * absoluteZetaTwo) := Real.log_nonneg (by linarith)
  have hlogt : 1 ≤ Real.log (|t|+6) :=
    ((Real.lt_log_iff_exp_lt htp).mpr (Real.exp_one_lt_three.trans (by linarith))).le
  have heq : Real.log (dirichletDiskEnvelope q t) =
      Real.log (4 * absoluteZetaTwo)+Real.log (|t|+6)+(1/2)*Real.log (q : ℝ) := by
    unfold dirichletDiskEnvelope
    rw [Real.log_mul (mul_pos hZp htp).ne' (Real.rpow_pos_of_pos hqp _).ne',
      Real.log_mul hZp.ne' htp.ne', Real.log_rpow hqp]
  rw [heq]
  nlinarith [mul_nonneg hlogZ hlogq, mul_le_mul_of_nonneg_left hlogt hlogZ]

theorem normalizedDirichlet_log_derivative {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) (t : ℝ) (w : ℂ)
    (hw : DirichletCharacter.LFunction chi (dirichletDiskPoint t w) ≠ 0) :
    deriv (normalizedDirichlet chi t) w / normalizedDirichlet chi t w =
      (5/2:ℂ) * (deriv (DirichletCharacter.LFunction chi) (dirichletDiskPoint t w) /
        DirichletCharacter.LFunction chi (dirichletDiskPoint t w)) := by
  have hn := LFunction_ne_zero_right chi (s := dirichletCenter t) (by simp)
  have hp : HasDerivAt (dirichletDiskPoint t) (5/2:ℂ) w := by
    simpa only [dirichletDiskPoint, id_eq, mul_one] using! (((hasDerivAt_id w).const_mul (5/2:ℂ)).const_add (dirichletCenter t))
  have hd := (((DirichletCharacter.differentiable_LFunction hchi).differentiableAt.hasDerivAt).comp w hp).div_const
    (DirichletCharacter.LFunction chi (dirichletCenter t))
  change HasDerivAt (normalizedDirichlet chi t)
    ((deriv (DirichletCharacter.LFunction chi) (dirichletDiskPoint t w) * (5/2:ℂ)) /
      DirichletCharacter.LFunction chi (dirichletCenter t)) w at hd
  rw [hd.deriv]
  unfold normalizedDirichlet
  field_simp

theorem uniform_dirichlet_local_log_derivative :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
      chi ≠ 1 → ∀ t : ℝ, ∃ S : Finset ℂ,
        (∀ rho, rho ∈ S ↔ ‖rho‖ ≤ 19/20 ∧
          DirichletCharacter.LFunction chi (dirichletDiskPoint t rho) = 0) ∧
        (∀ rho ∈ S, rho.re < -4/5) ∧
        ∀ w : ℂ, ‖w‖ ≤ 17/20 →
          DirichletCharacter.LFunction chi (dirichletDiskPoint t w) ≠ 0 →
          ‖(5/2:ℂ) * (deriv (DirichletCharacter.LFunction chi) (dirichletDiskPoint t w) /
            DirichletCharacter.LFunction chi (dirichletDiskPoint t w)) -
            ∑ rho ∈ S, (analyticOrderAt (normalizedDirichlet chi t) rho).toNat / (w-rho)‖ ≤
            C * (Real.log (q : ℝ)+Real.log (|t|+6)) := by
  classical
  obtain ⟨C, hC, hlocal⟩ := exists_local_zero_log_derivative_constant
  have hZ := one_le_absoluteZetaTwo
  have hlogZ : 0 ≤ Real.log (4 * absoluteZetaTwo) := Real.log_nonneg (by linarith)
  refine ⟨C * (Real.log (4 * absoluteZetaTwo)+1), mul_pos hC (by linarith), ?_⟩
  intro q _ chi hchi t
  have hn := LFunction_ne_zero_right chi (s := dirichletCenter t) (by simp)
  obtain ⟨S, hS, hb⟩ := hlocal (dirichletDiskEnvelope q t) (dirichletDiskEnvelope_gt_one q t)
    (normalizedDirichlet chi t) (fun w _ => normalizedDirichlet_analytic chi hchi t w)
    (normalizedDirichlet_zero chi t) (fun w hw => normalizedDirichlet_bound chi hchi t
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hw))
  have hzeros (rho : ℂ) : normalizedDirichlet chi t rho = 0 ↔
      DirichletCharacter.LFunction chi (dirichletDiskPoint t rho) = 0 := by
    unfold normalizedDirichlet
    exact div_eq_zero_iff.trans (or_iff_left hn)
  refine ⟨S, fun rho => (hS rho).trans (and_congr_right fun _ => hzeros rho), ?_, ?_⟩
  · intro rho hr
    exact normalizedDirichlet_zero_re_lt chi hchi t ((hS rho).mp hr).2
  · intro w hw hne
    have h := hb w hw (fun hz => hne ((hzeros w).mp hz))
    rw [normalizedDirichlet_log_derivative chi hchi t w hne] at h
    apply h.trans
    calc
      _ ≤ C * ((Real.log (4 * absoluteZetaTwo)+1) * (Real.log (q : ℝ)+Real.log (|t|+6))) :=
        mul_le_mul_of_nonneg_left (log_dirichletDiskEnvelope_bound q t) hC.le
      _ = _ := by ring

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz
open scoped BigOperators

lemma real_zero_term_nonneg {w rho : ℂ} (m : ℕ)
    (h : rho.re ≤ w.re) : 0 ≤ (((m : ℂ) / (w-rho)).re) := by
  rw [Complex.div_re]
  simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, zero_div, add_zero,
    Complex.sub_re]
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr h)) (Complex.normSq_nonneg _)

theorem uniform_neg_real_log_derivative :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
      chi ≠ 1 → ∀ sigma t : ℝ, 1 < sigma → sigma ≤ 2 →
      (-deriv (DirichletCharacter.LFunction chi) ((sigma:ℂ)+(t:ℂ)*Complex.I) /
        DirichletCharacter.LFunction chi ((sigma:ℂ)+(t:ℂ)*Complex.I)).re ≤
        C * (Real.log (q:ℝ)+Real.log (|t|+6)) := by
  classical
  obtain ⟨C, hC, hlocal⟩ := uniform_dirichlet_local_log_derivative
  refine ⟨C, hC, ?_⟩
  intro q _ chi hchi sigma t hs hs2
  obtain ⟨S, _, hSre, hb⟩ := hlocal q chi hchi t
  let w : ℂ := ((2/5*(sigma-3):ℝ):ℂ)
  have hw : ‖w‖ ≤ 17/20 := by
    change ‖((2/5*(sigma-3):ℝ):ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hwre : -4/5 < w.re := by
    dsimp only [w]
    simp only [Complex.ofReal_re]
    linarith
  have hnonzero : DirichletCharacter.LFunction chi (dirichletDiskPoint t w) ≠ 0 := by
    rw [dirichletDiskPoint_ofReal]
    exact LFunction_ne_zero_right chi (by simpa using hs)
  have h := hb w hw hnonzero
  have hsum : 0 ≤ (∑ rho ∈ S, (analyticOrderAt (normalizedDirichlet chi t) rho).toNat / (w-rho) : ℂ).re := by
    rw [Complex.re_sum]
    exact Finset.sum_nonneg (fun rho hr => real_zero_term_nonneg _ ((hSre rho hr).le.trans hwre.le))
  have herror := (Complex.re_le_norm (-(
    (5/2:ℂ) * (deriv (DirichletCharacter.LFunction chi) (dirichletDiskPoint t w) /
      DirichletCharacter.LFunction chi (dirichletDiskPoint t w)) -
      ∑ rho ∈ S, (analyticOrderAt (normalizedDirichlet chi t) rho).toNat / (w-rho)))).trans
    (by simpa only [norm_neg] using h)
  have hscale (a : ℂ) : ((5/2:ℂ)*a).re = (5/2:ℝ)*a.re := by
    norm_num [Complex.mul_re]
  rw [Complex.neg_re, Complex.sub_re, hscale] at herror
  have hq : (1:ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hpos : 0 ≤ C * (Real.log (q:ℝ)+Real.log (|t|+6)) :=
    mul_nonneg hC.le (add_nonneg (Real.log_nonneg hq) (Real.log_nonneg (by have := abs_nonneg t; linarith)))
  rw [show (sigma:ℂ)+(t:ℂ)*Complex.I = dirichletDiskPoint t w from (dirichletDiskPoint_ofReal sigma t).symm]
  rw [neg_div, Complex.neg_re]
  nlinarith

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz
open scoped BigOperators

lemma normalizedDirichlet_zero_order_pos {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) (t : ℝ) {rho : ℂ}
    (hr : ‖rho‖ ≤ 19/20) (hz : normalizedDirichlet chi t rho = 0) :
    1 ≤ (analyticOrderAt (normalizedDirichlet chi t) rho).toNat := by
  have hf : ∀ w ∈ Metric.closedBall (0:ℂ) 1, AnalyticAt ℂ (normalizedDirichlet chi t) w :=
    fun w _ => normalizedDirichlet_analytic chi hchi t w
  have hfne : normalizedDirichlet chi t 0 ≠ 0 := by rw [normalizedDirichlet_zero]; norm_num
  have hmem : rho ∈ _root_.Erdos970.zerosetKfR (19/20) (by norm_num) (normalizedDirichlet chi t) :=
    ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using hr, hz⟩
  have ht := _root_.Erdos970.lem_m_rho_is_nat (39/40) (19/20) (by norm_num) (by norm_num)
    (normalizedDirichlet chi t) hf hfne (by norm_num) rho hmem
  have hge := _root_.Erdos970.lem_m_rho_ge_1 (39/40) (19/20) (by norm_num) (by norm_num)
    (normalizedDirichlet chi t) hf hfne (by norm_num) rho hmem
  simpa using ENat.toNat_le_toNat hge ht

theorem uniform_zero_penalty :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
      chi ≠ 1 → ∀ sigma beta t : ℝ,
      1 < sigma → sigma ≤ 2 → 3/4 ≤ beta → beta < 1 →
      DirichletCharacter.LFunction chi ((beta:ℂ)+(t:ℂ)*Complex.I) = 0 →
      (-deriv (DirichletCharacter.LFunction chi) ((sigma:ℂ)+(t:ℂ)*Complex.I) /
        DirichletCharacter.LFunction chi ((sigma:ℂ)+(t:ℂ)*Complex.I)).re ≤
        C * (Real.log (q:ℝ)+Real.log (|t|+6)) - 1/(sigma-beta) := by
  classical
  obtain ⟨C, hC, hlocal⟩ := uniform_dirichlet_local_log_derivative
  refine ⟨C, hC, ?_⟩
  intro q _ chi hchi sigma beta t hs hs2 hb34 hb1 hzero
  obtain ⟨S, hS, hSre, hbound⟩ := hlocal q chi hchi t
  let w : ℂ := ((2/5*(sigma-3):ℝ):ℂ)
  let rho0 : ℂ := ((2/5*(beta-3):ℝ):ℂ)
  have hw : ‖w‖ ≤ 17/20 := by
    change ‖((2/5*(sigma-3):ℝ):ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hr : ‖rho0‖ ≤ 19/20 := by
    change ‖((2/5*(beta-3):ℝ):ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hwre : -4/5 < w.re := by
    dsimp only [w]
    simp only [Complex.ofReal_re]
    linarith
  have hrL : DirichletCharacter.LFunction chi (dirichletDiskPoint t rho0) = 0 := by
    rw [dirichletDiskPoint_ofReal]
    exact hzero
  have hrmem : rho0 ∈ S := (hS rho0).mpr ⟨hr, hrL⟩
  have hrNorm : normalizedDirichlet chi t rho0 = 0 := by
    unfold normalizedDirichlet
    rw [hrL, zero_div]
  have hm := normalizedDirichlet_zero_order_pos chi hchi t hr hrNorm
  have hden : 0 < sigma-beta := by linarith
  have hsub : w-rho0 = ((2/5*(sigma-beta):ℝ):ℂ) := by
    dsimp only [w, rho0]
    push_cast
    ring
  have hterm : (5/2:ℝ)/(sigma-beta) ≤
      (((analyticOrderAt (normalizedDirichlet chi t) rho0).toNat:ℂ)/(w-rho0)).re := by
    rw [hsub]
    rw [show ((analyticOrderAt (normalizedDirichlet chi t) rho0).toNat:ℂ) =
      (((analyticOrderAt (normalizedDirichlet chi t) rho0).toNat:ℝ):ℂ) by simp]
    rw [← Complex.ofReal_div, Complex.ofReal_re]
    calc
      _ = 1/(2/5*(sigma-beta)) := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast hm) (by positivity)
  have hsum : (5/2:ℝ)/(sigma-beta) ≤
      (∑ rho ∈ S, (analyticOrderAt (normalizedDirichlet chi t) rho).toNat / (w-rho):ℂ).re := by
    rw [Complex.re_sum]
    apply hterm.trans
    exact Finset.single_le_sum (fun rho hr => real_zero_term_nonneg (analyticOrderAt (normalizedDirichlet chi t) rho).toNat ((hSre rho hr).le.trans hwre.le)) hrmem
  have hn : DirichletCharacter.LFunction chi (dirichletDiskPoint t w) ≠ 0 := by
    rw [dirichletDiskPoint_ofReal]
    exact LFunction_ne_zero_right chi (by simpa using hs)
  have h := hbound w hw hn
  have herror := (Complex.re_le_norm (-(
    (5/2:ℂ) * (deriv (DirichletCharacter.LFunction chi) (dirichletDiskPoint t w) /
      DirichletCharacter.LFunction chi (dirichletDiskPoint t w)) -
      ∑ rho ∈ S, (analyticOrderAt (normalizedDirichlet chi t) rho).toNat / (w-rho)))).trans
    (by simpa only [norm_neg] using h)
  have hscale (a:ℂ) : ((5/2:ℂ)*a).re = (5/2:ℝ)*a.re := by norm_num [Complex.mul_re]
  rw [Complex.neg_re, Complex.sub_re, hscale] at herror
  have hq : (1:ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hpos : 0 ≤ C*(Real.log (q:ℝ)+Real.log (|t|+6)) :=
    mul_nonneg hC.le (add_nonneg (Real.log_nonneg hq) (Real.log_nonneg (by have := abs_nonneg t; linarith)))
  rw [show (sigma:ℂ)+(t:ℂ)*Complex.I = dirichletDiskPoint t w from (dirichletDiskPoint_ofReal sigma t).symm,
    neg_div, Complex.neg_re]
  rw [div_eq_mul_inv] at hsum
  rw [one_div]
  nlinarith only [herror, hsum, hpos]

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_CharacterPositivity
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
open scoped ComplexOrder

lemma characterPhase_norm {n : ℕ} (hn : n ≠ 0) (t : ℝ) : ‖characterPhase n t‖ = 1 := by
  unfold characterPhase
  rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
  simp

lemma characterPhase_double {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    characterPhase n (2*t) = characterPhase n t ^ 2 := by
  unfold characterPhase
  rw [sq, ← Complex.cpow_add _ _ (by exact_mod_cast hn : (n:ℂ) ≠ 0)]
  congr 1
  push_cast
  ring

lemma twist_vonMangoldt_term_split {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (sigma t : ℝ) (n : ℕ) :
    LSeries.term (fun k => chi k * (ArithmeticFunction.vonMangoldt k : ℂ))
      ((sigma:ℂ)+(t:ℂ)*Complex.I) n =
    LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (sigma:ℂ) n *
      chi n * characterPhase n t := by
  by_cases hn : n = 0
  · simp [hn]
  · have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
      Complex.cpow_add _ _ hnC]
    unfold characterPhase
    rw [neg_mul, Complex.cpow_neg]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

lemma character_positivity_polynomial (u : ℂ) (hu : ‖u‖ ≤ 1) :
    0 ≤ 3+4*u.re+(u^2).re := by
  have hsq : u.re^2+u.im^2 ≤ 1 := by
    have h := Complex.sq_norm u
    rw [Complex.normSq_apply] at h
    nlinarith [norm_nonneg u]
  simp only [pow_two, Complex.mul_re]
  nlinarith [sq_nonneg (1+u.re)]

lemma vonMangoldt_three_four_one_nonneg {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (sigma t : ℝ) (n : ℕ) :
    0 ≤ (3 * LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (sigma:ℂ) n +
      4 * LSeries.term (fun k => chi k * (ArithmeticFunction.vonMangoldt k : ℂ))
        ((sigma:ℂ)+(t:ℂ)*Complex.I) n +
      LSeries.term (fun k => (chi^2) k * (ArithmeticFunction.vonMangoldt k : ℂ))
        ((sigma:ℂ)+(2*t:ℝ)*Complex.I) n).re := by
  by_cases hn : n = 0
  · simp [hn]
  · let a : ℂ := LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (sigma:ℂ) n
    let u : ℂ := chi n * characterPhase n t
    have hu : ‖u‖ ≤ 1 := by
      dsimp only [u]
      rw [norm_mul, characterPhase_norm hn, mul_one]
      exact chi.norm_le_one n
    have ha : 0 ≤ a := LSeries.term_nonneg
      (by exact_mod_cast (ArithmeticFunction.vonMangoldt_nonneg (n := n))) sigma
    have ha' := Complex.nonneg_iff.mp ha
    rw [twist_vonMangoldt_term_split, twist_vonMangoldt_term_split,
      characterPhase_double hn]
    have hp : (chi^2) n = (chi n)^2 := chi.pow_apply' (by decide) n
    rw [hp]
    have heq : 3*a+4*(a*chi n*characterPhase n t)+a*(chi n)^2*(characterPhase n t)^2 =
        a*(3+4*u+u^2) := by dsimp [u] <;> ring
    change 0 ≤ (3*a+4*(a*chi n*characterPhase n t)+a*(chi n)^2*(characterPhase n t)^2).re
    rw [heq, Complex.mul_re, ← ha'.2]
    simp only [zero_mul, sub_zero]
    apply mul_nonneg ha'.1
    simpa using character_positivity_polynomial u hu

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz
open scoped BigOperators

lemma twisted_series_eq_actual_log_derivative {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => chi n * (ArithmeticFunction.vonMangoldt n : ℂ)) s =
      -deriv (DirichletCharacter.LFunction chi) s / DirichletCharacter.LFunction chi s := by
  change LSeries ((fun n : ℕ => chi n) * (fun n => (ArithmeticFunction.vonMangoldt n:ℂ))) s = _
  rw [DirichletCharacter.LSeries_twist_vonMangoldt_eq chi hs,
    ← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries chi hs,
    ← DirichletCharacter.LFunction_eq_LSeries chi hs]

theorem character_log_derivative_positivity {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (sigma t : ℝ) (hs : 1 < sigma) :
    0 ≤ 3 * (-deriv riemannZeta (sigma:ℂ) / riemannZeta (sigma:ℂ)).re +
      4 * (-deriv (DirichletCharacter.LFunction chi) ((sigma:ℂ)+(t:ℂ)*Complex.I) /
        DirichletCharacter.LFunction chi ((sigma:ℂ)+(t:ℂ)*Complex.I)).re +
      (-deriv (DirichletCharacter.LFunction (chi^2)) ((sigma:ℂ)+(2*t:ℝ)*Complex.I) /
        DirichletCharacter.LFunction (chi^2) ((sigma:ℂ)+(2*t:ℝ)*Complex.I)).re := by
  let a := LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n:ℂ)) (sigma:ℂ)
  let b := LSeries.term (fun n => chi n * (ArithmeticFunction.vonMangoldt n:ℂ))
    ((sigma:ℂ)+(t:ℂ)*Complex.I)
  let c := LSeries.term (fun n => (chi^2) n * (ArithmeticFunction.vonMangoldt n:ℂ))
    ((sigma:ℂ)+(2*t:ℝ)*Complex.I)
  have ha : Summable a := ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hs)
  have hb : Summable b := DirichletCharacter.LSeriesSummable_twist_vonMangoldt chi (by simpa using hs)
  have hc : Summable c := DirichletCharacter.LSeriesSummable_twist_vonMangoldt (chi^2) (by simpa using hs)
  have hsum := ((ha.mul_left (3:ℂ)).add (hb.mul_left (4:ℂ))).add hc
  have hvalue := ((ha.hasSum.mul_left (3:ℂ)).add (hb.hasSum.mul_left (4:ℂ))).add hc.hasSum
  have hpositive : 0 ≤ (∑' n:ℕ, (3*a n+4*b n+c n)).re := by
    rw [Complex.re_tsum hsum]
    exact tsum_nonneg (fun n => vonMangoldt_three_four_one_nonneg chi sigma t n)
  rw [hvalue.tsum_eq] at hpositive
  change 0 ≤ (3 * LSeries (fun n => (ArithmeticFunction.vonMangoldt n:ℂ)) (sigma:ℂ) +
    4 * LSeries (fun n => chi n * (ArithmeticFunction.vonMangoldt n:ℂ)) ((sigma:ℂ)+(t:ℂ)*Complex.I) +
    LSeries (fun n => (chi^2) n * (ArithmeticFunction.vonMangoldt n:ℂ)) ((sigma:ℂ)+(2*t:ℝ)*Complex.I)).re at hpositive
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hs),
    twisted_series_eq_actual_log_derivative chi (by simpa using hs),
    twisted_series_eq_actual_log_derivative (chi^2) (by simpa using hs)] at hpositive
  simpa [Complex.add_re, Complex.mul_re] using hpositive

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
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

lemma modulusHeight_double_le (q : ℕ) [NeZero q] (t : ℝ) :
    modulusHeight q (2*t) ≤ 2 * modulusHeight q t := by
  have hq : (1:ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlq := Real.log_nonneg hq
  have ht := abs_nonneg t
  have htp : 0 < |t|+6 := by linarith
  have h2 : Real.log 2 ≤ Real.log (|t|+6) := Real.log_le_log (by norm_num) (by linarith)
  have he : |2*t| = 2*|t| := by rw [abs_mul]; norm_num
  have hlog : Real.log (|2*t|+6) ≤ Real.log (2*(|t|+6)) :=
    Real.log_le_log (by positivity) (by rw [he]; linarith)
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) htp.ne'] at hlog
  unfold modulusHeight
  linarith

theorem exists_nonquadratic_zero_reciprocal_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
      chi^2 ≠ 1 → ∀ sigma beta t : ℝ,
      1 < sigma → sigma ≤ 2 → 3/4 ≤ beta → beta < 1 →
      DirichletCharacter.LFunction chi ((beta:ℂ)+(t:ℂ)*Complex.I) = 0 →
      4/(sigma-beta) ≤ 3/(sigma-1)+K*modulusHeight q t := by
  obtain ⟨Cp, hCp, hp⟩ := uniform_zero_penalty
  obtain ⟨Cu, hCu, hu⟩ := uniform_neg_real_log_derivative
  obtain ⟨Cz, hCz, hz⟩ := _root_.Erdos970.strongPnt_triv_bound_zeta
  refine ⟨3*Cz+4*Cp+2*Cu, by linarith, ?_⟩
  intro q _ chi hsq sigma beta t hs hs2 hb34 hb1 hzero
  have hchi : chi ≠ 1 := by
    intro h
    apply hsq
    rw [h, one_pow]
  have hpen := hp q chi hchi sigma beta t hs hs2 hb34 hb1 hzero
  have hup := hu q (chi^2) hsq sigma (2*t) hs hs2
  have hup' : (-deriv (DirichletCharacter.LFunction (chi^2)) ((sigma:ℂ)+(2*t:ℝ)*Complex.I) /
      DirichletCharacter.LFunction (chi^2) ((sigma:ℂ)+(2*t:ℝ)*Complex.I)).re ≤
      2*Cu*modulusHeight q t := by
    apply hup.trans
    change Cu * modulusHeight q (2*t) ≤ _
    have h := mul_le_mul_of_nonneg_left (modulusHeight_double_le q t) hCu.le
    nlinarith only [h]
  have hzeta := hz sigma 0 hs
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hzeta
  have hzeta' := (Complex.re_le_norm (-deriv riemannZeta (sigma:ℂ)/riemannZeta (sigma:ℂ))).trans hzeta
  have habsorb : Cz ≤ Cz*modulusHeight q t := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (modulusHeight_ge_one q t) hCz
  have hpositive := character_log_derivative_positivity chi sigma t hs
  change _ ≤ Cp*modulusHeight q t-1/(sigma-beta) at hpen
  rw [one_div] at hpen
  simp only [div_eq_mul_inv]
  nlinarith only [hpositive, hpen, hup', hzeta', habsorb]

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz

theorem exists_nonquadratic_zero_free_region :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
      chi^2 ≠ 1 → ∀ s : ℂ,
      1-c/modulusHeight q s.im ≤ s.re → DirichletCharacter.LFunction chi s ≠ 0 := by
  obtain ⟨K, hK, hineq⟩ := exists_nonquadratic_zero_reciprocal_bound
  let delta : ℝ := 1/(8*(K+1))
  have hd : 0 < delta := by dsimp [delta] <;> positivity
  have hd8 : delta ≤ 1/8 := by
    apply (div_le_iff₀ (by positivity : 0 < 8*(K+1))).mpr
    nlinarith
  have hKd : K*delta ≤ 1/8 := by
    dsimp only [delta]
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity : 0 < 8*(K+1))).mpr
    nlinarith
  let c : ℝ := delta/4
  refine ⟨c, by dsimp only [c] <;> positivity, ?_⟩
  intro q _ chi hsq s hs hzero
  have hchi : chi ≠ 1 := by
    intro h
    apply hsq
    rw [h, one_pow]
  have hb1 : s.re < 1 := by
    by_contra! h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re chi (Or.inl hchi) h hzero
  let H : ℝ := modulusHeight q s.im
  have hH : 1 ≤ H := modulusHeight_ge_one q s.im
  have hHp : 0 < H := by linarith
  let x : ℝ := delta/H
  have hxp : 0 < x := by dsimp only [x] <;> positivity
  have hxd : x ≤ delta := by
    apply (div_le_iff₀ hHp).mpr
    nlinarith
  have hclose : 1-s.re ≤ x/4 := by
    have he : c/H = x/4 := by dsimp only [c,x] <;> ring
    change 1-c/H ≤ s.re at hs
    rw [he] at hs
    linarith
  have hb34 : 3/4 ≤ s.re := by linarith
  have hsigma : 1 < 1+x := by linarith
  have hsigma2 : 1+x ≤ 2 := by linarith
  have hz : DirichletCharacter.LFunction chi ((s.re:ℂ)+(s.im:ℂ)*Complex.I) = 0 := by
    simpa only [Complex.re_add_im] using hzero
  have hr := hineq q chi hsq (1+x) s.re s.im hsigma hsigma2 hb34 hb1 hz
  let y : ℝ := 1+x-s.re
  have hyp : 0 < y := by dsimp only [y] <;> linarith
  have hy : y ≤ (5/4)*x := by dsimp only [y] <;> linarith
  have hKx : K*H*x ≤ 1/8 := by
    have he : K*H*x = K*delta := by dsimp only [x]; field_simp
    rw [he]
    exact hKd
  change 4/y ≤ 3/(1+x-1)+K*H at hr
  rw [add_sub_cancel_left] at hr
  have h := mul_le_mul_of_nonneg_right ((div_le_iff₀ hyp).mp hr) hxp.le
  have he : (3/x+K*H)*y*x = 3*y+K*H*x*y := by
    field_simp
  rw [he] at h
  have hKy := mul_le_mul_of_nonneg_right hKx hyp.le
  nlinarith only [h, hKy, hy, hxp]

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_PrincipalEulerCorrection
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

lemma prime_cpow_neg_norm_le_half {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖(p:ℂ)^(-s)‖ ≤ 1/2 := by
  rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
  have hpR : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  calc
    _ ≤ (p:ℝ)^(-1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ = 1/(p:ℝ) := by rw [Real.rpow_neg_one, one_div]
    _ ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hpR

lemma localEulerFactor_ne_zero {p : ℕ} (hp : p.Prime) {alpha s : ℂ}
    (ha : ‖alpha‖ ≤ 1) (hs : 1 ≤ s.re) : localEulerFactor alpha p s ≠ 0 := by
  have hu : ‖alpha*(p:ℂ)^(-s)‖ ≤ 1/2 := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right ha (norm_nonneg _)).trans (by simpa using prime_cpow_neg_norm_le_half hp hs)
  intro hz
  have he : alpha*(p:ℂ)^(-s) = 1 := (sub_eq_zero.mp hz).symm
  rw [he, norm_one] at hu
  norm_num at hu

lemma localEulerFactor_differentiable {p : ℕ} (hp : p.Prime) (alpha : ℂ) :
    Differentiable ℂ (localEulerFactor alpha p) := by
  unfold localEulerFactor
  fun_prop (disch := exact Or.inl (by exact_mod_cast hp.ne_zero))

lemma localEulerFactor_deriv {p : ℕ} (hp : p.Prime) (alpha s : ℂ) :
    deriv (localEulerFactor alpha p) s =
      (Real.log (p:ℝ):ℂ) * (alpha*(p:ℂ)^(-s)) := by
  have hn : (p:ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hd := ((((hasDerivAt_id s).neg).const_cpow (c := (p:ℂ)) (Or.inl hn)).const_mul alpha).const_sub 1
  simp only [Pi.neg_apply, id_eq] at hd
  convert! hd.deriv using 1
  all_goals try with_reducible_and_instances rfl
  rw [← Complex.natCast_log]
  ring

lemma norm_logDeriv_localEulerFactor {p : ℕ} (hp : p.Prime) {alpha s : ℂ}
    (ha : ‖alpha‖ ≤ 1) (hs : 1 ≤ s.re) :
    ‖logDeriv (localEulerFactor alpha p) s‖ ≤ Real.log (p:ℝ) := by
  have hpR : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hlog : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (by linarith)
  have hu : ‖alpha*(p:ℂ)^(-s)‖ ≤ 1/2 := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right ha (norm_nonneg _)).trans (by simpa using prime_cpow_neg_norm_le_half hp hs)
  have hden : ‖alpha*(p:ℂ)^(-s)‖ ≤ ‖localEulerFactor alpha p s‖ := by
    have h := norm_sub_norm_le (1:ℂ) (alpha*(p:ℂ)^(-s))
    rw [norm_one] at h
    change 1-‖alpha*(p:ℂ)^(-s)‖ ≤ ‖localEulerFactor alpha p s‖ at h
    linarith
  rw [logDeriv_apply, localEulerFactor_deriv hp, norm_div, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
  exact (div_le_iff₀ (norm_pos_iff.mpr (localEulerFactor_ne_zero hp ha hs))).mpr
    (mul_le_mul_of_nonneg_left hden hlog)

lemma sum_log_primeFactors_le_log (q : ℕ) [NeZero q] :
    ∑ p ∈ q.primeFactors, Real.log (p:ℝ) ≤ Real.log (q:ℝ) := by
  have hpos : 0 < ∏ p ∈ q.primeFactors, (p:ℝ) :=
    Finset.prod_pos (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
  rw [← Real.log_prod (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)]
  apply Real.log_le_log hpos
  have h : (((∏ p ∈ q.primeFactors, p : ℕ):ℕ):ℝ) ≤ (q:ℝ) := by
    exact_mod_cast Nat.le_of_dvd (NeZero.pos q) (Nat.prod_primeFactors_dvd q)
  simpa only [Nat.cast_prod] using! h

theorem norm_euler_log_correction_le_log (q : ℕ) [NeZero q] (S : Finset ℕ)
    (hS : S ⊆ q.primeFactors) (alpha : ℕ → ℂ) (ha : ∀ p ∈ S, ‖alpha p‖ ≤ 1)
    {s : ℂ} (hs : 1 ≤ s.re) :
    ‖∑ p ∈ S, logDeriv (localEulerFactor (alpha p) p) s‖ ≤ Real.log (q:ℝ) := by
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun p hp => norm_logDeriv_localEulerFactor
    (Nat.prime_of_mem_primeFactors (hS hp)) (ha p hp) hs)).trans
  apply (Finset.sum_le_sum_of_subset_of_nonneg hS (fun p hp _ =>
    Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le))).trans
  exact sum_log_primeFactors_le_log q

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology BigOperators

lemma principal_log_derivative_eq (q : ℕ) [NeZero q] {s : ℂ} (hs : 1 < s.re) :
    logDeriv (DirichletCharacter.LFunctionTrivChar q) s = logDeriv riemannZeta s +
      ∑ p ∈ q.primeFactors, logDeriv (localEulerFactor 1 p) s := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have he : DirichletCharacter.LFunctionTrivChar q =ᶠ[𝓝 s]
      (fun z => modulusEulerProduct q z * riemannZeta z) := by
    filter_upwards [isOpen_ne.mem_nhds hs1] with z hz
    simpa only [modulusEulerProduct, localEulerFactor, one_mul] using
      (DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := q) hz)
  have hf (p:ℕ) (hp : p ∈ q.primeFactors) : localEulerFactor 1 p s ≠ 0 :=
    localEulerFactor_ne_zero (Nat.prime_of_mem_primeFactors hp) (by simp) hs.le
  have hd (p:ℕ) (hp : p ∈ q.primeFactors) : DifferentiableAt ℂ (localEulerFactor 1 p) s :=
    (localEulerFactor_differentiable (Nat.prime_of_mem_primeFactors hp) 1).differentiableAt
  have hprod : modulusEulerProduct q s ≠ 0 := Finset.prod_ne_zero_iff.mpr hf
  have hdiff : DifferentiableAt ℂ (modulusEulerProduct q) s := DifferentiableAt.fun_finsetProd hd
  have hld : logDeriv (DirichletCharacter.LFunctionTrivChar q) s =
      logDeriv (fun z => modulusEulerProduct q z * riemannZeta z) s := by
    simp only [logDeriv_apply, he.deriv_eq, he.eq_of_nhds]
  rw [hld, logDeriv_mul s hprod (riemannZeta_ne_zero_of_one_le_re hs.le) hdiff
    (differentiableAt_riemannZeta hs1)]
  have hsum : logDeriv (modulusEulerProduct q) s =
      ∑ p ∈ q.primeFactors, logDeriv (localEulerFactor 1 p) s := logDeriv_prod hf hd
  rw [hsum, add_comm]

theorem norm_principal_log_derivative_difference (q : ℕ) [NeZero q]
    {s : ℂ} (hs : 1 < s.re) :
    ‖logDeriv (DirichletCharacter.LFunctionTrivChar q) s - logDeriv riemannZeta s‖ ≤
      Real.log (q:ℝ) := by
  rw [principal_log_derivative_eq q hs, add_sub_cancel_left]
  exact norm_euler_log_correction_le_log q q.primeFactors (Finset.Subset.refl _)
    (fun _ => 1) (by intro p hp; simp) hs.le

theorem principal_neg_real_log_derivative_le (q : ℕ) [NeZero q]
    {s : ℂ} (hs : 1 < s.re) :
    (-logDeriv (DirichletCharacter.LFunctionTrivChar q) s).re ≤
      (-logDeriv riemannZeta s).re + Real.log (q:ℝ) := by
  have h := (Complex.re_le_norm (-(logDeriv (DirichletCharacter.LFunctionTrivChar q) s -
    logDeriv riemannZeta s))).trans
    (by simpa only [norm_neg] using norm_principal_log_derivative_difference q hs)
  simp only [Complex.neg_re, Complex.sub_re] at h ⊢
  linarith

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_ZetaPoleBounds
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
open _root_.Set _root_.Complex

lemma neg_logDeriv_zeta_pole_split {s : ℂ} (hs : 1 < s.re) :
    -logDeriv riemannZeta s = -logDeriv regularZeta s + 1/(s-1) := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hz := riemannZeta_ne_zero_of_one_le_re hs.le
  simp only [logDeriv_apply, regularZeta]
  rw [DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one 1 hs1]
  simp only [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs1,
    DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunction_modOne_eq]
  field_simp
  ring

theorem exists_regular_zeta_compact_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 ≤ s.re → s.re ≤ 2 → |s.im| ≤ 6 →
      ‖logDeriv regularZeta s‖ ≤ C := by
  let K : Set ℂ := Icc (1:ℝ) 2 ×ℂ Icc (-6:ℝ) 6
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hc : ContinuousOn (fun s => -deriv regularZeta s / regularZeta s) K := by
    apply (DirichletCharacter.continuousOn_neg_logDeriv_LFunctionTrivChar₁ 1).mono
    intro s hs
    right
    have hr : 1 ≤ s.re := ((Complex.mem_reProdIm.mp hs).1).1
    simpa only [DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunction_modOne_eq] using
      riemannZeta_ne_zero_of_one_le_re hr
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro s hs hs2 ht
  have hm : s ∈ K := ⟨⟨hs,hs2⟩,abs_le.mp ht⟩
  have h := (hC s hm).trans (le_max_right (1:ℝ) C)
  simpa only [logDeriv_apply, neg_div, norm_neg] using h

theorem exists_zeta_small_height_real_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 < s.re → s.re ≤ 2 → |s.im| ≤ 6 →
      (-logDeriv riemannZeta s).re ≤ C+(1/(s-1)).re := by
  obtain ⟨C,hC,hbound⟩ := exists_regular_zeta_compact_bound
  refine ⟨C,hC,?_⟩
  intro s hs hs2 ht
  rw [neg_logDeriv_zeta_pole_split hs, Complex.add_re]
  have h := (Complex.re_le_norm (-logDeriv regularZeta s)).trans
    (by simpa only [norm_neg] using hbound s hs.le hs2 ht)
  linarith

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_PrimitiveTransfer
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace Erdos970Dependency.SiegelWalfisz





lemma zetaPole_real_nonneg {s : ℂ} (hs : 1 ≤ s.re) : 0 ≤ (1/(s-1)).re := by
  simpa using real_zero_term_nonneg (w := s) (rho := (1:ℂ)) 1 (by simpa using hs)

lemma zetaPole_real_eq (s : ℂ) :
    (1/(s-1)).re = (s.re-1)/((s.re-1)^2+s.im^2) := by
  rw [one_div, Complex.inv_re, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero, pow_two]

theorem exists_zeta_all_height_real_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (s : ℂ),
      1 < s.re → s.re ≤ 2 →
      (-logDeriv riemannZeta s).re ≤ C*(modulusHeight q s.im)^2+(1/(s-1)).re := by
  obtain ⟨C0,hC0,hsmall⟩ := exists_zeta_small_height_real_bound
  obtain ⟨A,hA,C1,hC1,hlarge⟩ := _root_.Erdos970.LogDerivZetaBndUnif2
  refine ⟨C0+C1+1, by positivity, ?_⟩
  intro q _ s hs hs2
  have hH := modulusHeight_ge_one q s.im
  have hHsq : 1 ≤ (modulusHeight q s.im)^2 := by nlinarith
  by_cases ht : |s.im| ≤ 6
  · have h := hsmall s hs hs2 ht
    have hlift := mul_le_mul_of_nonneg_left hHsq (show 0 ≤ C0+C1+1 by positivity)
    have hbound : C0 ≤ (C0+C1+1)*(modulusHeight q s.im)^2 := by nlinarith only [hlift,hC1]
    linarith
  · have ht6 : 6 < |s.im| := lt_of_not_ge ht
    have ht3 : 3 < |s.im| := by linarith
    have hlog : 0 < Real.log |s.im| := Real.log_pos (by linarith)
    have hr : 0 ≤ A/Real.log |s.im| := div_nonneg hA.1.le hlog.le
    have hstrip : s.re ∈ Set.Ici (1-A/(Real.log |s.im|)^1) := by
      change 1-A/(Real.log |s.im|)^1 ≤ s.re
      rw [pow_one]
      linarith
    have hz := hlarge s.re s.im ht3 hstrip
    have hnorm : ‖logDeriv riemannZeta s‖ ≤ C1*(Real.log |s.im|)^2 := by
      simpa only [logDeriv_apply, Complex.re_add_im] using hz
    have hq : (1:ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    have hlq := Real.log_nonneg hq
    have hlogle : Real.log |s.im| ≤ modulusHeight q s.im := by
      have h := Real.log_le_log (by linarith : 0 < |s.im|) (by linarith : |s.im| ≤ |s.im|+6)
      unfold modulusHeight
      linarith
    have hsq : (Real.log |s.im|)^2 ≤ (modulusHeight q s.im)^2 := by nlinarith
    have hreal := (Complex.re_le_norm (-logDeriv riemannZeta s)).trans
      (by simpa only [norm_neg] using hnorm)
    have hmul := mul_le_mul_of_nonneg_left hsq hC1.le
    have hpole := zetaPole_real_nonneg hs.le
    have hlift : C1*(modulusHeight q s.im)^2 ≤ (C0+C1+1)*(modulusHeight q s.im)^2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    linarith only [hreal, hmul, hlift, hpole]

theorem exists_principal_all_height_real_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (s : ℂ),
      1 < s.re → s.re ≤ 2 →
      (-logDeriv (DirichletCharacter.LFunctionTrivChar q) s).re ≤
        C*(modulusHeight q s.im)^2+(1/(s-1)).re := by
  obtain ⟨C,hC,hzeta⟩ := exists_zeta_all_height_real_bound
  refine ⟨C+1, by positivity, ?_⟩
  intro q _ s hs hs2
  have h := principal_neg_real_log_derivative_le q hs
  have hz := hzeta q s hs hs2
  have hH := modulusHeight_ge_one q s.im
  have hlog : Real.log (q:ℝ) ≤ modulusHeight q s.im := by
    have hh : 0 ≤ Real.log (|s.im|+6) := Real.log_nonneg (by have := abs_nonneg s.im; linarith)
    unfold modulusHeight
    linarith
  nlinarith only [h, hz, hH, hlog]





lemma real_pole_bound_away_from_zero (q : ℕ) [NeZero q] (hq : 3 ≤ q)
    {c sigma t : ℝ} (hc : 0 < c) (hs : 1 < sigma) (hs2 : sigma ≤ 2)
    (ht : c/(2*Real.log (q:ℝ)) ≤ |t|) :
    (1/(((sigma:ℂ)+(2*t:ℝ)*Complex.I)-1)).re ≤
      (1/c^2)*(modulusHeight q t)^2 := by
  have hqR : (3:ℝ) ≤ q := by exact_mod_cast hq
  have hL : 0 < Real.log (q:ℝ) := Real.log_pos (by linarith)
  have htpos : 0 < |t| := (div_pos hc (by positivity)).trans_le ht
  have htne : t ≠ 0 := abs_pos.mp htpos
  have htsq : 0 < 4*t^2 := by positivity
  have hc2 : 0 < c^2 := by positivity
  have hct : c ≤ 2*Real.log (q:ℝ)*|t| := by
    have h := (div_le_iff₀ (show 0 < 2*Real.log (q:ℝ) by positivity)).mp ht
    nlinarith only [h]
  have hcSq : c^2 ≤ 4*(Real.log (q:ℝ))^2*t^2 := by
    have h : c^2 ≤ (2*Real.log (q:ℝ)*|t|)^2 := by gcongr
    norm_num only [mul_pow, sq_abs] at h
    exact h
  have hp : Real.log (q:ℝ) ≤ modulusHeight q t := by
    have hh : 0 ≤ Real.log (|t|+6) := Real.log_nonneg (by have := abs_nonneg t; linarith)
    unfold modulusHeight
    linarith
  have hsq : (Real.log (q:ℝ))^2 ≤ (modulusHeight q t)^2 := by gcongr
  rw [zetaPole_real_eq]
  have hr : ((sigma:ℂ)+(2*t:ℝ)*Complex.I).re = sigma := by simp
  have hi : ((sigma:ℂ)+(2*t:ℝ)*Complex.I).im = 2*t := by simp
  rw [hr, hi]
  calc
    _ ≤ 1/(4*t^2) := by
      apply (div_le_div_iff₀ (by positivity : 0 < (sigma-1)^2+(2*t)^2) htsq).mpr
      have h := mul_le_mul_of_nonneg_right (show sigma-1 ≤ 1 by linarith) (sq_nonneg (2*t))
      nlinarith only [h, sq_nonneg (sigma-1)]
    _ ≤ (Real.log (q:ℝ))^2/c^2 := (div_le_div_iff₀ htsq hc2).mpr (by nlinarith only [hcSq])
    _ ≤ (modulusHeight q t)^2/c^2 := div_le_div_of_nonneg_right hsq hc2.le
    _ = _ := by ring

theorem exists_quadratic_zero_reciprocal_bound (c : ℝ) (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ (chi : DirichletCharacter ℂ q), chi ≠ 1 → chi^2 = 1 →
      ∀ sigma beta t : ℝ, 1 < sigma → sigma ≤ 2 → 3/4 ≤ beta → beta < 1 →
      c/(2*Real.log (q:ℝ)) ≤ |t| →
      DirichletCharacter.LFunction chi ((beta:ℂ)+(t:ℂ)*Complex.I) = 0 →
      4/(sigma-beta) ≤ 3/(sigma-1)+K*(modulusHeight q t)^2 := by
  obtain ⟨Cp,hCp,hpen⟩ := uniform_zero_penalty
  obtain ⟨Cu,hCu,hprincipal⟩ := exists_principal_all_height_real_bound
  obtain ⟨Cz,hCz,hzeta⟩ := _root_.Erdos970.strongPnt_triv_bound_zeta
  refine ⟨3*Cz+4*Cp+4*Cu+1/c^2, by positivity, ?_⟩
  intro q _ hq chi hchi hsq sigma beta t hs hs2 hb34 hb1 ht hzero
  have hH := modulusHeight_ge_one q t
  have hHsq : modulusHeight q t ≤ (modulusHeight q t)^2 := by nlinarith
  have hOne : 1 ≤ (modulusHeight q t)^2 := by nlinarith
  have h1 := hpen q chi hchi sigma beta t hs hs2 hb34 hb1 hzero
  have h1' : (-deriv (DirichletCharacter.LFunction chi) ((sigma:ℂ)+(t:ℂ)*Complex.I) /
      DirichletCharacter.LFunction chi ((sigma:ℂ)+(t:ℂ)*Complex.I)).re ≤
      Cp*(modulusHeight q t)^2-1/(sigma-beta) := by
    have hm := mul_le_mul_of_nonneg_left hHsq hCp.le
    change _ ≤ Cp*modulusHeight q t-1/(sigma-beta) at h1
    linarith only [h1,hm]
  have h2 := hprincipal q ((sigma:ℂ)+(2*t:ℝ)*Complex.I) (by simpa using hs) (by simpa using hs2)
  have h2H : (modulusHeight q (2*t))^2 ≤ 4*(modulusHeight q t)^2 := by
    have hh := modulusHeight_double_le q t
    have hH2 := modulusHeight_ge_one q (2*t)
    nlinarith
  have hp := real_pole_bound_away_from_zero q hq hc hs hs2 ht
  have h2' : (-deriv (DirichletCharacter.LFunction (1:DirichletCharacter ℂ q))
      ((sigma:ℂ)+(2*t:ℝ)*Complex.I) /
      DirichletCharacter.LFunction (1:DirichletCharacter ℂ q) ((sigma:ℂ)+(2*t:ℝ)*Complex.I)).re ≤
      (4*Cu+1/c^2)*(modulusHeight q t)^2 := by
    simp only [show ((sigma:ℂ)+(2*t:ℝ)*Complex.I).im = 2*t by simp,
      DirichletCharacter.LFunctionTrivChar, logDeriv_apply, ← neg_div] at h2
    have hm := mul_le_mul_of_nonneg_left h2H hCu.le
    nlinarith only [h2,hp,hm]
  have hz := hzeta sigma 0 hs
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hz
  have hz' := (Complex.re_le_norm (-deriv riemannZeta (sigma:ℂ)/riemannZeta (sigma:ℂ))).trans hz
  have hCz' : Cz ≤ Cz*(modulusHeight q t)^2 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hOne hCz
  have hpos := character_log_derivative_positivity chi sigma t hs
  rw [hsq] at hpos
  rw [one_div] at h1' h2'
  simp only [div_eq_mul_inv]
  nlinarith only [hpos,h1',h2',hz',hCz']





theorem exists_primitive_quadratic_zero_free_region :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ (chi : DirichletCharacter ℂ q), chi.IsPrimitive → chi ≠ 1 → chi^2 = 1 →
      ∀ s : ℂ, 1-c/(modulusHeight q s.im)^2 ≤ s.re →
        DirichletCharacter.LFunction chi s ≠ 0 := by
  obtain ⟨cd,hcd,hdisk⟩ := exists_primitive_real_zero_free_disk_jb247
  obtain ⟨K,hK,hineq⟩ := exists_quadratic_zero_reciprocal_bound cd hcd
  let delta : ℝ := 1/(8*(K+1))
  have hd : 0 < delta := by dsimp [delta] <;> positivity
  have hd8 : delta ≤ 1/8 := by
    apply (div_le_iff₀ (by positivity : 0 < 8*(K+1))).mpr
    nlinarith
  have hKd : K*delta ≤ 1/8 := by
    dsimp only [delta]
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity : 0 < 8*(K+1))).mpr
    nlinarith
  let c : ℝ := min (delta/4) (cd/4)
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  have hcδ : c ≤ delta/4 := min_le_left _ _
  have hcc : c ≤ cd/2 := by have h := min_le_right (delta/4) (cd/4); change c ≤ cd/4 at h; linarith
  refine ⟨c,hc,?_⟩
  intro q _ hq chi hprim hchi hsq s hs hzero
  have hb1 : s.re < 1 := by
    by_contra! h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re chi (Or.inl hchi) h hzero
  let H : ℝ := (modulusHeight q s.im)^2
  have hbase := modulusHeight_ge_one q s.im
  have hH : 1 ≤ H := by dsimp only [H] <;> nlinarith
  have hHp : 0 < H := by linarith
  let x : ℝ := delta/H
  have hxp : 0 < x := by dsimp only [x] <;> positivity
  have hxd : x ≤ delta := by
    apply (div_le_iff₀ hHp).mpr
    nlinarith
  have hclose : 1-s.re ≤ x/4 := by
    have h : c/H ≤ (delta/4)/H := div_le_div_of_nonneg_right hcδ hHp.le
    have he : (delta/4)/H = x/4 := by dsimp only [x] <;> ring
    rw [he] at h
    change 1-c/H ≤ s.re at hs
    linarith
  have hb34 : 3/4 ≤ s.re := by linarith
  have hsigma : 1 < 1+x := by linarith
  have hsigma2 : 1+x ≤ 2 := by linarith
  have hz : DirichletCharacter.LFunction chi ((s.re:ℂ)+(s.im:ℂ)*Complex.I) = 0 := by
    simpa only [Complex.re_add_im] using hzero
  have hheight : cd/(2*Real.log (q:ℝ)) ≤ |s.im| := by
    by_contra! hlow
    have hqR : (3:ℝ) ≤ q := by exact_mod_cast hq
    have hL : 0 < Real.log (q:ℝ) := Real.log_pos (by linarith)
    have hLH : Real.log (q:ℝ) ≤ H := by
      have ht : 0 ≤ Real.log (|s.im|+6) := Real.log_nonneg (by have := abs_nonneg s.im; linarith)
      have hle : Real.log (q:ℝ) ≤ modulusHeight q s.im := by unfold modulusHeight; linarith
      dsimp only [H]
      nlinarith
    have hbeta : 1-s.re ≤ cd/(2*Real.log (q:ℝ)) := by
      calc
        _ ≤ c/H := by change 1-c/H ≤ s.re at hs; linarith
        _ ≤ c/Real.log (q:ℝ) := div_le_div_of_nonneg_left hc.le hL hLH
        _ ≤ (cd/2)/Real.log (q:ℝ) := div_le_div_of_nonneg_right hcc hL.le
        _ = _ := by ring
    have hnorm : ‖s-1‖ ≤ cd/Real.log (q:ℝ) := by
      have h := Complex.norm_le_abs_re_add_abs_im (s-1)
      simp only [Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,sub_zero] at h
      rw [abs_of_neg (by linarith : s.re-1 < 0)] at h
      have he : 2*(cd/(2*Real.log (q:ℝ))) = cd/Real.log (q:ℝ) := by ring
      linarith
    have hreal : ∀ a : ZMod q, (chi a).im = 0 :=
      (RealCharacterAnalysis.real_values_iff_quadratic chi).mpr
        (MulChar.isQuadratic_iff_sq_eq_one.mpr hsq)
    exact hdisk q hq chi hprim hchi hreal s hnorm hzero
  have hr := hineq q hq chi hchi hsq (1+x) s.re s.im hsigma hsigma2 hb34 hb1 hheight hz
  let y : ℝ := 1+x-s.re
  have hyp : 0 < y := by dsimp only [y] <;> linarith
  have hy : y ≤ (5/4)*x := by dsimp only [y] <;> linarith
  have hKx : K*H*x ≤ 1/8 := by
    have he : K*H*x = K*delta := by dsimp only [x]; field_simp
    rw [he]
    exact hKd
  change 4/y ≤ 3/(1+x-1)+K*H at hr
  rw [add_sub_cancel_left] at hr
  have h := mul_le_mul_of_nonneg_right ((div_le_iff₀ hyp).mp hr) hxp.le
  have he : (3/x+K*H)*y*x = 3*y+K*H*x*y := by field_simp
  rw [he] at h
  have hKy := mul_le_mul_of_nonneg_right hKx hyp.le
  nlinarith only [h,hKy,hy,hxp]





theorem exists_primitive_zero_free_region :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ (chi : DirichletCharacter ℂ q), chi.IsPrimitive → chi ≠ 1 →
      ∀ s : ℂ, 1-c/(modulusHeight q s.im)^2 ≤ s.re →
        DirichletCharacter.LFunction chi s ≠ 0 := by
  obtain ⟨cn,hcn,hnonquad⟩ := exists_nonquadratic_zero_free_region
  obtain ⟨cq,hcq,hquad⟩ := exists_primitive_quadratic_zero_free_region
  refine ⟨min cn cq,lt_min hcn hcq,?_⟩
  intro q _ hq chi hprim hchi s hs
  have hH := modulusHeight_ge_one q s.im
  have hHp : 0 < modulusHeight q s.im := by linarith
  by_cases hsq : chi^2 = 1
  · apply hquad q hq chi hprim hchi hsq s
    have h := div_le_div_of_nonneg_right (min_le_right cn cq)
      (sq_nonneg (modulusHeight q s.im))
    linarith
  · apply hnonquad q chi hsq s
    have h1 : min cn cq/(modulusHeight q s.im)^2 ≤ min cn cq/modulusHeight q s.im :=
      div_le_div_of_nonneg_left (lt_min hcn hcq).le hHp (by nlinarith)
    have h2 : min cn cq/modulusHeight q s.im ≤ cn/modulusHeight q s.im :=
      div_le_div_of_nonneg_right (min_le_left cn cq) hHp.le
    linarith




open scoped BigOperators

lemma character_mod_two_eq_one (chi : DirichletCharacter ℂ 2) : chi = 1 := by
  apply MulChar.ext'
  intro a
  have ha : a = 0 ∨ a = 1 := by
    fin_cases a
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases ha with rfl | rfl
  · rw [chi.map_zero, (1 : DirichletCharacter ℂ 2).map_zero]
  · rw [chi.map_one, (1 : DirichletCharacter ℂ 2).map_one]

lemma primitiveCharacter_ne_one {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) : chi.primitiveCharacter ≠ 1 := by
  intro h
  apply hchi
  calc
    chi = DirichletCharacter.changeLevel chi.conductor_dvd_level chi.primitiveCharacter :=
      chi.changeLevel_primitiveCharacter.symm
    _ = 1 := by rw [h, DirichletCharacter.changeLevel_one]

lemma conductor_ge_three {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) : 3 ≤ chi.conductor := by
  have h0 := chi.conductor_ne_zero
  have h1 : chi.conductor ≠ 1 := fun h => hchi (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h)
  have h2 : chi.conductor ≠ 2 := by
    intro h
    have haux : ∀ n : ℕ, n=2 → ∀ psi : DirichletCharacter ℂ n, psi=1 := by
      intro n hn psi
      subst n
      exact character_mod_two_eq_one psi
    exact primitiveCharacter_ne_one chi hchi (haux _ h chi.primitiveCharacter)
  omega

lemma localEulerFactor_ne_zero_of_re_pos {p : ℕ} (hp : p.Prime) {alpha s : ℂ}
    (ha : ‖alpha‖ ≤ 1) (hs : 0 < s.re) : localEulerFactor alpha p s ≠ 0 := by
  have hpR : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have hpow : ‖(p:ℂ)^(-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
    calc
      _ < (p:ℝ)^(0:ℝ) := Real.rpow_lt_rpow_of_exponent_lt hpR (by linarith)
      _ = _ := Real.rpow_zero _
  have hu : ‖alpha*(p:ℂ)^(-s)‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right ha (norm_nonneg _)).trans_lt (by simpa using hpow)
  intro hz
  have he : alpha*(p:ℂ)^(-s) = 1 := (sub_eq_zero.mp hz).symm
  rw [he,norm_one] at hu
  exact (lt_irrefl 1) hu

lemma LFunction_changeLevel_ne_zero_iff {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) (chi : DirichletCharacter ℂ M) (hchi : chi ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunction (DirichletCharacter.changeLevel hMN chi) s ≠ 0 ↔
      DirichletCharacter.LFunction chi s ≠ 0 := by
  rw [DirichletCharacter.LFunction_changeLevel hMN chi (Or.inl hchi), mul_ne_zero_iff]
  have hp : (∏ p ∈ N.primeFactors, (1-chi p*(p:ℂ)^(-s))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact localEulerFactor_ne_zero_of_re_pos (Nat.prime_of_mem_primeFactors hp)
      (chi.norm_le_one p) hs
  exact and_iff_left hp

lemma LFunction_primitive_ne_zero_iff {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    let _ : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
    DirichletCharacter.LFunction chi s ≠ 0 ↔
      DirichletCharacter.LFunction chi.primitiveCharacter s ≠ 0 := by
  let _ : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have h := LFunction_changeLevel_ne_zero_iff chi.conductor_dvd_level chi.primitiveCharacter
    (primitiveCharacter_ne_one chi hchi) hs
  rwa [chi.changeLevel_primitiveCharacter] at h

end Erdos970Dependency.SiegelWalfisz


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_DirichletZeroFree
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

lemma modulusHeight_mono {m q : ℕ} [NeZero m] [NeZero q] (hmq : m ≤ q) (t : ℝ) :
    modulusHeight m t ≤ modulusHeight q t := by
  have h : Real.log (m:ℝ) ≤ Real.log (q:ℝ) :=
    Real.log_le_log (by exact_mod_cast NeZero.pos m) (by exact_mod_cast hmq)
  unfold modulusHeight
  linarith

theorem exists_nonprincipal_zero_free_region :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
      chi ≠ 1 → ∀ s : ℂ, 1-c/(modulusHeight q s.im)^2 ≤ s.re →
        DirichletCharacter.LFunction chi s ≠ 0 := by
  obtain ⟨cp,hcp,hprimitive⟩ := exists_primitive_zero_free_region
  let c : ℝ := min cp (1/4)
  have hc : 0 < c := lt_min hcp (by norm_num)
  have hcc : c ≤ cp := min_le_left _ _
  have hc4 : c ≤ 1/4 := min_le_right _ _
  refine ⟨c,hc,?_⟩
  intro q _ chi hchi s hs
  let _ : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hH := modulusHeight_ge_one q s.im
  have hHsq : 1 ≤ (modulusHeight q s.im)^2 := by nlinarith
  have hfrac : c/(modulusHeight q s.im)^2 ≤ c := by
    apply (div_le_iff₀ (by positivity : 0 < (modulusHeight q s.im)^2)).mpr
    nlinarith
  have hrep : 0 < s.re := by linarith
  apply (LFunction_primitive_ne_zero_iff chi hchi hrep).mpr
  have hcond : chi.conductor ≤ q := Nat.le_of_dvd (NeZero.pos q) chi.conductor_dvd_level
  have hHm := modulusHeight_ge_one chi.conductor s.im
  have hmono := modulusHeight_mono hcond s.im
  have hpow : (modulusHeight chi.conductor s.im)^2 ≤ (modulusHeight q s.im)^2 := by nlinarith
  have hfrac' : c/(modulusHeight q s.im)^2 ≤ cp/(modulusHeight chi.conductor s.im)^2 := by
    calc
      _ ≤ cp/(modulusHeight q s.im)^2 := div_le_div_of_nonneg_right hcc (sq_nonneg _)
      _ ≤ _ := div_le_div_of_nonneg_left hcp.le (by positivity) hpow
  apply hprimitive chi.conductor (conductor_ge_three chi hchi) chi.primitiveCharacter
    chi.primitiveCharacter_isPrimitive (primitiveCharacter_ne_one chi hchi) s
  linarith

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_LocalZeroMass
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

theorem uniform_normalized_zero_mass :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
      chi ≠ 1 → ∀ (t : ℝ) (S : Finset ℂ),
      (∀ rho, rho ∈ S ↔ ‖rho‖ ≤ 19/20 ∧ normalizedDirichlet chi t rho = 0) →
      ∑ rho ∈ S, ((analyticOrderAt (normalizedDirichlet chi t) rho).toNat:ℝ) ≤
        C*modulusHeight q t := by
  classical
  let D : ℝ := Real.log ((39/40:ℝ)/(19/20))
  have hD : 0 < D := Real.log_pos (by norm_num)
  have hZ := one_le_absoluteZetaTwo
  have hlog : 0 ≤ Real.log (4*absoluteZetaTwo) := Real.log_nonneg (by linarith)
  refine ⟨(Real.log (4*absoluteZetaTwo)+1)/D, div_pos (by linarith) hD, ?_⟩
  intro q _ chi hchi t S hS
  let f := normalizedDirichlet chi t
  have he : _root_.Erdos970.zerosetKfR (19/20) (by norm_num) f = (S:Set ℂ) := by
    ext rho
    simp only [_root_.Erdos970.zerosetKfR,Set.mem_ofPred_eq,Metric.mem_closedBall,dist_zero_right,Finset.mem_coe]
    exact (hS rho).symm
  have hf : (_root_.Erdos970.zerosetKfR (19/20) (by norm_num) f).Finite := by rw [he]; exact S.finite_toSet
  have hfin : hf.toFinset = S := by
    ext rho
    rw [Set.Finite.mem_toFinset,he]
    rfl
  have h0 : f 0 = 1 := normalizedDirichlet_zero chi t
  have hn : f 0 ≠ 0 := by rw [h0]; norm_num
  have hj := _root_.Erdos970.jensen_sum_bound_strict (dirichletDiskEnvelope q t) (39/40) (19/20)
    (dirichletDiskEnvelope_gt_one q t) (by norm_num) (by norm_num) (by norm_num)
    f (fun w _ => normalizedDirichlet_analytic chi hchi t w) hn h0 hf
    (fun w hw => normalizedDirichlet_bound chi hchi t (hw.trans (by norm_num)))
  rw [hfin] at hj
  calc
    _ ≤ Real.log (dirichletDiskEnvelope q t)/D := hj
    _ ≤ ((Real.log (4*absoluteZetaTwo)+1)*modulusHeight q t)/D :=
      div_le_div_of_nonneg_right (log_dirichletDiskEnvelope_bound q t) hD.le
    _ = _ := by ring

theorem uniform_local_zero_estimates :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
      chi ≠ 1 → ∀ t : ℝ, ∃ S : Finset ℂ,
        (∀ rho, rho ∈ S ↔ ‖rho‖ ≤ 19/20 ∧
          DirichletCharacter.LFunction chi (dirichletDiskPoint t rho) = 0) ∧
        (∑ rho ∈ S, ((analyticOrderAt (normalizedDirichlet chi t) rho).toNat:ℝ) ≤ C*modulusHeight q t) ∧
        ∀ w : ℂ, ‖w‖ ≤ 17/20 →
          DirichletCharacter.LFunction chi (dirichletDiskPoint t w) ≠ 0 →
          ‖(5/2:ℂ)*(deriv (DirichletCharacter.LFunction chi) (dirichletDiskPoint t w) /
            DirichletCharacter.LFunction chi (dirichletDiskPoint t w)) -
            ∑ rho ∈ S, (analyticOrderAt (normalizedDirichlet chi t) rho).toNat/(w-rho)‖ ≤
            C*modulusHeight q t := by
  classical
  obtain ⟨C0,hC0,hlocal⟩ := uniform_dirichlet_local_log_derivative
  obtain ⟨C1,hC1,hmass⟩ := uniform_normalized_zero_mass
  refine ⟨max C0 C1,lt_of_lt_of_le hC0 (le_max_left _ _),?_⟩
  intro q _ chi hchi t
  obtain ⟨S,hS,_,hb⟩ := hlocal q chi hchi t
  have hn := LFunction_ne_zero_right chi (s := dirichletCenter t) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hzeros (rho:ℂ) : normalizedDirichlet chi t rho = 0 ↔
      DirichletCharacter.LFunction chi (dirichletDiskPoint t rho) = 0 := by
    unfold normalizedDirichlet
    exact div_eq_zero_iff.trans (or_iff_left hn)
  have hSn : ∀ rho, rho ∈ S ↔ ‖rho‖ ≤ 19/20 ∧ normalizedDirichlet chi t rho = 0 := by
    intro rho
    rw [hzeros]
    exact hS rho
  have hH : 0 ≤ modulusHeight q t := zero_le_one.trans (modulusHeight_ge_one q t)
  refine ⟨S,hS,?_,?_⟩
  · exact (hmass q chi hchi t S hSn).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hH)
  · intro w hw hne
    exact (hb w hw hne).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hH)

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

lemma modulusHeight_diskPoint_le (q : ℕ) [NeZero q] (t : ℝ) {rho : ℂ}
    (hr : ‖rho‖ ≤ 19/20) :
    modulusHeight q (dirichletDiskPoint t rho).im ≤ 2*modulusHeight q t := by
  have hri : |rho.im| ≤ 19/20 := (Complex.abs_im_le_norm rho).trans hr
  have hi : (dirichletDiskPoint t rho).im = t+(5/2:ℝ)*rho.im := by
    simp [dirichletDiskPoint,dirichletCenter]
  have hdis : |(dirichletDiskPoint t rho).im| ≤ |t|+3 := by
    rw [hi]
    have h := abs_add_le t ((5/2:ℝ)*rho.im)
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 5/2)] at h
    linarith
  have ht := abs_nonneg t
  have hq : (1:ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlq := Real.log_nonneg hq
  have hl2 : Real.log 2 ≤ Real.log (|t|+6) := Real.log_le_log (by norm_num) (by linarith)
  have hl : Real.log (|(dirichletDiskPoint t rho).im|+6) ≤ Real.log (2*(|t|+6)) :=
    Real.log_le_log (by positivity) (by linarith)
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by positivity : |t|+6 ≠ 0)] at hl
  unfold modulusHeight
  linarith

theorem exists_uniform_zero_separation :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1/100 ∧ ∀ (q : ℕ) [NeZero q]
      (chi : DirichletCharacter ℂ q), chi ≠ 1 → ∀ sigma t : ℝ,
      1-a/(modulusHeight q t)^2 ≤ sigma →
      DirichletCharacter.LFunction chi ((sigma:ℂ)+(t:ℂ)*Complex.I) ≠ 0 ∧
      ∀ rho : ℂ, ‖rho‖ ≤ 19/20 →
        DirichletCharacter.LFunction chi (dirichletDiskPoint t rho) = 0 →
        a/(modulusHeight q t)^2 ≤ ‖((2/5*(sigma-3):ℝ):ℂ)-rho‖ := by
  obtain ⟨c,hc,hregion⟩ := exists_nonprincipal_zero_free_region
  let a : ℝ := min (c/16) (1/100)
  have ha : 0 < a := lt_min (by positivity) (by norm_num)
  have hac : a ≤ c/16 := min_le_left _ _
  have ha100 : a ≤ 1/100 := min_le_right _ _
  refine ⟨a,ha,ha100,?_⟩
  intro q _ chi hchi sigma t hs
  have hH := modulusHeight_ge_one q t
  have hHp : 0 < modulusHeight q t := by linarith
  have hHsq : 0 < (modulusHeight q t)^2 := by positivity
  constructor
  · apply hregion q chi hchi ((sigma:ℂ)+(t:ℂ)*Complex.I)
    simp only [show ((sigma:ℂ)+(t:ℂ)*Complex.I).re = sigma by simp,
      show ((sigma:ℂ)+(t:ℂ)*Complex.I).im = t by simp]
    have hdiv := div_le_div_of_nonneg_right (show a ≤ c by linarith) hHsq.le
    linarith
  · intro rho hr hz
    have hZ := modulusHeight_ge_one q (dirichletDiskPoint t rho).im
    have hZp : 0 < modulusHeight q (dirichletDiskPoint t rho).im := by linarith
    have hheight := modulusHeight_diskPoint_le q t hr
    have hpow : (modulusHeight q (dirichletDiskPoint t rho).im)^2 ≤
        4*(modulusHeight q t)^2 := by nlinarith
    have hdrop : c/(4*(modulusHeight q t)^2) ≤
        c/(modulusHeight q (dirichletDiskPoint t rho).im)^2 :=
      div_le_div_of_nonneg_left hc.le (by positivity) hpow
    have hzeroRe : (dirichletDiskPoint t rho).re <
        1-c/(modulusHeight q (dirichletDiskPoint t rho).im)^2 := by
      by_contra! h
      exact hregion q chi hchi (dirichletDiskPoint t rho) h hz
    have ha4 : 4*(a/(modulusHeight q t)^2) ≤ c/(4*(modulusHeight q t)^2) := by
      have h := div_le_div_of_nonneg_right (show 4*a ≤ c/4 by linarith) hHsq.le
      first | (convert h using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (h.trans (le_of_eq (by ring)))
    have hdiff : (5/2:ℝ)*((((2/5*(sigma-3):ℝ):ℂ)).re-rho.re) =
        sigma-(dirichletDiskPoint t rho).re := by
      rw [Complex.ofReal_re,dirichletDiskPoint_re]
      ring
    have har : 0 ≤ a/(modulusHeight q t)^2 := div_nonneg ha.le hHsq.le
    have hsep : a/(modulusHeight q t)^2 ≤ (((2/5*(sigma-3):ℝ):ℂ)).re-rho.re := by
      nlinarith only [hs,hzeroRe,hdrop,ha4,hdiff,har]
    have hn := Complex.re_le_norm (((2/5*(sigma-3):ℝ):ℂ)-rho)
    simp only [Complex.sub_re] at hn
    exact hsep.trans hn

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz
open scoped BigOperators

theorem exists_uniform_nonprincipal_strip_bound :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1/100 ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q), chi ≠ 1 →
      ∀ sigma t : ℝ, 1-a/(modulusHeight q t)^2 ≤ sigma → sigma ≤ 2 →
        DirichletCharacter.LFunction chi ((sigma:ℂ)+(t:ℂ)*Complex.I) ≠ 0 ∧
        ‖deriv (DirichletCharacter.LFunction chi) ((sigma:ℂ)+(t:ℂ)*Complex.I) /
          DirichletCharacter.LFunction chi ((sigma:ℂ)+(t:ℂ)*Complex.I)‖ ≤
          C*(modulusHeight q t)^3 := by
  classical
  obtain ⟨a,ha,ha100,hsep⟩ := exists_uniform_zero_separation
  obtain ⟨C0,hC0,hlocal⟩ := uniform_local_zero_estimates
  refine ⟨a,ha,ha100,C0+C0/a,by positivity,?_⟩
  intro q _ chi hchi sigma t hs hs2
  obtain ⟨hne,hseparate⟩ := hsep q chi hchi sigma t hs
  refine ⟨hne,?_⟩
  obtain ⟨S,hS,hmass,hbound⟩ := hlocal q chi hchi t
  let H : ℝ := modulusHeight q t
  have hH : 1 ≤ H := modulusHeight_ge_one q t
  have hHp : 0 < H := by linarith
  have hHsq : 1 ≤ H^2 := by nlinarith
  have hH2 : 0 < H^2 := by positivity
  have hr : 0 < a/H^2 := by positivity
  have hfrac : a/H^2 ≤ a := by
    apply (div_le_iff₀ hH2).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hHsq ha.le
  let w : ℂ := ((2/5*(sigma-3):ℝ):ℂ)
  have hw : ‖w‖ ≤ 17/20 := by
    change ‖((2/5*(sigma-3):ℝ):ℂ)‖ ≤ _
    rw [Complex.norm_real,Real.norm_eq_abs]
    change 1-a/H^2 ≤ sigma at hs
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hwne : DirichletCharacter.LFunction chi (dirichletDiskPoint t w) ≠ 0 := by
    rw [dirichletDiskPoint_ofReal]
    exact hne
  let D : ℂ := deriv (DirichletCharacter.LFunction chi) (dirichletDiskPoint t w) /
    DirichletCharacter.LFunction chi (dirichletDiskPoint t w)
  let Z : ℂ := ∑ rho ∈ S, (analyticOrderAt (normalizedDirichlet chi t) rho).toNat/(w-rho)
  have hterm (rho : ℂ) (hrho : rho ∈ S) :
      ‖((analyticOrderAt (normalizedDirichlet chi t) rho).toNat:ℂ)/(w-rho)‖ ≤
        ((analyticOrderAt (normalizedDirichlet chi t) rho).toNat:ℝ)/(a/H^2) := by
    rw [norm_div,Complex.norm_natCast]
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) hr
    exact hseparate rho ((hS rho).mp hrho).1 ((hS rho).mp hrho).2
  have hZ : ‖Z‖ ≤ (C0/a)*H^3 := by
    calc
      _ ≤ ∑ rho ∈ S, ‖((analyticOrderAt (normalizedDirichlet chi t) rho).toNat:ℂ)/(w-rho)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ rho ∈ S, ((analyticOrderAt (normalizedDirichlet chi t) rho).toNat:ℝ)/(a/H^2) :=
        Finset.sum_le_sum hterm
      _ = (∑ rho ∈ S, ((analyticOrderAt (normalizedDirichlet chi t) rho).toNat:ℝ))/(a/H^2) := by
        simp only [Finset.sum_div]
      _ ≤ (C0*H)/(a/H^2) := div_le_div_of_nonneg_right hmass hr.le
      _ = _ := by field_simp
  have hb := hbound w hw hwne
  change ‖(5/2:ℂ)*D-Z‖ ≤ C0*H at hb
  have ht := norm_add_le ((5/2:ℂ)*D-Z) Z
  rw [sub_add_cancel] at ht
  have hscale : ‖(5/2:ℂ)*D‖ = (5/2:ℝ)*‖D‖ := by rw [norm_mul]; norm_num
  rw [hscale] at ht
  have hh2 : H ≤ H^2 := by nlinarith
  have hh3 := mul_le_mul_of_nonneg_left hh2 hHp.le
  have hcube : H ≤ H^3 := by nlinarith only [hh2,hh3]
  have hsmall := mul_le_mul_of_nonneg_left hcube hC0.le
  rw [show (sigma:ℂ)+(t:ℂ)*Complex.I = dirichletDiskPoint t w from (dirichletDiskPoint_ofReal sigma t).symm]
  change ‖D‖ ≤ (C0+C0/a)*H^3
  nlinarith only [ht,hb,hZ,hsmall,norm_nonneg D]

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Set _root_.Filter
open scoped Topology
attribute [local instance] Classical.propDecidable

lemma rieszProfile_eq_weight {x : ℝ} (hx : 0 < x) : rieszProfile x = (rieszWeight x:ℂ) := by
  by_cases hx1 : x ≤ 1
  · have hm : x ∈ Ioc (0:ℝ) 1 := ⟨hx,hx1⟩
    simp [rieszProfile,hm,rieszWeight,max_eq_left (sub_nonneg.mpr hx1)]
  · have hm : x ∉ Ioc (0:ℝ) 1 := fun h => hx1 h.2
    have hx1' : 1 ≤ x := le_of_lt (lt_of_not_ge hx1)
    simp [rieszProfile,hm,rieszWeight,max_eq_right (sub_nonpos.mpr hx1')]

lemma continuous_rieszWeight : Continuous rieszWeight := by unfold rieszWeight; fun_prop

lemma continuousAt_rieszProfile {x : ℝ} (hx : 0 < x) : ContinuousAt rieszProfile x := by
  have he : rieszProfile =ᶠ[𝓝 x] (fun t => (rieszWeight t:ℂ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact rieszProfile_eq_weight hy
  exact (continuousAt_congr he).mpr (Complex.continuous_ofReal.comp continuous_rieszWeight).continuousAt

theorem hasMellin_rieszProfile {s : ℂ} (hs : 0 < s.re) :
    HasMellin rieszProfile s (rieszKernel s) := by
  have h0 := hasMellin_one_Ioc hs
  have h1 := hasMellin_cpow_Ioc (1:ℂ) (s := s) (by simp only [Complex.one_re] <;> linarith)
  have h1' : HasMellin ((Ioc (0:ℝ) 1).indicator (fun t => (t:ℂ))) s (1/(s+1)) := by
    simpa only [Complex.cpow_one] using h1
  have h := hasMellin_sub h0.1 h1'.1
  rw [h0.2,h1'.2] at h
  change HasMellin rieszProfile s (1/s-1/(s+1)) at h
  have hs0 : s ≠ 0 := by intro hz; simp [hz] at hs
  have hs1 : s+1 ≠ 0 := by
    intro hz
    have he := congrArg Complex.re hz
    simp only [Complex.add_re,Complex.one_re,Complex.zero_re] at he
    linarith
  have he : 1/s-1/(s+1) = rieszKernel s := by
    unfold rieszKernel
    field_simp
    ring
  rwa [he] at h

lemma rieszWeight_eq_zero {x : ℝ} (hx : 1 ≤ x) : rieszWeight x = 0 :=
  max_eq_right (sub_nonpos.mpr hx)

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_RieszKernelBounds
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
open _root_.MeasureTheory _root_.Filter
open scoped Topology

lemma rieszKernel_norm_bound {sigma : ℝ} (hs : 1/2 ≤ sigma) (t : ℝ) :
    ‖rieszKernel ((sigma:ℂ)+(t:ℂ)*Complex.I)‖ ≤ 4/(1+t^2) := by
  let z : ℂ := (sigma:ℂ)+(t:ℂ)*Complex.I
  have hr : z.re = sigma := by simp [z]
  have hi : z.im = t := by simp [z]
  have h0 : ‖z‖^2 = sigma^2+t^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply,hr,hi]
    ring
  have h1 : ‖z+1‖^2 = (sigma+1)^2+t^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    simp only [Complex.add_re,Complex.add_im,Complex.one_re,Complex.one_im,add_zero,hr,hi]
    ring
  have hle : ‖z‖ ≤ ‖z+1‖ := by nlinarith [norm_nonneg z,norm_nonneg (z+1)]
  have hp := mul_le_mul_of_nonneg_left hle (norm_nonneg z)
  have hsig : (1/4:ℝ) ≤ sigma^2 := by nlinarith [sq_nonneg (sigma-1/2)]
  have hden : (1+t^2)/4 ≤ ‖z‖*‖z+1‖ := by nlinarith only [h0,hp,hsig,sq_nonneg t]
  have hdp : 0 < ‖z‖*‖z+1‖ := by nlinarith only [hden,sq_nonneg t]
  change ‖1/(z*(z+1))‖ ≤ _
  rw [norm_div,norm_one,norm_mul]
  apply (div_le_div_iff₀ hdp (by positivity : 0 < 1+t^2)).mpr
  nlinarith only [hden]

lemma rieszMajorant_integrable : Integrable (fun t:ℝ => 4/(1+t^2)) := by
  simpa only [div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul (4:ℝ)

lemma continuous_rieszKernel_line {sigma : ℝ} (hs : 1/2 ≤ sigma) :
    Continuous (fun t:ℝ => rieszKernel ((sigma:ℂ)+(t:ℂ)*Complex.I)) := by
  unfold rieszKernel
  apply continuous_const.div (by fun_prop)
  intro t
  apply mul_ne_zero
  · intro hz
    have h := congrArg Complex.re hz
    simp at h
    linarith
  · intro hz
    have h := congrArg Complex.re hz
    simp at h
    linarith

lemma integrable_rieszKernel_line {sigma : ℝ} (hs : 1/2 ≤ sigma) :
    Integrable (fun t:ℝ => rieszKernel ((sigma:ℂ)+(t:ℂ)*Complex.I)) := by
  apply rieszMajorant_integrable.mono' (continuous_rieszKernel_line hs).aestronglyMeasurable
  exact Filter.Eventually.of_forall (rieszKernel_norm_bound hs)

theorem riesz_mellin_inversion {sigma x : ℝ} (hs : 1/2 ≤ sigma) (hx : 0 < x) :
    mellinInv sigma rieszKernel x = (rieszWeight x:ℂ) := by
  have hsp : 0 < sigma := by linarith
  have he (t:ℝ) : mellin rieszProfile ((sigma:ℂ)+(t:ℂ)*Complex.I) =
      rieszKernel ((sigma:ℂ)+(t:ℂ)*Complex.I) :=
    (hasMellin_rieszProfile (by simpa using hsp)).2
  have hvi : Complex.VerticalIntegrable (mellin rieszProfile) sigma := by
    apply (integrable_rieszKernel_line hs).congr
    exact Filter.Eventually.of_forall (fun t => (he t).symm)
  have h := mellinInv_mellin_eq sigma rieszProfile hx (hasMellin_rieszProfile (by simpa using hsp)).1
    hvi (continuousAt_rieszProfile hx)
  rw [rieszProfile_eq_weight hx] at h
  rw [← h]
  unfold mellinInv
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by dsimp only; rw [he t])

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_RieszTermCalculus
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
open _root_.MeasureTheory _root_.Filter
open scoped Topology

lemma riesz_scale_cpow {n X : ℝ} (hn : 0 < n) (hX : 0 < X) (s : ℂ) :
    ((n/X:ℝ):ℂ)^(-s) = (X:ℂ)^s/(n:ℂ)^s := by
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hXC : (X:ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  have hrC : ((n/X:ℝ):ℂ) ≠ 0 := by exact_mod_cast (div_pos hn hX).ne'
  have hl : Complex.log ((n/X:ℝ):ℂ) = Complex.log (n:ℂ)-Complex.log (X:ℂ) := by
    rw [← Complex.ofReal_log (div_pos hn hX).le,Real.log_div hn.ne' hX.ne',
      Complex.ofReal_sub,Complex.ofReal_log hn.le,Complex.ofReal_log hX.le]
  rw [Complex.cpow_def_of_ne_zero hrC,Complex.cpow_def_of_ne_zero hXC,
    Complex.cpow_def_of_ne_zero hnC,← Complex.exp_sub,hl]
  congr 1
  ring

lemma norm_rieszDirichletTerm (f : ℕ → ℂ) (sigma : ℝ) {X : ℝ} (hX : 0 < X)
    (n : ℕ) (t : ℝ) :
    ‖rieszDirichletTerm f sigma X n t‖ =
      ‖LSeries.term f (sigma:ℂ) n‖ * X^sigma * ‖rieszKernel ((sigma:ℂ)+(t:ℂ)*Complex.I)‖ := by
  have hre : ((sigma:ℂ)+(t:ℂ)*Complex.I).re = sigma := by simp
  have ht : ‖LSeries.term f ((sigma:ℂ)+(t:ℂ)*Complex.I) n‖ = ‖LSeries.term f (sigma:ℂ) n‖ := by
    simp only [LSeries.norm_term_eq,hre,Complex.ofReal_re]
  unfold rieszDirichletTerm
  rw [norm_mul,norm_mul,ht,Complex.norm_cpow_eq_rpow_re_of_pos hX,hre]
  ring

lemma rieszDirichletTerm_eq_scaled (f : ℕ → ℂ) (hf0 : f 0 = 0) (sigma : ℝ)
    {X : ℝ} (hX : 0 < X) (n : ℕ) (t : ℝ) :
    rieszDirichletTerm f sigma X n t = f n *
      (((n:ℝ)/X:ℝ):ℂ)^(-((sigma:ℂ)+(t:ℂ)*Complex.I)) *
        rieszKernel ((sigma:ℂ)+(t:ℂ)*Complex.I) := by
  by_cases hn : n=0
  · simp [rieszDirichletTerm,hn,hf0]
  · unfold rieszDirichletTerm
    rw [LSeries.term_of_ne_zero hn,riesz_scale_cpow (by exact_mod_cast Nat.pos_of_ne_zero hn) hX]
    simp only [div_eq_mul_inv]
    push_cast
    ring

lemma continuous_rieszDirichletTerm (f : ℕ → ℂ) {sigma X : ℝ}
    (hs : 1/2 ≤ sigma) (hX : 0 < X) (n : ℕ) :
    Continuous (rieszDirichletTerm f sigma X n) := by
  by_cases hn : n=0
  · subst n
    unfold rieszDirichletTerm
    simp only [LSeries.term_zero,zero_mul]
    exact continuous_const
  · have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn
    have hXC : (X:ℂ) ≠ 0 := by exact_mod_cast hX.ne'
    have hnp : Continuous (fun t:ℝ => (n:ℂ)^((sigma:ℂ)+(t:ℂ)*Complex.I)) := by
      fun_prop (disch := exact Or.inl hnC)
    have hXp : Continuous (fun t:ℝ => (X:ℂ)^((sigma:ℂ)+(t:ℂ)*Complex.I)) := by
      fun_prop (disch := exact Or.inl hXC)
    have hterm : Continuous (fun t:ℝ => LSeries.term f ((sigma:ℂ)+(t:ℂ)*Complex.I) n) := by
      simp only [LSeries.term_of_ne_zero hn]
      exact continuous_const.div hnp (fun _ => Complex.cpow_ne_zero_iff.mpr (Or.inl hnC))
    exact (hterm.mul (continuous_rieszKernel_line hs)).mul hXp

lemma integrable_rieszDirichletTerm (f : ℕ → ℂ) {sigma X : ℝ}
    (hs : 1/2 ≤ sigma) (hX : 0 < X) (n : ℕ) :
    Integrable (rieszDirichletTerm f sigma X n) := by
  have hg := (integrable_rieszKernel_line hs).norm.const_mul
    (‖LSeries.term f (sigma:ℂ) n‖ * X^sigma)
  apply hg.mono' (continuous_rieszDirichletTerm f hs hX n).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => (norm_rieszDirichletTerm f sigma hX n t).le)

lemma integral_norm_rieszDirichletTerm (f : ℕ → ℂ) {sigma X : ℝ}
    (hX : 0 < X) (n : ℕ) :
    (∫ t:ℝ, ‖rieszDirichletTerm f sigma X n t‖) =
      ‖LSeries.term f (sigma:ℂ) n‖ * X^sigma *
        ∫ t:ℝ, ‖rieszKernel ((sigma:ℂ)+(t:ℂ)*Complex.I)‖ := by
  simp_rw [norm_rieszDirichletTerm f sigma hX n]
  exact integral_const_mul _ _

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_RieszIntegralRepresentation
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
open _root_.MeasureTheory _root_.Filter
open scoped Topology BigOperators

lemma rieszTerm_integral (f : ℕ → ℂ) (hf0 : f 0 = 0) {sigma X : ℝ}
    (hs : 1/2 ≤ sigma) (hX : 0 < X) (n : ℕ) :
    mellinFactor * (∫ t:ℝ, rieszDirichletTerm f sigma X n t) =
      f n * (rieszWeight ((n:ℝ)/X):ℂ) := by
  by_cases hn : n=0
  · simp [rieszDirichletTerm,hn,hf0]
  · have hr : 0 < (n:ℝ)/X := div_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) hX
    have hi := riesz_mellin_inversion hs hr
    have hi' : mellinFactor * (∫ t:ℝ, (((n:ℝ)/X:ℝ):ℂ)^(-((sigma:ℂ)+(t:ℂ)*Complex.I)) *
        rieszKernel ((sigma:ℂ)+(t:ℂ)*Complex.I)) = (rieszWeight ((n:ℝ)/X):ℂ) := by
      simpa only [mellinInv,smul_eq_mul,RCLike.real_smul_eq_coe_mul,mellinFactor] using! hi
    have he : (∫ t:ℝ, rieszDirichletTerm f sigma X n t) =
        f n * (∫ t:ℝ, (((n:ℝ)/X:ℝ):ℂ)^(-((sigma:ℂ)+(t:ℂ)*Complex.I)) *
          rieszKernel ((sigma:ℂ)+(t:ℂ)*Complex.I)) := by
      simp_rw [rieszDirichletTerm_eq_scaled f hf0 sigma hX n,mul_assoc]
      exact integral_const_mul _ _
    rw [he]
    calc
      _ = f n * (mellinFactor * (∫ t:ℝ, (((n:ℝ)/X:ℝ):ℂ)^(-((sigma:ℂ)+(t:ℂ)*Complex.I)) *
          rieszKernel ((sigma:ℂ)+(t:ℂ)*Complex.I))) := by ring
      _ = _ := by rw [hi']

theorem hasSum_riesz_integral (f : ℕ → ℂ) (hf0 : f 0 = 0) {sigma X : ℝ}
    (hs : 1/2 ≤ sigma) (hf : LSeriesSummable f (sigma:ℂ)) (hX : 0 < X) :
    HasSum (fun n:ℕ => f n*(rieszWeight ((n:ℝ)/X):ℂ))
      (mellinFactor * ∫ t:ℝ, LSeries f ((sigma:ℂ)+(t:ℂ)*Complex.I) *
        rieszKernel ((sigma:ℂ)+(t:ℂ)*Complex.I) * (X:ℂ)^((sigma:ℂ)+(t:ℂ)*Complex.I)) := by
  have hnorm : Summable (fun n:ℕ => ∫ t:ℝ, ‖rieszDirichletTerm f sigma X n t‖) := by
    simp_rw [integral_norm_rieszDirichletTerm f hX]
    exact (hf.norm.mul_right (X^sigma)).mul_right _
  have h := hasSum_integral_of_summable_integral_norm
    (fun n:ℕ => integrable_rieszDirichletTerm f hs hX n) hnorm
  have hscaled := h.mul_left mellinFactor
  simp_rw [rieszTerm_integral f hf0 hs hX] at hscaled
  have hseries (t:ℝ) : (∑' n:ℕ, rieszDirichletTerm f sigma X n t) =
      LSeries f ((sigma:ℂ)+(t:ℂ)*Complex.I) * rieszKernel ((sigma:ℂ)+(t:ℂ)*Complex.I) *
        (X:ℂ)^((sigma:ℂ)+(t:ℂ)*Complex.I) := by
    simp only [rieszDirichletTerm,tsum_mul_right,LSeries]
  simp_rw [hseries] at hscaled
  exact hscaled

theorem character_riesz_mellin {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma X : ℝ} (hs : 1 < sigma) (hX : 0 < X) :
    (∑' n:ℕ, (chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) * (rieszWeight ((n:ℝ)/X):ℂ)) =
      mellinFactor * ∫ t:ℝ,
        (-deriv (DirichletCharacter.LFunction chi) ((sigma:ℂ)+(t:ℂ)*Complex.I) /
          DirichletCharacter.LFunction chi ((sigma:ℂ)+(t:ℂ)*Complex.I)) *
        rieszKernel ((sigma:ℂ)+(t:ℂ)*Complex.I) * (X:ℂ)^((sigma:ℂ)+(t:ℂ)*Complex.I) := by
  have hf0 : (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) 0 = 0 := by simp
  have hf : LSeriesSummable (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) (sigma:ℂ) :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt chi (by simpa using hs)
  rw [(hasSum_riesz_integral _ hf0 (by linarith) hf hX).tsum_eq]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by
    dsimp only
    rw [twisted_series_eq_actual_log_derivative chi (by simpa using hs)])

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_RieszIntegrand
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

theorem finite_character_riesz_mellin {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma X : ℝ} (hs : 1 < sigma) (hX : 0 < X) :
    rieszSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X =
      mellinFactor * ∫ t:ℝ,
        (-deriv (DirichletCharacter.LFunction chi) ((sigma:ℂ)+(t:ℂ)*Complex.I) /
          DirichletCharacter.LFunction chi ((sigma:ℂ)+(t:ℂ)*Complex.I)) *
        rieszKernel ((sigma:ℂ)+(t:ℂ)*Complex.I) * (X:ℂ)^((sigma:ℂ)+(t:ℂ)*Complex.I) := by
  rw [← tsum_riesz_eq_finite _ hX]
  exact character_riesz_mellin chi hs hX

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.MeasureTheory _root_.Filter
open scoped Topology

lemma finite_riesz_eq_integrand {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma X : ℝ} (hs : 1 < sigma) (hX : 0 < X) :
    rieszSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X =
      mellinFactor * ∫ t:ℝ, characterRieszIntegrand chi X ((sigma:ℂ)+(t:ℂ)*Complex.I) := by
  simpa only [characterRieszIntegrand,logDeriv_apply,neg_div] using finite_character_riesz_mellin chi hs hX

lemma norm_characterRieszIntegrand {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {X : ℝ} (hX : 0 < X) (s : ℂ) :
    ‖characterRieszIntegrand chi X s‖ =
      ‖logDeriv (DirichletCharacter.LFunction chi) s‖ * ‖rieszKernel s‖ * X^s.re := by
  unfold characterRieszIntegrand
  rw [norm_mul,norm_mul,norm_neg,Complex.norm_cpow_eq_rpow_re_of_pos hX]

lemma differentiableAt_rieszKernel {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ rieszKernel s := by
  have h0 : s ≠ 0 := by intro h; simp [h] at hs
  have h1 : s+1 ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.add_re,Complex.one_re,Complex.zero_re] at he
    linarith
  unfold rieszKernel
  have hc : DifferentiableAt ℂ (fun _ : ℂ => (1:ℂ)) s := by fun_prop
  exact hc.div (by fun_prop) (mul_ne_zero h0 h1)

lemma differentiableAt_characterRieszIntegrand {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) {X : ℝ} (hX : 0 < X)
    {s : ℂ} (hs : 0 < s.re) (hne : DirichletCharacter.LFunction chi s ≠ 0) :
    DifferentiableAt ℂ (characterRieszIntegrand chi X) s := by
  have hL := DirichletCharacter.differentiable_LFunction hchi
  have hder : DifferentiableAt ℂ (deriv (DirichletCharacter.LFunction chi)) s :=
    (hL.analyticAt s).deriv.differentiableAt
  have hlog : DifferentiableAt ℂ (fun z => -logDeriv (DirichletCharacter.LFunction chi) z) s := by
    change DifferentiableAt ℂ (fun z => -(deriv (DirichletCharacter.LFunction chi) z /
      DirichletCharacter.LFunction chi z)) s
    exact (hder.div hL.differentiableAt hne).neg
  have hXC : (X:ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  have hpow : DifferentiableAt ℂ (fun z:ℂ => (X:ℂ)^z) s := by
    fun_prop (disch := exact Or.inl hXC)
  exact (hlog.mul (differentiableAt_rieszKernel hs)).mul hpow

lemma continuous_characterRiesz_right {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) {sigma X : ℝ}
    (hs : 1 < sigma) (hX : 0 < X) :
    Continuous (fun t:ℝ => characterRieszIntegrand chi X ((sigma:ℂ)+(t:ℂ)*Complex.I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hre : ((sigma:ℂ)+(t:ℂ)*Complex.I).re = sigma := by simp
  exact (differentiableAt_characterRieszIntegrand chi hchi hX (by rw [hre]; linarith)
    (LFunction_ne_zero_right chi (by simpa only [hre] using hs))).continuousAt.comp (by fun_prop)

lemma integrable_characterRiesz_right {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) {sigma X : ℝ}
    (hs : 1 < sigma) (hX : 0 < X) :
    Integrable (fun t:ℝ => characterRieszIntegrand chi X ((sigma:ℂ)+(t:ℂ)*Complex.I)) := by
  obtain ⟨C,hC,hbound⟩ := uniform_log_derivative_right
  have hg := (integrable_rieszKernel_line (show 1/2 ≤ sigma by linarith)).norm.const_mul
    (((sigma-1)⁻¹+C)*X^sigma)
  apply hg.mono' (continuous_characterRiesz_right chi hchi hs hX).aestronglyMeasurable
  filter_upwards [] with t
  have hre : ((sigma:ℂ)+(t:ℂ)*Complex.I).re = sigma := by simp
  have hb := hbound q chi ((sigma:ℂ)+(t:ℂ)*Complex.I) (by simpa only [hre] using hs)
  rw [norm_characterRieszIntegrand chi hX,hre]
  change ‖logDeriv (DirichletCharacter.LFunction chi) ((sigma:ℂ)+(t:ℂ)*Complex.I)‖ * _ * _ ≤ _
  have hb' : ‖logDeriv (DirichletCharacter.LFunction chi) ((sigma:ℂ)+(t:ℂ)*Complex.I)‖ ≤
      (sigma-1)⁻¹+C := by simpa only [logDeriv_apply,hre] using hb
  calc
    _ ≤ ((sigma-1)⁻¹+C)*‖rieszKernel ((sigma:ℂ)+(t:ℂ)*Complex.I)‖*X^sigma := by gcongr
    _ = _ := by ring

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_RieszRectangle
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
open _root_.Set _root_.Complex

lemma modulusHeight_le_of_abs_le (q : ℕ) (T : ℝ) (hT : 0 ≤ T) {t : ℝ} (ht : |t| ≤ T) :
    modulusHeight q t ≤ modulusHeight q T := by
  have h := Real.log_le_log (by positivity : 0 < |t|+6) (by linarith : |t|+6 ≤ T+6)
  unfold modulusHeight
  rw [abs_of_nonneg hT]
  linarith

theorem exists_uniform_riesz_rectangle :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1/100 ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q), chi ≠ 1 →
      ∀ X sigma T : ℝ, 0 < X → 1 < sigma → sigma ≤ 2 → 0 < T →
        1/2 ≤ rieszContourLeft a q T ∧
        (∀ s ∈ rieszContourRectangle a q sigma T,
          DirichletCharacter.LFunction chi s ≠ 0 ∧
          ‖logDeriv (DirichletCharacter.LFunction chi) s‖ ≤ C*(modulusHeight q T)^3) ∧
        _root_.Erdos970.HolomorphicOn (characterRieszIntegrand chi X) (rieszContourRectangle a q sigma T) := by
  obtain ⟨a,ha,ha100,C,hC,hstrip⟩ := exists_uniform_nonprincipal_strip_bound
  refine ⟨a,ha,ha100,C,hC,?_⟩
  intro q _ chi hchi X sigma T hX _hs hs2 hT
  have hH := modulusHeight_ge_one q T
  have hHp : 0 < modulusHeight q T := by linarith
  have hHsq : 1 ≤ (modulusHeight q T)^2 := by nlinarith
  have hfrac : a/(modulusHeight q T)^2 ≤ a := by
    apply (div_le_iff₀ (by positivity : 0 < (modulusHeight q T)^2)).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hHsq ha.le
  have hleft : 1/2 ≤ rieszContourLeft a q T := by unfold rieszContourLeft; linarith
  have hb : ∀ s ∈ rieszContourRectangle a q sigma T,
      DirichletCharacter.LFunction chi s ≠ 0 ∧
      ‖logDeriv (DirichletCharacter.LFunction chi) s‖ ≤ C*(modulusHeight q T)^3 := by
    intro s hmem
    have hr := (Complex.mem_reProdIm.mp hmem).1
    have hi := (Complex.mem_reProdIm.mp hmem).2
    have hht := modulusHeight_le_of_abs_le q T hT.le (abs_le.mpr hi)
    have hHs := modulusHeight_ge_one q s.im
    have hHsp : 0 < modulusHeight q s.im := by linarith
    have hpow : (modulusHeight q s.im)^2 ≤ (modulusHeight q T)^2 := by nlinarith
    have hdiv := div_le_div_of_nonneg_left ha.le (show 0 < (modulusHeight q s.im)^2 by positivity) hpow
    have hs' : 1-a/(modulusHeight q s.im)^2 ≤ s.re := by
      change 1-a/(modulusHeight q T)^2 ≤ s.re ∧ s.re ≤ sigma at hr
      linarith
    have h := hstrip q chi hchi s.re s.im hs' (hr.2.trans hs2)
    simp only [Complex.re_add_im] at h
    refine ⟨h.1,?_⟩
    change ‖deriv (DirichletCharacter.LFunction chi) s / DirichletCharacter.LFunction chi s‖ ≤ _
    apply h.2.trans
    gcongr
  refine ⟨hleft,hb,?_⟩
  intro s hmem
  have hr := (Complex.mem_reProdIm.mp hmem).1.1
  have hsp : 0 < s.re := by linarith
  exact (differentiableAt_characterRieszIntegrand chi hchi hX hsp (hb s hmem).1).differentiableWithinAt

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_RieszCauchy
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
open _root_.Set _root_.Complex _root_.MeasureTheory

lemma cauchy_vertical_shift (f : ℂ → ℂ) (left right T : ℝ)
    (hlr : left ≤ right) (hT : 0 ≤ T)
    (hf : _root_.Erdos970.HolomorphicOn f (Icc left right ×ℂ Icc (-T) T)) :
    _root_.Erdos970.VIntegral f right (-T) T = _root_.Erdos970.VIntegral f left (-T) T -
      _root_.Erdos970.HIntegral f left right (-T) + _root_.Erdos970.HIntegral f left right T := by
  let z : ℂ := (left:ℂ)-(T:ℂ)*Complex.I
  let w : ℂ := (right:ℂ)+(T:ℂ)*Complex.I
  have hzr : z.re = left := by simp [z]
  have hzi : z.im = -T := by simp [z]
  have hwr : w.re = right := by simp [w]
  have hwi : w.im = T := by simp [w]
  have he : Rectangle z w = Icc left right ×ℂ Icc (-T) T := by
    simp only [Rectangle,hzr,hzi,hwr,hwi,uIcc_of_le hlr,uIcc_of_le (by linarith : -T ≤ T)]
  have hz := hf.vanishesOnRectangle (z := z) (w := w) (fun s hs => by simpa only [he] using hs)
  simp only [_root_.Erdos970.RectangleIntegral,hzr,hzi,hwr,hwi] at hz
  linear_combination hz

lemma norm_cauchy_vertical_le (f : ℂ → ℂ) (left right T : ℝ)
    (hlr : left ≤ right) (hT : 0 ≤ T)
    (hf : _root_.Erdos970.HolomorphicOn f (Icc left right ×ℂ Icc (-T) T)) :
    ‖_root_.Erdos970.VIntegral f right (-T) T‖ ≤ ‖_root_.Erdos970.VIntegral f left (-T) T‖ +
      ‖_root_.Erdos970.HIntegral f left right (-T)‖ + ‖_root_.Erdos970.HIntegral f left right T‖ := by
  rw [cauchy_vertical_shift f left right T hlr hT hf]
  calc
    _ ≤ ‖_root_.Erdos970.VIntegral f left (-T) T - _root_.Erdos970.HIntegral f left right (-T)‖ +
      ‖_root_.Erdos970.HIntegral f left right T‖ := norm_add_le _ _
    _ ≤ _ := by gcongr; exact norm_sub_le _ _

lemma norm_verticalIntegral_eq (f : ℂ → ℂ) (sigma : ℝ) :
    ‖_root_.Erdos970.VerticalIntegral f sigma‖ = ‖∫ t:ℝ, f ((sigma:ℂ)+(t:ℂ)*Complex.I)‖ := by
  simp only [_root_.Erdos970.VerticalIntegral,norm_smul,Complex.norm_I,one_mul]

lemma norm_VIntegral_eq (f : ℂ → ℂ) (sigma lo hi : ℝ) :
    ‖_root_.Erdos970.VIntegral f sigma lo hi‖ = ‖∫ t in lo..hi, f ((sigma:ℂ)+(t:ℂ)*Complex.I)‖ := by
  simp only [_root_.Erdos970.VIntegral,norm_smul,Complex.norm_I,one_mul]

lemma norm_full_vertical_shift_le (f : ℂ → ℂ) (left right T : ℝ)
    (hlr : left ≤ right) (hT : 0 ≤ T)
    (hf : _root_.Erdos970.HolomorphicOn f (Icc left right ×ℂ Icc (-T) T))
    (hi : Integrable (fun t:ℝ => f ((right:ℂ)+(t:ℂ)*Complex.I))) :
    ‖_root_.Erdos970.VerticalIntegral f right‖ ≤
      ‖∫ t in Iic (-T), f ((right:ℂ)+(t:ℂ)*Complex.I)‖ +
      ‖_root_.Erdos970.VIntegral f left (-T) T‖ + ‖_root_.Erdos970.HIntegral f left right (-T)‖ +
      ‖_root_.Erdos970.HIntegral f left right T‖ +
      ‖∫ t in Ici T, f ((right:ℂ)+(t:ℂ)*Complex.I)‖ := by
  rw [_root_.Erdos970.verticalIntegral_split_three (-T) T hi]
  have h1 := norm_add_le (Complex.I • (∫ t in Iic (-T), f ((right:ℂ)+(t:ℂ)*Complex.I)) +
    _root_.Erdos970.VIntegral f right (-T) T) (Complex.I • ∫ t in Ici T, f ((right:ℂ)+(t:ℂ)*Complex.I))
  have h2 := norm_add_le (Complex.I • ∫ t in Iic (-T), f ((right:ℂ)+(t:ℂ)*Complex.I))
    (_root_.Erdos970.VIntegral f right (-T) T)
  simp only [norm_smul,Complex.norm_I,one_mul] at h1 h2
  have h3 := norm_cauchy_vertical_le f left right T hlr hT hf
  linarith

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_RieszMajorantIntegrals
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
open _root_.MeasureTheory _root_.Set

lemma arctan_le_self_nonneg {x : ℝ} (hx : 0 ≤ x) : Real.arctan x ≤ x := by
  have h := intervalIntegral.integral_mono_on (a := 0) (b := x) hx
    integrable_inv_one_add_sq.intervalIntegrable (intervalIntegrable_const (c := (1:ℝ)))
    (fun t _ => show (1+t^2)⁻¹ ≤ 1 by
      rw [← one_div]
      exact (div_le_iff₀ (by positivity : 0 < 1+t^2)).mpr (by nlinarith [sq_nonneg t]))
  rw [integral_inv_one_add_sq,Real.arctan_zero,sub_zero] at h
  simpa using h

lemma rieszMajorant_upper_tail {T : ℝ} (hT : 0 < T) :
    (∫ t in Ici T, (4:ℝ)/(1+t^2)) ≤ 4/T := by
  rw [integral_Ici_eq_integral_Ioi]
  simp only [div_eq_mul_inv,integral_const_mul,integral_Ioi_inv_one_add_sq]
  have hi := Real.arctan_inv_of_pos hT
  simp only [div_eq_mul_inv] at hi
  rw [← hi]
  exact mul_le_mul_of_nonneg_left (arctan_le_self_nonneg (inv_nonneg.mpr hT.le)) (by norm_num)

lemma rieszMajorant_lower_tail {T : ℝ} (hT : 0 < T) :
    (∫ t in Iic (-T), (4:ℝ)/(1+t^2)) ≤ 4/T := by
  have he : (∫ t in Iic (-T), (4:ℝ)/(1+t^2)) = ∫ t in Ici T, (4:ℝ)/(1+t^2) := by
    rw [integral_Ici_eq_integral_Ioi]
    simp only [div_eq_mul_inv,integral_const_mul,integral_Iic_inv_one_add_sq,
      integral_Ioi_inv_one_add_sq,Real.arctan_neg]
    ring
  rw [he]
  exact rieszMajorant_upper_tail hT

lemma rieszMajorant_interval_le (T : ℝ) :
    (∫ t in (-T)..T, (4:ℝ)/(1+t^2)) ≤ 4*Real.pi := by
  simp only [div_eq_mul_inv,intervalIntegral.integral_const_mul,integral_inv_one_add_sq,Real.arctan_neg]
  have h := Real.arctan_lt_pi_div_two T
  linarith

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_RecoveryScale
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace Erdos970Dependency.SiegelWalfisz
open _root_.MeasureTheory _root_.Set _root_.Filter

theorem exists_uniform_riesz_right_tails :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
      chi ≠ 1 → ∀ X sigma T : ℝ, 0 < X → 1 < sigma → 0 < T →
      ‖∫ t in Iic (-T), characterRieszIntegrand chi X ((sigma:ℂ)+(t:ℂ)*Complex.I)‖ ≤
        4*((sigma-1)⁻¹+C)*X^sigma/T ∧
      ‖∫ t in Ici T, characterRieszIntegrand chi X ((sigma:ℂ)+(t:ℂ)*Complex.I)‖ ≤
        4*((sigma-1)⁻¹+C)*X^sigma/T := by
  obtain ⟨C,hC,hbound⟩ := uniform_log_derivative_right
  refine ⟨C,hC,?_⟩
  intro q _ chi hchi X sigma T hX hs hT
  let B : ℝ := (sigma-1)⁻¹+C
  let D : ℝ := B*X^sigma
  have hB : 0 ≤ B := by dsimp only [B] <;> positivity
  have hD : 0 ≤ D := by dsimp only [D] <;> positivity
  have hpoint (t:ℝ) : ‖characterRieszIntegrand chi X ((sigma:ℂ)+(t:ℂ)*Complex.I)‖ ≤
      D*((4:ℝ)/(1+t^2)) := by
    have hre : ((sigma:ℂ)+(t:ℂ)*Complex.I).re = sigma := by simp
    have hb : ‖logDeriv (DirichletCharacter.LFunction chi) ((sigma:ℂ)+(t:ℂ)*Complex.I)‖ ≤ B := by
      simpa only [logDeriv_apply,hre,B] using
        hbound q chi ((sigma:ℂ)+(t:ℂ)*Complex.I) (by simpa only [hre] using hs)
    rw [norm_characterRieszIntegrand chi hX,hre]
    calc
      _ ≤ B*‖rieszKernel ((sigma:ℂ)+(t:ℂ)*Complex.I)‖*X^sigma := by gcongr
      _ = D*‖rieszKernel ((sigma:ℂ)+(t:ℂ)*Complex.I)‖ := by dsimp only [D] <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (rieszKernel_norm_bound (by linarith) t) hD
  have hf := integrable_characterRiesz_right chi hchi hs hX
  have hg := rieszMajorant_integrable.const_mul D
  have htail (S:Set ℝ) (hbudget : (∫ t in S, (4:ℝ)/(1+t^2)) ≤ 4/T) :
      ‖∫ t in S, characterRieszIntegrand chi X ((sigma:ℂ)+(t:ℂ)*Complex.I)‖ ≤
        4*((sigma-1)⁻¹+C)*X^sigma/T := by
    calc
      _ ≤ ∫ t in S, ‖characterRieszIntegrand chi X ((sigma:ℂ)+(t:ℂ)*Complex.I)‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ t in S, D*((4:ℝ)/(1+t^2)) :=
        integral_mono (μ := volume.restrict S) hf.norm.integrableOn hg.integrableOn hpoint
      _ = D*(∫ t in S, (4:ℝ)/(1+t^2)) := integral_const_mul _ _
      _ ≤ D*(4/T) := mul_le_mul_of_nonneg_left hbudget hD
      _ = _ := by dsimp only [D,B] <;> ring
  exact ⟨htail (Iic (-T)) (rieszMajorant_lower_tail hT),
    htail (Ici T) (rieszMajorant_upper_tail hT)⟩

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Set _root_.Complex _root_.MeasureTheory
open scoped Interval

lemma riesz_left_edge_bound {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {X left right T C : ℝ} (hX : 0 < X) (hl : 1/2 ≤ left) (hlr : left ≤ right)
    (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hb : ∀ s ∈ Icc left right ×ℂ Icc (-T) T,
      ‖logDeriv (DirichletCharacter.LFunction chi) s‖ ≤ C*(modulusHeight q T)^3)
    (hf : _root_.Erdos970.HolomorphicOn (characterRieszIntegrand chi X) (Icc left right ×ℂ Icc (-T) T)) :
    ‖_root_.Erdos970.VIntegral (characterRieszIntegrand chi X) left (-T) T‖ ≤
      4*Real.pi*C*(modulusHeight q T)^3*X^left := by
  let B : ℝ := C*(modulusHeight q T)^3*X^left
  have hH := modulusHeight_ge_one q T
  have hB : 0 ≤ B := by dsimp only [B] <;> positivity
  have hTT : -T ≤ T := by linarith
  have hmaps : MapsTo (fun t:ℝ => (left:ℂ)+(t:ℂ)*Complex.I) (Icc (-T) T)
      (Icc left right ×ℂ Icc (-T) T) := by
    intro t ht
    simp only [Complex.mem_reProdIm,show ((left:ℂ)+(t:ℂ)*Complex.I).re = left by simp,
      show ((left:ℂ)+(t:ℂ)*Complex.I).im = t by simp]
    exact ⟨⟨le_rfl,hlr⟩,ht⟩
  have hc : ContinuousOn (fun t:ℝ => characterRieszIntegrand chi X ((left:ℂ)+(t:ℂ)*Complex.I))
      (Icc (-T) T) := hf.continuousOn.comp (by fun_prop) hmaps
  have hfi : IntervalIntegrable (fun t:ℝ => characterRieszIntegrand chi X ((left:ℂ)+(t:ℂ)*Complex.I))
      volume (-T) T := (show ContinuousOn _ (uIcc (-T) T) by simpa only [uIcc_of_le hTT] using hc).intervalIntegrable
  have hg := (rieszMajorant_integrable.const_mul B).intervalIntegrable (a := -T) (b := T)
  have hpoint : ∀ t ∈ Icc (-T) T,
      ‖characterRieszIntegrand chi X ((left:ℂ)+(t:ℂ)*Complex.I)‖ ≤ B*((4:ℝ)/(1+t^2)) := by
    intro t ht
    have hlog := hb _ (hmaps ht)
    rw [norm_characterRieszIntegrand chi hX,show ((left:ℂ)+(t:ℂ)*Complex.I).re = left by simp]
    calc
      _ ≤ (C*(modulusHeight q T)^3)*‖rieszKernel ((left:ℂ)+(t:ℂ)*Complex.I)‖*X^left := by gcongr
      _ = B*‖rieszKernel ((left:ℂ)+(t:ℂ)*Complex.I)‖ := by dsimp only [B] <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (rieszKernel_norm_bound hl t) hB
  have hcomp := intervalIntegral.integral_mono_on hTT hfi.norm hg hpoint
  rw [intervalIntegral.integral_const_mul] at hcomp
  have hmajor := mul_le_mul_of_nonneg_left (rieszMajorant_interval_le T) hB
  rw [norm_VIntegral_eq]
  calc
    _ ≤ ∫ t in (-T)..T, ‖characterRieszIntegrand chi X ((left:ℂ)+(t:ℂ)*Complex.I)‖ :=
      intervalIntegral.norm_integral_le_integral_norm hTT
    _ ≤ B*(4*Real.pi) := hcomp.trans hmajor
    _ = _ := by dsimp only [B] <;> ring

lemma riesz_horizontal_edge_bound {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {X left right T height C : ℝ} (hX : 1 ≤ X) (hl : 1/2 ≤ left) (hlr : left ≤ right)
    (hr : right ≤ 2) (_hT : 0 ≤ T) (hy : |height| = T) (hC : 0 ≤ C)
    (hb : ∀ s ∈ Icc left right ×ℂ Icc (-T) T,
      ‖logDeriv (DirichletCharacter.LFunction chi) s‖ ≤ C*(modulusHeight q T)^3)
    (hf : _root_.Erdos970.HolomorphicOn (characterRieszIntegrand chi X) (Icc left right ×ℂ Icc (-T) T)) :
    ‖_root_.Erdos970.HIntegral (characterRieszIntegrand chi X) left right height‖ ≤
      8*C*(modulusHeight q T)^3*X^right/(1+T^2) := by
  have hXp : 0 < X := by linarith
  let B : ℝ := C*(modulusHeight q T)^3*X^right*((4:ℝ)/(1+T^2))
  have hH := modulusHeight_ge_one q T
  have hB : 0 ≤ B := by dsimp only [B] <;> positivity
  have hmaps : MapsTo (fun x:ℝ => (x:ℂ)+(height:ℂ)*Complex.I) (Icc left right)
      (Icc left right ×ℂ Icc (-T) T) := by
    intro x hx
    simp only [Complex.mem_reProdIm,show ((x:ℂ)+(height:ℂ)*Complex.I).re = x by simp,
      show ((x:ℂ)+(height:ℂ)*Complex.I).im = height by simp]
    exact ⟨hx,abs_le.mp hy.le⟩
  have hc : ContinuousOn (fun x:ℝ => characterRieszIntegrand chi X ((x:ℂ)+(height:ℂ)*Complex.I))
      (Icc left right) := hf.continuousOn.comp (by fun_prop) hmaps
  have hfi : IntervalIntegrable (fun x:ℝ => characterRieszIntegrand chi X ((x:ℂ)+(height:ℂ)*Complex.I))
      volume left right := (show ContinuousOn _ (uIcc left right) by simpa only [uIcc_of_le hlr] using hc).intervalIntegrable
  have hpoint : ∀ x ∈ Icc left right,
      ‖characterRieszIntegrand chi X ((x:ℂ)+(height:ℂ)*Complex.I)‖ ≤ B := by
    intro x hx
    have hlog := hb _ (hmaps hx)
    have hkernel := rieszKernel_norm_bound (hl.trans hx.1) height
    have hsq : height^2 = T^2 := by rw [← sq_abs height,hy]
    rw [hsq] at hkernel
    have hpow := Real.rpow_le_rpow_of_exponent_le hX hx.2
    rw [norm_characterRieszIntegrand chi hXp,show ((x:ℂ)+(height:ℂ)*Complex.I).re = x by simp]
    calc
      _ ≤ (C*(modulusHeight q T)^3)*((4:ℝ)/(1+T^2))*X^right := by gcongr
      _ = B := by dsimp only [B] <;> ring
  have hcomp := intervalIntegral.integral_mono_on hlr hfi.norm (intervalIntegrable_const (c := B)) hpoint
  rw [intervalIntegral.integral_const] at hcomp
  have hwidth : right-left ≤ 2 := by linarith
  have hwidthB := mul_le_mul_of_nonneg_right hwidth hB
  unfold _root_.Erdos970.HIntegral
  have hn := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := fun x:ℝ => characterRieszIntegrand chi X ((x:ℂ)+(height:ℂ)*Complex.I)) hlr
  have hbound : ‖∫ x in left..right, characterRieszIntegrand chi X ((x:ℂ)+(height:ℂ)*Complex.I)‖ ≤ 2*B := by
    simp only [smul_eq_mul] at hcomp
    linarith
  apply hbound.trans_eq
  dsimp only [B]
  ring

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Set _root_.Complex _root_.MeasureTheory

lemma norm_mellinFactor : ‖mellinFactor‖ = 1/(2*Real.pi) := by
  unfold mellinFactor
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity)]

theorem exists_uniform_riesz_contour_bound_jb247_oai :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1/100 ∧ ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q), chi ≠ 1 →
      ∀ X sigma T : ℝ, 1 ≤ X → 1 < sigma → sigma ≤ 2 → 0 < T →
      ‖rieszSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X‖ ≤
        (1/(2*Real.pi)) *
          (4*Real.pi*C*(modulusHeight q T)^3*X^(rieszContourLeft a q T) +
            16*C*(modulusHeight q T)^3*X^sigma/(1+T^2) +
            8*((sigma-1)⁻¹+B)*X^sigma/T) := by
  obtain ⟨a,ha,ha100,C,hC,hrect⟩ := exists_uniform_riesz_rectangle
  obtain ⟨B,hB,htails⟩ := exists_uniform_riesz_right_tails
  refine ⟨a,ha,ha100,C,hC,B,hB,?_⟩
  intro q _ chi hchi X sigma T hX hs hs2 hT
  have hXp : 0 < X := by linarith
  obtain ⟨hl,hzero,hhol⟩ := hrect q chi hchi X sigma T hXp hs hs2 hT
  let left : ℝ := rieszContourLeft a q T
  have hlr : left ≤ sigma := by
    have hdiv : 0 ≤ a/(modulusHeight q T)^2 := div_nonneg ha.le (sq_nonneg _)
    dsimp only [left,rieszContourLeft]
    linarith
  have hlog : ∀ s ∈ Icc left sigma ×ℂ Icc (-T) T,
      ‖logDeriv (DirichletCharacter.LFunction chi) s‖ ≤ C*(modulusHeight q T)^3 :=
    fun s hmem => (hzero s hmem).2
  have hleft := riesz_left_edge_bound chi hXp hl hlr hT.le hC.le hlog hhol
  have hdown := riesz_horizontal_edge_bound chi (height := -T) hX hl hlr hs2 hT.le
    (by rw [abs_neg,abs_of_nonneg hT.le]) hC.le hlog hhol
  have hup := riesz_horizontal_edge_bound chi (height := T) hX hl hlr hs2 hT.le
    (abs_of_nonneg hT.le) hC.le hlog hhol
  obtain ⟨htlo,hthi⟩ := htails q chi hchi X sigma T hXp hs hT
  have hshift := norm_full_vertical_shift_le (characterRieszIntegrand chi X) left sigma T hlr hT.le
    hhol (integrable_characterRiesz_right chi hchi hs hXp)
  let E : ℝ := 4*Real.pi*C*(modulusHeight q T)^3*X^left +
    16*C*(modulusHeight q T)^3*X^sigma/(1+T^2) + 8*((sigma-1)⁻¹+B)*X^sigma/T
  have hfull : ‖_root_.Erdos970.VerticalIntegral (characterRieszIntegrand chi X) sigma‖ ≤ E := by
    have hp := add_le_add (add_le_add (add_le_add (add_le_add htlo hleft) hdown) hup) hthi
    apply (hshift.trans hp).trans_eq
    dsimp only [E,left]
    ring
  rw [finite_riesz_eq_integrand chi hs hXp,norm_mul,norm_mellinFactor,
    ← norm_verticalIntegral_eq (characterRieszIntegrand chi X) sigma]
  exact mul_le_mul_of_nonneg_left hfull (by positivity)

end Erdos970Dependency.SiegelWalfisz



end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.exists_uniform_riesz_contour_bound_jb247_oai := @OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.exists_uniform_riesz_contour_bound_jb247_oai
