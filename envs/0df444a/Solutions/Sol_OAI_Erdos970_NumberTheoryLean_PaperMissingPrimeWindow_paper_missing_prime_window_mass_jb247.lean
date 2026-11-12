-- Prove2me | solution 1 for OAI.Erdos970.NumberTheoryLean.PaperMissingPrimeWindow.paper_missing_prime_window_mass_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:05:57.839403+00:00
-- url     : https://prove2.me/submissions/ae23c50c-6836-44e0-baaf-a0f7187a1613

import Batteries.Tactic.Lemma
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Group.Support
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompMap
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.Bound
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UrysohnsLemma
import Definitions.Def_OAIQ247J010
import Theorems.Thm_OAI_Erdos970_NumberTheoryLean_MovingPrimeWindowProbability_source_missing_window_probability_jb247

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FiniteHistorySupport
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.Erdos970.NumberTheoryLean.ReferenceBenchmarkDecay.benchmark_even_below_two
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.FinitePathGeometry

open Set
open DerivativeWeights TransitionKernels

theorem nextGap_div_ratio {r t : ℝ} (ht : 0 < t) : nextGap r t / t = nextExponent r t := by
  unfold nextGap nextExponent
  field_simp

theorem valid_final {i : Side} {s : ℝ} {ts : List ℝ}
    (hs : Valid i s) (ht : Admissible i s ts) : Valid (finalSide i ts) (finalRatio s ts) := by
  induction ts generalizing i s with
  | nil => exact hs
  | cons t ts ih => exact ih (valid_next hs ht.1) ht.2

theorem nextGap_eq_cost {r t : ℝ} (ht : 0 < t) : nextGap r t = r * Real.exp (-cost t) := by
  have hx : 0 < 1 + 1 / t := by positivity
  unfold cost nextGap
  rw [Real.exp_neg, Real.exp_log hx]
  field_simp

theorem finalGap_eq_cost {i : Side} {s r : ℝ} {ts : List ℝ}
    (hs : Valid i s) (ht : Admissible i s ts) :
    finalGap r ts = r * Real.exp (-pathCost ts) := by
  induction ts generalizing i s r with
  | nil => simp [finalGap, pathCost]
  | cons t ts ih =>
    have hv := valid_next hs ht.1
    rw [finalGap, ih hv ht.2, nextGap_eq_cost (valid_pos hv), pathCost,
      neg_add, Real.exp_add]
    ring

end NumberTheoryLean.FinitePathGeometry



namespace NumberTheoryLean.FiniteHistoryTransport

open Set MeasureTheory ProbabilityTheory MeasurableEquiv
open scoped ENNReal

theorem extend_measurable {X : Type*} [MeasurableSpace X] (n : ℕ) :
    Measurable (fun p : Hist X n × X => extend n p.1 p.2) := by
  exact (measurable_IicProdIoc (X := fun _ => X) (m := n) (n := n+1)).comp
    (measurable_fst.prodMk ((piSingleton (X := fun _ => X) n).measurable.comp measurable_snd))

theorem mapHist_extend {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (f : X → Y) (n : ℕ) (h : Hist X n) (x : X) :
    mapHist f (n+1) (extend n h x) = extend n (mapHist f n h) (f x) := by
  ext k
  simp only [mapHist, extend, IicProdIoc_def, piSingleton,
    MeasurableEquiv.coe_mk, Equiv.coe_fn_mk]
  split_ifs <;> simp

theorem lintegral_pathKernel_succ {X : Type*} [MeasurableSpace X]
    (K : Kernel X X) [IsSFiniteKernel K] (n : ℕ) (h₀ : Hist X 0)
    {F : Hist X (n+1) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ h, F h ∂pathKernel K (n+1) h₀ =
      ∫⁻ h, ∫⁻ x, F (extend n h x) ∂K (last n h) ∂pathKernel K n h₀ := by
  rw [pathKernel, Kernel.partialTraj_succ_of_le (Nat.zero_le n),
    Kernel.lintegral_map _ (measurable_IicProdIoc (X := fun _ => X) (m := n) (n := n+1)) _ hF,
    Kernel.lintegral_comp _ _ _ (by exact hF.comp measurable_IicProdIoc)]
  congr 1
  funext h
  rw [Kernel.lintegral_id_prod (by exact hF.comp measurable_IicProdIoc),
    Kernel.lintegral_map _ (piSingleton (X := fun _ => X) n).measurable _
      (by exact (hF.comp measurable_IicProdIoc).comp measurable_prodMk_left)]
  rw [pastKernel, Kernel.comap_apply]
  rfl

end NumberTheoryLean.FiniteHistoryTransport



namespace NumberTheoryLean.FiniteHistoryTransport

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable (K : Kernel X X) (L : Kernel Y Y) [IsSFiniteKernel K] [IsSFiniteKernel L]
variable {f : X → Y} (hf : Measurable f)
variable (hstep : ∀ x, (K x).map f = L (f x))

include hf hstep

theorem lintegral_mapHist (n : ℕ) (h₀ : Hist X 0)
    {F : Hist Y n → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ h, F (mapHist f n h) ∂pathKernel K n h₀ =
      ∫⁻ h, F h ∂pathKernel L n (mapHist f 0 h₀) := by
  induction n with
  | zero =>
    simp only [pathKernel, Kernel.partialTraj_self, Kernel.id_apply]
    rw [lintegral_dirac' _ (by exact hF.comp (mapHist_measurable hf 0)), lintegral_dirac' _ hF]
  | succ n ih =>
    rw [lintegral_pathKernel_succ K n h₀ (by exact hF.comp (mapHist_measurable hf (n+1))),
      lintegral_pathKernel_succ L n (mapHist f 0 h₀) hF]
    have hG : Measurable (fun h : Hist Y n =>
        ∫⁻ y, F (extend n h y) ∂L (last n h)) := by
      have hm : Measurable (Function.uncurry (fun h : Hist Y n => fun y : Y =>
          F (extend n h y))) := hF.comp (extend_measurable n)
      simpa only [pastKernel, Kernel.comap_apply] using
        (hm.lintegral_kernel_prod_right (κ := pastKernel L n))
    calc
      _ = ∫⁻ h, ∫⁻ y, F (extend n (mapHist f n h) y)
          ∂L (last n (mapHist f n h)) ∂pathKernel K n h₀ := by
        apply lintegral_congr
        intro h
        simp only [mapHist_extend]
        change (∫⁻ x, F (extend n (mapHist f n h) (f x)) ∂K (last n h)) =
          ∫⁻ y, F (extend n (mapHist f n h) y) ∂L (f (last n h))
        rw [← hstep (last n h), lintegral_map]
        · exact hF.comp ((extend_measurable n).comp measurable_prodMk_left)
        · exact hf
      _ = _ := ih hG

theorem pathKernel_mapHist (n : ℕ) :
    (pathKernel K n).map (mapHist f n) =
      (pathKernel L n).comap (mapHist f 0) (mapHist_measurable hf 0) := by
  apply Kernel.ext_fun
  intro h₀ F hF
  rw [Kernel.lintegral_map _ (mapHist_measurable hf n) _ hF, Kernel.comap_apply]
  exact lintegral_mapHist K L hf hstep n h₀ hF

theorem pathMeasure_mapHist (n : ℕ) (h₀ : Hist X 0) :
    (pathKernel K n h₀).map (mapHist f n) =
      pathKernel L n (mapHist f 0 h₀) := by
  rw [← Kernel.map_apply _ (mapHist_measurable hf n), pathKernel_mapHist K L hf hstep,
    Kernel.comap_apply]

end NumberTheoryLean.FiniteHistoryTransport



namespace NumberTheoryLean.FiniteHistoryTransport

open Set MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

theorem extend_last (n : ℕ) (h : Hist X n) (x : X) : last (n+1) (extend n h x) = x := by
  simp [last, extend, IicProdIoc_def, MeasurableEquiv.piSingleton]

variable (K : Kernel X X) [IsSFiniteKernel K]

theorem lintegral_endpoint (n : ℕ) (h₀ : Hist X 0) {F : X → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ h, F (last n h) ∂pathKernel K n h₀ = ∫⁻ x, F x ∂(K^n) (last 0 h₀) := by
  induction n generalizing F with
  | zero =>
    change (∫⁻ h, F (last 0 h) ∂Kernel.id h₀) = ∫⁻ x, F x ∂Kernel.id (last 0 h₀)
    simp only [Kernel.id_apply]
    rw [lintegral_dirac' _ (by exact hF.comp (measurable_pi_apply _)), lintegral_dirac' _ hF]
  | succ n ih =>
    rw [lintegral_pathKernel_succ K n h₀ (by exact hF.comp (measurable_pi_apply _))]
    simp only [extend_last]
    have hp : K^(n+1) = K ∘ₖ (K^n) := by
      simpa only [Nat.add_comm, pow_one] using Kernel.pow_add K 1 n
    rw [hp, Kernel.lintegral_comp _ _ _ hF]
    exact ih (hF.lintegral_kernel (κ := K))

theorem pathKernel_endpoint (n : ℕ) :
    (pathKernel K n).map (last n) = (K^n).comap (last 0) (last_measurable 0) := by
  apply Kernel.ext_fun
  intro h₀ F hF
  rw [Kernel.lintegral_map _ (last_measurable n) _ hF, Kernel.comap_apply]
  exact lintegral_endpoint K n h₀ hF

theorem pathMeasure_endpoint (n : ℕ) (h₀ : Hist X 0) :
    (pathKernel K n h₀).map (last n) = (K^n) (last 0 h₀) := by
  rw [← Kernel.map_apply _ (last_measurable n), pathKernel_endpoint, Kernel.comap_apply]

theorem pathMeasure_coordinate [IsMarkovKernel K] (n k : ℕ) (hk : k ≤ n) (h₀ : Hist X 0) :
    (pathKernel K n h₀).map (fun h => h ⟨k, by simpa using hk⟩) =
      (K^k) (last 0 h₀) := by
  have hrestriction : (pathKernel K n h₀).map (frestrictLe₂ (π := fun _ => X) hk) = pathKernel K k h₀ :=
    Kernel.partialTraj_map_frestrictLe₂_apply (X := fun _ => X) (κ := pastKernel K) h₀ hk
  calc
    _ = ((pathKernel K n h₀).map (frestrictLe₂ (π := fun _ => X) hk)).map (last k) := by
      rw [Measure.map_map (last_measurable k) (measurable_frestrictLe₂ hk)]
      rfl
    _ = _ := by rw [hrestriction, pathMeasure_endpoint]

end NumberTheoryLean.FiniteHistoryTransport



namespace NumberTheoryLean.FiniteHistoryTransport

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

theorem ae_pathKernel_succ (K : Kernel X X) [IsSFiniteKernel K]
    (n : ℕ) (h₀ : Hist X 0) {P : Hist X (n+1) → Prop}
    (hP : MeasurableSet {h | P h})
    (hstep : ∀ᵐ h ∂pathKernel K n h₀, ∀ᵐ x ∂K (last n h), P (extend n h x)) :
    ∀ᵐ h ∂pathKernel K (n+1) h₀, P h := by
  classical
  rw [ae_iff]
  change pathKernel K (n+1) h₀ ({h | P h}ᶜ) = 0
  rw [← lintegral_indicator_one hP.compl,
    lintegral_pathKernel_succ K n h₀ (by exact measurable_const.indicator hP.compl)]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hstep] with h hh
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hh] with x hx
  simp [hx]

theorem pathSum_measurable {F : X → ℝ} (hF : Measurable F) (n : ℕ) :
    Measurable (pathSum F n) := by
  unfold pathSum
  fun_prop

theorem extend_previous (n : ℕ) (h : Hist X n) (x : X) (k : Finset.Iic n) :
    extend n h x ⟨k,by exact Finset.mem_Iic.mpr ((Finset.mem_Iic.mp k.2).trans n.le_succ)⟩ = h k := by
  simp [extend,IicProdIoc_def,show (k:ℕ) ≤ n from Finset.mem_Iic.mp k.2]

theorem pathSum_extend (F : X → ℝ) (n : ℕ) (h : Hist X n) (x : X) :
    pathSum F (n+1) (extend n h x) = pathSum F n h + F (last n h) := by
  rw [pathSum,Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    congr 1
    exact extend_previous n h x ⟨j,by exact Finset.mem_Iic.mpr j.isLt.le⟩
  · congr 1
    exact extend_previous n h x ⟨n,by simp⟩

end NumberTheoryLean.FiniteHistoryTransport


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_WeightIntegrals
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.Erdos970.NumberTheoryLean.ReferenceBenchmarkDecay.benchmark_even_below_two
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.TwoStepDensityBounds

open Set
open DerivativeWeights WeightFutureIntegrals FinitePathGeometry

theorem weight_antitone {i : Side} {s t : ℝ} (hs : Valid i s) (ht : Valid i t) (hst : s ≤ t) :
    weight i t ≤ weight i s := by
  cases i with
  | even =>
    exact phiEven_strictAntiOn.antitoneOn
      (by change 1 < s; dsimp [Valid] at hs <;> linarith)
      (by change 1 < t; dsimp [Valid] at ht <;> linarith) hst
  | odd => exact phiOdd_antitone hst

end NumberTheoryLean.TwoStepDensityBounds

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_HighPrimeRemoval
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.OAI.Erdos970.NumberTheoryLean.ReferenceProductsBasics.availablePrimes_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace ErdosPrimeInputs.PrimePrefixMass

open _root_.Finset
open StrongChebyshev PrimeAbel PrimeEndpoints PrimeErrorDecay HarmonicPrimeMeasure

lemma sum_primesBetween {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∑ p ∈ primesBetween a b, (p : ℝ)⁻¹) = reciprocalPrimes a b := by
  rw [primesBetween, Finset.sum_filter]
  exact (reciprocal_eq_core ha hab).symm

lemma interval_open_closed {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    intervalSum false true a b = reciprocalPrimes a b := by
  classical
  rw [intervalSum, reciprocal_eq_core ha hab]
  apply Finset.sum_congr rfl
  intro p hp
  have hpb : (p : ℝ) ≤ b := (Nat.le_floor_iff (le_trans ha hab)).mp (Nat.mem_primesLE.mp hp).1
  simp [intervalGuard, hpb]

end ErdosPrimeInputs.PrimePrefixMass



namespace ErdosPrimeInputs.PrimePrefixTail

open _root_.Finset
open PrimePrefixMass

lemma prefixWeight_nonneg (l : List ℕ) : 0 ≤ prefixWeight l := by
  unfold prefixWeight
  apply List.prod_nonneg
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  positivity

lemma tilted_weight (l : List ℕ) :
    ((l.map (fun p : ℕ => 2 * (p : ℝ)⁻¹)).prod) = (2 : ℝ) ^ l.length * prefixWeight l := by
  induction l with
  | nil => simp [prefixWeight]
  | cons p l ih => simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ, prefixWeight] at ih ⊢; rw [ih]; ring

lemma sum_sorted_products (s : Finset ℕ) (f : ℕ → ℝ) :
    (∑ l ∈ decreasingPrefixes s, (l.map f).prod) = ∏ p ∈ s, (1 + f p) := by
  rw [decreasingPrefixes, Finset.sum_image]
  · have hp (t : Finset ℕ) : ((t.sort (· ≥ ·)).map f).prod = ∏ p ∈ t, f p := by
      simpa only [Finset.sort_toFinset] using (List.prod_toFinset f (t.sort_nodup (· ≥ ·))).symm
    simp_rw [hp]
    exact (Finset.prod_one_add s).symm
  · intro t ht u hu h
    simpa only [Finset.sort_toFinset] using congrArg List.toFinset h

lemma sum_tilted_weights (s : Finset ℕ) :
    (∑ l ∈ decreasingPrefixes s, (2 : ℝ) ^ l.length * prefixWeight l) =
      ∏ p ∈ s, (1 + 2 * (p : ℝ)⁻¹) := by
  simp_rw [← tilted_weight]
  exact sum_sorted_products s _

theorem longPrefixMass_le (s : Finset ℕ) (m : ℕ) :
    longPrefixMass s m ≤ Real.exp (2 * ∑ p ∈ s, (p : ℝ)⁻¹) / (2 : ℝ) ^ m := by
  apply (le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) m)).mpr
  rw [mul_comm, longPrefixMass, Finset.mul_sum]
  calc
    _ ≤ ∑ l ∈ (decreasingPrefixes s).filter (fun l => m ≤ l.length),
        (2 : ℝ) ^ l.length * prefixWeight l := by
      apply Finset.sum_le_sum
      intro l hl
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Finset.mem_filter.mp hl).2) (prefixWeight_nonneg l)
    _ ≤ ∑ l ∈ decreasingPrefixes s, (2 : ℝ) ^ l.length * prefixWeight l := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro l hl hnot
      exact mul_nonneg (pow_nonneg (by norm_num) _) (prefixWeight_nonneg l)
    _ = ∏ p ∈ s, (1 + 2 * (p : ℝ)⁻¹) := sum_tilted_weights s
    _ ≤ ∏ p ∈ s, Real.exp (2 * (p : ℝ)⁻¹) := by
      apply Finset.prod_le_prod
      · intro p hp
        positivity
      · intro p hp
        simpa only [add_comm] using Real.add_one_le_exp (2 * (p : ℝ)⁻¹)
    _ = _ := by rw [← Real.exp_sum, ← Finset.mul_sum]

end ErdosPrimeInputs.PrimePrefixTail



namespace ErdosPrimeInputs.LongPrimePaths

open _root_.Filter _root_.Asymptotics
open scoped Topology
open PrimeAbel PrimeEndpoints PrimeErrorDecay HarmonicPrimeMeasure PrimePrefixMass PrimePrefixTail

lemma fixed_tilt_tail (C A : ℝ) : ∀ᶠ B : ℝ in atTop, ∀ m : ℕ,
    (Real.log B) ^ 2 / 2 ≤ m →
      Real.exp (2 * (Real.log B + C)) / (2 : ℝ) ^ m ≤ B ^ (-A) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 (2 * (A + 2 + 2 * |C|) / Real.log 2)))] with B hB hL
  intro m hm
  have hb0 : 0 < B := lt_trans zero_lt_one hB
  have hl1 : 1 ≤ Real.log B := le_trans (le_max_left _ _) hL
  have hl0 : 0 ≤ Real.log B := le_trans zero_le_one hl1
  have ht : 2 * (A + 2 + 2 * |C|) ≤ Real.log B * Real.log 2 :=
    (div_le_iff₀ hlog2).mp (le_trans (le_max_right _ _) hL)
  have ht' := mul_le_mul_of_nonneg_right ht hl0
  have hm' := mul_le_mul_of_nonneg_right hm hlog2.le
  have hC' := mul_le_mul_of_nonneg_left hl1 (abs_nonneg C)
  have he : 2 * (Real.log B + C) - (m : ℝ) * Real.log 2 ≤ Real.log B * (-A) := by
    nlinarith [le_abs_self C]
  have hpow : (2 : ℝ) ^ m = Real.exp ((m : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [hpow, ← Real.exp_sub, Real.rpow_def_of_pos hb0]
  exact Real.exp_le_exp.mpr he

theorem long_prime_paths_superpolynomial : ∃ w₀ : ℝ, 1 < w₀ ∧
    ∀ A : ℝ, ∀ᶠ B : ℝ in atTop, ∀ w : ℝ, w₀ ≤ w → ∀ ell : ℝ,
      1 ≤ ell → ell ≤ B → ∀ m : ℕ, (Real.log B) ^ 2 / 2 ≤ m →
      longPrefixMass (primesBetween (w ^ ell) (w ^ B)) m ≤ B ^ (-A) := by
  obtain ⟨c, C, w₀, hc, hC, hw₀, h⟩ := harmonic_prime_measure
  refine ⟨w₀, hw₀, ?_⟩
  intro A
  filter_upwards [fixed_tilt_tail C A] with B htail
  intro w hw ell hell hB m hm
  have hw1 := lt_of_lt_of_le hw₀ hw
  have hwpos : 0 < w := lt_trans zero_lt_one hw1
  have hab : w ^ ell ≤ w ^ B := Real.rpow_le_rpow_of_exponent_le hw1.le hB
  have ha : 0 ≤ w ^ ell := (Real.rpow_pos_of_pos hwpos ell).le
  have hh := h w hw ell B (by linarith) hB false true
  rw [harmonicMass_eq_intervalSum hw1, interval_open_closed ha hab] at hh
  have hexp : Real.exp (-c * Real.sqrt (ell * Real.log w)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (Real.sqrt_nonneg _))
  have hsum : (∑ p ∈ primesBetween (w ^ ell) (w ^ B), (p : ℝ)⁻¹) ≤ Real.log B + C := by
    rw [sum_primesBetween ha hab]
    have hu := (abs_le.mp hh).2
    have he := mul_le_mul_of_nonneg_left hexp hC.le
    have hl := Real.log_nonneg hell
    linarith
  calc
    _ ≤ Real.exp (2 * ∑ p ∈ primesBetween (w ^ ell) (w ^ B), (p : ℝ)⁻¹) / (2 : ℝ) ^ m := longPrefixMass_le _ _
    _ ≤ Real.exp (2 * (Real.log B + C)) / (2 : ℝ) ^ m :=
      div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsum (by norm_num))) (by positivity)
    _ ≤ _ := htail m hm

end ErdosPrimeInputs.LongPrimePaths



namespace ErdosPrimeInputs.HighPrimeGeometry

open _root_.Finset
open HarmonicPrimeMeasure PrimePrefixMass

lemma remainingGap_append (r₀ w : ℝ) (pre suf : List ℕ) :
    remainingGap r₀ w (pre ++ suf) = remainingGap (remainingGap r₀ w pre) w suf := by
  simp only [remainingGap, List.map_append, List.sum_append]
  ring

lemma cutoff_lower (x : ℕ → ℝ) {ell B : ℝ} (hB : ell ≤ B) (l : List ℕ)
    (hl : ∀ p ∈ l, ell ≤ x p) : ell ≤ cutoff x B l := by
  induction l generalizing B with
  | nil => exact hB
  | cons p l ih =>
    exact ih (hl p (by simp)) (fun q hq => hl q (by simp [hq]))

lemma suffix_le_cutoff (x : ℕ → ℝ) (hx : Monotone x) (B : ℝ) (pre suf : List ℕ)
    (hdec : (pre ++ suf).Pairwise (· > ·))
    (hB : ∀ p ∈ pre ++ suf, x p ≤ B) :
    ∀ p ∈ suf, x p ≤ cutoff x B pre := by
  induction pre generalizing B with
  | nil => exact hB
  | cons q pre ih =>
    have hp := List.pairwise_cons.mp hdec
    apply ih (x q) hp.2
    intro p hmem
    exact hx (le_of_lt (hp.1 p hmem))

lemma sum_exponents_le (x : ℕ → ℝ) (l : List ℕ) (b : ℝ)
    (hl : ∀ p ∈ l, x p ≤ b) : (l.map x).sum ≤ (l.length : ℝ) * b := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have hp := hl p (by simp)
    have ht := ih (fun q hq => hl q (by simp [hq]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith

lemma prime_exponent_bounds {w ell B : ℝ} (hw : 1 < w) {p : ℕ}
    (hp : p ∈ primesBetween (w ^ ell) (w ^ B)) :
    ell < primeExponent w p ∧ primeExponent w p ≤ B := by
  obtain ⟨hp, hlow⟩ := Finset.mem_filter.mp hp
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.pos
  have hhigh : (p : ℝ) ≤ w ^ B :=
    (Nat.le_floor_iff (Real.rpow_pos_of_pos (lt_trans zero_lt_one hw) B).le).mp (Nat.mem_primesLE.mp hp).1
  exact ⟨(lt_exponent_iff hw hp0).mpr hlow, (exponent_le_iff hw hp0).mpr hhigh⟩

theorem high_short_gap {r₀ w B ell S : ℝ} (hw : 1 < w) (hell : 0 < ell)
    (hellB : ell ≤ B) (hS : 0 ≤ S) {l : List ℕ}
    (hl : l ∈ decreasingPrefixes (primesBetween (w ^ ell) (w ^ B)))
    (hhigh : hasHighState r₀ w B S l) (hshort : (l.length : ℝ) < S / 2) :
    S * ell / 2 < remainingGap r₀ w l := by
  obtain ⟨pre, suf, rfl, hh⟩ := hhigh
  obtain ⟨hdec, hmem⟩ := mem_decreasingPrefixes.mp hl
  have hB : ∀ p ∈ pre ++ suf, primeExponent w p ≤ B := fun p hp =>
    (prime_exponent_bounds hw (hmem p hp)).2
  have hlow : ∀ p ∈ pre, ell ≤ primeExponent w p := fun p hp =>
    (prime_exponent_bounds hw (hmem p (List.mem_append_left _ hp))).1.le
  have hb : ell ≤ primeCutoff w B pre := cutoff_lower (primeExponent w) hellB pre hlow
  have hb0 : 0 < primeCutoff w B pre := lt_of_lt_of_le hell hb
  have hcut := suffix_le_cutoff (primeExponent w) (exponent_monotone hw) B pre suf hdec hB
  have hsum := sum_exponents_le (primeExponent w) suf (primeCutoff w B pre) hcut
  have hlen : (suf.length : ℝ) ≤ (List.length (pre ++ suf) : ℝ) := by
    simp only [List.length_append, Nat.cast_add]
    linarith [Nat.cast_nonneg (α := ℝ) pre.length]
  have hmul := mul_le_mul_of_nonneg_right hlen hb0.le
  have hshortmul := mul_lt_mul_of_pos_right hshort hb0
  have hbase := mul_le_mul_of_nonneg_left hb hS
  have hh := (lt_div_iff₀ hb0).mp hh
  rw [remainingGap_append]
  unfold remainingGap
  change S * primeCutoff w B pre < r₀ - (pre.map (primeExponent w)).sum at hh
  nlinarith

theorem high_small_gap_long {r₀ w B ell S K : ℝ} (hw : 1 < w) (hell : 0 < ell)
    (hellB : ell ≤ B) (hS : 0 ≤ S) (hK : K ≤ S * ell / 2) {l : List ℕ}
    (hl : l ∈ decreasingPrefixes (primesBetween (w ^ ell) (w ^ B)))
    (hhigh : hasHighState r₀ w B S l) (hgap : remainingGap r₀ w l ≤ K) :
    S / 2 ≤ (l.length : ℝ) := by
  by_contra h
  have hs := high_short_gap hw hell hellB hS hl hhigh (lt_of_not_ge h)
  linarith

end ErdosPrimeInputs.HighPrimeGeometry



namespace ErdosPrimeInputs.HighPrimeMass

open _root_.Finset
open PrimePrefixMass PrimePrefixTail HighPrimeGeometry

theorem lowGapHighMass_le_long {r₀ w B ell S K : ℝ} (hw : 1 < w) (hell : 0 < ell)
    (hellB : ell ≤ B) (hS : 0 ≤ S) (hK : K ≤ S * ell / 2) :
    lowGapHighMass r₀ w B ell S K ≤
      longPrefixMass (primesBetween (w ^ ell) (w ^ B)) ⌈S / 2⌉₊ := by
  classical
  unfold lowGapHighMass longPrefixMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro l hl
    obtain ⟨hl, hgap, hhigh⟩ := Finset.mem_filter.mp hl
    exact Finset.mem_filter.mpr ⟨hl, Nat.ceil_le.mpr
      (high_small_gap_long hw hell hellB hS hK hl hhigh hgap)⟩
  · intro l hl hnot
    exact prefixWeight_nonneg l

end ErdosPrimeInputs.HighPrimeMass



namespace ErdosPrimeInputs.HighPrimeRemoval

open _root_.Filter _root_.Asymptotics
open scoped Topology
open PrimePrefixMass PrimePrefixTail LongPrimePaths HighPrimeGeometry HighPrimeMass

theorem low_gap_high_removal : ∃ w₀ : ℝ, 1 < w₀ ∧
    ∀ K : ℝ, 0 < K → ∀ A : ℝ, ∀ᶠ B : ℝ in atTop,
      ∀ w : ℝ, w₀ ≤ w → ∀ ell : ℝ, 1 ≤ ell → ell ≤ B → ∀ r₀ : ℝ,
        lowGapHighMass r₀ w B ell ((Real.log B) ^ 2) K ≤ B ^ (-A) := by
  obtain ⟨w₀, hw₀, htail⟩ := long_prime_paths_superpolynomial
  refine ⟨w₀, hw₀, ?_⟩
  intro K hK A
  filter_upwards [htail A,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2 * K + 1))] with B hB hlog
  intro w hw ell hell hellB r₀
  have hw1 : 1 < w := lt_of_lt_of_le hw₀ hw
  have hell0 : 0 < ell := lt_of_lt_of_le zero_lt_one hell
  have hsmall : K ≤ (Real.log B) ^ 2 / 2 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_left hell (sq_nonneg (Real.log B))
  have hsmall' : K ≤ (Real.log B) ^ 2 * ell / 2 := by nlinarith
  exact (lowGapHighMass_le_long hw1 hell0 hellB (sq_nonneg _) hsmall').trans
    (hB w hw ell hell hellB _ (Nat.le_ceil _))

end ErdosPrimeInputs.HighPrimeRemoval


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeRatioBins
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSingletonClassChainState _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.OAI.Erdos970.NumberTheoryLean.ReferenceBenchmarkDecay.benchmark_even_below_two
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.PrimeTiltGeometry

open _root_.Erdos970.Set
open FinitePathGeometry ErdosPrimeInputs.HarmonicPrimeMeasure

theorem prime_tilt_step_identity {w ell S s r cap : ℝ} {i : Side} {closed : Bool} {p : ℕ}
    (hell : 0 ≤ ell) (hr : 0 < r) (hs : Valid i s) (hp : p ∈ children w ell S i s r cap closed) :
    (p : ℝ)⁻¹ = primeTilt w r i s p * ((r - primeExponent w p)/r)^2 *
      (weight i s / weight i.flip (childRatio w r p)) := by
  have ht := valid_pos (child_valid hs hp)
  have hw := weight_pos hs
  have hw' := weight_pos (child_valid hs hp)
  rw [← nextGap_childRatio hr (child_exponent_positive hell hp) ht]
  unfold primeTilt nextGap
  field_simp [hr.ne', ht.ne', hw.ne', hw'.ne']

end NumberTheoryLean.PrimeTiltGeometry

end

section

namespace NumberTheoryLean.PrimeTiltPrefixes

open _root_.Erdos970.Set
open FinitePathGeometry PrimeTiltGeometry ErdosPrimeInputs.HarmonicPrimeMeasure
open ErdosPrimeInputs.PrimePrefixMass

theorem ratios_admissible {w ell S s r cap : ℝ} {i : Side} {closed : Bool} {ps : List ℕ}
    (hpath : PrimeAdmissible w ell S i s r cap closed ps) : Admissible i s (primeRatios w r ps) := by
  classical
  induction ps generalizing i s r cap closed with
  | nil => trivial
  | cons p ps ih =>
    rcases hpath with ⟨hp,hps⟩
    exact ⟨(Finset.mem_filter.mp hp).2.2.2.1, ih hps⟩

theorem primeFinalGap_eq {w ell S s r cap : ℝ} {i : Side} {closed : Bool} {ps : List ℕ}
    (hell : 0 ≤ ell) (hr : 0 < r) (hs : Valid i s)
    (hpath : PrimeAdmissible w ell S i s r cap closed ps) :
    primeFinalGap w r ps = finalGap r (primeRatios w r ps) := by
  induction ps generalizing i s r cap closed with
  | nil => rfl
  | cons p ps ih =>
    rcases hpath with ⟨hp,hps⟩
    simp only [primeFinalGap, primeRatios, finalGap]
    rw [nextGap_childRatio hr (child_exponent_positive hell hp) (valid_pos (child_valid hs hp))]
    exact ih (child_gap_positive hell hr hs hp) (child_valid hs hp) hps

theorem prime_prefix_weight_identity {w ell S s r cap : ℝ} {i : Side} {closed : Bool} {ps : List ℕ}
    (hell : 0 ≤ ell) (hr : 0 < r) (hs : Valid i s)
    (hpath : PrimeAdmissible w ell S i s r cap closed ps) :
    prefixWeight ps = tiltProduct w i s r ps * (primeFinalGap w r ps / r)^2 *
      (weight i s / weight (finalSide i (primeRatios w r ps)) (finalRatio s (primeRatios w r ps))) := by
  induction ps generalizing i s r cap closed with
  | nil =>
    simp only [prefixWeight, List.map_nil, List.prod_nil, tiltProduct, primeFinalGap, primeRatios, finalSide, finalRatio]
    rw [div_self hr.ne', div_self (weight_pos hs).ne']
    norm_num
  | cons p ps ih =>
    rcases hpath with ⟨hp,hps⟩
    have hr' := child_gap_positive hell hr hs hp
    have hs' := child_valid hs hp
    have hi := ih hr' hs' hps
    have hf := weight_pos (valid_final hs' (ratios_admissible hps))
    have hstep := prime_tilt_step_identity hell hr hs hp
    simp only [prefixWeight, List.map_cons, List.prod_cons] at ⊢
    change (p : ℝ)⁻¹ * prefixWeight ps = _
    rw [hi, hstep]
    simp only [tiltProduct, primeFinalGap, primeRatios, finalSide, finalRatio]
    field_simp [hr.ne', hr'.ne', (weight_pos hs').ne', hf.ne']

theorem normalized_product_correction {e : ℝ} (he : 0 ≤ e) (w : ℝ) (i : Side) (s r : ℝ) (ps : List ℕ) :
    normalizedTiltProduct e w i s r ps * (1+e)^ps.length = tiltProduct w i s r ps := by
  induction ps generalizing i s r with
  | nil => simp [normalizedTiltProduct, tiltProduct]
  | cons p ps ih =>
    simp only [normalizedTiltProduct, tiltProduct, List.length_cons, pow_succ]
    rw [show (primeTilt w r i s p / (1+e)) * normalizedTiltProduct e w i.flip (childRatio w r p) (r-primeExponent w p) ps *
      ((1+e)^ps.length * (1+e)) = primeTilt w r i s p *
        (normalizedTiltProduct e w i.flip (childRatio w r p) (r-primeExponent w p) ps * (1+e)^ps.length) by
          field_simp [show 1+e ≠ 0 by linarith]]
    rw [ih]

theorem normalized_prime_prefix_weight_identity {w ell S s r cap e : ℝ} {i : Side} {closed : Bool} {ps : List ℕ}
    (he : 0 ≤ e) (hell : 0 ≤ ell) (hr : 0 < r) (hs : Valid i s)
    (hpath : PrimeAdmissible w ell S i s r cap closed ps) :
    prefixWeight ps = normalizedTiltProduct e w i s r ps * (1+e)^ps.length * (primeFinalGap w r ps / r)^2 *
      (weight i s / weight (finalSide i (primeRatios w r ps)) (finalRatio s (primeRatios w r ps))) := by
  rw [normalized_product_correction he]
  exact prime_prefix_weight_identity hell hr hs hpath

end NumberTheoryLean.PrimeTiltPrefixes

end

section

namespace NumberTheoryLean.PrimeHistories

open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open FinitePathGeometry PrimeTiltGeometry PrimeTiltPrefixes
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem terminal_append (w : ℝ) (z : Node) (ps qs : List ℕ) :
    terminal w z (ps++qs) = terminal w (terminal w z ps) qs := by
  exact List.foldl_append

theorem terminal_gap_eq (w : ℝ) (z : Node) (ps : List ℕ) :
    (terminal w z ps).gap = primeFinalGap w z.gap ps := by
  induction ps generalizing z with
  | nil => rfl
  | cons p ps ih => simpa only [terminal_cons, primeFinalGap, step] using ih (step w z p)

theorem terminal_ratio_eq (w : ℝ) (z : Node) (ps : List ℕ) :
    (terminal w z ps).ratio = finalRatio z.ratio (primeRatios w z.gap ps) := by
  induction ps generalizing z with
  | nil => rfl
  | cons p ps ih => simpa only [terminal_cons, primeRatios, finalRatio, step] using ih (step w z p)

theorem terminal_side_eq (w : ℝ) (z : Node) (ps : List ℕ) :
    (terminal w z ps).side = finalSide z.side (primeRatios w z.gap ps) := by
  induction ps generalizing z with
  | nil => rfl
  | cons p ps ih => simpa only [terminal_cons, primeRatios, finalSide, step] using ih (step w z p)

namespace History

variable {w ell S : ℝ} {start : Node}

theorem append_node (h : History w ell S start) (p : ℕ) (hp : p ∈ nodeChildren w ell S h.node) :
    (h.append p hp).node = step w h.node p := by
  change terminal w start (h.primes ++ [p]) = _
  rw [terminal_append, terminal_cons, terminal_nil]
  rfl

end History
end NumberTheoryLean.PrimeHistories

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_LowStateHorizon
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.LowStateHorizon

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostGrouping
open ArrivalKernelGeometry RegeneratingInverseBands HarmonicWeightKernel

 theorem cost_ge_inv_add_one {t : ℝ} (ht : 0 < t) : 1 / (t + 1) ≤ cost t := by
  have hx : 0 < 1 + 1 / t := by positivity
  have h := Real.one_sub_inv_le_log_of_pos hx
  have heq : 1 - (1 + 1 / t)⁻¹ = 1 / (t + 1) := by
    field_simp [ht.ne', hx.ne', show t + 1 ≠ 0 by linarith]
    ring
  rw [heq] at h
  exact h

theorem source_horizon_log_cube {B : ℝ} (hB : 2 ≤ Real.log B) :
    ((sourceHorizon ((Real.log B) ^ 2) B : ℕ) : ℝ) ≤ 5 * (Real.log B) ^ 3 := by
  let x := Real.log B
  have hx : 2 ≤ x := hB
  have hpos : 0 ≤ (x ^ 2 + 1) * (x + 2) := by positivity
  have hc := (Nat.ceil_lt_add_one hpos).le
  change ((⌈(x ^ 2 + 1) * (x + 2)⌉₊ + 1 : ℕ) : ℝ) ≤ 5 * x ^ 3
  push_cast
  have h2 : 0 ≤ (x - 2) * x := mul_nonneg (by linarith) (by linarith)
  have h3 : 0 ≤ (x - 2) * x ^ 2 := mul_nonneg (by linarith) (sq_nonneg x)
  nlinarith

end NumberTheoryLean.LowStateHorizon

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeGridGeometry
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.OAI.Erdos970.NumberTheoryLean.ReferenceBenchmarkDecay.benchmark_even_below_two
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace NumberTheoryLean.PrimeKilledChain

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltGeometry PrimeHistories PrimeRowNormalization

 theorem normalizationRate_pos : 0 < normalizationRate :=
  (Classical.choose_spec (Classical.choose_spec retained_row_mass_one_add)).1

theorem normalizationThreshold_gt_one : 1 < normalizationThreshold :=
  (Classical.choose_spec (Classical.choose_spec retained_row_mass_one_add)).2.1

variable (w ell S : ℝ) (start : Node)

variable {w ell S : ℝ} {start : Node}

theorem pathLaw_isProbability (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell)
    (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
    (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S) (n : ℕ) :
    IsProbabilityMeasure (pathLaw w ell S start n) := by
  let := chain_isMarkov hw hell hS0 hS hr hs hsS
  unfold pathLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end NumberTheoryLean.PrimeKilledChain



namespace NumberTheoryLean.PrimeChainProbabilities

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltGeometry PrimeTiltPrefixes PrimeHistories PrimeKilledChain

variable {w ell S : ℝ} {start : Node}

theorem history_append_eq_iff (h k : History w ell S start) (p q : ℕ)
    (hp : p ∈ nodeChildren w ell S h.node) (hq : q ∈ nodeChildren w ell S k.node) :
    h.append p hp = k.append q hq ↔ h = k ∧ p = q := by
  constructor
  · intro heq
    have hl := congrArg History.primes heq
    have hh := List.append_singleton_inj.mp hl
    exact ⟨History.ext hh.1,hh.2⟩
  · rintro ⟨rfl,rfl⟩
    exact History.ext rfl

theorem liveLaw_at_append (g h : History w ell S start) (p : ℕ)
    (hp : p ∈ nodeChildren w ell S h.node) :
    liveLaw w ell S start g {some (h.append p hp)} =
      ({h} : Set (History w ell S start)).indicator (fun _ => childProbability w ell S start h p) g := by
  classical
  simp only [liveLaw, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply,
    Set.indicator, Set.mem_singleton_iff, Pi.one_apply, Option.some.injEq, history_append_eq_iff,
    mul_ite, mul_one, mul_zero]
  by_cases hgh : g = h
  · subst g
    simp only [true_and, ite_true, if_true]
    calc
      _ = ∑ q ∈ nodeChildren w ell S h.node, if q = p then childProbability w ell S start h q else 0 :=
        Finset.sum_attach _ (fun q : ℕ => if q = p then childProbability w ell S start h q else 0)
      _ = _ := by simp [hp]
  · simp [hgh]

theorem chain_at_append (h : History w ell S start) (p : ℕ)
    (hp : p ∈ nodeChildren w ell S h.node) (z : ChainState w ell S start) :
    chain w ell S start z {some (h.append p hp)} =
      ({some h} : Set (ChainState w ell S start)).indicator (fun _ => childProbability w ell S start h p) z := by
  classical
  cases z with
  | none => simp [chain_none, Set.indicator]
  | some g =>
    rw [chain_some, completedLaw, Measure.add_apply, liveLaw_at_append, Measure.smul_apply]
    simp [Set.indicator]

theorem pathLaw_append (n : ℕ) (h : History w ell S start) (p : ℕ)
    (hp : p ∈ nodeChildren w ell S h.node) :
    pathLaw w ell S start (n+1) {some (h.append p hp)} =
      childProbability w ell S start h p * pathLaw w ell S start n {some h} := by
  unfold pathLaw
  have hpow : (chain w ell S start)^(n+1) = (chain w ell S start) ∘ₖ ((chain w ell S start)^n) := pow_succ' _ _
  rw [hpow, Kernel.comp_apply' _ _ _ (measurableSet_singleton _)]
  calc
    _ = ∫⁻ z, ({some h} : Set (ChainState w ell S start)).indicator
        (fun _ => childProbability w ell S start h p) z ∂((chain w ell S start)^n) (some History.empty) :=
      lintegral_congr (fun z => chain_at_append h p hp z)
    _ = _ := by rw [lintegral_indicator (measurableSet_singleton _), lintegral_const, Measure.restrict_apply_univ]

theorem nodeProduct_append (e w : ℝ) (z : Node) (ps qs : List ℕ) :
    nodeProduct e w z (ps++qs) = nodeProduct e w z ps * nodeProduct e w (terminal w z ps) qs := by
  induction ps generalizing z with
  | nil => simp [nodeProduct, normalizedTiltProduct, terminal]
  | cons p ps ih =>
    change (primeTilt w z.gap z.side z.ratio p / (1+e)) * nodeProduct e w (step w z p) (ps++qs) =
      ((primeTilt w z.gap z.side z.ratio p / (1+e)) * nodeProduct e w (step w z p) ps) *
        nodeProduct e w (terminal w (step w z p) ps) qs
    rw [ih, mul_assoc]

theorem nodeProduct_nonnegative {e : ℝ} (he : 0 ≤ e) {z : Node} {ps : List ℕ}
    (hs : Valid z.side z.ratio) (hp : allowed w ell S z ps) : 0 ≤ nodeProduct e w z ps := by
  induction ps generalizing z with
  | nil => exact zero_le_one
  | cons p ps ih =>
    rcases (allowed_cons w ell S z p ps).mp hp with ⟨hchild,hrest⟩
    change 0 ≤ (primeTilt w z.gap z.side z.ratio p / (1+e)) * nodeProduct e w (step w z p) ps
    exact mul_nonneg (div_nonneg (primeTilt_nonneg hs hchild) (by linarith)) (ih (child_valid hs hchild) hrest)

theorem pathLaw_singleton_weight (hs : Valid start.side start.ratio) (h : History w ell S start) :
    pathLaw w ell S start h.primes.length {some h} = ENNReal.ofReal (nodeProduct (epsilon w) w start h.primes) := by
  classical
  have main : ∀ ps : List ℕ, ∀ h : History w ell S start, h.primes = ps →
      pathLaw w ell S start ps.length {some h} = ENNReal.ofReal (nodeProduct (epsilon w) w start ps) := by
    intro ps
    induction ps using List.reverseRecOn with
    | nil =>
      intro h heq
      have hh : h = History.empty := History.ext heq
      subst h
      change Measure.dirac (some (History.empty : History w ell S start)) {some History.empty} = ENNReal.ofReal (1 : ℝ)
      simp
    | append_singleton ps p ih =>
      intro h heq
      have hall : allowed w ell S start (ps++[p]) := heq ▸ h.admissible
      obtain ⟨hpre,hlast⟩ := (allowed_append w ell S start ps [p]).mp hall
      let g : History w ell S start := ⟨ps,hpre⟩
      have hp : p ∈ nodeChildren w ell S g.node := (allowed_cons w ell S g.node p []).mp hlast |>.1
      have hh : h = g.append p hp := History.ext heq
      rw [hh, List.length_append, List.length_singleton, pathLaw_append, ih g rfl, nodeProduct_append]
      have hgn : Valid g.node.side g.node.ratio := terminal_valid hs g.admissible
      have hn : 0 ≤ primeTilt w g.node.gap g.node.side g.node.ratio p / (1+epsilon w) :=
        div_nonneg (primeTilt_nonneg (w := w) (r := g.node.gap) (i := g.node.side) (s := g.node.ratio) hgn hp) (normalizer_pos w).le
      change ENNReal.ofReal (primeTilt w g.node.gap g.node.side g.node.ratio p / (1+epsilon w)) *
          ENNReal.ofReal (nodeProduct (epsilon w) w start ps) =
        ENNReal.ofReal (nodeProduct (epsilon w) w start ps *
          (primeTilt w g.node.gap g.node.side g.node.ratio p / (1+epsilon w) * 1))
      rw [← ENNReal.ofReal_mul hn]
      congr 1
      ring
  exact main h.primes h rfl

theorem source_prime_weight_identity (hell : 0 ≤ ell) (hr : 0 < start.gap)
    (hs : Valid start.side start.ratio) (h : History w ell S start) :
    ErdosPrimeInputs.PrimePrefixMass.prefixWeight h.primes =
      (pathLaw w ell S start h.primes.length {some h}).toReal * (1+epsilon w)^h.primes.length *
        (h.node.gap/start.gap)^2 * (weight start.side start.ratio / weight h.node.side h.node.ratio) := by
  rw [pathLaw_singleton_weight hs h, ENNReal.toReal_ofReal (nodeProduct_nonnegative (epsilon_pos w).le hs h.admissible)]
  have hweight := normalized_prime_prefix_weight_identity (epsilon_pos w).le hell hr hs h.admissible
  simpa only [nodeProduct, History.node, terminal_gap_eq, terminal_side_eq, terminal_ratio_eq] using hweight

end NumberTheoryLean.PrimeChainProbabilities



namespace NumberTheoryLean.PrimeCompactVisits

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeTiltGeometry

variable {w ell S : ℝ} {start : Node}

theorem visit_nonneg (K : ℝ) (z : ChainState w ell S start) : 0 ≤ visit K z := by
  cases z with
  | none => exact le_rfl
  | some h => simp only [visit]; split_ifs <;> norm_num

theorem potential_nonneg {K : ℝ} (hK : 0 ≤ K) (hell : 0 ≤ ell)
    (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (z : ChainState w ell S start) :
    0 ≤ potential K z := by
  cases z with
  | none => exact le_rfl
  | some h =>
    have hg : 0 < h.node.gap := terminal_gap_positive hell hr hs h.admissible
    exact add_nonneg (le_min hg.le hK) zero_le_one

theorem potential_le {K : ℝ} (hK : 0 ≤ K) (z : ChainState w ell S start) :
    potential K z ≤ K+1 := by
  cases z with
  | none => change (0:ℝ) ≤ K+1; linarith
  | some h => exact add_le_add_left (min_le_right _ _) 1

theorem visit_le_potential {K : ℝ} (hK : 0 ≤ K) (hell : 0 ≤ ell)
    (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (z : ChainState w ell S start) :
    visit K z ≤ potential K z := by
  cases z with
  | none => exact le_rfl
  | some h =>
    have hg : 0 < h.node.gap := terminal_gap_positive hell hr hs h.admissible
    simp only [visit,potential]
    split_ifs with hle
    · rw [min_eq_left hle]; linarith
    · exact add_nonneg (le_min hg.le hK) zero_le_one

theorem child_potential_drift {K : ℝ} (hell : 1 ≤ ell)
    (h : History w ell S start) (p : ℕ) (hp : p ∈ nodeChildren w ell S h.node) :
    visit K (some h) + potential K (some (h.append p hp)) ≤ potential K (some h) := by
  classical
  have he : ell < ErdosPrimeInputs.HarmonicPrimeMeasure.primeExponent w p :=
    (Finset.mem_filter.mp hp).2.1
  simp only [visit,potential,History.append_node,step]
  split_ifs with hle
  · rw [min_eq_left hle]
    have hm := min_le_left (h.node.gap-ErdosPrimeInputs.HarmonicPrimeMeasure.primeExponent w p) K
    linarith
  · rw [min_eq_right (le_of_not_ge hle)]
    have hm := min_le_right (h.node.gap-ErdosPrimeInputs.HarmonicPrimeMeasure.primeExponent w p) K
    linarith

variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell)
    (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
    (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

include hell hr hs in

theorem actual_row_drift_ae {K : ℝ} (hK : 0 ≤ K) (z : ChainState w ell S start) :
    ∀ᵐ y ∂chain w ell S start z, visit K z + potential K y ≤ potential K z := by
  classical
  cases z with
  | none =>
    rw [chain_none]
    exact (ae_dirac_iff (by trivial)).mpr (by simp [visit,potential])
  | some h =>
    have hdead : visit K (some h) + potential K (none : ChainState w ell S start) ≤ potential K (some h) := by
      simpa only [potential,add_zero] using visit_le_potential hK (by linarith : 0 ≤ ell) hr hs (some h)
    have hchild := child_potential_drift (K := K) hell h
    apply ae_iff.mpr
    simp [chain_some,completedLaw,liveLaw,hdead,hchild]

end NumberTheoryLean.PrimeCompactVisits



namespace NumberTheoryLean.PrimeHistoryHorizon

open _root_.Set _root_.Finset
open _root_.Erdos970.Set
open FinitePathGeometry PrimeTiltGeometry PrimeTiltPrefixes PrimeHistories
open LowStateHorizon ErdosPrimeInputs.HarmonicPrimeMeasure

theorem valid_ratio_lower {i : Side} {t : ℝ} (ht : Valid i t) : (19/20 : ℝ) ≤ t := by
  cases i <;> dsimp [Valid] at ht <;> linarith

theorem prime_cost_lower {w ell S s r cap : ℝ} {i : Side} {closed : Bool} {ps : List ℕ}
    (hs : Valid i s) (hpath : PrimeAdmissible w ell S i s r cap closed ps) :
    (ps.length : ℝ)/(S+1) ≤ pathCost (primeRatios w r ps) := by
  classical
  induction ps generalizing i s r cap closed with
  | nil => simp [primeRatios,pathCost]
  | cons p ps ih =>
    rcases hpath with ⟨hp,hrest⟩
    have ht := valid_pos (child_valid hs hp)
    have htS : childRatio w r p ≤ S := (Finset.mem_filter.mp hp).2.2.2.2
    have hc : 1/(S+1) ≤ cost (childRatio w r p) :=
      (one_div_le_one_div_of_le (by linarith : 0 < childRatio w r p+1) (by linarith)).trans
        (cost_ge_inv_add_one ht)
    have hih := ih (child_valid hs hp) hrest
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, add_div, primeRatios, pathCost]
    linarith

theorem prime_gap_cost {w ell S s r cap : ℝ} {i : Side} {closed : Bool} {ps : List ℕ}
    (hell : 0 ≤ ell) (hr : 0 < r) (hs : Valid i s)
    (hpath : PrimeAdmissible w ell S i s r cap closed ps) :
    primeFinalGap w r ps = r * Real.exp (-pathCost (primeRatios w r ps)) := by
  rw [primeFinalGap_eq hell hr hs hpath, finalGap_eq_cost hs (ratios_admissible hpath)]

theorem prime_final_gap_lower {w ell S s r cap : ℝ} {i : Side} {closed : Bool} {ps : List ℕ}
    (hell : 0 < ell) (hr : 0 < r) (hs : Valid i s)
    (hpath : PrimeAdmissible w ell S i s r cap closed ps) (hne : ps ≠ []) :
    (19/20 : ℝ)*ell < primeFinalGap w r ps := by
  classical
  induction ps generalizing i s r cap closed with
  | nil => exact False.elim (hne rfl)
  | cons p ps ih =>
    rcases hpath with ⟨hp,hrest⟩
    cases ps with
    | nil =>
      have hx : ell < primeExponent w p := (Finset.mem_filter.mp hp).2.1
      have hx0 : 0 < primeExponent w p := hell.trans hx
      have ht := valid_ratio_lower (child_valid hs hp)
      have heq : r-primeExponent w p = childRatio w r p * primeExponent w p := by
        unfold childRatio
        field_simp
      change (19/20 : ℝ)*ell < r-primeExponent w p
      calc
        _ < (19/20 : ℝ)*primeExponent w p := mul_lt_mul_of_pos_left hx (by norm_num)
        _ ≤ childRatio w r p * primeExponent w p := mul_le_mul_of_nonneg_right ht hx0.le
        _ = _ := heq.symm
    | cons q qs =>
      exact ih (child_gap_positive hell.le hr hs hp) (child_valid hs hp) hrest (by simp)

theorem prime_source_horizon {w ell S s r cap B : ℝ} {i : Side} {closed : Bool} {ps : List ℕ}
    (hell : 1 ≤ ell) (hS : 0 ≤ S) (hr : 0 < r) (hs : Valid i s)
    (hpath : PrimeAdmissible w ell S i s r cap closed ps) (hB : 0 < B) (hsize : r ≤ (23/10 : ℝ)*B) :
    ps.length < sourceHorizon S B := by
  by_cases hne : ps = []
  · subst ps
    unfold sourceHorizon
    simp
  · have hell0 : 0 < ell := by linarith
    have hgap := prime_final_gap_lower hell0 hr hs hpath hne
    have hl := Real.log_lt_log (mul_pos (by norm_num : (0 : ℝ) < 19/20) hell0) hgap
    rw [prime_gap_cost hell0.le hr hs hpath,
      Real.log_mul hr.ne' (Real.exp_pos _).ne', Real.log_exp] at hl
    have hc := prime_cost_lower hs hpath
    have hlogR := Real.log_le_log hr hsize
    rw [Real.log_mul (by norm_num : (23/10 : ℝ) ≠ 0) hB.ne'] at hlogR
    have hlog23 : Real.log (23/10 : ℝ) ≤ 13/10 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 23/10)
      norm_num at h
      exact h
    have hlog19 : (-1/19 : ℝ) ≤ Real.log (19/20 : ℝ) := by
      have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 19/20)
      norm_num at h
      linarith
    have hlogell : Real.log (19/20 : ℝ) ≤ Real.log ((19/20 : ℝ)*ell) :=
      Real.log_le_log (by norm_num) (by nlinarith)
    have hn : (ps.length : ℝ)/(S+1) < Real.log B+2 := by linarith
    have hmul := (div_lt_iff₀ (by linarith : 0 < S+1)).mp hn
    have hceil := Nat.le_ceil ((S+1)*(Real.log B+2))
    have hreal : (ps.length : ℝ) < (sourceHorizon S B : ℝ) := by
      unfold sourceHorizon
      push_cast
      nlinarith
    exact_mod_cast hreal

theorem history_length_lt {w ell S B : ℝ} {start : Node}
    (hell : 1 ≤ ell) (hS : 0 ≤ S) (hr : 0 < start.gap) (hs : Valid start.side start.ratio)
    (hB : 0 < B) (hsize : start.gap ≤ (23/10 : ℝ)*B) (h : History w ell S start) :
    h.primes.length < sourceHorizon S B :=
  prime_source_horizon hell hS hr hs h.admissible hB hsize

end NumberTheoryLean.PrimeHistoryHorizon



namespace NumberTheoryLean.PrimeChainHorizon

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeHistoryHorizon LowStateHorizon

variable {w ell S : ℝ} {start : Node}

theorem stage_measurable (n : ℕ) : MeasurableSet {z : ChainState w ell S start | stage n z} := trivial

theorem next_stage (n : ℕ) (z : ChainState w ell S start) (hz : stage n z) :
    ∀ᵐ y ∂chain w ell S start z, stage (n+1) y := by
  classical
  cases z with
  | none =>
    rw [chain_none]
    exact (ae_dirac_iff (stage_measurable (n+1))).mpr trivial
  | some h =>
    have hlen : h.primes.length = n := hz
    apply ae_iff.mpr
    simp [chain_some, completedLaw, liveLaw, stage, History.append_primes, hlen]

theorem pathLaw_stage (n : ℕ) : ∀ᵐ z ∂pathLaw w ell S start n, stage n z := by
  induction n with
  | zero =>
    change ∀ᵐ z ∂Measure.dirac (some (History.empty : History w ell S start)), stage 0 z
    exact (ae_dirac_iff (stage_measurable 0)).mpr rfl
  | succ n ih =>
    have hp : (chain w ell S start)^(n+1) = (chain w ell S start) ∘ₖ ((chain w ell S start)^n) := pow_succ' _ _
    change ∀ᵐ z ∂((chain w ell S start)^(n+1)) (some History.empty), stage (n+1) z
    rw [hp]
    apply Kernel.ae_comp_of_ae_ae (stage_measurable (n+1))
    filter_upwards [ih] with z hz
    exact next_stage n z hz

end NumberTheoryLean.PrimeChainHorizon



namespace NumberTheoryLean.PrimeCorrectionFactor

open _root_.Filter _root_.Set
open _root_.Erdos970.Filter _root_.Erdos970.Set
open scoped Topology
open FinitePathGeometry PrimeHistories PrimeHistoryHorizon PrimeKilledChain LowStateHorizon

theorem correctionBudget_tendsto_zero (d : ℝ) : Tendsto (correctionBudget d) atTop (𝓝 0) := by
  have ht : Tendsto (fun x : ℝ => 5*d^3*x^6*Real.exp (-normalizationRate*x)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (6 : ℝ) normalizationRate normalizationRate_pos).const_mul (5*d^3)
    simpa only [Real.rpow_ofNat, mul_assoc, mul_zero] using h
  have hi : Tendsto (fun w : ℝ => 5*d^3*(Real.log w)^3*epsilon w) atTop (𝓝 0) := by
    apply Tendsto.congr' _ (ht.comp (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop))
    filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (0 : ℝ))] with w hw
    have hp : (Real.sqrt (Real.log w))^6 = (Real.log w)^3 := by
      calc
        _ = ((Real.sqrt (Real.log w))^2)^3 := by ring
        _ = _ := by rw [Real.sq_sqrt hw]
    simp only [Function.comp_apply, epsilon, hp]
  have h := ((Real.continuous_exp.tendsto (0 : ℝ)).comp hi).sub_const 1
  change Tendsto (fun w : ℝ => Real.exp (5*d^3*(Real.log w)^3*epsilon w)-1) atTop (𝓝 0)
  simpa only [Function.comp_apply, Real.exp_zero, sub_self] using h

theorem correction_le_budget {d w B : ℝ} (hB : 2 ≤ Real.log B) (hcomp : Real.log B ≤ d*Real.log w) (n : ℕ)
    (hn : n ≤ sourceHorizon ((Real.log B)^2) B) :
    0 ≤ (1+epsilon w)^n-1 ∧ (1+epsilon w)^n-1 ≤ correctionBudget d w := by
  have hpow1 : 1 ≤ (1+epsilon w)^n := one_le_pow₀ (by linarith [epsilon_pos w])
  have hN := source_horizon_log_cube hB
  have hnR : (n : ℝ) ≤ (sourceHorizon ((Real.log B)^2) B : ℝ) := by exact_mod_cast hn
  have hcube : (Real.log B)^3 ≤ (d*Real.log w)^3 := pow_le_pow_left₀ (by linarith) hcomp 3
  have hnum : (n : ℝ) ≤ 5*d^3*(Real.log w)^3 := by nlinarith [hN,hnR]
  have hbase : 1+epsilon w ≤ Real.exp (epsilon w) := by
    simpa only [add_comm] using Real.add_one_le_exp (epsilon w)
  have hp : (1+epsilon w)^n ≤ (Real.exp (epsilon w))^n := pow_le_pow_left₀ (by linarith [epsilon_pos w]) hbase n
  rw [← Real.exp_nat_mul] at hp
  have he : Real.exp ((n : ℝ)*epsilon w) ≤ Real.exp (5*d^3*(Real.log w)^3*epsilon w) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hnum (epsilon_pos w).le)
  exact ⟨sub_nonneg.mpr hpow1, sub_le_sub_right (hp.trans he) 1⟩

theorem history_correction {d w ell B : ℝ} {start : Node}
    (hlogB : 2 ≤ Real.log B)
    (hcomp : Real.log B ≤ d*Real.log w) (hell : 1 ≤ ell) (hr : 0 < start.gap)
    (hs : Valid start.side start.ratio) (hB : 0 < B) (hsize : start.gap ≤ (23/10 : ℝ)*B)
    (h : History w ell ((Real.log B)^2) start) :
    0 ≤ (1+epsilon w)^h.primes.length-1 ∧
      (1+epsilon w)^h.primes.length-1 ≤ correctionBudget d w :=
  correction_le_budget hlogB hcomp h.primes.length
    (history_length_lt hell (sq_nonneg _) hr hs hB hsize h).le

end NumberTheoryLean.PrimeCorrectionFactor



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_CemeteryHistoryLaw
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.CemeteryKernel

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

theorem complete_isMarkov (K : Kernel α α) (hK : ∀ x, K x univ ≤ 1) : IsMarkovKernel (complete K) := by
  constructor
  intro z
  constructor
  cases z with
  | inl x =>
    rw [complete_live, liveRow_apply, Measure.add_apply, Measure.map_apply measurable_inl MeasurableSet.univ,
      Set.preimage_univ, Measure.smul_apply]
    simp only [measure_univ, smul_eq_mul, mul_one]
    exact add_tsub_cancel_of_le (hK x)
  | inr u =>
    cases u
    change Measure.dirac (dead : Space α) univ = 1
    exact measure_univ

end NumberTheoryLean.CemeteryKernel

end

section

namespace NumberTheoryLean.CemeteryHistoryMap

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open CemeteryKernel FiniteHistoryTransport

variable {X : Type*} [MeasurableSpace X]
variable (K : Kernel X X) [IsMarkovKernel K] {E : Set X} (hE : MeasurableSet E)

instance restricted_complete_markov : IsMarkovKernel (complete (K.restrict hE)) := by
  apply complete_isMarkov
  intro x
  rw [Kernel.restrict_apply,Measure.restrict_apply_univ]
  exact (measure_mono (subset_univ E)).trans_eq (measure_univ (μ := K x))

end NumberTheoryLean.CemeteryHistoryMap

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_CompletedParentInterval
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ContinuousKilledBins

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PairedCostGrouping ArrivalKernelGeometry
open LowStateHorizon RegeneratingInverseBands KernelDensityBridge ContinuousRatioBins

instance continuousChain_isMarkov (v ell S : ℝ) : IsMarkovKernel (continuousChain v ell S) := by
  apply CemeteryKernel.complete_isMarkov
  intro z
  rw [lowKernel, Kernel.restrict_apply, Measure.restrict_apply_univ]
  calc
    _ ≤ costKernel z univ := measure_mono (subset_univ _)
    _ = 1 := measure_univ

end NumberTheoryLean.ContinuousKilledBins

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeCompactWeights
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.OAI.Erdos970.NumberTheoryLean.ReferenceBenchmarkDecay.benchmark_even_below_two
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.PrimeBinMembership

open _root_.Set _root_.Finset
open FinitePathGeometry PrimeTiltGeometry PrimeTiltPrefixes PrimeHistories
open PrimeRatioBins NormalizedPrimeBins PrimeKilledChain
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem step_consistent {w ell S : ℝ} {z : Node} {p : ℕ} (hell : 0 ≤ ell)
    (hr : 0 < z.gap) (hs : Valid z.side z.ratio) (hp : p ∈ nodeChildren w ell S z) :
    Consistent (step w z p) := by
  have hx := child_exponent_positive hell hp
  have ht := valid_pos (child_valid hs hp)
  change primeExponent w p = (z.gap-primeExponent w p)/childRatio w z.gap p
  rw [← nextGap_childRatio hr hx ht, nextGap_div_ratio ht, nextExponent_childRatio hr hx]

theorem terminal_consistent {w ell S : ℝ} {z : Node} {ps : List ℕ} (hell : 0 ≤ ell)
    (hr : 0 < z.gap) (hs : Valid z.side z.ratio) (hz : Consistent z) (hp : allowed w ell S z ps) :
    Consistent (terminal w z ps) := by
  induction ps generalizing z with
  | nil => exact hz
  | cons p ps ih =>
    rcases (allowed_cons w ell S z p ps).mp hp with ⟨hc,ht⟩
    exact ih (child_gap_positive hell hr hs hc) (child_valid hs hc) (step_consistent hell hr hs hc) ht

theorem history_consistent {w ell S : ℝ} {start : Node} (hell : 0 ≤ ell)
    (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hc : Consistent start)
    (h : History w ell S start) : Consistent h.node :=
  terminal_consistent hell hr hs hc h.admissible

end NumberTheoryLean.PrimeBinMembership

end

section

namespace NumberTheoryLean.ActualPrimeHigh
open FinitePathGeometry PrimeTiltGeometry PrimeTiltPrefixes PrimeHistories PrimeBinMembership
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass
open ErdosPrimeInputs.HighPrimeGeometry

theorem terminal_gap_remaining (w : ℝ) (z : Node) (ps : List ℕ) :
    (terminal w z ps).gap = remainingGap z.gap w ps := by
  induction ps generalizing z with
  | nil => simp [remainingGap]
  | cons p ps ih =>
    rw [terminal_cons,ih]
    simp only [remainingGap,step,List.map_cons,List.sum_cons]
    ring

theorem terminal_cutoff (w : ℝ) (z : Node) (ps : List ℕ) :
    (terminal w z ps).cutoff = primeCutoff w z.cutoff ps := by
  induction ps generalizing z with
  | nil => rfl
  | cons p ps ih => exact ih (step w z p)

theorem terminal_ratio_remaining {w ell U : ℝ} {z : Node} {ps : List ℕ}
    (hell : 0 ≤ ell) (hr : 0 < z.gap) (hs : Valid z.side z.ratio)
    (hz : Consistent z) (hp : allowed w ell U z ps) :
    (terminal w z ps).ratio = remainingGap z.gap w ps / primeCutoff w z.cutoff ps := by
  have hc := terminal_consistent hell hr hs hz hp
  have hg := terminal_gap_positive hell hr hs hp
  have hv := valid_pos (terminal_valid hs hp)
  rw [← terminal_gap_remaining w z ps,← terminal_cutoff w z ps]
  change (terminal w z ps).cutoff = (terminal w z ps).gap/(terminal w z ps).ratio at hc
  rw [hc]
  field_simp

theorem actual_has_high_iff {w ell U T : ℝ} {z : Node} {ps : List ℕ}
    (hell : 0 ≤ ell) (hr : 0 < z.gap) (hs : Valid z.side z.ratio)
    (hz : Consistent z) (hp : allowed w ell U z ps) :
    actualHasHigh w T z ps ↔ hasHighState z.gap w z.cutoff T ps := by
  constructor <;> rintro ⟨pre,suf,he,hh⟩
  · have hpre : allowed w ell U z pre := (allowed_append w ell U z pre suf).mp (he ▸ hp) |>.1
    rw [terminal_ratio_remaining hell hr hs hz hpre] at hh
    exact ⟨pre,suf,he,hh⟩
  · have hpre : allowed w ell U z pre := (allowed_append w ell U z pre suf).mp (he ▸ hp) |>.1
    rw [← terminal_ratio_remaining hell hr hs hz hpre] at hh
    exact ⟨pre,suf,he,hh⟩

end NumberTheoryLean.ActualPrimeHigh

end

section

namespace NumberTheoryLean.ActualPrimeHigh
open FinitePathGeometry PrimeTiltGeometry PrimeTiltPrefixes PrimeHistories PrimeBinMembership
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass
open ErdosPrimeInputs.HighPrimeGeometry

theorem uncapped_has_high_iff {w ell T : ℝ} {z : Node} {ps : List ℕ}
    (hell : 0 ≤ ell) (hr : 0 < z.gap) (hs : Valid z.side z.ratio) (hz : Consistent z)
    (hp : uncappedAllowed w ell z ps) :
    actualHasHigh w T z ps ↔ hasHighState z.gap w z.cutoff T ps := by
  obtain ⟨U,_,hU⟩ := (uncapped_iff_exists_ceiling w ell z ps).mp hp
  exact actual_has_high_iff hell hr hs hz hU

end NumberTheoryLean.ActualPrimeHigh

end

section

open scoped BigOperators
namespace NumberTheoryLean.ActualPrimeHigh
attribute [local instance] Classical.propDecidable
open FinitePathGeometry PrimeHistories PrimeBinMembership
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail ErdosPrimeInputs.HighPrimeGeometry

theorem uncapped_low_mass_le {w ell : ℝ} (_hw : 1 < w) {z : Node}
    (hell : 0 ≤ ell) (hr : 0 < z.gap) (hs : Valid z.side z.ratio)
    (hz : Consistent z) (T K : ℝ) :
    uncappedLowGapHighMass w ell z T K ≤
      ErdosPrimeInputs.HighPrimeMass.lowGapHighMass z.gap w z.cutoff ell T K := by
  classical
  unfold uncappedLowGapHighMass ErdosPrimeInputs.HighPrimeMass.lowGapHighMass
  simp only [terminal_gap_remaining]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ps hp
    obtain ⟨hfamily,hgap,hhigh⟩ := Finset.mem_filter.mp hp
    obtain ⟨hdec,hactual⟩ := Finset.mem_filter.mp hfamily
    exact Finset.mem_filter.mpr ⟨hdec,hgap,
      (uncapped_has_high_iff hell hr hs hz hactual).mp hhigh⟩
  · intro ps _ _
    exact prefixWeight_nonneg ps

end NumberTheoryLean.ActualPrimeHigh

end

section

namespace NumberTheoryLean.PrimeFamilyOccupation
open FinitePathGeometry PrimeHistories PrimeKilledChain
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass
open ActualPrimeHigh

theorem sum_histories {w ell S : ℝ} (hw : 1 < w) (start : Node) (F : List ℕ → ℝ) :
    letI := historyFintype (ell := ell) (S := S) hw start
    (∑ h : History w ell S start,F h.primes) =
      ∑ ps ∈ retainedPrefixes w ell S start,F ps := by
  classical
  let := historyFintype (ell := ell) (S := S) hw start
  calc
    _ = ∑ ps : {ps // ps ∈ retainedPrefixes w ell S start},F ps.val :=
      (Equiv.sum_comp (retainedHistoryEquiv hw start) (fun h => F h.primes)).symm
    _ = _ := Finset.sum_attach _ F

end NumberTheoryLean.PrimeFamilyOccupation

end

section

namespace NumberTheoryLean.PrimeCompactWeights

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeCompactVisits
open PrimeCorrectionFactor PrimeBinMembership PrimeTiltGeometry DerivativeWeights

theorem valid_compact_end {K : ℝ} (hK : 3 ≤ K) (i : Side) : Valid i K := by
  cases i <;> change _ ≤ K <;> linarith

theorem inverseBound_pos {K : ℝ} (hK : 3 ≤ K) : 0 < inverseBound K :=
  (one_div_pos.mpr (weight_pos (valid_compact_end hK .even))).trans_le (le_max_left _ _)

theorem compact_inverse_weight {K s : ℝ} {i : Side} (hK : 3 ≤ K) (hs : Valid i s) (hsK : s ≤ K) :
    1/weight i s ≤ inverseBound K := by
  have hpos := weight_pos (valid_compact_end hK i)
  have hmono := TwoStepDensityBounds.weight_antitone hs (valid_compact_end hK i) hsK
  have h := one_div_le_one_div_of_le hpos hmono
  cases i with
  | even => exact h.trans (le_max_left _ _)
  | odd => exact h.trans (le_max_right _ _)

theorem terminal_cutoff_lower {w ell S : ℝ} {start : Node} {ps : List ℕ}
    (hc : ell ≤ start.cutoff) (hp : allowed w ell S start ps) : ell ≤ (terminal w start ps).cutoff := by
  classical
  induction ps generalizing start with
  | nil => exact hc
  | cons p ps ih =>
    obtain ⟨hchild,htail⟩ := (allowed_cons w ell S start p ps).mp hp
    have hlo : ell < ErdosPrimeInputs.HarmonicPrimeMeasure.primeExponent w p :=
      (Finset.mem_filter.mp hchild).2.1
    exact ih hlo.le htail

theorem history_ratio_le_gap {w ell S : ℝ} {start : Node}
    (hell : 1 ≤ ell) (hr : 0 < start.gap) (hs : Valid start.side start.ratio)
    (hc : Consistent start) (hcut : ell ≤ start.cutoff) (h : History w ell S start) :
    h.node.ratio ≤ h.node.gap := by
  have hv : 0 < h.node.ratio := valid_pos (terminal_valid hs h.admissible)
  have hn : Consistent h.node := history_consistent (by linarith) hr hs hc h
  have hlow : ell ≤ h.node.cutoff := terminal_cutoff_lower hcut h.admissible
  change h.node.cutoff = h.node.gap/h.node.ratio at hn
  have he := (eq_div_iff hv.ne').mp hn
  nlinarith

theorem compactConstant_pos {K : ℝ} (hK : 3 ≤ K) : 0 < compactConstant K := by
  have hφ : 0 < weight .even (199/100) := weight_pos (by norm_num [Valid])
  have hI := inverseBound_pos hK
  unfold compactConstant
  positivity

theorem scaledWeight_nonneg {w B ell S : ℝ} {start : Node}
    (hs : Valid start.side start.ratio) (z : ChainState w ell S start) : 0 ≤ scaledWeight w B start z := by
  cases z with
  | none => exact le_rfl
  | some h =>
    have hφ := (weight_pos hs).le
    have hφ' := (weight_pos (terminal_valid hs h.admissible)).le
    have he := (normalizer_pos w).le
    unfold scaledWeight
    positivity

theorem scaled_compact_bound {d w ell B K : ℝ} {start : Node}
    (hK : 3 ≤ K) (hB : 0 < B) (hell : 1 ≤ ell) (hellB : ell ≤ B)
    (hlogB : 2 ≤ Real.log B) (hcomp : Real.log B ≤ d*Real.log w)
    (hbudget : correctionBudget d w ≤ 1)
    (hi : start.side = .even) (h199 : 199/100 ≤ start.ratio) (h23 : start.ratio ≤ 23/10)
    (hc : Consistent start) (hcut : start.cutoff = B)
    (h : History w ell ((Real.log B)^2) start) (hgK : h.node.gap ≤ K) :
    scaledWeight w B start (some h) ≤ compactConstant K := by
  have hs : Valid start.side start.ratio := by rw [hi]; change 198/100 ≤ start.ratio; linarith
  have hs0 := valid_pos hs
  have he : start.gap = B*start.ratio := by
    have hh : start.cutoff = start.gap/start.ratio := hc
    rw [hcut] at hh
    exact ((eq_div_iff hs0.ne').mp hh).symm
  have hr : 0 < start.gap := by rw [he]; positivity
  have hBr : B ≤ start.gap := by rw [he]; nlinarith
  have hsize : start.gap ≤ (23/10:ℝ)*B := by rw [he]; nlinarith
  have hrat : h.node.ratio ≤ K := (history_ratio_le_gap hell hr hs hc (by rwa [hcut]) h).trans hgK
  have hgv : Valid h.node.side h.node.ratio := terminal_valid hs h.admissible
  have hgp : 0 < h.node.gap := terminal_gap_positive (by linarith) hr hs h.admissible
  have hinv := compact_inverse_weight hK hgv hrat
  have hinit : weight start.side start.ratio ≤ weight .even (199/100) := by
    rw [hi]
    exact TwoStepDensityBounds.weight_antitone (by norm_num [Valid]) (hi ▸ hs) h199
  have hcorr : (1+epsilon w)^h.primes.length ≤ 2 := by
    have hh := (history_correction hlogB hcomp hell hr hs hB hsize h).2
    linarith
  have hgap : B^2*(h.node.gap/start.gap)^2 ≤ K^2 := by
    have hratio : B/start.gap ≤ 1 := (div_le_one hr).mpr hBr
    have hpos : 0 ≤ B/start.gap := div_nonneg hB.le hr.le
    have heq : B^2*(h.node.gap/start.gap)^2 = (B/start.gap)^2*h.node.gap^2 := by ring
    rw [heq]
    have h1 : (B/start.gap)^2 ≤ 1 := by nlinarith
    have h2 : h.node.gap^2 ≤ K^2 := by nlinarith
    nlinarith [sq_nonneg (B/start.gap),mul_nonneg (sub_nonneg.mpr h1) (sq_nonneg h.node.gap)]
  have hC : 0 ≤ (1+epsilon w)^h.primes.length := pow_nonneg (normalizer_pos w).le _
  have hI : 0 ≤ inverseBound K := (inverseBound_pos hK).le
  have hφ : 0 ≤ weight .even (199/100) := (weight_pos (by norm_num [Valid])).le
  have hpφ : 0 ≤ weight start.side start.ratio := (weight_pos hs).le
  have hφg : 0 < weight h.node.side h.node.ratio := weight_pos hgv
  calc
    _ = ((1+epsilon w)^h.primes.length*(B^2*(h.node.gap/start.gap)^2))*
        (weight start.side start.ratio*(1/weight h.node.side h.node.ratio)) := by unfold scaledWeight; ring
    _ ≤ (2*K^2)*(weight .even (199/100)*inverseBound K) := by
      exact mul_le_mul (mul_le_mul hcorr hgap (by positivity) (by norm_num))
        (mul_le_mul hinit hinv (by positivity) hφ) (by positivity) (by positivity)
    _ = _ := by unfold compactConstant; ring

end NumberTheoryLean.PrimeCompactWeights

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_ActualCouplingUpdates
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Finset
open scoped BigOperators
namespace Erdos970Dependency.MaximalCoupling

variable {ι : Type*} [Fintype ι]
attribute [local instance] Classical.propDecidable

omit [Fintype ι] in
theorem common_nonneg {a b : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (i : ι) :
    0 ≤ common a b i := le_min (ha i) (hb i)

omit [Fintype ι] in
theorem leftRemainder_nonneg (a b : ι → ℝ) (i : ι) : 0 ≤ leftRemainder a b i :=
  sub_nonneg.mpr (min_le_left _ _)
omit [Fintype ι] in
theorem rightRemainder_nonneg (a b : ι → ℝ) (i : ι) : 0 ≤ rightRemainder a b i :=
  sub_nonneg.mpr (min_le_right _ _)

theorem sum_leftRemainder {a b : ι → ℝ} (ha : ∑ i, a i = 1) :
    ∑ i, leftRemainder a b i = residual a b := by simp only [leftRemainder, sum_sub_distrib, ha, residual]
theorem sum_rightRemainder {a b : ι → ℝ} (hb : ∑ i, b i = 1) :
    ∑ i, rightRemainder a b i = residual a b := by simp only [rightRemainder, sum_sub_distrib, hb, residual]

theorem residual_nonneg {a b : ι → ℝ} (ha : ∑ i, a i = 1) : 0 ≤ residual a b := by
  rw [← sum_leftRemainder ha]
  exact sum_nonneg (fun i _ => leftRemainder_nonneg a b i)

theorem leftRemainder_zero {a b : ι → ℝ} (ha : ∑ i, a i = 1) (hr : residual a b = 0) (i : ι) :
    leftRemainder a b i = 0 := by
  have h := single_le_sum (fun j _ => leftRemainder_nonneg a b j) (mem_univ i)
  rw [sum_leftRemainder ha, hr] at h
  exact le_antisymm h (leftRemainder_nonneg a b i)

theorem matrix_nonneg {a b : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hsa : ∑ i, a i = 1) (i j : ι) : 0 ≤ matrix a b i j := by
  unfold matrix
  apply add_nonneg
  · split_ifs <;> first | exact common_nonneg ha hb i | exact le_rfl
  · split_ifs
    · exact le_rfl
    · exact div_nonneg (mul_nonneg (leftRemainder_nonneg a b i) (rightRemainder_nonneg a b j)) (residual_nonneg hsa)

theorem row_sum {a b : ι → ℝ} (ha : ∑ i, a i = 1) (hb : ∑ i, b i = 1) (i : ι) :
    ∑ j, matrix a b i j = a i := by
  classical
  by_cases hr : residual a b = 0
  · have hz := leftRemainder_zero ha hr i
    simp only [matrix, ite_eq_left hr, add_zero]
    simp only [sum_ite_eq, mem_univ, ite_true, if_true]
    unfold leftRemainder at hz
    linarith
  · simp only [matrix, ite_eq_right hr, sum_add_distrib]
    rw [sum_ite_eq]
    simp only [mem_univ, ite_true, if_true]
    rw [← sum_div, ← mul_sum, sum_rightRemainder hb]
    rw [mul_div_cancel_right₀ _ hr]
    unfold leftRemainder
    ring

end Erdos970Dependency.MaximalCoupling

end

section

namespace NumberTheoryLean.KernelBinConditioning

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]

theorem conditional_apply (K : Kernel α β) {B : Set β} (hB : MeasurableSet B) (default : β) (x : α) :
    conditional K hB default x = if K x B = 0 then Measure.dirac default else (K x B)⁻¹ • (K x).restrict B := rfl

instance conditional_isMarkov (K : Kernel α β) [IsMarkovKernel K] {B : Set β}
    (hB : MeasurableSet B) (default : β) : IsMarkovKernel (conditional K hB default) := by
  constructor
  intro x
  constructor
  classical
  rw [conditional_apply]
  by_cases hx : K x B = 0
  · rw [ite_eq_left hx]
    exact measure_univ
  · rw [ite_eq_right hx, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel hx (measure_ne_top _ _)

theorem weighted_conditional (K : Kernel α β) [IsMarkovKernel K] {B : Set β}
    (hB : MeasurableSet B) (default : β) (x : α) :
    (K x B) • conditional K hB default x = (K x).restrict B := by
  classical
  rw [conditional_apply]
  by_cases hx : K x B = 0
  · rw [ite_eq_left hx, hx, zero_smul]
    exact (Measure.restrict_eq_zero.mpr hx).symm
  · rw [ite_eq_right hx, smul_smul, ENNReal.mul_inv_cancel hx (measure_ne_top _ _), one_smul]

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem labelMass_measurable (K : Kernel α β) {label : β → ι} (hl : Measurable label) (i : ι) :
    Measurable (fun x => labelMass K label x i) :=
  ENNReal.measurable_toReal.comp (K.measurable_coe (hl (measurableSet_singleton i)))

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
theorem labelMass_nonneg (K : Kernel α β) (label : β → ι) (x : α) (i : ι) :
    0 ≤ labelMass K label x i := ENNReal.toReal_nonneg

variable [Fintype ι]

theorem labelMass_sum (K : Kernel α β) [IsMarkovKernel K] {label : β → ι}
    (hl : Measurable label) (x : α) : ∑ i, labelMass K label x i = 1 := by
  have h := sum_measure_preimage_singleton (μ := K x) (Finset.univ : Finset ι)
    (fun i _ => hl (measurableSet_singleton i))
  simp only [Finset.coe_univ, Set.preimage_univ, measure_univ] at h
  have hr := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _), ENNReal.toReal_one] at hr
  exact hr

theorem conditional_mixture (K : Kernel α β) [IsMarkovKernel K] {label : β → ι}
    (hl : Measurable label) (default : β) (x : α) :
    (∑ i, (K x (label ⁻¹' {i})) • conditional K (hl (measurableSet_singleton i)) default x) = K x := by
  simp_rw [weighted_conditional]
  apply Measure.ext
  intro B hB
  rw [Measure.finsetSum_apply]
  simp_rw [Measure.restrict_apply hB]
  have h := sum_measure_preimage_singleton (μ := (K x).restrict B) (Finset.univ : Finset ι)
    (fun i _ => hl (measurableSet_singleton i))
  simp only [Finset.coe_univ, Set.preimage_univ, Measure.restrict_apply_univ] at h
  have heq : ∀ i : ι, (K x).restrict B (label ⁻¹' {i}) = K x (B ∩ label ⁻¹' {i}) := by
    intro i
    rw [Measure.restrict_apply (hl (measurableSet_singleton i)), Set.inter_comm]
  simp_rw [heq] at h
  exact h

end NumberTheoryLean.KernelBinConditioning

end

section

namespace NumberTheoryLean.KernelCouplingWeights

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open KernelBinConditioning Erdos970Dependency.MaximalCoupling
attribute [local instance] Classical.propDecidable

variable {α β γ ι : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem weight_measurable (K : Kernel α β) (L : Kernel α γ) {f : β → ι} {g : γ → ι}
    (hf : Measurable f) (hg : Measurable g) (i j : ι) : Measurable (fun x => weight K L f g x i j) := by
  classical
  have ha := labelMass_measurable K hf
  have hb := labelMass_measurable L hg
  have hc (i : ι) : Measurable (fun x => common (labelMass K f x) (labelMass L g x) i) := (ha i).min (hb i)
  have hr : Measurable (fun x => residual (labelMass K f x) (labelMass L g x)) :=
    measurable_const.sub (Finset.measurable_sum univ (fun i _ => hc i))
  have hl : Measurable (fun x => leftRemainder (labelMass K f x) (labelMass L g x) i) := (ha i).sub (hc i)
  have hh : Measurable (fun x => rightRemainder (labelMass K f x) (labelMass L g x) j) := (hb j).sub (hc j)
  have hd : Measurable (fun x => if i = j then common (labelMass K f x) (labelMass L g x) i else 0) := by
    by_cases hij : i = j
    · simpa only [ite_eq_left hij] using hc i
    · simp only [ite_eq_right hij]
      exact measurable_const
  exact hd.add (Measurable.ite (measurableSet_eq_fun hr measurable_const) measurable_const ((hl.mul hh).div hr))

theorem weight_joint_measurable (K : Kernel α β) (L : Kernel α γ) {f : β → ι} {g : γ → ι}
    (hf : Measurable f) (hg : Measurable g) (i j : ι) :
    Measurable (Function.uncurry (fun (x : α) (_ : β × γ) => ENNReal.ofReal (weight K L f g x i j))) :=
  (ENNReal.measurable_ofReal.comp (weight_measurable K L hf hg i j)).comp measurable_fst

variable (K : Kernel α β) (L : Kernel α γ) [IsMarkovKernel K] [IsMarkovKernel L]
variable {f : β → ι} {g : γ → ι} (hf : Measurable f) (hg : Measurable g)
include hf hg

omit hg [IsMarkovKernel L] in
theorem weight_nonnegative (x : α) (i j : ι) : 0 ≤ weight K L f g x i j :=
  matrix_nonneg (labelMass_nonneg K f x) (labelMass_nonneg L g x) (labelMass_sum K hf x) i j

theorem weight_row (x : α) (i : ι) : ∑ j, weight K L f g x i j = labelMass K f x i :=
  row_sum (labelMass_sum K hf x) (labelMass_sum L hg x) i

theorem weight_row_ofReal (x : α) (i : ι) :
    ∑ j, ENNReal.ofReal (weight K L f g x i j) = K x (f ⁻¹' {i}) := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => weight_nonnegative K L (g := g) hf x i j), weight_row K L hf hg]
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

theorem weight_total_ofReal (x : α) : ∑ i, ∑ j, ENNReal.ofReal (weight K L f g x i j) = 1 := by
  simp_rw [weight_row_ofReal K L hf hg]
  have h := sum_measure_preimage_singleton (μ := K x) (Finset.univ : Finset ι)
    (fun i _ => hf (measurableSet_singleton i))
  simpa only [Finset.coe_univ, Set.preimage_univ, measure_univ] using h

end NumberTheoryLean.KernelCouplingWeights

end

section

namespace NumberTheoryLean.KernelCouplingLift

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open KernelBinConditioning KernelCouplingWeights

variable {α β γ ι : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
variable (K : Kernel α β) (L : Kernel α γ) [IsMarkovKernel K] [IsMarkovKernel L]
variable {f : β → ι} {g : γ → ι} (hf : Measurable f) (hg : Measurable g) (dβ : β) (dγ : γ)

theorem component_apply (i j : ι) (x : α) :
    component K L hf hg dβ dγ i j x = ENNReal.ofReal (weight K L f g x i j) •
      (conditional K (hf (measurableSet_singleton i)) dβ x).prod
        (conditional L (hg (measurableSet_singleton j)) dγ x) := by
  rw [component, Kernel.withDensity_apply _ (weight_joint_measurable K L hf hg i j) x,
    Kernel.prod_apply, withDensity_const]

theorem coupled_apply_set (x : α) {B : Set (β × γ)} (hB : MeasurableSet B) :
    coupled K L hf hg dβ dγ x B = ∑ i, ∑ j, ENNReal.ofReal (weight K L f g x i j) *
      ((conditional K (hf (measurableSet_singleton i)) dβ x).prod
        (conditional L (hg (measurableSet_singleton j)) dγ x)) B := by
  rw [coupled, Kernel.sum_apply' _ _ hB, tsum_fintype, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [component_apply, Measure.smul_apply, smul_eq_mul]

instance coupled_isMarkov : IsMarkovKernel (coupled K L hf hg dβ dγ) := by
  constructor
  intro x
  constructor
  rw [coupled_apply_set K L hf hg dβ dγ x MeasurableSet.univ]
  simp only [measure_univ, mul_one]
  exact weight_total_ofReal K L hf hg x

theorem coupled_map_fst (x : α) :
    (coupled K L hf hg dβ dγ x).map Prod.fst = K x := by
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply measurable_fst hB, coupled_apply_set K L hf hg dβ dγ x (measurable_fst hB)]
  have hpre : (Prod.fst ⁻¹' B : Set (β × γ)) = B ×ˢ univ := by ext p; simp
  rw [hpre]
  simp only [Measure.prod_prod, measure_univ, mul_one]
  simp_rw [← Finset.sum_mul, weight_row_ofReal K L hf hg]
  have h := congrArg (fun μ : Measure β => μ B) (conditional_mixture K hf dβ x)
  simpa only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul] using h

end NumberTheoryLean.KernelCouplingLift

end

section

namespace NumberTheoryLean.ActualProcessCoupling

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ContinuousKilledBins MeshRatioLabels KernelCouplingLift KernelBinConditioning

instance continuousParent_isMarkov (w ell S : ℝ) (start : Node) (v : ℝ) :
    IsMarkovKernel (continuousParent w ell S start v) := by unfold continuousParent; infer_instance

variable {w ell S : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
variable (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

instance jointKernel_isMarkov (v mesh : ℝ) : IsMarkovKernel (jointKernel hw hell hS0 hS hr hs hsS v mesh) := by
  let := chain_isMarkov hw hell hS0 hS hr hs hsS
  unfold jointKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem jointKernel_left (v mesh : ℝ) (p : ChainState w ell S start) (z : CemeteryKernel.Space CostState) :
    (jointKernel hw hell hS0 hS hr hs hsS v mesh (p,z)).map Prod.fst = chain w ell S start p := by
  let := chain_isMarkov hw hell hS0 hS hr hs hsS
  exact coupled_map_fst (primeParent w ell S start) (continuousParent w ell S start v)
    (primeLabel_measurable w ell S mesh start) (continuousLabel_measurable S mesh)
    none CemeteryKernel.dead (p,z)

end NumberTheoryLean.ActualProcessCoupling

end

section

namespace NumberTheoryLean.ActualCouplingFinite

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ContinuousKilledBins PrimeChainHorizon LowStateHorizon

section Generic
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable (K : Kernel α α) (L : Kernel β β)
variable {f : α → β} (hf : Measurable f)

include hf

theorem map_power_of_step (hstep : ∀ x, (K x).map f = L (f x)) (n : ℕ) (x : α) :
    ((K^n) x).map f = (L^n) (f x) := by
  let P : Kernel α β := Kernel.deterministic f hf
  have hinter : P ∘ₖ K = L ∘ₖ P := by
    rw [show P = Kernel.deterministic f hf from rfl, Kernel.deterministic_comp_eq_map,
      Kernel.comp_deterministic_eq_comap]
    ext x : 1
    rw [Kernel.map_apply _ hf,Kernel.comap_apply]
    exact hstep x
  have hpow : ∀ n, P ∘ₖ (K^n) = (L^n) ∘ₖ P := by
    intro n
    induction n with
    | zero =>
      change P ∘ₖ (Kernel.id : Kernel α α) = Kernel.id ∘ₖ P
      rw [Kernel.comp_id,Kernel.id_comp]
    | succ n ih =>
      have hp : K^(n+1) = (K^n) ∘ₖ K := pow_succ _ _
      have hq : L^(n+1) = (L^n) ∘ₖ L := pow_succ _ _
      rw [hp,hq,← Kernel.comp_assoc,ih,Kernel.comp_assoc,hinter,← Kernel.comp_assoc]
  have h := hpow n
  rw [show P = Kernel.deterministic f hf from rfl,Kernel.deterministic_comp_eq_map,
    Kernel.comp_deterministic_eq_comap] at h
  have hx := congrArg (fun M : Kernel α β => M x) h
  rwa [Kernel.map_apply _ hf,Kernel.comap_apply] at hx
end Generic

variable {w ell S : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
variable (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

instance jointKernel_pow_markov (v mesh : ℝ) (n : ℕ) :
    IsMarkovKernel ((jointKernel hw hell hS0 hS hr hs hsS v mesh)^n) := by
  induction n with
  | zero => change IsMarkovKernel (Kernel.id : Kernel (JointState w ell S start) (JointState w ell S start)); infer_instance
  | succ n ih =>
    let := ih
    have hp : (jointKernel hw hell hS0 hS hr hs hsS v mesh)^(n+1) =
      (jointKernel hw hell hS0 hS hr hs hsS v mesh) ∘ₖ ((jointKernel hw hell hS0 hS hr hs hsS v mesh)^n) := pow_succ' _ _
    rw [hp]
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem joint_power_left (v mesh : ℝ) (n : ℕ) (q : JointState w ell S start) :
    (((jointKernel hw hell hS0 hS hr hs hsS v mesh)^n) q).map Prod.fst =
      ((chain w ell S start)^n) q.1 := by
  let := chain_isMarkov hw hell hS0 hS hr hs hsS
  exact map_power_of_step _ _ measurable_fst
    (fun x => jointKernel_left hw hell hS0 hS hr hs hsS v mesh x.1 x.2) n q

instance jointPathLaw_probability (v mesh : ℝ) (z : CostState) (n : ℕ) :
    IsProbabilityMeasure (jointPathLaw hw hell hS0 hS hr hs hsS v mesh z n) := by
  unfold jointPathLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem jointPathLaw_prime (v mesh : ℝ) (z : CostState) (n : ℕ) :
    (jointPathLaw hw hell hS0 hS hr hs hsS v mesh z n).map Prod.fst = pathLaw w ell S start n :=
  joint_power_left hw hell hS0 hS hr hs hsS v mesh n (some History.empty,.inl z)

end NumberTheoryLean.ActualCouplingFinite

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FlaggedSourceStart
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.PersistentFailureFlag

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open ActualCouplingFinite

variable {α : Type*} [MeasurableSpace α]

theorem badBit_measurable {Bad : α → Prop} (hBad : MeasurableSet {x | Bad x}) : Measurable (badBit Bad) := by
  classical
  exact Measurable.ite hBad measurable_const measurable_const

theorem update_measurable {Bad : α → Prop} (hBad : MeasurableSet {x | Bad x}) : Measurable (update Bad) := by
  have hor : Measurable (fun p : Bool × Bool => p.1 || p.2) := measurable_of_countable _
  exact measurable_snd.prodMk (hor.comp ((measurable_snd.comp measurable_fst).prodMk
    ((badBit_measurable hBad).comp measurable_snd)))

instance marked_isMarkov (K : Kernel α α) [IsMarkovKernel K]
    {Bad : α → Prop} (hBad : MeasurableSet {x | Bad x}) : IsMarkovKernel (marked K hBad) := by
  unfold marked
  exact Kernel.IsMarkovKernel.map _ (update_measurable hBad)

theorem marked_apply (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (z : FlagState α) {B : Set (FlagState α)} (hB : MeasurableSet B) :
    marked K hBad z B = K z.1 {y | (y,z.2 || badBit Bad y) ∈ B} := by
  rw [marked,Kernel.map_apply' _ (update_measurable hBad) _ hB,
    Kernel.prod_apply' _ _ _ ((update_measurable hBad) hB),Kernel.id_apply]
  rw [lintegral_dirac']
  · rfl
  · exact measurable_measure_prodMk_left ((update_measurable hBad) hB)

theorem row_update_measurable {Bad : α → Prop} (hBad : MeasurableSet {x | Bad x}) (b : Bool) :
    Measurable (fun y : α => (y,b || badBit Bad y)) := by
  have hor : Measurable (fun p : Bool × Bool => p.1 || p.2) := measurable_of_countable _
  exact measurable_id.prodMk (hor.comp (measurable_const.prodMk (badBit_measurable hBad)))

theorem marked_eq_map (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (z : FlagState α) :
    marked K hBad z = (K z.1).map (fun y => (y,z.2 || badBit Bad y)) := by
  apply Measure.ext
  intro B hB
  rw [marked_apply K hBad z hB,Measure.map_apply (row_update_measurable hBad z.2) hB]
  rfl

theorem marked_map (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (z : FlagState α) : (marked K hBad z).map Prod.fst = K z.1 := by
  rw [marked_eq_map K hBad z,Measure.map_map (f:=fun y => (y,z.2 || badBit Bad y))
    (g:=Prod.fst) measurable_fst (row_update_measurable hBad z.2)]
  exact Measure.map_id

instance marked_pow_markov (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (n : ℕ) : IsMarkovKernel ((marked K hBad)^n) := by
  induction n with
  | zero => change IsMarkovKernel (Kernel.id : Kernel (FlagState α) (FlagState α)); infer_instance
  | succ n ih =>
    let := ih
    have hp : (marked K hBad)^(n+1) = (marked K hBad) ∘ₖ ((marked K hBad)^n) := pow_succ' _ _
    rw [hp]
    first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply update_measurable <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem marked_power_map (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (n : ℕ) (z : FlagState α) :
    (((marked K hBad)^n) z).map Prod.fst = (K^n) z.1 :=
  map_power_of_step (marked K hBad) K measurable_fst (marked_map K hBad) n z

instance law_probability (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (x : α) (n : ℕ) : IsProbabilityMeasure (law K hBad x n) := by
  unfold law
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end NumberTheoryLean.PersistentFailureFlag



namespace NumberTheoryLean.FlaggedSourceStart

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ActualCouplingFinite ActualFlagInvariant PersistentFailureFlag
open RegeneratingInverseBands ContinuousKilledBins

variable {w ell S : ℝ} {start : Node}

variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
variable (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

instance sourceLaw_probability (mesh : ℝ) (n : ℕ) :
    IsProbabilityMeasure (sourceLaw hw hell hS0 hS hr hs hsS mesh n) := by
  unfold sourceLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem sourceLaw_joint (mesh : ℝ) (n : ℕ) :
    (sourceLaw hw hell hS0 hS hr hs hsS mesh n).map Prod.fst =
      jointPathLaw hw hell hS0 hS hr hs hsS (Real.log start.gap) mesh (sourceCostState hs) n :=
  marked_power_map _ (mismatch_measurable mesh) n (sourceJoint w ell S start hs,false)

theorem sourceLaw_prime (mesh : ℝ) (n : ℕ) :
    (sourceLaw hw hell hS0 hS hr hs hsS mesh n).map (fun q => q.1.1) = pathLaw w ell S start n := by
  calc
    _ = ((sourceLaw hw hell hS0 hS hr hs hsS mesh n).map Prod.fst).map Prod.fst :=
      (Measure.map_map (f:=Prod.fst) (g:=Prod.fst) measurable_fst measurable_fst).symm
    _ = _ := by rw [sourceLaw_joint,jointPathLaw_prime]

end NumberTheoryLean.FlaggedSourceStart


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceMarginalRate
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.UniformBudgetRate

open _root_.Set _root_.Filter
open scoped Topology
open UniformFailureBudget ExponentialMesh BudgetPolynomialBound PrimeKilledChain

theorem source_scale_bound {d w B : ℝ} (hW : d^2 ≤ Real.log w)
    (hB : 2 ≤ Real.log B) (hcomp : Real.log B ≤ d*Real.log w) :
    (Real.log B)^2 ≤ (Real.log w)^3 ∧
      (LowStateHorizon.sourceHorizon ((Real.log B)^2) B:ℝ) ≤ 5*d^3*(Real.log w)^3 := by
  have hlog : 0 ≤ Real.log w := (sq_nonneg d).trans hW
  have hpow₂ := pow_le_pow_left₀ (show 0 ≤ Real.log B by linarith) hcomp 2
  have hpow₃ := pow_le_pow_left₀ (show 0 ≤ Real.log B by linarith) hcomp 3
  have hmul := mul_le_mul_of_nonneg_right hW (sq_nonneg (Real.log w))
  have hN := LowStateHorizon.source_horizon_log_cube hB
  constructor <;> nlinarith

end NumberTheoryLean.UniformBudgetRate

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_NonnegativeOriginalOccupation
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SourceCompactOccupation

open _root_.Set _root_.Filter _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeBinMembership
open PrimeCompactVisits PrimeCompactWeights PrimeCorrectionFactor
open FlaggedOccupationBound PersistentFailureFlag ActualProcessCoupling ActualFlaggedCompact

variable {w ell S B : ℝ} {start : Node}

theorem literal_scaled_weight (hell : 0 ≤ ell) (hr : 0 < start.gap)
    (hs : Valid start.side start.ratio) (h : History w ell S start) :
    B^2*ErdosPrimeInputs.PrimePrefixMass.prefixWeight h.primes =
      (pathLaw w ell S start h.primes.length {some h}).toReal*scaledWeight w B start (some h) := by
  rw [PrimeChainProbabilities.source_prime_weight_identity hell hr hs h]
  unfold scaledWeight
  ring

theorem compact_reward_envelope {K D : ℝ}
    (hbound : ∀ h : History w ell S start,h.node.gap ≤ K → scaledWeight w B start (some h) ≤ D)
    (z : ChainState w ell S start) :
    compactReward K w B start z ≤ ENNReal.ofReal D*ENNReal.ofReal (visit K z) := by
  cases z with
  | none => simp [compactReward,visit]
  | some h =>
    by_cases hh : h.node.gap ≤ K
    · simpa only [compactReward,visit,ite_eq_left hh,mul_one,ENNReal.ofReal_one]
        using ENNReal.ofReal_le_ofReal (hbound h hh)
    · simp [compactReward,visit,hh]

end NumberTheoryLean.SourceCompactOccupation

end

section

namespace NumberTheoryLean.PrimeFamilyOccupation
open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeChainHorizon
open PrimeCompactWeights SourceCompactOccupation
open ErdosPrimeInputs.PrimePrefixMass

variable {w ell S B : ℝ} {start : Node}

theorem singleton_off_stage (n : ℕ) (h : History w ell S start) (hne : h.primes.length ≠ n) :
    pathLaw w ell S start n {some h} = 0 := by
  have hsub : ({some h} : Set (ChainState w ell S start)) ⊆ {z | ¬stage n z} := by
    intro z hz
    have he : z = some h := hz
    subst z
    exact hne
  exact measure_mono_null hsub (ae_iff.mp (pathLaw_stage n))

theorem singleton_scaled_reward (hell : 0 ≤ ell) (hr : 0 < start.gap)
    (hs : Valid start.side start.ratio) (n : ℕ) (h : History w ell S start)
    (F : List ℕ → ℝ) :
    (pathLaw w ell S start n).real {some h} *
      (scaledWeight w B start (some h)*F h.primes) =
      if n = h.primes.length then B^2*prefixWeight h.primes*F h.primes else 0 := by
  classical
  by_cases hn : n = h.primes.length
  · rw [ite_eq_left hn,hn,measureReal_def]
    rw [← mul_assoc,← literal_scaled_weight hell hr hs h]
  · rw [ite_eq_right hn,measureReal_def,singleton_off_stage n h (Ne.symm hn)]
    simp

theorem finite_signed_original_occupation (hw : normalizationThreshold ≤ w)
    (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
    (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)
    (hB : 0 < B) (hsize : start.gap ≤ (23/10 : ℝ)*B) (F : List ℕ → ℝ) :
    (∑ n ∈ range (LowStateHorizon.sourceHorizon S B),
      ∫ z,scaledWeight w B start z*listReward F z ∂pathLaw w ell S start n) =
      B^2*(∑ ps ∈ retainedPrefixes w ell S start,prefixWeight ps*F ps) := by
  classical
  have hw1 : 1 < w := normalizationThreshold_gt_one.trans_le hw
  let := historyFintype (ell := ell) (S := S) hw1 start
  have hterm (n : ℕ) :
      (∫ z,scaledWeight w B start z*listReward F z ∂pathLaw w ell S start n) =
        ∑ h : History w ell S start,
          if n = h.primes.length then B^2*prefixWeight h.primes*F h.primes else 0 := by
    let := pathLaw_isProbability hw hell hS0 hS hr hs hsS n
    rw [integral_fintype Integrable.of_finite,Fintype.sum_option]
    simp only [scaledWeight,listReward,mul_zero,smul_zero,zero_add]
    apply Finset.sum_congr rfl
    intro h _hh
    exact singleton_scaled_reward (by linarith) hr hs n h F
  simp_rw [hterm]
  rw [Finset.sum_comm]
  have hlen (h : History w ell S start) : h.primes.length ∈ range (LowStateHorizon.sourceHorizon S B) :=
    mem_range.mpr (PrimeHistoryHorizon.history_length_lt hell hS0 hr hs hB hsize h)
  simp only [Finset.sum_ite_eq',hlen,ite_true, if_true]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  simpa only [mul_assoc] using sum_histories hw1 start (fun ps => prefixWeight ps*F ps)

end NumberTheoryLean.PrimeFamilyOccupation

end

section

namespace NumberTheoryLean.PrimeFamilyOccupation
open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeCompactWeights
open ErdosPrimeInputs.PrimePrefixMass

variable {w ell S B : ℝ} {start : Node}

theorem listReward_nonneg (F : List ℕ → ℝ)
    (hF : ∀ ps,allowed w ell S start ps → 0 ≤ F ps) (z : ChainState w ell S start) :
    0 ≤ listReward F z := by
  cases z with
  | none => exact le_rfl
  | some h => exact hF h.primes h.admissible

theorem finite_nonnegative_original_occupation (hw : normalizationThreshold ≤ w)
    (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
    (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)
    (hB : 0 < B) (hsize : start.gap ≤ (23/10 : ℝ)*B) (F : List ℕ → ℝ)
    (hF : ∀ ps,allowed w ell S start ps → 0 ≤ F ps) :
    (∑ n ∈ range (LowStateHorizon.sourceHorizon S B),
      ∫⁻ z,ENNReal.ofReal (scaledWeight w B start z*listReward F z) ∂pathLaw w ell S start n) =
      ENNReal.ofReal (B^2*(∑ ps ∈ retainedPrefixes w ell S start,prefixWeight ps*F ps)) := by
  classical
  have hw1 : 1 < w := normalizationThreshold_gt_one.trans_le hw
  let := historyFintype (ell := ell) (S := S) hw1 start
  have hnon (z : ChainState w ell S start) : 0 ≤ scaledWeight w B start z*listReward F z :=
    mul_nonneg (scaledWeight_nonneg hs z) (listReward_nonneg F hF z)
  rw [← finite_signed_original_occupation hw hell hS0 hS hr hs hsS hB hsize F]
  rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => integral_nonneg hnon)]
  apply Finset.sum_congr rfl
  intro n _hn
  let := pathLaw_isProbability hw hell hS0 hS hr hs hsS n
  exact (ofReal_integral_eq_lintegral_ofReal Integrable.of_finite
    (Filter.Eventually.of_forall hnon)).symm

end NumberTheoryLean.PrimeFamilyOccupation

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_UncappedHighRemoval
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualCouplingFinite.jointKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.ActualCouplingFinite.jointPathLaw_probability _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.continuousParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.jointKernel_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedSourceStart.sourceLaw_probability _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ActualPrimeHigh
open _root_.Filter
open scoped Topology
open FinitePathGeometry PrimeHistories PrimeBinMembership

theorem uncapped_low_gap_high_removal : ∃ w₀ : ℝ, 1 < w₀ ∧
    ∀ K : ℝ, 0 < K → ∀ A : ℝ, ∀ᶠ B : ℝ in atTop,
      ∀ w : ℝ, w₀ ≤ w → ∀ ell : ℝ, 1 ≤ ell → ell ≤ B → ∀ z : Node,
        z.cutoff = B → 0 < z.gap → Valid z.side z.ratio → Consistent z →
        uncappedLowGapHighMass w ell z ((Real.log B)^2) K ≤ B^(-A) := by
  obtain ⟨w₀,hw₀,hbound⟩ := ErdosPrimeInputs.HighPrimeRemoval.low_gap_high_removal
  refine ⟨w₀,hw₀,?_⟩
  intro K hK A
  filter_upwards [hbound K hK A] with B hB
  intro w hw ell hell hellB z hcut hr hs hz
  have h := uncapped_low_mass_le (hw₀.trans_le hw) (by linarith : 0 ≤ ell) hr hs hz
    ((Real.log B)^2) K
  rw [hcut] at h
  exact h.trans (hB w hw ell hell hellB z.gap)

end NumberTheoryLean.ActualPrimeHigh

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_CanonicalCoupledHistories
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.ActualCoupledHistories

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ActualFlagInvariant PersistentFailureFlag
open FlaggedSourceStart ContinuousKilledBins FiniteHistoryTransport

variable {w ell S : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

instance sourceTransition_markov (mesh : ℝ) :
    IsMarkovKernel (sourceTransition hw hell hS0 hS hr hs hsS mesh) := by
  unfold sourceTransition
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance sourceHistoryLaw_probability (mesh : ℝ) (n : ℕ) :
    IsProbabilityMeasure (sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh n) := by
  unfold sourceHistoryLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem sourceHistoryLaw_coordinate (mesh : ℝ) (n k : ℕ) (hk : k ≤ n) :
    (sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh n).map
      (fun h => h ⟨k, by simpa using hk⟩) = sourceLaw hw hell hS0 hS hr hs hsS mesh k :=
  pathMeasure_coordinate _ n k hk _

theorem sourceHistoryLaw_prime (mesh : ℝ) (n : ℕ) :
    (sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh n).map
      (mapHist (fun q => q.1.1) n) =
      pathKernel (chain w ell S start) n (fun _ => some History.empty) := by
  let := chain_isMarkov hw hell hS0 hS hr hs hsS
  apply pathMeasure_mapHist _ _ (measurable_fst.comp measurable_fst)
  intro q
  calc
    _ = ((sourceTransition hw hell hS0 hS hr hs hsS mesh q).map Prod.fst).map Prod.fst :=
      (Measure.map_map measurable_fst measurable_fst).symm
    _ = _ := by
      rw [sourceTransition, marked_map]
      exact jointKernel_left hw hell hS0 hS hr hs hsS (Real.log start.gap) mesh q.1.1 q.1.2

end NumberTheoryLean.ActualCoupledHistories



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeHistoryCompactCount
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.PrimeHistoryCompactCount

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeCompactVisits
open FiniteHistoryTransport ActualCoupledHistories ActualProcessCoupling PersistentFailureFlag

variable {w ell S : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

include hw hell hS0 hS hr hs hsS

theorem pathwise_compact_potential {R : ℝ} (hR : 0 ≤ R) (N : ℕ) :
    ∀ᵐ h ∂pathKernel (chain w ell S start) N (fun _ => some History.empty),
      pathSum (visit R) N h + potential R (last N h) ≤
        potential R (some (History.empty : History w ell S start)) := by
  let := chain_isMarkov hw hell hS0 hS hr hs hsS
  have hv : Measurable (visit (w:=w) (ell:=ell) (S:=S) (start:=start) R) := measurable_of_countable _
  have hp : Measurable (potential (w:=w) (ell:=ell) (S:=S) (start:=start) R) := measurable_of_countable _
  induction N with
  | zero =>
    change ∀ᵐ h ∂Measure.dirac (fun _ => some History.empty), _
    apply (ae_dirac_iff ((measurableSet_le
      ((pathSum_measurable hv 0).add (hp.comp (last_measurable 0))) measurable_const))).mpr
    simp [pathSum,last]
  | succ N ih =>
    apply ae_pathKernel_succ _ N _ (measurableSet_le
      ((pathSum_measurable hv (N+1)).add (hp.comp (last_measurable (N+1)))) measurable_const)
    filter_upwards [ih] with h hh
    filter_upwards [actual_row_drift_ae hell hr hs hR (last N h)] with y hy
    change pathSum (visit R) (N+1) (FiniteHistoryTransport.extend N h y) +
      potential R (last (N+1) (FiniteHistoryTransport.extend N h y)) ≤ _
    rw [pathSum_extend,extend_last]
    linarith

theorem pathwise_compact_count {R : ℝ} (hR : 0 ≤ R) (N : ℕ) :
    ∀ᵐ h ∂pathKernel (chain w ell S start) N (fun _ => some History.empty),
      pathSum (visit R) N h ≤ R+1 := by
  filter_upwards [pathwise_compact_potential hw hell hS0 hS hr hs hsS hR N] with h hh
  have hp := potential_nonneg hR (by linarith : 0 ≤ ell) hr hs (last N h)
  have hinit := potential_le (w:=w) (ell:=ell) (S:=S) (start:=start) hR (some History.empty)
  linarith

theorem sourceHistory_compact_count {R : ℝ} (hR : 0 ≤ R) (mesh : ℝ) (N : ℕ) :
    ∀ᵐ h ∂sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N,
      pathSum (visit R) N (mapHist (fun q => q.1.1) N h) ≤ R+1 := by
  have hP : MeasurableSet {h : Hist (ChainState w ell S start) N |
      pathSum (visit R) N h ≤ R+1} :=
    measurableSet_le (pathSum_measurable (measurable_of_countable _) N) measurable_const
  have hh : ∀ᵐ h ∂(sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N).map
      (mapHist (fun q => q.1.1) N), pathSum (visit R) N h ≤ R+1 := by
    rw [sourceHistoryLaw_prime]
    exact pathwise_compact_count hw hell hS0 hS hr hs hsS hR N
  exact (ae_map_iff (mapHist_measurable (by exact measurable_fst.comp measurable_fst) N).aemeasurable hP).mp hh

end NumberTheoryLean.PrimeHistoryCompactCount

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FullPathCompactSelection
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.FullPathCompactSelection

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain ActualProcessCoupling PersistentFailureFlag
open FiniteHistoryTransport ActualCoupledHistories PrimeHistoryCompactCount
open PrimeCompactVisits PrimeCompactWeights SourceCompactOccupation

variable {w ell S B : ℝ} {start : Node}

theorem fullCompactReward_envelope {R D : ℝ}
    (hbound : ∀ h : History w ell S start, h.node.gap ≤ R → scaledWeight w B start (some h) ≤ D)
    (N : ℕ) (h : Hist (FlagState (JointState w ell S start)) N) :
    fullCompactReward R w B start N h ≤
      ENNReal.ofReal D * ENNReal.ofReal (pathSum (visit R) N (mapHist (fun q => q.1.1) N h)) := by
  unfold fullCompactReward pathSum mapHist
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => visit_nonneg _ _),Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  exact compact_reward_envelope hbound _

variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem selected_compact_history_bound {R D : ℝ} (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hbound : ∀ h : History w ell S start, h.node.gap ≤ R → scaledWeight w B start (some h) ≤ D)
    (mesh : ℝ) (N : ℕ) {A : Set (Hist (FlagState (JointState w ell S start)) N)}
    (hA : MeasurableSet A) :
    (∫⁻ h, A.indicator (fullCompactReward R w B start N) h
      ∂sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N) ≤
      ENNReal.ofReal (D*(R+1)) * sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N A := by
  calc
    _ ≤ ∫⁻ h, A.indicator (fun _ => ENNReal.ofReal (D*(R+1))) h
        ∂sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N := by
      apply lintegral_mono_ae
      filter_upwards [sourceHistory_compact_count hw hell hS0 hS hr hs hsS hR mesh N] with h hh
      apply Set.indicator_le_indicator
      refine (fullCompactReward_envelope hbound N h).trans ?_
      rw [ENNReal.ofReal_mul hD]
      exact mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hh) zero_le
    _ = _ := lintegral_indicator_const hA _

end NumberTheoryLean.FullPathCompactSelection

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_SourceSelectedCompactOccupation
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SourceSelectedCompactOccupation

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain ActualProcessCoupling PersistentFailureFlag
open FiniteHistoryTransport ActualCoupledHistories FullPathCompactSelection
open PrimeCompactWeights PrimeCorrectionFactor PrimeBinMembership

theorem fullSourceLaw_eq {w ell S : ℝ} {start : Node}
    (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
    (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
    (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S) (mesh : ℝ) (N : ℕ) :
    fullSourceLaw w ell S start hs mesh N = sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N := rfl

theorem source_selected_compact (R : ℝ) (hR : 3 ≤ R) (d : ℝ) (_hd : 0 < d) :
    ∃ C w₀ : ℝ, 0 < C ∧ 1 < w₀ ∧ ∀ w : ℝ, w₀ ≤ w → ∀ ell B : ℝ,
      ∀ start : Node, ∀ hs : Valid start.side start.ratio,
      1 ≤ ell → ell ≤ B → 0 < B → 2 ≤ Real.log B → Real.log B ≤ d*Real.log w →
      start.side = .even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
      Consistent start → start.cutoff = B →
      let S := (Real.log B)^2
      ∀ mesh : ℝ, ∀ N : ℕ, ∀ A : Set (Hist (FlagState (JointState w ell S start)) N),
        MeasurableSet A →
        (∫⁻ h, A.indicator (fullCompactReward R w B start N) h
          ∂fullSourceLaw w ell S start hs mesh N) ≤
            ENNReal.ofReal C * fullSourceLaw w ell S start hs mesh N A := by
  have hD := compactConstant_pos hR
  have hevent := ((correctionBudget_tendsto_zero d).eventually
    (eventually_le_nhds (by norm_num : (0:ℝ) < 1))).and
      (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (d^2)))
  obtain ⟨W,hW⟩ := eventually_atTop.mp hevent
  refine ⟨compactConstant R*(R+1),max normalizationThreshold W,by positivity,
    normalizationThreshold_gt_one.trans_le (le_max_left _ _),?_⟩
  intro w hw ell B start hs hell hellB hB hlogB hcomp hi h199 h23 hc hcut
  dsimp only
  intro mesh N A hA
  have hnorm : normalizationThreshold ≤ w := (le_max_left _ _).trans hw
  have hwe := hW w ((le_max_right _ _).trans hw)
  have hscale := UniformBudgetRate.source_scale_bound hwe.2 hlogB hcomp
  have hS0 : 0 ≤ (Real.log B)^2 := sq_nonneg _
  have hsS : start.ratio ≤ (Real.log B)^2 := by nlinarith
  have he : start.gap = B*start.ratio := by
    have hh : start.cutoff = start.gap/start.ratio := hc
    rw [hcut] at hh
    exact ((eq_div_iff (valid_pos hs).ne').mp hh).symm
  have hr : 0 < start.gap := by rw [he]; exact mul_pos hB (valid_pos hs)
  have hbound := scaled_compact_bound hR hB hell hellB hlogB hcomp hwe.1 hi h199 h23 hc hcut
  rw [fullSourceLaw_eq hnorm hell hS0 hscale.1 hr hs hsS]
  exact selected_compact_history_bound hnorm hell hS0 hscale.1 hr hs hsS
    (by linarith) hD.le hbound mesh N hA

end NumberTheoryLean.SourceSelectedCompactOccupation

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_FullHistoryPrimeOccupation
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.FullHistoryPrimeOccupation

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain ActualProcessCoupling PersistentFailureFlag
open FiniteHistoryTransport ActualCoupledHistories SourceSelectedCompactOccupation
open PrimeCompactWeights PrimeFamilyOccupation ErdosPrimeInputs.PrimePrefixMass

variable {w ell S B : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem prime_coordinate (mesh : ℝ) (N k : ℕ) (hk : k ≤ N) :
    (sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N).map
      (fun h => (h ⟨k,by simpa using hk⟩).1.1) = pathLaw w ell S start k := by
  calc
    _ = ((sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N).map
        (fun h => h ⟨k,by simpa using hk⟩)).map (fun q => q.1.1) := by
      exact (Measure.map_map
        (f := fun h : Hist (FlagState (JointState w ell S start)) N => h ⟨k,Finset.mem_Iic.mpr hk⟩)
        (g := fun q : FlagState (JointState w ell S start) => q.1.1)
        (by fun_prop) (by fun_prop)).symm
    _ = _ := by rw [sourceHistoryLaw_coordinate hw hell hS0 hS hr hs hsS mesh N k hk,
      FlaggedSourceStart.sourceLaw_prime]

theorem fullListReward_integral (mesh : ℝ) (N : ℕ) (F : List ℕ → ℝ) :
    (∫⁻ h,fullListReward w B start F N h ∂sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N) =
      ∑ n ∈ range N, ∫⁻ z,ENNReal.ofReal (scaledWeight w B start z*listReward F z)
        ∂pathLaw w ell S start n := by
  unfold fullListReward
  rw [lintegral_finsetSum]
  · rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j _
    have hm : Measurable (fun z : ChainState w ell S start =>
        ENNReal.ofReal (scaledWeight w B start z*listReward F z)) := measurable_of_countable _
    rw [← prime_coordinate hw hell hS0 hS hr hs hsS mesh N j j.isLt.le,
      lintegral_map hm (by exact (measurable_fst.comp measurable_fst).comp (measurable_pi_apply _))]
  · intro j _
    exact (measurable_of_countable (fun z : ChainState w ell S start =>
      ENNReal.ofReal (scaledWeight w B start z*listReward F z))).comp
        ((measurable_fst.comp measurable_fst).comp (measurable_pi_apply _))

theorem finite_family_full_history (hB : 0 < B) (hsize : start.gap ≤ (23/10:ℝ)*B)
    (mesh : ℝ) (F : List ℕ → ℝ) (hF : ∀ ps,allowed w ell S start ps → 0 ≤ F ps) :
    (∫⁻ h,fullListReward w B start F (LowStateHorizon.sourceHorizon S B) h
      ∂sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh (LowStateHorizon.sourceHorizon S B)) =
      ENNReal.ofReal (B^2*(∑ ps ∈ retainedPrefixes w ell S start,prefixWeight ps*F ps)) := by
  rw [fullListReward_integral]
  exact finite_nonnegative_original_occupation hw hell hS0 hS hr hs hsS hB hsize F hF

end NumberTheoryLean.FullHistoryPrimeOccupation

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_NearPrefixOccurrence
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.CompactPrefixOccurrence

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain ActualProcessCoupling PersistentFailureFlag
open FiniteHistoryTransport ActualCoupledHistories SourceSelectedCompactOccupation
open FullHistoryPrimeOccupation FullPathCompactSelection SourceCompactOccupation
open PrimeCompactWeights PrimeCompactVisits PrimeFamilyOccupation

attribute [local instance] Classical.propDecidable

variable {w ell S B R : ℝ} {start : Node}

theorem occurs_measurable (E : Set (List ℕ)) (N : ℕ) :
    MeasurableSet {h : Hist (FlagState (JointState w ell S start)) N | occurs E N h} := by
  simp only [occurs,Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro j
  have hm : Measurable (fun h : Hist (FlagState (JointState w ell S start)) N =>
      (h ⟨j,Finset.mem_Iic.mpr j.isLt.le⟩).1.1) := by fun_prop
  exact hm (show MeasurableSet {z : ChainState w ell S start | selectedNode E z} from by trivial)

theorem listSelection_nonneg (E : Set (List ℕ)) (ps : List ℕ) : 0 ≤ listSelection E ps := by
  unfold listSelection
  split_ifs <;> norm_num

theorem selected_node_compact (E : Set (List ℕ))
    (hcompact : ∀ h : History w ell S start,h.primes ∈ E → h.node.gap ≤ R)
    (z : ChainState w ell S start) :
    ENNReal.ofReal (scaledWeight w B start z*listReward (listSelection E) z) ≤
      compactReward R w B start z := by
  cases z with
  | none => simp [scaledWeight,listReward,compactReward,visit]
  | some h =>
    by_cases he : h.primes ∈ E
    · simp [listReward,listSelection,he,compactReward,visit,hcompact h he]
    · simp [listReward,listSelection,he]

theorem full_selected_le_occurrence (E : Set (List ℕ))
    (hcompact : ∀ h : History w ell S start,h.primes ∈ E → h.node.gap ≤ R)
    (N : ℕ) (h : Hist (FlagState (JointState w ell S start)) N) :
    fullListReward w B start (listSelection E) N h ≤
      {h | occurs E N h}.indicator (fullCompactReward R w B start N) h := by
  by_cases ho : occurs E N h
  · rw [Set.indicator_of_mem (show h ∈ {h | occurs E N h} from ho)]
    exact Finset.sum_le_sum (fun j _ => selected_node_compact E hcompact _)
  · rw [Set.indicator_of_notMem (show h ∉ {h | occurs E N h} from ho)]
    apply le_of_eq
    unfold fullListReward
    apply Finset.sum_eq_zero
    intro j _
    have hj : ¬selectedNode E (h ⟨j,Finset.mem_Iic.mpr j.isLt.le⟩).1.1 :=
      fun hj => ho ⟨j,hj⟩
    cases hz : (h ⟨j,Finset.mem_Iic.mpr j.isLt.le⟩).1.1 with
    | none => simp [scaledWeight,listReward]
    | some p =>
      rw [hz] at hj
      change p.primes ∉ E at hj
      simp [listReward,listSelection,hj]

end NumberTheoryLean.CompactPrefixOccurrence

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_RetainedCompactEvent
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.RetainedCompactEvent

open _root_.Set _root_.Filter _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain ActualProcessCoupling PersistentFailureFlag
open PrimeBinMembership
open ActualCoupledHistories SourceSelectedCompactOccupation FullHistoryPrimeOccupation
open FullPathCompactSelection CompactPrefixOccurrence PrimeFamilyOccupation
open ErdosPrimeInputs.PrimePrefixMass

attribute [local instance] Classical.propDecidable

theorem retained_compact_event (R : ℝ) (hR : 3 ≤ R) (d : ℝ) (hd : 0 < d) :
    ∃ C w₀ : ℝ, 0 < C ∧ 1 < w₀ ∧ ∀ w : ℝ,w₀ ≤ w → ∀ ell B : ℝ,
      ∀ start : Node, ∀ hs : Valid start.side start.ratio,
      1 ≤ ell → ell ≤ B → 0 < B → 2 ≤ Real.log B → Real.log B ≤ d*Real.log w →
      start.side = .even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
      Consistent start → start.cutoff = B →
      let S := (Real.log B)^2
      let N := LowStateHorizon.sourceHorizon S B
      ∀ mesh : ℝ, ∀ E : Set (List ℕ),
        (∀ ps ∈ retainedPrefixes w ell S start, ps ∈ E → (terminal w start ps).gap ≤ R) →
        ENNReal.ofReal (B^2*(∑ ps ∈ (retainedPrefixes w ell S start).filter (· ∈ E),prefixWeight ps)) ≤
          ENNReal.ofReal C * fullSourceLaw w ell S start hs mesh N {h | occurs E N h} := by
  obtain ⟨C,W,hC,hW,hsel⟩ := source_selected_compact R hR d hd
  obtain ⟨W₁,hW₁⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (d^2)))
  refine ⟨C,max W (max normalizationThreshold W₁),hC,hW.trans_le (le_max_left _ _),?_⟩
  intro w hw ell B start hs hell hellB hB hlogB hcomp hi h199 h23 hc hcut
  dsimp only
  intro mesh E hcompact
  have hwW : W ≤ w := (le_max_left _ _).trans hw
  have hnorm : normalizationThreshold ≤ w :=
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans hw
  have hlogw : d^2 ≤ Real.log w := hW₁ w
    ((le_trans (le_max_right _ _) (le_max_right _ _)).trans hw)
  have hscale := UniformBudgetRate.source_scale_bound hlogw hlogB hcomp
  have hS0 : 0 ≤ (Real.log B)^2 := sq_nonneg _
  have hsS : start.ratio ≤ (Real.log B)^2 := by nlinarith
  have he : start.gap = B*start.ratio := by
    have hh : start.cutoff = start.gap/start.ratio := hc
    rw [hcut] at hh
    exact ((eq_div_iff (valid_pos hs).ne').mp hh).symm
  have hr : 0 < start.gap := by rw [he]; exact mul_pos hB (valid_pos hs)
  have hsize : start.gap ≤ (23/10:ℝ)*B := by rw [he]; nlinarith
  have hw1 : 1 < w := normalizationThreshold_gt_one.trans_le hnorm
  have hnode : ∀ h : History w ell ((Real.log B)^2) start,h.primes ∈ E → h.node.gap ≤ R := by
    intro h hh
    exact hcompact h.primes ((mem_retainedPrefixes hw1 start h.primes).mpr h.admissible) hh
  have hsum : (∑ ps ∈ retainedPrefixes w ell ((Real.log B)^2) start,prefixWeight ps*listSelection E ps) =
      ∑ ps ∈ (retainedPrefixes w ell ((Real.log B)^2) start).filter (· ∈ E),prefixWeight ps := by
    simp [Finset.sum_filter,listSelection,mul_ite]
  rw [← hsum,← finite_family_full_history hnorm hell hS0 hscale.1 hr hs hsS hB hsize
    mesh (listSelection E) (fun ps _ => listSelection_nonneg E ps)]
  calc
    _ ≤ ∫⁻ h,{h | occurs E (LowStateHorizon.sourceHorizon ((Real.log B)^2) B) h}.indicator
        (fullCompactReward R w B start (LowStateHorizon.sourceHorizon ((Real.log B)^2) B)) h
        ∂sourceHistoryLaw hnorm hell hS0 hscale.1 hr hs hsS mesh
          (LowStateHorizon.sourceHorizon ((Real.log B)^2) B) :=
      lintegral_mono (full_selected_le_occurrence E hnode _)
    _ ≤ _ := by
      have hh := hsel w hwW ell B start hs hell hellB hB hlogB hcomp hi h199 h23 hc hcut
        mesh (LowStateHorizon.sourceHorizon ((Real.log B)^2) B) _ (occurs_measurable E _)
      exact hh

end NumberTheoryLean.RetainedCompactEvent

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_CompactSelectedPartition
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.PrimeFamilyOccupation
attribute [local instance] Classical.propDecidable
open FinitePathGeometry PrimeHistories PrimeTiltGeometry
open ActualPrimeHigh

theorem retained_no_high {w ell S : ℝ} {start : Node} {ps : List ℕ}
    (hsS : start.ratio ≤ S) (hp : allowed w ell S start ps) :
    ¬actualHasHigh w S start ps := by
  rintro ⟨pre,suf,he,hh⟩
  have hpre := (allowed_append w ell S start pre suf).mp (he ▸ hp) |>.1
  exact (not_lt_of_ge (terminal_ratio_le hsS hpre)) hh

theorem allowed_of_uncapped_prefix_ceiling {w ell S : ℝ} {start : Node} {ps : List ℕ}
    (hp : uncappedAllowed w ell start ps)
    (hbound : ∀ pre suf : List ℕ, ps = pre++suf → (terminal w start pre).ratio ≤ S) :
    allowed w ell S start ps := by
  classical
  induction ps generalizing start with
  | nil => exact allowed_nil w ell S start
  | cons p ps ih =>
    obtain ⟨hc,ht⟩ := hp
    have hpS : (step w start p).ratio ≤ S := by
      simpa only [terminal_cons,terminal_nil] using hbound [p] ps rfl
    have hb : ∀ pre suf : List ℕ, ps = pre++suf →
        (terminal w (step w start p) pre).ratio ≤ S := by
      intro pre suf he
      exact hbound (p::pre) suf (by rw [List.cons_append,he])
    obtain ⟨hprime,hlo,hcap,hmin⟩ := Finset.mem_filter.mp hc
    apply (allowed_cons w ell S start p ps).mpr
    exact ⟨Finset.mem_filter.mpr ⟨hprime,hlo,hcap,hmin,hpS⟩,ih ht hb⟩

theorem allowed_iff_uncapped_no_high {w ell S : ℝ} {start : Node} (hsS : start.ratio ≤ S)
    (ps : List ℕ) : allowed w ell S start ps ↔
      uncappedAllowed w ell start ps ∧ ¬actualHasHigh w S start ps := by
  constructor
  · intro hp
    exact ⟨(uncapped_iff_exists_ceiling w ell start ps).mpr ⟨S,hsS,hp⟩,retained_no_high hsS hp⟩
  · rintro ⟨hp,hh⟩
    apply allowed_of_uncapped_prefix_ceiling hp
    intro pre suf he
    exact le_of_not_gt (fun h => hh ⟨pre,suf,he,h⟩)

theorem retained_eq_nonhigh {w ell S : ℝ} (hw : 1 < w) {start : Node} (hsS : start.ratio ≤ S) :
    retainedPrefixes w ell S start =
      (uncappedPrefixes w ell start).filter (fun ps => ¬actualHasHigh w S start ps) := by
  classical
  ext ps
  rw [mem_retainedPrefixes hw,Finset.mem_filter,mem_uncappedPrefixes hw]
  exact allowed_iff_uncapped_no_high hsS ps

theorem uncapped_sum_partition {w ell S : ℝ} (hw : 1 < w) {start : Node}
    (hsS : start.ratio ≤ S) (F : List ℕ → ℝ) :
    (∑ ps ∈ uncappedPrefixes w ell start,F ps) =
      (∑ ps ∈ retainedPrefixes w ell S start,F ps) +
      ∑ ps ∈ (uncappedPrefixes w ell start).filter (actualHasHigh w S start),F ps := by
  classical
  rw [retained_eq_nonhigh hw hsS]
  exact (Finset.sum_filter_not_add_sum_filter _ _ _).symm

end NumberTheoryLean.PrimeFamilyOccupation

end

section

namespace NumberTheoryLean.CompactSelectedPartition

open _root_.Set _root_.Finset
open FinitePathGeometry PrimeHistories PrimeFamilyOccupation ActualPrimeHigh
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail

attribute [local instance] Classical.propDecidable

theorem selected_uncapped_partition {w ell S : ℝ} (hw : 1 < w) {start : Node}
    (hsS : start.ratio ≤ S) (E : Set (List ℕ)) :
    (∑ ps ∈ (uncappedPrefixes w ell start).filter (· ∈ E),prefixWeight ps) =
      (∑ ps ∈ (retainedPrefixes w ell S start).filter (· ∈ E),prefixWeight ps) +
      ∑ ps ∈ ((uncappedPrefixes w ell start).filter (actualHasHigh w S start)).filter (· ∈ E),
        prefixWeight ps := by
  have h := uncapped_sum_partition (ell:=ell) hw hsS (fun ps => if ps ∈ E then prefixWeight ps else 0)
  simpa only [Finset.sum_filter] using h

theorem selected_uncapped_le {w ell S R : ℝ} (hw : 1 < w) {start : Node}
    (hsS : start.ratio ≤ S) (E : Set (List ℕ))
    (hcompact : ∀ ps ∈ uncappedPrefixes w ell start,ps ∈ E → (terminal w start ps).gap ≤ R) :
    (∑ ps ∈ (uncappedPrefixes w ell start).filter (· ∈ E),prefixWeight ps) ≤
      (∑ ps ∈ (retainedPrefixes w ell S start).filter (· ∈ E),prefixWeight ps) +
      uncappedLowGapHighMass w ell start S R := by
  rw [selected_uncapped_partition hw hsS E]
  apply add_le_add le_rfl
  unfold uncappedLowGapHighMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ps hp
    obtain ⟨hhigh,hE⟩ := Finset.mem_filter.mp hp
    obtain ⟨hps,hh⟩ := Finset.mem_filter.mp hhigh
    exact Finset.mem_filter.mpr ⟨hps,hcompact ps hps hE,hh⟩
  · intro ps _ _
    exact prefixWeight_nonneg ps

end NumberTheoryLean.CompactSelectedPartition

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Conclusions_JacobsthalSourceScale
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.JacobsthalSourceScale

open _root_.Filter _root_.Asymptotics
open scoped Topology

theorem log_square_le_sqrt_eventually : ∀ᶠ L : ℝ in atTop,(Real.log L)^2 ≤ Real.sqrt L := by
  have h := (isLittleO_log_rpow_rpow_atTop (2:ℝ) (s:=1/2) (by norm_num)).bound (by norm_num : (0:ℝ)<1)
  filter_upwards [h,eventually_gt_atTop (1:ℝ)] with L hL hpos
  have hr : 0 ≤ L^((1/2:ℝ)) := Real.rpow_nonneg (by linarith) _
  simpa only [Real.rpow_ofNat,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (Real.log L)),
    abs_of_nonneg hr,one_mul,← Real.sqrt_eq_rpow,abs_of_nonneg (Real.sqrt_nonneg L)] using hL

theorem sourceW_bounds_eventually : ∀ᶠ L : ℝ in atTop,
    1 < sourceW L ∧ Real.sqrt L ≤ sourceW L ∧ sourceW L ≤ L := by
  filter_upwards [log_square_le_sqrt_eventually,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with L hsmall hL hlog
  have hL0 : 0 < L := by linarith
  have hden : 0 < (Real.log L)^2 := sq_pos_of_pos (by linarith)
  have hsq : Real.sqrt L ≤ sourceW L := by
    apply (le_div_iff₀ hden).mpr
    have hm := mul_le_mul_of_nonneg_left hsmall (Real.sqrt_nonneg L)
    simpa only [Real.mul_self_sqrt hL0.le] using hm
  have hlow : 1 < Real.sqrt L := by
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 1) hL
  refine ⟨hlow.trans_le hsq,hsq,?_⟩
  exact div_le_self hL0.le (by nlinarith : 1 ≤ (Real.log L)^2)

theorem sourceW_tendsto : Tendsto sourceW atTop atTop := by
  apply tendsto_atTop.mpr
  intro R
  filter_upwards [sourceW_bounds_eventually,Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop R)] with L hW hR
  exact hR.trans hW.2.1

theorem source_scale_eventually : ∀ᶠ L : ℝ in atTop,
    1 < sourceW L ∧ 0 < sourceB L ∧ Real.sqrt L ≤ sourceB L ∧ sourceB L ≤ L ∧
      Real.log (sourceB L) ≤ 2*Real.log (sourceW L) := by
  filter_upwards [sourceW_bounds_eventually,log_square_le_sqrt_eventually,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    sourceW_tendsto.eventually (eventually_ge_atTop (Real.exp 1))] with L hW hsmall hL hlog hWexp
  have hL0 : 0 < L := by linarith
  have hW0 : 0 < sourceW L := by linarith [hW.1]
  have hlogW : 1 ≤ Real.log (sourceW L) := by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hWexp
  have hlogWL : Real.log (sourceW L) ≤ Real.log L := Real.log_le_log hW0 hW.2.2
  have hlogSmall : Real.log (sourceW L) ≤ Real.sqrt L := by
    have hh : Real.log L ≤ (Real.log L)^2 := by nlinarith
    exact hlogWL.trans (hh.trans hsmall)
  have hBpos : 0 < sourceB L := div_pos hL0 (by linarith)
  have hBsq : Real.sqrt L ≤ sourceB L := by
    apply (le_div_iff₀ (show 0 < Real.log (sourceW L) by linarith)).mpr
    have hm := mul_le_mul_of_nonneg_left hlogSmall (Real.sqrt_nonneg L)
    simpa only [Real.mul_self_sqrt hL0.le] using hm
  have hBL : sourceB L ≤ L := div_le_self hL0.le hlogW
  have hLWsq : L ≤ (sourceW L)^2 := by
    have hh := mul_self_le_mul_self (Real.sqrt_nonneg L) hW.2.1
    nlinarith [Real.sq_sqrt hL0.le]
  have hcomp := Real.log_le_log hBpos (hBL.trans hLWsq)
  refine ⟨hW.1,hBpos,hBsq,hBL,?_⟩
  simpa only [Real.log_pow,Nat.cast_ofNat] using hcomp

theorem sourceB_tendsto : Tendsto sourceB atTop atTop := by
  apply tendsto_atTop.mpr
  intro R
  filter_upwards [source_scale_eventually,Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop R)] with L h hR
  exact hR.trans h.2.2.1

end NumberTheoryLean.JacobsthalSourceScale

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_UncappedCompactEvent
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.UncappedCompactEvent

open _root_.Set _root_.Filter _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain ActualProcessCoupling PersistentFailureFlag
open PrimeBinMembership
open ActualCoupledHistories SourceSelectedCompactOccupation FullHistoryPrimeOccupation
open CompactPrefixOccurrence PrimeFamilyOccupation ActualPrimeHigh CompactSelectedPartition
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail RetainedCompactEvent

attribute [local instance] Classical.propDecidable

theorem uncapped_compact_event (R : ℝ) (hR : 3 ≤ R) (d : ℝ) (hd : 0 < d) :
    ∃ C w₀ : ℝ, 0 < C ∧ 1 < w₀ ∧ ∀ A : ℝ, ∃ B₀ : ℝ, 0 < B₀ ∧
      ∀ B w : ℝ, B₀ ≤ B → w₀ ≤ w → ∀ ell : ℝ, ∀ start : Node,
      ∀ hs : Valid start.side start.ratio,
      1 ≤ ell → ell ≤ B → Real.log B ≤ d*Real.log w →
      start.side = .even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
      Consistent start → start.cutoff = B →
      let S := (Real.log B)^2
      let N := LowStateHorizon.sourceHorizon S B
      ∀ mesh : ℝ, ∀ E : Set (List ℕ),
        (∀ ps ∈ uncappedPrefixes w ell start, ps ∈ E → (terminal w start ps).gap ≤ R) →
        (∑ ps ∈ (uncappedPrefixes w ell start).filter (· ∈ E),prefixWeight ps) ≤
          (C/B^2) * (fullSourceLaw w ell S start hs mesh N {h | occurs E N h}).toReal + B^(-A) := by
  obtain ⟨C,W,hC,hW,hret⟩ := retained_compact_event R hR d hd
  obtain ⟨WH,hWH,hhigh⟩ := uncapped_low_gap_high_removal
  let w₀ := max W (max WH (max normalizationThreshold (Real.exp (d^2))))
  refine ⟨C,w₀,hC,hW.trans_le (le_max_left _ _),?_⟩
  intro A
  obtain ⟨BH,hBH⟩ := eventually_atTop.mp (hhigh R (by linarith) A)
  refine ⟨max (Real.exp 2) BH,(Real.exp_pos 2).trans_le (le_max_left _ _),?_⟩
  intro B w hB₀ hw ell start hs hell hellB hcomp hi h199 h23 hc hcut
  dsimp only
  intro mesh E hcompact
  have heB : Real.exp 2 ≤ B := (le_max_left _ _).trans hB₀
  have hB : 0 < B := (Real.exp_pos 2).trans_le heB
  have hlogB : 2 ≤ Real.log B := (Real.le_log_iff_exp_le hB).mpr heB
  have hwW : W ≤ w := (le_max_left _ _).trans hw
  have hwH : WH ≤ w := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hw
  have hnorm : normalizationThreshold ≤ w :=
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))).trans hw
  have hexp : Real.exp (d^2) ≤ w :=
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))).trans hw
  have hw1 : 1 < w := normalizationThreshold_gt_one.trans_le hnorm
  have hlogw : d^2 ≤ Real.log w := (Real.le_log_iff_exp_le (by linarith : 0 < w)).mpr hexp
  have hscale := UniformBudgetRate.source_scale_bound hlogw hlogB hcomp
  have hS0 : 0 ≤ (Real.log B)^2 := sq_nonneg _
  have hsS : start.ratio ≤ (Real.log B)^2 := by nlinarith
  have he : start.gap = B*start.ratio := by
    have hh : start.cutoff = start.gap/start.ratio := hc
    rw [hcut] at hh
    exact ((eq_div_iff (valid_pos hs).ne').mp hh).symm
  have hr : 0 < start.gap := by rw [he]; exact mul_pos hB (valid_pos hs)
  have hcompactRet : ∀ ps ∈ retainedPrefixes w ell ((Real.log B)^2) start,
      ps ∈ E → (terminal w start ps).gap ≤ R := by
    intro ps hp hE
    rw [retained_eq_nonhigh hw1 hsS] at hp
    exact hcompact ps (Finset.mem_filter.mp hp).1 hE
  have hretain := hret w hwW ell B start hs hell hellB hB hlogB hcomp hi h199 h23 hc hcut
    mesh E hcompactRet
  let μ := fullSourceLaw w ell ((Real.log B)^2) start hs mesh
    (LowStateHorizon.sourceHorizon ((Real.log B)^2) B)
  let U : Set (FiniteHistoryTransport.Hist
      (FlagState (JointState w ell ((Real.log B)^2) start))
      (LowStateHorizon.sourceHorizon ((Real.log B)^2) B)) :=
    {h | occurs E (LowStateHorizon.sourceHorizon ((Real.log B)^2) B) h}
  have : IsProbabilityMeasure μ := by
    dsimp [μ]
    rw [fullSourceLaw_eq hnorm hell hS0 hscale.1 hr hs hsS]
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hm : 0 ≤ ∑ ps ∈ (retainedPrefixes w ell ((Real.log B)^2) start).filter (· ∈ E),prefixWeight ps :=
    Finset.sum_nonneg (fun ps _ => prefixWeight_nonneg ps)
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ U)) hretain
  rw [ENNReal.toReal_ofReal (mul_nonneg (sq_nonneg B) hm),ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hC.le] at hreal
  have hretReal : (∑ ps ∈ (retainedPrefixes w ell ((Real.log B)^2) start).filter (· ∈ E),prefixWeight ps) ≤
      (C/B^2)*(μ U).toReal := by
    calc
      _ ≤ (C*(μ U).toReal)/B^2 := (le_div_iff₀ (sq_pos_of_pos hB)).mpr (by nlinarith only [hreal])
      _ = _ := by ring
  have hhighB := hBH B ((le_max_right _ _).trans hB₀) w hwH ell hell hellB start hcut hr hs hc
  exact (selected_uncapped_le hw1 hsS E hcompact).trans (add_le_add hretReal hhighB)

end NumberTheoryLean.UncappedCompactEvent

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PaperMissingPrimeWindow
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.WeightedMissingPrimeWindow

open _root_.Set _root_.Filter _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeBinMembership ActualPrimeHigh
open PriorPrimeWindow MovingPrimeWindowProbability UncappedCompactEvent
open SourceSelectedCompactOccupation CompactPrefixOccurrence
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail

attribute [local instance] Classical.propDecidable

theorem weighted_missing_prime_window : ∃ κ₀ : ℝ, 0 < κ₀ ∧
    ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∀ R d eps : ℝ, 3 ≤ R → 0 < d → 0 < eps →
      ∃ rho : ℝ, 10 < rho ∧ ∀ K : ℝ, 0 < K → ∃ B₀ w₀ : ℝ, 0 < B₀ ∧ 1 < w₀ ∧
      ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w → ∀ ell : ℝ, ∀ start : Node,
      ∀ _hs : Valid start.side start.ratio,
      1 ≤ ell → ell ≤ B → Real.log B ≤ d*Real.log w →
      start.side = .even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
      Consistent start → start.cutoff = B → w ≤ start.gap →
      ∀ E : Set (List ℕ),
        (∀ ps ∈ uncappedPrefixes w ell start, ps ∈ E → (terminal w start ps).gap ≤ R ∧
          ¬hasPrimeWindow w (K*(Real.log w)^2) (rho*K*(Real.log w)^2) start ps) →
        B^2*(∑ ps ∈ (uncappedPrefixes w ell start).filter (· ∈ E),prefixWeight ps) ≤ eps := by
  obtain ⟨κ₀,hκ₀,hProb⟩ := source_missing_window_probability_jb247
  refine ⟨κ₀,hκ₀,?_⟩
  intro κ hκ hκle R d eps hR hd heps
  obtain ⟨C,WC,hC,hWC,hCompact⟩ := uncapped_compact_event R hR d hd
  let delta := eps/(2*C)
  have hdelt : 0 < delta := by dsimp [delta] <;> positivity
  obtain ⟨rho,hrho,hMoving⟩ := hProb κ hκ hκle R d delta hd hdelt
  refine ⟨rho,hrho,?_⟩
  intro K hK
  obtain ⟨WP,hWP,hP⟩ := hMoving K hK
  obtain ⟨BC,hBC,hCbound⟩ := hCompact (3:ℝ)
  refine ⟨max BC (max (Real.exp 2) (2/eps)),max WC WP,
    hBC.trans_le (le_max_left _ _),hWC.trans_le (le_max_left _ _),?_⟩
  intro B w hBB hw ell start hs hell hellB hcomp hi h199 h23 hc hcut hgap E hE
  have hB : 0 < B := hBC.trans_le ((le_max_left _ _).trans hBB)
  have heB : Real.exp 2 ≤ B := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hBB
  have hlogB : 2 ≤ Real.log B := (Real.le_log_iff_exp_le hB).mpr heB
  have hwC : WC ≤ w := (le_max_left _ _).trans hw
  have hwP : WP ≤ w := (le_max_right _ _).trans hw
  have hw1 : 1 < w := hWC.trans_le hwC
  have hsS : start.ratio ≤ (Real.log B)^2 := by nlinarith
  have hHist : ∀ p : History w ell ((Real.log B)^2) start,p.primes ∈ E → p.node.gap ≤ R ∧
      ¬hasPrimeWindow w (K*(Real.log w)^2) (rho*K*(Real.log w)^2) start p.primes := by
    intro p hp
    have hUn : p.primes ∈ uncappedPrefixes w ell start :=
      (mem_uncappedPrefixes hw1 start p.primes).mpr
        ((uncapped_iff_exists_ceiling w ell start p.primes).mpr ⟨(Real.log B)^2,hsS,p.admissible⟩)
    exact hE p.primes hUn hp
  have hProbability := hP w hwP ell B start hs hell hB hlogB hcomp hi h199 h23 hc hcut hgap E hHist
  have hpReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hProbability
  rw [ENNReal.toReal_ofReal hdelt.le] at hpReal
  have hMass := hCbound B w ((le_max_left _ _).trans hBB) hwC ell start hs hell hellB hcomp
    hi h199 h23 hc hcut (ExponentialMesh.mesh κ w) E (fun ps hp hsel => (hE ps hp hsel).1)
  have hMass' : (∑ ps ∈ (uncappedPrefixes w ell start).filter (· ∈ E),prefixWeight ps) ≤
      (C/B^2)*delta+B^(-(3:ℝ)) :=
    hMass.trans (add_le_add (mul_le_mul_of_nonneg_left hpReal (by positivity)) le_rfl)
  have hlarge : 2/eps ≤ B := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hBB
  have hinv : 1/B ≤ eps/2 := by
    have hh := (div_le_iff₀ heps).mp hlarge
    apply (div_le_iff₀ hB).mpr
    nlinarith
  have hCD : C*delta = eps/2 := by dsimp [delta]; field_simp [hC.ne']
  have hpow : B^(-(3:ℝ)) = (B^3)⁻¹ := by rw [Real.rpow_neg hB.le,Real.rpow_ofNat]
  calc
    _ ≤ B^2*((C/B^2)*delta+B^(-(3:ℝ))) := mul_le_mul_of_nonneg_left hMass' (sq_nonneg B)
    _ = C*delta+1/B := by rw [hpow]; field_simp [hB.ne']
    _ ≤ eps := by rw [hCD]; linarith

end NumberTheoryLean.WeightedMissingPrimeWindow

end

section

namespace NumberTheoryLean.MissingWindowPrimeMass

open _root_.Set _root_.Finset
open FinitePathGeometry PrimeHistories PrimeBinMembership ActualPrimeHigh PriorPrimeWindow
open ErdosPrimeInputs.PrimePrefixMass WeightedMissingPrimeWindow

theorem moving_missing_prefix_mass (R d eps : ℝ) (hR : 3 ≤ R) (hd : 0 < d) (heps : 0 < eps) :
    ∃ rho : ℝ, 10 < rho ∧ ∀ K : ℝ, 0 < K → ∃ B₀ w₀ : ℝ, 0 < B₀ ∧ 1 < w₀ ∧
      ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w → ∀ ell : ℝ, ∀ start : Node,
      ∀ _hs : Valid start.side start.ratio,
      1 ≤ ell → ell ≤ B → Real.log B ≤ d*Real.log w →
      start.side = .even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
      Consistent start → start.cutoff = B → w ≤ start.gap →
      B^2*(∑ ps ∈ missingWindowPrefixes w ell R (K*(Real.log w)^2)
        (rho*K*(Real.log w)^2) start,prefixWeight ps) ≤ eps := by
  classical
  obtain ⟨κ₀,hκ₀,hbound⟩ := weighted_missing_prime_window
  obtain ⟨rho,hrho,hK⟩ := hbound κ₀ hκ₀ le_rfl R d eps hR hd heps
  refine ⟨rho,hrho,?_⟩
  intro K hKpos
  obtain ⟨B₀,w₀,hB₀,hw₀,h⟩ := hK K hKpos
  refine ⟨B₀,w₀,hB₀,hw₀,?_⟩
  intro B w hB hw ell start hs hell hellB hcomp hi h199 h23 hc hcut hgap
  let E : Set (List ℕ) := {ps | (terminal w start ps).gap ≤ R ∧
    ¬hasPrimeWindow w (K*(Real.log w)^2) (rho*K*(Real.log w)^2) start ps}
  have hh := h B w hB hw ell start hs hell hellB hcomp hi h199 h23 hc hcut hgap E
    (fun _ _ hmem => hmem)
  have hset : missingWindowPrefixes w ell R (K*(Real.log w)^2) (rho*K*(Real.log w)^2) start =
      (uncappedPrefixes w ell start).filter (fun ps => ps ∈ E) := by
    ext ps
    simp only [missingWindowPrefixes,Finset.mem_filter,E,Set.mem_ofPred_eq]
  rw [hset]
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply Finset.sum_congr
  · ext ps
    simp only [Finset.mem_filter]
  · intro ps _
    rfl

end NumberTheoryLean.MissingWindowPrimeMass

end

section

namespace NumberTheoryLean.PaperMissingPrimeWindow

open _root_.Set _root_.Filter _root_.Finset
open scoped Topology
open FinitePathGeometry PrimeHistories PrimeBinMembership ActualPrimeHigh
open JacobsthalSourceScale MissingWindowPrimeMass ErdosPrimeInputs.PrimePrefixMass

theorem sourceW_le_sourceB_eventually : ∀ᶠ L : ℝ in atTop,sourceW L ≤ sourceB L := by
  filter_upwards [sourceW_bounds_eventually,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with L hW hL hlog
  have hLp : 0 < L := by linarith
  have hlogW : 0 < Real.log (sourceW L) := Real.log_pos hW.1
  have hd : Real.log (sourceW L) ≤ (Real.log L)^2 := by
    have hh := Real.log_le_log (by linarith [hW.1] : 0 < sourceW L) hW.2.2
    nlinarith
  exact div_le_div_of_nonneg_left hLp.le hlogW hd

theorem paper_missing_prime_window_mass_jb247_oai (R eps : ℝ) (hR : 3 ≤ R) (heps : 0 < eps) :
    ∃ rho : ℝ, 10 < rho ∧ ∀ K : ℝ, 0 < K → ∃ L₀ : ℝ, 0 < L₀ ∧
      ∀ L : ℝ,L₀ ≤ L → ∀ ell : ℝ,1 ≤ ell → ell ≤ 2 → ∀ start : Node,
      start.side = .even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
      Consistent start → start.cutoff = sourceB L →
      (sourceB L)^2*(∑ ps ∈ missingWindowPrefixes (sourceW L) ell R
        (K*(Real.log (sourceW L))^2) (rho*K*(Real.log (sourceW L))^2) start,prefixWeight ps) ≤ eps := by
  obtain ⟨rho,hrho,hK⟩ := moving_missing_prefix_mass R 2 eps hR (by norm_num) heps
  refine ⟨rho,hrho,?_⟩
  intro K hKpos
  obtain ⟨B₀,w₀,_hB₀,_hw₀,h⟩ := hK K hKpos
  have he : ∀ᶠ L : ℝ in atTop,∀ ell : ℝ,1 ≤ ell → ell ≤ 2 → ∀ start : Node,
      start.side = .even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
      Consistent start → start.cutoff = sourceB L →
      (sourceB L)^2*(∑ ps ∈ missingWindowPrefixes (sourceW L) ell R
        (K*(Real.log (sourceW L))^2) (rho*K*(Real.log (sourceW L))^2) start,prefixWeight ps) ≤ eps := by
    filter_upwards [source_scale_eventually,sourceW_le_sourceB_eventually,
      sourceB_tendsto.eventually (eventually_ge_atTop (max B₀ 2)),
      sourceW_tendsto.eventually (eventually_ge_atTop w₀)] with L hscale hWB hB hw
    intro ell hell hell2 start hi h199 h23 hc hcut
    have hs : Valid start.side start.ratio := by rw [hi]; change 198/100 ≤ start.ratio; linarith
    have heq : start.gap = sourceB L*start.ratio := by
      have hh : start.cutoff = start.gap/start.ratio := hc
      rw [hcut] at hh
      exact ((eq_div_iff (valid_pos hs).ne').mp hh).symm
    have hgap : sourceW L ≤ start.gap := by
      have hBg : sourceB L ≤ start.gap := by rw [heq]; nlinarith [hscale.2.1]
      exact hWB.trans hBg
    exact h (sourceB L) (sourceW L) ((le_max_left _ _).trans hB) hw ell start hs hell
      (hell2.trans ((le_max_right _ _).trans hB)) hscale.2.2.2.2 hi h199 h23 hc hcut hgap
  obtain ⟨L₁,hL₁⟩ := eventually_atTop.mp he
  refine ⟨max 1 L₁,by have hh := le_max_left (1:ℝ) L₁; linarith,?_⟩
  intro L hL
  exact hL₁ L ((le_max_right _ _).trans hL)

end NumberTheoryLean.PaperMissingPrimeWindow

end

end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.NumberTheoryLean.PaperMissingPrimeWindow.paper_missing_prime_window_mass_jb247_oai := @OAI.Erdos970.NumberTheoryLean.PaperMissingPrimeWindow.paper_missing_prime_window_mass_jb247_oai
