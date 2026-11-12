-- Prove2me | solution 1 for OAI.Erdos970.ErdosSourceLineBudget.uniform_original_rich_line_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:57:30.803797+00:00
-- url     : https://prove2.me/submissions/60e11bbe-2bba-4404-aaf9-c80cec6f3fa4

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
import Definitions.Def_OAIQ247J008

section
-- module Solutions.OAIQ247_JB.Compat
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_BivariateCalculus
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosImplicitCurvature

theorem mixed_partials (Q : Bivariate) : partialY (partialX Q) = partialX (partialY Q) := by
  classical
  ext m
  simp [partialX, partialY, MvPolynomial.coeff_pderiv,
    add_assoc, add_left_comm, add_comm, mul_left_comm, mul_comm]
  ring

theorem hasDerivAt_peval_graph (Q : Bivariate) (f : ℝ → ℝ) (df x : ℝ)
    (hf : HasDerivAt f df x) :
    HasDerivAt (fun t => peval Q t (f t))
      (peval (partialX Q) x (f x)+peval (partialY Q) x (f x)*df) x := by
  simpa using hasDerivAt_peval Q id f 1 df x (hasDerivAt_id x) hf

end ErdosImplicitCurvature

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_ImplicitDerivatives
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Filter
open scoped Topology
namespace ErdosImplicitCurvature

theorem graph_zero_near (Q : Bivariate) (f : ℝ → ℝ) {I : Set ℝ} (hI : IsOpen I)
    (hcurve : ∀ t ∈ I, peval Q t (f t) = 0) {x : ℝ} (hx : x ∈ I) :
    (fun t => peval Q t (f t)) =ᶠ[𝓝 x] (fun _ => 0) := by
  filter_upwards [hI.mem_nhds hx] with t ht
  exact hcurve t ht

theorem implicit_first_equation (Q : Bivariate) (f : ℝ → ℝ) {I : Set ℝ}
    (hI : IsOpen I) (hf : DifferentiableOn ℝ f I)
    (hcurve : ∀ t ∈ I, peval Q t (f t) = 0) {x : ℝ} (hx : x ∈ I) :
    peval (partialX Q) x (f x)+peval (partialY Q) x (f x)*deriv f x = 0 := by
  have hd := hasDerivAt_peval_graph Q f (deriv f x) x
    (hf.differentiableAt (hI.mem_nhds hx)).hasDerivAt
  have hz := (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
    (graph_zero_near Q f hI hcurve hx)
  exact hd.unique hz

theorem implicit_first_derivative (Q : Bivariate) (f : ℝ → ℝ) {I : Set ℝ}
    (hI : IsOpen I) (hf : DifferentiableOn ℝ f I)
    (hcurve : ∀ t ∈ I, peval Q t (f t) = 0) {x : ℝ} (hx : x ∈ I)
    (hQy : peval (partialY Q) x (f x) ≠ 0) :
    deriv f x = -peval (partialX Q) x (f x)/peval (partialY Q) x (f x) := by
  apply (eq_div_iff hQy).mpr
  have h := implicit_first_equation Q f hI hf hcurve hx
  nlinarith only [h]

theorem implicit_second_equation (Q : Bivariate) (f : ℝ → ℝ) {I : Set ℝ}
    (hI : IsOpen I) (hf : ContDiffOn ℝ 2 f I)
    (hcurve : ∀ t ∈ I, peval Q t (f t) = 0) {x : ℝ} (hx : x ∈ I) :
    peval (partialX (partialX Q)) x (f x) +
      2*peval (partialX (partialY Q)) x (f x)*deriv f x +
      peval (partialY (partialY Q)) x (f x)*(deriv f x)^2 +
      peval (partialY Q) x (f x)*deriv (deriv f) x = 0 := by
  have hf1 : DifferentiableOn ℝ f I := hf.differentiableOn (by norm_num)
  have hdf : ContDiffOn ℝ 1 (deriv f) I := hf.deriv_of_isOpen hI (by norm_num)
  have hd1 := (hf1.differentiableAt (hI.mem_nhds hx)).hasDerivAt
  have hd2 := ((hdf.differentiableOn (by norm_num)).differentiableAt (hI.mem_nhds hx)).hasDerivAt
  have hPx := hasDerivAt_peval_graph (partialX Q) f (deriv f x) x hd1
  have hPy := hasDerivAt_peval_graph (partialY Q) f (deriv f x) x hd1
  have hactual := hPx.add (hPy.mul hd2)
  have he : (fun t => peval (partialX Q) t (f t)+peval (partialY Q) t (f t)*deriv f t)
      =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [hI.mem_nhds hx] with t ht
    exact implicit_first_equation Q f hI hf1 hcurve ht
  have hz := (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq he
  have h := hactual.unique hz
  rw [mixed_partials Q] at h
  linear_combination h

end ErdosImplicitCurvature

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_RegularImplicitArc
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosLatticeChain

theorem short_card_le_square (V : Finset (ℕ × ℕ)) (T : ℕ) :
    (shortVectors V T).card ≤ (T+1)^2 := by
  have h := Fintype.card_le_of_embedding (shortSquareEmbedding V T)
  simpa [pow_two] using h

theorem short_long_card (V : Finset (ℕ × ℕ)) (T : ℕ) :
    (shortVectors V T).card+(longVectors V T).card = V.card := by
  simpa only [shortVectors, longVectors, not_le] using
    Finset.card_filter_add_card_filter_not (s := V) (fun v => vectorLength v ≤ T)

theorem long_card_mul_le_length (V : Finset (ℕ × ℕ)) (T : ℕ) :
    (T+1)*(longVectors V T).card ≤ totalLength V := by
  calc
    _ = ∑ _v ∈ longVectors V T, (T+1) := by simp [mul_comm]
    _ ≤ ∑ v ∈ longVectors V T, vectorLength v := by
      apply Finset.sum_le_sum
      intro v hv
      exact (Finset.mem_filter.mp hv).2
    _ ≤ ∑ v ∈ V, vectorLength v := Finset.sum_le_sum_of_subset
      (Finset.filter_subset _ _)
    _ = _ := rfl

theorem card_le_square_add_div (V : Finset (ℕ × ℕ)) (T : ℕ) {L : ℝ}
    (hL : (totalLength V : ℝ) ≤ L) :
    (V.card : ℝ) ≤ ((T : ℝ)+1)^2+L/((T : ℝ)+1) := by
  have hden : (0 : ℝ) < (T : ℝ)+1 := by positivity
  have hs : ((shortVectors V T).card : ℝ) ≤ ((T : ℝ)+1)^2 := by
    exact_mod_cast short_card_le_square V T
  have hl : ((T : ℝ)+1)*((longVectors V T).card : ℝ) ≤ L := by
    have h : ((T : ℝ)+1)*((longVectors V T).card : ℝ) ≤ (totalLength V : ℝ) := by
      exact_mod_cast long_card_mul_le_length V T
    exact h.trans hL
  have hld : ((longVectors V T).card : ℝ) ≤ L/((T : ℝ)+1) :=
    (le_div_iff₀ hden).mpr (by nlinarith only [hl])
  have he : ((shortVectors V T).card : ℝ)+((longVectors V T).card : ℝ) = (V.card : ℝ) := by
    exact_mod_cast short_long_card V T
  linarith

end ErdosLatticeChain

end

section

open scoped BigOperators
namespace ErdosLatticeChain

theorem consecutive_sum {n : ℕ} (f : Fin (n+1) → ℤ) :
    (∑ i : Fin n, (f i.succ-f i.castSucc)) = f (Fin.last n)-f 0 := by
  have hfirst := Fin.sum_univ_succ f
  have hlast := Fin.sum_univ_castSucc f
  rw [Finset.sum_sub_distrib]
  linarith

theorem variation_of_monotone {n : ℕ} (f : Fin (n+1) → ℤ) (hf : Monotone f) :
    (coordinateVariation f : ℝ) = (f (Fin.last n) : ℝ)-(f 0 : ℝ) := by
  have he : (coordinateVariation f : ℤ) = f (Fin.last n)-f 0 := by
    unfold coordinateVariation
    push_cast
    rw [← consecutive_sum f]
    apply Finset.sum_congr rfl
    intro i _
    exact abs_of_nonneg (sub_nonneg.mpr (hf (by exact_mod_cast Nat.le_succ i.val)))
  exact_mod_cast he

theorem variation_of_antitone {n : ℕ} (f : Fin (n+1) → ℤ) (hf : Antitone f) :
    (coordinateVariation f : ℝ) = (f 0 : ℝ)-(f (Fin.last n) : ℝ) := by
  have he : (coordinateVariation f : ℤ) = f 0-f (Fin.last n) := by
    unfold coordinateVariation
    push_cast
    have h := consecutive_sum f
    have hneg : (∑ i : Fin n, -(f i.succ-f i.castSucc)) = f 0-f (Fin.last n) := by
      rw [Finset.sum_neg_distrib, h]
      ring
    rw [← hneg]
    apply Finset.sum_congr rfl
    intro i _
    exact abs_of_nonpos (sub_nonpos.mpr (hf (by exact_mod_cast Nat.le_succ i.val)))
  exact_mod_cast he

theorem variation_le_box {n : ℕ} (f : Fin (n+1) → ℤ) (S : ℝ)
    (hf : Monotone f ∨ Antitone f) (hbox : ∀ i, 0 ≤ (f i : ℝ) ∧ (f i : ℝ) ≤ S) :
    (coordinateVariation f : ℝ) ≤ S := by
  rcases hf with hf | hf
  · rw [variation_of_monotone f hf]
    linarith [(hbox 0).1, (hbox (Fin.last n)).2]
  · rw [variation_of_antitone f hf]
    linarith [(hbox (Fin.last n)).1, (hbox 0).2]

end ErdosLatticeChain

end


namespace ErdosLatticeChain

theorem vector_card_bound (V : Finset (ℕ × ℕ)) {L : ℝ} (hL : 0 ≤ L)
    (hlength : (totalLength V : ℝ) ≤ L) :
    (V.card : ℝ) ≤ 5*(1+L^((2 : ℝ)/3)) := by
  by_cases hL1 : 1 ≤ L
  · have hLp : 0 < L := by linarith
    let r := L^((1 : ℝ)/3)
    let T := ⌊r⌋₊
    have hr : 1 ≤ r := Real.one_le_rpow hL1 (by norm_num)
    have hrp : 0 < r := by linarith
    have hT : (T : ℝ) ≤ r := Nat.floor_le hrp.le
    have hTr : r ≤ (T : ℝ)+1 := (Nat.lt_floor_add_one r).le
    have hT2 : (T : ℝ)+1 ≤ 2*r := by linarith
    have hsquare : ((T : ℝ)+1)^2 ≤ 4*L^((2 : ℝ)/3) := by
      calc
        _ ≤ (2*r)^2 := by gcongr
        _ = _ := by
          dsimp [r]
          rw [mul_pow, ← Real.rpow_mul_natCast hL]
          norm_num
    have hlong : L/((T : ℝ)+1) ≤ L^((2 : ℝ)/3) := by
      calc
        _ ≤ L/r := div_le_div_of_nonneg_left hL hrp hTr
        _ = _ := by
          dsimp [r]
          rw [show (2 : ℝ)/3 = 1-1/3 by norm_num, Real.rpow_sub hLp, Real.rpow_one]
    have h := card_le_square_add_div V T hlength
    linarith
  · have h := card_le_square_add_div V 0 hlength
    have hp := Real.rpow_nonneg hL ((2 : ℝ)/3)
    norm_num at h
    linarith

end ErdosLatticeChain


section

open scoped BigOperators
namespace ErdosLatticeChain

theorem earlier_lt_later {n : ℕ} (i : Fin (n-1)) : earlierIndex i < laterIndex i :=
  Nat.lt_succ_self i.val

theorem int_eq_of_natAbs_eq_nonneg {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a.natAbs = b.natAbs) : a = b := by
  have hc := congrArg (fun n : ℕ => (n : ℤ)) h
  simpa only [Int.natCast_natAbs, abs_of_nonneg ha, abs_of_nonneg hb] using hc

theorem int_eq_of_natAbs_eq_nonpos {a b : ℤ} (ha : a ≤ 0) (hb : b ≤ 0)
    (h : a.natAbs = b.natAbs) : a = b := by
  have hc := congrArg (fun n : ℕ => (n : ℤ)) h
  have hn : -a = -b := by
    simpa only [Int.natCast_natAbs, abs_of_nonpos ha, abs_of_nonpos hb] using hc
  exact neg_injective hn

theorem natIncrement_injective {n : ℕ} (P : Fin n → ℤ × ℤ)
    (hx : Monotone fun i => (P i).1)
    (hy : (Monotone fun i => (P i).2) ∨ (Antitone fun i => (P i).2))
    (hd : Function.Injective (consecutiveDifference P)) : Function.Injective (natIncrement P) := by
  intro i j h
  apply hd
  apply Prod.ext
  · apply int_eq_of_natAbs_eq_nonneg
      (sub_nonneg.mpr (hx (earlier_lt_later i).le))
      (sub_nonneg.mpr (hx (earlier_lt_later j).le))
    exact congrArg Prod.fst h
  · rcases hy with hy | hy
    · apply int_eq_of_natAbs_eq_nonneg
        (sub_nonneg.mpr (hy (earlier_lt_later i).le))
        (sub_nonneg.mpr (hy (earlier_lt_later j).le))
      exact congrArg Prod.snd h
    · apply int_eq_of_natAbs_eq_nonpos
        (sub_nonpos.mpr (hy (earlier_lt_later i).le))
        (sub_nonpos.mpr (hy (earlier_lt_later j).le))
      exact congrArg Prod.snd h

theorem incrementVectors_card {n : ℕ} (P : Fin n → ℤ × ℤ)
    (hi : Function.Injective (natIncrement P)) : (incrementVectors P).card = n-1 := by
  rw [incrementVectors, Finset.card_image_of_injective _ hi, Finset.card_univ, Fintype.card_fin]

theorem incrementVectors_length {n : ℕ} (P : Fin (n+1) → ℤ × ℤ)
    (hi : Function.Injective (natIncrement P)) :
    totalLength (incrementVectors P) =
      coordinateVariation (fun i => (P i).1)+coordinateVariation (fun i => (P i).2) := by
  unfold totalLength incrementVectors
  rw [Finset.sum_image]
  · change (∑ i : Fin n, (((P i.succ).1-(P i.castSucc).1).natAbs +
        ((P i.succ).2-(P i.castSucc).2).natAbs)) = _
    rw [Finset.sum_add_distrib]
    rfl
  · exact fun i _ j _ h => hi h

end ErdosLatticeChain

end


namespace ErdosImplicitCurvature

theorem peval_inflectionPolynomial (Q : Bivariate) (x y : ℝ) :
    peval (inflectionPolynomial Q) x y =
      peval (partialX (partialX Q)) x y*(peval (partialY Q) x y)^2 -
      2*peval (partialX (partialY Q)) x y*peval (partialX Q) x y*peval (partialY Q) x y +
      peval (partialY (partialY Q)) x y*(peval (partialX Q) x y)^2 := by
  simp [inflectionPolynomial, peval]

theorem curvature_scalar_identity {a b c d e u v : ℝ} (hb : b ≠ 0)
    (h1 : a+b*u = 0) (h2 : c+2*d*u+e*u^2+b*v = 0) :
    u = -a/b ∧ v = -(c*b^2-2*d*a*b+e*a^2)/b^3 := by
  have hu : u = -a/b := (eq_div_iff hb).mpr (by nlinarith only [h1])
  refine ⟨hu, ?_⟩
  apply (eq_div_iff (pow_ne_zero 3 hb)).mpr
  rw [hu] at h2
  field_simp at h2
  linear_combination h2

theorem implicit_derivatives (Q : Bivariate) (f : ℝ → ℝ) {I : Set ℝ}
    (hI : IsOpen I) (hf : ContDiffOn ℝ 2 f I)
    (hcurve : ∀ t ∈ I, peval Q t (f t) = 0) {x : ℝ} (hx : x ∈ I)
    (hQy : peval (partialY Q) x (f x) ≠ 0) :
    deriv f x = -peval (partialX Q) x (f x)/peval (partialY Q) x (f x) ∧
      deriv (deriv f) x = -peval (inflectionPolynomial Q) x (f x)/(peval (partialY Q) x (f x))^3 := by
  rw [peval_inflectionPolynomial]
  exact curvature_scalar_identity hQy
    (implicit_first_equation Q f hI (hf.differentiableOn (by norm_num)) hcurve hx)
    (implicit_second_equation Q f hI hf hcurve hx)

theorem implicit_second_derivative (Q : Bivariate) (f : ℝ → ℝ) {I : Set ℝ}
    (hI : IsOpen I) (hf : ContDiffOn ℝ 2 f I)
    (hcurve : ∀ t ∈ I, peval Q t (f t) = 0) {x : ℝ} (hx : x ∈ I)
    (hQy : peval (partialY Q) x (f x) ≠ 0) :
    deriv (deriv f) x = -peval (inflectionPolynomial Q) x (f x)/(peval (partialY Q) x (f x))^3 :=
  (implicit_derivatives Q f hI hf hcurve hx hQy).2

theorem curvature_zero_iff (Q : Bivariate) (f : ℝ → ℝ) {I : Set ℝ}
    (hI : IsOpen I) (hf : ContDiffOn ℝ 2 f I)
    (hcurve : ∀ t ∈ I, peval Q t (f t) = 0) {x : ℝ} (hx : x ∈ I)
    (hQy : peval (partialY Q) x (f x) ≠ 0) :
    deriv (deriv f) x = 0 ↔ peval (inflectionPolynomial Q) x (f x) = 0 := by
  rw [implicit_second_derivative Q f hI hf hcurve hx hQy]
  simp [div_eq_zero_iff, hQy]

theorem curvature_ne_zero_iff (Q : Bivariate) (f : ℝ → ℝ) {I : Set ℝ}
    (hI : IsOpen I) (hf : ContDiffOn ℝ 2 f I)
    (hcurve : ∀ t ∈ I, peval Q t (f t) = 0) {x : ℝ} (hx : x ∈ I)
    (hQy : peval (partialY Q) x (f x) ≠ 0) :
    deriv (deriv f) x ≠ 0 ↔ peval (inflectionPolynomial Q) x (f x) ≠ 0 :=
  not_congr (curvature_zero_iff Q f hI hf hcurve hx hQy)

end ErdosImplicitCurvature



namespace ErdosLatticeChain

theorem lattice_chain_bound {n : ℕ} (P : Fin n → ℤ × ℤ) (S : ℝ) (hS : 0 ≤ S)
    (hx : StrictMono fun i => (P i).1)
    (hy : (Monotone fun i => (P i).2) ∨ (Antitone fun i => (P i).2))
    (hbox : ∀ i, (0 ≤ ((P i).1 : ℝ) ∧ ((P i).1 : ℝ) ≤ S) ∧
      (0 ≤ ((P i).2 : ℝ) ∧ ((P i).2 : ℝ) ≤ S))
    (hd : Function.Injective (consecutiveDifference P)) :
    (n : ℝ) ≤ 12*(1+S^((2 : ℝ)/3)) := by
  have hp : 0 ≤ S^((2 : ℝ)/3) := Real.rpow_nonneg hS _
  cases n with
  | zero => simp only [Nat.cast_zero] <;> positivity
  | succ n =>
    have hi := natIncrement_injective P hx.monotone hy hd
    have hcard : (incrementVectors P).card = n := by
      simpa using incrementVectors_card P hi
    have hlength : (totalLength (incrementVectors P) : ℝ) ≤ 2*S := by
      rw [incrementVectors_length P hi, Nat.cast_add]
      have h1 := variation_le_box (fun i => (P i).1) S (Or.inl hx.monotone) (fun i => (hbox i).1)
      have h2 := variation_le_box (fun i => (P i).2) S hy (fun i => (hbox i).2)
      linarith
    have hv := vector_card_bound (incrementVectors P) (show 0 ≤ 2*S by positivity) hlength
    rw [hcard] at hv
    have htwo : (2*S)^((2 : ℝ)/3) ≤ 2*S^((2 : ℝ)/3) := by
      rw [Real.mul_rpow (by norm_num) hS]
      apply mul_le_mul_of_nonneg_right _ hp
      have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
        (show (2 : ℝ)/3 ≤ 1 by norm_num)
      simpa only [Real.rpow_one] using h
    simp only [Nat.cast_succ]
    linarith

theorem difference_injective_of_slope {n : ℕ} (P : Fin n → ℤ × ℤ)
    (hs : Function.Injective (consecutiveSlope P)) :
    Function.Injective (consecutiveDifference P) := by
  intro i j h
  apply hs
  exact congrArg (fun v : ℤ × ℤ => (v.2 : ℝ)/(v.1 : ℝ)) h

end ErdosLatticeChain



namespace ErdosConvexGraph

open ErdosLatticeChain

theorem convex_secants_lt {I : Set ℝ} {f : ℝ → ℝ} (hf : StrictConvexOn ℝ I f)
    {a b c d : ℝ} (ha : a ∈ I) (hb : b ∈ I) (hc : c ∈ I) (hd : d ∈ I)
    (hab : a < b) (hbc : b ≤ c) (hcd : c < d) :
    (f b-f a)/(b-a) < (f d-f c)/(d-c) := by
  rcases eq_or_lt_of_le hbc with hbc | hbc
  · subst c
    exact hf.slope_strict_mono_adjacent ha hd hab hcd
  · exact (hf.slope_strict_mono_adjacent ha hc hab hbc).trans
      (hf.slope_strict_mono_adjacent hb hd hbc hcd)

theorem concave_secants_lt {I : Set ℝ} {f : ℝ → ℝ} (hf : StrictConcaveOn ℝ I f)
    {a b c d : ℝ} (ha : a ∈ I) (hb : b ∈ I) (hc : c ∈ I) (hd : d ∈ I)
    (hab : a < b) (hbc : b ≤ c) (hcd : c < d) :
    (f d-f c)/(d-c) < (f b-f a)/(b-a) := by
  rcases eq_or_lt_of_le hbc with hbc | hbc
  · subst c
    exact hf.slope_anti_adjacent ha hd hab hcd
  · exact (hf.slope_anti_adjacent hb hd hbc hcd).trans
      (hf.slope_anti_adjacent ha hc hab hbc)

theorem consecutive_intervals_ordered {n : ℕ} {i j : Fin (n-1)} (hij : i < j) :
    laterIndex i ≤ earlierIndex j := Nat.succ_le_of_lt hij

theorem convex_secantSlopes_strictMono {n : ℕ} {I : Set ℝ} {f : ℝ → ℝ}
    (hf : StrictConvexOn ℝ I f) (x : Fin n → ℝ) (hx : StrictMono x)
    (hdom : ∀ i, x i ∈ I) : StrictMono (secantSlopes f x) := by
  intro i j hij
  exact convex_secants_lt hf (hdom _) (hdom _) (hdom _) (hdom _)
    (hx (earlier_lt_later i)) (hx.monotone (consecutive_intervals_ordered hij))
    (hx (earlier_lt_later j))

theorem concave_secantSlopes_strictAnti {n : ℕ} {I : Set ℝ} {f : ℝ → ℝ}
    (hf : StrictConcaveOn ℝ I f) (x : Fin n → ℝ) (hx : StrictMono x)
    (hdom : ∀ i, x i ∈ I) : StrictAnti (secantSlopes f x) := by
  intro i j hij
  exact concave_secants_lt hf (hdom _) (hdom _) (hdom _) (hdom _)
    (hx (earlier_lt_later i)) (hx.monotone (consecutive_intervals_ordered hij))
    (hx (earlier_lt_later j))

theorem consecutiveSlope_eq_secantSlopes {n : ℕ} (P : Fin n → ℤ × ℤ) (f : ℝ → ℝ)
    (hgraph : ∀ i, ((P i).2 : ℝ) = f ((P i).1 : ℝ)) :
    consecutiveSlope P = secantSlopes f (fun i => ((P i).1 : ℝ)) := by
  funext i
  simp only [consecutiveSlope, consecutiveDifference, secantSlopes, Int.cast_sub, hgraph]

end ErdosConvexGraph



namespace ErdosConvexGraph

open ErdosLatticeChain

theorem graph_chain_y_monotone {n : ℕ} (P : Fin n → ℤ × ℤ) (I : Set ℝ) (f : ℝ → ℝ)
    (hx : Monotone fun i => (P i).1)
    (hf : MonotoneOn f I ∨ AntitoneOn f I) (hgraph : ∀ i, OnGraph I f (P i)) :
    (Monotone fun i => (P i).2) ∨ (Antitone fun i => (P i).2) := by
  rcases hf with hf | hf
  · left
    intro i j hij
    have h := hf (hgraph i).1 (hgraph j).1 (show ((P i).1 : ℝ) ≤ ((P j).1 : ℝ) by
      exact_mod_cast hx hij)
    rw [← (hgraph i).2, ← (hgraph j).2] at h
    exact_mod_cast h
  · right
    intro i j hij
    have h := hf (hgraph i).1 (hgraph j).1 (show ((P i).1 : ℝ) ≤ ((P j).1 : ℝ) by
      exact_mod_cast hx hij)
    rw [← (hgraph i).2, ← (hgraph j).2] at h
    exact_mod_cast h

theorem graph_chain_slopes {n : ℕ} (P : Fin n → ℤ × ℤ) (I : Set ℝ) (f : ℝ → ℝ)
    (hx : StrictMono fun i => (P i).1)
    (hf : StrictConvexOn ℝ I f ∨ StrictConcaveOn ℝ I f)
    (hgraph : ∀ i, OnGraph I f (P i)) :
    StrictMono (consecutiveSlope P) ∨ StrictAnti (consecutiveSlope P) := by
  have hxr : StrictMono fun i => ((P i).1 : ℝ) := by
    intro i j hij
    change ((P i).1 : ℝ) < ((P j).1 : ℝ)
    exact_mod_cast (show (P i).1 < (P j).1 from hx hij)
  rw [consecutiveSlope_eq_secantSlopes P f (fun i => (hgraph i).2)]
  rcases hf with hf | hf
  · exact Or.inl (convex_secantSlopes_strictMono hf _ hxr (fun i => (hgraph i).1))
  · exact Or.inr (concave_secantSlopes_strictAnti hf _ hxr (fun i => (hgraph i).1))

theorem graph_chain_bound {n : ℕ} (P : Fin n → ℤ × ℤ) (I : Set ℝ) (f : ℝ → ℝ)
    (S : ℝ) (hS : 0 ≤ S) (hx : StrictMono fun i => (P i).1)
    (hcurve : StrictConvexOn ℝ I f ∨ StrictConcaveOn ℝ I f)
    (hmono : MonotoneOn f I ∨ AntitoneOn f I)
    (hgraph : ∀ i, OnGraph I f (P i)) (hbox : ∀ i, InSquare S (P i)) :
    (n : ℝ) ≤ 12*(1+S^((2 : ℝ)/3)) := by
  apply lattice_chain_bound P S hS hx (graph_chain_y_monotone P I f hx.monotone hmono hgraph) hbox
  apply difference_injective_of_slope P
  rcases graph_chain_slopes P I f hx hcurve hgraph with hs | hs
  · exact hs.injective
  · exact hs.injective

end ErdosConvexGraph



namespace ErdosConvexGraph

theorem onGraph_fst_injective {I : Set ℝ} {f : ℝ → ℝ} {p q : ℤ × ℤ}
    (hp : OnGraph I f p) (hq : OnGraph I f q) (h : p.1 = q.1) : p = q := by
  apply Prod.ext h
  have he : (p.2 : ℝ) = (q.2 : ℝ) := by rw [hp.2, hq.2, h]
  exact_mod_cast he

theorem graphAbscissae_card (G : Finset (ℤ × ℤ)) (I : Set ℝ) (f : ℝ → ℝ)
    (hG : ∀ p ∈ G, OnGraph I f p) : (graphAbscissae G).card = G.card := by
  apply Finset.card_image_of_injOn
  intro p hp q hq h
  exact onGraph_fst_injective (hG p hp) (hG q hq) h

theorem graphEnumeration_mem (G : Finset (ℤ × ℤ)) (I : Set ℝ) (f : ℝ → ℝ)
    (hG : ∀ p ∈ G, OnGraph I f p) (i : Fin (graphAbscissae G).card) :
    graphEnumeration G f i ∈ G := by
  have hm := (graphAbscissae G).orderEmbOfFin_mem rfl i
  obtain ⟨p, hp, he⟩ := Finset.mem_image.mp hm
  have hpoint : graphEnumeration G f i = p := by
    apply Prod.ext
    · exact he.symm
    · change ⌊f (((graphAbscissae G).orderEmbOfFin rfl i : ℤ) : ℝ)⌋ = p.2
      rw [← he, ← (hG p hp).2]
      exact Int.floor_intCast _
  rw [hpoint]
  exact hp

theorem graphEnumeration_strictMono (G : Finset (ℤ × ℤ)) (f : ℝ → ℝ) :
    StrictMono fun i => (graphEnumeration G f i).1 :=
  ((graphAbscissae G).orderEmbOfFin rfl).strictMono

theorem finite_graph_set_bound (G : Finset (ℤ × ℤ)) (I : Set ℝ) (f : ℝ → ℝ)
    (S : ℝ) (hS : 0 ≤ S)
    (hcurve : StrictConvexOn ℝ I f ∨ StrictConcaveOn ℝ I f)
    (hmono : MonotoneOn f I ∨ AntitoneOn f I)
    (hgraph : ∀ p ∈ G, OnGraph I f p) (hbox : ∀ p ∈ G, InSquare S p) :
    (G.card : ℝ) ≤ 12*(1+S^((2 : ℝ)/3)) := by
  have h := graph_chain_bound (graphEnumeration G f) I f S hS
    (graphEnumeration_strictMono G f) hcurve hmono
    (fun i => hgraph _ (graphEnumeration_mem G I f hgraph i))
    (fun i => hbox _ (graphEnumeration_mem G I f hgraph i))
  rwa [graphAbscissae_card G I f hgraph] at h





attribute [local instance] Classical.propDecidable

theorem mem_graphLatticePoints (I : Set ℝ) (f : ℝ → ℝ) (S : ℝ) (p : ℤ × ℤ) :
    p ∈ graphLatticePoints I f S ↔ InSquare S p ∧ OnGraph I f p := by
  simp only [graphLatticePoints, InSquare, Finset.mem_filter, Finset.product_eq_sprod,
    Finset.mem_product, Finset.mem_Icc, Int.le_floor, Int.cast_nonneg_iff]

theorem graph_arc_lattice_bound (I : Set ℝ) (f : ℝ → ℝ) (S : ℝ) (hS : 0 ≤ S)
    (hcurve : StrictConvexOn ℝ I f ∨ StrictConcaveOn ℝ I f)
    (hmono : MonotoneOn f I ∨ AntitoneOn f I) :
    ((graphLatticePoints I f S).card : ℝ) ≤ 12*(1+S^((2 : ℝ)/3)) :=
  finite_graph_set_bound _ I f S hS hcurve hmono
    (fun p hp => ((mem_graphLatticePoints I f S p).mp hp).2)
    (fun p hp => ((mem_graphLatticePoints I f S p).mp hp).1)

theorem open_graph_arc_bound (a b : ℝ) (f : ℝ → ℝ) (S : ℝ) (hS : 0 ≤ S)
    (hcurve : StrictConvexOn ℝ (Set.Ioo a b) f ∨ StrictConcaveOn ℝ (Set.Ioo a b) f)
    (hmono : MonotoneOn f (Set.Ioo a b) ∨ AntitoneOn f (Set.Ioo a b)) :
    ((graphLatticePoints (Set.Ioo a b) f S).card : ℝ) ≤ 12*(1+S^((2 : ℝ)/3)) :=
  graph_arc_lattice_bound _ f S hS hcurve hmono

end ErdosConvexGraph



namespace ErdosImplicitCurvature





theorem continuous_nonzero_fixed_sign {I : Set ℝ} {g : ℝ → ℝ}
    (hI : IsPreconnected I) (hg : ContinuousOn g I) (hne : ∀ x ∈ I, g x ≠ 0) :
    (∀ x ∈ I, 0 < g x) ∨ (∀ x ∈ I, g x < 0) := by
  by_cases hp : ∀ x ∈ I, 0 < g x
  · exact Or.inl hp
  · right
    push Not at hp
    obtain ⟨a, ha, hga⟩ := hp
    have hneg : g a < 0 := by
      rcases lt_or_eq_of_le hga with h | h
      · exact h
      · exact (hne a ha h).elim
    intro y hy
    by_contra! hgy
    have hz : 0 ∈ g '' I := hI.intermediate_value ha hy hg ⟨hneg.le, hgy⟩
    obtain ⟨z, hz, he⟩ := hz
    exact hne z hz he

theorem regular_implicit_monotone (Q : Bivariate) (f : ℝ → ℝ) (a b : ℝ)
    (hf : ContDiffOn ℝ 2 f (Set.Ioo a b))
    (hcurve : ∀ x ∈ Set.Ioo a b, peval Q x (f x) = 0)
    (hQx : ∀ x ∈ Set.Ioo a b, peval (partialX Q) x (f x) ≠ 0)
    (hQy : ∀ x ∈ Set.Ioo a b, peval (partialY Q) x (f x) ≠ 0) :
    MonotoneOn f (Set.Ioo a b) ∨ AntitoneOn f (Set.Ioo a b) := by
  have hd : DifferentiableOn ℝ f (Set.Ioo a b) := hf.differentiableOn (by norm_num)
  have hc : ContDiffOn ℝ 1 (deriv f) (Set.Ioo a b) := hf.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hne : ∀ x ∈ Set.Ioo a b, deriv f x ≠ 0 := by
    intro x hx
    rw [implicit_first_derivative Q f isOpen_Ioo hd hcurve hx (hQy x hx)]
    exact div_ne_zero (neg_ne_zero.mpr (hQx x hx)) (hQy x hx)
  rcases continuous_nonzero_fixed_sign isPreconnected_Ioo hc.continuousOn hne with hp | hn
  · left
    exact monotoneOn_of_deriv_nonneg (convex_Ioo a b) hf.continuousOn
      (hd.mono interior_subset) (fun x hx => (hp x (interior_subset hx)).le)
  · right
    exact antitoneOn_of_deriv_nonpos (convex_Ioo a b) hf.continuousOn
      (hd.mono interior_subset) (fun x hx => (hn x (interior_subset hx)).le)

theorem regular_implicit_convex_or_concave (Q : Bivariate) (f : ℝ → ℝ) (a b : ℝ)
    (hf : ContDiffOn ℝ 2 f (Set.Ioo a b))
    (hcurve : ∀ x ∈ Set.Ioo a b, peval Q x (f x) = 0)
    (hQy : ∀ x ∈ Set.Ioo a b, peval (partialY Q) x (f x) ≠ 0)
    (hInf : ∀ x ∈ Set.Ioo a b, peval (inflectionPolynomial Q) x (f x) ≠ 0) :
    StrictConvexOn ℝ (Set.Ioo a b) f ∨ StrictConcaveOn ℝ (Set.Ioo a b) f := by
  have hc1 : ContDiffOn ℝ 1 (deriv f) (Set.Ioo a b) := hf.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hc2 : ContDiffOn ℝ 0 (deriv (deriv f)) (Set.Ioo a b) :=
    hc1.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hne : ∀ x ∈ Set.Ioo a b, deriv (deriv f) x ≠ 0 := by
    intro x hx
    exact (curvature_ne_zero_iff Q f isOpen_Ioo hf hcurve hx (hQy x hx)).mpr (hInf x hx)
  rcases continuous_nonzero_fixed_sign isPreconnected_Ioo hc2.continuousOn hne with hp | hn
  · left
    apply strictConvexOn_of_deriv2_pos (convex_Ioo a b) hf.continuousOn
    intro x hx
    exact hp x (interior_subset hx)
  · right
    apply strictConcaveOn_of_deriv2_neg (convex_Ioo a b) hf.continuousOn
    intro x hx
    exact hn x (interior_subset hx)

theorem regular_implicit_arc_lattice_bound (Q : Bivariate) (f : ℝ → ℝ) (a b S : ℝ)
    (hS : 0 ≤ S) (hf : ContDiffOn ℝ 2 f (Set.Ioo a b))
    (hcurve : ∀ x ∈ Set.Ioo a b, peval Q x (f x) = 0)
    (hQx : ∀ x ∈ Set.Ioo a b, peval (partialX Q) x (f x) ≠ 0)
    (hQy : ∀ x ∈ Set.Ioo a b, peval (partialY Q) x (f x) ≠ 0)
    (hInf : ∀ x ∈ Set.Ioo a b, peval (inflectionPolynomial Q) x (f x) ≠ 0) :
    ((ErdosConvexGraph.graphLatticePoints (Set.Ioo a b) f S).card : ℝ) ≤
      12*(1+S^((2 : ℝ)/3)) :=
  ErdosConvexGraph.open_graph_arc_bound a b f S hS
    (regular_implicit_convex_or_concave Q f a b hf hcurve hQy hInf)
    (regular_implicit_monotone Q f a b hf hcurve hQx hQy)

end ErdosImplicitCurvature


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_NestedCoordinates
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.Erdos970.ErdosCriticalGeometry.beval_nested
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosCriticalGeometry

variable (R : Type*) [CommSemiring R]

theorem eval_nestedX (Q : MV R) (x y : R) :
    nestedEvalHom R y x (nestedX R Q) = MvPolynomial.eval ![x,y] Q := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp [nestedEvalHom]
  | add P Q hP hQ => simp [map_add, hP, hQ]
  | mul_X P i hP =>
      fin_cases i
      · simp [map_mul, hP]
      · simp [map_mul, hP]

end ErdosCriticalGeometry

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_PolynomialLocalGraph
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Filter
open scoped Topology ContDiff
namespace ErdosDivisibleInflection
open ErdosImplicitCurvature

theorem exists_local_real_graph (Q : Bivariate) (x y : ℝ)
    (hQ : peval Q x y = 0) (hQy : peval (partialY Q) x y ≠ 0) :
    ∃ (a b : ℝ) (f : ℝ → ℝ), a < x ∧ x < b ∧ f x = y ∧
      ContDiffOn ℝ 2 f (Set.Ioo a b) ∧
      (∀ t ∈ Set.Ioo a b, peval Q t (f t) = 0) ∧
      (∀ t ∈ Set.Ioo a b, peval (partialY Q) t (f t) ≠ 0) := by
  have hc : ContDiffAt ℝ 2 (planeEval Q) (x,y) := (contDiff_planeEval Q 2).contDiffAt
  have hi : (fderiv ℝ (planeEval Q) (x,y) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    rw [fderiv_planeEval_inr]
    exact scalar_map_invertible _ hQy
  let f := hc.implicitFunction (by norm_num) hi
  have hfx : f x = y := hc.implicitFunction_apply_self (by norm_num) hi
  have hcf : ContDiffAt ℝ 2 f x := hc.contDiffAt_implicitFunction (by norm_num) hi
  have hcurve : ∀ᶠ t in 𝓝 x, peval Q t (f t) = 0 := by
    have h := hc.eventually_apply_implicitFunction (by norm_num) hi
    exact h.mono fun t ht => ht.trans hQ
  have hpair : ContinuousAt (fun t : ℝ => (t,f t)) x :=
    continuousAt_id.prodMk hcf.continuousAt
  have hplane : ContinuousAt (planeEval (partialY Q)) (x,f x) :=
    (contDiff_planeEval (partialY Q) 0).continuous.continuousAt
  have hcy : ContinuousAt (fun t => peval (partialY Q) t (f t)) x := by
    change ContinuousAt (planeEval (partialY Q) ∘ (fun t : ℝ => (t,f t))) x
    exact ContinuousAt.comp (f := fun t : ℝ => (t,f t)) hplane hpair
  have hny : ∀ᶠ t in 𝓝 x, peval (partialY Q) t (f t) ≠ 0 := by
    apply hcy.eventually_ne
    rwa [hfx]
  obtain ⟨U,hU,hfU⟩ := hcf.contDiffOn (m := 2) le_rfl (by norm_num)
  have hN : U ∩ {t | peval Q t (f t) = 0} ∩ {t | peval (partialY Q) t (f t) ≠ 0} ∈ 𝓝 x :=
    inter_mem (inter_mem hU hcurve) hny
  obtain ⟨eps,heps,hball⟩ := Metric.mem_nhds_iff.mp hN
  have hsub : Set.Ioo (x-eps) (x+eps) ⊆
      U ∩ {t | peval Q t (f t) = 0} ∩ {t | peval (partialY Q) t (f t) ≠ 0} := by
    simpa only [Real.ball_eq_Ioo] using hball
  refine ⟨x-eps,x+eps,f,by linarith,by linarith,hfx,hfU.mono ?_,?_,?_⟩
  · exact fun t ht => (hsub ht).1.1
  · exact fun t ht => (hsub ht).1.2
  · exact fun t ht => (hsub ht).2

end ErdosDivisibleInflection

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_PrimitiveResultant
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.Erdos970.ErdosCriticalGeometry.beval_nested
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosBivariateResultant

theorem beval_eq_specialize (P : Bivariate) (x y : ℂ) :
    beval P x y = (specialize P x).eval y := rfl

theorem resultant_bezout (P Q : Bivariate) (hdeg : P.natDegree ≠ 0 ∨ Q.natDegree ≠ 0) :
    ∃ U V : Bivariate, P*U+Q*V = Polynomial.C (xResultant P Q) := by
  obtain ⟨U,V,_,_,h⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant P Q le_rfl le_rfl hdeg
  exact ⟨U,V,h⟩

theorem common_zero_resultant_zero (P Q : Bivariate)
    (hdeg : P.natDegree ≠ 0 ∨ Q.natDegree ≠ 0) (x y : ℂ)
    (hP : beval P x y = 0) (hQ : beval Q x y = 0) :
    (xResultant P Q).eval x = 0 := by
  obtain ⟨U,V,h⟩ := resultant_bezout P Q hdeg
  have he := congrArg (fun R : Bivariate => beval R x y) h
  simpa only [beval_add, beval_mul, beval_C, hP, hQ, zero_mul, zero_add] using he.symm

theorem specialize_degree_le (P : Bivariate) (x : ℂ) :
    (specialize P x).natDegree ≤ P.natDegree := Polynomial.natDegree_map_le

theorem common_zero_resultant_zero_of_fiber (P Q : Bivariate) (x y : ℂ)
    (hPx : specialize P x ≠ 0) (hP : beval P x y = 0) (hQ : beval Q x y = 0) :
    (xResultant P Q).eval x = 0 := by
  have hd : 0 < (specialize P x).natDegree :=
    Polynomial.natDegree_pos_of_eval₂_root hPx (RingHom.id ℂ) hP (fun z hz => hz)
  have hdeg : 0 < P.natDegree := hd.trans_le (specialize_degree_le P x)
  exact common_zero_resultant_zero P Q (Or.inl hdeg.ne') x y hP hQ

end ErdosBivariateResultant

end

section

open scoped BigOperators
namespace ErdosBivariateResultant

theorem determinant_degree_le {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n (Polynomial ℂ)) (D : n → ℕ)
    (hM : ∀ i j, (M i j).natDegree ≤ D j) : M.det.natDegree ≤ ∑ j, D j := by
  classical
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro sigma _
  apply (Polynomial.natDegree_smul_le (Equiv.Perm.sign sigma) _).trans
  apply (Polynomial.natDegree_prod_le _ _).trans
  exact Finset.sum_le_sum fun j _ => hM (sigma j) j

theorem resultant_degree_from_coefficients (P Q : Bivariate) (m n A B : ℕ)
    (hP : ∀ k, (P.coeff k).natDegree ≤ A) (hQ : ∀ k, (Q.coeff k).natDegree ≤ B) :
    (P.resultant Q m n).natDegree ≤ m*B+n*A := by
  let D : Fin (m+n) → ℕ := Fin.addCases (fun _ : Fin m => B) (fun _ : Fin n => A)
  have hcol (i j : Fin (m+n)) : (P.sylvester Q m n i j).natDegree ≤ D j := by
    induction j using Fin.addCases with
    | left j =>
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left, D]
        split_ifs
        · exact hQ _
        · simp
    | right j =>
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right, D]
        split_ifs
        · exact hP _
        · simp
  have h := determinant_degree_le (P.sylvester Q m n) D hcol
  change (P.resultant Q m n).natDegree ≤ _ at h
  have hsum : (∑ j, D j) = m*B+n*A := by
    rw [Fin.sum_univ_add]
    simp [D]
  rwa [hsum] at h

end ErdosBivariateResultant

end

section

open scoped BigOperators
namespace ErdosBivariateResultant

attribute [local instance] Classical.propDecidable

theorem mem_resultantRoots (P Q : Bivariate) (hR : xResultant P Q ≠ 0) (x : ℂ) :
    x ∈ resultantRoots P Q ↔ (xResultant P Q).eval x = 0 := by
  simp only [resultantRoots, Multiset.mem_toFinset, Polynomial.mem_roots hR, Polynomial.IsRoot.def]

theorem mem_verticalRoots (P : Bivariate) (x y : ℂ) (hPx : specialize P x ≠ 0) :
    y ∈ verticalRoots P x ↔ beval P x y = 0 := by
  simp only [verticalRoots, Multiset.mem_toFinset, Polynomial.mem_roots hPx,
    Polynomial.IsRoot.def, beval_eq_specialize]

theorem mem_rootPairs (P Q : Bivariate) (p : ℂ × ℂ) :
    p ∈ rootPairs P Q ↔ p.1 ∈ resultantRoots P Q ∧ p.2 ∈ verticalRoots P p.1 := by
  rcases p with ⟨a,b⟩
  simp only [rootPairs, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨x,hx,y,hy,hp⟩
    cases hp
    exact ⟨hx,hy⟩
  · intro h
    exact ⟨a,h.1,b,h.2,rfl⟩

theorem mem_commonZeroFinset (P Q : Bivariate) (hR : xResultant P Q ≠ 0)
    (hP : ∀ x : ℂ, specialize P x ≠ 0) (p : ℂ × ℂ) :
    p ∈ commonZeroFinset P Q ↔ p ∈ commonZeroSet P Q := by
  simp only [commonZeroFinset, Finset.mem_filter, mem_rootPairs, commonZeroSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨_,hy⟩,hQ⟩
    exact ⟨(mem_verticalRoots P p.1 p.2 (hP p.1)).mp hy,hQ⟩
  · rintro ⟨hp,hq⟩
    refine ⟨⟨(mem_resultantRoots P Q hR p.1).mpr ?_,
      (mem_verticalRoots P p.1 p.2 (hP p.1)).mpr hp⟩,hq⟩
    exact common_zero_resultant_zero_of_fiber P Q p.1 p.2 (hP p.1) hp hq

theorem coe_commonZeroFinset (P Q : Bivariate) (hR : xResultant P Q ≠ 0)
    (hP : ∀ x : ℂ, specialize P x ≠ 0) :
    (commonZeroFinset P Q : Set (ℂ × ℂ)) = commonZeroSet P Q := by
  ext p
  exact mem_commonZeroFinset P Q hR hP p

theorem commonZeroSet_finite (P Q : Bivariate) (hR : xResultant P Q ≠ 0)
    (hP : ∀ x : ℂ, specialize P x ≠ 0) : (commonZeroSet P Q).Finite := by
  rw [← coe_commonZeroFinset P Q hR hP]
  exact Finset.finite_toSet _

theorem resultantRoots_card_le (P Q : Bivariate) :
    (resultantRoots P Q).card ≤ (xResultant P Q).natDegree :=
  (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' _)

theorem verticalRoots_card_le (P : Bivariate) (x : ℂ) : (verticalRoots P x).card ≤ P.natDegree :=
  (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans (specialize_degree_le P x))

theorem commonZeroFinset_card_le (P Q : Bivariate) :
    (commonZeroFinset P Q).card ≤ (xResultant P Q).natDegree*P.natDegree := by
  calc
    _ ≤ (rootPairs P Q).card := Finset.card_filter_le _ _
    _ ≤ ∑ x ∈ resultantRoots P Q, ((verticalRoots P x).image fun y => (x,y)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ resultantRoots P Q, P.natDegree := by
      apply Finset.sum_le_sum
      intro x _
      exact Finset.card_image_le.trans (verticalRoots_card_le P x)
    _ = (resultantRoots P Q).card*P.natDegree := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (resultantRoots_card_le P Q)

theorem common_zero_finite_count (P Q : Bivariate) (hR : xResultant P Q ≠ 0)
    (hP : ∀ x : ℂ, specialize P x ≠ 0) :
    (commonZeroSet P Q).Finite ∧
      (commonZeroSet P Q).ncard ≤ (xResultant P Q).natDegree*P.natDegree := by
  refine ⟨commonZeroSet_finite P Q hR hP, ?_⟩
  rw [← coe_commonZeroFinset P Q hR hP, Set.ncard_coe_finset]
  exact commonZeroFinset_card_le P Q

end ErdosBivariateResultant

end

section

namespace ErdosCriticalGeometry

open ErdosBivariateResultant

theorem primitive_specialize_ne_zero (P : Nested ℂ) (hP : P.IsPrimitive) (x : ℂ) :
    specialize P x ≠ 0 := by
  intro hz
  have hcoeff (k : ℕ) : (P.coeff k).eval x = 0 := by
    have h := congrArg (fun p : Polynomial ℂ => p.coeff k) hz
    change (Polynomial.evalRingHom x) (P.coeff k) = 0
    simpa only [specialize, Polynomial.coeff_map, Polynomial.coeff_zero] using h
  have hdiv : Polynomial.C (Polynomial.X-Polynomial.C x) ∣ P := by
    apply (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr
    intro k
    exact Polynomial.dvd_iff_isRoot.mpr (hcoeff k)
  exact Polynomial.not_isUnit_X_sub_C x
    ((Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mp hP) _ hdiv)


theorem irreducible_resultant_ne_zero (P G : Nested ℂ) (hP : Irreducible P)
    (hdeg : P.natDegree ≠ 0) (hnd : ¬P ∣ G) : xResultant P G ≠ 0 := by
  classical
  let K := FractionRing (Polynomial ℂ)
  let : IsPrincipalIdealRing (Polynomial K) := by
    let := Polynomial.instEuclideanDomain (R := K)
    exact EuclideanDomain.to_principal_ideal_domain
  let phi : Polynomial ℂ →+* K := algebraMap (Polynomial ℂ) K
  have hphi : Function.Injective phi := IsFractionRing.injective (Polynomial ℂ) K
  have hprim := hP.isPrimitive hdeg
  have hirr : Irreducible (P.map phi) :=
    (hprim.irreducible_iff_irreducible_map_fraction_map (K := K)).mp hP
  have hnd' : ¬P.map phi ∣ G.map phi := by
    intro h
    exact hnd (hprim.dvd_of_fraction_map_dvd_fraction_map (K := K) h)
  have hcop : IsCoprime (P.map phi) (G.map phi) :=
    hirr.coprime_iff_not_dvd.mpr hnd'
  have hres := Polynomial.resultant_ne_zero (P.map phi) (G.map phi) hcop
  intro hz
  apply hres
  rw [Polynomial.natDegree_map_eq_of_injective hphi, Polynomial.natDegree_map_eq_of_injective hphi,
    Polynomial.resultant_map_map]
  simpa only [xResultant, map_zero] using congrArg phi hz

end ErdosCriticalGeometry

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_NestedDegreeBounds
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.Erdos970.ErdosCriticalGeometry.beval_nested
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosCriticalGeometry

variable (R : Type*) [CommSemiring R]

theorem unique_degree_le_totalDegree (P : MvPolynomial (Fin 1) R) :
    (MvPolynomial.uniqueAlgEquiv R (Fin 1) P).natDegree ≤ P.totalDegree := by
  classical
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [MvPolynomial.coeff_uniqueAlgEquiv]
  by_contra hc
  have h := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hc)
  simp only [Finsupp.sum_single_index] at h
  exact (not_le_of_gt hk) h

theorem nestedX_degree_le (Q : MV R) : (nestedX R Q).natDegree ≤ Q.totalDegree := by
  change (Polynomial.map (MvPolynomial.uniqueAlgEquiv R (Fin 1)).toRingHom
    (MvPolynomial.finSuccEquiv R 1 Q)).natDegree ≤ _
  exact Polynomial.natDegree_map_le.trans
    ((MvPolynomial.natDegree_finSuccEquiv Q).le.trans (MvPolynomial.degreeOf_le_totalDegree Q 0))

theorem nestedX_coefficient_degree_le (Q : MV R) (k : ℕ) :
    ((nestedX R Q).coeff k).natDegree ≤ Q.totalDegree := by
  change ((Polynomial.map (MvPolynomial.uniqueAlgEquiv R (Fin 1)).toRingHom
    (MvPolynomial.finSuccEquiv R 1 Q)).coeff k).natDegree ≤ _
  rw [Polynomial.coeff_map]
  apply (unique_degree_le_totalDegree R _).trans
  by_cases h : (MvPolynomial.finSuccEquiv R 1 Q).coeff k = 0
  · simp [h]
  · have hb := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le Q k h
    omega

theorem nestedY_degree_le (Q : MV R) : (nestedY R Q).natDegree ≤ Q.totalDegree := by
  have h := nestedX_degree_le R (MvPolynomial.renameEquiv R (Equiv.swap (0 : Fin 2) 1) Q)
  simpa only [MvPolynomial.totalDegree_renameEquiv, nestedY, AlgEquiv.trans_apply] using h

theorem nestedY_coefficient_degree_le (Q : MV R) (k : ℕ) :
    ((nestedY R Q).coeff k).natDegree ≤ Q.totalDegree := by
  have h := nestedX_coefficient_degree_le R (MvPolynomial.renameEquiv R (Equiv.swap (0 : Fin 2) 1) Q) k
  simpa only [MvPolynomial.totalDegree_renameEquiv, nestedY, AlgEquiv.trans_apply] using h

theorem partial_totalDegree_le (Q : MV R) (i : Fin 2) :
    (MvPolynomial.pderiv i Q).totalDegree ≤ Q.totalDegree-1 := by
  classical
  apply Finset.sup_le
  intro m hm
  have hc := MvPolynomial.mem_support_iff.mp hm
  rw [MvPolynomial.coeff_pderiv] at hc
  have hQ := MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hc)
  have hd := MvPolynomial.le_totalDegree hQ
  rw [Finsupp.sum_add_index] at hd
  · simp only [Finsupp.sum_single_index] at hd
    omega
  · simp
  · intros
    rfl

end ErdosCriticalGeometry

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_NestedPartials
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.Erdos970.ErdosCriticalGeometry.beval_nested
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosCriticalGeometry

variable (R : Type*) [CommSemiring R]

theorem nestedX_partial_zero (Q : MV R) :
    nestedX R (MvPolynomial.pderiv 0 Q) = (nestedX R Q).derivative := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp [map_add, hP, hQ]
  | mul_X P i hP =>
      fin_cases i
      · simp [hP, Polynomial.derivative_mul]
        ring
      · simp [hP, Polynomial.derivative_mul]
        ring

theorem nestedY_partial_one (Q : MV R) :
    nestedY R (MvPolynomial.pderiv 1 Q) = (nestedY R Q).derivative := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp [map_add, hP, hQ]
  | mul_X P i hP =>
      fin_cases i
      · simp [hP, Polynomial.derivative_mul]
        ring
      · simp [hP, Polynomial.derivative_mul]
        ring

end ErdosCriticalGeometry

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_NonlinearCoordinateDegree
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.Erdos970.ErdosCriticalGeometry.beval_nested
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosCriticalGeometry

theorem irreducible_of_constant_polynomial (p : Polynomial ℂ)
    (hp : Irreducible (Polynomial.C p : Nested ℂ)) : Irreducible p := by
  refine ⟨fun h => hp.not_isUnit (Polynomial.isUnit_C.mpr h), ?_⟩
  intro a b hab
  have h := hp.2 (show Polynomial.C p = Polynomial.C a*Polynomial.C b by rw [hab, map_mul])
  exact h.imp Polynomial.isUnit_C.mp Polynomial.isUnit_C.mp

theorem nonlinear_outer_degree_pos (E : MV ℂ ≃ₐ[ℂ] Nested ℂ) (i : Fin 2)
    (hXi : E (MvPolynomial.X i) = Polynomial.C Polynomial.X)
    (Q : MV ℂ) (hQ : Irreducible Q) (hdeg : 1 < Q.totalDegree) : 0 < (E Q).natDegree := by
  have hC (c : ℂ) : E (MvPolynomial.C c) = Polynomial.C (Polynomial.C c) := by
    simpa using E.commutes c
  have hEQ : Irreducible (E Q) := (MulEquiv.irreducible_iff E.toMulEquiv).mpr hQ
  by_contra! hzero
  have he : E Q = Polynomial.C ((E Q).coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hzero
  have hc : Irreducible ((E Q).coeff 0) := irreducible_of_constant_polynomial _ (he ▸ hEQ)
  have hlin := Polynomial.eq_X_add_C_of_degree_le_one
    (IsAlgClosed.degree_eq_one_of_irreducible ℂ hc).le
  let a : ℂ := ((E Q).coeff 0).coeff 1
  let b : ℂ := ((E Q).coeff 0).coeff 0
  have hQlin : Q = MvPolynomial.C a*MvPolynomial.X i+MvPolynomial.C b := by
    apply E.injective
    rw [map_add, map_mul, hC, hC, hXi, he, hlin]
    simp only [map_add, map_mul, a, b]
  have ht : Q.totalDegree ≤ 1 := by
    rw [hQlin]
    apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
    · simp
  omega

theorem nonlinear_nestedX_degree_pos (Q : MV ℂ) (hQ : Irreducible Q) (hdeg : 1 < Q.totalDegree) :
    0 < (nestedX ℂ Q).natDegree :=
  nonlinear_outer_degree_pos (nestedX ℂ) 1 (nestedX_X_one ℂ) Q hQ hdeg

theorem nonlinear_nestedY_degree_pos (Q : MV ℂ) (hQ : Irreducible Q) (hdeg : 1 < Q.totalDegree) :
    0 < (nestedY ℂ Q).natDegree :=
  nonlinear_outer_degree_pos (nestedY ℂ) 0 (nestedY_X_zero ℂ) Q hQ hdeg

theorem nonlinear_partial_zero_ne (Q : MV ℂ) (hQ : Irreducible Q) (hdeg : 1 < Q.totalDegree) :
    MvPolynomial.pderiv 0 Q ≠ 0 := by
  intro hz
  have hd := congrArg (nestedX ℂ) hz
  rw [nestedX_partial_zero, map_zero] at hd
  exact (nonlinear_nestedX_degree_pos Q hQ hdeg).ne' (Polynomial.derivative_eq_zero.mp hd)

theorem nonlinear_partial_one_ne (Q : MV ℂ) (hQ : Irreducible Q) (hdeg : 1 < Q.totalDegree) :
    MvPolynomial.pderiv 1 Q ≠ 0 := by
  intro hz
  have hd := congrArg (nestedY ℂ) hz
  rw [nestedY_partial_one, map_zero] at hd
  exact (nonlinear_nestedY_degree_pos Q hQ hdeg).ne' (Polynomial.derivative_eq_zero.mp hd)

theorem nonlinear_partial_not_dvd (Q : MV ℂ) (hQ : Irreducible Q) (hdeg : 1 < Q.totalDegree)
    (i : Fin 2) : ¬ Q ∣ MvPolynomial.pderiv i Q := by
  have hn : MvPolynomial.pderiv i Q ≠ 0 := by
    fin_cases i
    · exact nonlinear_partial_zero_ne Q hQ hdeg
    · exact nonlinear_partial_one_ne Q hQ hdeg
  intro hd
  have h1 := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hd hn
  have h2 := partial_totalDegree_le ℂ Q i
  omega

end ErdosCriticalGeometry

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_RealCriticalPoints
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosCriticalGeometry

open ErdosBivariateResultant

theorem intersectionPoints_eq_nested (Q G : MV ℂ) :
    intersectionPoints Q G = commonZeroSet (nestedY ℂ Q) (nestedY ℂ G) := by
  ext p
  simp only [intersectionPoints, commonZeroSet, Set.mem_ofPred_eq, beval_nested]

theorem nonlinear_fibers_nonzero (Q : MV ℂ) (hQ : Irreducible Q) (hdeg : 1 < Q.totalDegree) :
    ∀ x : ℂ, specialize (nestedY ℂ Q) x ≠ 0 := by
  have hi : Irreducible (nestedY ℂ Q) := (MulEquiv.irreducible_iff (nestedY ℂ).toMulEquiv).mpr hQ
  exact primitive_specialize_ne_zero _ (hi.isPrimitive (nonlinear_nestedY_degree_pos Q hQ hdeg).ne')

theorem nonlinear_resultant_nonzero (Q G : MV ℂ) (hQ : Irreducible Q)
    (hdeg : 1 < Q.totalDegree) (hnd : ¬Q ∣ G) : xResultant (nestedY ℂ Q) (nestedY ℂ G) ≠ 0 := by
  have hi : Irreducible (nestedY ℂ Q) := (MulEquiv.irreducible_iff (nestedY ℂ).toMulEquiv).mpr hQ
  apply irreducible_resultant_ne_zero _ _ hi (nonlinear_nestedY_degree_pos Q hQ hdeg).ne'
  rintro ⟨H,hH⟩
  apply hnd
  refine ⟨(nestedY ℂ).symm H, ?_⟩
  apply (nestedY ℂ).injective
  simpa only [map_mul, AlgEquiv.apply_symm_apply] using hH

theorem mv_resultant_degree_le (Q G : MV ℂ) :
    (xResultant (nestedY ℂ Q) (nestedY ℂ G)).natDegree ≤ 2*Q.totalDegree*G.totalDegree := by
  have h := resultant_degree_from_coefficients (nestedY ℂ Q) (nestedY ℂ G)
    (nestedY ℂ Q).natDegree (nestedY ℂ G).natDegree Q.totalDegree G.totalDegree
    (nestedY_coefficient_degree_le ℂ Q) (nestedY_coefficient_degree_le ℂ G)
  change (xResultant (nestedY ℂ Q) (nestedY ℂ G)).natDegree ≤ _ at h
  calc
    _ ≤ _ := h
    _ ≤ Q.totalDegree*G.totalDegree+G.totalDegree*Q.totalDegree := Nat.add_le_add
      (Nat.mul_le_mul_right _ (nestedY_degree_le ℂ Q))
      (Nat.mul_le_mul_right _ (nestedY_degree_le ℂ G))
    _ = _ := by ring

theorem irreducible_intersection_bound (Q G : MV ℂ) (hQ : Irreducible Q)
    (hdeg : 1 < Q.totalDegree) (hnd : ¬Q ∣ G) :
    (intersectionPoints Q G).Finite ∧
      (intersectionPoints Q G).ncard ≤ 2*Q.totalDegree^2*G.totalDegree := by
  rw [intersectionPoints_eq_nested]
  obtain ⟨hfin,hcard⟩ := common_zero_finite_count (nestedY ℂ Q) (nestedY ℂ G)
    (nonlinear_resultant_nonzero Q G hQ hdeg hnd) (nonlinear_fibers_nonzero Q hQ hdeg)
  refine ⟨hfin, hcard.trans ?_⟩
  calc
    _ ≤ (2*Q.totalDegree*G.totalDegree)*Q.totalDegree :=
      Nat.mul_le_mul (mv_resultant_degree_le Q G) (nestedY_degree_le ℂ Q)
    _ = _ := by ring

theorem irreducible_abscissa_bound (Q G : MV ℂ) (hQ : Irreducible Q)
    (hdeg : 1 < Q.totalDegree) (hnd : ¬Q ∣ G) :
    (intersectionAbscissae Q G).Finite ∧
      (intersectionAbscissae Q G).ncard ≤ 2*Q.totalDegree*G.totalDegree := by
  have hR := nonlinear_resultant_nonzero Q G hQ hdeg hnd
  have hF := nonlinear_fibers_nonzero Q hQ hdeg
  have hsub : intersectionAbscissae Q G ⊆
      (resultantRoots (nestedY ℂ Q) (nestedY ℂ G) : Set ℂ) := by
    rintro x ⟨p,hp,rfl⟩
    apply (mem_resultantRoots _ _ hR p.1).mpr
    apply common_zero_resultant_zero_of_fiber _ _ p.1 p.2 (hF p.1)
    · simpa only [beval_nested] using hp.1
    · simpa only [beval_nested] using hp.2
  have hfinite := (Finset.finite_toSet (resultantRoots (nestedY ℂ Q) (nestedY ℂ G))).subset hsub
  refine ⟨hfinite, ?_⟩
  calc
    _ ≤ (resultantRoots (nestedY ℂ Q) (nestedY ℂ G) : Set ℂ).ncard :=
      Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (resultantRoots (nestedY ℂ Q) (nestedY ℂ G)).card := Set.ncard_coe_finset _
    _ ≤ _ := (resultantRoots_card_le _ _).trans (mv_resultant_degree_le Q G)

end ErdosCriticalGeometry

end

section

namespace ErdosDivisibleInflection

open ErdosCriticalGeometry

theorem nested_affineLine (A B : ℂ) :
    nestedY ℂ (affineLine A B) = Polynomial.X-Polynomial.C (affineInner A B) := by
  simp [affineLine,affineInner,map_sub,map_add,map_mul]

theorem eval_affine_substitution (P : Nested ℂ) (A B x : ℂ) :
    (P.eval (affineInner A B)).eval x =
      ErdosBivariateResultant.beval P x (A*x+B) := by
  have h := Polynomial.eval₂_at_apply (p := P) (Polynomial.evalRingHom x) (affineInner A B)
  rw [← Polynomial.eval_map] at h
  simpa [affineInner,ErdosBivariateResultant.beval_eq_specialize,
    ErdosBivariateResultant.specialize] using h.symm

theorem affine_interval_factor (Q : MV ℂ) (A B : ℂ) (a b : ℝ) (hab : a < b)
    (hzero : ∀ t ∈ Set.Ioo a b,
      MvPolynomial.eval ![(t : ℂ),A*(t : ℂ)+B] Q = 0) : affineLine A B ∣ Q := by
  let P := nestedY ℂ Q
  let R := P.eval (affineInner A B)
  have hz (t : ℝ) (ht : t ∈ Set.Ioo a b) : R.eval (t : ℂ) = 0 := by
    rw [show R = P.eval (affineInner A B) from rfl, eval_affine_substitution]
    exact (beval_nested Q (t : ℂ) (A*(t : ℂ)+B)).trans (hzero t ht)
  have hR : R = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply ((Set.Ioo_infinite hab).image Complex.ofReal_injective.injOn).mono
    rintro z ⟨t,ht,rfl⟩
    exact hz t ht
  have hdiv : Polynomial.X-Polynomial.C (affineInner A B) ∣ P := Polynomial.dvd_iff_isRoot.mpr hR
  obtain ⟨H,hH⟩ := hdiv
  refine ⟨(nestedY ℂ).symm H, ?_⟩
  apply (nestedY ℂ).injective
  simpa only [map_mul,AlgEquiv.apply_symm_apply,nested_affineLine] using hH

theorem affineLine_not_unit (A B : ℂ) : ¬IsUnit (affineLine A B) := by
  intro h
  have hmap := h.map (nestedY ℂ).toRingHom
  change IsUnit (nestedY ℂ (affineLine A B)) at hmap
  rw [nested_affineLine] at hmap
  exact Polynomial.not_isUnit_X_sub_C _ hmap

theorem affineLine_degree_le (A B : ℂ) : (affineLine A B).totalDegree ≤ 1 := by
  have he : affineLine A B = MvPolynomial.X 1 +
      MvPolynomial.C (-A)*MvPolynomial.X 0+MvPolynomial.C (-B) := by
    simp only [affineLine,map_neg]
    ring
  rw [he]
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le
    · simp
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
  · simp

theorem no_affine_interval (Q : MV ℂ) (hQ : Irreducible Q) (hdeg : 1 < Q.totalDegree)
    (A B : ℂ) (a b : ℝ) (hab : a < b)
    (hzero : ∀ t ∈ Set.Ioo a b,
      MvPolynomial.eval ![(t : ℂ),A*(t : ℂ)+B] Q = 0) : False := by
  obtain ⟨H,hH⟩ := affine_interval_factor Q A B a b hab hzero
  have hunit : IsUnit H := (hQ.2 hH).resolve_left (affineLine_not_unit A B)
  have hD : H.totalDegree = 0 := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hunit).2
  have hle : Q.totalDegree ≤ 1 := by
    rw [hH]
    exact (MvPolynomial.totalDegree_mul _ _).trans (by rw [hD,add_zero]; exact affineLine_degree_le A B)
  omega

end ErdosDivisibleInflection

end

section

namespace ErdosCriticalGeometry

theorem mem_criticalPoints (Q : MV ℂ) (p : ℂ × ℂ) : p ∈ criticalPoints Q ↔
    MvPolynomial.eval ![p.1,p.2] Q = 0 ∧
      (MvPolynomial.eval ![p.1,p.2] (MvPolynomial.pderiv 0 Q) = 0 ∨
       MvPolynomial.eval ![p.1,p.2] (MvPolynomial.pderiv 1 Q) = 0) := by
  constructor
  · rintro (h | h)
    · exact ⟨h.1, Or.inl h.2⟩
    · exact ⟨h.1, Or.inr h.2⟩
  · rintro ⟨h, h' | h'⟩
    · exact Or.inl ⟨h,h'⟩
    · exact Or.inr ⟨h,h'⟩

theorem partial_intersection_bound (Q : MV ℂ) (hQ : Irreducible Q)
    (hdeg : 1 < Q.totalDegree) (i : Fin 2) :
    (intersectionPoints Q (MvPolynomial.pderiv i Q)).Finite ∧
      (intersectionPoints Q (MvPolynomial.pderiv i Q)).ncard ≤ 2*Q.totalDegree^3 := by
  obtain ⟨hfin,hcard⟩ := irreducible_intersection_bound Q (MvPolynomial.pderiv i Q)
    hQ hdeg (nonlinear_partial_not_dvd Q hQ hdeg i)
  refine ⟨hfin,hcard.trans ?_⟩
  calc
    _ ≤ (2*Q.totalDegree^2)*Q.totalDegree := Nat.mul_le_mul_left _
      ((partial_totalDegree_le ℂ Q i).trans (Nat.sub_le _ _))
    _ = _ := by ring

theorem partial_abscissa_bound (Q : MV ℂ) (hQ : Irreducible Q)
    (hdeg : 1 < Q.totalDegree) (i : Fin 2) :
    (intersectionAbscissae Q (MvPolynomial.pderiv i Q)).Finite ∧
      (intersectionAbscissae Q (MvPolynomial.pderiv i Q)).ncard ≤ 2*Q.totalDegree^2 := by
  obtain ⟨hfin,hcard⟩ := irreducible_abscissa_bound Q (MvPolynomial.pderiv i Q)
    hQ hdeg (nonlinear_partial_not_dvd Q hQ hdeg i)
  refine ⟨hfin,hcard.trans ?_⟩
  calc
    _ ≤ (2*Q.totalDegree)*Q.totalDegree := Nat.mul_le_mul_left _
      ((partial_totalDegree_le ℂ Q i).trans (Nat.sub_le _ _))
    _ = _ := by ring

theorem critical_points_bound (Q : MV ℂ) (hQ : Irreducible Q) (hdeg : 1 < Q.totalDegree) :
    (criticalPoints Q).Finite ∧ (criticalPoints Q).ncard ≤ 4*Q.totalDegree^3 := by
  obtain ⟨h0,c0⟩ := partial_intersection_bound Q hQ hdeg 0
  obtain ⟨h1,c1⟩ := partial_intersection_bound Q hQ hdeg 1
  refine ⟨h0.union h1, ?_⟩
  have h := Set.ncard_union_le (intersectionPoints Q (MvPolynomial.pderiv 0 Q))
    (intersectionPoints Q (MvPolynomial.pderiv 1 Q))
  change (criticalPoints Q).ncard ≤ _ at h
  omega

theorem critical_abscissae_bound (Q : MV ℂ) (hQ : Irreducible Q) (hdeg : 1 < Q.totalDegree) :
    (criticalAbscissae Q).Finite ∧ (criticalAbscissae Q).ncard ≤ 4*Q.totalDegree^2 := by
  obtain ⟨h0,c0⟩ := partial_abscissa_bound Q hQ hdeg 0
  obtain ⟨h1,c1⟩ := partial_abscissa_bound Q hQ hdeg 1
  have he : criticalAbscissae Q = intersectionAbscissae Q (MvPolynomial.pderiv 0 Q) ∪
      intersectionAbscissae Q (MvPolynomial.pderiv 1 Q) := Set.image_union _ _ _
  rw [he]
  refine ⟨h0.union h1, ?_⟩
  have h := Set.ncard_union_le (intersectionAbscissae Q (MvPolynomial.pderiv 0 Q))
    (intersectionAbscissae Q (MvPolynomial.pderiv 1 Q))
  omega

end ErdosCriticalGeometry

end

section

namespace ErdosCriticalGeometry

theorem inflection_degree_le (Q : MV ℂ) : (inflection Q).totalDegree ≤ 3*Q.totalDegree := by
  have h1 (i : Fin 2) : (MvPolynomial.pderiv i Q).totalDegree ≤ Q.totalDegree :=
    (partial_totalDegree_le ℂ Q i).trans (Nat.sub_le _ _)
  have h2 (i j : Fin 2) : (MvPolynomial.pderiv i (MvPolynomial.pderiv j Q)).totalDegree ≤ Q.totalDegree :=
    ((partial_totalDegree_le ℂ _ i).trans (Nat.sub_le _ _)).trans (h1 j)
  have hp (i : Fin 2) : ((MvPolynomial.pderiv i Q)^2).totalDegree ≤ 2*Q.totalDegree :=
    (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (h1 i))
  have ha : (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 Q)*(MvPolynomial.pderiv 1 Q)^2).totalDegree ≤
      3*Q.totalDegree := (MvPolynomial.totalDegree_mul _ _).trans (by linarith [h2 0 0,hp 1])
  have hb : (MvPolynomial.C (-2 : ℂ)*MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 Q)*
      MvPolynomial.pderiv 0 Q*MvPolynomial.pderiv 1 Q).totalDegree ≤ 3*Q.totalDegree := by
    have hA := MvPolynomial.totalDegree_mul (MvPolynomial.C (-2 : ℂ)) (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 Q))
    have hB := MvPolynomial.totalDegree_mul (MvPolynomial.C (-2 : ℂ)*MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 Q)) (MvPolynomial.pderiv 0 Q)
    have hC := MvPolynomial.totalDegree_mul (MvPolynomial.C (-2 : ℂ)*MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 Q)*MvPolynomial.pderiv 0 Q) (MvPolynomial.pderiv 1 Q)
    simp only [MvPolynomial.totalDegree_C, zero_add] at hA
    linarith [h2 0 1,h1 0,h1 1]
  have hc : (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 Q)*(MvPolynomial.pderiv 0 Q)^2).totalDegree ≤
      3*Q.totalDegree := (MvPolynomial.totalDegree_mul _ _).trans (by linarith [h2 1 1,hp 0])
  unfold inflection
  exact (MvPolynomial.totalDegree_add _ _).trans
    (max_le ((MvPolynomial.totalDegree_add _ _).trans (max_le ha hb)) hc)

theorem inflection_intersection_bounds (Q : MV ℂ) (hQ : Irreducible Q)
    (hdeg : 1 < Q.totalDegree) (hnd : ¬Q ∣ inflection Q) :
    (intersectionPoints Q (inflection Q)).Finite ∧
      (intersectionPoints Q (inflection Q)).ncard ≤ 6*Q.totalDegree^3 ∧
      (intersectionAbscissae Q (inflection Q)).Finite ∧
      (intersectionAbscissae Q (inflection Q)).ncard ≤ 6*Q.totalDegree^2 := by
  obtain ⟨hp,cp⟩ := irreducible_intersection_bound Q (inflection Q) hQ hdeg hnd
  obtain ⟨ha,ca⟩ := irreducible_abscissa_bound Q (inflection Q) hQ hdeg hnd
  refine ⟨hp,cp.trans ?_,ha,ca.trans ?_⟩
  · calc
      _ ≤ (2*Q.totalDegree^2)*(3*Q.totalDegree) := Nat.mul_le_mul_left _ (inflection_degree_le Q)
      _ = _ := by ring
  · calc
      _ ≤ (2*Q.totalDegree)*(3*Q.totalDegree) := Nat.mul_le_mul_left _ (inflection_degree_le Q)
      _ = _ := by ring

theorem exceptional_abscissae_bound (Q : MV ℂ) (hQ : Irreducible Q)
    (hdeg : 1 < Q.totalDegree) (hnd : ¬Q ∣ inflection Q) :
    (exceptionalAbscissae Q).Finite ∧ (exceptionalAbscissae Q).ncard ≤ 10*Q.totalDegree^2 := by
  obtain ⟨hc,cc⟩ := critical_abscissae_bound Q hQ hdeg
  obtain ⟨_,_,hi,ci⟩ := inflection_intersection_bounds Q hQ hdeg hnd
  have he : exceptionalAbscissae Q = criticalAbscissae Q ∪ intersectionAbscissae Q (inflection Q) :=
    Set.image_union _ _ _
  rw [he]
  refine ⟨hc.union hi, ?_⟩
  have h := Set.ncard_union_le (criticalAbscissae Q) (intersectionAbscissae Q (inflection Q))
  omega

end ErdosCriticalGeometry

end

section

namespace ErdosCriticalGeometry

theorem complexify_totalDegree (Q : MV ℝ) : (complexify Q).totalDegree = Q.totalDegree := by
  unfold complexify MvPolynomial.totalDegree
  rw [MvPolynomial.support_map_of_injective Q (show Function.Injective (algebraMap ℝ ℂ) from
    Complex.ofReal_injective)]

theorem complexify_partial (Q : MV ℝ) (i : Fin 2) :
    complexify (MvPolynomial.pderiv i Q) = MvPolynomial.pderiv i (complexify Q) :=
  MvPolynomial.pderiv_map.symm

theorem complexify_eval (Q : MV ℝ) (x y : ℝ) :
    MvPolynomial.eval ![(x : ℂ),(y : ℂ)] (complexify Q) = (MvPolynomial.eval ![x,y] Q : ℂ) := by
  have he : (algebraMap ℝ ℂ) ∘ (![x,y] : Fin 2 → ℝ) = ![(x : ℂ),(y : ℂ)] := by
    funext i
    fin_cases i <;> rfl
  have h := MvPolynomial.map_eval (algebraMap ℝ ℂ) ![x,y] Q
  rw [he] at h
  exact h.symm

theorem complexPoint_injective : Function.Injective complexPoint := by
  intro p q h
  apply Prod.ext
  · exact Complex.ofReal_injective (congrArg Prod.fst h)
  · exact Complex.ofReal_injective (congrArg Prod.snd h)

theorem real_critical_iff (Q : MV ℝ) (p : ℝ × ℝ) :
    complexPoint p ∈ criticalPoints (complexify Q) ↔ p ∈ realCriticalPoints Q := by
  rw [mem_criticalPoints]
  simp only [complexPoint, realCriticalPoints, Set.mem_ofPred_eq, ← complexify_partial,
    complexify_eval, Complex.ofReal_eq_zero]

theorem real_critical_points_bound (Q : MV ℝ) (hQ : Irreducible (complexify Q))
    (hdeg : 1 < Q.totalDegree) :
    (realCriticalPoints Q).Finite ∧ (realCriticalPoints Q).ncard ≤ 4*Q.totalDegree^3 := by
  have hd : 1 < (complexify Q).totalDegree := by rwa [complexify_totalDegree]
  obtain ⟨hfin,hcard⟩ := critical_points_bound (complexify Q) hQ hd
  have he : realCriticalPoints Q = complexPoint ⁻¹' criticalPoints (complexify Q) := by
    ext p
    exact (real_critical_iff Q p).symm
  have hrfin : (realCriticalPoints Q).Finite := by
    rw [he]
    exact hfin.preimage (fun _ _ _ _ h => complexPoint_injective h)
  refine ⟨hrfin, ?_⟩
  have hle := Set.ncard_le_ncard_of_injOn complexPoint
    (fun p hp => (real_critical_iff Q p).mpr hp) complexPoint_injective.injOn hfin
  apply hle.trans
  simpa only [complexify_totalDegree] using hcard

theorem real_critical_abscissae_bound (Q : MV ℝ) (hQ : Irreducible (complexify Q))
    (hdeg : 1 < Q.totalDegree) :
    (realCriticalAbscissae Q).Finite ∧ (realCriticalAbscissae Q).ncard ≤ 4*Q.totalDegree^2 := by
  have hd : 1 < (complexify Q).totalDegree := by rwa [complexify_totalDegree]
  obtain ⟨hfin,hcard⟩ := critical_abscissae_bound (complexify Q) hQ hd
  have hrfin := (real_critical_points_bound Q hQ hdeg).1.image Prod.fst
  refine ⟨hrfin, ?_⟩
  have hmap : ∀ x ∈ realCriticalAbscissae Q, (x : ℂ) ∈ criticalAbscissae (complexify Q) := by
    rintro x ⟨p,hp,he⟩
    exact ⟨complexPoint p,(real_critical_iff Q p).mpr hp,congrArg Complex.ofReal he⟩
  have hle := Set.ncard_le_ncard_of_injOn Complex.ofReal hmap Complex.ofReal_injective.injOn hfin
  apply hle.trans
  simpa only [complexify_totalDegree] using hcard

end ErdosCriticalGeometry

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_InflectionTransport
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosDivisibleInflection

open ErdosImplicitCurvature ErdosCriticalGeometry

theorem peval_eq_eval_pair (Q : MV ℝ) (x y : ℝ) :
    peval Q x y = MvPolynomial.eval ![x,y] Q := by
  have h : (fun i : Fin 2 => if i = 0 then x else y) = ![x,y] := by
    funext i
    fin_cases i <;> simp
  simp only [peval,h]

theorem complexify_inflection (Q : MV ℝ) :
    complexify (inflectionPolynomial Q) = inflection (complexify Q) := by
  unfold inflectionPolynomial partialX partialY inflection
  simp only [complexify, map_add, map_sub, map_mul, map_pow, map_ofNat,
    ← MvPolynomial.pderiv_map, map_neg]
  ring

theorem inflection_zero_of_complex_divisibility (Q : MV ℝ)
    (hdiv : complexify Q ∣ inflection (complexify Q)) (x y : ℝ)
    (hQ : peval Q x y = 0) : peval (inflectionPolynomial Q) x y = 0 := by
  have hQC : MvPolynomial.eval ![(x : ℂ),(y : ℂ)] (complexify Q) = 0 := by
    rw [complexify_eval, ← peval_eq_eval_pair, hQ]
    simp
  obtain ⟨H,hH⟩ := hdiv
  have hIC : MvPolynomial.eval ![(x : ℂ),(y : ℂ)] (inflection (complexify Q)) = 0 := by
    rw [hH, map_mul, hQC, zero_mul]
  rw [← complexify_inflection, complexify_eval, Complex.ofReal_eq_zero] at hIC
  rwa [peval_eq_eval_pair]

theorem zero_second_derivative_on_divisible_graph (Q : MV ℝ) (f : ℝ → ℝ) (a b : ℝ)
    (hdiv : complexify Q ∣ inflection (complexify Q))
    (hf : ContDiffOn ℝ 2 f (Set.Ioo a b))
    (hcurve : ∀ t ∈ Set.Ioo a b, peval Q t (f t) = 0)
    (hQy : ∀ t ∈ Set.Ioo a b, peval (partialY Q) t (f t) ≠ 0) :
    ∀ t ∈ Set.Ioo a b, deriv (deriv f) t = 0 := by
  intro t ht
  apply (curvature_zero_iff Q f isOpen_Ioo hf hcurve ht (hQy t ht)).mpr
  exact inflection_zero_of_complex_divisibility Q hdiv t (f t) (hcurve t ht)

end ErdosDivisibleInflection

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_AffineBranch
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosDivisibleInflection

theorem affine_of_second_derivative_zero (f : ℝ → ℝ) (a b x : ℝ)
    (hx : x ∈ Set.Ioo a b) (hf : ContDiffOn ℝ 2 f (Set.Ioo a b))
    (h2 : ∀ t ∈ Set.Ioo a b, deriv (deriv f) t = 0) :
    ∃ A B : ℝ, ∀ t ∈ Set.Ioo a b, f t = A*t+B := by
  have hdf : ContDiffOn ℝ 1 (deriv f) (Set.Ioo a b) := hf.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hdconst : Set.EqOn (deriv f) (fun _ => deriv f x) (Set.Ioo a b) := by
    apply isOpen_Ioo.eqOn_of_deriv_eq (g := fun _ : ℝ => deriv f x) isPreconnected_Ioo
      (hdf.differentiableOn (by norm_num)) (differentiableOn_const (deriv f x)) _ hx rfl
    intro t ht
    simpa only [deriv_const] using h2 t ht
  let A := deriv f x
  let B := f x-A*x
  have hAffine (t : ℝ) : HasDerivAt (fun t => A*t+B) A t := by
    simpa using ((hasDerivAt_id t).const_mul A).add_const B
  have he : Set.EqOn f (fun t => A*t+B) (Set.Ioo a b) := by
    apply isOpen_Ioo.eqOn_of_deriv_eq (g := fun t => A*t+B) isPreconnected_Ioo
      (hf.differentiableOn (by norm_num)) (fun t _ => (hAffine t).differentiableAt.differentiableWithinAt)
      _ hx _
    · intro t ht
      rw [(hAffine t).deriv]
      exact hdconst ht
    · dsimp [A,B]
      ring
  exact ⟨A,B,fun t ht => he ht⟩

end ErdosDivisibleInflection

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_DivisibleInflection
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosDivisibleInflection

open ErdosCriticalGeometry ErdosImplicitCurvature

theorem swap_twice (R : Type*) [CommSemiring R] (Q : MV R) :
    swapVars R (swapVars R Q) = Q := by
  simpa [swapVars] using (MvPolynomial.renameEquiv R (Equiv.swap (0 : Fin 2) 1)).apply_symm_apply Q

theorem nestedX_swap (R : Type*) [CommSemiring R] (Q : MV R) :
    nestedX R (swapVars R Q) = nestedY R Q := rfl

theorem nestedY_swap (R : Type*) [CommSemiring R] (Q : MV R) :
    nestedY R (swapVars R Q) = nestedX R Q := by
  change nestedX R (swapVars R (swapVars R Q)) = _
  rw [swap_twice]

theorem partial_zero_swap (R : Type*) [CommSemiring R] (Q : MV R) :
    MvPolynomial.pderiv 0 (swapVars R Q) = swapVars R (MvPolynomial.pderiv 1 Q) := by
  apply (nestedX R).injective
  rw [nestedX_partial_zero,nestedX_swap,nestedX_swap,nestedY_partial_one]

theorem partial_one_swap (R : Type*) [CommSemiring R] (Q : MV R) :
    MvPolynomial.pderiv 1 (swapVars R Q) = swapVars R (MvPolynomial.pderiv 0 Q) := by
  apply (nestedY R).injective
  rw [nestedY_partial_one,nestedY_swap,nestedY_swap,nestedX_partial_zero]

theorem eval_swap (R : Type*) [CommSemiring R] (Q : MV R) (x y : R) :
    MvPolynomial.eval ![x,y] (swapVars R Q) = MvPolynomial.eval ![y,x] Q := by
  have h1 := eval_nestedX R (swapVars R Q) x y
  rw [nestedX_swap] at h1
  exact h1.symm.trans (eval_nestedY R Q y x)

theorem peval_swap (Q : MV ℝ) (x y : ℝ) : peval (swapVars ℝ Q) x y = peval Q y x := by
  rw [peval_eq_eval_pair,peval_eq_eval_pair,eval_swap]

theorem complexify_swap (Q : MV ℝ) : complexify (swapVars ℝ Q) = swapVars ℂ (complexify Q) := by
  simp only [complexify,swapVars,MvPolynomial.renameEquiv_apply,MvPolynomial.map_rename]

theorem mixed_partials_complex (Q : MV ℂ) :
    MvPolynomial.pderiv 1 (MvPolynomial.pderiv 0 Q) =
      MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 Q) := by
  classical
  ext m
  simp [MvPolynomial.coeff_pderiv,add_assoc,add_left_comm,add_comm,mul_left_comm,mul_comm]
  ring

theorem inflection_swap (Q : MV ℂ) : inflection (swapVars ℂ Q) = swapVars ℂ (inflection Q) := by
  unfold inflection
  simp only [partial_zero_swap,partial_one_swap,mixed_partials_complex,map_add,map_mul,map_pow]
  have hC : swapVars ℂ (MvPolynomial.C (-2 : ℂ)) = MvPolynomial.C (-2 : ℂ) := by simp [swapVars]
  rw [hC]
  ring

theorem complex_divisibility_swap (Q : MV ℝ)
    (hdiv : complexify Q ∣ inflection (complexify Q)) :
    complexify (swapVars ℝ Q) ∣ inflection (complexify (swapVars ℝ Q)) := by
  rw [complexify_swap,inflection_swap]
  exact map_dvd (swapVars ℂ).toRingHom hdiv

end ErdosDivisibleInflection

end

section

namespace ErdosDivisibleInflection

open ErdosCriticalGeometry ErdosImplicitCurvature

theorem no_regular_y_point (Q : MV ℝ) (hQ : Irreducible (complexify Q))
    (hdeg : 1 < Q.totalDegree) (hdiv : complexify Q ∣ inflection (complexify Q))
    (x y : ℝ) (hzero : peval Q x y = 0) (hy : peval (partialY Q) x y ≠ 0) : False := by
  obtain ⟨a,b,f,hax,hxb,hfx,hf,hcurve,hfy⟩ := exists_local_real_graph Q x y hzero hy
  have hsecond := zero_second_derivative_on_divisible_graph Q f a b hdiv hf hcurve hfy
  obtain ⟨A,B,haffine⟩ := affine_of_second_derivative_zero f a b x ⟨hax,hxb⟩ hf hsecond
  have hdegC : 1 < (complexify Q).totalDegree := by rwa [complexify_totalDegree]
  apply no_affine_interval (complexify Q) hQ hdegC (A : ℂ) (B : ℂ) a b (hax.trans hxb)
  intro t ht
  have hz := hcurve t ht
  rw [haffine t ht] at hz
  have hc := complexify_eval Q t (A*t+B)
  rw [← peval_eq_eval_pair,hz] at hc
  simpa only [Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_zero] using hc

theorem no_regular_x_point (Q : MV ℝ) (hQ : Irreducible (complexify Q))
    (hdeg : 1 < Q.totalDegree) (hdiv : complexify Q ∣ inflection (complexify Q))
    (x y : ℝ) (hzero : peval Q x y = 0) (hx : peval (partialX Q) x y ≠ 0) : False := by
  have hirr : Irreducible (complexify (swapVars ℝ Q)) := by
    rw [complexify_swap]
    exact (MulEquiv.irreducible_iff (swapVars ℂ).toMulEquiv).mpr hQ
  have hd : 1 < (swapVars ℝ Q).totalDegree := by
    simpa only [swapVars,MvPolynomial.totalDegree_renameEquiv] using hdeg
  have hz : peval (swapVars ℝ Q) y x = 0 := by rw [peval_swap]; exact hzero
  have hpart : peval (partialY (swapVars ℝ Q)) y x ≠ 0 := by
    change peval (MvPolynomial.pderiv 1 (swapVars ℝ Q)) y x ≠ 0
    rw [partial_one_swap,peval_swap]
    exact hx
  exact no_regular_y_point (swapVars ℝ Q) hirr hd (complex_divisibility_swap Q hdiv) y x hz hpart

theorem divisible_inflection_gradient_zero (Q : MV ℝ)
    (hQ : Irreducible (complexify Q)) (hdeg : 1 < Q.totalDegree)
    (hdiv : complexify Q ∣ inflection (complexify Q)) (x y : ℝ)
    (hzero : peval Q x y = 0) :
    peval (partialX Q) x y = 0 ∧ peval (partialY Q) x y = 0 := by
  constructor
  · by_contra hx
    exact no_regular_x_point Q hQ hdeg hdiv x y hzero hx
  · by_contra hy
    exact no_regular_y_point Q hQ hdeg hdiv x y hzero hy

end ErdosDivisibleInflection

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_FiberCardinalityConstancy
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosGlobalFiberBranches

theorem finite_orderIso_unique {α β : Type*} [LinearOrder α] [LinearOrder β]
    [Finite α] (f g : α ≃o β) : f = g := Subsingleton.elim f g

end ErdosGlobalFiberBranches

end

section

open Set
namespace ErdosGlobalFiberBranches
open ErdosImplicitCurvature ErdosLocalFiberGraphs

theorem chartOrderIso_val {Q : Bivariate} {x L U : ℝ}
    (c : FiberCharts Q x L U) (t : ℝ) (ht : t ∈ Ioo c.a c.b)
    (r : boundedFiber Q x L U) : (chartOrderIso c t ht r : ℝ) = c.graph r t := rfl

end ErdosGlobalFiberBranches

end

section

open Set Filter
open scoped Topology
namespace ErdosLocalFiberGraphs
open ErdosImplicitCurvature ErdosCriticalGeometry

theorem boundedFiber_card_le_degree (Q : Bivariate) (x L U z : ℝ)
    (hz : peval Q x z ≠ 0) : (boundedFiber Q x L U).ncard ≤ Q.totalDegree := by
  classical
  have hf := boundedFiber_finite Q x L U z hz
  have hp : verticalPolynomial Q x ≠ 0 := by
    intro he
    apply hz
    rw [← verticalPolynomial_eval,he,Polynomial.eval_zero]
  calc
    (boundedFiber Q x L U).ncard = hf.toFinset.card := ncard_eq_toFinset_card _ hf
    _ ≤ (verticalPolynomial Q x).natDegree := Polynomial.card_le_degree_of_subset_roots (by
      intro y hy
      apply (Polynomial.mem_roots hp).mpr
      change (verticalPolynomial Q x).eval y = 0
      exact (verticalPolynomial_eval Q x y).trans (hf.mem_toFinset.mp hy).2)
    _ ≤ (nestedY ℝ Q).natDegree := Polynomial.natDegree_map_le
    _ ≤ Q.totalDegree := nestedY_degree_le ℝ Q

end ErdosLocalFiberGraphs

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_GlobalFiniteBranches
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set
open scoped Topology
namespace ErdosGlobalFiberBranches
open ErdosImplicitCurvature ErdosLocalFiberGraphs

namespace RegularDomain
variable {Q : Bivariate} {x L U : ℝ} {I : Set ℝ} (d : RegularDomain Q x L U I)
include d

theorem branch_eq_transport (r : boundedFiber Q x L U) {t : ℝ} (ht : t ∈ I) :
    d.branch r t = (d.transport t ht r : ℝ) := by simp only [branch,dite_eq_left ht]

theorem branch_mem (r : boundedFiber Q x L U) {t : ℝ} (ht : t ∈ I) :
    d.branch r t ∈ boundedFiber Q t L U := by
  rw [d.branch_eq_transport r ht]
  exact (d.transport t ht r).property

theorem branch_ordered {t : ℝ} (ht : t ∈ I) : StrictMono (fun r => d.branch r t) := by
  intro r s hrs
  change d.branch r t < d.branch s t
  rw [d.branch_eq_transport r ht,d.branch_eq_transport s ht]
  exact (d.transport t ht).strictMono hrs

theorem branch_coverage {t : ℝ} (ht : t ∈ I) :
    boundedFiber Q t L U = range (fun r => d.branch r t) := by
  ext y
  constructor
  · intro hy
    obtain ⟨r,hr⟩ := (d.transport t ht).surjective ⟨y,hy⟩
    refine ⟨r,?_⟩
    change d.branch r t = y
    rw [d.branch_eq_transport r ht]
    exact congrArg Subtype.val hr
  · rintro ⟨r,rfl⟩
    exact d.branch_mem r ht

theorem branch_interior (r : boundedFiber Q x L U) {t : ℝ} (ht : t ∈ I) :
    d.branch r t ∈ Ioo L U :=
  boundedFiber_interior Q t L U (d.regular ht).1 (d.regular ht).2.1 (d.branch_mem r ht)

end RegularDomain

end ErdosGlobalFiberBranches

end

section

open Set Filter
open scoped Topology ContDiff
namespace ErdosGlobalFiberBranches
open ErdosImplicitCurvature ErdosLocalFiberGraphs
namespace RegularDomain
variable {Q : Bivariate} {x L U : ℝ} {I : Set ℝ} (d : RegularDomain Q x L U I)

theorem transport_chart {t s : ℝ} (ht : t ∈ I) (hs : s ∈ I)
    (c : FiberCharts Q t L U) (hsc : s ∈ Ioo c.a c.b) :
    d.transport s hs = (d.transport t ht).trans (chartOrderIso c s hsc) := by
  let := (d.fiber_finite d.base_mem).fintype
  exact finite_orderIso_unique _ _

theorem branch_eq_chart (r : boundedFiber Q x L U) {t s : ℝ}
    (ht : t ∈ I) (hs : s ∈ I) (c : FiberCharts Q t L U) (hsc : s ∈ Ioo c.a c.b) :
    d.branch r s = c.graph (d.transport t ht r) s := by
  rw [d.branch_eq_transport r hs,d.transport_chart ht hs c hsc]
  exact chartOrderIso_val c s hsc (d.transport t ht r)

theorem branch_smooth (r : boundedFiber Q x L U) : ContDiffOn ℝ 2 (d.branch r) I := by
  apply d.isOpen.contDiffOn_iff.mpr
  intro t ht
  obtain ⟨c⟩ := exists_bounded_fiber_charts Q t L U
    (d.regular ht).1 (d.regular ht).2.1 (d.regular ht).2.2
  have hc : ContDiffAt ℝ 2 (c.graph (d.transport t ht r)) t :=
    (c.graph_smooth _).contDiffAt (isOpen_Ioo.mem_nhds ⟨c.left,c.right⟩)
  apply hc.congr_of_eventuallyEq
  filter_upwards [d.isOpen.mem_nhds ht,isOpen_Ioo.mem_nhds ⟨c.left,c.right⟩] with s hsI hsC
  exact d.branch_eq_chart r ht hsI c hsC

end RegularDomain

end ErdosGlobalFiberBranches

end

section

open Set
open scoped Topology ContDiff
namespace ErdosGlobalFiberBranches
open ErdosImplicitCurvature ErdosLocalFiberGraphs

theorem global_finite_ordered_branches (Q : Bivariate) (x L U : ℝ) (I : Set ℝ)
    (hopen : IsOpen I) (hconn : IsPreconnected I) (hx : x ∈ I)
    (hregular : I ⊆ regularParameters Q L U) :
    ∃ n : ℕ, n = (boundedFiber Q x L U).ncard ∧ n ≤ Q.totalDegree ∧
      ∃ f : Fin n → ℝ → ℝ,
        (∀ i, ContDiffOn ℝ 2 (f i) I) ∧
        (∀ t ∈ I, StrictMono (fun i => f i t)) ∧
        (∀ i, ∀ t ∈ I, f i t ∈ Ioo L U ∧ peval Q t (f i t) = 0 ∧
          peval (partialY Q) t (f i t) ≠ 0) ∧
        (∀ t ∈ I, boundedFiber Q t L U = range (fun i => f i t)) := by
  classical
  let d : RegularDomain Q x L U I := ⟨hopen,hconn,hx,hregular⟩
  let := (d.fiber_finite hx).fintype
  let n := (boundedFiber Q x L U).ncard
  let e : Fin n ≃o boundedFiber Q x L U :=
    Fintype.orderIsoFinOfCardEq _ (fintypeCard_eq_ncard _)
  refine ⟨n,rfl,boundedFiber_card_le_degree Q x L U L (hregular hx).1,
    (fun i => d.branch (e i)),(fun i => d.branch_smooth (e i)),?_,?_,?_⟩
  · exact fun t ht => (d.branch_ordered ht).comp e.strictMono
  · intro i t ht
    exact ⟨d.branch_interior (e i) ht,(d.branch_mem (e i) ht).2,
      (hregular ht).2.2 _ (d.branch_mem (e i) ht)⟩
  · intro t ht
    rw [d.branch_coverage ht]
    ext y
    constructor
    · rintro ⟨r,hr⟩
      obtain ⟨i,rfl⟩ := e.surjective r
      exact ⟨i,hr⟩
    · rintro ⟨i,hi⟩
      exact ⟨e i,hi⟩

theorem global_branches_on_regular_domain (Q : Bivariate) (L U : ℝ) (I : Set ℝ)
    (hopen : IsOpen I) (hconn : IsPreconnected I)
    (hregular : I ⊆ regularParameters Q L U) :
    ∃ n ≤ Q.totalDegree, ∃ f : Fin n → ℝ → ℝ,
      (∀ i, ContDiffOn ℝ 2 (f i) I) ∧
      (∀ t ∈ I, StrictMono (fun i => f i t)) ∧
      (∀ i, ∀ t ∈ I, f i t ∈ Ioo L U ∧ peval Q t (f i t) = 0 ∧
        peval (partialY Q) t (f i t) ≠ 0) ∧
      (∀ t ∈ I, boundedFiber Q t L U = range (fun i => f i t)) := by
  classical
  by_cases hI : I.Nonempty
  · obtain ⟨x,hx⟩ := hI
    obtain ⟨n,_,hn,f,hf⟩ := global_finite_ordered_branches Q x L U I hopen hconn hx hregular
    exact ⟨n,hn,f,hf⟩
  · have hempty : I = ∅ := not_nonempty_iff_eq_empty.mp hI
    subst I
    refine ⟨0,Nat.zero_le _,Fin.elim0,?_,?_,?_,?_⟩
    · exact fun i => Fin.elim0 i
    · simp
    · simp
    · simp

end ErdosGlobalFiberBranches

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_PolynomialStripPoints
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set
namespace ErdosRegularStrip
open ErdosImplicitCurvature ErdosLocalFiberGraphs ErdosConvexGraph
attribute [local instance] Classical.propDecidable

theorem mem_polynomialStripPoints (Q : Bivariate) (a b S : ℝ) (p : ℤ × ℤ) :
    p ∈ polynomialStripPoints Q a b S ↔
      InSquare S p ∧ (p.1 : ℝ) ∈ Ioo a b ∧ peval Q p.1 p.2 = 0 := by
  simp only [polynomialStripPoints,InSquare,Finset.mem_filter,Finset.product_eq_sprod,
    Finset.mem_product,Finset.mem_Icc,Int.le_floor,Int.cast_nonneg_iff]

theorem strip_eq_graph_union (Q : Bivariate) (a b S : ℝ) {n : ℕ} (f : Fin n → ℝ → ℝ)
    (hcurve : ∀ i, ∀ t ∈ Ioo a b, peval Q t (f i t) = 0)
    (hcover : ∀ t ∈ Ioo a b, boundedFiber Q t 0 S = range (fun i => f i t)) :
    polynomialStripPoints Q a b S =
      Finset.univ.biUnion (fun i => graphLatticePoints (Ioo a b) (f i) S) := by
  classical
  ext p
  constructor
  · intro hp
    have h := (mem_polynomialStripPoints Q a b S p).mp hp
    have hy : (p.2 : ℝ) ∈ boundedFiber Q p.1 0 S := ⟨h.1.2,h.2.2⟩
    obtain ⟨i,hi⟩ := (hcover p.1 h.2.1).subset hy
    apply Finset.mem_biUnion.mpr
    exact ⟨i,Finset.mem_univ i,(mem_graphLatticePoints _ _ _ p).mpr
      ⟨h.1,h.2.1,hi.symm⟩⟩
  · intro hp
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hp
    have h := (mem_graphLatticePoints (Ioo a b) (f i) S p).mp hi
    apply (mem_polynomialStripPoints Q a b S p).mpr
    refine ⟨h.1,h.2.1,?_⟩
    rw [h.2.2]
    exact hcurve i p.1 h.2.1

end ErdosRegularStrip

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_RegularStripBound
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set
namespace ErdosRegularStrip
open ErdosImplicitCurvature ErdosLocalFiberGraphs ErdosGlobalFiberBranches ErdosConvexGraph

theorem regular_strip_lattice_bound (Q : Bivariate) (a b S : ℝ) (hS : 0 ≤ S)
    (hboundary : ∀ t ∈ Ioo a b, peval Q t 0 ≠ 0 ∧ peval Q t S ≠ 0)
    (hregular : ∀ t ∈ Ioo a b, ∀ y ∈ Icc 0 S, peval Q t y = 0 →
      peval (partialX Q) t y ≠ 0 ∧ peval (partialY Q) t y ≠ 0 ∧
        peval (inflectionPolynomial Q) t y ≠ 0) :
    ((polynomialStripPoints Q a b S).card : ℝ) ≤
      12*(Q.totalDegree : ℝ)*(1+S^((2 : ℝ)/3)) := by
  classical
  have hR : Ioo a b ⊆ regularParameters Q 0 S := by
    intro t ht
    exact ⟨(hboundary t ht).1,(hboundary t ht).2,
      fun y hy => (hregular t ht y hy.1 hy.2).2.1⟩
  obtain ⟨n,hn,f,hf,_,hvals,hcover⟩ :=
    global_branches_on_regular_domain Q 0 S (Ioo a b) isOpen_Ioo isPreconnected_Ioo hR
  have hcurve : ∀ i, ∀ t ∈ Ioo a b, peval Q t (f i t) = 0 :=
    fun i t ht => (hvals i t ht).2.1
  have hparts (i : Fin n) : ((graphLatticePoints (Ioo a b) (f i) S).card : ℝ) ≤
      12*(1+S^((2 : ℝ)/3)) := by
    apply regular_implicit_arc_lattice_bound Q (f i) a b S hS (hf i) (hcurve i)
    · intro t ht
      exact (hregular t ht (f i t) (Ioo_subset_Icc_self (hvals i t ht).1)
        (hcurve i t ht)).1
    · exact fun t ht => (hvals i t ht).2.2
    · intro t ht
      exact (hregular t ht (f i t) (Ioo_subset_Icc_self (hvals i t ht).1)
        (hcurve i t ht)).2.2
  have hcount : (polynomialStripPoints Q a b S).card ≤
      ∑ i : Fin n, (graphLatticePoints (Ioo a b) (f i) S).card := by
    rw [strip_eq_graph_union Q a b S f hcurve hcover]
    exact Finset.card_biUnion_le
  calc
    ((polynomialStripPoints Q a b S).card : ℝ) ≤
        ∑ i : Fin n, ((graphLatticePoints (Ioo a b) (f i) S).card : ℝ) := by exact_mod_cast hcount
    _ ≤ ∑ _i : Fin n, 12*(1+S^((2 : ℝ)/3)) := Finset.sum_le_sum (fun i _ => hparts i)
    _ = (n : ℝ)*(12*(1+S^((2 : ℝ)/3))) := by simp
    _ ≤ (Q.totalDegree : ℝ)*(12*(1+S^((2 : ℝ)/3))) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (by positivity)
    _ = 12*(Q.totalDegree : ℝ)*(1+S^((2 : ℝ)/3)) := by ring

end ErdosRegularStrip

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SortedRealGaps
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set
namespace ErdosMarkedStrips

theorem no_mark_in_gap (E : Finset ℝ) (i : Fin (E.card-1)) {x : ℝ}
    (hx : x ∈ Ioo (gapLeft E i) (gapRight E i)) : x ∉ E := by
  intro hE
  obtain ⟨j,hj⟩ := (E.range_orderEmbOfFin rfl).symm.subset hE
  have hl : gapLeft E i < E.orderEmbOfFin rfl j := by simpa only [hj] using hx.1
  have hh : E.orderEmbOfFin rfl j < gapRight E i := by simpa only [hj] using hx.2
  have hlo := (E.orderEmbOfFin rfl).lt_iff_lt.mp hl
  have hhi := (E.orderEmbOfFin rfl).lt_iff_lt.mp hh
  change i.val < j.val at hlo
  change j.val < i.val+1 at hhi
  omega

theorem exists_gap_of_not_mem (E : Finset ℝ) {S x : ℝ} (h0 : 0 ∈ E) (hS : S ∈ E)
    (hx : x ∈ Icc 0 S) (hxE : x ∉ E) :
    ∃ i : Fin (E.card-1), x ∈ Ioo (gapLeft E i) (gapRight E i) := by
  classical
  let e := E.orderEmbOfFin rfl
  obtain ⟨j0,hj0⟩ := (E.range_orderEmbOfFin rfl).symm.subset h0
  obtain ⟨jS,hjS⟩ := (E.range_orderEmbOfFin rfl).symm.subset hS
  have hx0 : 0 < x := lt_of_le_of_ne hx.1 (fun he => hxE (he ▸ h0))
  let A := Finset.univ.filter (fun j : Fin E.card => e j < x)
  have hA : A.Nonempty := ⟨j0,Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,by simpa only [e,hj0] using hx0⟩⟩
  let j := A.max' hA
  have hjA : j ∈ A := A.max'_mem hA
  have hjx : e j < x := (Finset.mem_filter.mp hjA).2
  have hjSlt : j < jS := e.lt_iff_lt.mp (hjx.trans_le (by simpa only [e,hjS] using hx.2))
  have hnext : j.val+1 < E.card := by have hj := jS.isLt; change j.val < jS.val at hjSlt; omega
  let k : Fin E.card := ⟨j.val+1,hnext⟩
  have hnot : ¬e k < x := by
    intro hkx
    have hkA : k ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hkx⟩
    have hle : k ≤ j := A.le_max' k hkA
    change j.val+1 ≤ j.val at hle
    omega
  have hxne : x ≠ e k := by
    intro he
    apply hxE
    rw [he]
    exact E.orderEmbOfFin_mem rfl k
  let i : Fin (E.card-1) := ⟨j.val,by omega⟩
  refine ⟨i,?_,?_⟩
  · exact hjx
  · exact lt_of_le_of_ne (le_of_not_gt hnot) hxne

end ErdosMarkedStrips

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_MarkedStripTotal
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set
namespace ErdosMarkedStrips
open ErdosImplicitCurvature ErdosLocalFiberGraphs ErdosRegularStrip ErdosConvexGraph
attribute [local instance] Classical.propDecidable

theorem mem_polynomialSquarePoints (Q : Bivariate) (S : ℝ) (p : ℤ × ℤ) :
    p ∈ polynomialSquarePoints Q S ↔ InSquare S p ∧ peval Q p.1 p.2 = 0 := by
  simp only [polynomialSquarePoints,InSquare,Finset.mem_filter,Finset.product_eq_sprod,
    Finset.mem_product,Finset.mem_Icc,Int.le_floor,Int.cast_nonneg_iff]

theorem mem_markedFiberPoints (Q : Bivariate) (t S : ℝ) (p : ℤ × ℤ) :
    p ∈ markedFiberPoints Q t S ↔ p ∈ polynomialSquarePoints Q S ∧ (p.1 : ℝ) = t := by
  simp only [markedFiberPoints,Finset.mem_filter]

theorem markedFiber_card_le (Q : Bivariate) (t S : ℝ)
    (hp : verticalPolynomial Q t ≠ 0) : (markedFiberPoints Q t S).card ≤ Q.totalDegree := by
  classical
  obtain ⟨z,hz⟩ : ∃ z : ℝ, peval Q t z ≠ 0 := by
    by_contra! h
    apply hp
    apply Polynomial.funext
    intro z
    rw [verticalPolynomial_eval,h z,Polynomial.eval_zero]
  have hfin := boundedFiber_finite Q t 0 S z hz
  have hmap : ∀ p ∈ (markedFiberPoints Q t S : Set (ℤ × ℤ)),
      (p.2 : ℝ) ∈ boundedFiber Q t 0 S := by
    intro p hp
    have hm := (mem_markedFiberPoints Q t S p).mp hp
    have hs := (mem_polynomialSquarePoints Q S p).mp hm.1
    refine ⟨hs.1.2,?_⟩
    simpa only [hm.2] using hs.2
  have hinj : InjOn (fun p : ℤ × ℤ => (p.2 : ℝ)) (markedFiberPoints Q t S : Set (ℤ × ℤ)) := by
    intro p hp q hq hpq
    have hp1 := ((mem_markedFiberPoints Q t S p).mp hp).2
    have hq1 := ((mem_markedFiberPoints Q t S q).mp hq).2
    apply Prod.ext
    · exact_mod_cast hp1.trans hq1.symm
    · change (p.2 : ℝ) = (q.2 : ℝ) at hpq
      exact_mod_cast hpq
  have hc := ncard_le_ncard_of_injOn (fun p : ℤ × ℤ => (p.2 : ℝ)) hmap hinj hfin
  simp only [ncard_coe_finset] at hc
  exact hc.trans (boundedFiber_card_le_degree Q t 0 S z hz)

theorem square_points_partition (Q : Bivariate) (S : ℝ) (E : Finset ℝ)
    (h0 : 0 ∈ E) (hS : S ∈ E) :
    polynomialSquarePoints Q S =
      E.biUnion (fun t => markedFiberPoints Q t S) ∪
        Finset.univ.biUnion (fun i : Fin (E.card-1) =>
          polynomialStripPoints Q (gapLeft E i) (gapRight E i) S) := by
  classical
  ext p
  constructor
  · intro hp
    have hs := (mem_polynomialSquarePoints Q S p).mp hp
    by_cases hm : (p.1 : ℝ) ∈ E
    · apply Finset.mem_union_left
      exact Finset.mem_biUnion.mpr ⟨p.1,hm,(mem_markedFiberPoints Q p.1 S p).mpr ⟨hp,rfl⟩⟩
    · obtain ⟨i,hi⟩ := exists_gap_of_not_mem E h0 hS hs.1.1 hm
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,
        (mem_polynomialStripPoints Q _ _ S p).mpr ⟨hs.1,hi,hs.2⟩⟩
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨t,_,ht⟩ := Finset.mem_biUnion.mp hp
      exact ((mem_markedFiberPoints Q t S p).mp ht).1
    · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hp
      have hs := (mem_polynomialStripPoints Q _ _ S p).mp hi
      exact (mem_polynomialSquarePoints Q S p).mpr ⟨hs.1,hs.2.2⟩

end ErdosMarkedStrips

end

section

open Set
namespace ErdosMarkedStrips
open ErdosImplicitCurvature ErdosLocalFiberGraphs ErdosRegularStrip ErdosConvexGraph

theorem marked_square_lattice_bound (Q : Bivariate) (S : ℝ) (E : Finset ℝ)
    (hS : 0 ≤ S) (h0 : 0 ∈ E) (hSE : S ∈ E)
    (hfiber : ∀ t ∈ E, verticalPolynomial Q t ≠ 0) (hregular : RegularOff Q S E) :
    ((polynomialSquarePoints Q S).card : ℝ) ≤
      13*(E.card : ℝ)*(Q.totalDegree : ℝ)*(1+S^((2 : ℝ)/3)) := by
  classical
  let B := 1+S^((2 : ℝ)/3)
  have hB : 1 ≤ B := by
    dsimp [B]
    exact le_add_of_nonneg_right (Real.rpow_nonneg hS _)
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  have hstrip (i : Fin (E.card-1)) :
      ((polynomialStripPoints Q (gapLeft E i) (gapRight E i) S).card : ℝ) ≤
        12*(Q.totalDegree : ℝ)*B := by
    apply regular_strip_lattice_bound Q _ _ S hS
    · exact fun t ht => (hregular t (no_mark_in_gap E i ht)).1
    · exact fun t ht => (hregular t (no_mark_in_gap E i ht)).2
  have hcount : (polynomialSquarePoints Q S).card ≤
      (∑ t ∈ E, (markedFiberPoints Q t S).card) +
      ∑ i : Fin (E.card-1), (polynomialStripPoints Q (gapLeft E i) (gapRight E i) S).card := by
    rw [square_points_partition Q S E h0 hSE]
    exact (Finset.card_union_le _ _).trans
      (Nat.add_le_add Finset.card_biUnion_le Finset.card_biUnion_le)
  have hm : (∑ t ∈ E, ((markedFiberPoints Q t S).card : ℝ)) ≤
      (E.card : ℝ)*(Q.totalDegree : ℝ) := by
    calc
      _ ≤ ∑ _t ∈ E, (Q.totalDegree : ℝ) := Finset.sum_le_sum (fun t ht => by
        exact_mod_cast markedFiber_card_le Q t S (hfiber t ht))
      _ = _ := by simp
  have hg : (∑ i : Fin (E.card-1),
      ((polynomialStripPoints Q (gapLeft E i) (gapRight E i) S).card : ℝ)) ≤
      (E.card : ℝ)*(12*(Q.totalDegree : ℝ)*B) := by
    calc
      _ ≤ ∑ _i : Fin (E.card-1), 12*(Q.totalDegree : ℝ)*B :=
        Finset.sum_le_sum (fun i _ => hstrip i)
      _ = ((E.card-1 : ℕ) : ℝ)*(12*(Q.totalDegree : ℝ)*B) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le E.card 1) (by positivity)
  have hc : ((polynomialSquarePoints Q S).card : ℝ) ≤
      (∑ t ∈ E, ((markedFiberPoints Q t S).card : ℝ)) +
      ∑ i : Fin (E.card-1), ((polynomialStripPoints Q (gapLeft E i) (gapRight E i) S).card : ℝ) := by
    exact_mod_cast hcount
  calc
    ((polynomialSquarePoints Q S).card : ℝ) ≤
        (E.card : ℝ)*(Q.totalDegree : ℝ) + (E.card : ℝ)*(12*(Q.totalDegree : ℝ)*B) :=
      hc.trans (add_le_add hm hg)
    _ ≤ (E.card : ℝ)*(Q.totalDegree : ℝ)*B + (E.card : ℝ)*(12*(Q.totalDegree : ℝ)*B) := by
      have hscale : (E.card : ℝ)*(Q.totalDegree : ℝ) ≤
          (E.card : ℝ)*(Q.totalDegree : ℝ)*B := by
        calc
          _ = (E.card : ℝ)*(Q.totalDegree : ℝ)*1 := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hB (by positivity)
      exact add_le_add hscale le_rfl
    _ = 13*(E.card : ℝ)*(Q.totalDegree : ℝ)*(1+S^((2 : ℝ)/3)) := by dsimp [B] <;> ring

theorem marked_square_cubic_bound (Q : Bivariate) (S : ℝ) (E : Finset ℝ) (C : ℕ)
    (hS : 0 ≤ S) (h0 : 0 ∈ E) (hSE : S ∈ E)
    (hfiber : ∀ t ∈ E, verticalPolynomial Q t ≠ 0) (hregular : RegularOff Q S E)
    (hcard : E.card ≤ C*Q.totalDegree^2) :
    ((polynomialSquarePoints Q S).card : ℝ) ≤
      13*(C : ℝ)*(Q.totalDegree : ℝ)^3*(1+S^((2 : ℝ)/3)) := by
  calc
    ((polynomialSquarePoints Q S).card : ℝ) ≤
        13*(E.card : ℝ)*(Q.totalDegree : ℝ)*(1+S^((2 : ℝ)/3)) :=
      marked_square_lattice_bound Q S E hS h0 hSE hfiber hregular
    _ ≤ 13*((C : ℝ)*(Q.totalDegree : ℝ)^2)*(Q.totalDegree : ℝ)*(1+S^((2 : ℝ)/3)) := by
      gcongr
      exact_mod_cast hcard
    _ = _ := by ring

end ErdosMarkedStrips

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_RealAlgebraicFibers
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set
namespace ErdosAlgebraicCurve
open ErdosCriticalGeometry ErdosImplicitCurvature ErdosDivisibleInflection ErdosLocalFiberGraphs

theorem finite_real_preimage (A : Set ℂ) (hA : A.Finite) :
    (Complex.ofReal ⁻¹' A).Finite ∧ (Complex.ofReal ⁻¹' A).ncard ≤ A.ncard := by
  refine ⟨hA.preimage Complex.ofReal_injective.injOn,?_⟩
  exact ncard_le_ncard_of_injOn Complex.ofReal (fun _ h => h) Complex.ofReal_injective.injOn hA

theorem real_vertical_nonzero (Q : MV ℝ) (hQ : Irreducible (complexify Q))
    (hdeg : 1 < Q.totalDegree) (x : ℝ) : verticalPolynomial Q x ≠ 0 := by
  intro hz
  have hdegC : 1 < (complexify Q).totalDegree := by rwa [complexify_totalDegree]
  let P := ErdosBivariateResultant.specialize (nestedY ℂ (complexify Q)) (x : ℂ)
  have hp : P ≠ 0 := nonlinear_fibers_nonzero (complexify Q) hQ hdegC x
  have hroot : ∀ y : ℝ, P.IsRoot (y : ℂ) := by
    intro y
    have hy : peval Q x y = 0 := by rw [← verticalPolynomial_eval,hz,Polynomial.eval_zero]
    change ErdosBivariateResultant.beval (nestedY ℂ (complexify Q)) (x : ℂ) (y : ℂ) = 0
    rw [beval_nested,complexify_eval,← peval_eq_eval_pair,hy,Complex.ofReal_zero]
  have hinf : (range Complex.ofReal).Infinite := infinite_range_of_injective Complex.ofReal_injective
  apply hinf
  apply (Polynomial.finite_setOfPred_isRoot hp).subset
  rintro y ⟨z,rfl⟩
  exact hroot z

end ErdosAlgebraicCurve

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_HorizontalBoundaryMarks
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set
namespace ErdosAlgebraicCurve
open ErdosCriticalGeometry ErdosImplicitCurvature ErdosDivisibleInflection

theorem horizontalLine_ne_zero (z : ℂ) : affineLine 0 z ≠ 0 := by
  intro hz
  have h := congrArg (MvPolynomial.eval ![(0 : ℂ),z+1]) hz
  simp [affineLine] at h

theorem nonlinear_not_dvd_horizontal (Q : MV ℂ) (hdeg : 1 < Q.totalDegree) (z : ℂ) :
    ¬Q ∣ affineLine 0 z := by
  intro hdiv
  have hd := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv (horizontalLine_ne_zero z)
  exact (not_le_of_gt hdeg) (hd.trans (affineLine_degree_le 0 z))

theorem boundary_abscissae_bound (Q : MV ℝ) (hQ : Irreducible (complexify Q))
    (hdeg : 1 < Q.totalDegree) (y : ℝ) :
    (boundaryAbscissae Q y).Finite ∧ (boundaryAbscissae Q y).ncard ≤ 2*Q.totalDegree := by
  have hd : 1 < (complexify Q).totalDegree := by rwa [complexify_totalDegree]
  obtain ⟨hfin,hcard⟩ := irreducible_abscissa_bound (complexify Q) (affineLine 0 (y : ℂ)) hQ hd
    (nonlinear_not_dvd_horizontal _ hd y)
  have hpre := finite_real_preimage (intersectionAbscissae (complexify Q) (affineLine 0 (y : ℂ))) hfin
  have hsub : boundaryAbscissae Q y ⊆
      Complex.ofReal ⁻¹' intersectionAbscissae (complexify Q) (affineLine 0 (y : ℂ)) := by
    intro x hx
    refine ⟨((x : ℂ),(y : ℂ)),⟨?_,?_⟩,rfl⟩
    · rw [complexify_eval,← peval_eq_eval_pair]
      change peval Q x y = 0 at hx
      rw [hx,Complex.ofReal_zero]
    · simp [affineLine]
  refine ⟨hpre.1.subset hsub,?_⟩
  calc
    _ ≤ (Complex.ofReal ⁻¹' intersectionAbscissae (complexify Q) (affineLine 0 (y : ℂ))).ncard :=
      ncard_le_ncard hsub hpre.1
    _ ≤ _ := hpre.2
    _ ≤ _ := hcard
    _ ≤ 2*(complexify Q).totalDegree*1 := Nat.mul_le_mul_left _ (affineLine_degree_le 0 y)
    _ = 2*Q.totalDegree := by rw [mul_one,complexify_totalDegree]

end ErdosAlgebraicCurve

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_RealExceptionalMarks
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set
namespace ErdosAlgebraicCurve
open ErdosCriticalGeometry ErdosImplicitCurvature ErdosDivisibleInflection

theorem mem_realExceptionalAbscissae (Q : MV ℝ) (x y : ℝ) (hzero : peval Q x y = 0)
    (hbad : peval (partialX Q) x y = 0 ∨ peval (partialY Q) x y = 0 ∨
      peval (inflectionPolynomial Q) x y = 0) : x ∈ realExceptionalAbscissae Q := by
  have hc : complexPoint (x,y) ∈ exceptionalPoints (complexify Q) := by
    rcases hbad with hx | hy | hi
    · apply Or.inl
      apply (real_critical_iff Q (x,y)).mpr
      change MvPolynomial.eval ![x,y] Q = 0 ∧
        (MvPolynomial.eval ![x,y] (MvPolynomial.pderiv 0 Q) = 0 ∨
         MvPolynomial.eval ![x,y] (MvPolynomial.pderiv 1 Q) = 0)
      simpa only [← peval_eq_eval_pair,partialX,partialY] using And.intro hzero (Or.inl hx)
    · apply Or.inl
      apply (real_critical_iff Q (x,y)).mpr
      change MvPolynomial.eval ![x,y] Q = 0 ∧
        (MvPolynomial.eval ![x,y] (MvPolynomial.pderiv 0 Q) = 0 ∨
         MvPolynomial.eval ![x,y] (MvPolynomial.pderiv 1 Q) = 0)
      simpa only [← peval_eq_eval_pair,partialX,partialY] using And.intro hzero (Or.inr hy)
    · apply Or.inr
      change MvPolynomial.eval ![(x : ℂ),(y : ℂ)] (complexify Q) = 0 ∧
        MvPolynomial.eval ![(x : ℂ),(y : ℂ)] (inflection (complexify Q)) = 0
      constructor
      · rw [complexify_eval,← peval_eq_eval_pair,hzero,Complex.ofReal_zero]
      · rw [← complexify_inflection,complexify_eval,← peval_eq_eval_pair,hi,Complex.ofReal_zero]
  exact ⟨complexPoint (x,y),hc,rfl⟩

theorem divisible_critical_marks (Q : MV ℝ) (hQ : Irreducible (complexify Q))
    (hdeg : 1 < Q.totalDegree) (hdiv : complexify Q ∣ inflection (complexify Q)) :
    ∃ B : Finset ℝ, B.card ≤ 4*Q.totalDegree^2 ∧ ∀ x ∉ B, ∀ y : ℝ, peval Q x y ≠ 0 := by
  classical
  obtain ⟨hf,hc⟩ := real_critical_abscissae_bound Q hQ hdeg
  refine ⟨hf.toFinset,?_,?_⟩
  · rwa [← ncard_eq_toFinset_card _ hf]
  · intro x hx y hzero
    apply hx
    apply hf.mem_toFinset.mpr
    refine ⟨(x,y),?_,rfl⟩
    have hgrad := divisible_inflection_gradient_zero Q hQ hdeg hdiv x y hzero
    change MvPolynomial.eval ![x,y] Q = 0 ∧
      (MvPolynomial.eval ![x,y] (MvPolynomial.pderiv 0 Q) = 0 ∨
       MvPolynomial.eval ![x,y] (MvPolynomial.pderiv 1 Q) = 0)
    simpa only [← peval_eq_eval_pair,partialX,partialY] using And.intro hzero (Or.inl hgrad.1)

theorem nondivisible_exceptional_marks (Q : MV ℝ) (hQ : Irreducible (complexify Q))
    (hdeg : 1 < Q.totalDegree) (hnd : ¬complexify Q ∣ inflection (complexify Q)) :
    ∃ B : Finset ℝ, B.card ≤ 10*Q.totalDegree^2 ∧
      ∀ x ∉ B, ∀ y : ℝ, peval Q x y = 0 →
        peval (partialX Q) x y ≠ 0 ∧ peval (partialY Q) x y ≠ 0 ∧
          peval (inflectionPolynomial Q) x y ≠ 0 := by
  classical
  have hd : 1 < (complexify Q).totalDegree := by rwa [complexify_totalDegree]
  obtain ⟨hc,hcard⟩ := exceptional_abscissae_bound (complexify Q) hQ hd hnd
  obtain ⟨hf,hpre⟩ := finite_real_preimage (exceptionalAbscissae (complexify Q)) hc
  change (realExceptionalAbscissae Q).Finite at hf
  refine ⟨hf.toFinset,?_,?_⟩
  · rw [← ncard_eq_toFinset_card _ hf]
    exact hpre.trans (by simpa only [complexify_totalDegree] using hcard)
  · intro x hx y hz
    have hn : x ∉ realExceptionalAbscissae Q := fun h => hx (hf.mem_toFinset.mpr h)
    refine ⟨?_,?_,?_⟩
    · exact fun h => hn (mem_realExceptionalAbscissae Q x y hz (Or.inl h))
    · exact fun h => hn (mem_realExceptionalAbscissae Q x y hz (Or.inr (Or.inl h)))
    · exact fun h => hn (mem_realExceptionalAbscissae Q x y hz (Or.inr (Or.inr h)))

theorem exists_bad_abscissae (Q : MV ℝ) (hQ : Irreducible (complexify Q))
    (hdeg : 1 < Q.totalDegree) :
    ∃ B : Finset ℝ, B.card ≤ 10*Q.totalDegree^2 ∧
      ∀ x ∉ B, ∀ y : ℝ, peval Q x y = 0 →
        peval (partialX Q) x y ≠ 0 ∧ peval (partialY Q) x y ≠ 0 ∧
          peval (inflectionPolynomial Q) x y ≠ 0 := by
  by_cases hdiv : complexify Q ∣ inflection (complexify Q)
  · obtain ⟨B,hB,hzero⟩ := divisible_critical_marks Q hQ hdeg hdiv
    exact ⟨B,hB.trans (Nat.mul_le_mul_right _ (by omega)),
      fun x hx y hy => (hzero x hx y hy).elim⟩
  · exact nondivisible_exceptional_marks Q hQ hdeg hdiv

end ErdosAlgebraicCurve

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_ComplexSquareScaling
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped ComplexConjugate
namespace ErdosComplexCurveFactors
open ErdosCriticalGeometry

theorem coeff_conjugate (F : MV ℂ) (m : Fin 2 →₀ ℕ) :
    (conjugate F).coeff m = conj (F.coeff m) := MvPolynomial.coeff_map _ _ _

theorem conjugate_irreducible {F : MV ℂ} (hF : Irreducible F) : Irreducible (conjugate F) :=
  (MulEquiv.irreducible_iff conjugateEquiv.toMulEquiv).mpr hF

theorem conjugate_totalDegree (F : MV ℂ) : (conjugate F).totalDegree = F.totalDegree := by
  unfold conjugate MvPolynomial.totalDegree
  rw [MvPolynomial.support_map_of_injective F Complex.conjAe.injective]

theorem eval_conjugate_real (F : MV ℂ) (x y : ℝ) :
    MvPolynomial.eval ![(x : ℂ),(y : ℂ)] (conjugate F) =
      conj (MvPolynomial.eval ![(x : ℂ),(y : ℂ)] F) := by
  have he : (starRingEnd ℂ) ∘ (![(x : ℂ),(y : ℂ)] : Fin 2 → ℂ) = ![(x : ℂ),(y : ℂ)] := by
    funext i
    fin_cases i <;> simp
  have h := MvPolynomial.map_eval (starRingEnd ℂ) ![(x : ℂ),(y : ℂ)] F
  rw [he] at h
  exact h.symm

end ErdosComplexCurveFactors

end

section

open Set
namespace ErdosAlgebraicCurve
open ErdosCriticalGeometry ErdosImplicitCurvature ErdosLocalFiberGraphs ErdosMarkedStrips

theorem exists_algebraic_marks (Q : MV ℝ) (hQ : Irreducible (complexify Q))
    (hdeg : 1 < Q.totalDegree) (S : ℝ) :
    ∃ E : Finset ℝ, 0 ∈ E ∧ S ∈ E ∧ E.card ≤ 14*Q.totalDegree^2 ∧
      (∀ t ∈ E, verticalPolynomial Q t ≠ 0) ∧ RegularOff Q S E := by
  classical
  obtain ⟨B,hB,hbad⟩ := exists_bad_abscissae Q hQ hdeg
  obtain ⟨hf0,hc0⟩ := boundary_abscissae_bound Q hQ hdeg 0
  obtain ⟨hfS,hcS⟩ := boundary_abscissae_bound Q hQ hdeg S
  let E := B ∪ hf0.toFinset ∪ hfS.toFinset ∪ {0,S}
  have hBE : B ⊆ E := fun x hx => Finset.mem_union_left _
    (Finset.mem_union_left _ (Finset.mem_union_left _ hx))
  have h0E : hf0.toFinset ⊆ E := fun x hx => Finset.mem_union_left _
    (Finset.mem_union_left _ (Finset.mem_union_right _ hx))
  have hSE : hfS.toFinset ⊆ E := fun x hx => Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  have hsize : E.card ≤ B.card+hf0.toFinset.card+hfS.toFinset.card+2 := by
    calc
      _ ≤ (B ∪ hf0.toFinset ∪ hfS.toFinset).card+({0,S} : Finset ℝ).card := Finset.card_union_le _ _
      _ ≤ ((B ∪ hf0.toFinset).card+hfS.toFinset.card)+2 :=
        Nat.add_le_add (Finset.card_union_le _ _) (Finset.card_le_two)
      _ ≤ _ := Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _
  have h0card : hf0.toFinset.card ≤ 2*Q.totalDegree := by rwa [← ncard_eq_toFinset_card _ hf0]
  have hScard : hfS.toFinset.card ≤ 2*Q.totalDegree := by rwa [← ncard_eq_toFinset_card _ hfS]
  refine ⟨E,?_,?_,?_,(fun t _ => real_vertical_nonzero Q hQ hdeg t),?_⟩
  · exact Finset.mem_union_right _ (by simp)
  · exact Finset.mem_union_right _ (by simp)
  · have hn : 10*Q.totalDegree^2+4*Q.totalDegree+2 ≤ 14*Q.totalDegree^2 := by nlinarith
    omega
  · intro t ht
    have hnotB : t ∉ B := fun h => ht (hBE h)
    refine ⟨⟨?_,?_⟩,?_⟩
    · exact fun hz => ht (h0E (hf0.mem_toFinset.mpr hz))
    · exact fun hz => ht (hSE (hfS.mem_toFinset.mpr hz))
    · exact fun y _ hy => hbad t hnotB y hy

end ErdosAlgebraicCurve

end

section

namespace ErdosAlgebraicCurve
open ErdosCriticalGeometry ErdosImplicitCurvature ErdosMarkedStrips

theorem absolutely_irreducible_curve_lattice_bound (Q : MV ℝ)
    (hQ : Irreducible (complexify Q)) (hdeg : 1 < Q.totalDegree)
    (S : ℝ) (hS : 0 ≤ S) :
    ((polynomialSquarePoints Q S).card : ℝ) ≤
      182*(Q.totalDegree : ℝ)^3*(1+S^((2 : ℝ)/3)) := by
  obtain ⟨E,h0,hSE,hcard,hfiber,hregular⟩ := exists_algebraic_marks Q hQ hdeg S
  have h := marked_square_cubic_bound Q S E 14 hS h0 hSE hfiber hregular hcard
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h]

end ErdosAlgebraicCurve

end

section

open Set
namespace ErdosComplexCurveFactors
open ErdosCriticalGeometry ErdosImplicitCurvature ErdosDivisibleInflection ErdosMarkedStrips ErdosConvexGraph
attribute [local instance] Classical.propDecidable

theorem mem_complexSquarePoints (F : MV ℂ) (S : ℝ) (p : ℤ × ℤ) :
    p ∈ complexSquarePoints F S ↔ InSquare S p ∧
      MvPolynomial.eval ![(p.1 : ℂ),(p.2 : ℂ)] F = 0 := by
  simp only [complexSquarePoints,InSquare,Finset.mem_filter,Finset.product_eq_sprod,
    Finset.mem_product,Finset.mem_Icc,Int.le_floor,Int.cast_nonneg_iff]

theorem scalar_totalDegree (a : ℂ) (ha : a ≠ 0) (F : MV ℂ) :
    (MvPolynomial.C a * F).totalDegree = F.totalDegree := by
  have hs : (MvPolynomial.C a * F).support = F.support := by
    ext m
    simp only [MvPolynomial.mem_support_iff,MvPolynomial.coeff_C_mul,mul_ne_zero_iff]
    exact ⟨fun h => h.2,fun h => ⟨ha,h⟩⟩
  unfold MvPolynomial.totalDegree
  rw [hs]

theorem complexSquare_scalar (a : ℂ) (ha : a ≠ 0) (F : MV ℂ) (S : ℝ) :
    complexSquarePoints (MvPolynomial.C a * F) S = complexSquarePoints F S := by
  ext p
  simp only [mem_complexSquarePoints,map_mul,MvPolynomial.eval_C,mul_eq_zero,ha,false_or]

theorem eval_complexify_int (R : MV ℝ) (p : ℤ × ℤ) :
    MvPolynomial.eval ![(p.1 : ℂ),(p.2 : ℂ)] (complexify R) = (peval R p.1 p.2 : ℂ) := by
  simpa only [Complex.ofReal_intCast,peval_eq_eval_pair] using complexify_eval R p.1 p.2

theorem complexSquare_complexify (R : MV ℝ) (S : ℝ) :
    complexSquarePoints (complexify R) S = polynomialSquarePoints R S := by
  ext p
  simp only [mem_complexSquarePoints,mem_polynomialSquarePoints,eval_complexify_int,Complex.ofReal_eq_zero]

theorem scalar_irreducible_iff (a : ℂ) (ha : a ≠ 0) (F : MV ℂ) :
    Irreducible (MvPolynomial.C a * F) ↔ Irreducible F :=
  irreducible_isUnit_mul ((isUnit_iff_ne_zero.mpr ha).map MvPolynomial.C)

theorem complexIntPoint_injective : Function.Injective complexIntPoint := by
  intro p q hpq
  have h1 : (p.1 : ℂ) = (q.1 : ℂ) := congrArg Prod.fst hpq
  have h2 : (p.2 : ℂ) = (q.2 : ℂ) := congrArg Prod.snd hpq
  exact Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2)

end ErdosComplexCurveFactors

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_RealCoefficientNormalization
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped ComplexConjugate
namespace ErdosComplexCurveFactors
open ErdosCriticalGeometry

theorem coeff_realCoefficients (F : MV ℂ) (m : Fin 2 →₀ ℕ) :
    (realCoefficients F).coeff m = (F.coeff m).re := rfl

theorem complexify_realCoefficients (F : MV ℂ) (hF : conjugate F = F) :
    complexify (realCoefficients F) = F := by
  ext m
  change (MvPolynomial.map (algebraMap ℝ ℂ) (realCoefficients F)).coeff m = F.coeff m
  rw [MvPolynomial.coeff_map,coeff_realCoefficients]
  apply Complex.conj_eq_iff_re.mp
  have h := congrArg (fun P : MV ℂ => P.coeff m) hF
  simpa only [coeff_conjugate] using h

theorem normalized_conjugate_eq (F : MV ℂ) (c : ℂ) (hc : c ≠ 0)
    (hrel : conjugate F = MvPolynomial.C c * F) (m : Fin 2 →₀ ℕ)
    (hm : F.coeff m ≠ 0) :
    conjugate (MvPolynomial.C (F.coeff m)⁻¹ * F) = MvPolynomial.C (F.coeff m)⁻¹ * F := by
  have hcoeff (k : Fin 2 →₀ ℕ) : conj (F.coeff k) = c*F.coeff k := by
    have h := congrArg (fun P : MV ℂ => P.coeff k) hrel
    simpa only [coeff_conjugate,MvPolynomial.coeff_C_mul] using h
  ext k
  simp only [coeff_conjugate,MvPolynomial.coeff_C_mul,map_mul,map_inv₀,hcoeff]
  field_simp [hc,hm]

theorem realScalable_of_dvd_conjugate (F : MV ℂ) (hF : Irreducible F)
    (hdiv : F ∣ conjugate F) : RealScalable F := by
  obtain ⟨H,hH⟩ := hdiv
  have hu : IsUnit H := ((conjugate_irreducible hF).2 hH).resolve_left hF.not_isUnit
  obtain ⟨c,hc,hC⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hu
  have hc0 : c ≠ 0 := hc.ne_zero
  have hrel : conjugate F = MvPolynomial.C c * F := by rw [hH,hC,mul_comm]
  obtain ⟨m,hm⟩ := MvPolynomial.exists_coeff_ne_zero hF.ne_zero
  let N := MvPolynomial.C (F.coeff m)⁻¹ * F
  have hN : conjugate N = N := normalized_conjugate_eq F c hc0 hrel m hm
  have hR : complexify (realCoefficients N) = N := complexify_realCoefficients N hN
  refine ⟨F.coeff m,hm,realCoefficients N,?_⟩
  rw [hR]
  change F = MvPolynomial.C (F.coeff m) * (MvPolynomial.C (F.coeff m)⁻¹ * F)
  rw [← mul_assoc,← map_mul,mul_inv_cancel₀ hm,map_one,one_mul]

theorem nonreal_not_dvd_conjugate (F : MV ℂ) (hF : Irreducible F)
    (hreal : ¬RealScalable F) : ¬F ∣ conjugate F :=
  fun h => hreal (realScalable_of_dvd_conjugate F hF h)

end ErdosComplexCurveFactors

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_BivariateMonomialIndex
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosAuxiliaryPolynomial

theorem monomialIndex_card (D : ℕ) : Fintype.card (MonomialIndex D) = (D+2).choose 2 := by
  simp only [MonomialIndex,Fintype.card_sigma,Fintype.card_fin]
  change (∑ i : Fin (D+1), (fun n : ℕ => n+1) i.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => n+1) (D+1)]
  simpa only [Nat.choose_one_right,Nat.add_assoc] using Nat.sum_range_add_choose D 1

theorem exponent_zero {D : ℕ} (i : MonomialIndex D) : exponent i 0 = i.2.val := by simp [exponent]

theorem exponent_one {D : ℕ} (i : MonomialIndex D) : exponent i 1 = i.1.val-i.2.val := by simp [exponent]

theorem exponent_injective (D : ℕ) : Function.Injective (@exponent D) := by
  rintro ⟨k,j⟩ ⟨l,h⟩ he
  have hx := congrArg (fun e : Fin 2 →₀ ℕ => e 0) he
  have hy := congrArg (fun e : Fin 2 →₀ ℕ => e 1) he
  simp only [exponent_zero,exponent_one] at hx hy
  have hj := j.isLt
  have hh := h.isLt
  have hkl : k = l := Fin.ext (by omega)
  subst l
  have hjh : j = h := Fin.ext hx
  subst h
  rfl

end ErdosAuxiliaryPolynomial

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_CoefficientHeightChoice
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosAuxiliaryPolynomial

theorem boxHeight_pos {M N : ℕ} (hM : 0 < M) : 0 < boxHeight M N := by
  apply Nat.ceil_pos.mpr
  exact Real.rpow_pos_of_pos (by exact_mod_cast hM) _

theorem boxHeight_card_strict {M N : ℕ} (hN : 0 < N) : M < (boxHeight M N+1)^N := by
  have hle : (M : ℝ)^((N : ℝ)⁻¹) ≤ (boxHeight M N : ℝ) := Nat.le_ceil _
  have hlt : (M : ℝ)^((N : ℝ)⁻¹) < (boxHeight M N : ℝ)+1 := by linarith
  have h := (Real.rpow_inv_lt_iff_of_pos (Nat.cast_nonneg M)
    (by positivity : (0 : ℝ) ≤ (boxHeight M N : ℝ)+1)
    (by exact_mod_cast hN : (0 : ℝ) < (N : ℝ))).mp hlt
  rw [Real.rpow_natCast] at h
  exact_mod_cast h

theorem boxHeight_le_twice_root {M N : ℕ} (hM : 0 < M) :
    (boxHeight M N : ℝ) ≤ 2*(M : ℝ)^((N : ℝ)⁻¹) := by
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hM)
  have hroot : (1 : ℝ) ≤ (M : ℝ)^((N : ℝ)⁻¹) := Real.one_le_rpow hM1 (by positivity)
  have hc := Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg M) (N : ℝ)⁻¹)
  change (boxHeight M N : ℝ) < (M : ℝ)^((N : ℝ)⁻¹)+1 at hc
  linarith

theorem boxHeight_log_bound {M N : ℕ} (hM : 0 < M) (_hN : 0 < N) :
    Real.log (2*(boxHeight M N : ℝ)) ≤ Real.log 4+Real.log (M : ℝ)/(N : ℝ) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hH : (0 : ℝ) < (boxHeight M N : ℝ) := by exact_mod_cast boxHeight_pos (N := N) hM
  have hr : (0 : ℝ) < (M : ℝ)^((N : ℝ)⁻¹) := Real.rpow_pos_of_pos hM0 _
  have hb := boxHeight_le_twice_root (N := N) hM
  calc
    _ ≤ Real.log (4*((M : ℝ)^((N : ℝ)⁻¹))) :=
      Real.log_le_log (by positivity) (by linarith)
    _ = Real.log 4+Real.log ((M : ℝ)^((N : ℝ)⁻¹)) := Real.log_mul (by norm_num) hr.ne'
    _ = Real.log 4+Real.log (M : ℝ)/(N : ℝ) := by rw [Real.log_rpow hM0]; ring

end ErdosAuxiliaryPolynomial

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeBinCounting
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosInversePrimeBin

theorem primeBin_log_sum {R xi : ℝ} (hR : 0 ≤ R) (hxi : 0 ≤ xi) :
    (∑ p ∈ primeBin R xi,Real.log p) = Chebyshev.theta ((1+xi)*R)-Chebyshev.theta R := by
  have hsub : Nat.primesLE ⌊R⌋₊ ⊆ Nat.primesLE ⌊(1+xi)*R⌋₊ := by
    intro p hp
    obtain ⟨hle,hprime⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hle.trans (Nat.floor_mono (by nlinarith)),hprime⟩
  rw [Chebyshev.theta_eq_sum_primesLE,Chebyshev.theta_eq_sum_primesLE]
  simpa only [primeBin] using (Finset.sum_sdiff_eq_sub (f := fun p : ℕ => Real.log p) hsub)

theorem primeBin_log_sum_upper {R xi : ℝ} (hR : 2 ≤ R) (hxi : 0 ≤ xi) (hxi1 : xi ≤ 1) :
    (∑ p ∈ primeBin R xi,Real.log p) ≤ (primeBin R xi).card*(2*Real.log R) := by
  have hR0 : 0 < R := by linarith
  have hupper : (1+xi)*R ≤ R^2 := by nlinarith
  have hb0 : 0 < (1+xi)*R := by positivity
  have hlog : Real.log ((1+xi)*R) ≤ 2*Real.log R := by
    have h := Real.log_le_log hb0 hupper
    simpa only [Real.log_pow,Nat.cast_ofNat] using h
  calc
    _ ≤ ∑ _p ∈ primeBin R xi,2*Real.log R := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hprime,_,hhi⟩ := (mem_primeBin hR0.le hxi p).mp hp
      exact (Real.log_le_log (by exact_mod_cast hprime.pos) hhi).trans hlog
    _ = _ := by simp

end ErdosInversePrimeBin

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_HighPrimeRemoval
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace ErdosInversePrimeBin
open _root_.Filter _root_.Asymptotics
open scoped Topology
open ErdosPrimeInputs.StrongChebyshev ErdosPrimeInputs.PrimeErrorDecay

theorem prime_bin_theta_error : ∃ c C R₀ : ℝ,0 < c ∧ 0 < C ∧ 2 ≤ R₀ ∧
    ∀ R : ℝ,R₀ ≤ R → ∀ xi : ℝ,0 ≤ xi → xi ≤ 1 →
      |Chebyshev.theta ((1+xi)*R)-Chebyshev.theta R-xi*R| ≤ 3*C*R*decay c R := by
  obtain ⟨c,hc,hstrong⟩ := theta_strong
  obtain ⟨C,hC,hbig⟩ := hstrong.exists_pos
  obtain ⟨A,hA⟩ := eventually_atTop.mp hbig.bound
  refine ⟨c,C,max A 2,hc,hC,le_max_right _ _,?_⟩
  intro R hR xi hxi hxi1
  have hR2 : 2 ≤ R := (le_max_right _ _).trans hR
  have hR0 : 0 < R := by linarith
  have hRA : A ≤ R := (le_max_left _ _).trans hR
  have hbR : R ≤ (1+xi)*R := by nlinarith
  have hb2 : (1+xi)*R ≤ 2*R := by nlinarith
  have htheta (x : ℝ) (hx : A ≤ x) (hx0 : 0 ≤ x) :
      |Chebyshev.theta x-x| ≤ C*(x*decay c x) := by
    have h := hA x hx
    simp only [Real.norm_eq_abs] at h
    rw [abs_of_nonneg (errorScale_nonneg c hx0)] at h
    exact h
  have hr := htheta R hRA hR0.le
  have hb : |Chebyshev.theta ((1+xi)*R)-(1+xi)*R| ≤ 2*C*R*decay c R := by
    calc
      _ ≤ C*(((1+xi)*R)*decay c ((1+xi)*R)) := htheta _ (hRA.trans hbR) (hR0.le.trans hbR)
      _ ≤ C*((2*R)*decay c R) := mul_le_mul_of_nonneg_left
        (mul_le_mul hb2 (decay_antitone hc.le hR0 hbR) (decay_pos _ _).le (by positivity)) hC.le
      _ = _ := by ring
  have he : Chebyshev.theta ((1+xi)*R)-Chebyshev.theta R-xi*R =
      (Chebyshev.theta ((1+xi)*R)-(1+xi)*R)-(Chebyshev.theta R-R) := by ring
  rw [he]
  exact (abs_sub _ _).trans (by nlinarith only [hb,hr])

theorem decay_tendsto_zero {c : ℝ} (hc : 0 < c) : Tendsto (decay c) atTop (𝓝 0) := by
  have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (Tendsto.const_mul_atTop hc (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [Function.comp_apply,decay,neg_mul]

theorem uniform_bin_theta_error {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ R : ℝ in atTop,2 ≤ R ∧ ∀ xi : ℝ,eta ≤ xi → xi ≤ 1 →
      |Chebyshev.theta ((1+xi)*R)-Chebyshev.theta R-xi*R| ≤ xi*R/2 := by
  obtain ⟨c,C,R₀,hc,hC,hR₀,hbound⟩ := prime_bin_theta_error
  have hdec : Tendsto (fun R : ℝ => 3*C*decay c R) atTop (𝓝 0) := by
    simpa only [mul_zero] using (decay_tendsto_zero hc).const_mul (3*C)
  filter_upwards [eventually_ge_atTop R₀,
    hdec.eventually (eventually_le_nhds (show 0 < eta/2 by positivity))] with R hR hd
  have hR2 := hR₀.trans hR
  refine ⟨hR2,?_⟩
  intro xi hxi hxi1
  have hxi0 : 0 ≤ xi := heta.le.trans hxi
  have he := hbound R hR xi hxi0 hxi1
  have hm := mul_le_mul_of_nonneg_right hd (show 0 ≤ R by linarith)
  have hwidth := mul_le_mul_of_nonneg_right hxi (show 0 ≤ R by linarith)
  exact he.trans (by nlinarith only [hm,hwidth])

end ErdosInversePrimeBin



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_ComplexComponentBound
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set
open scoped ComplexConjugate
namespace ErdosComplexCurveFactors
open ErdosCriticalGeometry ErdosImplicitCurvature ErdosAlgebraicCurve ErdosMarkedStrips

theorem nonreal_component_card_bound (F : MV ℂ) (hF : Irreducible F)
    (hdeg : 1 < F.totalDegree) (hreal : ¬RealScalable F) (S : ℝ) :
    (complexSquarePoints F S).card ≤ 2*F.totalDegree^3 := by
  have hnd := nonreal_not_dvd_conjugate F hF hreal
  obtain ⟨hfinite,hcard⟩ := irreducible_intersection_bound F (conjugate F) hF hdeg hnd
  have hmap : ∀ p ∈ (complexSquarePoints F S : Set (ℤ × ℤ)),
      complexIntPoint p ∈ intersectionPoints F (conjugate F) := by
    intro p hp
    have hz := ((mem_complexSquarePoints F S p).mp hp).2
    change MvPolynomial.eval ![(p.1 : ℂ),(p.2 : ℂ)] F = 0 ∧
      MvPolynomial.eval ![(p.1 : ℂ),(p.2 : ℂ)] (conjugate F) = 0
    refine ⟨hz,?_⟩
    simpa only [Complex.ofReal_intCast,hz,map_zero] using eval_conjugate_real F p.1 p.2
  have hc := ncard_le_ncard_of_injOn complexIntPoint hmap complexIntPoint_injective.injOn hfinite
  simp only [ncard_coe_finset] at hc
  calc
    _ ≤ _ := hc
    _ ≤ _ := hcard
    _ = 2*F.totalDegree^3 := by rw [conjugate_totalDegree]; ring

theorem realScalable_component_bound (F : MV ℂ) (hF : Irreducible F)
    (hdeg : 1 < F.totalDegree) (hreal : RealScalable F) (S : ℝ) (hS : 0 ≤ S) :
    ((complexSquarePoints F S).card : ℝ) ≤
      182*(F.totalDegree : ℝ)^3*(1+S^((2 : ℝ)/3)) := by
  obtain ⟨a,ha,R,rfl⟩ := hreal
  have hR := (scalar_irreducible_iff a ha (complexify R)).mp hF
  have hd : 1 < R.totalDegree := by
    simpa only [scalar_totalDegree a ha,complexify_totalDegree] using hdeg
  simpa only [complexSquare_scalar a ha,complexSquare_complexify,scalar_totalDegree a ha,
    complexify_totalDegree] using absolutely_irreducible_curve_lattice_bound R hR hd S hS

theorem irreducible_complex_curve_bound (F : MV ℂ) (hF : Irreducible F)
    (hdeg : 1 < F.totalDegree) (S : ℝ) (hS : 0 ≤ S) :
    ((complexSquarePoints F S).card : ℝ) ≤
      182*(F.totalDegree : ℝ)^3*(1+S^((2 : ℝ)/3)) := by
  by_cases hreal : RealScalable F
  · exact realScalable_component_bound F hF hdeg hreal S hS
  · have h := nonreal_component_card_bound F hF hdeg hreal S
    have hB : 1 ≤ 1+S^((2 : ℝ)/3) := le_add_of_nonneg_right (Real.rpow_nonneg hS _)
    calc
      ((complexSquarePoints F S).card : ℝ) ≤ 2*(F.totalDegree : ℝ)^3 := by exact_mod_cast h
      _ ≤ 182*(F.totalDegree : ℝ)^3 := by gcongr; norm_num
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hB

end ErdosComplexCurveFactors

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_RichLinearFactor
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open UniqueFactorizationMonoid
namespace ErdosComplexCurveFactors
open ErdosCriticalGeometry

attribute [local instance] complexPolynomialNormalization

theorem associated_constant {F G : MV ℂ} (h : Associated F G) :
    ∃ a : ℂ, a ≠ 0 ∧ G = MvPolynomial.C a * F := by
  obtain ⟨u,hu⟩ := h
  obtain ⟨a,ha,hua⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp u.isUnit
  exact ⟨a,ha.ne_zero,by rw [← hu,hua,mul_comm]⟩

theorem associated_totalDegree {F G : MV ℂ} (h : Associated F G) : F.totalDegree = G.totalDegree := by
  obtain ⟨a,ha,rfl⟩ := associated_constant h
  exact (scalar_totalDegree a ha F).symm

theorem associated_squarePoints {F G : MV ℂ} (h : Associated F G) (S : ℝ) :
    complexSquarePoints F S = complexSquarePoints G S := by
  obtain ⟨a,ha,rfl⟩ := associated_constant h
  exact (complexSquare_scalar a ha F S).symm

theorem irreducible_totalDegree_pos {F : MV ℂ} (hF : Irreducible F) : 0 < F.totalDegree := by
  apply Nat.pos_of_ne_zero
  intro hd
  have he := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hd
  have hc : F.coeff 0 ≠ 0 := by
    intro hc
    apply hF.ne_zero
    rw [he,hc,map_zero]
  apply hF.not_isUnit
  rw [he]
  exact (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C

theorem totalDegree_multiset_prod (s : Multiset (MV ℂ)) (hs : ∀ F ∈ s, F ≠ 0) :
    s.prod.totalDegree = (s.map MvPolynomial.totalDegree).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons F s ih =>
      have hF := hs F (Multiset.mem_cons_self _ _)
      have hrest : ∀ G ∈ s, G ≠ 0 := fun G hG => hs G (Multiset.mem_cons_of_mem hG)
      have hprod : s.prod ≠ 0 := Multiset.prod_ne_zero (fun h => hrest 0 h rfl)
      rw [Multiset.prod_cons,MvPolynomial.totalDegree_mul_of_isDomain hF hprod,
        Multiset.map_cons,Multiset.sum_cons,ih hrest]

theorem multiset_card_le_degree_sum (s : Multiset (MV ℂ)) (hs : ∀ F ∈ s, Irreducible F) :
    s.card ≤ (s.map MvPolynomial.totalDegree).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons F s ih =>
      have hF := irreducible_totalDegree_pos (hs F (Multiset.mem_cons_self _ _))
      have hrest := ih (fun G hG => hs G (Multiset.mem_cons_of_mem hG))
      simp only [Multiset.card_cons,Multiset.map_cons,Multiset.sum_cons]
      omega

theorem normalizedFactors_card_le_degree (P : MV ℂ) (hP : P ≠ 0) :
    (normalizedFactors P).card ≤ P.totalDegree := by
  have hirr := irreducible_of_normalized_factor (a := P)
  have hsum := totalDegree_multiset_prod (normalizedFactors P) (fun F hF => (hirr F hF).ne_zero)
  have hassoc := associated_totalDegree (prod_normalizedFactors hP)
  rw [hsum] at hassoc
  exact (multiset_card_le_degree_sum (normalizedFactors P) hirr).trans hassoc.le

theorem mem_nonlinearFactors (P F : MV ℂ) :
    F ∈ nonlinearFactors P ↔ F ∈ normalizedFactors P ∧ 1 < F.totalDegree := by
  classical
  simp only [nonlinearFactors,Finset.mem_filter,Multiset.mem_toFinset]

theorem nonlinearFactors_card_le_degree (P : MV ℂ) (hP : P ≠ 0) :
    (nonlinearFactors P).card ≤ P.totalDegree := by
  classical
  exact (Finset.card_filter_le _ _).trans
    ((Multiset.toFinset_card_le _).trans (normalizedFactors_card_le_degree P hP))

theorem nonlinearFactor_degree_le {P F : MV ℂ} (hP : P ≠ 0) (hF : F ∈ nonlinearFactors P) :
    F.totalDegree ≤ P.totalDegree :=
  MvPolynomial.totalDegree_le_of_dvd_of_isDomain
    (dvd_of_mem_normalizedFactors ((mem_nonlinearFactors P F).mp hF).1) hP

end ErdosComplexCurveFactors

end

section

open Set UniqueFactorizationMonoid
namespace ErdosComplexCurveFactors
attribute [local instance] complexPolynomialNormalization
open ErdosCriticalGeometry ErdosConvexGraph
attribute [local instance] Classical.propDecidable

theorem mem_nonlinearSquarePoints (P : MV ℂ) (S : ℝ) (p : ℤ × ℤ) :
    p ∈ nonlinearSquarePoints P S ↔ InSquare S p ∧ OnNonlinearComponent P p := by
  simp only [nonlinearSquarePoints,InSquare,Finset.mem_filter,Finset.product_eq_sprod,
    Finset.mem_product,Finset.mem_Icc,Int.le_floor,Int.cast_nonneg_iff]

theorem nonlinearSquare_eq_union (P : MV ℂ) (hP : P ≠ 0) (S : ℝ) :
    nonlinearSquarePoints P S = (nonlinearFactors P).biUnion (fun F => complexSquarePoints F S) := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨hs,F,hF,hdiv,hdeg,hzero⟩ := (mem_nonlinearSquarePoints P S p).mp hp
    obtain ⟨G,hG,hFG⟩ := exists_mem_normalizedFactors_of_dvd hP hF hdiv
    have hGdeg : 1 < G.totalDegree := by rwa [← associated_totalDegree hFG]
    have hpG : p ∈ complexSquarePoints G S := by
      rw [← associated_squarePoints hFG S]
      exact (mem_complexSquarePoints F S p).mpr ⟨hs,hzero⟩
    exact Finset.mem_biUnion.mpr ⟨G,(mem_nonlinearFactors P G).mpr ⟨hG,hGdeg⟩,hpG⟩
  · intro hp
    obtain ⟨F,hF,hpF⟩ := Finset.mem_biUnion.mp hp
    have hnorm := (mem_nonlinearFactors P F).mp hF
    have hpoint := (mem_complexSquarePoints F S p).mp hpF
    exact (mem_nonlinearSquarePoints P S p).mpr
      ⟨hpoint.1,F,irreducible_of_normalized_factor F hnorm.1,
        dvd_of_mem_normalizedFactors hnorm.1,hnorm.2,hpoint.2⟩

end ErdosComplexCurveFactors

end

section

open Set UniqueFactorizationMonoid
namespace ErdosComplexCurveFactors
attribute [local instance] complexPolynomialNormalization
open ErdosCriticalGeometry

theorem nonlinear_square_degree_four_bound (P : MV ℂ) (hP : P ≠ 0) (S : ℝ) (hS : 0 ≤ S) :
    ((nonlinearSquarePoints P S).card : ℝ) ≤
      182*(P.totalDegree : ℝ)^4*(1+S^((2 : ℝ)/3)) := by
  classical
  have hbound (F : MV ℂ) (hF : F ∈ nonlinearFactors P) :
      ((complexSquarePoints F S).card : ℝ) ≤
        182*(P.totalDegree : ℝ)^3*(1+S^((2 : ℝ)/3)) := by
    have hm := (mem_nonlinearFactors P F).mp hF
    calc
      _ ≤ 182*(F.totalDegree : ℝ)^3*(1+S^((2 : ℝ)/3)) :=
        irreducible_complex_curve_bound F (irreducible_of_normalized_factor F hm.1) hm.2 S hS
      _ ≤ _ := by
        gcongr
        exact_mod_cast nonlinearFactor_degree_le hP hF
  have hc : (nonlinearSquarePoints P S).card ≤
      ∑ F ∈ nonlinearFactors P, (complexSquarePoints F S).card := by
    rw [nonlinearSquare_eq_union P hP S]
    exact Finset.card_biUnion_le
  calc
    ((nonlinearSquarePoints P S).card : ℝ) ≤
        ∑ F ∈ nonlinearFactors P, ((complexSquarePoints F S).card : ℝ) := by exact_mod_cast hc
    _ ≤ ∑ _F ∈ nonlinearFactors P, 182*(P.totalDegree : ℝ)^3*(1+S^((2 : ℝ)/3)) :=
      Finset.sum_le_sum hbound
    _ = ((nonlinearFactors P).card : ℝ)*(182*(P.totalDegree : ℝ)^3*(1+S^((2 : ℝ)/3))) := by simp
    _ ≤ (P.totalDegree : ℝ)*(182*(P.totalDegree : ℝ)^3*(1+S^((2 : ℝ)/3))) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast nonlinearFactors_card_le_degree P hP) (by positivity)
    _ = 182*(P.totalDegree : ℝ)^4*(1+S^((2 : ℝ)/3)) := by ring

theorem nonlinear_square_bound_of_degree_le (P : MV ℂ) (hP : P ≠ 0) (D : ℕ)
    (hD : P.totalDegree ≤ D) (S : ℝ) (hS : 0 ≤ S) :
    ((nonlinearSquarePoints P S).card : ℝ) ≤ 182*(D : ℝ)^4*(1+S^((2 : ℝ)/3)) := by
  apply (nonlinear_square_degree_four_bound P hP S hS).trans
  gcongr

end ErdosComplexCurveFactors

end

section

open UniqueFactorizationMonoid
namespace ErdosRichLine
open ErdosCriticalGeometry ErdosComplexCurveFactors ErdosConvexGraph
attribute [local instance] complexPolynomialNormalization

theorem mem_linearFactors (P F : MV ℂ) :
    F ∈ linearFactors P ↔ F ∈ normalizedFactors P ∧ F.totalDegree = 1 := by
  classical
  simp only [linearFactors,Finset.mem_filter,Multiset.mem_toFinset]

theorem linearFactors_card_le_degree (P : MV ℂ) (hP : P ≠ 0) :
    (linearFactors P).card ≤ P.totalDegree := by
  classical
  exact (Finset.card_filter_le _ _).trans
    ((Multiset.toFinset_card_le _).trans (normalizedFactors_card_le_degree P hP))

theorem zero_mem_normalized_factor (P : MV ℂ) (hP : P ≠ 0) (p : ℤ × ℤ)
    (hp : MvPolynomial.eval ![(p.1 : ℂ),(p.2 : ℂ)] P = 0) :
    ∃ F ∈ normalizedFactors P, MvPolynomial.eval ![(p.1 : ℂ),(p.2 : ℂ)] F = 0 := by
  classical
  let ev := MvPolynomial.eval ![(p.1 : ℂ),(p.2 : ℂ)]
  obtain ⟨a,ha,hprod⟩ := associated_constant (prod_normalizedFactors hP)
  have hz : ev (normalizedFactors P).prod = 0 := by
    have h := hp
    rw [hprod,map_mul,MvPolynomial.eval_C] at h
    exact (mul_eq_zero.mp h).resolve_left ha
  rw [map_multiset_prod] at hz
  obtain ⟨F,hF,hzF⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hz)
  exact ⟨F,hF,hzF⟩

theorem square_zero_cover (P : MV ℂ) (hP : P ≠ 0) (S : ℝ) :
    complexSquarePoints P S ⊆ nonlinearSquarePoints P S ∪
      (linearFactors P).biUnion (fun F => complexSquarePoints F S) := by
  classical
  intro p hp
  obtain ⟨hs,hzero⟩ := (mem_complexSquarePoints P S p).mp hp
  obtain ⟨F,hF,hzF⟩ := zero_mem_normalized_factor P hP p hzero
  have hirr := irreducible_of_normalized_factor F hF
  have hpos := irreducible_totalDegree_pos hirr
  by_cases hdeg : F.totalDegree = 1
  · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨F,(mem_linearFactors P F).mpr ⟨hF,hdeg⟩,
        (mem_complexSquarePoints F S p).mpr ⟨hs,hzF⟩⟩)
  · exact Finset.mem_union_left _ ((mem_nonlinearSquarePoints P S p).mpr
      ⟨hs,F,hirr,dvd_of_mem_normalizedFactors hF,by omega,hzF⟩)

end ErdosRichLine

end

section

namespace ErdosRichLine
open ErdosCriticalGeometry ErdosComplexCurveFactors
attribute [local instance] complexPolynomialNormalization

theorem selected_point_cover (P : MV ℂ) (hP : P ≠ 0) (S : ℝ) (X : Finset (ℤ × ℤ))
    (hX : X ⊆ complexSquarePoints P S) :
    X ⊆ nonlinearSquarePoints P S ∪
      (linearFactors P).biUnion (fun F => X ∩ complexSquarePoints F S) := by
  classical
  intro p hp
  rcases Finset.mem_union.mp (square_zero_cover P hP S (hX hp)) with hn | hl
  · exact Finset.mem_union_left _ hn
  · obtain ⟨F,hF,hpF⟩ := Finset.mem_biUnion.mp hl
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨F,hF,Finset.mem_inter.mpr ⟨hp,hpF⟩⟩)

theorem selected_count_bound (P : MV ℂ) (hP : P ≠ 0) (D : ℕ) (hD : P.totalDegree ≤ D)
    (S : ℝ) (hS : 0 ≤ S) (X : Finset (ℤ × ℤ)) (hX : X ⊆ complexSquarePoints P S)
    (M : ℝ) (hM : 0 ≤ M)
    (hsmall : ∀ F ∈ linearFactors P, ((X ∩ complexSquarePoints F S).card : ℝ) ≤ M) :
    (X.card : ℝ) ≤ 182*(D : ℝ)^4*(1+S^((2 : ℝ)/3))+(D : ℝ)*M := by
  classical
  have hc : X.card ≤ (nonlinearSquarePoints P S).card+
      ∑ F ∈ linearFactors P, (X ∩ complexSquarePoints F S).card :=
    (Finset.card_le_card (selected_point_cover P hP S X hX)).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _))
  have hlines : ((linearFactors P).card : ℝ) ≤ (D : ℝ) := by
    exact_mod_cast (linearFactors_card_le_degree P hP).trans hD
  calc
    (X.card : ℝ) ≤ ((nonlinearSquarePoints P S).card : ℝ)+
        ∑ F ∈ linearFactors P, ((X ∩ complexSquarePoints F S).card : ℝ) := by exact_mod_cast hc
    _ ≤ 182*(D : ℝ)^4*(1+S^((2 : ℝ)/3))+∑ _F ∈ linearFactors P, M :=
      add_le_add (nonlinear_square_bound_of_degree_le P hP D hD S hS) (Finset.sum_le_sum hsmall)
    _ = 182*(D : ℝ)^4*(1+S^((2 : ℝ)/3))+((linearFactors P).card : ℝ)*M := by simp
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right hlines hM)

theorem exists_rich_linear_factor (P : MV ℂ) (hP : P ≠ 0) (D : ℕ) (hD : P.totalDegree ≤ D)
    (S : ℝ) (hS : 0 ≤ S) (X : Finset (ℤ × ℤ)) (hX : X ⊆ complexSquarePoints P S)
    (M : ℝ) (hM : 0 ≤ M)
    (hlarge : 182*(D : ℝ)^4*(1+S^((2 : ℝ)/3))+(D : ℝ)*M < (X.card : ℝ)) :
    ∃ F : MV ℂ, Irreducible F ∧ F ∣ P ∧ F.totalDegree = 1 ∧
      M < ((X ∩ complexSquarePoints F S).card : ℝ) := by
  classical
  have hex : ∃ F ∈ linearFactors P, M < ((X ∩ complexSquarePoints F S).card : ℝ) := by
    by_contra h
    push Not at h
    exact (not_le_of_gt hlarge) (selected_count_bound P hP D hD S hS X hX M hM h)
  obtain ⟨F,hF,hcard⟩ := hex
  have hn := (mem_linearFactors P F).mp hF
  exact ⟨F,UniqueFactorizationMonoid.irreducible_of_normalized_factor F hn.1,
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hn.1,hn.2,hcard⟩

end ErdosRichLine

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_LinearPolynomialForm
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosRichLine
open ErdosCriticalGeometry

theorem exponent_sum_le_one_cases (m : Fin 2 →₀ ℕ) (hm : m.sum (fun _ n => n) ≤ 1) :
    m = 0 ∨ m = Finsupp.single 0 1 ∨ m = Finsupp.single 1 1 := by
  have hs : m 0+m 1 ≤ 1 := by
    have he : m.sum (fun _ n => n) = m 0+m 1 := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
      exact Fin.sum_univ_two _
    rwa [he] at hm
  by_cases h0 : m 0 = 0
  · by_cases h1 : m 1 = 0
    · left
      ext i
      fin_cases i <;> simp [h0,h1]
    · right;right
      have h1' : m 1 = 1 := by omega
      ext i
      fin_cases i <;> simp [h0,h1']
  · right;left
    have h0' : m 0 = 1 := by omega
    have h1 : m 1 = 0 := by omega
    ext i
    fin_cases i <;> simp [h0',h1]

theorem linear_polynomial_form (F : MV ℂ) (hdeg : F.totalDegree ≤ 1) :
    F = MvPolynomial.C (F.coeff 0)+
      MvPolynomial.C (F.coeff (Finsupp.single 0 1))*MvPolynomial.X 0+
      MvPolynomial.C (F.coeff (Finsupp.single 1 1))*MvPolynomial.X 1 := by
  classical
  have he0 : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ 0 := by
    intro h
    have hh := congrArg (fun m : Fin 2 →₀ ℕ => m 0) h
    simp at hh
  have he1 : (Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ 0 := by
    intro h
    have hh := congrArg (fun m : Fin 2 →₀ ℕ => m 1) h
    simp at hh
  have he01 : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := by
    intro h
    have hh := congrArg (fun m : Fin 2 →₀ ℕ => m 0) h
    simp at hh
  ext m
  by_cases hm : m.sum (fun _ n => n) ≤ 1
  · rcases exponent_sum_le_one_cases m hm with rfl | rfl | rfl <;>
      simp [MvPolynomial.coeff_C_mul,MvPolynomial.coeff_C,
        MvPolynomial.coeff_X,he0,he1,he01,Ne.symm he0,Ne.symm he1,Ne.symm he01]
  · have hm0 : m ≠ 0 := by rintro rfl; simp at hm
    have hm1 : m ≠ Finsupp.single 0 1 := by rintro rfl; simp at hm
    have hm2 : m ≠ Finsupp.single 1 1 := by rintro rfl; simp at hm
    have hc : F.coeff m = 0 := by
      by_contra hn
      exact hm ((MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hn)).trans hdeg)
    simp [MvPolynomial.coeff_C_mul,MvPolynomial.coeff_C,
      MvPolynomial.coeff_X,Ne.symm hm0,Ne.symm hm1,Ne.symm hm2,hc]

theorem linear_polynomial_eval (F : MV ℂ) (hdeg : F.totalDegree ≤ 1) (x y : ℂ) :
    MvPolynomial.eval ![x,y] F = F.coeff 0+F.coeff (Finsupp.single 0 1)*x+
      F.coeff (Finsupp.single 1 1)*y := by
  conv_lhs => rw [linear_polynomial_form F hdeg]
  simp

end ErdosRichLine

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_FactorDividesAbscissa
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosRichLine
open ErdosCriticalGeometry

theorem linear_y_coefficient_ne_zero (F : MV ℂ) (hdeg : F.totalDegree = 1)
    (p q : ℤ × ℤ) (hx : p.1 ≠ q.1)
    (hp : MvPolynomial.eval ![(p.1 : ℂ),(p.2 : ℂ)] F = 0)
    (hq : MvPolynomial.eval ![(q.1 : ℂ),(q.2 : ℂ)] F = 0) :
    F.coeff (Finsupp.single 1 1) ≠ 0 := by
  intro ha
  rw [linear_polynomial_eval F hdeg.le,ha,zero_mul,add_zero] at hp hq
  have hprod : F.coeff (Finsupp.single 0 1)*((p.1 : ℂ)-(q.1 : ℂ)) = 0 := by
    linear_combination hp-hq
  have hdx : (p.1 : ℂ)-(q.1 : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hx)
  have hb := (mul_eq_zero.mp hprod).resolve_right hdx
  have hc : F.coeff 0 = 0 := by simpa [hb] using hp
  have hF : F = 0 := by rw [linear_polynomial_form F hdeg.le,hc,hb,ha];simp
  rw [hF,MvPolynomial.totalDegree_zero] at hdeg
  contradiction

theorem linear_integer_cross_product (F : MV ℂ) (hdeg : F.totalDegree = 1)
    (p q : ℤ × ℤ) (hx : p.1 ≠ q.1)
    (hp : MvPolynomial.eval ![(p.1 : ℂ),(p.2 : ℂ)] F = 0)
    (hq : MvPolynomial.eval ![(q.1 : ℂ),(q.2 : ℂ)] F = 0)
    (r : ℤ × ℤ) (hr : MvPolynomial.eval ![(r.1 : ℂ),(r.2 : ℂ)] F = 0) :
    (q.1-p.1)*(r.2-p.2) = (q.2-p.2)*(r.1-p.1) := by
  have ha := linear_y_coefficient_ne_zero F hdeg p q hx hp hq
  rw [linear_polynomial_eval F hdeg.le] at hp hq hr
  have he : ((q.1 : ℂ)-(p.1 : ℂ))*((r.2 : ℂ)-(p.2 : ℂ)) =
      ((q.2 : ℂ)-(p.2 : ℂ))*((r.1 : ℂ)-(p.1 : ℂ)) := by
    apply mul_left_cancel₀ ha
    linear_combination ((q.1 : ℂ)-(p.1 : ℂ))*(hr-hp)-
      ((r.1 : ℂ)-(p.1 : ℂ))*(hq-hp)
  exact_mod_cast he

end ErdosRichLine

end

section

namespace ErdosRichLine
open ErdosCriticalGeometry

theorem primitive_line_from_cross_products (p q : ℤ × ℤ) (hx : p.1 ≠ q.1) :
    ∃ l : PrimitiveIntegerLine, ∀ r : ℤ × ℤ,
      (q.1-p.1)*(r.2-p.2) = (q.2-p.2)*(r.1-p.1) → l.Contains r := by
  let s : ℚ := ((q.2-p.2 : ℤ) : ℚ)/((q.1-p.1 : ℤ) : ℚ)
  let l : PrimitiveIntegerLine :=
    ⟨s.den,s.num,(s.den : ℤ)*p.2-s.num*p.1,s.den_pos,s.reduced⟩
  have hdx : q.1-p.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hdxQ : ((q.1-p.1 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hdx
  have hdQ : (s.den : ℚ) ≠ 0 := by exact_mod_cast s.den_ne_zero
  have hratio : (s.num : ℚ)/(s.den : ℚ) = ((q.2-p.2 : ℤ) : ℚ)/((q.1-p.1 : ℤ) : ℚ) :=
    s.num_div_den
  have hmulQ := (div_eq_div_iff hdQ hdxQ).mp hratio
  have hmul : s.num*(q.1-p.1) = (q.2-p.2)*(s.den : ℤ) := by exact_mod_cast hmulQ
  refine ⟨l,?_⟩
  intro r hr
  change (s.den : ℤ)*r.2 = s.num*r.1+((s.den : ℤ)*p.2-s.num*p.1)
  apply mul_left_cancel₀ hdx
  linear_combination (s.den : ℤ)*hr-(r.1-p.1)*hmul

theorem primitive_line_of_polynomial (F : MV ℂ) (hdeg : F.totalDegree = 1)
    (p q : ℤ × ℤ) (hx : p.1 ≠ q.1)
    (hp : MvPolynomial.eval ![(p.1 : ℂ),(p.2 : ℂ)] F = 0)
    (hq : MvPolynomial.eval ![(q.1 : ℂ),(q.2 : ℂ)] F = 0) :
    ∃ l : PrimitiveIntegerLine, ∀ r : ℤ × ℤ,
      MvPolynomial.eval ![(r.1 : ℂ),(r.2 : ℂ)] F = 0 → l.Contains r := by
  obtain ⟨l,hl⟩ := primitive_line_from_cross_products p q hx
  exact ⟨l,fun r hr => hl r (linear_integer_cross_product F hdeg p q hx hp hq r hr)⟩

end ErdosRichLine

end

section

namespace ErdosRichLine
open ErdosCriticalGeometry ErdosComplexCurveFactors

theorem exists_rich_primitive_line (P : MV ℂ) (hP : P ≠ 0) (D : ℕ) (hD : P.totalDegree ≤ D)
    (S : ℝ) (hS : 0 ≤ S) (X : Finset (ℤ × ℤ)) (hX : X ⊆ complexSquarePoints P S)
    (hinj : Set.InjOn Prod.fst (X : Set (ℤ × ℤ))) (M : ℝ) (hM : 1 ≤ M)
    (hlarge : 182*(D : ℝ)^4*(1+S^((2 : ℝ)/3))+(D : ℝ)*M < (X.card : ℝ)) :
    ∃ (F : MV ℂ) (l : PrimitiveIntegerLine),
      Irreducible F ∧ F ∣ P ∧ F.totalDegree = 1 ∧
      M < ((X ∩ complexSquarePoints F S).card : ℝ) ∧
      ∀ r ∈ X ∩ complexSquarePoints F S, l.Contains r := by
  classical
  obtain ⟨F,hF,hFP,hdeg,hcount⟩ := exists_rich_linear_factor P hP D hD S hS X hX M
    (le_trans zero_le_one hM) hlarge
  have htwo : 1 < (X ∩ complexSquarePoints F S).card := by exact_mod_cast lt_of_le_of_lt hM hcount
  obtain ⟨p,hp,q,hq,hpq⟩ := Finset.one_lt_card.mp htwo
  have hx : p.1 ≠ q.1 := fun he => hpq (hinj (Finset.mem_inter.mp hp).1 (Finset.mem_inter.mp hq).1 he)
  have hpz := ((mem_complexSquarePoints F S p).mp (Finset.mem_inter.mp hp).2).2
  have hqz := ((mem_complexSquarePoints F S q).mp (Finset.mem_inter.mp hq).2).2
  obtain ⟨l,hl⟩ := primitive_line_of_polynomial F hdeg p q hx hpz hqz
  refine ⟨F,l,hF,hFP,hdeg,hcount,?_⟩
  intro r hr
  exact hl r (((mem_complexSquarePoints F S r).mp (Finset.mem_inter.mp hr).2).2)

end ErdosRichLine

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeBinRationalList
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open scoped BigOperators
namespace ErdosInversePrimeBin
open _root_.Filter
open scoped Topology

theorem primeBin_log_sum_lower {R xi : ℝ} (hR : 0 < R) (hxi : 0 ≤ xi) :
    (primeBin R xi).card*Real.log R ≤ ∑ p ∈ primeBin R xi,Real.log p := by
  calc
    _ = ∑ _p ∈ primeBin R xi,Real.log R := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p hp
      exact Real.log_le_log hR ((mem_primeBin hR.le hxi p).mp hp).2.1.le

theorem uniform_prime_bin_count {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ R : ℝ in atTop,2 ≤ R ∧ ∀ xi : ℝ,eta ≤ xi → xi ≤ 1 →
      xi*R/(4*Real.log R) ≤ (primeBin R xi).card ∧
      (primeBin R xi).card ≤ 2*xi*R/Real.log R := by
  filter_upwards [uniform_bin_theta_error heta] with R hR
  refine ⟨hR.1,?_⟩
  intro xi hxi hxi1
  have hxi0 := heta.le.trans hxi
  have hR0 : 0 < R := by linarith [hR.1]
  have hlog : 0 < Real.log R := Real.log_pos (by linarith [hR.1])
  have he := hR.2 xi hxi hxi1
  rw [← primeBin_log_sum hR0.le hxi0] at he
  have hlow := (abs_le.mp he).1
  have hhigh := (abs_le.mp he).2
  have hcountupper := primeBin_log_sum_upper hR.1 hxi0 hxi1
  have hcountlower := primeBin_log_sum_lower hR0 hxi0
  constructor
  · apply (div_le_iff₀ (show 0 < 4*Real.log R by positivity)).mpr
    nlinarith only [hlow,hcountupper]
  · apply (le_div_iff₀ hlog).mpr
    have hprod := mul_nonneg hxi0 hR0.le
    nlinarith only [hhigh,hcountlower,hprod]

end ErdosInversePrimeBin

end

section

open _root_.Filter
open scoped Topology
namespace ErdosSourcePolynomial
open ErdosInversePrimeBin

theorem prime_bin_log_upper {R xi : ℝ} (hR : 2 ≤ R) (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (p : primeBin R xi) : Real.log (p.val : ℝ) ≤ 2*Real.log R := by
  have hR0 : 0 < R := by linarith
  have hp := (mem_primeBin hR0.le hxi0 p.val).mp p.property
  have hp2 : (p.val : ℝ) ≤ 2*R := hp.2.2.trans
    (mul_le_mul_of_nonneg_right (by linarith : 1+xi ≤ 2) hR0.le)
  have hsq : 2*R ≤ R^2 := by
    simpa only [pow_two] using mul_le_mul_of_nonneg_right hR hR0.le
  have h := Real.log_le_log (hR0.trans hp.2.1) (hp2.trans hsq)
  simpa only [Real.log_pow,Nat.cast_ofNat] using h

theorem prime_bin_slope_cost_bound {R xi L : ℝ} (hR : 2 ≤ R) (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (hL : 0 < L) (T : primeBin R xi → Finset ℤ)
    (hcount : ((primeBin R xi).card : ℝ) ≤ 2*R/Real.log R)
    (hthin : (∑ p : primeBin R xi, ((T p).card : ℝ)) ≤ ((primeBin R xi).card : ℝ)*R/L^6) :
    (∑ p : primeBin R xi, ((T p).card : ℝ)*Real.log (p.val : ℝ)) ≤ 4*R^2/L^6 := by
  have hR0 : 0 < R := by linarith
  have hlog : 0 < Real.log R := Real.log_pos (by linarith)
  calc
    _ ≤ ∑ p : primeBin R xi, ((T p).card : ℝ)*(2*Real.log R) :=
      Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_left (prime_bin_log_upper hR hxi0 hxi1 p) (Nat.cast_nonneg _))
    _ = (∑ p : primeBin R xi, ((T p).card : ℝ))*(2*Real.log R) := by rw [Finset.sum_mul]
    _ ≤ (((primeBin R xi).card : ℝ)*R/L^6)*(2*Real.log R) :=
      mul_le_mul_of_nonneg_right hthin (by positivity)
    _ ≤ ((2*R/Real.log R)*R/L^6)*(2*Real.log R) := by gcongr
    _ = 4*R^2/L^6 := by field_simp <;> ring

theorem rich_prime_log_lower {R xi eta c : ℝ} (hR : 2 ≤ R) (heta : 0 < eta)
    (hxi : eta ≤ xi) (hc : 0 ≤ c)
    (hcount : xi*R/(4*Real.log R) ≤ ((primeBin R xi).card : ℝ))
    (I : Finset ℕ) (hIP : I ⊆ primeBin R xi)
    (hrich : c*((primeBin R xi).card : ℝ) ≤ (I.card : ℝ)) :
    c*eta*R/4 ≤ ∑ p ∈ I, Real.log (p : ℝ) := by
  have hR0 : 0 < R := by linarith
  have hlog : 0 < Real.log R := Real.log_pos (by linarith)
  have hxi0 : 0 ≤ xi := heta.le.trans hxi
  have hsum : (I.card : ℝ)*Real.log R ≤ ∑ p ∈ I, Real.log (p : ℝ) := by
    calc
      _ = ∑ _p ∈ I, Real.log R := by simp
      _ ≤ _ := Finset.sum_le_sum (fun p hp =>
        Real.log_le_log hR0 ((mem_primeBin hR0.le hxi0 p).mp (hIP hp)).2.1.le)
  calc
    c*eta*R/4 ≤ c*xi*R/4 := by gcongr
    _ = c*(xi*R/(4*Real.log R))*Real.log R := by field_simp
    _ ≤ c*((primeBin R xi).card : ℝ)*Real.log R := by gcongr
    _ ≤ (I.card : ℝ)*Real.log R := mul_le_mul_of_nonneg_right hrich hlog.le
    _ ≤ _ := hsum

theorem uniform_prime_bin_budgets {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ R : ℝ in atTop, 2 ≤ R ∧ ∀ xi : ℝ, eta ≤ xi → xi ≤ 1 →
      (∀ L : ℝ, 0 < L → ∀ T : primeBin R xi → Finset ℤ,
        (∑ p : primeBin R xi, ((T p).card : ℝ)) ≤ ((primeBin R xi).card : ℝ)*R/L^6 →
        (∑ p : primeBin R xi, ((T p).card : ℝ)*Real.log (p.val : ℝ)) ≤ 4*R^2/L^6) ∧
      (∀ c : ℝ, 0 ≤ c → ∀ I : Finset ℕ, I ⊆ primeBin R xi →
        c*((primeBin R xi).card : ℝ) ≤ (I.card : ℝ) → c*eta*R/4 ≤ ∑ p ∈ I, Real.log (p : ℝ)) := by
  filter_upwards [uniform_prime_bin_count heta] with R hR
  refine ⟨hR.1,?_⟩
  intro xi hxi hxi1
  have hxi0 := heta.le.trans hxi
  have hlog : 0 < Real.log R := Real.log_pos (by linarith [hR.1])
  have hR0 : 0 < R := by linarith [hR.1]
  have hbounds := hR.2 xi hxi hxi1
  have hupper : ((primeBin R xi).card : ℝ) ≤ 2*R/Real.log R := by
    apply hbounds.2.trans
    gcongr
    linarith
  exact ⟨fun L hL T hthin => prime_bin_slope_cost_bound hR.1 hxi0 hxi1 hL T hupper hthin,
    fun c hc I hIP hrich => rich_prime_log_lower hR.1 heta hxi hc hbounds.1 I hIP hrich⟩

end ErdosSourcePolynomial

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_PolynomialValueBound
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosAuxiliaryPolynomial

theorem exponent_sum {D : ℕ} (i : MonomialIndex D) :
    (exponent i).sum (fun _ n => n) = i.1.val := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
  simp only [Fin.sum_univ_two,exponent_zero,exponent_one]
  have h := i.2.isLt
  omega

theorem coeff_encode {D : ℕ} (v : MonomialIndex D → ℤ) (i : MonomialIndex D) :
    (encode v).coeff (exponent i) = v i := by
  classical
  simp [encode,MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial,(exponent_injective D).eq_iff]

theorem encode_eq_zero_iff {D : ℕ} (v : MonomialIndex D → ℤ) : encode v = 0 ↔ v = 0 := by
  constructor
  · intro h
    funext i
    have hi := congrArg (fun P : MvPolynomial (Fin 2) ℤ => P.coeff (exponent i)) h
    simpa only [coeff_encode,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply,Pi.zero_apply,MvPolynomial.coeff_zero] using hi
  · rintro rfl
    simp [encode]

theorem encode_degree_le {D : ℕ} (v : MonomialIndex D → ℤ) : (encode v).totalDegree ≤ D := by
  apply (MvPolynomial.mem_restrictTotalDegree (R := ℤ) (Fin 2) D (encode v)).mp
  apply Submodule.sum_mem
  intro i hi
  apply (MvPolynomial.mem_restrictTotalDegree (R := ℤ) (Fin 2) D _).mpr
  have h := MvPolynomial.totalDegree_monomial_le (exponent i) (v i)
  change (MvPolynomial.monomial (exponent i) (v i)).totalDegree ≤ (exponent i).sum (fun _ n => n) at h
  rw [exponent_sum] at h
  exact h.trans (Nat.le_of_lt_succ i.1.isLt)

theorem encode_coefficient_bound {D H : ℕ} (v : MonomialIndex D → ℤ)
    (hv : ∀ i, |v i| ≤ (H : ℤ)) (m : Fin 2 →₀ ℕ) : |(encode v).coeff m| ≤ (H : ℤ) := by
  classical
  by_cases hm : ∃ i : MonomialIndex D, exponent i = m
  · obtain ⟨i,rfl⟩ := hm
    rw [coeff_encode]
    exact hv i
  · have hz : (encode v).coeff m = 0 := by
      simp only [encode,MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial]
      apply Finset.sum_eq_zero
      intro i hi
      exact ite_eq_right (fun h => hm ⟨i,h⟩)
    rw [hz,abs_zero]
    exact Int.natCast_nonneg H

end ErdosAuxiliaryPolynomial

end

section

namespace ErdosAuxiliaryPolynomial

theorem exponent_representation (D : ℕ) (m : Fin 2 →₀ ℕ)
    (hm : m.sum (fun _ n => n) ≤ D) : ∃ i : MonomialIndex D, exponent i = m := by
  have hsum : m.sum (fun _ n => n) = m 0+m 1 := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    exact Fin.sum_univ_two _
  rw [hsum] at hm
  let k : Fin (D+1) := ⟨m 0+m 1,by omega⟩
  have hj : m 0 < k.val+1 := by
    change m 0 < m 0+m 1+1
    omega
  let i : MonomialIndex D := ⟨k,⟨m 0,hj⟩⟩
  refine ⟨i,?_⟩
  ext j
  fin_cases j <;> simp [exponent,i,k]

theorem coeff_encode_of_not_range {D : ℕ} (v : MonomialIndex D → ℤ) (m : Fin 2 →₀ ℕ)
    (hm : ¬∃ i : MonomialIndex D, exponent i = m) : (encode v).coeff m = 0 := by
  classical
  simp only [encode,MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial]
  apply Finset.sum_eq_zero
  intro i hi
  exact ite_eq_right (fun h => hm ⟨i,h⟩)

theorem encode_coefficients (Q : MvPolynomial (Fin 2) ℤ) (D : ℕ) (hD : Q.totalDegree ≤ D) :
    encode (fun i : MonomialIndex D => Q.coeff (exponent i)) = Q := by
  classical
  ext m
  by_cases hm : ∃ i : MonomialIndex D, exponent i = m
  · obtain ⟨i,rfl⟩ := hm
    exact coeff_encode _ i
  · have hz : Q.coeff m = 0 := by
      by_contra hc
      have hd := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hc)
      exact hm (exponent_representation D m (hd.trans hD))
    rw [coeff_encode_of_not_range _ m hm,hz]

end ErdosAuxiliaryPolynomial

end

section

namespace ErdosAuxiliaryPolynomial

theorem evalReal_monomial {D : ℕ} (i : MonomialIndex D) (c : ℤ) (x y : ℝ) :
    evalReal (MvPolynomial.monomial (exponent i) c) x y =
      (c : ℝ)*(x^i.2.val*y^(i.1.val-i.2.val)) := by
  change MvPolynomial.eval₂ (Int.castRingHom ℝ) ![x,y]
    (MvPolynomial.monomial (exponent i) c) = _
  rw [MvPolynomial.eval₂_monomial,Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp [exponent,Fin.prod_univ_two]

theorem evalReal_encode {D : ℕ} (v : MonomialIndex D → ℤ) (x y : ℝ) :
    evalReal (encode v) x y =
      ∑ i : MonomialIndex D, (v i : ℝ)*(x^i.2.val*y^(i.1.val-i.2.val)) := by
  change (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) ![x,y])
    (∑ i, MvPolynomial.monomial (exponent i) (v i)) = _
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => evalReal_monomial i (v i) x y)

theorem evalReal_int (Q : MvPolynomial (Fin 2) ℤ) (x y : ℤ) :
    evalReal Q (x : ℝ) (y : ℝ) = (MvPolynomial.eval ![x,y] Q : ℝ) := by
  have he : (Int.castRingHom ℝ) ∘ (![x,y] : Fin 2 → ℤ) = ![(x : ℝ),(y : ℝ)] := by
    funext i
    fin_cases i <;> rfl
  have h := MvPolynomial.eval₂_comp (Int.castRingHom ℝ) ![x,y] Q
  rw [he] at h
  exact h.symm

theorem evalReal_encode_bound {D H : ℕ} (v : MonomialIndex D → ℤ)
    (hv : ∀ i, |v i| ≤ (H : ℤ)) (S x y : ℝ)
    (hx : 0 ≤ x ∧ x ≤ S) (hy : 0 ≤ y ∧ y ≤ S) :
    |evalReal (encode v) x y| ≤ ((D+2).choose 2 : ℝ)*(H : ℝ)*(max 1 S)^D := by
  have hx0 := hx.1
  have hy0 := hy.1
  let M := max 1 S
  have hM : 1 ≤ M := le_max_left _ _
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hxM : x ≤ M := hx.2.trans (le_max_right _ _)
  have hyM : y ≤ M := hy.2.trans (le_max_right _ _)
  have hterm (i : MonomialIndex D) :
      |(v i : ℝ)*(x^i.2.val*y^(i.1.val-i.2.val))| ≤ (H : ℝ)*M^D := by
    have hc : |(v i : ℝ)| ≤ (H : ℝ) := by exact_mod_cast hv i
    have hp : x^i.2.val*y^(i.1.val-i.2.val) ≤ M^D := by
      calc
        _ ≤ M^i.2.val*M^(i.1.val-i.2.val) := by gcongr
        _ = M^i.1.val := by
          rw [← pow_add]
          congr 1
          have hi := i.2.isLt
          omega
        _ ≤ M^D := pow_le_pow_right₀ hM (Nat.le_of_lt_succ i.1.isLt)
    rw [abs_mul,abs_mul,abs_of_nonneg (pow_nonneg hx.1 _),abs_of_nonneg (pow_nonneg hy.1 _)]
    exact mul_le_mul hc hp (mul_nonneg (pow_nonneg hx.1 _) (pow_nonneg hy.1 _)) (Nat.cast_nonneg H)
  rw [evalReal_encode]
  calc
    _ ≤ ∑ i : MonomialIndex D, |(v i : ℝ)*(x^i.2.val*y^(i.1.val-i.2.val))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : MonomialIndex D, (H : ℝ)*M^D := Finset.sum_le_sum (fun i _ => hterm i)
    _ = (Fintype.card (MonomialIndex D) : ℝ)*((H : ℝ)*M^D) := by simp
    _ = ((D+2).choose 2 : ℝ)*(H : ℝ)*(max 1 S)^D := by rw [monomialIndex_card]; ring

theorem polynomial_value_bound (Q : MvPolynomial (Fin 2) ℤ) (D H : ℕ)
    (hD : Q.totalDegree ≤ D) (hH : ∀ m : Fin 2 →₀ ℕ, |Q.coeff m| ≤ (H : ℤ))
    (S : ℝ) (x y : ℤ) (hx : 0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ S) (hy : 0 ≤ (y : ℝ) ∧ (y : ℝ) ≤ S) :
    |(MvPolynomial.eval ![x,y] Q : ℝ)| ≤ ((D+2).choose 2 : ℝ)*(H : ℝ)*(max 1 S)^D := by
  rw [← evalReal_int,← encode_coefficients Q D hD]
  exact evalReal_encode_bound _ (fun i => hH (exponent i)) S x y hx hy

end ErdosAuxiliaryPolynomial

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_LineSubstitution
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosAuxiliaryPolynomial

theorem lineSub_monomial {R : Type*} [CommRing R] (φ : ℤ →+* R) (a s : R)
    {D : ℕ} (i : MonomialIndex D) (c : ℤ) :
    lineSub φ a s (MvPolynomial.monomial (exponent i) c) =
      Polynomial.C (φ c)*(Polynomial.X^i.2.val *
        (Polynomial.C a-Polynomial.C s*Polynomial.X)^(i.1.val-i.2.val)) := by
  change MvPolynomial.eval₂ (Polynomial.C.comp φ)
    ![Polynomial.X,Polynomial.C a-Polynomial.C s*Polynomial.X]
    (MvPolynomial.monomial (exponent i) c) = _
  rw [MvPolynomial.eval₂_monomial,Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp [exponent,Fin.prod_univ_two]

theorem affine_natDegree_le {R : Type*} [CommRing R] (a s : R) :
    (Polynomial.C a-Polynomial.C s*Polynomial.X).natDegree ≤ 1 := by
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · simp
  · have h := Polynomial.natDegree_mul_le (p := Polynomial.C s) (q := Polynomial.X)
    simp only [Polynomial.natDegree_C,zero_add] at h
    exact h.trans Polynomial.natDegree_X_le

theorem lineSub_monomial_degree {R : Type*} [CommRing R] (φ : ℤ →+* R) (a s : R)
    {D : ℕ} (i : MonomialIndex D) (c : ℤ) :
    (lineSub φ a s (MvPolynomial.monomial (exponent i) c)).natDegree ≤ D := by
  have hx : (Polynomial.X^i.2.val : Polynomial R).natDegree ≤ i.2.val := by
    simpa using Polynomial.natDegree_pow_le_of_le i.2.val (Polynomial.natDegree_X_le (R := R))
  have hl : ((Polynomial.C a-Polynomial.C s*Polynomial.X)^(i.1.val-i.2.val)).natDegree ≤ i.1.val-i.2.val := by
    simpa using Polynomial.natDegree_pow_le_of_le (i.1.val-i.2.val) (affine_natDegree_le a s)
  rw [lineSub_monomial]
  have hprod := Polynomial.natDegree_mul_le (p := (Polynomial.X : Polynomial R)^i.2.val)
    (q := (Polynomial.C a-Polynomial.C s*Polynomial.X)^(i.1.val-i.2.val))
  have hC := Polynomial.natDegree_mul_le (p := Polynomial.C (φ c))
    (q := Polynomial.X^i.2.val*(Polynomial.C a-Polynomial.C s*Polynomial.X)^(i.1.val-i.2.val))
  simp only [Polynomial.natDegree_C,zero_add] at hC
  have hk := i.1.isLt
  have hj := i.2.isLt
  exact (hC.trans (hprod.trans (Nat.add_le_add hx hl))).trans (by omega)

theorem lineSub_encode_degree {R : Type*} [CommRing R] (φ : ℤ →+* R) (a s : R)
    {D : ℕ} (v : MonomialIndex D → ℤ) : (lineSub φ a s (encode v)).natDegree ≤ D := by
  rw [encode,map_sum]
  exact Polynomial.natDegree_sum_le_of_forall_le _ _ (fun i _ => lineSub_monomial_degree φ a s i (v i))

theorem lineSub_encode_eq_zero {R : Type*} [CommRing R] (φ : ℤ →+* R) (a s : R)
    {D : ℕ} (v : MonomialIndex D → ℤ)
    (h : ∀ k : Fin (D+1), (lineSub φ a s (encode v)).coeff k = 0) :
    lineSub φ a s (encode v) = 0 := by
  ext k
  rw [Polynomial.coeff_zero]
  by_cases hk : k ≤ D
  · exact h ⟨k,by omega⟩
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((lineSub_encode_degree φ a s v).trans_lt (by omega))

end ErdosAuxiliaryPolynomial

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeProductLifting
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosAuxiliaryPolynomial

theorem lineSub_eval {R : Type*} [CommRing R] (φ : ℤ →+* R) (a s z : R)
    (Q : MvPolynomial (Fin 2) ℤ) :
    (lineSub φ a s Q).eval z = MvPolynomial.eval₂Hom φ ![z,a-s*z] Q := by
  have he : (Polynomial.evalRingHom z).comp (lineSub φ a s) =
      MvPolynomial.eval₂Hom φ ![z,a-s*z] := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [lineSub]
    · intro i
      fin_cases i <;> simp [lineSub]
  exact congrArg (fun f : MvPolynomial (Fin 2) ℤ →+* R => f Q) he

theorem eval_integer_cast {R : Type*} [CommRing R] (Q : MvPolynomial (Fin 2) ℤ) (x y : ℤ) :
    MvPolynomial.eval₂Hom (Int.castRingHom R) ![(x : R),(y : R)] Q =
      (MvPolynomial.eval ![x,y] Q : R) := by
  have he : (Int.castRingHom R) ∘ (![x,y] : Fin 2 → ℤ) = ![(x : R),(y : R)] := by
    funext i
    fin_cases i <;> rfl
  have h := MvPolynomial.eval₂_comp (Int.castRingHom R) ![x,y] Q
  rw [he] at h
  exact h.symm

theorem divides_of_line_incidence (p : ℕ) (Q : MvPolynomial (Fin 2) ℤ) (a s : ZMod p)
    (x y : ℤ) (hline : lineSub (Int.castRingHom (ZMod p)) a s Q = 0)
    (hinc : (y : ZMod p) = a-s*(x : ZMod p)) : (p : ℤ) ∣ MvPolynomial.eval ![x,y] Q := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  rw [← eval_integer_cast,hinc,← lineSub_eval,hline,Polynomial.eval_zero]

theorem zero_of_prime_product_large (n : ℤ) (I : Finset ℕ)
    (hprime : ∀ p ∈ I, Nat.Prime p) (hdiv : ∀ p ∈ I, (p : ℤ) ∣ n)
    (hlarge : |(n : ℝ)| < ((∏ p ∈ I, p : ℕ) : ℝ)) : n = 0 := by
  by_contra hn
  have hd : (∏ p ∈ I, p) ∣ n.natAbs :=
    Finset.prod_primes_dvd n.natAbs (fun p hp => (hprime p hp).prime)
      (fun p hp => Int.natCast_dvd.mp (hdiv p hp))
  have hle : (∏ p ∈ I, p) ≤ n.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hn) hd
  have habs : (n.natAbs : ℝ) = |(n : ℝ)| := by rw [Nat.cast_natAbs,Int.cast_abs]
  have hleR : ((∏ p ∈ I, p : ℕ) : ℝ) ≤ |(n : ℝ)| := by
    rw [← habs]
    exact_mod_cast hle
  exact (not_lt_of_ge hleR) hlarge

theorem value_zero_of_incident_prime_product (Q : MvPolynomial (Fin 2) ℤ) (D H : ℕ)
    (hD : Q.totalDegree ≤ D) (hH : ∀ m : Fin 2 →₀ ℕ, |Q.coeff m| ≤ (H : ℤ))
    (S : ℝ) (x y : ℤ) (hx : 0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ S) (hy : 0 ≤ (y : ℝ) ∧ (y : ℝ) ≤ S)
    (I : Finset ℕ) (hprime : ∀ p ∈ I, Nat.Prime p)
    (a s : ∀ p : I, ZMod p.val)
    (hline : ∀ p : I, lineSub (Int.castRingHom (ZMod p.val)) (a p) (s p) Q = 0)
    (hinc : ∀ p : I, (y : ZMod p.val) = a p-s p*(x : ZMod p.val))
    (hlarge : ((D+2).choose 2 : ℝ)*(H : ℝ)*(max 1 S)^D < ((∏ p ∈ I, p : ℕ) : ℝ)) :
    MvPolynomial.eval ![x,y] Q = 0 := by
  apply zero_of_prime_product_large _ I hprime
  · intro p hp
    exact divides_of_line_incidence p Q (a ⟨p,hp⟩) (s ⟨p,hp⟩) x y (hline ⟨p,hp⟩) (hinc ⟨p,hp⟩)
  · exact (polynomial_value_bound Q D H hD hH S x y hx hy).trans_lt hlarge

end ErdosAuxiliaryPolynomial

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_CoefficientBoxCollision
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosAuxiliaryPolynomial

theorem boxLift_injective {ι : Type*} {H : ℕ} : Function.Injective (@boxLift ι H) := by
  intro x y h
  funext i
  apply Fin.ext
  have hi : ((x i).val : ℤ) = ((y i).val : ℤ) := congrFun h i
  exact_mod_cast hi

theorem exists_bounded_kernel_vector {ι Γ : Type*} [Fintype ι]
    [AddCommGroup Γ] [Fintype Γ] (φ : (ι → ℤ) →+ Γ) (H : ℕ)
    (hcard : Fintype.card Γ < (H+1)^(Fintype.card ι)) :
    ∃ v : ι → ℤ, v ≠ 0 ∧ (∀ i, |v i| ≤ (H : ℤ)) ∧ φ v = 0 := by
  classical
  let f : (ι → Fin (H+1)) → Γ := fun x => φ (boxLift x)
  have hnot : ¬Function.Injective f := by
    intro hinj
    have hc := Fintype.card_le_of_injective f hinj
    have he : Fintype.card (ι → Fin (H+1)) = (H+1)^(Fintype.card ι) := by simp
    rw [he] at hc
    exact (not_le_of_gt hcard) hc
  unfold Function.Injective at hnot
  push Not at hnot
  obtain ⟨x,y,hxy,hne⟩ := hnot
  let v := boxLift x - boxLift y
  have hv : v ≠ 0 := by
    intro hz
    apply hne
    apply boxLift_injective
    exact sub_eq_zero.mp hz
  refine ⟨v,hv,?_,?_⟩
  · intro i
    have hx := (x i).isLt
    have hy := (y i).isLt
    change |((x i).val : ℤ) - ((y i).val : ℤ)| ≤ (H : ℤ)
    rw [abs_le]
    omega
  · change φ (boxLift x - boxLift y) = 0
    rw [map_sub]
    change φ (boxLift x) = φ (boxLift y) at hxy
    rw [hxy,sub_self]

end ErdosAuxiliaryPolynomial

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_LineCongruenceConstruction
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosAuxiliaryPolynomial

theorem residueSystem_card (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p)
    (T : ∀ p : P, Finset (ZMod p.val)) (D : ℕ) :
    @Fintype.card (ResidueSystem P T D) (residueFintype P hP T D) =
      ∏ p : P, p.val^((D+1)*(T p).card) := by
  classical
  let (p : P) : NeZero p.val := ⟨Nat.ne_of_gt (hP p p.property)⟩
  change Fintype.card (∀ p : P, ∀ _s : T p, Fin (D+1) → ZMod p.val) = _
  simp [Fintype.card_pi,← pow_mul]

theorem exists_line_congruence_polynomial (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p)
    (T : ∀ p : P, Finset (ZMod p.val)) (a : ∀ p : P, ZMod p.val) (D H : ℕ)
    (hbox : (∏ p : P, p.val^((D+1)*(T p).card)) < (H+1)^((D+2).choose 2)) :
    ∃ Q : MvPolynomial (Fin 2) ℤ, Q ≠ 0 ∧ Q.totalDegree ≤ D ∧
      (∀ m : Fin 2 →₀ ℕ, |Q.coeff m| ≤ (H : ℤ)) ∧
      ∀ p : P, ∀ s : T p, lineSub (Int.castRingHom (ZMod p.val)) (a p) s.val Q = 0 := by
  classical
  let := residueFintype P hP T D
  have hc : Fintype.card (ResidueSystem P T D) < (H+1)^(Fintype.card (MonomialIndex D)) := by
    rw [residueSystem_card,monomialIndex_card]
    exact hbox
  obtain ⟨v,hv,hbound,hzero⟩ := exists_bounded_kernel_vector (constraintMap P T a D) H hc
  refine ⟨encode v,(encode_eq_zero_iff v).not.mpr hv,encode_degree_le v,
    encode_coefficient_bound v hbound,?_⟩
  intro p s
  apply lineSub_encode_eq_zero
  intro k
  have h := congrFun (congrFun (congrFun hzero p) s) k
  exact h

end ErdosAuxiliaryPolynomial

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_AuxiliaryPolynomialLifting
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosAuxiliaryPolynomial

theorem constraintVolume_pos (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p)
    (T : ∀ p : P, Finset (ZMod p.val)) (D : ℕ) : 0 < constraintVolume P T D := by
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (hP p p.property) _

theorem constraintVolume_log (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p)
    (T : ∀ p : P, Finset (ZMod p.val)) (D : ℕ) :
    Real.log (constraintVolume P T D : ℝ) = ((D : ℝ)+1)*logarithmicCost P T := by
  classical
  unfold constraintVolume logarithmicCost
  simp only [Nat.cast_prod,Nat.cast_pow]
  rw [Real.log_prod (by
    intro p hp
    exact pow_ne_zero _ (by exact_mod_cast (Nat.ne_of_gt (hP p p.property))))]
  simp only [Real.log_pow,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  ring

theorem dimension_pos (D : ℕ) : 0 < (D+2).choose 2 := Nat.choose_pos (by omega)

theorem dimension_ratio (D : ℕ) :
    ((D : ℝ)+1)/((D+2).choose 2 : ℝ) = 2/((D : ℝ)+2) := by
  have hNat : (D+2)*(D+1) = (D+2).choose 2*2 := by
    simpa only [Nat.choose_one_right,Nat.add_assoc] using Nat.add_one_mul_choose_eq (D+1) 1
  have hReal : ((D : ℝ)+2)*((D : ℝ)+1) = ((D+2).choose 2 : ℝ)*2 := by exact_mod_cast hNat
  apply (div_eq_div_iff (by exact_mod_cast (dimension_pos D).ne') (by positivity)).mpr
  nlinarith only [hReal]

theorem exists_small_line_polynomial (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p)
    (T : ∀ p : P, Finset (ZMod p.val)) (a : ∀ p : P, ZMod p.val) (D : ℕ) :
    ∃ (Q : MvPolynomial (Fin 2) ℤ) (H : ℕ), Q ≠ 0 ∧ Q.totalDegree ≤ D ∧ 0 < H ∧
      (∀ m : Fin 2 →₀ ℕ, |Q.coeff m| ≤ (H : ℤ)) ∧
      (∀ p : P, ∀ s : T p, lineSub (Int.castRingHom (ZMod p.val)) (a p) s.val Q = 0) ∧
      Real.log (2*(H : ℝ)) ≤ Real.log 4 + 2/((D : ℝ)+2)*logarithmicCost P T := by
  let M := constraintVolume P T D
  let N := (D+2).choose 2
  let H := boxHeight M N
  have hM : 0 < M := constraintVolume_pos P hP T D
  have hN : 0 < N := dimension_pos D
  obtain ⟨Q,hQ,hdegree,hcoeff,hline⟩ := exists_line_congruence_polynomial P hP T a D H
    (boxHeight_card_strict hN)
  refine ⟨Q,H,hQ,hdegree,boxHeight_pos hM,hcoeff,hline,?_⟩
  have hlog := boxHeight_log_bound hM hN
  change Real.log (2*(H : ℝ)) ≤ Real.log 4 + Real.log (constraintVolume P T D : ℝ)/((D+2).choose 2 : ℝ) at hlog
  rw [constraintVolume_log P hP T D] at hlog
  have he : (((D : ℝ)+1)*logarithmicCost P T)/((D+2).choose 2 : ℝ) =
      2/((D : ℝ)+2)*logarithmicCost P T := by
    calc
      _ = (((D : ℝ)+1)/((D+2).choose 2 : ℝ))*logarithmicCost P T := by ring
      _ = _ := by rw [dimension_ratio]
  rwa [he] at hlog

end ErdosAuxiliaryPolynomial

end

section

namespace ErdosAuxiliaryPolynomial

theorem valueBudget_pos (D H : ℕ) (hH : 0 < H) (S : ℝ) : 0 < valueBudget D H S := by
  have hN : (0 : ℝ) < ((D+2).choose 2 : ℝ) := by exact_mod_cast dimension_pos D
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH
  have hM : (0 : ℝ) < max 1 S := zero_lt_one.trans_le (le_max_left _ _)
  exact mul_pos (mul_pos hN hH0) (pow_pos hM D)

theorem valueBudget_log (D H : ℕ) (hH : 0 < H) (S : ℝ) :
    Real.log (valueBudget D H S) = logarithmicValueBudget D H S := by
  have hN : (((D+2).choose 2 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (dimension_pos D).ne'
  have hH0 : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
  have hM : (max 1 S : ℝ) ≠ 0 := (zero_lt_one.trans_le (le_max_left _ _)).ne'
  rw [valueBudget,Real.log_mul (mul_ne_zero hN hH0) (pow_ne_zero D hM),
    Real.log_mul hN hH0,Real.log_pow]
  rfl

theorem prime_product_log (I : Finset ℕ) (hprime : ∀ p ∈ I, Nat.Prime p) :
    Real.log ((∏ p ∈ I, p : ℕ) : ℝ) = ∑ p ∈ I, Real.log (p : ℝ) := by
  rw [Nat.cast_prod]
  exact Real.log_prod (fun p hp => by exact_mod_cast (hprime p hp).ne_zero)

theorem value_zero_of_log_prime_budget (Q : MvPolynomial (Fin 2) ℤ) (D H : ℕ)
    (hD : Q.totalDegree ≤ D) (hH : ∀ m : Fin 2 →₀ ℕ, |Q.coeff m| ≤ (H : ℤ)) (hHpos : 0 < H)
    (S : ℝ) (x y : ℤ) (hx : 0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ S) (hy : 0 ≤ (y : ℝ) ∧ (y : ℝ) ≤ S)
    (I : Finset ℕ) (hprime : ∀ p ∈ I, Nat.Prime p) (a s : ∀ p : I, ZMod p.val)
    (hline : ∀ p : I, lineSub (Int.castRingHom (ZMod p.val)) (a p) (s p) Q = 0)
    (hinc : ∀ p : I, (y : ZMod p.val) = a p-s p*(x : ZMod p.val))
    (hlarge : logarithmicValueBudget D H S < ∑ p ∈ I, Real.log (p : ℝ)) :
    MvPolynomial.eval ![x,y] Q = 0 := by
  apply value_zero_of_incident_prime_product Q D H hD hH S x y hx hy I hprime a s hline hinc
  have hp : (0 : ℝ) < ((∏ p ∈ I, p : ℕ) : ℝ) := by
    exact_mod_cast (Finset.prod_pos (fun p hp => (hprime p hp).pos))
  apply (Real.log_lt_log_iff (valueBudget_pos D H hHpos S) hp).mp
  rw [valueBudget_log D H hHpos S,prime_product_log I hprime]
  exact hlarge

end ErdosAuxiliaryPolynomial

end

section

namespace ErdosAuxiliaryPolynomial

theorem logarithmicCost_le_budget (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p)
    (T : ∀ p : P, Finset (ZMod p.val)) (K : P → ℝ)
    (hK : ∀ p : P, ((T p).card : ℝ) ≤ K p) :
    logarithmicCost P T ≤ ∑ p : P, K p*Real.log (p.val : ℝ) := by
  apply Finset.sum_le_sum
  intro p hp
  apply mul_le_mul_of_nonneg_right (hK p)
  apply Real.log_nonneg
  exact_mod_cast Nat.succ_le_of_lt (hP p p.property)

end ErdosAuxiliaryPolynomial

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_BoxInflation
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Filter
open scoped Topology
namespace ErdosInverseBoxHeight

theorem bin_inflation_le_power {B C xi : ℝ} (hB : 1 ≤ B) (hC : 0 ≤ C)
    (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1) :
    (1+xi)^(C*Real.log B) ≤ B^C := by
  have hB0 : 0 < B := by linarith
  have hx0 : 0 < 1+xi := by linarith
  have hlB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hlx : Real.log (1+xi) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos hx0
    linarith
  rw [Real.rpow_def_of_pos hx0,Real.rpow_def_of_pos hB0]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_right hlx (mul_nonneg hC hlB)]

theorem uniform_bin_inflation (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ z : ℝ in atTop, 1 < z ∧ ∀ B xi : ℝ,
      1 ≤ B → B ≤ Real.log z → 0 ≤ xi → xi ≤ 1 →
      (1+xi)^(C*Real.log B) ≤ z^((1:ℝ)/10) := by
  have hlog := (isLittleO_log_rpow_rpow_atTop C (by norm_num : (0:ℝ)<1/10)).bound zero_lt_one
  filter_upwards [eventually_gt_atTop (1:ℝ),hlog] with z hz hpow
  refine ⟨hz,?_⟩
  intro B xi hB hBz hxi0 hxi1
  have hz0 : 0 ≤ z := by linarith
  have hL0 : 0 ≤ Real.log z := Real.log_nonneg hz.le
  have hbound : (Real.log z)^C ≤ z^((1:ℝ)/10) := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hL0 C),
      abs_of_nonneg (Real.rpow_nonneg hz0 ((1:ℝ)/10)),one_mul] using hpow
  exact (bin_inflation_le_power hB hC hxi0 hxi1).trans
    ((Real.rpow_le_rpow (by linarith : 0 ≤ B) hBz hC).trans hbound)

theorem sourceZ_le_small_power : ∀ᶠ z : ℝ in atTop,
    1 < z ∧ 0 < sourceZ z ∧ sourceZ z ≤ z^((1:ℝ)/100) := by
  have hlog := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 100
  filter_upwards [eventually_gt_atTop (1:ℝ),hlog] with z hz hL
  dsimp only [Function.comp_apply] at hL
  refine ⟨hz,Real.exp_pos _,?_⟩
  have hz0 : 0 < z := by linarith
  have hlog0 : 0 ≤ Real.log z := (Real.log_pos hz).le
  rw [sourceZ,Real.rpow_def_of_pos hz0]
  apply Real.exp_le_exp.mpr
  have h := div_le_div_of_nonneg_left hlog0 (by norm_num : (0:ℝ)<100) hL
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  ring

end ErdosInverseBoxHeight

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_CorrectionFloorRemainder
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseBoxHeight

theorem source_B_bounds : ∀ᶠ z : ℝ in atTop,
    Real.exp 1 ≤ sourceW z ∧ 1 ≤ sourceB z ∧ sourceB z ≤ Real.log z := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop (2:ℝ) (by norm_num : (0:ℝ)<1)).bound (Real.exp_pos (-1))
  have hl := Real.tendsto_log_atTop.eventually hsmall
  have hlarge := Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 1)
  filter_upwards [hl,hlarge] with z hz hL
  let L := Real.log z
  have hL0 : 0 < L := (Real.exp_pos 1).trans_le hL
  have hLL : 1 ≤ Real.log L := by
    have h := Real.log_le_log (Real.exp_pos 1) hL
    simpa only [Real.log_exp] using h
  have hsq0 : 0 < (Real.log L)^2 := sq_pos_of_pos (by linarith)
  have hsq1 : 1 ≤ (Real.log L)^2 := by nlinarith
  have hbound : (Real.log L)^2 ≤ Real.exp (-1)*L := by
    change ‖(Real.log L)^(2:ℝ)‖ ≤ Real.exp (-1)*‖L^(1:ℝ)‖ at hz
    simpa only [Real.norm_eq_abs,Real.rpow_two,Real.rpow_one,
      abs_of_nonneg (sq_nonneg (Real.log L)),abs_of_pos hL0] using hz
  have hW : Real.exp 1 ≤ sourceW z := by
    apply (le_div_iff₀ hsq0).mpr
    have h := mul_le_mul_of_nonneg_left hbound (Real.exp_pos 1).le
    have he : Real.exp 1*Real.exp (-1)=1 := by rw [← Real.exp_add]; norm_num
    nlinarith
  have hW0 : 0 < sourceW z := (Real.exp_pos 1).trans_le hW
  have hlogW : 1 ≤ Real.log (sourceW z) := by
    have h := Real.log_le_log (Real.exp_pos 1) hW
    simpa only [Real.log_exp] using h
  have hWle : sourceW z ≤ L := div_le_self hL0.le hsq1
  have hlogle : Real.log (sourceW z) ≤ L := by
    have h := Real.log_le_log hW0 hWle
    have h' := Real.log_le_sub_one_of_pos hL0
    linarith
  refine ⟨hW,?_,?_⟩
  · exact (one_le_div (by linarith : 0 < Real.log (sourceW z))).mpr hlogle
  · exact div_le_self hL0.le hlogW

theorem sourceY_le_square {z : ℝ} (hL : 1 ≤ Real.log z) : (sourceY z : ℝ) ≤ z^2 := by
  have hden : 1 ≤ (Real.log z)^2 := by nlinarith
  exact (Nat.floor_le (div_nonneg (sq_nonneg z) (sq_nonneg _))).trans
    (div_le_self (sq_nonneg z) hden)

theorem source_cofactor_le_square {z p q : ℝ} (hL : 1 ≤ Real.log z)
    (hp : 1 ≤ p) (hq : 0 ≤ q) (hpq : p*q ≤ (sourceY z : ℝ)) : q ≤ z^2 := by
  have hmul : q ≤ p*q := by nlinarith [mul_le_mul_of_nonneg_right hp hq]
  exact hmul.trans (hpq.trans (sourceY_le_square hL))

end ErdosInverseBoxHeight

end

section

open _root_.Filter
open scoped Topology
namespace ErdosSourceLineBudget
open ErdosInverseBoxHeight

theorem source_W_power_quarter (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ z : ℝ in atTop, 1 < sourceW z ∧ (sourceW z)^C ≤ z^((1 : ℝ)/4) := by
  have hs := (isLittleO_log_rpow_rpow_atTop C (by norm_num : (0 : ℝ) < 1/4)).bound zero_lt_one
  have hLL := Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 1)
  filter_upwards [source_B_bounds,hs,hLL,eventually_gt_atTop (1 : ℝ)] with z hB hz hlog hz1
  have hz0 : 0 < z := by linarith
  have hL0 : 0 < Real.log z := Real.log_pos hz1
  have hLL1 : 1 ≤ Real.log (Real.log z) := by
    have h := Real.log_le_log (Real.exp_pos 1) hlog
    simpa only [Real.log_exp] using h
  have hsquare : 1 ≤ (Real.log (Real.log z))^2 := by nlinarith
  have hWL : sourceW z ≤ Real.log z := div_le_self hL0.le hsquare
  have hW1 : 1 < sourceW z := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le hB.1
  refine ⟨hW1,?_⟩
  have hh : (Real.log z)^C ≤ z^((1 : ℝ)/4) := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hL0.le C),
      abs_of_nonneg (Real.rpow_nonneg hz0.le ((1 : ℝ)/4)),one_mul] using hz
  exact (Real.rpow_le_rpow (by linarith) hWL hC).trans hh

theorem source_Y_three_halves :
    ∀ᶠ z : ℝ in atTop, z^((3 : ℝ)/2) ≤ (sourceY z : ℝ) := by
  have hs := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1/2)).bound
    (by norm_num : (0 : ℝ) < 1/2)
  filter_upwards [hs,eventually_ge_atTop (2 : ℝ)] with z hz hz2
  have hz0 : 0 < z := by linarith
  have hL : 0 < Real.log z := Real.log_pos (by linarith)
  have hL2 : 0 < (Real.log z)^2 := sq_pos_of_pos hL
  have hh : (Real.log z)^2 ≤ (1/2 : ℝ)*z^((1 : ℝ)/2) := by
    simpa only [Real.norm_eq_abs,Real.rpow_two,abs_of_nonneg (sq_nonneg (Real.log z)),
      abs_of_nonneg (Real.rpow_nonneg hz0.le ((1 : ℝ)/2))] using hz
  have hp : z^((1 : ℝ)/2)*z^((3 : ℝ)/2) = z^2 := by
    rw [← Real.rpow_add hz0]
    norm_num
  have hmul : 2*z^((3 : ℝ)/2)*(Real.log z)^2 ≤ z^2 := by
    nlinarith [mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hz0.le ((3 : ℝ)/2))]
  have hquot : 2*z^((3 : ℝ)/2) ≤ z^2/(Real.log z)^2 := (le_div_iff₀ hL2).mpr hmul
  have hfloor := Nat.lt_floor_add_one (z^2/(Real.log z)^2)
  have hone : 1 ≤ z^((3 : ℝ)/2) := Real.one_le_rpow (by linarith) (by norm_num)
  change z^((3 : ℝ)/2) ≤ (⌊z^2/(Real.log z)^2⌋₊ : ℝ)
  linarith

end ErdosSourceLineBudget

end

section

open _root_.Filter
open scoped Topology
namespace ErdosSourceLineBudget
open ErdosInverseBoxHeight

theorem source_parent_square_lower (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ z : ℝ in atTop, 1 < z ∧ ∀ p q R S : ℝ,
      0 < p → 0 < q → p ≤ 2*R → R ≤ z^((1 : ℝ)/100) → q ≤ S →
      Real.logb (sourceW z) ((sourceY z : ℝ)/(p*q)) ≤ C → z ≤ S := by
  have hquarter := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 24/100)).eventually_ge_atTop 2
  filter_upwards [source_W_power_quarter C hC,source_Y_three_halves,hquarter,
    eventually_gt_atTop (1 : ℝ)] with z hW hY htwo hz
  have hz0 : 0 < z := by linarith
  refine ⟨hz,?_⟩
  intro p q R S hp hq hpR hR hqS hlen
  have hY0 : (0 : ℝ) < sourceY z := (Real.rpow_pos_of_pos hz0 _).trans_le hY
  have hP : p ≤ z^((1 : ℝ)/4) := by
    calc
      p ≤ 2*R := hpR
      _ ≤ 2*z^((1 : ℝ)/100) := mul_le_mul_of_nonneg_left hR (by norm_num)
      _ ≤ z^((24 : ℝ)/100)*z^((1 : ℝ)/100) :=
        mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hz0.le _)
      _ = z^((1 : ℝ)/4) := by rw [← Real.rpow_add hz0];norm_num
  have hratio := (Real.logb_le_iff_le_rpow hW.1 (div_pos hY0 (mul_pos hp hq))).mp hlen
  have hmul : (sourceY z : ℝ) ≤ (sourceW z)^C*(p*q) := (div_le_iff₀ (mul_pos hp hq)).mp hratio
  have hsmall : (sourceW z)^C*p ≤ z^((1 : ℝ)/2) := by
    calc
      _ ≤ z^((1 : ℝ)/4)*z^((1 : ℝ)/4) := mul_le_mul hW.2 hP hp.le
        (Real.rpow_nonneg hz0.le _)
      _ = _ := by rw [← Real.rpow_add hz0];norm_num
  have hle : z^((3 : ℝ)/2) ≤ z^((1 : ℝ)/2)*q := by
    apply hY.trans
    apply hmul.trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hsmall hq.le
  have he : z^((3 : ℝ)/2) = z^((1 : ℝ)/2)*z := by
    have hh := Real.rpow_add hz0 ((1 : ℝ)/2) 1
    norm_num at hh
    exact hh
  rw [he] at hle
  exact (le_of_mul_le_mul_left hle (Real.rpow_pos_of_pos hz0 ((1 : ℝ)/2))).trans hqS

end ErdosSourceLineBudget

end

section

open _root_.Filter
open scoped Topology
namespace ErdosSourceLineBudget
open ErdosInverseBoxHeight

theorem source_Z_ge_two : ∀ᶠ z : ℝ in atTop, 2 ≤ sourceZ z := by
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 1)] with z hz
  have hL : 0 < Real.log z := (Real.exp_pos 1).trans_le hz
  have hLL : 1 ≤ Real.log (Real.log z) := by
    have hh := Real.log_le_log (Real.exp_pos 1) hz
    simpa only [Real.log_exp] using hh
  have hLLL : Real.log (Real.log z) ≤ Real.log z := by
    have hh := Real.log_le_sub_one_of_pos hL
    linarith
  have hratio : 1 ≤ Real.log z/Real.log (Real.log z) :=
    (one_le_div (by linarith)).mpr hLLL
  have hexp : (2 : ℝ) ≤ Real.exp 1 := by
    have hh := Real.add_one_le_exp (1 : ℝ)
    norm_num at hh ⊢
    exact hh
  exact hexp.trans (Real.exp_le_exp.mpr hratio)

theorem extraction_small_power {z R S Z : ℝ} (hz : 1 < z) (hR : 0 ≤ R) (hZ : 0 ≤ Z)
    (hRz : R ≤ z^((1 : ℝ)/100)) (hZz : Z ≤ z^((1 : ℝ)/100)) (hSz : z ≤ S)
    (hbig : 728 < z^((19 : ℝ)/75)) :
    728*R^4*Z^4 < S^((1 : ℝ)/3) := by
  have hz0 : 0 < z := by linarith
  have hR4 : R^4 ≤ z^((4 : ℝ)/100) := by
    calc
      _ ≤ (z^((1 : ℝ)/100))^4 := by gcongr
      _ = _ := by rw [← Real.rpow_mul_natCast hz0.le];norm_num
  have hZ4 : Z^4 ≤ z^((4 : ℝ)/100) := by
    calc
      _ ≤ (z^((1 : ℝ)/100))^4 := by gcongr
      _ = _ := by rw [← Real.rpow_mul_natCast hz0.le];norm_num
  calc
    _ ≤ 728*z^((4 : ℝ)/100)*z^((4 : ℝ)/100) := by gcongr
    _ = 728*z^((2 : ℝ)/25) := by rw [mul_assoc,← Real.rpow_add hz0];norm_num
    _ < z^((19 : ℝ)/75)*z^((2 : ℝ)/25) :=
      mul_lt_mul_of_pos_right hbig (Real.rpow_pos_of_pos hz0 _)
    _ = z^((1 : ℝ)/3) := by rw [← Real.rpow_add hz0];norm_num
    _ ≤ S^((1 : ℝ)/3) := Real.rpow_le_rpow hz0.le hSz (by norm_num)

theorem minimum_line_size_power {z R S Z : ℝ} (hz : 1 < z) (hR : 0 < R) (hZ : 0 < Z)
    (hRz : R ≤ z^((1 : ℝ)/100)) (hZz : Z ≤ z^((1 : ℝ)/100)) (hSz : z ≤ S) :
    z^((93 : ℝ)/100) ≤ S/(R*Z^6) := by
  have hz0 : 0 < z := by linarith
  have hZ6 : Z^6 ≤ z^((6 : ℝ)/100) := by
    calc
      _ ≤ (z^((1 : ℝ)/100))^6 := by gcongr
      _ = _ := by rw [← Real.rpow_mul_natCast hz0.le];norm_num
  have hprod : R*Z^6 ≤ z^((7 : ℝ)/100) := by
    calc
      _ ≤ z^((1 : ℝ)/100)*z^((6 : ℝ)/100) := by gcongr
      _ = _ := by rw [← Real.rpow_add hz0];norm_num
  apply (le_div_iff₀ (mul_pos hR (pow_pos hZ 6))).mpr
  calc
    _ ≤ z^((93 : ℝ)/100)*z^((7 : ℝ)/100) :=
      mul_le_mul_of_nonneg_left hprod (Real.rpow_nonneg hz0.le _)
    _ = z := by rw [← Real.rpow_add hz0];norm_num
    _ ≤ S := hSz

end ErdosSourceLineBudget

end

section

namespace ErdosSourceLineBudget

theorem finite_extraction_budget (D : ℕ) (R S Z : ℝ) (hD : (D : ℝ) ≤ R)
    (hR : 0 < R) (hS : 1 ≤ S) (hZ : 2 ≤ Z)
    (hsmall : 728*R^4*Z^4 < S^((1 : ℝ)/3)) :
    182*(D : ℝ)^4*(1+S^((2 : ℝ)/3))+(D : ℝ)*(S/(R*Z^6)) < S/Z^4 := by
  have hS0 : 0 < S := by linarith
  have hZ0 : 0 < Z := by linarith
  have hu : 1 ≤ S^((2 : ℝ)/3) := Real.one_le_rpow hS (by norm_num)
  have hprod : S^((1 : ℝ)/3)*S^((2 : ℝ)/3) = S := by
    rw [← Real.rpow_add hS0]
    norm_num
  have hlarge : 728*R^4*Z^4*S^((2 : ℝ)/3) < S := by
    have hh := mul_lt_mul_of_pos_right hsmall (Real.rpow_pos_of_pos hS0 ((2 : ℝ)/3))
    rwa [hprod] at hh
  have hnonlinear : 182*(D : ℝ)^4*(1+S^((2 : ℝ)/3)) < S/(2*Z^4) := by
    have hpower : (D : ℝ)^4 ≤ R^4 := by gcongr
    have hfirst : 182*(D : ℝ)^4*(1+S^((2 : ℝ)/3)) ≤ 364*R^4*S^((2 : ℝ)/3) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hpower) (show 0 ≤ 1+S^((2 : ℝ)/3) by positivity),
        mul_nonneg (pow_nonneg hR.le 4) (sub_nonneg.mpr hu)]
    apply hfirst.trans_lt
    apply (lt_div_iff₀ (by positivity : 0 < 2*Z^4)).mpr
    nlinarith
  have hlinear : (D : ℝ)*(S/(R*Z^6)) ≤ S/(2*Z^4) := by
    calc
      _ ≤ R*(S/(R*Z^6)) := mul_le_mul_of_nonneg_right hD (by positivity)
      _ = S/Z^6 := by field_simp
      _ ≤ S/(2*Z^4) := by
        apply div_le_div_of_nonneg_left hS0.le (by positivity)
        have hs : 2 ≤ Z^2 := by nlinarith
        nlinarith [mul_nonneg (pow_nonneg hZ0.le 4) (sub_nonneg.mpr hs)]
  calc
    _ < S/(2*Z^4)+S/(2*Z^4) := add_lt_add_of_lt_of_le hnonlinear hlinear
    _ = _ := by ring

end ErdosSourceLineBudget

end

section

namespace ErdosSourcePolynomial
open ErdosAuxiliaryPolynomial

theorem sourceDegree_le {z R : ℝ} (hR : 0 ≤ R) :
    (sourceDegree z R : ℝ) ≤ R/(Real.log z)^2 :=
  Nat.floor_le (div_nonneg hR (sq_nonneg _))

theorem sourceDegree_le_R {z R : ℝ} (hR : 0 ≤ R) (hL : 1 ≤ Real.log z) :
    (sourceDegree z R : ℝ) ≤ R :=
  (sourceDegree_le hR).trans (div_le_self hR (by nlinarith))

theorem source_degree_factor {z R : ℝ} (hR : 0 < R) (hL : 0 < Real.log z) :
    2/((sourceDegree z R : ℝ)+2) ≤ 2*(Real.log z)^2/R := by
  have hf := Nat.lt_floor_add_one (R/(Real.log z)^2)
  change R/(Real.log z)^2 < (sourceDegree z R : ℝ)+1 at hf
  have hden : (0 : ℝ) < (sourceDegree z R : ℝ)+2 := by positivity
  have hsq : 0 < (Real.log z)^2 := sq_pos_of_pos hL
  have hprod : R ≤ ((sourceDegree z R : ℝ)+2)*(Real.log z)^2 :=
    (div_le_iff₀ hsq).mp (by linarith)
  apply (div_le_div_iff₀ hden hR).mpr
  convert! (mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 2)) using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem dimension_le_square (D : ℕ) : ((D+2).choose 2 : ℝ) ≤ ((D : ℝ)+2)^2 := by
  have h := Nat.choose_le_pow (D+2) 2
  exact_mod_cast h

theorem source_dimension_log_bound {z R : ℝ} (hz : 2 ≤ z) (hR : 0 ≤ R)
    (hRz : R ≤ z) (hL : 1 ≤ Real.log z) :
    Real.log ((sourceDegree z R+2).choose 2 : ℝ) ≤ 4*Real.log z := by
  have hd := sourceDegree_le_R hR hL
  have hn := dimension_le_square (sourceDegree z R)
  have hz0 : 0 ≤ z := by linarith
  have hD2 : (sourceDegree z R : ℝ)+2 ≤ z^2 := by nlinarith
  have hN : ((sourceDegree z R+2).choose 2 : ℝ) ≤ z^4 := by
    apply hn.trans
    calc
      _ ≤ (z^2)^2 := by gcongr
      _ = z^4 := by ring
  have hpos : (0 : ℝ) < ((sourceDegree z R+2).choose 2 : ℝ) := by
    exact_mod_cast dimension_pos (sourceDegree z R)
  have h := Real.log_le_log hpos hN
  simpa only [Real.log_pow,Nat.cast_ofNat] using h

end ErdosSourcePolynomial

end

section

open _root_.Filter
open scoped Topology
namespace ErdosSourceLineBudget
open ErdosInverseBoxHeight ErdosSourcePolynomial

theorem uniform_extraction_budget (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ z : ℝ in atTop, 1 < z ∧ ∀ p q R S : ℝ,
      0 < p → 0 < q → p ≤ 2*R → R ≤ z^((1 : ℝ)/100) → q ≤ S →
      Real.logb (sourceW z) ((sourceY z : ℝ)/(p*q)) ≤ C →
      z^((93 : ℝ)/100) ≤ S/(R*(sourceZ z)^6) ∧ 1 ≤ S/(R*(sourceZ z)^6) ∧
      182*(sourceDegree z R : ℝ)^4*(1+S^((2 : ℝ)/3))+
        (sourceDegree z R : ℝ)*(S/(R*(sourceZ z)^6)) < S/(sourceZ z)^4 := by
  have hbig := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 19/75)).eventually_gt_atTop 728
  filter_upwards [source_parent_square_lower C hC,sourceZ_le_small_power,source_Z_ge_two,hbig,
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with z hparent hZ hZ2 hlarge hL
  refine ⟨hparent.1,?_⟩
  intro p q R S hp hq hpR hR hqS hlen
  have hSz := hparent.2 p q R S hp hq hpR hR hqS hlen
  have hR0 : 0 < R := by linarith
  have hS1 : 1 ≤ S := hparent.1.le.trans hSz
  have hmin := minimum_line_size_power hparent.1 hR0 hZ.2.1 hR hZ.2.2 hSz
  have hmin1 : 1 ≤ S/(R*(sourceZ z)^6) :=
    (Real.one_le_rpow hparent.1.le (by norm_num : (0 : ℝ) ≤ 93/100)).trans hmin
  have hsmall := extraction_small_power hparent.1 hR0.le hZ.2.1.le hR hZ.2.2 hSz hlarge
  exact ⟨hmin,hmin1,finite_extraction_budget (sourceDegree z R) R S (sourceZ z)
    (sourceDegree_le_R hR0.le hL) hR0 hS1 hZ2 hsmall⟩

end ErdosSourceLineBudget

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_LatticeSpacing
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosRichLine

theorem congruent_integer_set_card (A : Finset ℤ) (S : ℝ) (hS : 0 ≤ S)
    (d : ℕ) (hd : 0 < d) (hbox : ∀ x ∈ A, 0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ S)
    (hdiv : ∀ x ∈ A, ∀ y ∈ A, (d : ℤ) ∣ x-y) :
    (A.card : ℝ) ≤ S/(d : ℝ)+1 := by
  classical
  by_cases hA : A.Nonempty
  · let x0 : ℤ := A.min' hA
    have hx0 : x0 ∈ A := Finset.min'_mem A hA
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
    let f : ℤ → ℤ := fun x => (x-x0)/(d : ℤ)
    have he (x : ℤ) (hx : x ∈ A) : (d : ℤ)*f x = x-x0 := by
      exact Int.mul_ediv_cancel' (hdiv x hx x0 hx0)
    have hinj : Set.InjOn f (A : Set ℤ) := by
      intro x hx y hy hxy
      have hh : x-x0 = y-x0 := by rw [← he x hx,← he y hy,hxy]
      omega
    have hfloor : 0 ≤ ⌊S/(d : ℝ)⌋ := Int.floor_nonneg.mpr (div_nonneg hS hdR.le)
    have hsubset : A.image f ⊆ Finset.Icc 0 ⌊S/(d : ℝ)⌋ := by
      intro t ht
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ht
      have hmin : x0 ≤ x := Finset.min'_le A x hx
      have hf0 : 0 ≤ f x := Int.ediv_nonneg (sub_nonneg.mpr hmin) hdZ.le
      have heR : (d : ℝ)*(f x : ℝ) = (x : ℝ)-(x0 : ℝ) := by exact_mod_cast he x hx
      have hfS : (f x : ℝ) ≤ S/(d : ℝ) := by
        apply (le_div_iff₀ hdR).mpr
        have hb := hbox x hx
        have hb0 := (hbox x0 hx0).1
        nlinarith
      exact Finset.mem_Icc.mpr ⟨hf0,Int.le_floor.mpr hfS⟩
    have hc : A.card ≤ (Finset.Icc (0 : ℤ) ⌊S/(d : ℝ)⌋).card := by
      rw [← Finset.card_image_of_injOn hinj]
      exact Finset.card_le_card hsubset
    have hi : ((Finset.Icc (0 : ℤ) ⌊S/(d : ℝ)⌋).card : ℝ) =
        (⌊S/(d : ℝ)⌋ : ℝ)+1 := by
      have hh := Int.card_Icc_of_le 0 ⌊S/(d : ℝ)⌋ (show (0 : ℤ) ≤ ⌊S/(d : ℝ)⌋+1 by omega)
      simp only [sub_zero] at hh
      exact_mod_cast hh
    calc
      (A.card : ℝ) ≤ ((Finset.Icc (0 : ℤ) ⌊S/(d : ℝ)⌋).card : ℝ) := by exact_mod_cast hc
      _ = (⌊S/(d : ℝ)⌋ : ℝ)+1 := hi
      _ ≤ S/(d : ℝ)+1 := add_le_add (Int.floor_le _) le_rfl
  · rw [Finset.not_nonempty_iff_eq_empty.mp hA]
    simp only [Finset.card_empty,Nat.cast_zero]
    positivity

theorem PrimitiveIntegerLine.denominator_dvd_x_difference (l : PrimitiveIntegerLine)
    (p q : ℤ × ℤ) (hp : l.Contains p) (hq : l.Contains q) :
    (l.denominator : ℤ) ∣ p.1-q.1 := by
  have he : l.slope*(p.1-q.1) = (l.denominator : ℤ)*(p.2-q.2) := by
    unfold Contains at hp hq
    linear_combination hq-hp
  have hg : Int.gcd (l.denominator : ℤ) l.slope = 1 := by
    simpa [Int.gcd_def] using l.reduced.symm.gcd_eq_one
  apply Int.dvd_of_dvd_mul_right_of_gcd_one (a := (l.denominator : ℤ)) (b := l.slope)
  · rw [he]
    exact dvd_mul_right _ _
  · exact hg

end ErdosRichLine

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_BoxHeightBudget
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseBoxHeight

theorem small_power_height {z Sq R Z : ℝ} (hz : 4 ≤ z)
    (hSq : 0 ≤ Sq) (hR : 0 ≤ R) (hZ : 0 ≤ Z)
    (hSqz : Sq ≤ z^((21:ℝ)/10)) (hRz : R ≤ z^((1:ℝ)/100))
    (hZz : Z ≤ z^((1:ℝ)/100)) : 2*Sq*R^2*Z^20 ≤ z^3 := by
  have hz0 : 0 ≤ z := by linarith
  have hzpos : 0 < z := by linarith
  have htwo : (2:ℝ) ≤ z^((1:ℝ)/2) := by
    rw [← Real.sqrt_eq_rpow]
    exact (Real.le_sqrt (by norm_num) hz0).mpr (by norm_num; exact hz)
  have hRp : R^2 ≤ z^((2:ℝ)/100) := by
    calc
      _ ≤ (z^((1:ℝ)/100))^2 := by gcongr
      _ = _ := by rw [← Real.rpow_mul_natCast hz0]; norm_num
  have hZp : Z^20 ≤ z^((20:ℝ)/100) := by
    calc
      _ ≤ (z^((1:ℝ)/100))^20 := by gcongr
      _ = _ := by rw [← Real.rpow_mul_natCast hz0]; norm_num
  calc
    _ ≤ z^((1:ℝ)/2)*z^((21:ℝ)/10)*z^((2:ℝ)/100)*z^((20:ℝ)/100) := by gcongr
    _ = z^((141:ℝ)/50) := by
      rw [← Real.rpow_add hzpos,← Real.rpow_add hzpos,← Real.rpow_add hzpos]
      norm_num
    _ ≤ z^3 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ z)
        (by norm_num : (141:ℝ)/50 ≤ 3)
      norm_num at h ⊢
      exact h

theorem uniform_box_height (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ z : ℝ in atTop, 1 < z ∧ ∀ Sq R B xi q : ℝ,
      0 ≤ Sq → 0 ≤ R → 1 ≤ B → B ≤ Real.log z → 0 ≤ xi → xi ≤ 1 →
      0 < q → q ≤ z^2 → Sq/q ≤ (1+xi)^(C*Real.log B) → R ≤ z^((1:ℝ)/100) →
      2*Sq*R^2*(sourceZ z)^20 ≤ z^3 := by
  filter_upwards [uniform_bin_inflation C hC,sourceZ_le_small_power,eventually_ge_atTop (4:ℝ)]
    with z hInfl hZ hz
  refine ⟨hInfl.1,?_⟩
  intro Sq R B xi q hSq hR hB hBL hxi0 hxi1 hq hqz hinfl hRz
  have hBpow := hInfl.2 B xi hB hBL hxi0 hxi1
  have hSqz : Sq ≤ z^((21:ℝ)/10) := by
    have hSqbound := (div_le_iff₀ hq).mp (hinfl.trans hBpow)
    calc
      _ ≤ z^((1:ℝ)/10)*q := hSqbound
      _ ≤ z^((1:ℝ)/10)*z^2 :=
        mul_le_mul_of_nonneg_left hqz (Real.rpow_nonneg (by linarith) _)
      _ = _ := by
        rw [← Real.rpow_natCast z 2,← Real.rpow_add (by linarith : 0 < z)]
        norm_num
  exact small_power_height hz hSq hR hZ.2.1.le hSqz hRz hZ.2.2

end ErdosInverseBoxHeight

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceSquareScale
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter
open scoped Topology
namespace ErdosSourcePolynomial
open ErdosInverseBoxHeight

theorem sourceZ_ge_one {z : ℝ} (hL : 1 ≤ Real.log z) : 1 ≤ sourceZ z := by
  apply Real.one_le_exp_iff.mpr
  exact div_nonneg (zero_le_one.trans hL) (Real.log_nonneg hL)

theorem square_scale_of_root_height {z Sq R : ℝ} (hSq : 0 ≤ Sq) (hR : 1 ≤ R)
    (hL : 1 ≤ Real.log z) (hheight : 2*Sq*R^2*(sourceZ z)^20 ≤ z^3) : Sq ≤ z^3 := by
  have hR2 : 1 ≤ R^2 := one_le_pow₀ hR
  have hZ20 : 1 ≤ (sourceZ z)^20 := one_le_pow₀ (sourceZ_ge_one hL)
  have hm : 1 ≤ R^2*(sourceZ z)^20 := one_le_mul_of_one_le_of_one_le hR2 hZ20
  have hf : 1 ≤ 2*(R^2*(sourceZ z)^20) := by linarith
  calc
    Sq = Sq*1 := by ring
    _ ≤ Sq*(2*(R^2*(sourceZ z)^20)) := mul_le_mul_of_nonneg_left hf hSq
    _ = 2*Sq*R^2*(sourceZ z)^20 := by ring
    _ ≤ z^3 := hheight

theorem uniform_source_square_scale (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ z : ℝ in atTop, 2 ≤ z ∧ 1 ≤ Real.log z ∧ ∀ Sq R p q xi : ℝ,
      1 ≤ p → 0 < q → p*q ≤ (sourceY z : ℝ) →
      1 ≤ Sq/q → Sq/q ≤ (1+xi)^(C*Real.log (sourceB z)) →
      1 ≤ R → R ≤ z^((1 : ℝ)/100) → 0 ≤ xi → xi ≤ 1 → Sq ≤ z^3 := by
  filter_upwards [uniform_box_height C hC,source_B_bounds,
    Real.tendsto_log_atTop.eventually_ge_atTop 1,eventually_ge_atTop (2 : ℝ)] with z hheight hB hL hz
  refine ⟨hz,hL,?_⟩
  intro Sq R p q xi hp hq hpq hSqratio hinfl hR hRhi hxi0 hxi1
  have hSq : 0 ≤ Sq := hq.le.trans ((one_le_div hq).mp hSqratio)
  have hqz := source_cofactor_le_square hL hp hq.le hpq
  have hh := hheight.2 Sq R (sourceB z) xi q hSq (zero_le_one.trans hR)
    hB.2.1 hB.2.2 hxi0 hxi1 hq hqz hinfl hRhi
  exact square_scale_of_root_height hSq hR hL hh

end ErdosSourcePolynomial

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceValueSmallness
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Filter
open scoped Topology
namespace ErdosSourcePolynomial

theorem eventual_value_budget_small (alpha delta : ℝ) (ha : 0 < alpha) (hd : 0 < delta) :
    ∀ᶠ z : ℝ in atTop, 2 ≤ z ∧ 1 ≤ Real.log z ∧ ∀ R : ℝ, z^alpha ≤ R →
      4*Real.log z+Real.log 4+8*R/(Real.log z)^4+3*R/Real.log z < delta*R := by
  have hlo := (isLittleO_log_rpow_rpow_atTop (1 : ℝ) ha).bound (by positivity : 0 < delta/16)
  have hlarge := Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (44/delta))
  have hpow := (tendsto_rpow_atTop ha).eventually_ge_atTop (4*Real.log 4/delta)
  filter_upwards [hlo,hlarge,hpow,eventually_ge_atTop (2 : ℝ)] with z hsmall hL hP hz
  have hL1 : 1 ≤ Real.log z := (le_max_left _ _).trans hL
  have hL0 : 0 < Real.log z := by linarith
  have hz0 : 0 < z := by linarith
  have hpow0 : 0 < z^alpha := Real.rpow_pos_of_pos hz0 _
  have hlog : Real.log z ≤ delta/16*z^alpha := by
    simpa only [Real.rpow_one,Real.norm_eq_abs,abs_of_pos hL0,abs_of_pos hpow0] using hsmall
  have hconst : Real.log 4 ≤ delta/4*z^alpha := by
    have h := (div_le_iff₀ hd).mp hP
    nlinarith only [h]
  have h44 : 44/delta ≤ Real.log z := (le_max_right _ _).trans hL
  have hfrac : 11/Real.log z ≤ delta/4 := by
    apply (div_le_iff₀ hL0).mpr
    have h := (div_le_iff₀ hd).mp h44
    nlinarith only [h]
  have hLpow : Real.log z ≤ (Real.log z)^4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hL1 (by norm_num : (1 : ℕ) ≤ 4)
  have h8 : 8/(Real.log z)^4 ≤ 8/Real.log z :=
    div_le_div_of_nonneg_left (by norm_num) hL0 hLpow
  have hsum : 8/(Real.log z)^4+3/Real.log z ≤ delta/4 := by
    calc
      _ ≤ 8/Real.log z+3/Real.log z := add_le_add h8 le_rfl
      _ = 11/Real.log z := by ring
      _ ≤ _ := hfrac
  refine ⟨hz,hL1,?_⟩
  intro R hR
  have hR0 : 0 < R := hpow0.trans_le hR
  have haR : 4*Real.log z ≤ delta/4*R := by
    have h := mul_le_mul_of_nonneg_left hR (by positivity : 0 ≤ delta/4)
    nlinarith only [h,hlog]
  have hbR : Real.log 4 ≤ delta/4*R := hconst.trans (mul_le_mul_of_nonneg_left hR (by positivity))
  have hcR : 8*R/(Real.log z)^4+3*R/Real.log z ≤ delta/4*R := by
    convert! mul_le_mul_of_nonneg_right hsum hR0.le using 1
    all_goals try with_reducible_and_instances rfl
    ring
  nlinarith [mul_pos hd hR0]

end ErdosSourcePolynomial

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_IntegerSlopeConstruction
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosAuxiliaryPolynomial

theorem residueSlopes_card_le (P : Finset ℕ) (T : P → Finset ℤ) (p : P) :
    (residueSlopes P T p).card ≤ (T p).card := by
  classical
  exact Finset.card_image_le

theorem exists_integer_slope_polynomial (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p)
    (T : P → Finset ℤ) (a : P → ℤ) (D : ℕ) :
    ∃ (Q : MvPolynomial (Fin 2) ℤ) (H : ℕ), Q ≠ 0 ∧ Q.totalDegree ≤ D ∧ 0 < H ∧
      (∀ m : Fin 2 →₀ ℕ, |Q.coeff m| ≤ (H : ℤ)) ∧
      (∀ p : P, ∀ s ∈ T p,
        lineSub (Int.castRingHom (ZMod p.val)) (a p : ZMod p.val) (s : ZMod p.val) Q = 0) ∧
      Real.log (2*(H : ℝ)) ≤ Real.log 4+2/((D : ℝ)+2)*
        (∑ p : P, ((T p).card : ℝ)*Real.log (p.val : ℝ)) := by
  classical
  obtain ⟨Q,H,hQ,hD,hH,hcoeff,hline,hlog⟩ := exists_small_line_polynomial P hP
    (residueSlopes P T) (fun p => (a p : ZMod p.val)) D
  refine ⟨Q,H,hQ,hD,hH,hcoeff,?_,?_⟩
  · intro p s hs
    apply hline p ⟨(s : ZMod p.val),?_⟩
    exact Finset.mem_image.mpr ⟨s,hs,rfl⟩
  · have hc : logarithmicCost P (residueSlopes P T) ≤
        ∑ p : P, ((T p).card : ℝ)*Real.log (p.val : ℝ) :=
      logarithmicCost_le_budget P hP (residueSlopes P T) (fun p => ((T p).card : ℝ))
        (fun p => by exact_mod_cast residueSlopes_card_le P T p)
    exact hlog.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hc (by positivity)))

theorem exists_integer_auxiliary_polynomial_lifting (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (T : P → Finset ℤ) (a : P → ℤ) (D : ℕ) :
    ∃ (Q : MvPolynomial (Fin 2) ℤ) (H : ℕ), Q ≠ 0 ∧ Q.totalDegree ≤ D ∧ 0 < H ∧
      (∀ m : Fin 2 →₀ ℕ, |Q.coeff m| ≤ (H : ℤ)) ∧
      (∀ p : P, ∀ s ∈ T p,
        lineSub (Int.castRingHom (ZMod p.val)) (a p : ZMod p.val) (s : ZMod p.val) Q = 0) ∧
      Real.log (2*(H : ℝ)) ≤ Real.log 4+2/((D : ℝ)+2)*
        (∑ p : P, ((T p).card : ℝ)*Real.log (p.val : ℝ)) ∧
      ∀ (S : ℝ) (x y : ℤ), (0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ S) →
        (0 ≤ (y : ℝ) ∧ (y : ℝ) ≤ S) →
        ∀ (I : Finset ℕ) (hIP : I ⊆ P),
          (∀ p : I, IntegerLineIncidence P T a x y ⟨p.val,hIP p.property⟩) →
          logarithmicValueBudget D H S < ∑ p ∈ I, Real.log (p : ℝ) →
          MvPolynomial.eval ![x,y] Q = 0 := by
  classical
  obtain ⟨Q,H,hQ,hD,hH,hcoeff,hline,hlog⟩ :=
    exists_integer_slope_polynomial P (fun p hp => (hP p hp).pos) T a D
  refine ⟨Q,H,hQ,hD,hH,hcoeff,hline,hlog,?_⟩
  intro S x y hx hy I hIP hinc hlarge
  unfold IntegerLineIncidence at hinc
  choose s hsmem hs using hinc
  apply value_zero_of_log_prime_budget Q D H hD hcoeff hH S x y hx hy I
    (fun p hp => hP p (hIP hp))
    (fun p : I => (a ⟨p.val,hIP p.property⟩ : ZMod p.val))
    (fun p : I => (s p : ZMod p.val))
  · exact fun p => hline ⟨p.val,hIP p.property⟩ (s p) (hsmem p)
  · exact hs
  · exact hlarge

end ErdosAuxiliaryPolynomial

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_OriginalSourcePolynomial
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosSourcePolynomial
open ErdosAuxiliaryPolynomial

theorem source_coefficient_log_bound {z R cost : ℝ} {H : ℕ}
    (hR : 0 < R) (hL : 0 < Real.log z) (hcost0 : 0 ≤ cost)
    (hcost : cost ≤ 4*R^2/(Real.log z)^6)
    (hheight : Real.log (2*(H : ℝ)) ≤ Real.log 4+2/((sourceDegree z R : ℝ)+2)*cost) :
    Real.log (2*(H : ℝ)) ≤ Real.log 4+8*R/(Real.log z)^4 := by
  apply hheight.trans
  apply add_le_add le_rfl
  calc
    _ ≤ (2*(Real.log z)^2/R)*cost := mul_le_mul_of_nonneg_right (source_degree_factor hR hL) hcost0
    _ ≤ (2*(Real.log z)^2/R)*(4*R^2/(Real.log z)^6) :=
      mul_le_mul_of_nonneg_left hcost (by positivity)
    _ = 8*R/(Real.log z)^4 := by field_simp <;> ring

theorem source_value_log_budget {z R S : ℝ} {H : ℕ}
    (hz : 2 ≤ z) (hR : 0 < R) (hRz : R ≤ z) (hL : 1 ≤ Real.log z)
    (hH : 0 < H) (hS : S ≤ z^3)
    (hheight : Real.log (2*(H : ℝ)) ≤ Real.log 4+8*R/(Real.log z)^4) :
    logarithmicValueBudget (sourceDegree z R) H S ≤
      4*Real.log z+Real.log 4+8*R/(Real.log z)^4+3*R/Real.log z := by
  have hL0 : 0 < Real.log z := by linarith
  have hN := source_dimension_log_bound hz hR.le hRz hL
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH
  have hlogH : Real.log (H : ℝ) ≤ Real.log 4+8*R/(Real.log z)^4 :=
    (Real.log_le_log hH0 (by linarith : (H : ℝ) ≤ 2*(H : ℝ))).trans hheight
  have hM0 : (0 : ℝ) < max 1 S := zero_lt_one.trans_le (le_max_left _ _)
  have hM : max 1 S ≤ z^3 := max_le (one_le_pow₀ (by linarith : 1 ≤ z)) hS
  have hlogM : Real.log (max 1 S) ≤ 3*Real.log z := by
    simpa only [Real.log_pow,Nat.cast_ofNat] using Real.log_le_log hM0 hM
  have hlogM0 : 0 ≤ Real.log (max 1 S) := Real.log_nonneg (le_max_left _ _)
  have hprod : (sourceDegree z R : ℝ)*Real.log (max 1 S) ≤ 3*R/Real.log z := by
    calc
      _ ≤ (R/(Real.log z)^2)*(3*Real.log z) :=
        mul_le_mul (sourceDegree_le hR.le) hlogM hlogM0 (by positivity)
      _ = _ := by field_simp
  unfold logarithmicValueBudget
  linarith

end ErdosSourcePolynomial

end

section

open _root_.Filter
open scoped Topology
namespace ErdosSourcePolynomial
open ErdosAuxiliaryPolynomial ErdosInversePrimeBin

theorem uniform_polynomial_for_bounded_square (eta alpha c : ℝ)
    (heta : 0 < eta) (halpha : 0 < alpha) (hc : 0 < c) :
    ∀ᶠ z : ℝ in atTop, 2 ≤ z ∧ 1 ≤ Real.log z ∧ ∀ R xi S : ℝ,
      z^alpha ≤ R → R ≤ z^((1 : ℝ)/100) → eta ≤ xi → xi ≤ 1 → S ≤ z^3 →
      ∀ (T : primeBin R xi → Finset ℤ) (a : primeBin R xi → ℤ),
        (∑ p : primeBin R xi, ((T p).card : ℝ)) ≤ ((primeBin R xi).card : ℝ)*R/(Real.log z)^6 →
        Nonempty (SourcePolynomialWitness z R xi S eta c T a) := by
  obtain ⟨R0,hR0⟩ := Filter.eventually_atTop.mp (uniform_prime_bin_budgets heta)
  have hbig := (tendsto_rpow_atTop halpha).eventually_ge_atTop R0
  filter_upwards [eventual_value_budget_small alpha (c*eta/4) halpha (by positivity),hbig]
    with z hsmall hbig
  refine ⟨hsmall.1,hsmall.2.1,?_⟩
  intro R xi S hRlo hRhi hxi hxi1 hS T a hthin
  have hbin := hR0 R (hbig.trans hRlo)
  have hR : 0 < R := by linarith [hbin.1]
  have hL : 0 < Real.log z := by linarith [hsmall.2.1]
  have hxi0 : 0 ≤ xi := heta.le.trans hxi
  have hRz : R ≤ z := by
    apply hRhi.trans
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by linarith [hsmall.1] : 1 ≤ z) (by norm_num : (1 : ℝ)/100 ≤ 1)
  have hprime : ∀ p ∈ primeBin R xi, Nat.Prime p := fun p hp =>
    ((mem_primeBin hR.le hxi0 p).mp hp).1
  obtain ⟨Q,H,hQ,hD,hH,hcoeff,hline,hheight,hlift⟩ :=
    exists_integer_auxiliary_polynomial_lifting (primeBin R xi) hprime T a (sourceDegree z R)
  have hbudgets := hbin.2 xi hxi hxi1
  have hcost := hbudgets.1 (Real.log z) hL T hthin
  have hcost0 : 0 ≤ ∑ p : primeBin R xi, ((T p).card : ℝ)*Real.log (p.val : ℝ) := by
    apply Finset.sum_nonneg
    intro p hp
    apply mul_nonneg (Nat.cast_nonneg _)
    apply Real.log_nonneg
    exact_mod_cast Nat.succ_le_of_lt (hprime p p.property).pos
  have hheight' := source_coefficient_log_bound hR hL hcost0 hcost hheight
  have hvalue := source_value_log_budget hsmall.1 hR hRz hsmall.2.1 hH hS hheight'
  have hstrict : logarithmicValueBudget (sourceDegree z R) H S < c*eta*R/4 := by
    have h := hvalue.trans_lt (hsmall.2.2 R hRlo)
    convert! h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  refine ⟨{
    polynomial := Q
    height := H
    nonzero := hQ
    degree_le := hD
    height_pos := hH
    coefficient_bound := hcoeff
    line_vanishing := hline
    height_bound := hheight'
    value_budget := hstrict
    rich_vanishing := ?_ }⟩
  intro x y hx hy I hIP hrich hinc
  exact hlift S x y hx hy I hIP hinc (hstrict.trans_le (hbudgets.2 c hc.le I hIP hrich))

end ErdosSourcePolynomial

end

section

open _root_.Filter
open scoped Topology
namespace ErdosSourcePolynomial
open ErdosAuxiliaryPolynomial ErdosInversePrimeBin ErdosInverseBoxHeight

theorem uniform_original_source_polynomial (C eta alpha c : ℝ)
    (hC : 0 ≤ C) (heta : 0 < eta) (halpha : 0 < alpha) (hc : 0 < c) :
    ∀ᶠ z : ℝ in atTop, 2 ≤ z ∧ ∀ S R p q xi : ℝ,
      1 ≤ p → 0 < q → p*q ≤ (sourceY z : ℝ) →
      1 ≤ S/q → S/q ≤ (1+xi)^(C*Real.log (sourceB z)) →
      z^alpha ≤ R → R ≤ z^((1 : ℝ)/100) → eta ≤ xi → xi ≤ 1 →
      ∀ (T : primeBin R xi → Finset ℤ) (a : primeBin R xi → ℤ),
        (∑ r : primeBin R xi, ((T r).card : ℝ)) ≤ ((primeBin R xi).card : ℝ)*R/(Real.log z)^6 →
        Nonempty (SourcePolynomialWitness z R xi S eta c T a) := by
  filter_upwards [uniform_polynomial_for_bounded_square eta alpha c heta halpha hc,
    uniform_source_square_scale C hC] with z hpoly hscale
  refine ⟨hpoly.1,?_⟩
  intro S R p q xi hp hq hpq hratio hinfl hRlo hRhi hxi hxi1 T a hthin
  have hR1 : 1 ≤ R := (Real.one_le_rpow (by linarith [hpoly.1] : 1 ≤ z) halpha.le).trans hRlo
  have hxi0 : 0 ≤ xi := heta.le.trans hxi
  have hS := hscale.2.2 S R p q xi hp hq hpq hratio hinfl hR1 hRhi hxi0 hxi1
  exact hpoly.2.2 R xi S hRlo hRhi hxi hxi1 hS T a hthin

end ErdosSourcePolynomial

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_LineCoordinateCounts
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosRichLine
open ErdosConvexGraph

theorem coordinate_card_le_div (X : Finset (ℤ × ℤ)) (f : ℤ × ℤ → ℤ)
    (hinj : Set.InjOn f (X : Set (ℤ × ℤ))) (S : ℝ) (hS : 0 ≤ S)
    (d : ℕ) (hd : 0 < d) (hbox : ∀ p ∈ X, 0 ≤ (f p : ℝ) ∧ (f p : ℝ) ≤ S)
    (hdiv : ∀ p ∈ X, ∀ q ∈ X, (d : ℤ) ∣ f p-f q) :
    (X.card : ℝ) ≤ S/(d : ℝ)+1 := by
  classical
  have hh := congruent_integer_set_card (X.image f) S hS d hd
    (by rintro x hx;obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx;exact hbox p hp)
    (by
      intro x hx y hy
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hy
      exact hdiv p hp q hq)
  rwa [Finset.card_image_of_injOn hinj] at hh

theorem PrimitiveIntegerLine.slope_dvd_y_difference (l : PrimitiveIntegerLine)
    (p q : ℤ × ℤ) (hp : l.Contains p) (hq : l.Contains q) :
    (l.slope.natAbs : ℤ) ∣ p.2-q.2 := by
  have he : (l.denominator : ℤ)*(p.2-q.2) = l.slope*(p.1-q.1) := by
    unfold Contains at hp hq
    linear_combination hp-hq
  have hg : Int.gcd l.slope (l.denominator : ℤ) = 1 := by
    simpa [Int.gcd_def] using l.reduced.gcd_eq_one
  have hh : l.slope ∣ p.2-q.2 := Int.dvd_of_dvd_mul_right_of_gcd_one
    (by rw [he];exact dvd_mul_right _ _) hg
  simpa only [Int.natCast_natAbs,abs_dvd] using hh

theorem PrimitiveIntegerLine.y_injective (l : PrimitiveIntegerLine) (ha : l.slope ≠ 0)
    (X : Finset (ℤ × ℤ)) (hline : ∀ p ∈ X, l.Contains p) :
    Set.InjOn Prod.snd (X : Set (ℤ × ℤ)) := by
  intro p hp q hq he
  have hp' := hline p hp
  have hq' := hline q hq
  unfold Contains at hp' hq'
  have hm : l.slope*p.1 = l.slope*q.1 := by rw [he] at hp';omega
  exact Prod.ext (mul_left_cancel₀ ha hm) he

theorem PrimitiveIntegerLine.denominator_point_count (l : PrimitiveIntegerLine)
    (X : Finset (ℤ × ℤ)) (S : ℝ) (hS : 0 ≤ S)
    (hinj : Set.InjOn Prod.fst (X : Set (ℤ × ℤ)))
    (hbox : ∀ p ∈ X, InSquare S p) (hline : ∀ p ∈ X, l.Contains p) :
    (X.card : ℝ) ≤ S/(l.denominator : ℝ)+1 :=
  coordinate_card_le_div X Prod.fst hinj S hS l.denominator l.denominator_pos
    (fun p hp => (hbox p hp).1)
    (fun p hp q hq => l.denominator_dvd_x_difference p q (hline p hp) (hline q hq))

theorem PrimitiveIntegerLine.slope_point_count (l : PrimitiveIntegerLine) (ha : l.slope ≠ 0)
    (X : Finset (ℤ × ℤ)) (S : ℝ) (hS : 0 ≤ S)
    (hbox : ∀ p ∈ X, InSquare S p) (hline : ∀ p ∈ X, l.Contains p) :
    (X.card : ℝ) ≤ S/(l.slope.natAbs : ℝ)+1 :=
  coordinate_card_le_div X Prod.snd (l.y_injective ha X hline) S hS l.slope.natAbs
    (Int.natAbs_pos.mpr ha) (fun p hp => (hbox p hp).2)
    (fun p hp q hq => l.slope_dvd_y_difference p q (hline p hp) (hline q hq))

end ErdosRichLine

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_RichLineHeights
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosRichLine
open ErdosConvexGraph

theorem spacing_implies_height (N S d : ℝ) (hN : 2 ≤ N) (hd : 0 < d)
    (hcount : N ≤ S/d+1) : d ≤ 2*S/N := by
  have hstep : (N-1)*d ≤ S := (le_div_iff₀ hd).mp (by linarith)
  have hNp : 0 < N := by linarith
  apply (le_div_iff₀ hNp).mpr
  nlinarith

theorem PrimitiveIntegerLine.height_bounds (l : PrimitiveIntegerLine)
    (X : Finset (ℤ × ℤ)) (S : ℝ) (hS : 0 ≤ S) (hN : 2 ≤ X.card)
    (hinj : Set.InjOn Prod.fst (X : Set (ℤ × ℤ)))
    (hbox : ∀ p ∈ X, InSquare S p) (hline : ∀ p ∈ X, l.Contains p) :
    (l.denominator : ℝ) ≤ 2*S/(X.card : ℝ) ∧
      |(l.slope : ℝ)| ≤ 2*S/(X.card : ℝ) ∧
      |(l.intercept : ℝ)| ≤ 4*S^2/(X.card : ℝ) := by
  have hNR : (2 : ℝ) ≤ X.card := by exact_mod_cast hN
  have hNp : (0 : ℝ) < X.card := by linarith
  have hD : (l.denominator : ℝ) ≤ 2*S/(X.card : ℝ) :=
    spacing_implies_height _ _ _ hNR (by exact_mod_cast l.denominator_pos)
      (l.denominator_point_count X S hS hinj hbox hline)
  have hA : |(l.slope : ℝ)| ≤ 2*S/(X.card : ℝ) := by
    by_cases ha : l.slope = 0
    · simp only [ha,Int.cast_zero,abs_zero]
      positivity
    · have hh := spacing_implies_height _ _ _ hNR
        (show (0 : ℝ) < l.slope.natAbs by exact_mod_cast Int.natAbs_pos.mpr ha)
        (l.slope_point_count ha X S hS hbox hline)
      simpa only [Nat.cast_natAbs,Int.cast_abs] using hh
  obtain ⟨p,hp⟩ := Finset.card_pos.mp (show 0 < X.card by omega)
  have he : (l.intercept : ℝ) = (l.denominator : ℝ)*(p.2 : ℝ)-(l.slope : ℝ)*(p.1 : ℝ) := by
    have hh : l.intercept = (l.denominator : ℤ)*p.2-l.slope*p.1 := by
      have hl := hline p hp
      unfold Contains at hl
      linarith
    exact_mod_cast hh
  have hb := hbox p hp
  have hB : |(l.intercept : ℝ)| ≤ 4*S^2/(X.card : ℝ) := by
    calc
      |(l.intercept : ℝ)| ≤ |(l.denominator : ℝ)*(p.2 : ℝ)|+|(l.slope : ℝ)*(p.1 : ℝ)| := by
        rw [he]
        exact abs_sub _ _
      _ = (l.denominator : ℝ)*(p.2 : ℝ)+|(l.slope : ℝ)| *(p.1 : ℝ) := by
        rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg _),abs_of_nonneg hb.2.1,
          abs_of_nonneg hb.1.1]
      _ ≤ (2*S/(X.card : ℝ))*S+(2*S/(X.card : ℝ))*S := add_le_add
        (mul_le_mul hD hb.2.2 hb.2.1 (by positivity))
        (mul_le_mul hA hb.1.2 hb.1.1 (by positivity))
      _ = 4*S^2/(X.card : ℝ) := by ring
  exact ⟨hD,hA,hB⟩

end ErdosRichLine

end

section

namespace ErdosRichLine
open ErdosCriticalGeometry ErdosComplexCurveFactors ErdosConvexGraph

theorem exists_rich_line_with_heights (P : MV ℂ) (hP : P ≠ 0) (D : ℕ) (hD : P.totalDegree ≤ D)
    (S : ℝ) (hS : 0 ≤ S) (X : Finset (ℤ × ℤ)) (hX : X ⊆ complexSquarePoints P S)
    (hinj : Set.InjOn Prod.fst (X : Set (ℤ × ℤ))) (M : ℝ) (hM : 1 ≤ M)
    (hlarge : 182*(D : ℝ)^4*(1+S^((2 : ℝ)/3))+(D : ℝ)*M < (X.card : ℝ)) :
    ∃ (F : MV ℂ) (l : PrimitiveIntegerLine) (Y : Finset (ℤ × ℤ)),
      Irreducible F ∧ F ∣ P ∧ F.totalDegree = 1 ∧
      Y = X ∩ complexSquarePoints F S ∧ Y ⊆ X ∧ M < (Y.card : ℝ) ∧
      (∀ r ∈ Y, l.Contains r) ∧
      (l.denominator : ℝ) ≤ 2*S/(Y.card : ℝ) ∧
      |(l.slope : ℝ)| ≤ 2*S/(Y.card : ℝ) ∧
      |(l.intercept : ℝ)| ≤ 4*S^2/(Y.card : ℝ) := by
  classical
  obtain ⟨F,l,hF,hFP,hdeg,hcount,hline⟩ := exists_rich_primitive_line P hP D hD S hS X hX hinj M hM hlarge
  let Y := X ∩ complexSquarePoints F S
  have hsub : Y ⊆ X := Finset.inter_subset_left
  have htwo : 2 ≤ Y.card := by
    have hh : (1 : ℝ) < Y.card := lt_of_le_of_lt hM hcount
    have hh' : 1 < Y.card := by exact_mod_cast hh
    omega
  have hbox : ∀ r ∈ Y, InSquare S r := fun r hr =>
    ((mem_complexSquarePoints F S r).mp (Finset.mem_inter.mp hr).2).1
  have hxin : Set.InjOn Prod.fst (Y : Set (ℤ × ℤ)) :=
    fun _ hp _ hq he => hinj (hsub hp) (hsub hq) he
  obtain ⟨hden,hslope,hinter⟩ := l.height_bounds Y S hS htwo hxin hbox hline
  exact ⟨F,l,Y,hF,hFP,hdeg,rfl,hsub,hcount,hline,hden,hslope,hinter⟩

end ErdosRichLine

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_IntegerRichLine
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosRichLine
open ErdosCriticalGeometry ErdosComplexCurveFactors ErdosConvexGraph

theorem integerComplexification_degree (P : MV ℤ) :
    (integerComplexification P).totalDegree = P.totalDegree := by
  unfold integerComplexification MvPolynomial.totalDegree
  rw [MvPolynomial.support_map_of_injective P (Int.cast_injective)]

theorem integerComplexification_eval (P : MV ℤ) (p : ℤ × ℤ) :
    MvPolynomial.eval ![(p.1 : ℂ),(p.2 : ℂ)] (integerComplexification P) =
      (MvPolynomial.eval ![p.1,p.2] P : ℂ) := by
  have he : (Int.castRingHom ℂ) ∘ (![p.1,p.2] : Fin 2 → ℤ) = ![(p.1 : ℂ),(p.2 : ℂ)] := by
    funext i
    fin_cases i <;> rfl
  have h := MvPolynomial.map_eval (Int.castRingHom ℂ) ![p.1,p.2] P
  rw [he] at h
  exact h.symm

theorem integer_polynomial_rich_line (P : MV ℤ) (hP : P ≠ 0) (D : ℕ) (hD : P.totalDegree ≤ D)
    (S : ℝ) (hS : 0 ≤ S) (X : Finset (ℤ × ℤ))
    (hbox : ∀ p ∈ X, InSquare S p) (hzero : ∀ p ∈ X, MvPolynomial.eval ![p.1,p.2] P = 0)
    (hinj : Set.InjOn Prod.fst (X : Set (ℤ × ℤ))) (M : ℝ) (hM : 1 ≤ M)
    (hlarge : 182*(D : ℝ)^4*(1+S^((2 : ℝ)/3))+(D : ℝ)*M < (X.card : ℝ)) :
    ∃ (l : PrimitiveIntegerLine) (Y : Finset (ℤ × ℤ)),
      Y ⊆ X ∧ M < (Y.card : ℝ) ∧ (∀ r ∈ Y, l.Contains r) ∧
      (l.denominator : ℝ) ≤ 2*S/(Y.card : ℝ) ∧
      |(l.slope : ℝ)| ≤ 2*S/(Y.card : ℝ) ∧
      |(l.intercept : ℝ)| ≤ 4*S^2/(Y.card : ℝ) := by
  have hPc : integerComplexification P ≠ 0 := by
    intro h
    apply hP
    exact MvPolynomial.map_injective (Int.castRingHom ℂ) Int.cast_injective
      (by simpa only [integerComplexification,map_zero] using h)
  have hDc : (integerComplexification P).totalDegree ≤ D := by rwa [integerComplexification_degree]
  have hX : X ⊆ complexSquarePoints (integerComplexification P) S := by
    intro p hp
    apply (mem_complexSquarePoints _ S p).mpr
    refine ⟨hbox p hp,?_⟩
    rw [integerComplexification_eval,hzero p hp,Int.cast_zero]
  obtain ⟨F,l,Y,_hF,_hFP,_hdeg,_hY,hsub,hcard,hline,hden,hslope,hinter⟩ :=
    exists_rich_line_with_heights (integerComplexification P) hPc D hDc S hS X hX hinj M hM hlarge
  exact ⟨l,Y,hsub,hcard,hline,hden,hslope,hinter⟩

end ErdosRichLine

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_NonstructuredCounts
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter
open scoped Topology
namespace ErdosSourceLineBudget
open ErdosInverseBoxHeight ErdosSourcePolynomial ErdosAuxiliaryPolynomial ErdosInversePrimeBin
open ErdosRichLine ErdosConvexGraph

theorem uniform_original_rich_line_jb247_oai (C Cparent eta alpha c : ℝ)
    (hC : 0 ≤ C) (hCp : 0 ≤ Cparent) (heta : 0 < eta) (halpha : 0 < alpha) (hc : 0 < c) :
    ∀ᶠ z : ℝ in atTop, 2 ≤ z ∧ ∀ S R p q xi : ℝ,
      1 ≤ p → 0 < q → p*q ≤ (sourceY z : ℝ) →
      1 ≤ S/q → S/q ≤ (1+xi)^(C*Real.log (sourceB z)) →
      z^alpha ≤ R → R ≤ z^((1 : ℝ)/100) → eta ≤ xi → xi ≤ 1 → p ≤ 2*R →
      Real.logb (sourceW z) ((sourceY z : ℝ)/(p*q)) ≤ Cparent →
      ∀ (T : primeBin R xi → Finset ℤ) (a : primeBin R xi → ℤ),
        (∑ r : primeBin R xi, ((T r).card : ℝ)) ≤ ((primeBin R xi).card : ℝ)*R/(Real.log z)^6 →
        ∀ X : Finset (ℤ × ℤ), (∀ v ∈ X, InSquare S v) →
          Set.InjOn Prod.fst (X : Set (ℤ × ℤ)) →
          S/(sourceZ z)^4 ≤ (X.card : ℝ) → (∀ v ∈ X, RichPoint R xi c T a v) →
          ∃ (l : PrimitiveIntegerLine) (Y : Finset (ℤ × ℤ)), Y ⊆ X ∧
            S/(R*(sourceZ z)^6) < (Y.card : ℝ) ∧ (∀ v ∈ Y, l.Contains v) ∧
            (l.denominator : ℝ) ≤ 2*S/(Y.card : ℝ) ∧
            |(l.slope : ℝ)| ≤ 2*S/(Y.card : ℝ) ∧
            |(l.intercept : ℝ)| ≤ 4*S^2/(Y.card : ℝ) := by
  filter_upwards [uniform_original_source_polynomial C eta alpha c hC heta halpha hc,
    uniform_extraction_budget Cparent hCp] with z hz hb
  refine ⟨hz.1,?_⟩
  intro S R p q xi hp hq hpq hratio hinfl hRlo hRhi hxi hxi1 hpR hlen T a hthin
    X hbox hinj hcard hrich
  obtain ⟨w⟩ := hz.2 S R p q xi hp hq hpq hratio hinfl hRlo hRhi hxi hxi1 T a hthin
  have hp0 : 0 < p := by linarith
  have hqS : q ≤ S := (one_le_div hq).mp hratio
  have hS : 0 ≤ S := hq.le.trans hqS
  have hbudget := hb.2 p q R S hp0 hq hpR hRhi hqS hlen
  have hzero : ∀ v ∈ X, MvPolynomial.eval ![v.1,v.2] w.polynomial = 0 := by
    intro v hv
    obtain ⟨I,hIP,hI,hinc⟩ := hrich v hv
    exact w.rich_vanishing v.1 v.2 (hbox v hv).1 (hbox v hv).2 I hIP hI hinc
  exact integer_polynomial_rich_line w.polynomial w.nonzero (sourceDegree z R) w.degree_le
    S hS X hbox hzero hinj (S/(R*(sourceZ z)^6)) hbudget.2.1 (hbudget.2.2.trans_le hcard)

end ErdosSourceLineBudget

end

end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.ErdosSourceLineBudget.uniform_original_rich_line_jb247_oai := @OAI.Erdos970.ErdosSourceLineBudget.uniform_original_rich_line_jb247_oai
