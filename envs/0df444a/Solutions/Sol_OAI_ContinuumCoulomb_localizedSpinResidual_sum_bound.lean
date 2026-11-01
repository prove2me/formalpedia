-- Prove2me | solution 1 for OAI.ContinuumCoulomb.localizedSpinResidual_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:52:30.144929+00:00
-- url     : https://prove2.me/submissions/466ea32e-d77e-49b0-a41d-ec64c0349c90

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Nodup
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Hom.PowersetCard
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_OAIQ092A010

section
-- module Solutions.OAIQ092_CC.CoulombRadii_Packets_CoulombKernel
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace NeutralAtom
open scoped Convolution
open ContinuousLinearMap

theorem contDiff_regularizedKernel {ε : ℝ} (hε : ε ≠ 0) :
    ContDiff ℝ ∞ (regularizedKernel ε) := by
  apply ContDiff.rpow_const_of_ne
  · exact (contDiff_norm_sq ℝ).add contDiff_const
  · intro x
    exact (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hε)).ne'

theorem coulombKernel_eq_rpow (x : Position) :
    coulombKernel x = (‖x‖^2)^(-1/2 : ℝ) := by
  rw [← Real.rpow_natCast_mul (norm_nonneg x)]
  norm_num [coulombKernel, Real.rpow_neg_one]

theorem regularizedKernel_le {ε : ℝ} {x : Position} (hx : x ≠ 0) :
    regularizedKernel ε x ≤ coulombKernel x := by
  rw [coulombKernel_eq_rpow]
  exact Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos (norm_pos_iff.mpr hx))
    (le_add_of_nonneg_right (sq_nonneg ε)) (by norm_num)

theorem regularizedKernel_nonneg (ε : ℝ) (x : Position) :
    0 ≤ regularizedKernel ε x := by unfold regularizedKernel; positivity

theorem regularizedKernel_tendsto {ε : ℕ → ℝ} (hlim : Tendsto ε atTop (𝓝 0))
    {x : Position} (hx : x ≠ 0) :
    Tendsto (fun n => regularizedKernel (ε n) x) atTop (𝓝 (coulombKernel x)) := by
  have hh : Tendsto (fun n => ‖x‖^2+(ε n)^2) atTop (𝓝 (‖x‖^2)) := by
    simpa using tendsto_const_nhds.add (hlim.pow 2)
  have hr := hh.rpow tendsto_const_nhds
    (Or.inl (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)) : ‖x‖^2 ≠ 0 ∨ 0 < (-1/2:ℝ))
  simpa only [regularizedKernel, coulombKernel_eq_rpow] using hr

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_ConfigurationMeasurableEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb

open scoped Classical

open scoped Classical

section FiberContraction
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [SigmaFinite μ] [SigmaFinite ν]

omit [SigmaFinite μ] [SigmaFinite ν] in

lemma tensorPair_memLp [SFinite μ] {w : B → ℂ} {v : A → ℂ}
    (hw : MemLp w 2 ν) (hv : MemLp v 2 μ) :
    MemLp (fun z : B × A => w z.1 * v z.2) 2 (ν.prod μ) := by
  apply (memLp_two_iff_integrable_sq_norm
    (hw.aestronglyMeasurable.comp_fst.mul hv.aestronglyMeasurable.comp_snd)).2
  simpa only [Pi.mul_apply, norm_mul, mul_pow] using hw.norm.integrable_sq.mul_prod hv.norm.integrable_sq

end FiberContraction

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FormDomain_SmoothCompact
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.Coulomb.complexWindow_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma flatSpinOrbital_memLp (v : Space → Fin 2 → ℂ)
    (hv : ∀ s, MemLp (fun x => v x s) 2 volume) :
    MemLp (flatSpinOrbital v) 2 spinSpaceMeasure := by
  change MemLp (flatSpinOrbital v) 2 (Measure.count.prod volume)
  have hi (s : Fin 2) : MemLp (fun t : Fin 2 => if t = s then (1:ℂ) else 0) 2 Measure.count := by
    apply MemLp.of_bound (by fun_prop) 1
    exact ae_of_all _ (fun t => by split_ifs <;> norm_num)
  have H := memLp_finsetSum Finset.univ (fun (s : Fin 2) _ => tensorPair_memLp (hi s)
    ((hv s).comp_measurePreserving (PiLp.volume_preserving_toLp _)))
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  funext sx
  simp [flatSpinOrbital, ite_mul]

lemma flatSpinOrbital_inner (v u : Space → Fin 2 → ℂ)
    (hv : ∀ s, MemLp (fun x => v x s) 2 volume)
    (hu : ∀ s, MemLp (fun x => u x s) 2 volume) :
    (∫ a, star (flatSpinOrbital v a) * flatSpinOrbital u a ∂spinSpaceMeasure) =
      ∑ s : Fin 2, ∫ x : Space, star (v x s) * u x s := by
  have hI := (flatSpinOrbital_memLp v hv).star.integrable_mul (flatSpinOrbital_memLp u hu)
  change Integrable (fun a => star (flatSpinOrbital v a) * flatSpinOrbital u a)
    (Measure.count.prod volume) at hI
  change (∫ a, star (flatSpinOrbital v a) * flatSpinOrbital u a ∂(Measure.count.prod volume)) = _
  rw [integral_prod _ hI, integral_count]
  apply Finset.sum_congr rfl
  intro s _
  exact (show MeasurePreserving (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)) volume volume from
    PiLp.volume_preserving_toLp _).integral_comp' (fun x => star (v x s) * u x s)

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_Localization_TruncatedCoulomb
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.Coulomb.complexWindow_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
lemma coulombKernel_nonneg (x : Space) : 0 ≤ coulombKernel x := inv_nonneg.mpr (norm_nonneg _)
lemma coulombKernel_measurable : Measurable coulombKernel := measurable_norm.inv
lemma coulombKernel_integrableOn_ball (R : ℝ) : IntegrableOn coulombKernel (Metric.ball 0 R) := by
  apply integrableOn_ball_of_norm_le_rpow (C := 1) (α := 1) (by simp) (by norm_num)
  · exact Filter.Eventually.of_forall (fun x => by simp [coulombKernel, Real.rpow_neg_one])
  · exact coulombKernel_measurable.aestronglyMeasurable

lemma truncatedCoulomb_integrable (R : ℝ) : Integrable (truncatedCoulomb R) :=
  (coulombKernel_integrableOn_ball R).integrable_indicator measurableSet_ball

lemma coulomb_integrand_bound {f : Space → ℝ} {M R : ℝ} (hf0 : ∀ y, 0 ≤ f y)
    (hfM : ∀ y, f y ≤ M) (hR : 0 < R) (x y : Space) :
    coulombKernel (x-y) * f y ≤ M * truncatedCoulomb R (x-y) + R⁻¹ * f y := by
  by_cases h : x-y ∈ Metric.ball (0:Space) R
  · rw [truncatedCoulomb, Set.indicator_of_mem h]
    have H := mul_le_mul_of_nonneg_left (hfM y) (coulombKernel_nonneg (x-y))
    linarith [mul_nonneg (inv_nonneg.mpr hR.le) (hf0 y)]
  · rw [truncatedCoulomb, Set.indicator_of_notMem h, mul_zero, zero_add]
    have hn : R ≤ ‖x-y‖ := by simpa [Metric.mem_ball, dist_zero_right] using h
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hR hn) (hf0 y)

lemma coulomb_convolution_integrable {f : Space → ℝ} (hf : Integrable f) (hm : Measurable f)
    {M R : ℝ} (hf0 : ∀ y, 0 ≤ f y) (hfM : ∀ y, f y ≤ M) (hR : 0 < R) (x : Space) :
    Integrable (fun y => coulombKernel (x-y) * f y) := by
  have hnear := (truncatedCoulomb_integrable R).comp_sub_left x
  apply ((hnear.const_mul M).add (hf.const_mul R⁻¹)).mono'
    (((coulombKernel_measurable.comp (measurable_const.sub measurable_id)).mul hm).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun y => by
    change ‖coulombKernel (x-y) * f y‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (coulombKernel_nonneg _) (hf0 _))]
    exact coulomb_integrand_bound hf0 hfM hR x y)

lemma coulomb_signed_convolution_integrable {f : Space → ℝ} (hf : Integrable f)
    (hm : Measurable f) {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) (x : Space) :
    Integrable (fun y => coulombKernel (x-y)*f y) := by
  have h := coulomb_convolution_integrable hf.norm hm.norm (fun y => norm_nonneg _) hM
    (by norm_num : (0:ℝ) < 1) x
  apply h.mono' (((coulombKernel_measurable.comp (by fun_prop)).mul hm).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun y => by
    change ‖coulombKernel (x-y)*f y‖ ≤ coulombKernel (x-y)*‖f y‖
    rw [norm_mul, Real.norm_of_nonneg (coulombKernel_nonneg _)] )

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombGramApprox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative local duality for overlapping densities. The compact local
tests are disjoint; the electron density packets need not be disjoint. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace ContinuumCoulomb

theorem dualMatrix_quadratic_lower {m : ℕ} (A : Fin m → Fin m → ℝ)
    {a delta : ℝ} (hdelta : 0 ≤ delta) (hdiag : ∀ i, a ≤ A i i)
    (hoff : ∀ i j, i ≠ j → |A i j| ≤ delta) (d : Fin m → ℝ) :
    (a - m * delta) * ∑ i, d i ^ 2 ≤ ∑ i, ∑ j, A i j * d i * d j := by
  classical
  have hpoint (i j : Fin m) :
      (if i = j then a * d i ^ 2 else 0) - delta / 2 * (d i ^ 2 + d j ^ 2) ≤
        A i j * d i * d j := by
    by_cases hij : i = j
    · subst j
      rw [ite_eq_left rfl]
      have h := mul_le_mul_of_nonneg_right (hdiag i) (sq_nonneg (d i))
      have hzero := mul_nonneg hdelta (sq_nonneg (d i))
      nlinarith
    · rw [ite_eq_right hij, zero_sub]
      have hprod : |A i j * d i * d j| ≤ delta * (|d i| * |d j|) := by
        calc
          _ = |A i j| * (|d i| * |d j|) := by simp only [abs_mul]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (hoff i j hij)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      have htwo : 2 * (|d i| * |d j|) ≤ d i ^ 2 + d j ^ 2 := by
        nlinarith [sq_nonneg (|d i| - |d j|), sq_abs (d i), sq_abs (d j)]
      have hscaled := mul_le_mul_of_nonneg_left htwo hdelta
      nlinarith [neg_abs_le (A i j * d i * d j)]
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) fun j _ => hpoint i j
  have hrow (i : Fin m) :
      (∑ j, ((if i = j then a * d i ^ 2 else 0) - delta / 2 * (d i ^ 2 + d j ^ 2))) =
      a * d i ^ 2 - delta / 2 * ((m : ℝ) * d i ^ 2 + ∑ j, d j ^ 2) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp_rw [hrow] at hsum
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  convert hsum using 1
  all_goals try with_reducible_and_instances rfl
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarModeProperties
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positivity, finite L² normalization and compact support of the actual
manufactured planar potential. The differential eigen-equation and gap are
not assumed by these declarations. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem normalizedPlanarMode_normalized : (∫ r, normalizedPlanarMode r ^ 2) = 1 := by
  simp_rw [normalizedPlanarMode, div_pow]
  rw [integral_div, Real.sq_sqrt planarResolventMode_square_integral_positive.le,
    div_self planarResolventMode_square_integral_positive.ne']

theorem manufacturedPlanarWell_nonpositive (r : PlanarPosition) : manufacturedPlanarWell r ≤ 0 :=
  div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (planarForcing_nonnegative r))
    (mul_nonneg (by norm_num) (planarResolventMode_positive r).le)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_VerticalMode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual normalized Gaussian in the transverse direction. -/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace ContinuumCoulomb

theorem verticalMode_normalized {freq : ℝ} (hfreq : 0 < freq) :
    (∫ z : ℝ, verticalMode freq z ^ 2) = 1 := by
  simp_rw [verticalMode_square hfreq]
  rw [integral_div, integral_gaussian, div_self]
  exact (Real.sqrt_pos.mpr (div_pos Real.pi_pos hfreq)).ne'

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedModes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual localized modes in planar/transverse coordinates. The measure is
the product of planar Euclidean volume and one-dimensional Lebesgue measure.
The split Laplacian below is the sum of the three coordinate derivatives. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem localizedMode_normalized {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) : (∫ p, localizedMode freq u p ^ 2) = 1 := by
  simp_rw [localizedMode, mul_pow]
  rw [Measure.volume_eq_prod,
    integral_prod_mul (fun r => normalizedPlanarMode (r - u) ^ 2)
      (fun z => verticalMode freq z ^ 2),
    integral_sub_right_eq_self (fun r => normalizedPlanarMode r ^ 2) u,
    normalizedPlanarMode_normalized, verticalMode_normalized hfreq, one_mul]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_SplitCoordinates
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Volume-preserving planar/transverse coordinates for the actual
three-dimensional Coulomb space. The intermediate product has its Euclidean
L² norm; the final ordinary product carries the same product volume. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem positionSplitCoordinates_integral (f : SplitPosition → ℝ) :
    (∫ x : Position, f (positionSplitCoordinates x)) = ∫ p, f p :=
  positionSplitCoordinates_measurePreserving.integral_comp
    positionSplitCoordinates.toHomeomorph.measurableEmbedding f

theorem positionSplitCoordinates_norm_sq (x : Position) :
    ‖x‖ ^ 2 = ‖(positionSplitCoordinates x).1‖ ^ 2 +
      (positionSplitCoordinates x).2 ^ 2 := by
  change ‖x‖ ^ 2 = ‖(positionSplitIsometry x).fst‖ ^ 2 + (positionSplitIsometry x).snd ^ 2
  have h := WithLp.prod_norm_sq_eq_of_L2 (positionSplitIsometry x)
  rw [positionSplitIsometry.norm_map] at h
  simpa only [Real.norm_eq_abs, sq_abs] using h

theorem continuumLocalizedMode_normalized {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) : (∫ x : Position, continuumLocalizedMode freq u x ^ 2) = 1 := by
  change (∫ x : Position, (localizedMode freq u (positionSplitCoordinates x)) ^ 2) = 1
  rw [positionSplitCoordinates_integral (fun p => localizedMode freq u p ^ 2),
    localizedMode_normalized hfreq]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_Variational_CorrectionDensity
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace NeutralAtom
open scoped Convolution
open ContinuousLinearMap

theorem translated_kernel_indicator_eq (x : Position) (r : ℝ) :
    (Metric.ball x r).indicator (fun y => coulombKernel (x-y)) =
      (fun y => (Metric.ball (0 : Position) r).indicator coulombKernel (x-y)) := by
  ext y
  have hh : x-y ∈ Metric.ball (0 : Position) r ↔ y ∈ Metric.ball x r := by
    simp only [Metric.mem_ball, dist_eq_norm, sub_zero, norm_sub_rev]
  by_cases hy : y ∈ Metric.ball x r <;> simp [hh, hy]

theorem translated_kernel_indicator_integrable (x : Position) (r : ℝ) :
    Integrable ((Metric.ball x r).indicator (fun y => coulombKernel (x-y))) := by
  rw [translated_kernel_indicator_eq]
  exact (integrable_comp_sub_left
    ((Metric.ball (0 : Position) r).indicator coulombKernel) x).mpr
      ((coulombKernel_integrableOn_ball r).integrable_indicator measurableSet_ball)

theorem translated_kernel_indicator_integral (x : Position) (r : ℝ) :
    (∫ y, (Metric.ball x r).indicator (fun y => coulombKernel (x-y)) y) =
      kernelBallMass r := by
  rw [translated_kernel_indicator_eq, integral_sub_left_eq_self,
    integral_indicator measurableSet_ball]
  rfl

theorem potential_integrable_and_bound {ρ : Position → ℝ} {x : Position} {r A : ℝ}
    (hρ : Integrable ρ) (hpos : ∀ y, 0 ≤ ρ y) (hr : 0 < r)
    (hloc : ∀ y ∈ Metric.ball x r, ρ y ≤ A) :
    Integrable (fun y => coulombKernel (x-y)*ρ y) ∧
      potentialOf ρ x ≤ A*kernelBallMass r+r⁻¹*(∫ y, ρ y) := by
  let b : Position → ℝ := fun y =>
    A*((Metric.ball x r).indicator (fun y => coulombKernel (x-y))) y+r⁻¹*ρ y
  have hb : Integrable b :=
    ((translated_kernel_indicator_integrable x r).const_mul A).add (hρ.const_mul r⁻¹)
  have hdom : ∀ y, coulombKernel (x-y)*ρ y ≤ b y := by
    intro y
    by_cases hy : y ∈ Metric.ball x r
    · simp only [b, Set.indicator_of_mem hy]
      exact (mul_le_mul_of_nonneg_left (hloc y hy) (coulombKernel_nonneg _)).trans
        (by nlinarith [mul_nonneg (inv_nonneg.mpr hr.le) (hpos y)])
    · simp only [b, Set.indicator_of_notMem hy, mul_zero, zero_add]
      have hd : r ≤ ‖x-y‖ := by
        simpa only [Metric.mem_ball, not_lt, dist_eq_norm, norm_sub_rev] using hy
      exact mul_le_mul_of_nonneg_right (inv_anti₀ hr hd) (hpos y)
  have hprod : AEStronglyMeasurable (fun y => coulombKernel (x-y)*ρ y) volume :=
    ((measurable_coulombKernel.comp (measurable_const.sub measurable_id)).aestronglyMeasurable).mul
      hρ.aestronglyMeasurable
  have hi : Integrable (fun y => coulombKernel (x-y)*ρ y) := hb.mono' hprod
    (Filter.Eventually.of_forall (fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (coulombKernel_nonneg _) (hpos y))]
      exact hdom y))
  refine ⟨hi, (integral_mono hi hb hdom).trans_eq ?_⟩
  dsimp [b]
  rw [integral_add ((translated_kernel_indicator_integrable x r).const_mul A) (hρ.const_mul r⁻¹),
    integral_const_mul, integral_const_mul, translated_kernel_indicator_integral]

theorem potentialOf_nonneg {ρ : Position → ℝ} (hρ : ∀ y, 0 ≤ ρ y) (x : Position) :
    0 ≤ potentialOf ρ x := integral_nonneg (fun y => mul_nonneg (coulombKernel_nonneg _) (hρ y))

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCoulomb
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite actual Coulomb interactions of the localized densities. Bounded
probability densities permit the existing elementary near/far Coulomb bound;
no interaction coefficient is introduced as a spectral input. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem localizedDensity_mass {freq : ℝ} (hfreq : 0 < freq) (u : PlanarPosition) :
    (∫ x, localizedDensity freq u x) = 1 := continuumLocalizedMode_normalized hfreq u

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarSharpDecay
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A sharp exponential rate for the actual planar resolvent mode. Gaussian
exponential tilting gives a polynomial prefactor and decay `exp (-|r|)`, as
needed to bracket the contact hoppings at lengths `(1±ε)D`. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarHeatKernel_tilt {t : ℝ} (ht : 0 < t) (e b : PlanarPosition) :
    planarHeatKernel t b * Real.exp (inner ℝ e b) =
      Real.exp (t * ‖e‖ ^ 2) * planarHeatKernel t (b - (2 * t) • e) := by
  have he : -‖b‖ ^ 2 / (4 * t) + inner ℝ e b =
      t * ‖e‖ ^ 2 + -‖b - (2 * t) • e‖ ^ 2 / (4 * t) := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs, real_inner_comm b e]
    field_simp
    ring
  unfold planarHeatKernel
  rw [mul_assoc, ← Real.exp_add, he, Real.exp_add]
  ring

theorem planarForcing_exponential_bound (e s : PlanarPosition) :
    planarForcing s ≤ Real.exp (‖e‖ - inner ℝ e s) := by
  by_cases hf : planarForcing s = 0
  · rw [hf]
    exact (Real.exp_pos _).le
  have hs : ‖s‖ ≤ 1 := le_of_lt (lt_of_not_ge
    (fun h => hf (planarForcing_zero_of_norm_ge_one h)))
  have hi : inner ℝ e s ≤ ‖e‖ := (real_inner_le_norm e s).trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hs (norm_nonneg e))
  exact (planarForcing_le_one s).trans (Real.one_le_exp (by linarith))

theorem planarHeatForcing_tilt_bound {t : ℝ} (ht : 0 < t) (e r b : PlanarPosition) :
    planarHeatKernel t b * planarForcing (r - b) ≤
      (Real.exp (‖e‖ - inner ℝ e r) * Real.exp (t * ‖e‖ ^ 2)) *
        planarHeatKernel t (b - (2 * t) • e) := by
  calc
    _ ≤ planarHeatKernel t b * Real.exp (‖e‖ - inner ℝ e (r - b)) :=
      mul_le_mul_of_nonneg_left (planarForcing_exponential_bound e (r - b))
        (planarHeatKernel_positive ht b).le
    _ = Real.exp (‖e‖ - inner ℝ e r) *
        (planarHeatKernel t b * Real.exp (inner ℝ e b)) := by
      rw [inner_sub_right, show ‖e‖ - (inner ℝ e r - inner ℝ e b) =
        (‖e‖ - inner ℝ e r) + inner ℝ e b by ring, Real.exp_add]
      ring
    _ = _ := by rw [planarHeatKernel_tilt ht]; ring

theorem planarHeatAverage_tilt_bound {t : ℝ} (ht : 0 < t) (e r : PlanarPosition) :
    planarHeatAverage t r ≤
      Real.exp (‖e‖ - inner ℝ e r) * Real.exp (t * ‖e‖ ^ 2) := by
  have hi := ((planarHeatKernel_integrable ht).comp_sub_right ((2 * t) • e)).const_mul
    (Real.exp (‖e‖ - inner ℝ e r) * Real.exp (t * ‖e‖ ^ 2))
  have h := integral_mono (planarHeatAverage_integrand_integrable ht r) hi
    (planarHeatForcing_tilt_bound ht e r)
  simpa only [planarHeatAverage, integral_const_mul, integral_sub_right_eq_self,
    planarHeatKernel_integral ht, mul_one] using h

theorem planarResolventMode_tilt_bound (e r : PlanarPosition) (he : ‖e‖ < 1) :
    planarResolventMode r ≤ Real.exp (‖e‖ - inner ℝ e r) / (1 - ‖e‖ ^ 2) := by
  have hc : 0 < 1 - ‖e‖ ^ 2 := by nlinarith [norm_nonneg e]
  have hi : IntegrableOn (fun t : ℝ => Real.exp (-(1 - ‖e‖ ^ 2) * t)) (Set.Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 hc
  rw [planarResolventMode_heat_representation]
  have h := integral_mono_ae (planarResolventMode_heat_integrable r)
    (hi.const_mul (Real.exp (‖e‖ - inner ℝ e r))) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      calc
        _ ≤ Real.exp (-t) * (Real.exp (‖e‖ - inner ℝ e r) * Real.exp (t * ‖e‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left (planarHeatAverage_tilt_bound ht e r) (Real.exp_pos _).le
        _ = Real.exp (‖e‖ - inner ℝ e r) * Real.exp (-(1 - ‖e‖ ^ 2) * t) := by
          rw [show -(1 - ‖e‖ ^ 2) * t = -t + t * ‖e‖ ^ 2 by ring, Real.exp_add]
          ring)
  have heval : (∫ t : ℝ in Set.Ioi 0, Real.exp (-(1 - ‖e‖ ^ 2) * t)) =
      (1 - ‖e‖ ^ 2)⁻¹ := by
    rw [integral_exp_mul_Ioi (by linarith : -(1 - ‖e‖ ^ 2) < 0)]
    simp
    rw [show ‖e‖ ^ 2 - 1 = -(1 - ‖e‖ ^ 2) by ring, div_neg]
    simp only [neg_div, neg_neg, one_div]
  simpa only [integral_const_mul, heval, div_eq_mul_inv] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarExponentialEnvelope
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global exponential envelopes at every fixed rate below one, and
integrability of their planar radial envelopes. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarExponentialConstant_positive {a : ℝ} (ha : 0 ≤ a) (ha₁ : a < 1) :
    0 < planarExponentialConstant a := div_pos (Real.exp_pos _) (by nlinarith)

theorem planarResolventMode_exponential_envelope {a : ℝ} (ha : 0 ≤ a) (ha₁ : a < 1)
    (r : PlanarPosition) : planarResolventMode r ≤ planarExponentialConstant a * Real.exp (-a * ‖r‖) := by
  have hd : 0 < 1 - a ^ 2 := by nlinarith
  by_cases hr : r = 0
  · subst r
    simp only [norm_zero, mul_zero, Real.exp_zero, mul_one]
    apply (planarResolventMode_le_one 0).trans
    apply (le_div_iff₀ hd).mpr
    have h := Real.one_le_exp ha
    nlinarith [sq_nonneg a]
  have hnorm : 0 < ‖r‖ := norm_pos_iff.mpr hr
  let e : PlanarPosition := (a / ‖r‖) • r
  have he : ‖e‖ = a := by
    dsimp [e]
    rw [norm_smul, Real.norm_of_nonneg (div_nonneg ha hnorm.le)]
    field_simp
  have hi : inner ℝ e r = a * ‖r‖ := by
    dsimp [e]
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  have h := planarResolventMode_tilt_bound e r (by rw [he]; exact ha₁)
  rw [he, hi] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  unfold planarExponentialConstant
  rw [show a - a * ‖r‖ = a + -a * ‖r‖ by ring, Real.exp_add]
  ring

theorem exponential_inverse_cubic_bound {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-c * t) ≤ (1 + 3 / c) ^ 3 / (1 + t) ^ 3 := by
  have hq : 0 < c / 3 := by positivity
  have he := Real.add_one_le_exp (c / 3 * t)
  have ht' : t ≤ (3 / c) * Real.exp (c / 3 * t) := by
    have h : t * c ≤ 3 * Real.exp (c / 3 * t) := by nlinarith only [he]
    calc
      _ ≤ (3 * Real.exp (c / 3 * t)) / c := (le_div_iff₀ hc).mpr h
      _ = _ := by ring
  have h₁ : 1 ≤ Real.exp (c / 3 * t) := Real.one_le_exp (mul_nonneg hq.le ht)
  have hb : 1 + t ≤ (1 + 3 / c) * Real.exp (c / 3 * t) := by nlinarith only [ht', h₁]
  have hp := pow_le_pow_left₀ (by linarith : 0 ≤ 1 + t) hb 3
  rw [mul_pow, ← Real.exp_nat_mul] at hp
  norm_num only [Nat.cast_ofNat] at hp
  have harg : (3 : ℝ) * (c / 3 * t) = c * t := by ring
  rw [harg] at hp
  have hm := mul_le_mul_of_nonneg_left hp (Real.exp_pos (-c * t)).le
  have hexp : Real.exp (-c * t) * Real.exp (c * t) = 1 := by
    rw [← Real.exp_add]
    simp
  have hbound : Real.exp (-c * t) * (1 + t) ^ 3 ≤ (1 + 3 / c) ^ 3 := by
    calc
      _ ≤ Real.exp (-c * t) * ((1 + 3 / c) ^ 3 * Real.exp (c * t)) := hm
      _ = _ := by rw [mul_left_comm, hexp, mul_one]
  exact (le_div_iff₀ (pow_pos (by linarith : 0 < 1 + t) 3)).mpr hbound

theorem planar_exp_norm_integrable {c : ℝ} (hc : 0 < c) :
    Integrable (fun r : PlanarPosition => Real.exp (-c * ‖r‖)) := by
  have hi : Integrable (fun r : PlanarPosition => (1 + ‖r‖) ^ (-(3 : ℝ))) :=
    integrable_one_add_norm (by norm_num [PlanarPosition])
  apply (hi.const_mul ((1 + 3 / c) ^ 3)).mono' (by fun_prop)
  exact Filter.Eventually.of_forall (fun r => by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.rpow_neg (by positivity)]
    simpa only [Real.rpow_ofNat, div_eq_mul_inv] using exponential_inverse_cubic_bound hc (norm_nonneg r))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarOverlap
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual normalized planar orbitals have overlap bounded at rate 0.9,
uniformly over every pair of centers. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem normalizedPlanarExponentialConstant_positive {a : ℝ} (ha : 0 ≤ a) (ha₁ : a < 1) :
    0 < normalizedPlanarExponentialConstant a :=
  div_pos (planarExponentialConstant_positive ha ha₁)
    (Real.sqrt_pos.mpr planarResolventMode_square_integral_positive)

theorem normalizedPlanarMode_exponential_envelope {a : ℝ} (ha : 0 ≤ a) (ha₁ : a < 1)
    (r : PlanarPosition) :
    normalizedPlanarMode r ≤ normalizedPlanarExponentialConstant a * Real.exp (-a * ‖r‖) := by
  have h := div_le_div_of_nonneg_right (planarResolventMode_exponential_envelope ha ha₁ r)
    (Real.sqrt_nonneg (∫ r, planarResolventMode r ^ 2))
  convert h using 1 <;> first | rfl | (unfold normalizedPlanarExponentialConstant; ring)

theorem planarModeOverlap_integrable (u v : PlanarPosition) :
    Integrable (fun r => normalizedPlanarMode (r - u) * normalizedPlanarMode (r - v)) :=
  (normalizedPlanarMode_memLp.comp_measurePreserving (measurePreserving_sub_right volume u)).integrable_mul
    (normalizedPlanarMode_memLp.comp_measurePreserving (measurePreserving_sub_right volume v))

theorem planarModeOverlap_nonnegative (u v : PlanarPosition) : 0 ≤ planarModeOverlap u v :=
  integral_nonneg (fun _ => mul_nonneg (normalizedPlanarMode_positive _).le (normalizedPlanarMode_positive _).le)

theorem planarModeOverlap_diagonal (u : PlanarPosition) : planarModeOverlap u u = 1 := by
  unfold planarModeOverlap
  simp_rw [← pow_two]
  rw [integral_sub_right_eq_self (fun r => normalizedPlanarMode r ^ 2) u,
    normalizedPlanarMode_normalized]

theorem planarModeOverlap_envelope {a b : ℝ} (hb : 0 ≤ b) (hba : b < a) (ha₁ : a < 1)
    (u v : PlanarPosition) :
    planarModeOverlap u v ≤
      (normalizedPlanarExponentialConstant a ^ 2 *
        (∫ r : PlanarPosition, Real.exp (-(a - b) * ‖r‖))) * Real.exp (-b * ‖u - v‖) := by
  have ha : 0 ≤ a := le_trans hb hba.le
  have hC := (normalizedPlanarExponentialConstant_positive ha ha₁).le
  have hpt (r : PlanarPosition) :
      normalizedPlanarMode (r - u) * normalizedPlanarMode (r - v) ≤
        (normalizedPlanarExponentialConstant a ^ 2 * Real.exp (-b * ‖u - v‖)) *
          Real.exp (-(a - b) * ‖r - u‖) := by
    have ht : ‖u - v‖ ≤ ‖r - u‖ + ‖r - v‖ := by
      simpa only [dist_eq_norm, norm_sub_rev u r] using dist_triangle u r v
    have hs := mul_le_mul_of_nonneg_left ht hb
    have he : -a * (‖r - u‖ + ‖r - v‖) ≤ -b * ‖u - v‖ + -(a - b) * ‖r - u‖ := by
      nlinarith [mul_nonneg (sub_pos.mpr hba).le (norm_nonneg (r - v))]
    calc
      _ ≤ (normalizedPlanarExponentialConstant a * Real.exp (-a * ‖r - u‖)) *
          (normalizedPlanarExponentialConstant a * Real.exp (-a * ‖r - v‖)) :=
        mul_le_mul (normalizedPlanarMode_exponential_envelope ha ha₁ _)
          (normalizedPlanarMode_exponential_envelope ha ha₁ _)
          (normalizedPlanarMode_positive _).le (mul_nonneg hC (Real.exp_pos _).le)
      _ = normalizedPlanarExponentialConstant a ^ 2 * Real.exp (-a * (‖r - u‖ + ‖r - v‖)) := by
        rw [show -a * (‖r - u‖ + ‖r - v‖) = -a * ‖r - u‖ + -a * ‖r - v‖ by ring,
          Real.exp_add]
        ring
      _ ≤ normalizedPlanarExponentialConstant a ^ 2 *
          Real.exp (-b * ‖u - v‖ + -(a - b) * ‖r - u‖) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (sq_nonneg _)
      _ = _ := by rw [Real.exp_add]; ring
  have hi := ((planar_exp_norm_integrable (sub_pos.mpr hba)).comp_sub_right u).const_mul
    (normalizedPlanarExponentialConstant a ^ 2 * Real.exp (-b * ‖u - v‖))
  have h := integral_mono (planarModeOverlap_integrable u v) hi hpt
  rw [integral_const_mul, integral_sub_right_eq_self
    (fun r : PlanarPosition => Real.exp (-(a - b) * ‖r‖)) u] at h
  exact h.trans_eq (by ring)

theorem planarOverlapConstant_nonnegative : 0 ≤ planarOverlapConstant :=
  mul_nonneg (sq_nonneg _) (integral_nonneg (fun _ => (Real.exp_pos _).le))

theorem planarModeOverlap_decay (u v : PlanarPosition) :
    planarModeOverlap u v ≤ planarOverlapConstant * Real.exp (-(9 / 10 : ℝ) * ‖u - v‖) := by
  have h := planarModeOverlap_envelope (a := 19 / 20) (b := 9 / 10)
    (by norm_num) (by norm_num) (by norm_num) u v
  norm_num only [show (19 / 20 : ℝ) - 9 / 10 = 1 / 20 by norm_num] at h
  exact h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedOrbitalGram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual localized L2 orbitals form a well-conditioned independent
family whenever the exponentially small pair overlaps have a small row sum.
In particular their finite span has an actual orthonormal basis. -/

noncomputable section
open MeasureTheory InnerProductSpace
open scoped BigOperators
namespace ContinuumCoulomb

theorem dualMatrix_quadratic_upper {m : ℕ} (A : Fin m → Fin m → ℝ)
    {a delta : ℝ} (hdelta : 0 ≤ delta) (hdiag : ∀ i, A i i ≤ a)
    (hoff : ∀ i j, i ≠ j → |A i j| ≤ delta) (d : Fin m → ℝ) :
    (∑ i, ∑ j, A i j * d i * d j) ≤ (a + m * delta) * ∑ i, d i ^ 2 := by
  have h := dualMatrix_quadratic_lower (fun i j => -A i j) hdelta
    (fun i => neg_le_neg (hdiag i)) (fun i j hij => by simpa only [abs_neg] using hoff i j hij) d
  simp only [neg_mul, Finset.sum_neg_distrib] at h
  linarith

theorem localizedOverlapBound_nonnegative (D : ℝ) : 0 ≤ localizedOverlapBound D :=
  mul_nonneg planarOverlapConstant_nonnegative (Real.exp_pos _).le

theorem planarModeOverlap_offsite {D : ℝ} {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i - u j‖) (i j : Fin m) (hij : i ≠ j) :
    |planarModeOverlap (u i) (u j)| ≤ localizedOverlapBound D := by
  rw [abs_of_nonneg (planarModeOverlap_nonnegative _ _)]
  exact (planarModeOverlap_decay _ _).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by linarith [hsep i j hij])) planarOverlapConstant_nonnegative)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_GramCorrection
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative symmetric orthonormalization of a finite real Gram matrix.
The correction is the actual spectral inverse square root, with Euclidean
operator norm estimates independent of the ambient function space. -/

noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace ContinuumCoulomb.GramCorrection

lemma inverseSqrt_bounds {a x : ℝ} (_ha : 0 ≤ a) (has : a ≤ 1 / 2)
    (hx : 1 - a ≤ x ∧ x ≤ 1 + a) :
    (Real.sqrt x)⁻¹ ≤ 2 ∧ |(Real.sqrt x)⁻¹ - 1| ≤ 2 * a := by
  have hxp : 0 < x := by linarith
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxp
  have hsq := Real.sq_sqrt hxp.le
  have hslo : (1 / 2 : ℝ) ≤ Real.sqrt x := by
    nlinarith [Real.sqrt_nonneg x]
  have hinv : (Real.sqrt x)⁻¹ ≤ 2 := by
    rw [← one_div]
    apply (div_le_iff₀ hs).mpr
    linarith
  refine ⟨hinv, ?_⟩
  have hid : ((Real.sqrt x)⁻¹ - 1) *
      (Real.sqrt x * (Real.sqrt x + 1)) = 1 - x := by
    calc
      _ = ((Real.sqrt x)⁻¹ * Real.sqrt x - Real.sqrt x) * (Real.sqrt x + 1) := by ring
      _ = (1 - Real.sqrt x) * (Real.sqrt x + 1) := by rw [inv_mul_cancel₀ hs.ne']
      _ = 1 - x := by nlinarith
  have hden : (1 / 2 : ℝ) ≤ Real.sqrt x * (Real.sqrt x + 1) := by
    nlinarith
  have habs : |1 - x| ≤ a := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  have hm : |(Real.sqrt x)⁻¹ - 1| * (Real.sqrt x * (Real.sqrt x + 1)) ≤ a := by
    rw [← abs_of_nonneg (by positivity : 0 ≤ Real.sqrt x * (Real.sqrt x + 1)), ← abs_mul, hid]
    exact habs
  nlinarith [mul_nonneg (abs_nonneg ((Real.sqrt x)⁻¹ - 1)) (sub_nonneg.mpr hden)]

variable {m : ℕ} {G : Matrix (Fin m) (Fin m) ℝ}

lemma eigenvalue_bounds (hG : G.IsHermitian) {delta : ℝ} (hdelta : 0 ≤ delta)
    (hdiag : ∀ i, G i i = 1) (hoff : ∀ i j, i ≠ j → |G i j| ≤ delta) (i : Fin m) :
    1 - m * delta ≤ hG.eigenvalues i ∧ hG.eigenvalues i ≤ 1 + m * delta := by
  let v : Fin m → ℝ := hG.eigenvectorBasis i
  have hnorm : ∑ j, v j ^ 2 = 1 := by
    have h := congrArg (fun t : ℝ => t ^ 2) (hG.eigenvectorBasis.orthonormal.1 i)
    simpa only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, one_pow] using h
  have hval : hG.eigenvalues i = ∑ j, ∑ k, G j k * v j * v k := by
    rw [hG.eigenvalues_eq]
    simp only [RCLike.re_to_real, star_trivial, dotProduct, mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    dsimp [v]
    ring
  rw [hval]
  have hlo := dualMatrix_quadratic_lower G hdelta (fun j => (hdiag j).ge) hoff v
  have hhi := dualMatrix_quadratic_upper G hdelta (fun j => (hdiag j).le) hoff v
  rw [hnorm, mul_one] at hlo hhi
  exact ⟨hlo, hhi⟩

lemma correction_norm_bounds (hG : G.IsHermitian) {delta : ℝ} (hdelta : 0 ≤ delta)
    (hdiag : ∀ i, G i i = 1) (hoff : ∀ i j, i ≠ j → |G i j| ≤ delta)
    (hsmall : m * delta ≤ 1 / 2) :
    ‖correction hG‖ ≤ 2 ∧ ‖correction hG - 1‖ ≤ 2 * m * delta := by
  have ha : 0 ≤ (m : ℝ) * delta := mul_nonneg (Nat.cast_nonneg _) hdelta
  have hb (i : Fin m) := inverseSqrt_bounds ha hsmall (eigenvalue_bounds hG hdelta hdiag hoff i)
  have hnorm : ‖correction hG‖ ≤ 2 := by
    rw [correction, ← hG.cfc_eq]
    apply norm_cfc_le (by norm_num : (0 : ℝ) ≤ 2)
    intro x hx
    rw [hG.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    exact (hb i).1
  refine ⟨hnorm, ?_⟩
  have hc : ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹) (spectrum ℝ G) :=
    G.finite_real_spectrum.continuousOn _
  rw [correction, ← hG.cfc_eq, ← cfc_const_one ℝ G, ← cfc_sub _ _ G hc continuousOn_const]
  apply norm_cfc_le (by positivity : (0 : ℝ) ≤ 2 * m * delta)
  intro x hx
  rw [hG.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  simpa only [Real.norm_eq_abs, mul_assoc] using (hb i).2

lemma entry_abs_le_norm (B : Matrix (Fin m) (Fin m) ℝ) (i j : Fin m) : |B i j| ≤ ‖B‖ := by
  let v : EuclideanSpace ℝ (Fin m) := PiLp.single 2 j 1
  let y : EuclideanSpace ℝ (Fin m) := Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ) B v
  have hy : y i = B i j := by
    change (B *ᵥ Pi.single j (1 : ℝ)) i = B i j
    rw [Matrix.mulVec_single_one]
    rfl
  calc
    |B i j| = ‖y i‖ := by rw [hy, Real.norm_eq_abs]
    _ ≤ ‖y‖ := PiLp.norm_apply_le y i
    _ ≤ ‖Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ) B‖ * ‖v‖ := (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ) B).le_opNorm v
    _ = ‖B‖ := by rw [Matrix.l2_opNorm_toEuclideanCLM]; simp only [v, PiLp.norm_single, norm_one, mul_one]

lemma correction_entry_bounds (hG : G.IsHermitian) {delta : ℝ} (hdelta : 0 ≤ delta)
    (hdiag : ∀ i, G i i = 1) (hoff : ∀ i j, i ≠ j → |G i j| ≤ delta)
    (hsmall : m * delta ≤ 1 / 2) (i j : Fin m) :
    |correction hG i j - if i = j then 1 else 0| ≤ 2 * m * delta ∧
      |correction hG i j| ≤ 2 := by
  have hb := correction_norm_bounds hG hdelta hdiag hoff hsmall
  constructor
  · simpa only [Matrix.sub_apply, Matrix.one_apply] using
      (entry_abs_le_norm (correction hG - 1) i j).trans hb.2
  · exact (entry_abs_le_norm (correction hG) i j).trans hb.1

end ContinuumCoulomb.GramCorrection

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RealSpinOrbitals
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spin lifting of real C1 orbitals into the actual fermionic weak-H1
domain. Any injective list of occupied orthonormal spatial/spin modes
gives a normalized antisymmetric state on the full configuration space. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem realSpinOrbital_inner (f g : Position → ℝ) (σ τ : Fin 2) :
    (∑ s : Fin 2, ∫ x, star (realSpinOrbital f σ x s) * realSpinOrbital g τ x s) =
      if σ = τ then (↑(∫ x, f x * g x) : ℂ) else 0 := by
  by_cases h : σ = τ
  · subst τ
    have hp (s : Fin 2) :
        (∫ x, star (realSpinOrbital f σ x s) * realSpinOrbital g σ x s) =
          if s=σ then (↑(∫ x, f x*g x) : ℂ) else 0 := by
      by_cases hs : s=σ
      · subst s
        simp only [realSpinOrbital, ite_true, if_true, Complex.star_def, Complex.conj_ofReal,
          ← Complex.ofReal_mul, integral_complex_ofReal]
      · simp [realSpinOrbital, hs]
    simp only [hp, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  · have hz (s : Fin 2) (x : Position) : star (realSpinOrbital f σ x s) * realSpinOrbital g τ x s = 0 := by
      by_cases hs : s = σ
      · subst s
        simp [realSpinOrbital, h]
      · simp [realSpinOrbital, hs]
    simp only [hz, integral_zero, Finset.sum_const_zero, h, ite_false, if_false]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_OrthonormalLocalizedModes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual spectral inverse-square-root correction applied to the
manufactured orbitals. These are C1 decaying orthonormal spatial functions;
injectively occupied spatial/spin modes give actual normalized fermions. -/

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace ContinuumCoulomb

theorem correctedLocalizedCoefficients_entries {D : ℝ} {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖) (hs : m * localizedOverlapBound D ≤ 1/2) (i j : Fin m) :
    |correctedLocalizedCoefficients u i j - if i=j then 1 else 0| ≤ 2*m*localizedOverlapBound D ∧
      |correctedLocalizedCoefficients u i j| ≤ 2 :=
  GramCorrection.correction_entry_bounds (localizedModeGram_isHermitian u)
    (localizedOverlapBound_nonnegative D) (fun j => planarModeOverlap_diagonal (u j))
    (planarModeOverlap_offsite u hsep) hs i j

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_DensitySynthesis
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Nonnegative continuous-density synthesis for the unit-charge construction

The density is the uniform slab plus `ΔV/(4π)`. Compact support of `V`
inside the slab makes its attractive Coulomb field exactly the slab field
plus `V`. A pointwise Laplacian bound makes the density nonnegative.
Only C² regularity is required, as the manuscript's manufactured well is
finitely smooth.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem slabDensity_integral (rho H S : ℝ) :
    (∫ x, slabDensity rho H S x) = volume.real (slabDomain H S) * rho := by
  exact integral_indicator_const rho (slabDomain_isClosed H S).measurableSet

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarWellMatrix
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual well matrix elements. The well at the first orbital center gives
exactly the distance-dependent hopping; a well far from both centers gives
an error decaying at rate 1.9. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarWellMatrix_integrable (u v w : PlanarPosition) :
    Integrable (fun r => normalizedPlanarMode (r - u) * manufacturedPlanarWell (r - w) *
      normalizedPlanarMode (r - v)) := by
  apply (((normalizedPlanarMode_C7.continuous.comp (continuous_id.sub continuous_const)).mul
    (manufacturedPlanarWell_C7.continuous.comp (continuous_id.sub continuous_const))).mul
    (normalizedPlanarMode_C7.continuous.comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport
  exact (manufacturedPlanarWell_hasCompactSupport.comp_homeomorph (Homeomorph.subRight w)).mul_left.mul_right

theorem planarWellMatrixConstant_nonnegative : 0 ≤ planarWellMatrixConstant :=
  mul_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
    (integral_nonneg (fun _ => abs_nonneg _))

theorem planarWellMatrix_two_far {D : ℝ} (u v w : PlanarPosition)
    (hu : D ≤ ‖u - w‖) (hv : D ≤ ‖v - w‖) :
    |planarWellMatrix u v w| ≤ planarWellMatrixConstant * Real.exp (-(19 / 10 : ℝ) * D) := by
  let C := normalizedPlanarExponentialConstant (19 / 20)
  have hC : 0 ≤ C := (normalizedPlanarExponentialConstant_positive (by norm_num) (by norm_num)).le
  let B := C ^ 2 * Real.exp ((19 / 10 : ℝ) - (19 / 10 : ℝ) * D)
  have hpt (r : PlanarPosition) :
      ‖normalizedPlanarMode (r - u) * manufacturedPlanarWell (r - w) * normalizedPlanarMode (r - v)‖ ≤
        B * |manufacturedPlanarWell (r - w)| := by
    by_cases hw : manufacturedPlanarWell (r - w) = 0
    · simp only [hw, mul_zero, zero_mul, norm_zero, abs_zero, le_refl]
    have hs : ‖r - w‖ ≤ 1 := by
      have hm := (manufacturedPlanarWell_support.trans planarForcing_support)
        (subset_tsupport _ (show r - w ∈ Function.support manufacturedPlanarWell from hw))
      simpa only [Metric.mem_closedBall, dist_zero_right] using hm
    have htu : ‖u - w‖ ≤ ‖r - u‖ + ‖r - w‖ := by
      simpa only [dist_eq_norm, norm_sub_rev u r] using dist_triangle u r w
    have htv : ‖v - w‖ ≤ ‖r - v‖ + ‖r - w‖ := by
      simpa only [dist_eq_norm, norm_sub_rev v r] using dist_triangle v r w
    have he : -(19 / 20 : ℝ) * (‖r - u‖ + ‖r - v‖) ≤ 19 / 10 - (19 / 10 : ℝ) * D := by
      linarith
    have hp : normalizedPlanarMode (r - u) * normalizedPlanarMode (r - v) ≤ B := by
      calc
        _ ≤ (C * Real.exp (-(19 / 20 : ℝ) * ‖r - u‖)) *
            (C * Real.exp (-(19 / 20 : ℝ) * ‖r - v‖)) :=
          mul_le_mul (normalizedPlanarMode_exponential_envelope (by norm_num) (by norm_num) _)
            (normalizedPlanarMode_exponential_envelope (by norm_num) (by norm_num) _)
            (normalizedPlanarMode_positive _).le (mul_nonneg hC (Real.exp_pos _).le)
        _ = C ^ 2 * Real.exp (-(19 / 20 : ℝ) * (‖r - u‖ + ‖r - v‖)) := by
          rw [show -(19 / 20 : ℝ) * (‖r - u‖ + ‖r - v‖) =
            -(19 / 20 : ℝ) * ‖r - u‖ + -(19 / 20 : ℝ) * ‖r - v‖ by ring, Real.exp_add]
          ring
        _ ≤ B := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (sq_nonneg C)
    rw [norm_mul, norm_mul, Real.norm_of_nonneg (normalizedPlanarMode_positive _).le,
      Real.norm_of_nonneg (normalizedPlanarMode_positive _).le, Real.norm_eq_abs]
    convert mul_le_mul_of_nonneg_right hp (abs_nonneg (manufacturedPlanarWell (r - w))) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hiW : Integrable manufacturedPlanarWell :=
    manufacturedPlanarWell_C7.continuous.integrable_of_hasCompactSupport manufacturedPlanarWell_hasCompactSupport
  have hi := (hiW.abs.comp_sub_right w).const_mul B
  have h := norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall hpt)
  rw [integral_const_mul, integral_sub_right_eq_self (fun r : PlanarPosition => |manufacturedPlanarWell r|) w] at h
  rw [Real.norm_eq_abs] at h
  apply h.trans_eq
  dsimp [B, C, planarWellMatrixConstant]
  rw [show (19 / 10 : ℝ) - (19 / 10 : ℝ) * D =
    (19 / 10 : ℝ) + -(19 / 10 : ℝ) * D by ring, Real.exp_add]
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCoulombTranslation
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Direct Coulomb coefficients as actual translated-density profiles. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarCenter_norm (u : PlanarPosition) : ‖planarCenter u‖ = ‖u‖ := by
  have h := positionSplitCoordinates_norm_sq (planarCenter u)
  simp only [planarCenter, ContinuousLinearEquiv.apply_symm_apply, zero_pow (by norm_num : 2 ≠ 0),
    add_zero] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

theorem continuumLocalizedMode_translate (freq : ℝ) (u : PlanarPosition) (x : Position) :
    continuumLocalizedMode freq u x = continuumLocalizedMode freq 0 (x - planarCenter u) := by
  simp only [continuumLocalizedMode, localizedMode, map_sub, planarCenter,
    ContinuousLinearEquiv.apply_symm_apply, Prod.fst_sub, Prod.snd_sub, sub_zero]

theorem localizedDensity_translate (freq : ℝ) (u : PlanarPosition) (x : Position) :
    localizedDensity freq u x = localizedDensity freq 0 (x - planarCenter u) := by
  simp only [localizedDensity, continuumLocalizedMode_translate freq u]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarSobolev
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Closure of the actual manufactured-well inequality on the planar
Sobolev graph. The bounded potential acts on actual L² classes, and the
form is continuous in the function-and-gradient norm. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

namespace PlanarSobolev

attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instMeasurableSpacePlanarPosition
attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instBorelSpacePlanarPosition
attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instMeasureSpacePlanarPosition
theorem wellBound_nonnegative : 0 ≤ wellBound :=
  (norm_nonneg (manufacturedPlanarWell 0)).trans (wellBound_spec 0)

end PlanarSobolev
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarWellLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact localization of the actual sum of manufactured wells. Site
pieces see exactly their own well; the exterior piece sees zero potential. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem planarWellSum_continuous {ι : Type*} [Fintype ι] (u : ι → PlanarPosition) :
    Continuous (planarWellSum u) :=
  continuous_finsetSum _ (fun i _ => manufacturedPlanarWell_C7.continuous.comp
    (continuous_id.sub (continuous_const : Continuous (fun _ : PlanarPosition => u i))))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ExplicitVerticalCutoff
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit smooth transverse cutoff. Its formula uses only the fixed
smooth transition function, so rational approximation can use the actual
exponential formula instead of a classically selected bump function. -/

noncomputable section
namespace ContinuumCoulomb

namespace verticalCutoffBump

theorem nonneg {z : ℝ} : 0 ≤ verticalCutoffBump z :=
  Real.smoothTransition.nonneg _

theorem le_one {z : ℝ} : verticalCutoffBump z ≤ 1 :=
  Real.smoothTransition.le_one _

theorem one_of_mem_closedBall {z : ℝ} (hz : z ∈ Metric.closedBall (0 : ℝ) 1) :
    verticalCutoffBump z = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have hab : |z| ≤ 1 := by simpa [Metric.mem_closedBall, Real.dist_eq] using hz
  have hsq := (sq_le_sq₀ (abs_nonneg z) (by norm_num : (0:ℝ) ≤ 1)).mpr hab
  rw [sq_abs] at hsq
  linarith

end verticalCutoffBump
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedWellField
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual compact three-dimensional well field in the unit-charge
construction. Its coefficients are Coulomb counterterms. The cutoff only weakens the attractive uncorrected wells. -/

noncomputable section
open scoped BigOperators ContDiff
namespace ContinuumCoulomb

theorem slabWellCutoff_bounds (S z : ℝ) :
    0 ≤ slabWellCutoff S z ∧ slabWellCutoff S z ≤ 1 :=
  ⟨verticalCutoffBump.nonneg, verticalCutoffBump.le_one⟩

theorem slabWellCutoff_inner {S : ℝ} (hS : 0 < S) {z : ℝ} (hz : |z| ≤ S/2) :
    slabWellCutoff S z = 1 := by
  apply verticalCutoffBump.one_of_mem_closedBall
  change dist ((2/S)*z) 0 ≤ 1
  rw [dist_zero_right, Real.norm_eq_abs, abs_mul, abs_of_pos (div_pos (by norm_num) hS)]
  have hm := mul_le_mul_of_nonneg_left hz (div_pos (by norm_num : (0:ℝ)<2) hS).le
  have he : (2/S)*(S/2) = (1:ℝ) := by field_simp
  exact hm.trans_eq he

theorem manufacturedWellField_inner (freq scale : ℝ) {S : ℝ} (hS : 0 < S)
    {m : ℕ} (u : Fin m → PlanarPosition) (x : Position)
    (hx : |(positionSplitCoordinates x).2| ≤ S/2) :
    manufacturedWellField freq scale S u x =
      countertermWellSum freq scale u (positionSplitCoordinates x).1 := by
  simp only [manufacturedWellField, slabWellCutoff_inner hS hx, one_mul]

theorem positionSplitCoordinates_fst_zero (x : Position) :
    (positionSplitCoordinates x).1 0 = x 0 := rfl

theorem positionSplitCoordinates_fst_one (x : Position) :
    (positionSplitCoordinates x).1 1 = x 1 := rfl

theorem positionSplitCoordinates_snd (x : Position) :
    (positionSplitCoordinates x).2 = x 2 := rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabLineIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Centered-interval comparison for the actual one-coordinate Coulomb
integrals. It is the coordinatewise monotonicity step in the slab estimate. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem centeredLineIntegral_translate (f : ℝ → ℝ) (H x : ℝ) :
    centeredLineIntegral f H x = ∫ t in (-H)..H, f (x-t) := by
  rw [intervalIntegral.integral_comp_sub_left]
  simp only [centeredLineIntegral, sub_neg_eq_add]

theorem centeredLineIntegral_hasDerivAt (f : ℝ → ℝ) (hf : Continuous f) (H x : ℝ) :
    HasDerivAt (centeredLineIntegral f H) (f (x+H)-f (x-H)) x := by
  let F : ℝ → ℝ := fun a => ∫ t in (0:ℝ)..a, f t
  have hF (a : ℝ) : HasDerivAt F (f a) a :=
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have he : centeredLineIntegral f H = (fun a => F (a+H)-F (a-H)) := by
    funext a
    exact (intervalIntegral.integral_interval_sub_left
      (hf.intervalIntegrable 0 (a+H)) (hf.intervalIntegrable 0 (a-H))).symm
  rw [he]
  simpa only [Function.comp_def, id_eq, mul_one] using
    ((hF (x+H)).comp x ((hasDerivAt_id x).add_const H)).fun_sub
      ((hF (x-H)).comp x ((hasDerivAt_id x).sub_const H))

theorem coulombLineKernel_continuous {A : ℝ} (hA : 0 < A) :
    Continuous (coulombLineKernel A) := by
  apply Continuous.inv₀
  · exact (continuous_const.add (continuous_id.pow 2)).sqrt
  · intro t
    exact (Real.sqrt_pos.mpr (by nlinarith [sq_nonneg t] : 0 < A+t^2)).ne'

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabKernelEstimates
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inverse-cube horizontal tail bound and the exact absolute-value
integral that produce the quadratic potential of the infinite slab. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem reciprocal_sqrt_difference_bound {R A B : ℝ} (hR : 0 < R)
    (hA : R^2 ≤ A) (hB : R^2 ≤ B) :
    |(Real.sqrt A)⁻¹ - (Real.sqrt B)⁻¹| ≤ |A-B|/(2*R^3) := by
  have hA0 : 0 ≤ A := (sq_nonneg R).trans hA
  have hB0 : 0 ≤ B := (sq_nonneg R).trans hB
  have hsA : R ≤ Real.sqrt A := by
    rw [← Real.sqrt_sq hR.le]
    exact Real.sqrt_le_sqrt hA
  have hsB : R ≤ Real.sqrt B := by
    rw [← Real.sqrt_sq hR.le]
    exact Real.sqrt_le_sqrt hB
  have hpA : 0 < Real.sqrt A := hR.trans_le hsA
  have hpB : 0 < Real.sqrt B := hR.trans_le hsB
  have hd : 0 < Real.sqrt A * Real.sqrt B * (Real.sqrt A + Real.sqrt B) := by positivity
  have he : (Real.sqrt A)⁻¹ - (Real.sqrt B)⁻¹ =
      (B-A)/(Real.sqrt A * Real.sqrt B * (Real.sqrt A+Real.sqrt B)) := by
    field_simp
    nlinarith [Real.sq_sqrt hA0, Real.sq_sqrt hB0]
  have hprod : R^2 ≤ Real.sqrt A * Real.sqrt B := by
    simpa only [pow_two] using mul_le_mul hsA hsB hR.le hpA.le
  have hsum : 2*R ≤ Real.sqrt A+Real.sqrt B := by linarith
  have hden : 2*R^3 ≤ Real.sqrt A*Real.sqrt B*(Real.sqrt A+Real.sqrt B) := by
    have h := mul_le_mul hprod hsum (by positivity : 0 ≤ 2*R)
      (mul_nonneg hpA.le hpB.le)
    nlinarith only [h]
  rw [he, abs_div, abs_of_pos hd, abs_sub_comm B A]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hden

private theorem integral_abs_sub_of_inside {S z : ℝ} (_hS : 0 ≤ S)
    (hz : |z| ≤ S) :
    (∫ w in (-S)..S, |z-w|) = S^2+z^2 := by
  have hzlo : -S ≤ z := (abs_le.mp hz).1
  have hzhi : z ≤ S := (abs_le.mp hz).2
  have hc : Continuous (fun w : ℝ => |z-w|) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (-S) z) (hc.intervalIntegrable z S)]
  have hl : (∫ w in (-S)..z, |z-w|) = ∫ w in (-S)..z, z-w := by
    apply intervalIntegral.integral_congr
    intro w hw
    have hmem : w ∈ Set.Icc (-S) z := by simpa only [Set.uIcc_of_le hzlo] using hw
    exact abs_of_nonneg (sub_nonneg.mpr hmem.2)
  have hr : (∫ w in z..S, |z-w|) = ∫ w in z..S, w-z := by
    apply intervalIntegral.integral_congr
    intro w hw
    have hmem : w ∈ Set.Icc z S := by simpa only [Set.uIcc_of_le hzhi] using hw
    change |z-w| = w-z
    rw [abs_of_nonpos (sub_nonpos.mpr hmem.1)]
    ring
  rw [hl, hr]
  calc
    _ = ((∫ w : ℝ in (-S)..z, z) - (∫ w : ℝ in (-S)..z, w)) +
        ((∫ w : ℝ in z..S, w) - (∫ w : ℝ in z..S, z)) := by
      exact congrArg₂ (· + ·)
        (intervalIntegral.integral_sub (f := fun _ : ℝ => z) (g := fun w : ℝ => w)
          (continuous_const.intervalIntegrable _ _) (continuous_id.intervalIntegrable _ _))
        (intervalIntegral.integral_sub (f := fun w : ℝ => w) (g := fun _ : ℝ => z)
          (continuous_id.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _))
    _ = _ := by
      simp only [intervalIntegral.integral_const, smul_eq_mul, integral_id]
      ring

theorem slab_absolute_difference_integral {S z : ℝ} (hS : 0 ≤ S) (hz : |z| ≤ S) :
    (∫ w in (-S)..S, (|z-w|-|w|)) = z^2 := by
  have hc : Continuous (fun w : ℝ => |z-w|) := by fun_prop
  rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _)
    (continuous_abs.intervalIntegrable _ _),
    integral_abs_sub_of_inside hS hz]
  have h := integral_abs_sub_of_inside hS (show |(0:ℝ)| ≤ S by simpa using hS)
  simp only [zero_sub, abs_neg, zero_pow (by decide : 2 ≠ 0), add_zero] at h
  rw [h]
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabCoordinates
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact ordinary product coordinates for the slab Coulomb integral.
These allow the finite-box potential to be treated by one-coordinate
integrals without changing the Euclidean volume normalization. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem slabPotential_eq_setIntegral (rho H S : ℝ) (y : Position) :
    slabPotential rho H S y = -rho * ∫ x in slabDomain H S, Coulomb.coulombKernel (y-x) := by
  have he : (fun x => Coulomb.coulombKernel (y-x)*slabDensity rho H S x) =
      (slabDomain H S).indicator (fun x => rho*Coulomb.coulombKernel (y-x)) := by
    funext x
    by_cases hx : x ∈ slabDomain H S
    · simp only [slabDensity, Set.indicator_of_mem hx]
      ring
    · simp only [slabDensity, Set.indicator_of_notMem hx, mul_zero]
  unfold slabPotential
  rw [he, integral_indicator (slabDomain_isClosed H S).measurableSet, integral_const_mul]
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabRegularization
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.Coulomb.complexWindow_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Regularization of the actual finite-slab potential. The singular
Coulomb limit is justified on the full volume integral; no continuity of
the slab indicator is assumed. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ContinuumCoulomb

theorem slabCoulomb_integrableOn {H S : ℝ} (hH : 0 ≤ H) (hS : 0 ≤ S) (y : Position) :
    IntegrableOn (fun x => Coulomb.coulombKernel (y-x)) (slabDomain H S) := by
  have hm : Measurable (slabDensity 1 H S) :=
    measurable_const.indicator (slabDomain_isClosed H S).measurableSet
  have hb (x : Position) : ‖slabDensity 1 H S x‖ ≤ 1 := by
    by_cases hx : x ∈ slabDomain H S <;>
      simp [slabDensity, hx]
  have hi := Coulomb.coulomb_signed_convolution_integrable
    (slabDensity_integrable hH hS 1) hm hb y
  have he : (fun x => Coulomb.coulombKernel (y-x)*slabDensity 1 H S x) =
      (slabDomain H S).indicator (fun x => Coulomb.coulombKernel (y-x)) := by
    funext x
    by_cases hx : x ∈ slabDomain H S <;> simp [slabDensity, hx]
  rw [he, integrable_indicator_iff (slabDomain_isClosed H S).measurableSet] at hi
  exact hi

theorem regularizedSlab_integrableOn {epsilon H S : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (y : Position) :
    IntegrableOn (fun x => NeutralAtom.regularizedKernel epsilon (y-x)) (slabDomain H S) :=
  ((NeutralAtom.contDiff_regularizedKernel hepsilon).continuous.comp
    (continuous_const.sub continuous_id)).continuousOn.integrableOn_compact
      (slabDomain_isCompact hH hS)

theorem regularizedSlabPotential_tendsto {epsilon : ℕ → ℝ}
    (hepsilon : ∀ n, 0 < epsilon n) (hlim : Tendsto epsilon atTop (𝓝 0))
    (rho : ℝ) {H S : ℝ} (hH : 0 ≤ H) (hS : 0 ≤ S) (y : Position) :
    Tendsto (fun n => regularizedSlabPotential (epsilon n) rho H S y)
      atTop (𝓝 (slabPotential rho H S y)) := by
  have hae : ∀ᵐ x ∂(volume.restrict (slabDomain H S)), y-x ≠ 0 := by
    filter_upwards [ae_restrict_of_ae (volume.ae_ne y)] with x hx
    exact sub_ne_zero.mpr (Ne.symm hx)
  have hi := slabCoulomb_integrableOn hH hS y
  have hc : Tendsto
      (fun n => ∫ x in slabDomain H S, NeutralAtom.regularizedKernel (epsilon n) (y-x))
      atTop (𝓝 (∫ x in slabDomain H S, Coulomb.coulombKernel (y-x))) := by
    apply tendsto_integral_of_dominated_convergence
      (fun x => Coulomb.coulombKernel (y-x))
    · intro n
      exact ((NeutralAtom.contDiff_regularizedKernel (hepsilon n).ne').continuous.comp
        (continuous_const.sub continuous_id)).aestronglyMeasurable
    · exact hi
    · intro n
      filter_upwards [hae] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (NeutralAtom.regularizedKernel_nonneg _ _)]
      exact NeutralAtom.regularizedKernel_le hx
    · filter_upwards [hae] with x hx
      exact NeutralAtom.regularizedKernel_tendsto hlim hx
  rw [slabPotential_eq_setIntegral]
  exact hc.const_mul (-rho)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabSections
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite product sections of the actual rectangular slab measure. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace ContinuumCoulomb

theorem slabProductDomain_preimage (H S : ℝ) :
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm ⁻¹' slabProductDomain H S = slabDomain H S := by
  ext x
  change (∀ i : Fin 3, i ∈ Set.univ → -slabSide H S i ≤ x i ∧ x i ≤ slabSide H S i) ↔
    |x 0| ≤ H ∧ |x 1| ≤ H ∧ |x 2| ≤ S
  simp only [Set.mem_univ, true_implies, abs_le]
  constructor
  · intro h
    exact ⟨by simpa [slabSide] using h 0,
      by simpa [slabSide] using h 1, by simpa [slabSide] using h 2⟩
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i
    · simpa [slabSide] using h0
    · simpa [slabSide] using h1
    · simpa [slabSide] using h2

theorem slabProductMeasure_eq (H S : ℝ) :
    slabProductMeasure H S = (volume : Measure (Fin 3 → ℝ)).restrict (slabProductDomain H S) := by
  exact (Measure.restrict_pi_pi (fun _ : Fin 3 => (volume : Measure ℝ))
    (fun i => Set.Icc (-slabSide H S i) (slabSide H S i))).symm

theorem slabProduct_measurePreserving (H S : ℝ) :
    MeasurePreserving (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))
      (slabProductMeasure H S) (volume.restrict (slabDomain H S)) := by
  have hm := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).restrict_preimage
    (s := slabProductDomain H S)
    (MeasurableSet.univ_pi (fun i => measurableSet_Icc))
  rw [slabProductDomain_preimage, ← slabProductMeasure_eq] at hm
  exact MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm hm

theorem slabProduct_integral (H S : ℝ) (f : Position → ℝ) :
    (∫ x, f (WithLp.toLp 2 x) ∂slabProductMeasure H S) =
      ∫ y in slabDomain H S, f y := by
  exact (slabProduct_measurePreserving H S).integral_comp' f

theorem slabProduct_integrable (H S : ℝ) (f : Position → ℝ) :
    Integrable (fun x => f (WithLp.toLp 2 x)) (slabProductMeasure H S) ↔
      IntegrableOn f (slabDomain H S) :=
  (slabProduct_measurePreserving H S).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding

theorem regularizedKernel_eq_sqrt (epsilon : ℝ) (x : Position) :
    NeutralAtom.regularizedKernel epsilon x = (Real.sqrt (‖x‖^2+epsilon^2))⁻¹ := by
  rw [NeutralAtom.regularizedKernel, Real.sqrt_eq_rpow]
  convert Real.rpow_neg (add_nonneg (sq_nonneg ‖x‖) (sq_nonneg epsilon)) (1/2:ℝ) using 1
  all_goals try with_reducible_and_instances rfl
  norm_num

theorem regularizedKernel_section (epsilon : ℝ) (y : Position) (i : Fin 3)
    (t : ℝ) (v : Fin 2 → ℝ) :
    NeutralAtom.regularizedKernel epsilon (y-WithLp.toLp 2 (i.insertNth t v)) =
      coulombLineKernel
        (epsilon^2+∑ j : Fin 2, (y (i.succAbove j)-v j)^2) (y i-t) := by
  rw [regularizedKernel_eq_sqrt]
  unfold coulombLineKernel
  congr 2
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succAbove _ i]
  simp only [PiLp.sub_apply, Fin.insertNth_apply_same,
    Fin.insertNth_apply_succAbove]
  ring

theorem zeroPositionCoordinate_same (i : Fin 3) (y : Position) :
    zeroPositionCoordinate i y i = 0 := by simp [zeroPositionCoordinate]

theorem zeroPositionCoordinate_other (i : Fin 3) (y : Position) (j : Fin 2) :
    zeroPositionCoordinate i y (i.succAbove j) = y (i.succAbove j) := by
  simp [zeroPositionCoordinate, Fin.succAbove_ne]

private theorem regularizedProduct_integrable {epsilon H S : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (y : Position) :
    Integrable (fun x : Fin 3 → ℝ => NeutralAtom.regularizedKernel epsilon
      (y-WithLp.toLp 2 x)) (slabProductMeasure H S) :=
  (slabProduct_integrable H S _).mpr (regularizedSlab_integrableOn hepsilon hH hS y)

private theorem regularizedSection_integrable {epsilon H S : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (y : Position) (i : Fin 3) :
    Integrable (fun p : ℝ × (Fin 2 → ℝ) => NeutralAtom.regularizedKernel epsilon
      (y-WithLp.toLp 2 (i.insertNth p.1 p.2)))
      ((slabAxisMeasure H S i).prod
        (Measure.pi (fun j : Fin 2 => slabAxisMeasure H S (i.succAbove j)))) := by
  have hp := (measurePreserving_piFinSuccAbove (slabAxisMeasure H S) i).symm
  have h := (hp.integrable_comp_emb
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) i).symm.measurableEmbedding).mpr
    (regularizedProduct_integrable hepsilon hH hS y)
  exact h

theorem regularizedSlab_sectionIntegral {epsilon H S : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (y : Position) (i : Fin 3) :
    (∫ x in slabDomain H S, NeutralAtom.regularizedKernel epsilon (y-x)) =
      ∫ v : Fin 2 → ℝ, ∫ t : ℝ,
        NeutralAtom.regularizedKernel epsilon (y-WithLp.toLp 2 (i.insertNth t v))
        ∂slabAxisMeasure H S i
        ∂Measure.pi (fun j : Fin 2 => slabAxisMeasure H S (i.succAbove j)) := by
  rw [← slabProduct_integral H S (fun x => NeutralAtom.regularizedKernel epsilon (y-x))]
  change (∫ x : Fin 3 → ℝ, NeutralAtom.regularizedKernel epsilon (y-WithLp.toLp 2 x)
    ∂Measure.pi (slabAxisMeasure H S)) = _
  rw [← ((measurePreserving_piFinSuccAbove (slabAxisMeasure H S) i).symm).integral_comp']
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  exact integral_prod_symm _ (regularizedSection_integrable hepsilon hH hS y i)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabPlanarIntegral
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact horizontal-plane Coulomb differences. The individually divergent
plane integrals are never separated; their integrable difference has a
finite antiderivative and a zero limit at infinity. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ContinuumCoulomb

theorem slabRootDifference_quotient {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (r : ℝ) :
    slabRootDifference A B r = (A-B)/(Real.sqrt (r^2+A)+Real.sqrt (r^2+B)) := by
  have hpA : 0 < r^2+A := by positivity
  have hpB : 0 < r^2+B := by positivity
  have hden : 0 < Real.sqrt (r^2+A)+Real.sqrt (r^2+B) := by positivity
  apply (eq_div_iff hden.ne').mpr
  unfold slabRootDifference
  nlinarith [Real.sq_sqrt hpA.le, Real.sq_sqrt hpB.le]

theorem slabRootDifference_tendsto {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    Tendsto (slabRootDifference A B) atTop (𝓝 0) := by
  have hp : Tendsto (fun r : ℝ => r^2) atTop atTop := tendsto_pow_atTop (by norm_num)
  have ha := Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_right _ A hp)
  have hb := Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_right _ B hp)
  have hd := ha.atTop_add_atTop hb
  simpa only [Function.comp_apply, ← slabRootDifference_quotient hA hB] using hd.const_div_atTop (A-B)

theorem slabRootDifference_hasDerivAt {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (r : ℝ) :
    HasDerivAt (slabRootDifference A B) (slabRadialDifference A B r) r := by
  have hpA : 0 < r^2+A := by positivity
  have hpB : 0 < r^2+B := by positivity
  have ha := (((hasDerivAt_id r).pow 2).add_const A).sqrt hpA.ne'
  have hb := (((hasDerivAt_id r).pow 2).add_const B).sqrt hpB.ne'
  refine (ha.fun_sub hb).congr_deriv ?_
  · dsimp only [slabRadialDifference, coulombLineKernel]
    simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    rw [add_comm A (r^2), add_comm B (r^2)]
    field_simp

theorem slabRadialDifference_nonnegative {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B)
    {r : ℝ} (hr : 0 ≤ r) : 0 ≤ slabRadialDifference A B r := by
  apply mul_nonneg hr
  apply sub_nonneg.mpr
  unfold coulombLineKernel
  exact inv_anti₀ (Real.sqrt_pos.mpr (by positivity : 0 < A+r^2))
    (Real.sqrt_le_sqrt (by linarith : A+r^2 ≤ B+r^2))

theorem slabRadialDifference_integrable {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    IntegrableOn (slabRadialDifference A B) (Set.Ioi (0:ℝ)) := by
  rcases le_total A B with hAB | hBA
  · exact integrableOn_Ioi_deriv_of_nonneg'
      (fun r _ => slabRootDifference_hasDerivAt hA hB r)
      (fun r hr => slabRadialDifference_nonnegative hA hAB hr.le)
      (slabRootDifference_tendsto hA hB)
  · have h := (integrableOn_Ioi_deriv_of_nonneg'
      (fun r _ => slabRootDifference_hasDerivAt hB hA r)
      (fun r hr => slabRadialDifference_nonnegative hB hBA hr.le)
      (slabRootDifference_tendsto hB hA)).neg
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext r
    change slabRadialDifference A B r = -slabRadialDifference B A r
    unfold slabRadialDifference
    ring

theorem slabRadialDifference_integral {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (∫ r in Set.Ioi (0:ℝ), slabRadialDifference A B r) = Real.sqrt B-Real.sqrt A := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun r _ => slabRootDifference_hasDerivAt hA hB r)
    (slabRadialDifference_integrable hA hB) (slabRootDifference_tendsto hA hB)
  simpa [slabRootDifference] using h

theorem slabPlanarDifference_integrable {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    Integrable (fun p : PlanarPosition =>
      coulombLineKernel A ‖p‖-coulombLineKernel B ‖p‖) := by
  apply (integrable_fun_norm_addHaar (E := PlanarPosition) volume
    (f := fun r => coulombLineKernel A r-coulombLineKernel B r)).mpr
  simp only [finrank_euclideanSpace_fin, Nat.reduceSub, pow_one, smul_eq_mul]
  exact slabRadialDifference_integrable hA hB

/-- Exact difference of two horizontal Coulomb plane integrals. -/
theorem slabPlanarDifference_integral {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (∫ p : PlanarPosition, coulombLineKernel A ‖p‖-coulombLineKernel B ‖p‖) =
      2*Real.pi*(Real.sqrt B-Real.sqrt A) := by
  have h := integral_fun_norm_addHaar (E := PlanarPosition) volume
    (fun r => coulombLineKernel A r-coulombLineKernel B r)
  simp only [finrank_euclideanSpace_fin, Nat.reduceSub, pow_one, smul_eq_mul,
    nsmul_eq_mul] at h
  have hm : volume.real (Metric.ball (0 : PlanarPosition) 1) = Real.pi := by
    simp [Measure.real, EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_ofReal Real.pi_pos.le]
  have hi : (∫ r in Set.Ioi (0:ℝ),
      r*(coulombLineKernel A r-coulombLineKernel B r)) = Real.sqrt B-Real.sqrt A :=
    slabRadialDifference_integral hA hB
  rw [hm, hi] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabPlanarTail
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inverse-cube tail in two horizontal dimensions. Its exact mass is
`2π/H`, giving the finite-slab truncation error without divergent integrals. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

private theorem slabRadialTail_weight {H : ℝ} (hH : 0 < H) (r : ℝ) :
    r * slabRadialTail H r = (Set.Ioi H).indicator (fun t : ℝ => t ^ (-2 : ℝ)) r := by
  by_cases hr : H < r
  · simp only [slabRadialTail, Set.indicator_of_mem (Set.mem_Ioi.mpr hr)]
    have hp : 0 < r := hH.trans hr
    rw [show (-2 : ℝ) = -3+1 by norm_num, Real.rpow_add hp, Real.rpow_one]
    ring
  · simp [slabRadialTail, hr]

private theorem slabRadialTail_weight_integrable {H : ℝ} (hH : 0 < H) :
    IntegrableOn (fun r : ℝ => r * slabRadialTail H r) (Set.Ioi 0) := by
  have hi := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hH
  have h := (integrable_indicator_iff measurableSet_Ioi).mpr hi
  simpa only [slabRadialTail_weight hH] using h.integrableOn

private theorem slabRadialTail_weight_integral {H : ℝ} (hH : 0 < H) :
    (∫ r in Set.Ioi (0:ℝ), r * slabRadialTail H r) = H⁻¹ := by
  simp_rw [slabRadialTail_weight hH]
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
  rw [Set.Ioi_inter_Ioi, max_eq_left hH.le]
  have h := integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hH
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
  rw [Real.rpow_neg_one]

theorem slabPlanarTail_integrable {H : ℝ} (hH : 0 < H) :
    Integrable (slabPlanarTail H) := by
  apply (integrable_fun_norm_addHaar (E := PlanarPosition) volume
    (f := slabRadialTail H)).mpr
  simp only [finrank_euclideanSpace_fin, Nat.reduceSub, pow_one, smul_eq_mul]
  exact slabRadialTail_weight_integrable hH

theorem slabPlanarTail_nonnegative (H : ℝ) (p : PlanarPosition) :
    0 ≤ slabPlanarTail H p := by
  unfold slabPlanarTail slabRadialTail
  by_cases h : H < ‖p‖
  · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr h)]
    exact Real.rpow_nonneg (norm_nonneg p) _
  · simp [h]

/-- The exact horizontal inverse-cube tail mass. -/
theorem slabPlanarTail_integral {H : ℝ} (hH : 0 < H) :
    (∫ p, slabPlanarTail H p) = 2*Real.pi/H := by
  have h := integral_fun_norm_addHaar (E := PlanarPosition) volume (slabRadialTail H)
  simp only [finrank_euclideanSpace_fin, Nat.reduceSub, pow_one, smul_eq_mul,
    nsmul_eq_mul] at h
  have hm : volume.real (Metric.ball (0 : PlanarPosition) 1) = Real.pi := by
    simp [Measure.real, EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_ofReal Real.pi_pos.le]
  rw [hm, slabRadialTail_weight_integral hH] at h
  change (∫ p, slabRadialTail H ‖p‖) = _
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
  ring

theorem slabPlanarBox_measurable (H : ℝ) : MeasurableSet (slabPlanarBox H) := by
  have h0 : IsClosed {p : PlanarPosition | |p 0| ≤ H} :=
    isClosed_le (by fun_prop) continuous_const
  have h1 : IsClosed {p : PlanarPosition | |p 1| ≤ H} :=
    isClosed_le (by fun_prop) continuous_const
  exact (h0.inter h1).measurableSet

theorem slabPlanarBox_compl_norm {H : ℝ} {p : PlanarPosition}
    (hp : p ∉ slabPlanarBox H) : H < ‖p‖ := by
  by_contra h
  have hn : ‖p‖ ≤ H := le_of_not_gt h
  apply hp
  have h0 : |p 0| ≤ ‖p‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le p 0
  have h1 : |p 1| ≤ ‖p‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le p 1
  exact ⟨h0.trans hn, h1.trans hn⟩

theorem slab_regularized_line_difference_uniform {R S epsilon z w : ℝ}
    (hR : 0 < R) (hz : |z| ≤ S) (hw : |w| ≤ S) :
    |coulombLineKernel (epsilon^2+(z-w)^2) R -
      coulombLineKernel (epsilon^2+w^2) R| ≤ 3*S^2/(2*R^3) := by
  have h := reciprocal_sqrt_difference_bound hR
    (show R^2 ≤ (epsilon^2+(z-w)^2)+R^2 by nlinarith [sq_nonneg epsilon, sq_nonneg (z-w)])
    (show R^2 ≤ (epsilon^2+w^2)+R^2 by nlinarith [sq_nonneg epsilon, sq_nonneg w])
  have hS : 0 ≤ S := (abs_nonneg z).trans hz
  have hz2 : z^2 ≤ S^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg z) hS).mpr hz
  have hzw : |z*w| ≤ S^2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul hz hw (abs_nonneg w) hS
  have ha : |(epsilon^2+(z-w)^2+R^2)-(epsilon^2+w^2+R^2)| ≤ 3*S^2 := by
    rw [show (epsilon^2+(z-w)^2+R^2)-(epsilon^2+w^2+R^2) = z^2-2*(z*w) by ring]
    apply (abs_sub _ _).trans
    rw [abs_of_nonneg (sq_nonneg z), abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith
  exact h.trans (div_le_div_of_nonneg_right ha (by positivity))

/-- The finite square loses at most the integrable radial tail. -/
theorem slabPlanarDifference_tail_bound {H S epsilon z w : ℝ} (hH : 0 < H)
    (hepsilon : epsilon ≠ 0) (hz : |z| ≤ S) (hw : |w| ≤ S) :
    |∫ p in (slabPlanarBox H)ᶜ,
      (coulombLineKernel (epsilon^2+(z-w)^2) ‖p‖-
       coulombLineKernel (epsilon^2+w^2) ‖p‖)| ≤ 3*Real.pi*S^2/H := by
  let f := fun p : PlanarPosition =>
    coulombLineKernel (epsilon^2+(z-w)^2) ‖p‖-
      coulombLineKernel (epsilon^2+w^2) ‖p‖
  have hA : 0 < epsilon^2+(z-w)^2 := add_pos_of_pos_of_nonneg
    (sq_pos_of_ne_zero hepsilon) (sq_nonneg _)
  have hB : 0 < epsilon^2+w^2 := add_pos_of_pos_of_nonneg
    (sq_pos_of_ne_zero hepsilon) (sq_nonneg _)
  have hi : Integrable f := slabPlanarDifference_integrable hA hB
  have ht : Integrable (fun p => (3*S^2/2)*slabPlanarTail H p) :=
    (slabPlanarTail_integrable hH).const_mul _
  have hpt (p : PlanarPosition) (hp : p ∈ (slabPlanarBox H)ᶜ) :
      ‖f p‖ ≤ (3*S^2/2)*slabPlanarTail H p := by
    have hn := slabPlanarBox_compl_norm hp
    have hn0 : 0 < ‖p‖ := hH.trans hn
    have hbound := slab_regularized_line_difference_uniform (epsilon := epsilon) hn0 hz hw
    rw [Real.norm_eq_abs]
    change |coulombLineKernel (epsilon^2+(z-w)^2) ‖p‖-
      coulombLineKernel (epsilon^2+w^2) ‖p‖| ≤ _
    unfold slabPlanarTail slabRadialTail
    rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hn), Real.rpow_neg (norm_nonneg p), Real.rpow_ofNat]
    convert hbound using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hm : (∫ p in (slabPlanarBox H)ᶜ, ‖f p‖) ≤
      ∫ p in (slabPlanarBox H)ᶜ, (3*S^2/2)*slabPlanarTail H p :=
    setIntegral_mono_on hi.norm.integrableOn ht.integrableOn
      (slabPlanarBox_measurable H).compl hpt
  have hall : (∫ p in (slabPlanarBox H)ᶜ, (3*S^2/2)*slabPlanarTail H p) ≤
      ∫ p, (3*S^2/2)*slabPlanarTail H p :=
    setIntegral_le_integral ht (Filter.Eventually.of_forall
      (fun p => mul_nonneg (by positivity) (slabPlanarTail_nonnegative H p)))
  calc
    _ = ‖∫ p in (slabPlanarBox H)ᶜ, f p‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ p in (slabPlanarBox H)ᶜ, ‖f p‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ p, (3*S^2/2)*slabPlanarTail H p := hm.trans hall
    _ = _ := by rw [integral_const_mul, slabPlanarTail_integral hH]; ring

/-- The finite horizontal square differs from the infinite-plane formula by
at most the inverse-cube tail. -/
theorem slabPlanarDifference_estimate {H S epsilon z w : ℝ} (hH : 0 < H)
    (hepsilon : epsilon ≠ 0) (hz : |z| ≤ S) (hw : |w| ≤ S) :
    |(∫ p in slabPlanarBox H,
       (coulombLineKernel (epsilon^2+(z-w)^2) ‖p‖-
        coulombLineKernel (epsilon^2+w^2) ‖p‖)) -
      2*Real.pi*(Real.sqrt (epsilon^2+w^2)-Real.sqrt (epsilon^2+(z-w)^2))| ≤
        3*Real.pi*S^2/H := by
  have hA : 0 < epsilon^2+(z-w)^2 := add_pos_of_pos_of_nonneg
    (sq_pos_of_ne_zero hepsilon) (sq_nonneg _)
  have hB : 0 < epsilon^2+w^2 := add_pos_of_pos_of_nonneg
    (sq_pos_of_ne_zero hepsilon) (sq_nonneg _)
  have hs := integral_add_compl (slabPlanarBox_measurable H)
    (slabPlanarDifference_integrable hA hB)
  rw [slabPlanarDifference_integral hA hB] at hs
  have he : (∫ p in slabPlanarBox H,
       (coulombLineKernel (epsilon^2+(z-w)^2) ‖p‖-
        coulombLineKernel (epsilon^2+w^2) ‖p‖)) -
      2*Real.pi*(Real.sqrt (epsilon^2+w^2)-Real.sqrt (epsilon^2+(z-w)^2)) =
      -(∫ p in (slabPlanarBox H)ᶜ,
       (coulombLineKernel (epsilon^2+(z-w)^2) ‖p‖-
        coulombLineKernel (epsilon^2+w^2) ‖p‖)) := by linarith
  rw [he, abs_neg]
  exact slabPlanarDifference_tail_bound hH hepsilon hz hw

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabProfile
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative removal of the vertical regularization. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ContinuumCoulomb

theorem slab_sqrt_regularization (epsilon a : ℝ) :
    0 ≤ Real.sqrt (epsilon^2+a^2)-|a| ∧
      Real.sqrt (epsilon^2+a^2)-|a| ≤ |epsilon| := by
  have hp : 0 ≤ epsilon^2+a^2 := by positivity
  have hl : |a| ≤ Real.sqrt (epsilon^2+a^2) := by
    rw [← Real.sqrt_sq_eq_abs a]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg epsilon])
  constructor
  · linarith
  · have hs := Real.sq_sqrt hp
    have he := sq_abs epsilon
    have ha := sq_abs a
    nlinarith [Real.sqrt_nonneg (epsilon^2+a^2), abs_nonneg epsilon,
      abs_nonneg a, mul_nonneg (abs_nonneg epsilon) (abs_nonneg a)]

theorem slabRegularizedProfile_error {S z : ℝ} (hS : 0 ≤ S) (hz : |z| ≤ S)
    (epsilon : ℝ) : |slabRegularizedProfile epsilon S z-z^2| ≤ 4*S*|epsilon| := by
  have hc : Continuous (fun w : ℝ => Real.sqrt (epsilon^2+(z-w)^2)-
      Real.sqrt (epsilon^2+w^2)) := by fun_prop
  have hd : Continuous (fun w : ℝ => |z-w|-|w|) := by fun_prop
  rw [slabRegularizedProfile, ← slab_absolute_difference_integral hS hz,
    ← intervalIntegral.integral_sub (hc.intervalIntegrable _ _) (hd.intervalIntegrable _ _)]
  have hbound (w : ℝ) :
      ‖(Real.sqrt (epsilon^2+(z-w)^2)-Real.sqrt (epsilon^2+w^2))-(|z-w|-|w|)‖ ≤
        2*|epsilon| := by
    obtain ⟨ha0,ha1⟩ := slab_sqrt_regularization epsilon (z-w)
    obtain ⟨hb0,hb1⟩ := slab_sqrt_regularization epsilon w
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -S) (b := S) (fun w _ => hbound w)
  rw [Real.norm_eq_abs, sub_neg_eq_add, abs_of_nonneg (by linarith : 0 ≤ S+S)] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem slabRegularizedProfile_tendsto {S z : ℝ} (hS : 0 ≤ S) (hz : |z| ≤ S)
    {epsilon : ℕ → ℝ} (hepsilon : Tendsto epsilon atTop (𝓝 0)) :
    Tendsto (fun n => slabRegularizedProfile (epsilon n) S z) atTop (𝓝 (z^2)) := by
  apply Metric.tendsto_nhds.mpr
  intro delta hdelta
  have hlim : Tendsto (fun n => 4*S*|epsilon n|) atTop (𝓝 0) := by
    simpa using hepsilon.abs.const_mul (4*S)
  filter_upwards [((tendsto_order.1 hlim).2 delta hdelta)] with n hn
  rw [Real.dist_eq]
  exact (slabRegularizedProfile_error hS hz (epsilon n)).trans_lt hn

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabVerticalCoordinates
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical-first coordinates for the actual three-dimensional slab. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem slabVerticalEquiv_symm_apply (p : ℝ × PlanarPosition) :
    slabVerticalEquiv.symm p = WithLp.toLp 2 ![p.2 0, p.2 1, p.1] := by
  ext i
  fin_cases i <;> rfl

theorem slabVerticalEquiv_apply (x : Position) :
    slabVerticalEquiv x = (x 2, WithLp.toLp 2 ![x 0, x 1]) := by
  apply Prod.ext
  · rfl
  · ext i
    fin_cases i <;> rfl

theorem slabVerticalEquiv_measurePreserving : MeasurePreserving slabVerticalEquiv :=
  ((MeasurePreserving.id volume).prod (PiLp.volume_preserving_toLp (Fin 2))).comp
    ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).comp
      (PiLp.volume_preserving_ofLp (Fin 3)))

theorem slabVerticalEquiv_preimage (H S : ℝ) :
    slabVerticalEquiv ⁻¹' (Set.Icc (-S) S ×ˢ slabPlanarBox H) = slabDomain H S := by
  ext x
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Icc, slabVerticalEquiv_apply,
    slabPlanarBox, Set.mem_ofPred_eq, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, slabDomain, abs_le]
  tauto

theorem slabVertical_setIntegral (H S : ℝ) (f : Position → ℝ) :
    (∫ x in slabDomain H S, f x) =
      ∫ p in Set.Icc (-S) S ×ˢ slabPlanarBox H, f (slabVerticalEquiv.symm p) := by
  have h := slabVerticalEquiv_measurePreserving.restrict_preimage
    (s := Set.Icc (-S) S ×ˢ slabPlanarBox H)
    (measurableSet_Icc.prod (slabPlanarBox_measurable H))
  rw [slabVerticalEquiv_preimage] at h
  simpa only [Function.comp_apply, MeasurableEquiv.symm_apply_apply] using
    h.integral_comp' (f ∘ slabVerticalEquiv.symm)

theorem regularizedSlab_vertical_kernel (epsilon z : ℝ) (p : ℝ × PlanarPosition) :
    NeutralAtom.regularizedKernel epsilon (slabAxisPoint z-slabVerticalEquiv.symm p) =
      coulombLineKernel (epsilon^2+(z-p.1)^2) ‖p.2‖ := by
  rw [regularizedKernel_eq_sqrt, slabVerticalEquiv_symm_apply]
  unfold coulombLineKernel
  congr 2
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [slabAxisPoint, PiLp.sub_apply, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
    zero_sub, neg_sq]
  rw [Fin.succ_zero_eq_one]
  ring

theorem regularizedSlab_vertical_integrable {epsilon H S : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (z : ℝ) :
    IntegrableOn (fun p : ℝ × PlanarPosition =>
      coulombLineKernel (epsilon^2+(z-p.1)^2) ‖p.2‖)
      (Set.Icc (-S) S ×ˢ slabPlanarBox H) := by
  have h := slabVerticalEquiv_measurePreserving.restrict_preimage
    (s := Set.Icc (-S) S ×ˢ slabPlanarBox H)
    (measurableSet_Icc.prod (slabPlanarBox_measurable H))
  rw [slabVerticalEquiv_preimage] at h
  have hs := (MeasurePreserving.symm slabVerticalEquiv h).integrable_comp_emb
    (g := fun x : Position => NeutralAtom.regularizedKernel epsilon (slabAxisPoint z-x))
    slabVerticalEquiv.symm.measurableEmbedding
  exact (hs.mpr (regularizedSlab_integrableOn hepsilon hH hS (slabAxisPoint z))).congr
    (Filter.Eventually.of_forall (regularizedSlab_vertical_kernel epsilon z))

theorem regularizedSlab_vertical (epsilon rho : ℝ) {H S : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (z : ℝ) :
    regularizedSlabPotential epsilon rho H S (slabAxisPoint z) =
      -rho * ∫ w in Set.Icc (-S) S, ∫ p in slabPlanarBox H,
        coulombLineKernel (epsilon^2+(z-w)^2) ‖p‖ := by
  unfold regularizedSlabPotential
  rw [slabVertical_setIntegral]
  simp_rw [regularizedSlab_vertical_kernel]
  rw [Measure.volume_eq_prod, setIntegral_prod _
    (regularizedSlab_vertical_integrable hepsilon hH hS z)]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabConfinement
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative confinement by the actual finite rectangular Coulomb slab. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace ContinuumCoulomb

private theorem slabPlanarBox_compact {H : ℝ} (hH : 0 ≤ H) :
    IsCompact (slabPlanarBox H) := by
  have h0 : IsClosed {p : PlanarPosition | |p 0| ≤ H} :=
    isClosed_le (by fun_prop) continuous_const
  have h1 : IsClosed {p : PlanarPosition | |p 1| ≤ H} :=
    isClosed_le (by fun_prop) continuous_const
  apply (isCompact_closedBall (0 : PlanarPosition) (2*(H+1))).of_isClosed_subset (h0.inter h1)
  intro p hp
  have hcoord (i : Fin 2) : |p i| ≤ H := by
    fin_cases i
    · exact hp.1
    · exact hp.2
  have hsq : ‖p‖^2 ≤ 2*H^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      (sq_le_sq₀ (abs_nonneg (p i)) hH).mpr (hcoord i))
    simpa only [sq_abs, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat] using h
  rw [Metric.mem_closedBall, dist_zero_right]
  nlinarith [norm_nonneg p]

private theorem slabPlanarSection_kernel_integrable {epsilon H : ℝ}
    (hepsilon : epsilon ≠ 0) (hH : 0 ≤ H) (z w : ℝ) :
    IntegrableOn (fun p : PlanarPosition => coulombLineKernel (epsilon^2+(z-w)^2) ‖p‖)
      (slabPlanarBox H) :=
  ((coulombLineKernel_continuous (add_pos_of_pos_of_nonneg
    (sq_pos_of_ne_zero hepsilon) (sq_nonneg _))).comp continuous_norm).continuousOn.integrableOn_compact
      (slabPlanarBox_compact hH)

private theorem slabPlanarSection_intervalIntegrable {epsilon H S : ℝ}
    (hepsilon : epsilon ≠ 0) (hH : 0 ≤ H) (hS : 0 ≤ S) (z : ℝ) :
    IntervalIntegrable (slabPlanarSection epsilon H z) volume (-S) S := by
  have hp : Integrable (fun p : ℝ × PlanarPosition =>
      coulombLineKernel (epsilon^2+(z-p.1)^2) ‖p.2‖)
      ((volume.restrict (Set.Icc (-S) S)).prod (volume.restrict (slabPlanarBox H))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact regularizedSlab_vertical_integrable hepsilon hH hS z
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mpr hp.integral_prod_left

private theorem slabPlanarSection_sub {epsilon H : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 ≤ H) (z w : ℝ) :
    slabPlanarSection epsilon H z w-slabPlanarSection epsilon H 0 w =
      ∫ p in slabPlanarBox H,
        (coulombLineKernel (epsilon^2+(z-w)^2) ‖p‖-
          coulombLineKernel (epsilon^2+w^2) ‖p‖) := by
  unfold slabPlanarSection
  rw [← integral_sub (slabPlanarSection_kernel_integrable hepsilon hH z w)
    (slabPlanarSection_kernel_integrable hepsilon hH 0 w)]
  simp only [zero_sub, neg_sq]

private theorem regularizedSlab_vertical_interval (epsilon rho : ℝ) {H S : ℝ}
    (hepsilon : epsilon ≠ 0) (hH : 0 ≤ H) (hS : 0 ≤ S) (z : ℝ) :
    regularizedSlabPotential epsilon rho H S (slabAxisPoint z) =
      -rho * ∫ w in (-S)..S, slabPlanarSection epsilon H z w := by
  rw [regularizedSlab_vertical epsilon rho hepsilon hH hS z,
    intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
  rfl

private theorem slabPlaneError_bound {epsilon H S z w : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 < H) (hz : |z| ≤ S) (hw : |w| ≤ S) :
    |slabPlaneError epsilon H z w| ≤ 3*Real.pi*S^2/H := by
  unfold slabPlaneError
  rw [slabPlanarSection_sub hepsilon hH.le]
  have he := slabPlanarDifference_estimate hH hepsilon hz hw
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

private theorem regularizedSlab_error_identity {epsilon rho H S z : ℝ}
    (hepsilon : epsilon ≠ 0) (hH : 0 ≤ H) (hS : 0 ≤ S) :
    regularizedSlabPotential epsilon rho H S (slabAxisPoint z)-
      regularizedSlabPotential epsilon rho H S (slabAxisPoint 0)-
      2*Real.pi*rho*slabRegularizedProfile epsilon S z =
        -rho*∫ w in (-S)..S, slabPlaneError epsilon H z w := by
  let P := fun w : ℝ => Real.sqrt (epsilon^2+(z-w)^2)-Real.sqrt (epsilon^2+w^2)
  have hP : Continuous P := by dsimp [P]; fun_prop
  have hIz := slabPlanarSection_intervalIntegrable hepsilon hH hS z
  have hI0 := slabPlanarSection_intervalIntegrable hepsilon hH hS 0
  rw [regularizedSlab_vertical_interval epsilon rho hepsilon hH hS z,
    regularizedSlab_vertical_interval epsilon rho hepsilon hH hS 0]
  unfold slabPlaneError slabRegularizedProfile
  rw [intervalIntegral.integral_add (hIz.sub hI0)
    ((hP.intervalIntegrable _ _).const_mul _),
    intervalIntegral.integral_sub hIz hI0, intervalIntegral.integral_const_mul]
  ring

/-- The regularized finite slab differs from its one-dimensional profile
by at most the horizontal inverse-cube tail. -/
theorem regularizedSlab_confinement_error {epsilon rho H S z : ℝ}
    (hepsilon : epsilon ≠ 0) (hrho : 0 ≤ rho) (hH : 0 < H)
    (hS : 0 ≤ S) (hz : |z| ≤ S) :
    |regularizedSlabPotential epsilon rho H S (slabAxisPoint z)-
      regularizedSlabPotential epsilon rho H S (slabAxisPoint 0)-
      2*Real.pi*rho*slabRegularizedProfile epsilon S z| ≤ 6*Real.pi*rho*S^3/H := by
  have hbound (w : ℝ) (hw : w ∈ Set.uIoc (-S) S) :
      ‖slabPlaneError epsilon H z w‖ ≤ 3*Real.pi*S^2/H := by
    have hh : w ∈ Set.Ioc (-S) S := by
      simpa only [Set.uIoc_of_le (by linarith : -S ≤ S)] using hw
    rw [Real.norm_eq_abs]
    exact slabPlaneError_bound hepsilon hH hz (abs_le.mpr ⟨hh.1.le, hh.2⟩)
  have hEI := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [Real.norm_eq_abs, sub_neg_eq_add, abs_of_nonneg (by linarith : 0 ≤ S+S)] at hEI
  rw [regularizedSlab_error_identity hepsilon hH.le hS,
    abs_mul, abs_neg, abs_of_nonneg hrho]
  calc
    _ ≤ rho*((3*Real.pi*S^2/H)*(S+S)) := mul_le_mul_of_nonneg_left hEI hrho
    _ = _ := by ring

/-- The actual singular finite-slab potential has the quadratic profile,
with a uniform error controlled by its finite horizontal extent. -/
theorem slabPotential_axis_error {rho H S z : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 < H) (hS : 0 ≤ S) (hz : |z| ≤ S) :
    |slabPotential rho H S (slabAxisPoint z)-slabPotential rho H S 0-
      2*Real.pi*rho*z^2| ≤ 6*Real.pi*rho*S^3/H := by
  let epsilon : ℕ → ℝ := fun n => ((n:ℝ)+1)⁻¹
  have hep (n : ℕ) : 0 < epsilon n := by dsimp [epsilon]; positivity
  have heps : Tendsto epsilon atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hzlim := regularizedSlabPotential_tendsto hep heps rho hH.le hS (slabAxisPoint z)
  have hzero : slabAxisPoint 0 = 0 := by ext i; fin_cases i <;> rfl
  have h0lim : Tendsto (fun n => regularizedSlabPotential (epsilon n) rho H S (slabAxisPoint 0))
      atTop (𝓝 (slabPotential rho H S 0)) := by
    simpa only [hzero] using
      regularizedSlabPotential_tendsto hep heps rho hH.le hS (slabAxisPoint 0)
  have hplim := (slabRegularizedProfile_tendsto hS hz heps).const_mul (2*Real.pi*rho)
  have hlim : Tendsto (fun n => |regularizedSlabPotential (epsilon n) rho H S (slabAxisPoint z)-
      regularizedSlabPotential (epsilon n) rho H S (slabAxisPoint 0)-
      2*Real.pi*rho*slabRegularizedProfile (epsilon n) S z|) atTop
      (𝓝 |slabPotential rho H S (slabAxisPoint z)-slabPotential rho H S 0-2*Real.pi*rho*z^2|) :=
    ((hzlim.sub h0lim).sub hplim).abs
  apply le_of_tendsto hlim
  exact Filter.Eventually.of_forall (fun n =>
    regularizedSlab_confinement_error (hep n).ne' hrho hH hS hz)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabLineFlatness
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quadratic horizontal variation of a centered Coulomb line integral. -/

noncomputable section
namespace ContinuumCoulomb

theorem coulombLine_boundary_difference {A H x : ℝ} (hA : 0 < A) (hH : 0 < H)
    (hx : |x| ≤ H/2) :
    |coulombLineKernel A (x+H)-coulombLineKernel A (x-H)| ≤ 16*|x|/H^2 := by
  have hlo : -(H/2) ≤ x := (abs_le.mp hx).1
  have hhi : x ≤ H/2 := (abs_le.mp hx).2
  have hp : (H/2)^2 ≤ (x+H)^2 :=
    (sq_le_sq₀ (by positivity) (by linarith)).mpr (by linarith)
  have hn : (H/2)^2 ≤ (H-x)^2 :=
    (sq_le_sq₀ (by positivity) (by linarith)).mpr (by linarith)
  have hb := reciprocal_sqrt_difference_bound (show 0 < H/2 by positivity)
    (show (H/2)^2 ≤ A+(x+H)^2 by linarith)
    (show (H/2)^2 ≤ A+(x-H)^2 by nlinarith)
  have he : (A+(x+H)^2)-(A+(x-H)^2) = 4*H*x := by ring
  rw [he, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<4), abs_of_pos hH] at hb
  change |coulombLineKernel A (x+H)-coulombLineKernel A (x-H)| ≤ _ at hb
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  field_simp
  ring

theorem coulombLineIntegral_quadratic_variation {A H x : ℝ} (hA : 0 < A) (hH : 0 < H)
    (hx : |x| ≤ H/2) :
    |centeredLineIntegral (coulombLineKernel A) H x-
      centeredLineIntegral (coulombLineKernel A) H 0| ≤ 16*x^2/H^2 := by
  let f := centeredLineIntegral (coulombLineKernel A) H
  let d := fun t => coulombLineKernel A (t+H)-coulombLineKernel A (t-H)
  have hd (t : ℝ) : HasDerivAt f (d t) t :=
    centeredLineIntegral_hasDerivAt _ (coulombLineKernel_continuous hA) H t
  have hbound (t : ℝ) (ht : t ∈ Set.Icc (-|x|) |x|) : ‖d t‖ ≤ 16*|x|/H^2 := by
    have ht' : |t| ≤ |x| := abs_le.mpr ht
    have h := coulombLine_boundary_difference hA hH (ht'.trans hx)
    rw [Real.norm_eq_abs]
    exact h.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left ht' (by norm_num)) (sq_nonneg H))
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hd t).hasDerivWithinAt) hbound (convex_Icc (-|x|) |x|)
    (show (0:ℝ) ∈ Set.Icc (-|x|) |x| by constructor <;> linarith [abs_nonneg x])
    (show x ∈ Set.Icc (-|x|) |x| from ⟨neg_abs_le x, le_abs_self x⟩)
  simpa only [Real.norm_eq_abs, sub_zero, f, div_mul_eq_mul_div, mul_assoc, ← pow_two, sq_abs] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabInterior
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Interior horizontal flatness and the full finite-slab approximation. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ContinuumCoulomb

private theorem coulombLine_setIntegral_variation {A H x : ℝ} (hA : 0 < A)
    (hH : 0 < H) (hx : |x| ≤ H/2) :
    |(∫ t in Set.Icc (-H) H, coulombLineKernel A (x-t))-
      (∫ t in Set.Icc (-H) H, coulombLineKernel A (0-t))| ≤ 16*x^2/H^2 := by
  have h := coulombLineIntegral_quadratic_variation hA hH hx
  simp only [centeredLineIntegral_translate,
    intervalIntegral.integral_of_le (show -H ≤ H by linarith),
    ← integral_Icc_eq_integral_Ioc] at h
  exact h

private theorem slabOtherMeasure_mass {H S : ℝ} (hH : 0 ≤ H) (hS : 0 ≤ S)
    (i : Fin 3) (hi : i ≠ 2) :
    (Measure.pi (fun j : Fin 2 => slabAxisMeasure H S (i.succAbove j))).real Set.univ = 4*H*S := by
  rw [Measure.real, Measure.pi_univ, Fin.prod_univ_two, ENNReal.toReal_mul]
  simp only [slabAxisMeasure, Measure.restrict_apply_univ, Real.volume_Icc]
  fin_cases i
  · norm_num [slabSide, Fin.succAbove, ENNReal.toReal_ofReal, hH, hS, Fin.ext_iff]
    ring
  · norm_num [slabSide, Fin.succAbove, ENNReal.toReal_ofReal, hH, hS, Fin.ext_iff]
    ring
  · exact (hi rfl).elim

private theorem slabInteriorSection_integrable {epsilon H S : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (y : Position) (i : Fin 3) :
    Integrable (fun v : Fin 2 → ℝ => ∫ t : ℝ,
      NeutralAtom.regularizedKernel epsilon (y-WithLp.toLp 2 (i.insertNth t v))
      ∂slabAxisMeasure H S i)
      (Measure.pi (fun j : Fin 2 => slabAxisMeasure H S (i.succAbove j))) := by
  have hp := (measurePreserving_piFinSuccAbove (slabAxisMeasure H S) i).symm
  have hi := (hp.integrable_comp_emb
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) i).symm.measurableEmbedding).mpr
      ((slabProduct_integrable H S _).mpr (regularizedSlab_integrableOn hepsilon hH hS y))
  exact hi.integral_prod_right

private theorem regularizedSlab_coordinate_variation {epsilon rho H S : ℝ}
    (hepsilon : epsilon ≠ 0) (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 ≤ S)
    (y : Position) (i : Fin 3) (hi : i ≠ 2) (hy : |y i| ≤ H/2) :
    |regularizedSlabPotential epsilon rho H S y-
      regularizedSlabPotential epsilon rho H S (zeroPositionCoordinate i y)| ≤
        64*rho*S*(y i)^2/H := by
  let mu := Measure.pi (fun j : Fin 2 => slabAxisMeasure H S (i.succAbove j))
  let F := fun (v : Fin 2 → ℝ) => ∫ t : ℝ,
    NeutralAtom.regularizedKernel epsilon (y-WithLp.toLp 2 (i.insertNth t v))
    ∂slabAxisMeasure H S i
  let G := fun (v : Fin 2 → ℝ) => ∫ t : ℝ,
    NeutralAtom.regularizedKernel epsilon (zeroPositionCoordinate i y-
      WithLp.toLp 2 (i.insertNth t v)) ∂slabAxisMeasure H S i
  have hF : Integrable F mu := slabInteriorSection_integrable hepsilon hH.le hS y i
  have hG : Integrable G mu :=
    slabInteriorSection_integrable hepsilon hH.le hS (zeroPositionCoordinate i y) i
  have hb (v : Fin 2 → ℝ) : ‖F v-G v‖ ≤ 16*(y i)^2/H^2 := by
    dsimp only [F, G]
    simp_rw [regularizedKernel_section, zeroPositionCoordinate_same, zeroPositionCoordinate_other]
    have hA : 0 < epsilon^2+∑ j : Fin 2, (y (i.succAbove j)-v j)^2 :=
      add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hepsilon)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    rw [Real.norm_eq_abs]
    change |(∫ t in Set.Icc (-slabSide H S i) (slabSide H S i),
      coulombLineKernel _ (y i-t))-(∫ t in Set.Icc (-slabSide H S i) (slabSide H S i),
      coulombLineKernel _ (0-t))| ≤ _
    rw [show slabSide H S i = H by simp [slabSide, hi]]
    exact coulombLine_setIntegral_variation hA hH hy
  have hI : |(∫ v, F v ∂mu)-(∫ v, G v ∂mu)| ≤ (16*(y i)^2/H^2)*(4*H*S) := by
    rw [← integral_sub hF hG, ← Real.norm_eq_abs]
    have h := norm_integral_le_of_norm_le_const (μ := mu) (f := fun v => F v-G v)
      (Filter.Eventually.of_forall hb)
    simpa only [mu, slabOtherMeasure_mass hH.le hS i hi] using h
  unfold regularizedSlabPotential
  rw [regularizedSlab_sectionIntegral hepsilon hH.le hS y i,
    regularizedSlab_sectionIntegral hepsilon hH.le hS (zeroPositionCoordinate i y) i,
    ← mul_sub, abs_mul, abs_neg, abs_of_nonneg hrho]
  change rho*|(∫ v, F v ∂mu)-(∫ v, G v ∂mu)| ≤ _
  apply (mul_le_mul_of_nonneg_left hI hrho).trans_eq
  field_simp
  ring

theorem slabPotential_coordinate_variation {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 < H) (hS : 0 ≤ S) (y : Position) (i : Fin 3) (hi : i ≠ 2)
    (hy : |y i| ≤ H/2) :
    |slabPotential rho H S y-slabPotential rho H S (zeroPositionCoordinate i y)| ≤
      64*rho*S*(y i)^2/H := by
  let epsilon : ℕ → ℝ := fun n => ((n:ℝ)+1)⁻¹
  have hep (n : ℕ) : 0 < epsilon n := by dsimp [epsilon]; positivity
  have heps : Tendsto epsilon atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hlim := ((regularizedSlabPotential_tendsto hep heps rho hH.le hS y).sub
    (regularizedSlabPotential_tendsto hep heps rho hH.le hS (zeroPositionCoordinate i y))).abs
  exact le_of_tendsto hlim (Filter.Eventually.of_forall (fun n =>
    regularizedSlab_coordinate_variation (hep n).ne' hrho hH hS y i hi hy))

theorem slabPotential_horizontal_variation {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 < H) (hS : 0 ≤ S) (y : Position)
    (hy0 : |y 0| ≤ H/2) (hy1 : |y 1| ≤ H/2) :
    |slabPotential rho H S y-slabPotential rho H S (slabAxisPoint (y 2))| ≤
      64*rho*S*((y 0)^2+(y 1)^2)/H := by
  have h0 := slabPotential_coordinate_variation hrho hH hS y 0 (by decide) hy0
  have h1 := slabPotential_coordinate_variation hrho hH hS (zeroPositionCoordinate 0 y) 1
    (by decide) (by simpa [zeroPositionCoordinate] using hy1)
  have he : zeroPositionCoordinate 1 (zeroPositionCoordinate 0 y) = slabAxisPoint (y 2) := by
    ext j
    fin_cases j <;> simp [zeroPositionCoordinate, slabAxisPoint]
  rw [he] at h1
  have hcoord : zeroPositionCoordinate 0 y 1 = y 1 := by simp [zeroPositionCoordinate]
  rw [hcoord] at h1
  calc
    _ ≤ |slabPotential rho H S y-slabPotential rho H S (zeroPositionCoordinate 0 y)|+
        |slabPotential rho H S (zeroPositionCoordinate 0 y)-slabPotential rho H S (slabAxisPoint (y 2))| :=
      abs_sub_le _ _ _
    _ ≤ 64*rho*S*(y 0)^2/H+64*rho*S*(y 1)^2/H := add_le_add h0 h1
    _ = _ := by ring

/-- The finite slab approximates the harmonic potential throughout its
central horizontal half-box and vertical thickness. -/
theorem slabPotential_interior_error {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 < H) (hS : 0 ≤ S) (y : Position)
    (hy0 : |y 0| ≤ H/2) (hy1 : |y 1| ≤ H/2) (hy2 : |y 2| ≤ S) :
    |slabPotential rho H S y-slabPotential rho H S 0-2*Real.pi*rho*(y 2)^2| ≤
      64*rho*S*((y 0)^2+(y 1)^2)/H+6*Real.pi*rho*S^3/H := by
  have h0 := slabPotential_horizontal_variation hrho hH hS y hy0 hy1
  have h1 := slabPotential_axis_error hrho hH hS hy2
  calc
    _ = |(slabPotential rho H S y-slabPotential rho H S (slabAxisPoint (y 2)))+
        (slabPotential rho H S (slabAxisPoint (y 2))-slabPotential rho H S 0-
          2*Real.pi*rho*(y 2)^2)| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add h0 h1)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabRegularity
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity and global boundedness of the actual slab field, including
its discontinuous density at the slab boundary. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem slabPotential_abs_bound {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (x : Position) :
    |slabPotential rho H S x| ≤
      rho*NeutralAtom.kernelBallMass 1+volume.real (slabDomain H S)*rho := by
  have hb := (NeutralAtom.potential_integrable_and_bound
    (slabDensity_integrable hH hS rho) (slabDensity_nonnegative hrho H S)
    (by norm_num : (0:ℝ)<1) (fun y _ => slabDensity_le hrho H S y) (x := x)).2
  rw [slabDensity_integral] at hb
  rw [slabPotential_eq_negativePotentialOf, abs_neg,
    abs_of_nonneg (NeutralAtom.potentialOf_nonneg (slabDensity_nonnegative hrho H S) x)]
  simpa only [inv_one, one_mul] using hb

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedHigherMoments
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The spatial moments needed to control the finite-slab
operator residual. All moments refer to the actual normalized orbital density. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

private theorem polynomial_exponential_bound (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    t^k*Real.exp (-t/2) ≤ (2:ℝ)^k*(k.factorial:ℝ) := by
  have hf : 0 < (k.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos k)
  have he := Real.pow_div_factorial_le_exp (t/2) (by positivity : 0 ≤ t/2) k
  have hid : ((t/2)^k/(k.factorial:ℝ))*((2:ℝ)^k*(k.factorial:ℝ)) = t^k := by
    rw [div_pow]
    field_simp
  have h := mul_le_mul_of_nonneg_right he
    (show 0 ≤ (2:ℝ)^k*(k.factorial:ℝ) by positivity)
  rw [hid] at h
  have h' := mul_le_mul_of_nonneg_right h (Real.exp_pos (-t/2)).le
  have hc : (Real.exp (t/2)*((2:ℝ)^k*(k.factorial:ℝ)))*Real.exp (-t/2) =
      (2:ℝ)^k*(k.factorial:ℝ) := by
    rw [mul_right_comm,← Real.exp_add]
    rw [show t/2 + -t/2 = 0 by ring, Real.exp_zero, one_mul]
  exact h'.trans_eq hc

theorem normalizedPlanarMode_norm_moment_integrable (k : ℕ) :
    Integrable (fun r : PlanarPosition => ‖r‖^k*normalizedPlanarMode r^2) := by
  let C := planarExponentialConstant (1/2)^2*((2:ℝ)^k*(k.factorial:ℝ))
  have hmajor := (planar_exp_norm_integrable (by norm_num : (0:ℝ)<1/2)).const_mul C
  have hraw : Integrable (fun r : PlanarPosition => ‖r‖^k*planarResolventMode r^2) := by
    apply hmajor.mono'
      ((continuous_norm.pow k).mul (planarResolventMode_C7.continuous.pow 2)).aestronglyMeasurable
    filter_upwards [] with r
    change ‖‖r‖^k*planarResolventMode r^2‖ ≤ C*Real.exp (-(1/2:ℝ)*‖r‖)
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _) (sq_nonneg _))]
    have hm := pow_le_pow_left₀ (planarResolventMode_positive r).le
      (planarResolventMode_exponential_envelope (by norm_num : (0:ℝ)≤1/2)
        (by norm_num : (1/2:ℝ)<1) r) 2
    rw [mul_pow] at hm
    have hex : Real.exp (-(1/2:ℝ)*‖r‖)^2 =
        Real.exp (-‖r‖/2)*Real.exp (-(1/2:ℝ)*‖r‖) := by
      rw [pow_two]
      congr 1
      congr 1
      ring
    rw [hex] at hm
    calc
      _ ≤ ‖r‖^k*(planarExponentialConstant (1/2)^2*
          (Real.exp (-‖r‖/2)*Real.exp (-(1/2:ℝ)*‖r‖))) :=
        mul_le_mul_of_nonneg_left hm (pow_nonneg (norm_nonneg _) _)
      _ = (planarExponentialConstant (1/2)^2*(‖r‖^k*Real.exp (-‖r‖/2)))*
          Real.exp (-(1/2:ℝ)*‖r‖) := by ring
      _ ≤ C*Real.exp (-(1/2:ℝ)*‖r‖) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (polynomial_exponential_bound k (norm_nonneg r))
            (sq_nonneg _)) (Real.exp_pos _).le
  simp_rw [normalizedPlanarMode,div_pow,← mul_div_assoc]
  exact hraw.div_const _

private theorem localizedDensity_even_moment_integrable {freq : ℝ} (hfreq : 0 < freq)
    (k : ℕ) : Integrable (fun x : Position => ‖x‖^(2*k)*localizedDensity freq 0 x) := by
  have hp := (normalizedPlanarMode_norm_moment_integrable (2*k)).mul_prod (verticalMode_square_integrable hfreq)
  have hz := normalizedPlanarMode_square_integrable.mul_prod (verticalMode_moment_integrable hfreq (2*k))
  have hi : Integrable (fun p : SplitPosition => (‖p.1‖^2+p.2^2)^k*localizedMode freq 0 p^2) := by
    apply ((hp.add hz).const_mul ((2:ℝ)^(k-1))).mono'
      ((((continuous_fst.norm.pow 2).add (continuous_snd.pow 2)).pow k).mul
        ((localizedMode_C7 freq 0).continuous.pow 2)).aestronglyMeasurable
    filter_upwards [] with p
    change ‖(‖p.1‖^2+p.2^2)^k*localizedMode freq 0 p^2‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (by positivity) _) (sq_nonneg _))]
    have h : (‖p.1‖^2+p.2^2)^k ≤ (2:ℝ)^(k-1)*(‖p.1‖^(2*k)+p.2^(2*k)) := by
      simpa only [← pow_mul] using add_pow_le (sq_nonneg ‖p.1‖) (sq_nonneg p.2) k
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg (localizedMode freq 0 p))
    convert hm using 1
    all_goals try with_reducible_and_instances rfl
    simp only [localizedMode,sub_zero,mul_pow,Pi.add_apply]
    ring
  have ht := positionSplitCoordinates_measurePreserving.integrable_comp_of_integrable hi
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [Function.comp_apply,localizedDensity,continuumLocalizedMode]
  rw [pow_mul, positionSplitCoordinates_norm_sq]

theorem localizedDensity_fourth_moment_integrable {freq : ℝ} (hfreq : 0 < freq) :
    Integrable (fun x : Position => ‖x‖^4*localizedDensity freq 0 x) :=
  localizedDensity_even_moment_integrable hfreq 2

theorem localizedDensity_eighth_moment_integrable {freq : ℝ} (hfreq : 0 < freq) :
    Integrable (fun x : Position => ‖x‖^8*localizedDensity freq 0 x) :=
  localizedDensity_even_moment_integrable hfreq 4

/-- A wider horizontal slab is needed for simultaneous nuclear cubature and
compressed-energy accuracy. This moment absorbs its polynomial growth. -/
theorem localizedDensity_seventySecond_moment_integrable {freq : ℝ} (hfreq : 0 < freq) :
    Integrable (fun x : Position => ‖x‖^72*localizedDensity freq 0 x) :=
  localizedDensity_even_moment_integrable hfreq 36

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedMomentTail
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Translated fourth/eighth moments and the weighted tails used in the
finite-slab operator estimate. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

private theorem translated_moment {freq : ℝ} (hfreq : 0 < freq) (k : ℕ)
    (hk : Integrable (fun x : Position => ‖x‖^k*localizedDensity freq 0 x))
    (u : PlanarPosition) :
    Integrable (fun x : Position => ‖x‖^k*localizedDensity freq u x) ∧
      localizedDensityMoment freq u k ≤
        (2:ℝ)^(k-1)*(localizedDensityMoment freq 0 k+‖u‖^k) := by
  let c := planarCenter u
  let F (x : Position) := ‖x‖^k*localizedDensity freq 0 x+
    ‖c‖^k*localizedDensity freq 0 x
  have hF : Integrable F := hk.add ((localizedDensity_integrable hfreq 0).const_mul _)
  have hmajor : Integrable (fun x => (2:ℝ)^(k-1)*F (x-c)) :=
    (hF.comp_sub_right c).const_mul _
  have hp (x : Position) : ‖x‖^k*localizedDensity freq u x ≤ (2:ℝ)^(k-1)*F (x-c) := by
    have hn : ‖x‖ ≤ ‖x-c‖+‖c‖ := by
      simpa only [sub_add_cancel] using norm_add_le (x-c) c
    have hb := (pow_le_pow_left₀ (norm_nonneg x) hn k).trans
      (add_pow_le (norm_nonneg (x-c)) (norm_nonneg c) k)
    have hm := mul_le_mul_of_nonneg_right hb (localizedDensity_nonnegative freq 0 (x-c))
    rw [localizedDensity_translate]
    convert hm using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [F, c]
    ring
  have hi : Integrable (fun x : Position => ‖x‖^k*localizedDensity freq u x) := by
    apply hmajor.mono' ((continuous_norm.pow k).mul (localizedDensity_continuous freq u)).aestronglyMeasurable
    filter_upwards [] with x
    change ‖‖x‖^k*localizedDensity freq u x‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg x) k)
      (localizedDensity_nonnegative freq u x))]
    exact hp x
  refine ⟨hi, ?_⟩
  have h := integral_mono hi hmajor hp
  change localizedDensityMoment freq u k ≤ _ at h
  rw [integral_const_mul, integral_sub_right_eq_self] at h
  dsimp [F] at h
  rw [integral_add hk ((localizedDensity_integrable hfreq 0).const_mul _),
    integral_const_mul, localizedDensity_mass hfreq 0, mul_one] at h
  simpa only [c, planarCenter_norm, localizedDensityMoment] using h

theorem localizedDensity_fourth_moment_translate {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) :
    Integrable (fun x : Position => ‖x‖^4*localizedDensity freq u x) ∧
      localizedDensityMoment freq u 4 ≤ 8*(localizedDensityMoment freq 0 4+‖u‖^4) := by
  convert translated_moment hfreq 4 (localizedDensity_fourth_moment_integrable hfreq) u using 1
  all_goals try with_reducible_and_instances rfl
  norm_num

theorem localizedDensity_eighth_moment_translate {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) :
    Integrable (fun x : Position => ‖x‖^8*localizedDensity freq u x) ∧
      localizedDensityMoment freq u 8 ≤ 128*(localizedDensityMoment freq 0 8+‖u‖^8) := by
  convert translated_moment hfreq 8 (localizedDensity_eighth_moment_integrable hfreq) u using 1
  all_goals try with_reducible_and_instances rfl
  norm_num

theorem localizedDensity_seventySecond_moment_translate {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) :
    Integrable (fun x : Position => ‖x‖^72*localizedDensity freq u x) ∧
      localizedDensityMoment freq u 72 ≤
        (2:ℝ)^71*(localizedDensityMoment freq 0 72+‖u‖^72) :=
  translated_moment hfreq 72 (localizedDensity_seventySecond_moment_integrable hfreq) u

private theorem weighted_tail {freq R : ℝ} (hR : 0 < R) (u : PlanarPosition)
    (a b : ℕ) (ha : Integrable (fun x : Position => ‖x‖^a*localizedDensity freq u x))
    (hab : Integrable (fun x : Position => ‖x‖^(a+b)*localizedDensity freq u x))
    {S : Set Position} (hS : MeasurableSet S) (hout : ∀ x ∉ S, R ≤ ‖x‖) :
    (∫ x in Sᶜ, ‖x‖^a*localizedDensity freq u x) ≤
      localizedDensityMoment freq u (a+b)/R^b := by
  have hp (x : Position) (hx : x ∈ Sᶜ) :
      R^b*(‖x‖^a*localizedDensity freq u x) ≤ ‖x‖^(a+b)*localizedDensity freq u x := by
    have h := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hR.le (hout x hx) b)
      (mul_nonneg (pow_nonneg (norm_nonneg x) a) (localizedDensity_nonnegative freq u x))
    simpa only [pow_add, mul_left_comm, mul_assoc] using h
  have h := setIntegral_mono_on (ha.const_mul (R^b)).integrableOn hab.integrableOn hS.compl hp
  have hfull := integral_mono_measure (μ := volume.restrict Sᶜ) Measure.restrict_le_self
    (Filter.Eventually.of_forall (fun x => mul_nonneg (pow_nonneg (norm_nonneg x) (a+b))
      (localizedDensity_nonnegative freq u x))) hab
  rw [integral_const_mul] at h
  apply (le_div_iff₀ (pow_pos hR b)).mpr
  simpa only [localizedDensityMoment, mul_comm] using h.trans hfull

theorem localizedDensity_mass_tail_eighth {freq R : ℝ} (hfreq : 0 < freq) (hR : 0 < R)
    (u : PlanarPosition) {S : Set Position} (hS : MeasurableSet S)
    (hout : ∀ x ∉ S, R ≤ ‖x‖) :
    (∫ x in Sᶜ, localizedDensity freq u x) ≤ localizedDensityMoment freq u 8/R^8 := by
  simpa only [pow_zero, one_mul, zero_add] using weighted_tail hR u 0 8
    (by simpa only [pow_zero, one_mul] using localizedDensity_integrable hfreq u)
    (localizedDensity_eighth_moment_translate hfreq u).1 hS hout

theorem localizedDensity_mass_tail_seventySecond {freq R : ℝ} (hfreq : 0 < freq) (hR : 0 < R)
    (u : PlanarPosition) {S : Set Position} (hS : MeasurableSet S)
    (hout : ∀ x ∉ S, R ≤ ‖x‖) :
    (∫ x in Sᶜ, localizedDensity freq u x) ≤ localizedDensityMoment freq u 72/R^72 := by
  simpa only [pow_zero,one_mul,zero_add] using weighted_tail hR u 0 72
    (by simpa only [pow_zero,one_mul] using localizedDensity_integrable hfreq u)
    (localizedDensity_seventySecond_moment_translate hfreq u).1 hS hout

theorem localizedDensity_fourth_tail_seventySecond {freq R : ℝ} (hfreq : 0 < freq) (hR : 0 < R)
    (u : PlanarPosition) {S : Set Position} (hS : MeasurableSet S)
    (hout : ∀ x ∉ S, R ≤ ‖x‖) :
    (∫ x in Sᶜ, ‖x‖^4*localizedDensity freq u x) ≤ localizedDensityMoment freq u 72/R^68 := by
  exact weighted_tail hR u 4 68 (localizedDensity_fourth_moment_translate hfreq u).1
    (localizedDensity_seventySecond_moment_translate hfreq u).1 hS hout

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabOrbitalResidual
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite slab's actual harmonic-oscillator residual on a localized
orbital. Interior accuracy and weighted tails are kept separately. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem slabResidualMultiplier_abs_bound {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (x : Position) :
    |slabResidualMultiplier rho H S x| ≤
      2*slabUniformBound rho H S+(2*Real.pi*rho)*‖x‖^2 := by
  have hx := slabPotential_abs_bound hrho hH hS x
  have h0 := slabPotential_abs_bound hrho hH hS 0
  have hn : (x 2)^2 ≤ ‖x‖^2 := by
    have h := PiLp.norm_apply_le x 2
    rw [Real.norm_eq_abs] at h
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr h
  have hc : 0 ≤ 2*Real.pi*rho := by positivity
  unfold slabResidualMultiplier
  calc
    _ ≤ |slabPotential rho H S x-slabPotential rho H S 0|+
        |2*Real.pi*rho*(x 2)^2| := abs_sub _ _
    _ ≤ 2*slabUniformBound rho H S+(2*Real.pi*rho)*(x 2)^2 := by
      rw [abs_of_nonneg (mul_nonneg hc (sq_nonneg _))]
      have h := (abs_sub (slabPotential rho H S x) (slabPotential rho H S 0)).trans
        (add_le_add hx h0)
      dsimp [slabUniformBound]
      linarith
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hn hc)

private theorem square_times_density_bound {f : ℝ} {A B t d : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ht : 0 ≤ t) (hd : 0 ≤ d)
    (hf : |f| ≤ A+B*t) : f^2*d ≤ 2*A^2*d+2*B^2*t^2*d := by
  have hs := (sq_le_sq₀ (abs_nonneg f) (by positivity : 0 ≤ A+B*t)).mpr hf
  rw [sq_abs] at hs
  have hq : f^2 ≤ 2*A^2+2*B^2*t^2 := by nlinarith [sq_nonneg (A-B*t)]
  nlinarith [mul_le_mul_of_nonneg_right hq hd]

theorem slabOrbitalResidual_square_integrable {rho H S freq : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 ≤ H) (hS : 0 ≤ S) (hfreq : 0 < freq)
    (u : PlanarPosition) : Integrable (fun x => slabOrbitalResidual rho H S freq u x^2) := by
  let A := 2*slabUniformBound rho H S
  let B := 2*Real.pi*rho
  have hA : 0 ≤ A := by
    have h := slabPotential_abs_bound hrho hH hS (0 : Position)
    have := abs_nonneg (slabPotential rho H S 0)
    dsimp [A, slabUniformBound]
    linarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hmajor : Integrable (fun x : Position =>
      2*A^2*localizedDensity freq u x+2*B^2*(‖x‖^4*localizedDensity freq u x)) :=
    ((localizedDensity_integrable hfreq u).const_mul _).add
      ((localizedDensity_fourth_moment_translate hfreq u).1.const_mul _)
  apply hmajor.mono'
    ((((slabPotential_continuous hrho hH hS).sub continuous_const).sub
      (continuous_const.mul (positionSplitCoordinates.continuous.snd.pow 2))).mul
      (continuumLocalizedMode_C7 freq u).continuous |>.pow 2).aestronglyMeasurable
  filter_upwards [] with x
  change ‖slabOrbitalResidual rho H S freq u x^2‖ ≤ _
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have h := square_times_density_bound hA hB (sq_nonneg ‖x‖)
    (localizedDensity_nonnegative freq u x) (slabResidualMultiplier_abs_bound hrho hH hS x)
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp [slabOrbitalResidual, localizedDensity, A, B] <;> ring)

theorem slabOrbitalResidual_square_bound_seventySecond {rho H S freq R : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 ≤ S) (hfreq : 0 < freq)
    (hR : 0 < R) (hRH : R ≤ H/2) (hRS : R ≤ S) (u : PlanarPosition) :
    (∫ x, slabOrbitalResidual rho H S freq u x^2) ≤
      2*(6*Real.pi*rho*S^3/H)^2+
      2*(64*rho*S/H)^2*localizedDensityMoment freq u 4+
      2*(2*slabUniformBound rho H S)^2*(localizedDensityMoment freq u 72/R^72)+
      2*(2*Real.pi*rho)^2*(localizedDensityMoment freq u 72/R^68) := by
  let K := Metric.closedBall (0 : Position) R
  let a := 6*Real.pi*rho*S^3/H
  let b := 64*rho*S/H
  let A := 2*slabUniformBound rho H S
  let B := 2*Real.pi*rho
  have hK : MeasurableSet K := Metric.isClosed_closedBall.measurableSet
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hA : 0 ≤ A := by
    have h := slabPotential_abs_bound hrho hH.le hS (0 : Position)
    have := abs_nonneg (slabPotential rho H S 0)
    dsimp [A, slabUniformBound]
    linarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hi := slabOrbitalResidual_square_integrable hrho hH.le hS hfreq u
  have hd := localizedDensity_integrable hfreq u
  have h4 := (localizedDensity_fourth_moment_translate hfreq u).1
  have hout (x : Position) (hx : x ∉ K) : R ≤ ‖x‖ := by
    exact (lt_of_not_ge (by simpa only [K, Metric.mem_closedBall, dist_zero_right] using hx)).le
  have hinner (x : Position) (hx : x ∈ K) : |slabResidualMultiplier rho H S x| ≤ a+b*‖x‖^2 := by
    have hnorm : ‖x‖ ≤ R := by simpa only [K, Metric.mem_closedBall, dist_zero_right] using hx
    have hcoord (i : Fin 3) : |x i| ≤ R := by
      simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le x i).trans hnorm
    have hxy : (x 0)^2+(x 1)^2 ≤ ‖x‖^2 := by
      have he := positionSplitCoordinates_norm_sq x
      have hp : ‖(positionSplitCoordinates x).1‖^2 = (x 0)^2+(x 1)^2 := by
        rw [EuclideanSpace.norm_sq_eq]
        simp only [Fin.sum_univ_two, positionSplitCoordinates_fst_zero, positionSplitCoordinates_fst_one, Real.norm_eq_abs, sq_abs]
      rw [hp] at he
      nlinarith [sq_nonneg (x 2)]
    have h := slabPotential_interior_error hrho hH hS x
      ((hcoord 0).trans hRH) ((hcoord 1).trans hRH) ((hcoord 2).trans hRS)
    change |slabResidualMultiplier rho H S x| ≤ _ at h
    calc
      _ ≤ 64*rho*S*((x 0)^2+(x 1)^2)/H+6*Real.pi*rho*S^3/H := h
      _ = a+b*((x 0)^2+(x 1)^2) := by dsimp [a,b]; ring
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hxy hb)
  have hinnerSq (x : Position) (hx : x ∈ K) : slabOrbitalResidual rho H S freq u x^2 ≤
      2*a^2*localizedDensity freq u x+2*b^2*(‖x‖^4*localizedDensity freq u x) := by
    have h := square_times_density_bound ha hb (sq_nonneg ‖x‖)
      (localizedDensity_nonnegative freq u x) (hinner x hx)
    convert h using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp [slabOrbitalResidual, localizedDensity] <;> ring)
  have houterSq (x : Position) : slabOrbitalResidual rho H S freq u x^2 ≤
      2*A^2*localizedDensity freq u x+2*B^2*(‖x‖^4*localizedDensity freq u x) := by
    have h := square_times_density_bound hA hB (sq_nonneg ‖x‖)
      (localizedDensity_nonnegative freq u x) (slabResidualMultiplier_abs_bound hrho hH.le hS x)
    convert h using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp [slabOrbitalResidual, localizedDensity, A, B] <;> ring)
  have hinside := setIntegral_mono_on hi.integrableOn
    ((hd.const_mul (2*a^2)).add (h4.const_mul (2*b^2))).integrableOn hK hinnerSq
  have houtside := setIntegral_mono_on hi.integrableOn
    ((hd.const_mul (2*A^2)).add (h4.const_mul (2*B^2))).integrableOn hK.compl
    (fun x _ => houterSq x)
  simp only [Pi.add_apply] at hinside houtside
  rw [integral_add (hd.const_mul (2*a^2)).integrableOn (h4.const_mul (2*b^2)).integrableOn,
    integral_const_mul, integral_const_mul] at hinside
  rw [integral_add (hd.const_mul (2*A^2)).integrableOn (h4.const_mul (2*B^2)).integrableOn,
    integral_const_mul, integral_const_mul] at houtside
  have hmass : (∫ x in K, localizedDensity freq u x) ≤ 1 := by
    rw [← localizedDensity_mass hfreq u]
    exact integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall (localizedDensity_nonnegative freq u)) hd
  have hmoment : (∫ x in K, ‖x‖^4*localizedDensity freq u x) ≤ localizedDensityMoment freq u 4 :=
    integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall (fun x => mul_nonneg (pow_nonneg (norm_nonneg x) 4)
        (localizedDensity_nonnegative freq u x))) h4
  have ht0 := localizedDensity_mass_tail_seventySecond hfreq hR u hK hout
  have ht4 := localizedDensity_fourth_tail_seventySecond hfreq hR u hK hout
  have hsum := add_le_add (hinside.trans (add_le_add
    (mul_le_mul_of_nonneg_left hmass (by positivity))
    (mul_le_mul_of_nonneg_left hmoment (by positivity))))
    (houtside.trans (add_le_add (mul_le_mul_of_nonneg_left ht0 (by positivity))
      (mul_le_mul_of_nonneg_left ht4 (by positivity))))
  rw [integral_add_compl hK hi] at hsum
  simpa only [mul_one, a, b, A, B, add_assoc] using hsum

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedWellMatrix
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual three-dimensional well matrix elements equal the planar ones:
the transverse Gaussian contributes exactly its unit squared mass. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem localizedWellIntegrand_split (freq : ℝ) (u v w : PlanarPosition) (x : Position) :
    localizedWellIntegrand freq u v w x =
      (normalizedPlanarMode ((positionSplitCoordinates x).1 - u) *
        manufacturedPlanarWell ((positionSplitCoordinates x).1 - w) *
        normalizedPlanarMode ((positionSplitCoordinates x).1 - v)) *
        verticalMode freq (positionSplitCoordinates x).2 ^ 2 := by
  unfold localizedWellIntegrand continuumLocalizedMode localizedMode
  ring

theorem localizedWellIntegrand_integrable {freq : ℝ} (hfreq : 0 < freq) (u v w : PlanarPosition) :
    Integrable (localizedWellIntegrand freq u v w) := by
  have hi : Integrable (fun p : SplitPosition =>
      (normalizedPlanarMode (p.1 - u) * manufacturedPlanarWell (p.1 - w) * normalizedPlanarMode (p.1 - v)) *
        verticalMode freq p.2 ^ 2) := by
    rw [Measure.volume_eq_prod]
    exact (planarWellMatrix_integrable u v w).mul_prod (verticalMode_square_integrable hfreq)
  have h := positionSplitCoordinates_measurePreserving.integrable_comp_of_integrable hi
  simpa only [Function.comp_def, ← localizedWellIntegrand_split] using h

theorem localizedWellIntegrand_integral {freq : ℝ} (hfreq : 0 < freq) (u v w : PlanarPosition) :
    (∫ x, localizedWellIntegrand freq u v w x) = planarWellMatrix u v w := by
  simp_rw [localizedWellIntegrand_split]
  rw [positionSplitCoordinates_integral (fun p =>
      (normalizedPlanarMode (p.1 - u) * manufacturedPlanarWell (p.1 - w) * normalizedPlanarMode (p.1 - v)) *
        verticalMode freq p.2 ^ 2), Measure.volume_eq_prod, integral_prod_mul
      (fun r => normalizedPlanarMode (r - u) * manufacturedPlanarWell (r - w) * normalizedPlanarMode (r - v))
      (fun z => verticalMode freq z ^ 2), verticalMode_normalized hfreq, mul_one]
  rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedWellResidual
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual other-well residual has exponentially small L2 mass.
The square of a nonpositive bounded well is controlled by its negative
well matrix element, so the checked two-tail estimate applies directly. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem localizedWellAction_continuous (freq : ℝ) (u w : PlanarPosition) :
    Continuous (localizedWellAction freq u w) :=
  (manufacturedPlanarWell_C7.continuous.comp
    ((positionSplitCoordinates.continuous.fst).sub continuous_const)).mul
      (continuumLocalizedMode_C7 freq u).continuous

theorem localizedWellAction_memLp {freq : ℝ} (hfreq : 0 < freq) (u w : PlanarPosition) :
    MemLp (localizedWellAction freq u w) 2 := by
  apply (continuumLocalizedMode_memLp hfreq u).of_le_mul
    (c := PlanarSobolev.wellBound) (localizedWellAction_continuous freq u w).aestronglyMeasurable
  filter_upwards [] with x
  rw [localizedWellAction, norm_mul]
  exact mul_le_mul_of_nonneg_right (PlanarSobolev.wellBound_spec _) (norm_nonneg _)

theorem localizedWellAction_square_integrable {freq : ℝ} (hfreq : 0 < freq) (u w : PlanarPosition) :
    Integrable (fun x => localizedWellAction freq u w x ^ 2) :=
  (memLp_two_iff_integrable_sq (localizedWellAction_continuous freq u w).aestronglyMeasurable).mp
    (localizedWellAction_memLp hfreq u w)

theorem localizedWellAction_square_le_matrix {freq : ℝ} (hfreq : 0 < freq) (u w : PlanarPosition) :
    (∫ x, localizedWellAction freq u w x ^ 2) ≤ PlanarSobolev.wellBound * |planarWellMatrix u u w| := by
  have hp (x : Position) : localizedWellAction freq u w x ^ 2 ≤
      PlanarSobolev.wellBound * (-localizedWellIntegrand freq u u w x) := by
    have hn := manufacturedPlanarWell_nonpositive ((positionSplitCoordinates x).1-w)
    have hb := PlanarSobolev.wellBound_spec ((positionSplitCoordinates x).1-w)
    rw [Real.norm_eq_abs, abs_of_nonpos hn] at hb
    have hsq : manufacturedPlanarWell ((positionSplitCoordinates x).1-w)^2 ≤
        PlanarSobolev.wellBound * (-manufacturedPlanarWell ((positionSplitCoordinates x).1-w)) := by
      nlinarith [mul_nonneg (neg_nonneg.mpr hn) (sub_nonneg.mpr hb)]
    have h := mul_le_mul_of_nonneg_right hsq (sq_nonneg (continuumLocalizedMode freq u x))
    unfold localizedWellAction localizedWellIntegrand
    nlinarith only [h]
  have h := integral_mono (localizedWellAction_square_integrable hfreq u w)
    ((localizedWellIntegrand_integrable hfreq u u w).neg.const_mul PlanarSobolev.wellBound) hp
  simp only [Pi.neg_apply] at h
  rw [integral_const_mul, integral_neg, localizedWellIntegrand_integral hfreq] at h
  exact h.trans (mul_le_mul_of_nonneg_left (neg_le_abs _) PlanarSobolev.wellBound_nonnegative)

theorem localizedWellAction_square_decay {freq D : ℝ} (hfreq : 0 < freq)
    (u w : PlanarPosition) (hd : D ≤ ‖u-w‖) :
    (∫ x, localizedWellAction freq u w x ^ 2) ≤
      (PlanarSobolev.wellBound * planarWellMatrixConstant) * Real.exp (-(19/10 : ℝ)*D) := by
  exact (localizedWellAction_square_le_matrix hfreq u w).trans
    ((mul_le_mul_of_nonneg_left (planarWellMatrix_two_far u u w hd hd)
      PlanarSobolev.wellBound_nonnegative).trans_eq (mul_assoc _ _ _).symm)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedMultiwellResidual
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! L2 bounds on the actual differential residuals of the localized modes.
The estimate is polynomial in the number of wells; it does not sum over a
many-electron occupation basis. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem localizedMultiwellResidual_memLp {freq : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (j : Fin m) :
    MemLp (localizedMultiwellResidual freq u j) 2 := by
  classical
  apply memLp_finsetSum
  intro k _
  by_cases hk : k = j
  · simp only [hk, ite_true, if_true]
    exact MemLp.zero
  · simp only [hk, ite_false, if_false]
    exact localizedWellAction_memLp hfreq _ _

theorem localizedMultiwellResidual_square_integrable {freq : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (j : Fin m) :
    Integrable (fun x => localizedMultiwellResidual freq u j x ^ 2) :=
  (localizedMultiwellResidual_memLp hfreq u j).integrable_sq

theorem localizedMultiwellResidual_square_bound {freq D : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖) (j : Fin m) :
    (∫ x, localizedMultiwellResidual freq u j x ^ 2) ≤
      (m : ℝ)^2*(PlanarSobolev.wellBound*planarWellMatrixConstant)*
        Real.exp (-(19/10 : ℝ)*D) := by
  classical
  let f (k : Fin m) (x : Position) :=
    if k = j then 0 else localizedWellAction freq (u j) (u k) x
  have hi (k : Fin m) : Integrable (fun x => f k x ^ 2) := by
    by_cases hk : k = j
    · simp only [f, hk, ite_true, if_true, zero_pow (by norm_num : 2 ≠ 0)]
      exact integrable_zero Position ℝ volume
    · simpa only [f, hk, ite_false, if_false] using localizedWellAction_square_integrable hfreq (u j) (u k)
  have hpoint (x : Position) : localizedMultiwellResidual freq u j x ^ 2 ≤
      (m : ℝ)*(∑ k, f k x ^ 2) := by
    simpa only [localizedMultiwellResidual, f, Finset.card_univ, Fintype.card_fin] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun k => f k x))
  have h := integral_mono (localizedMultiwellResidual_square_integrable hfreq u j)
    ((integrable_finsetSum Finset.univ (fun k _ => hi k)).const_mul (m : ℝ)) hpoint
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun k _ => hi k)] at h
  have hterm (k : Fin m) : (∫ x, f k x ^ 2) ≤
      (PlanarSobolev.wellBound*planarWellMatrixConstant)*Real.exp (-(19/10 : ℝ)*D) := by
    by_cases hk : k = j
    · simp only [f, hk, ite_true, if_true, zero_pow (by norm_num : 2 ≠ 0), integral_zero]
      exact mul_nonneg (mul_nonneg PlanarSobolev.wellBound_nonnegative
        planarWellMatrixConstant_nonnegative) (Real.exp_pos _).le
    · simpa only [f, hk, ite_false, if_false] using
        localizedWellAction_square_decay hfreq (u j) (u k) (hsep j k (Ne.symm hk))
  calc
    _ ≤ (m : ℝ)*(∑ k, ∫ x, f k x ^ 2) := h
    _ ≤ (m : ℝ)*(∑ _k : Fin m,
        (PlanarSobolev.wellBound*planarWellMatrixConstant)*Real.exp (-(19/10 : ℝ)*D)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k _ => hterm k)) (Nat.cast_nonneg m)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_WellFieldOrbitalResidual
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cutoff and depth-counterterm contribution to the actual localized
one-particle residual. The estimate uses polynomially many spatial modes. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem planarWellSum_abs_bound {m : ℕ} (u : Fin m → PlanarPosition) (r : PlanarPosition) :
    |planarWellSum u r| ≤ (m : ℝ)*PlanarSobolev.wellBound := by
  unfold planarWellSum
  calc
    _ ≤ ∑ i, |manufacturedPlanarWell (r-u i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin m, PlanarSobolev.wellBound := Finset.sum_le_sum (fun i _ => by
      simpa only [Real.norm_eq_abs] using PlanarSobolev.wellBound_spec (r-u i))
    _ = _ := by simp

theorem countertermWellSum_sub_eq (freq scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (r : PlanarPosition) :
    countertermWellSum freq scale u r-planarWellSum u r =
      ∑ i, (localizedCounterterm freq u i/scale)*manufacturedPlanarWell (r-u i) := by
  unfold countertermWellSum planarWellSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem countertermWellSum_sub_abs_bound (freq scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) {δ : ℝ}
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ δ) (r : PlanarPosition) :
    |countertermWellSum freq scale u r-planarWellSum u r| ≤
      (m : ℝ)*δ*PlanarSobolev.wellBound := by
  rw [countertermWellSum_sub_eq]
  calc
    _ ≤ ∑ i, |(localizedCounterterm freq u i/scale)*manufacturedPlanarWell (r-u i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin m, δ*PlanarSobolev.wellBound := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (hcoeff i).1]
      exact mul_le_mul (hcoeff i).2 (by
        simpa only [Real.norm_eq_abs] using PlanarSobolev.wellBound_spec (r-u i))
        (abs_nonneg _) ((hcoeff i).1.trans (hcoeff i).2)
    _ = _ := by simp [mul_assoc]

theorem manufacturedWellField_sub_abs_bound (freq scale S : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) {δ : ℝ} (_hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ δ) (x : Position) :
    |manufacturedWellField freq scale S u x-planarWellSum u (positionSplitCoordinates x).1| ≤
      (m : ℝ)*(δ+1)*PlanarSobolev.wellBound := by
  let t := slabWellCutoff S (positionSplitCoordinates x).2
  let a := countertermWellSum freq scale u (positionSplitCoordinates x).1
  let b := planarWellSum u (positionSplitCoordinates x).1
  have ht : 0 ≤ t ∧ t ≤ 1 := slabWellCutoff_bounds _ _
  have hdiff := countertermWellSum_sub_abs_bound freq scale u hcoeff (positionSplitCoordinates x).1
  have hb := planarWellSum_abs_bound u (positionSplitCoordinates x).1
  have h1 : |t-1| ≤ 1 := by rw [abs_of_nonpos (by linarith : t-1 ≤ 0)]; linarith
  have he : t*a-b = t*(a-b)+(t-1)*b := by ring
  change |t*a-b| ≤ _
  rw [he]
  calc
    _ ≤ |t*(a-b)|+|(t-1)*b| := abs_add_le _ _
    _ ≤ (m : ℝ)*δ*PlanarSobolev.wellBound+(m : ℝ)*PlanarSobolev.wellBound := by
      rw [abs_mul, abs_mul, abs_of_nonneg ht.1]
      exact add_le_add
        ((mul_le_mul_of_nonneg_right ht.2 (abs_nonneg _)).trans (by simpa only [one_mul] using hdiff))
        ((mul_le_mul_of_nonneg_right h1 (abs_nonneg _)).trans (by simpa only [one_mul] using hb))
    _ = _ := by ring

theorem wellFieldOrbitalResidual_square_integrable {freq : ℝ} (hfreq : 0 < freq)
    (scale S : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ δ) (j : Fin m) :
    Integrable (fun x => wellFieldOrbitalResidual freq scale S u j x^2) := by
  have hm : MemLp (wellFieldOrbitalResidual freq scale S u j) 2 := by
    apply (continuumLocalizedMode_memLp hfreq (u j)).of_le_mul
      (c := (m : ℝ)*(δ+1)*PlanarSobolev.wellBound)
      ((((manufacturedWellField_C7 freq scale S u).continuous.sub
        ((planarWellSum_continuous u).comp positionSplitCoordinates.continuous.fst)).mul
        (continuumLocalizedMode_C7 freq (u j)).continuous).aestronglyMeasurable)
    filter_upwards [] with x
    change ‖(manufacturedWellField freq scale S u x-planarWellSum u (positionSplitCoordinates x).1)*
      continuumLocalizedMode freq (u j) x‖ ≤ _
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (manufacturedWellField_sub_abs_bound freq scale S u hδ hcoeff x)
      (norm_nonneg _)
  exact hm.integrable_sq

theorem wellFieldOrbitalResidual_square_bound {freq S : ℝ} (hfreq : 0 < freq)
    (hS : 0 < S) (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ δ) (j : Fin m) :
    (∫ x, wellFieldOrbitalResidual freq scale S u j x^2) ≤
      ((m : ℝ)*δ*PlanarSobolev.wellBound)^2+
      ((m : ℝ)*(δ+1)*PlanarSobolev.wellBound)^2*
        (localizedDensityMoment freq (u j) 8/(S/2)^8) := by
  let K := Metric.closedBall (0 : Position) (S/2)
  let A := (m : ℝ)*δ*PlanarSobolev.wellBound
  let B := (m : ℝ)*(δ+1)*PlanarSobolev.wellBound
  have hK : MeasurableSet K := Metric.isClosed_closedBall.measurableSet
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (Nat.cast_nonneg m) hδ) PlanarSobolev.wellBound_nonnegative
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (Nat.cast_nonneg m) (by linarith)) PlanarSobolev.wellBound_nonnegative
  have hi := wellFieldOrbitalResidual_square_integrable hfreq scale S u hδ hcoeff j
  have hd := localizedDensity_integrable hfreq (u j)
  have hp (x : Position) (hx : x ∈ K) : wellFieldOrbitalResidual freq scale S u j x^2 ≤
      A^2*localizedDensity freq (u j) x := by
    have hxnorm : ‖x‖ ≤ S/2 := by simpa only [K, Metric.mem_closedBall, dist_zero_right] using hx
    have hz : |(positionSplitCoordinates x).2| ≤ S/2 := by
      simpa only [positionSplitCoordinates_snd, Real.norm_eq_abs] using
        (PiLp.norm_apply_le x 2).trans hxnorm
    have hb := countertermWellSum_sub_abs_bound freq scale u hcoeff (positionSplitCoordinates x).1
    rw [← manufacturedWellField_inner freq scale hS u x hz] at hb
    have h := mul_le_mul_of_nonneg_right ((sq_le_sq₀ (abs_nonneg _) hA).mpr hb)
      (localizedDensity_nonnegative freq (u j) x)
    simpa only [wellFieldOrbitalResidual, localizedDensity, mul_pow, sq_abs] using h
  have hq (x : Position) : wellFieldOrbitalResidual freq scale S u j x^2 ≤
      B^2*localizedDensity freq (u j) x := by
    have hb := manufacturedWellField_sub_abs_bound freq scale S u hδ hcoeff x
    have h := mul_le_mul_of_nonneg_right ((sq_le_sq₀ (abs_nonneg _) hB).mpr hb)
      (localizedDensity_nonnegative freq (u j) x)
    simpa only [wellFieldOrbitalResidual, localizedDensity, mul_pow, sq_abs] using h
  have hin := setIntegral_mono_on hi.integrableOn (hd.const_mul (A^2)).integrableOn hK hp
  have hout := setIntegral_mono_on hi.integrableOn (hd.const_mul (B^2)).integrableOn hK.compl
    (fun x _ => hq x)
  rw [integral_const_mul] at hin hout
  have hmass : (∫ x in K, localizedDensity freq (u j) x) ≤ 1 := by
    rw [← localizedDensity_mass hfreq (u j)]
    exact integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall (localizedDensity_nonnegative freq (u j))) hd
  have htail := localizedDensity_mass_tail_eighth hfreq (half_pos hS) (u j) hK
    (fun x hx => (lt_of_not_ge (by simpa only [K, Metric.mem_closedBall, dist_zero_right] using hx)).le)
  have h := add_le_add (hin.trans (mul_le_mul_of_nonneg_left hmass (sq_nonneg A)))
    (hout.trans (mul_le_mul_of_nonneg_left htail (sq_nonneg B)))
  rw [integral_add_compl hK hi] at h
  simpa only [mul_one, A, B] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedOrbitalResidual
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The residual for the actual manufactured one-body operator is the sum
of the checked off-site, finite-slab, and cutoff/counterterm residuals. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

private theorem slab_residual_continuous {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (freq : ℝ) (u : PlanarPosition) :
    Continuous (slabOrbitalResidual rho H S freq u) :=
  (((slabPotential_continuous hrho hH hS).sub continuous_const).sub
    (continuous_const.mul (positionSplitCoordinates.continuous.snd.pow 2))).mul
    (continuumLocalizedMode_C7 freq u).continuous

private theorem well_residual_continuous (freq scale S : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (j : Fin m) :
    Continuous (wellFieldOrbitalResidual freq scale S u j) :=
  ((manufacturedWellField_C7 freq scale S u).continuous.sub
    ((planarWellSum_continuous u).comp positionSplitCoordinates.continuous.fst)).mul
    (continuumLocalizedMode_C7 freq (u j)).continuous

theorem manufacturedOrbitalResidual_memLp {rho H S freq : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 ≤ H) (hS : 0 ≤ S) (hfreq : 0 < freq)
    (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ δ) (j : Fin m) :
    MemLp (manufacturedOrbitalResidual rho H S freq scale u j) 2 := by
  have hs : MemLp (slabOrbitalResidual rho H S freq (u j)) 2 :=
    (memLp_two_iff_integrable_sq (slab_residual_continuous hrho hH hS freq (u j)).aestronglyMeasurable).mpr
      (slabOrbitalResidual_square_integrable hrho hH hS hfreq (u j))
  have hw : MemLp (wellFieldOrbitalResidual freq scale S u j) 2 :=
    (memLp_two_iff_integrable_sq (well_residual_continuous freq scale S u j).aestronglyMeasurable).mpr
      (wellFieldOrbitalResidual_square_integrable hfreq scale S u hδ hcoeff j)
  exact ((localizedMultiwellResidual_memLp hfreq u j).add hs).add hw

theorem manufacturedOrbitalResidual_square_integrable {rho H S freq : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 ≤ H) (hS : 0 ≤ S) (hfreq : 0 < freq)
    (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ δ) (j : Fin m) :
    Integrable (fun x => manufacturedOrbitalResidual rho H S freq scale u j x^2) :=
  (manufacturedOrbitalResidual_memLp hrho hH hS hfreq scale u hδ hcoeff j).integrable_sq

theorem manufacturedOrbitalResidual_square_bound {rho H S freq δ D R : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hfreq : 0 < freq)
    (hR : 0 < R) (hRH : R ≤ H/2) (hRS : R ≤ S)
    (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖) (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ δ) (j : Fin m) :
    (∫ x, manufacturedOrbitalResidual rho H S freq scale u j x^2) ≤
      manufacturedOrbitalSquaredError rho H S freq δ D R u j := by
  have hpoint (x : Position) : manufacturedOrbitalResidual rho H S freq scale u j x^2 ≤
      3*(localizedMultiwellResidual freq u j x^2+slabOrbitalResidual rho H S freq (u j) x^2+
        wellFieldOrbitalResidual freq scale S u j x^2) := by
    unfold manufacturedOrbitalResidual
    nlinarith [sq_nonneg (localizedMultiwellResidual freq u j x-slabOrbitalResidual rho H S freq (u j) x),
      sq_nonneg (localizedMultiwellResidual freq u j x-wellFieldOrbitalResidual freq scale S u j x),
      sq_nonneg (slabOrbitalResidual rho H S freq (u j) x-wellFieldOrbitalResidual freq scale S u j x)]
  have hm := localizedMultiwellResidual_square_integrable hfreq u j
  have hs := slabOrbitalResidual_square_integrable hrho hH.le hS.le hfreq (u j)
  have hw := wellFieldOrbitalResidual_square_integrable hfreq scale S u hδ hcoeff j
  have h := integral_mono
    (manufacturedOrbitalResidual_square_integrable hrho hH.le hS.le hfreq scale u hδ hcoeff j)
    (((hm.add hs).add hw).const_mul 3) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_const_mul] at h
  have hsum := integral_add (hm.add hs) hw
  have hpair := integral_add hm hs
  simp only [Pi.add_apply] at hsum hpair
  rw [hsum, hpair] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (localizedMultiwellResidual_square_bound hfreq u hsep j)
      (slabOrbitalResidual_square_bound_seventySecond hrho hH hS.le hfreq hR hRH hRS (u j)))
      (wellFieldOrbitalResidual_square_bound hfreq hS scale u hδ hcoeff j)) (by norm_num))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CorrectedManufacturedResidual
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gram correction preserves a polynomial residual bound: it sums over
spatial modes, independently of the many-electron occupation basis. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem correctedManufacturedResidual_memLp {rho H S freq : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 ≤ H) (hS : 0 ≤ S) (hfreq : 0 < freq)
    (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ j, 0 ≤ localizedCounterterm freq u j/scale ∧
      localizedCounterterm freq u j/scale ≤ δ) (i : Fin m) :
    MemLp (correctedManufacturedResidual rho H S freq scale u i) 2 :=
  memLp_finsetSum Finset.univ (fun j _ =>
    (manufacturedOrbitalResidual_memLp hrho hH hS hfreq scale u hδ hcoeff j).const_mul _)

theorem correctedManufacturedResidual_square_bound {rho H S freq δ D R : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hfreq : 0 < freq)
    (hR : 0 < R) (hRH : R ≤ H/2) (hRS : R ≤ S)
    (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : m*localizedOverlapBound D ≤ 1/2) (hδ : 0 ≤ δ)
    (hcoeff : ∀ j, 0 ≤ localizedCounterterm freq u j/scale ∧
      localizedCounterterm freq u j/scale ≤ δ) (i : Fin m) :
    (∫ x, correctedManufacturedResidual rho H S freq scale u i x^2) ≤
      4*(m : ℝ)*(∑ j, manufacturedOrbitalSquaredError rho H S freq δ D R u j) := by
  have hraw (j : Fin m) :=
    manufacturedOrbitalResidual_square_integrable hrho hH.le hS.le hfreq scale u hδ hcoeff j
  have hc (j : Fin m) : correctedLocalizedCoefficients u i j^2 ≤ 4 := by
    have h := (correctedLocalizedCoefficients_entries u hsep hs i j).2
    calc
      _ = |correctedLocalizedCoefficients u i j|^2 := (sq_abs _).symm
      _ ≤ (2:ℝ)^2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = 4 := by norm_num
  have hpoint (x : Position) : correctedManufacturedResidual rho H S freq scale u i x^2 ≤
      4*(m : ℝ)*(∑ j, manufacturedOrbitalResidual rho H S freq scale u j x^2) := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun j => correctedLocalizedCoefficients u i j*manufacturedOrbitalResidual rho H S freq scale u j x)
    simp only [Finset.card_univ,Fintype.card_fin] at h
    change correctedManufacturedResidual rho H S freq scale u i x^2 ≤ _ at h
    apply h.trans
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      mul_le_mul_of_nonneg_right (hc j) (sq_nonneg (manufacturedOrbitalResidual rho H S freq scale u j x)))
    simp only [mul_pow] at *
    have hmul := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg m : (0:ℝ) ≤ m)
    calc
      _ ≤ (m:ℝ)*(∑ j, 4*manufacturedOrbitalResidual rho H S freq scale u j x^2) := hmul
      _ = _ := by rw [← Finset.mul_sum]; ring
  have hi := integral_mono
    (correctedManufacturedResidual_memLp hrho hH.le hS.le hfreq scale u hδ hcoeff i).integrable_sq
    ((integrable_finsetSum Finset.univ (fun j _ => hraw j)).const_mul (4*(m:ℝ))) hpoint
  rw [integral_const_mul,integral_finsetSum Finset.univ (fun j _ => hraw j)] at hi
  exact hi.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ =>
    manufacturedOrbitalResidual_square_bound hrho hH hS hfreq hR hRH hRS scale u hsep hδ hcoeff j))
    (by positivity))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_SpinTensorResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tensor residual bounds in the full physical spin measure, with the exact
mass of the weak-H1 finite tensor state as normalization. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem flatRealSpinOrbital_norm_sq (f : Position → ℝ) (hf : MemLp f 2) (σ : Fin 2) :
    (∫ x, ‖Coulomb.flatSpinOrbital (realSpinOrbital f σ) x‖^2 ∂Coulomb.spinSpaceMeasure) =
      ∫ x, f x^2 := by
  have h := Coulomb.flatSpinOrbital_inner (realSpinOrbital f σ) (realSpinOrbital f σ)
    (realSpinOrbital_memLp f hf σ) (realSpinOrbital_memLp f hf σ)
  have hn (z : ℂ) : star z*z = ((‖z‖^2:ℝ):ℂ) := by
    simpa only [starRingEnd_apply,Complex.ofReal_pow] using Complex.conj_mul' z
  rw [realSpinOrbital_inner] at h
  simp_rw [hn] at h
  rw [integral_complex_ofReal] at h
  simpa only [ite_true, if_true,← pow_two,Complex.ofReal_inj] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedTensorResidual
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual corrected manufactured orbital residuals, lifted to both spin
components and all electron coordinates, satisfy a polynomial L2 estimate. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem localizedSpinResidual_sum_norm {rho H S freq : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 ≤ H) (hS : 0 ≤ S) (hfreq : 0 < freq)
    (scale : ℝ) {m : ℕ} (u : Fin (m+1) → PlanarPosition) {η : ℝ} (hη : 0 ≤ η)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ η) :
    (∑ j, ∫ x, ‖Coulomb.flatSpinOrbital (localizedSpinResidual rho H S freq scale u j) x‖^2
      ∂Coulomb.spinSpaceMeasure) =
      2*∑ i, ∫ x, correctedManufacturedResidual rho H S freq scale u i x^2 := by
  simp only [localizedSpinResidual,flatRealSpinOrbital_norm_sq _
    (correctedManufacturedResidual_memLp hrho hH hS hfreq scale u hη hcoeff _)]
  rw [(HubbardGlobal.siteModes m).symm.sum_comp
    (fun p : Fin (m+1) × Fin 2 => ∫ x, correctedManufacturedResidual rho H S freq scale u p.1 x^2)]
  simp only [Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,← Finset.mul_sum]
  norm_num

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedTensorProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounds on the actual finite tensor projection for the manufactured
potential, including its full weak-H1 orthogonal remainder. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem localizedSpinResidual_sum_bound_oai {rho H S freq η D R : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hfreq : 0 < freq)
    (hR : 0 < R) (hRH : R ≤ H/2) (hRS : R ≤ S)
    (scale : ℝ) {m : ℕ} (u : Fin (m+1) → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : (m+1:ℕ)*localizedOverlapBound D ≤ 1/2) (hη : 0 ≤ η)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ η) :
    (∑ j, ∫ x, ‖Coulomb.flatSpinOrbital (localizedSpinResidual rho H S freq scale u j) x‖^2
      ∂Coulomb.spinSpaceMeasure) ≤
      8*(m+1:ℕ)^2*∑ j, manufacturedOrbitalSquaredError rho H S freq η D R u j := by
  rw [localizedSpinResidual_sum_norm hrho hH.le hS.le hfreq scale u hη hcoeff]
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    correctedManufacturedResidual_square_bound hrho hH hS hfreq hR hRH hRS
      scale u hsep hs hη hcoeff i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at he
  nlinarith only [he]

end ContinuumCoulomb

end

end OAI
end

theorem solution : type_of% @OAI.ContinuumCoulomb.localizedSpinResidual_sum_bound_oai := @OAI.ContinuumCoulomb.localizedSpinResidual_sum_bound_oai
