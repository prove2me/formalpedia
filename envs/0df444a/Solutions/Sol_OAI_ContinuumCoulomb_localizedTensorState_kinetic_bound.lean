-- Prove2me | solution 1 for OAI.ContinuumCoulomb.localizedTensorState_kinetic_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:55:50.220057+00:00
-- url     : https://prove2.me/submissions/acf002a7-7b48-4333-ae4e-639bf769f8ca

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
import Theorems.Thm_OAI_ContinuumCoulomb_localizedSpinResidual_sum_bound

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FormDomain_Add
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
open ContinuousLinearMap
open scoped Convolution

lemma mass_nonneg {n : ℕ} (ψ : H1Vector n) : 0 ≤ mass ψ :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))

end Coulomb
end
end

end OAI
end

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
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_PairRegroup
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
namespace Coulomb

lemma integrable_finite_count_prod {S E F : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] [MeasurableSpace E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {μ : Measure E} (f : S × E → F)
    (hf : ∀ s, Integrable (fun x => f (s,x)) μ) : Integrable f (Measure.count.prod μ) := by
  rw [Measure.prod, Measure.count,
    Measure.bind_sum _ _ (measurable_of_countable _).aemeasurable]
  simp only [Measure.dirac_bind (measurable_of_countable _)]
  refine integrable_sum_measure (fun spin => ?_) (hasSum_fintype _).summable
  exact (measurableEmbedding_prodMk_left spin).integrable_map_iff.mpr (hf spin)

lemma integral_finite_count_prod {S E F : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] [MeasurableSpace E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {μ : Measure E} [SFinite μ] (f : S × E → F)
    (hf : ∀ s, Integrable (fun x => f (s,x)) μ) :
    (∫ sx, f sx ∂(Measure.count.prod μ)) = ∑ s, ∫ x, f (s,x) ∂μ := by
  rw [integral_prod _ (integrable_finite_count_prod f hf), integral_count]
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_ConfigurationMeasurableEquiv
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
namespace Coulomb

open scoped Classical

open scoped Classical

theorem configurationMeasurableEquiv_apply (n : ℕ) (x : Configuration n) (i : Fin n) :
    configurationMeasurableEquiv n x i = position x i := rfl

theorem tensorOrbital_inner_integral {n : ℕ} {α : Type*}
    (v : α → Space → Fin 2 → ℂ) (b c : Fin n → α) :
    (∑ s : Spins n, ∫ x, star (tensorOrbital v b s x) * tensorOrbital v c s x) =
      ∏ i, ∑ t : Fin 2, ∫ y, star (v (b i) y t) * v (c i) y t := by
  classical
  have hi : ∀ s : Spins n,
      (∫ x, star (tensorOrbital v b s x) * tensorOrbital v c s x) =
      ∏ i, ∫ y, star (v (b i) y (s i)) * v (c i) y (s i) := by
    intro s
    calc
      _ = ∫ x : Fin n → Space, ∏ i, star (v (b i) (x i) (s i)) * v (c i) (x i) (s i) := by
        rw [← (configurationMeasurableEquiv_measurePreserving n).integral_comp']
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          simp only [tensorOrbital, star_prod, Finset.prod_mul_distrib,
            configurationMeasurableEquiv_apply]
      _ = _ := integral_fintype_prod_volume_eq_prod
        (fun i (y : Space) => star (v (b i) y (s i)) * v (c i) y (s i))
  simp_rw [hi]
  exact (Fintype.prod_sum fun i (t : Fin 2) => ∫ y, star (v (b i) y t) * v (c i) y t).symm

lemma norm_toLp_sq_complex {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {f : A → ℂ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  calc
    (↑(‖hf.toLp f‖ ^ 2) : ℂ) = inner ℂ (hf.toLp f) (hf.toLp f) := by
      simp [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
    _ = ∫ x, star (f x) * f x ∂μ := inner_toLp_complex hf hf
    _ = ∫ x, (↑(‖f x‖ ^ 2) : ℂ) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        rw [mul_comm, Complex.ofReal_pow]
        exact inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (f x)

lemma H1Vector.toHilbert_norm_sq {n : ℕ} (ψ : H1Vector n) :
    ‖ψ.toHilbert‖ ^ 2 = mass ψ := by
  rw [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_congr rfl fun s _ => norm_toLp_sq_complex (ψ.value_L2 s)

lemma tensorHilbert_inner {n : ℕ} {α : Type*}
    (v : α → Space → Fin 2 → ℂ)
    (hv : ∀ a s, MemLp (fun x => v a x s) 2 volume)
    (b c : Fin n → α) :
    inner ℂ (tensorHilbert v hv b) (tensorHilbert v hv c) =
      ∏ i, ∑ t : Fin 2, ∫ y, star (v (b i) y t) * v (c i) y t := by
  rw [PiLp.inner_apply]
  simp only [tensorHilbert, WithLp.ofLp_toLp, inner_toLp_complex]
  exact tensorOrbital_inner_integral v b c

lemma tensorHilbert_orthonormal {n : ℕ} {α : Type*}
    (v : α → Space → Fin 2 → ℂ)
    (hv : ∀ a s, MemLp (fun x => v a x s) 2 volume)
    (ho : ∀ a c, (∑ t : Fin 2, ∫ y, star (v a y t) * v c y t) =
      if a = c then (1 : ℂ) else 0) :
    Orthonormal ℂ (tensorHilbert (n := n) v hv) := by
  classical
  rw [orthonormal_iff_ite]
  intro b c
  rw [tensorHilbert_inner]
  simp_rw [ho]
  by_cases h : b = c
  · subst c; simp
  · rw [ite_eq_right h]
    have hi : ∃ i, b i ≠ c i := by
      by_contra hh
      apply h
      funext i
      exact not_not.mp (not_exists.mp hh i)
    obtain ⟨i, hi⟩ := hi
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [ite_eq_right hi]

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
-- module Solutions.OAIQ092_CC.CoulombRadii_FormDomain_OrbitalHilbertBasis
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

section GeneralFermionSpace
variable {A ι : Type*} [MeasurableSpace A] {μ : Measure A} [SigmaFinite μ]

lemma scalarTensor_inner_integral {n : ℕ} (v : ι → A → ℂ) (b c : Fin n → ι) :
    (∫ x : Fin n → A, star (∏ i, v (b i) (x i)) * (∏ i, v (c i) (x i))
      ∂(Measure.pi fun _ => μ)) = ∏ i, ∫ a, star (v (b i) a) * v (c i) a ∂μ := by
  simp only [star_prod, ← Finset.prod_mul_distrib]
  exact integral_fintype_prod_eq_prod (μ := fun _ : Fin n => μ)
    (fun i a => star (v (b i) a) * v (c i) a)

lemma scalarTensor_orthonormal {n : ℕ} (v : ι → A → ℂ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0) :
    ∀ b c : Fin n → ι, (∫ x, star (∏ i, v (b i) (x i)) * (∏ i, v (c i) (x i))
      ∂(Measure.pi fun _ => μ)) = if b = c then (1 : ℂ) else 0 := by
  intro b c
  rw [scalarTensor_inner_integral]
  simp_rw [ho]
  by_cases h : b = c
  · subst c; simp
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ : ∃ i, b i ≠ c i := by
      by_contra hh
      apply h
      funext i
      exact not_not.mp (not_exists.mp hh i)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact ite_eq_right hi

end GeneralFermionSpace

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_TsumFixed
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb

variable {A ι : Type*} [MeasurableSpace A] {μ : Measure A}
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)

include ho in
lemma orbital_orthonormal : Orthonormal ℂ (fun i => (hv i).toLp (v i)) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [inner_toLp_complex]
  exact ho i j

lemma orbital_sum_toLp (s : Finset ι) (c : ι → ℂ) :
    (orbital_sum_memLp v hv s c).toLp (fun x => ∑ i ∈ s, c i * v i x) =
      ∑ i ∈ s, c i • (hv i).toLp (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; rfl
  | @insert a s ha ih =>
    have he : (fun x => ∑ i ∈ insert a s, c i * v i x) =
        (fun x => c a * v a x) + (fun x => ∑ i ∈ s, c i * v i x) := by
      funext x
      simp [Finset.sum_insert ha]
    rw [show (orbital_sum_memLp v hv (insert a s) c).toLp _ =
      ((hv a).const_mul (c a)).toLp (fun x => c a * v a x) +
      (orbital_sum_memLp v hv s c).toLp (fun x => ∑ i ∈ s, c i * v i x) from by
        simpa only [he] using ((hv a).const_mul (c a)).toLp_add
          (orbital_sum_memLp v hv s c)]
    rw [ih, Finset.sum_insert ha]
    congr 1

include hv ho in
lemma orbital_sum_sq (s : Finset ι) (c : ι → ℂ) :
    (∫ x, ‖∑ i ∈ s, c i * v i x‖^2 ∂μ) = ∑ i ∈ s, ‖c i‖^2 := by
  rw [← norm_toLp_sq_complex (orbital_sum_memLp v hv s c), orbital_sum_toLp v hv s c]
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum]
  calc
    (↑(‖∑ i ∈ s, c i • (hv i).toLp (v i)‖^2) : ℂ) =
        inner ℂ (∑ i ∈ s, c i • (hv i).toLp (v i))
          (∑ i ∈ s, c i • (hv i).toLp (v i)) := by
      simp [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
    _ = ∑ i ∈ s, star (c i) * c i := (orbital_orthonormal v hv ho).inner_sum c c s
    _ = ∑ i ∈ s, (↑(‖c i‖^2) : ℂ) := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [starRingEnd_apply, Complex.ofReal_pow] using Complex.conj_mul' (c i)

end Coulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_SpinCubeEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace Coulomb
lemma measurePreserving_const_uncurry {I J A : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace A] (μ : Measure A) [SigmaFinite μ] :
    MeasurePreserving (MeasurableEquiv.curry I J A).symm
      (Measure.pi fun _ : I => Measure.pi fun _ : J => μ)
      (Measure.pi fun _ : I × J => μ) := by
  refine ⟨(MeasurableEquiv.curry I J A).symm.measurable, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [(MeasurableEquiv.curry I J A).symm.map_apply]
  have he : (MeasurableEquiv.curry I J A).symm ⁻¹' univ.pi s =
      univ.pi (fun i => univ.pi (fun j => s (i,j))) := by
    ext x
    simp only [mem_preimage, mem_univ_pi, MeasurableEquiv.curry_symm_apply]
    exact ⟨fun h i j => h (i,j), fun h p => h p.1 p.2⟩
  rw [he, Measure.pi_pi]
  simp only [Measure.pi_pi, Fintype.prod_prod_type]

lemma measure_pi_count {I A : Type*} [Fintype I] [Fintype A]
    [MeasurableSpace A] [MeasurableSingletonClass A] :
    (Measure.pi fun _ : I => (Measure.count : Measure A)) = Measure.count := by
  apply Measure.ext_of_singleton
  intro x
  simp only [Measure.pi_singleton, Measure.count_singleton, Finset.prod_const_one]

end Coulomb

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_IntegrableIntegralAeTendsto
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
namespace Coulomb

lemma spinCubeEquiv_full_measurePreserving (n : ℕ) :
    MeasurePreserving (spinCubeEquiv n) (Measure.pi fun _ : Fin n => spinSpaceMeasure)
      (Measure.count.prod volume) := by
  have h1 := measurePreserving_arrowProdEquivProdArrow (Fin 2) (Fin 3 → ℝ) (Fin n)
    (fun _ => Measure.count) (fun _ => volume)
  rw [measure_pi_count] at h1
  have h2 := (MeasurePreserving.id (Measure.count : Measure (Spins n))).prod
    (measurePreserving_const_uncurry (I := Fin n) (J := Fin 3) (volume : Measure ℝ))
  exact h2.comp h1

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

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
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_SpinConfigurationIntegral
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
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
lemma spinConfiguration_integral {n : ℕ} (F : Spins n → Configuration n → ℝ)
    (hF : ∀ s, Integrable (F s)) :
    (∫ z, F ((spinCubeEquiv n) z).1 (WithLp.toLp 2 ((spinCubeEquiv n) z).2)
      ∂(Measure.pi fun _ : Fin n => spinSpaceMeasure)) = ∑ s, ∫ x, F s x := by
  rw [(spinCubeEquiv_full_measurePreserving n).integral_comp'
    (fun sx => F sx.1 (WithLp.toLp 2 sx.2))]
  have hm : MeasurePreserving (MeasurableEquiv.toLp 2 ((Fin n × Fin 3) → ℝ)) volume volume :=
    PiLp.volume_preserving_toLp _
  rw [integral_finite_count_prod _ (fun s => hm.integrable_comp_of_integrable (hF s))]
  apply Finset.sum_congr rfl
  intro s _
  exact hm.integral_comp' (F s)

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarGroundTransform
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The planar manufactured well's ground-state transform. Integration by
parts establishes positivity on actual compact C¹ test functions. Existence,
decay and the excitation gap of the specific resolvent-generated mode remain
separate analytic steps. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem planarPartial_C1 {phi : PlanarPosition → ℝ} (hphi : ContDiff ℝ 2 phi)
    (e : PlanarPosition) : ContDiff ℝ 1 (planarPartial phi e) :=
  (hphi.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).clm_apply contDiff_const

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarHeatLimit
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Gaussian change of scale and the actual time-zero limit of the heat
average. The bound by the normalized time-one Gaussian permits dominated
convergence even though the Gaussian has noncompact support. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ContinuumCoulomb

theorem planarHeatKernel_sqrt_scale {t : ℝ} (ht : 0 < t) (r : PlanarPosition) :
    planarHeatKernel t (Real.sqrt t • r) = t⁻¹ * planarHeatKernel 1 r := by
  have hs : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  rw [planarHeatKernel, planarHeatKernel, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, hs]
  have he : -(t * ‖r‖ ^ 2) / (4 * t) = -‖r‖ ^ 2 / (4 * 1) := by
    field_simp
  rw [he]
  ring

theorem planarHeatAverage_scaled {t : ℝ} (ht : 0 < t) (r : PlanarPosition) :
    planarHeatAverage t r = ∫ b, planarHeatKernel 1 b * planarForcing (r - Real.sqrt t • b) := by
  have hi := Measure.integral_comp_smul_of_nonneg (volume : Measure PlanarPosition)
    (fun b => planarHeatKernel t b * planarForcing (r - b)) (Real.sqrt t)
    (hR := Real.sqrt_nonneg t)
  simp only [finrank_euclideanSpace_fin, Real.sq_sqrt ht.le, smul_eq_mul,
    planarHeatKernel_sqrt_scale ht] at hi
  simp_rw [mul_assoc] at hi
  rw [integral_const_mul] at hi
  exact (mul_left_cancel₀ (inv_ne_zero ht.ne') hi).symm

theorem planarScaledHeatIntegrand_measurable (t : ℝ) (r : PlanarPosition) :
    AEStronglyMeasurable (fun b => planarHeatKernel 1 b *
      planarForcing (r - Real.sqrt t • b)) := by
  have hc : Continuous (fun b : PlanarPosition => r - Real.sqrt t • b) := by fun_prop
  exact ((planarHeatKernel_continuous 1).mul
    (planarForcing_C7.continuous.comp hc)).aestronglyMeasurable

theorem planarScaledHeatIntegrand_bound (t : ℝ) (r b : PlanarPosition) :
    ‖planarHeatKernel 1 b * planarForcing (r - Real.sqrt t • b)‖ ≤ planarHeatKernel 1 b := by
  have hk : 0 < planarHeatKernel 1 b := planarHeatKernel_positive (by norm_num) b
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hk.le (planarForcing_nonnegative _))]
  exact mul_le_of_le_one_right hk.le (planarForcing_le_one _)

theorem planarScaledHeatIntegrand_tendsto (r b : PlanarPosition) :
    Tendsto (fun t : ℝ => planarHeatKernel 1 b * planarForcing (r - Real.sqrt t • b))
      (𝓝[>] (0 : ℝ)) (𝓝 (planarHeatKernel 1 b * planarForcing r)) := by
  have hs : Tendsto (fun t : ℝ => Real.sqrt t • b) (𝓝[>] 0) (𝓝 (0 : PlanarPosition)) := by
    have hs0 : Tendsto Real.sqrt (𝓝 (0 : ℝ)) (𝓝 (Real.sqrt 0)) :=
      Real.continuous_sqrt.continuousAt.tendsto
    simpa only [Real.sqrt_zero, zero_smul] using
      (hs0.mono_left nhdsWithin_le_nhds).smul_const b
  have hr : Tendsto (fun t : ℝ => r - Real.sqrt t • b) (𝓝[>] 0) (𝓝 r) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hs
  exact tendsto_const_nhds.mul (planarForcing_C7.continuous.continuousAt.tendsto.comp hr)

theorem planarHeatAverage_tendsto_zero (r : PlanarPosition) :
    Tendsto (fun t => planarHeatAverage t r) (𝓝[>] (0 : ℝ)) (𝓝 (planarForcing r)) := by
  have hconv : Tendsto
      (fun t : ℝ => ∫ b, planarHeatKernel 1 b * planarForcing (r - Real.sqrt t • b))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ b, planarHeatKernel 1 b * planarForcing r)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (F := fun t b => planarHeatKernel 1 b * planarForcing (r - Real.sqrt t • b))
      (f := fun b => planarHeatKernel 1 b * planarForcing r)
      (bound := planarHeatKernel 1)
    · exact Eventually.of_forall (fun t => planarScaledHeatIntegrand_measurable t r)
    · exact Eventually.of_forall (fun t => Eventually.of_forall (fun b =>
        planarScaledHeatIntegrand_bound t r b))
    · exact planarHeatKernel_integrable (by norm_num)
    · exact Eventually.of_forall (planarScaledHeatIntegrand_tendsto r)
  have hv : (∫ b, planarHeatKernel 1 b * planarForcing r) = planarForcing r := by
    rw [integral_mul_const, planarHeatKernel_integral (by norm_num), one_mul]
  rw [hv] at hconv
  apply hconv.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (planarHeatAverage_scaled ht r).symm

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarHeatDifferential
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise differential identities for the actual two-dimensional Gaussian
kernel. Its time derivative is its coordinate Laplacian. -/

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace BigOperators
namespace ContinuumCoulomb

theorem planarHeatKernel_C2 (t : ℝ) : ContDiff ℝ 2 (planarHeatKernel t) := by
  unfold planarHeatKernel
  exact contDiff_const.mul (((contDiff_norm_sq ℝ).neg.div_const (4 * t)).exp)

theorem planarHeatKernel_hasDerivAt {t : ℝ} (ht : 0 < t) (r : PlanarPosition) :
    HasDerivAt (fun s => planarHeatKernel s r) (planarHeatTimeDerivative t r) t := by
  have hi := hasDerivAt_inv ht.ne'
  have h := (hi.const_mul ((4 * Real.pi)⁻¹)).mul
    ((hi.const_mul (-‖r‖ ^ 2 / 4)).exp)
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
  · beta_reduce
    change planarHeatKernel s r = (4 * Real.pi)⁻¹ * s⁻¹ * Real.exp (-‖r‖ ^ 2 / 4 * s⁻¹)
    unfold planarHeatKernel
    congr 1 <;> ring_nf
  · dsimp [planarHeatTimeDerivative, planarHeatKernel]
    have he : -‖r‖ ^ 2 / (4 * t) = -‖r‖ ^ 2 / 4 * t⁻¹ := by ring
    rw [he]
    field_simp
    ring

theorem planarHeatKernel_partial (t : ℝ) (e r : PlanarPosition) :
    planarPartial (planarHeatKernel t) e r =
      (-inner ℝ e r / (2 * t)) * planarHeatKernel t r := by
  have hd := ((((hasStrictFDerivAt_norm_sq r).hasFDerivAt.neg).mul_const (4 * t)⁻¹).exp).const_mul
    ((4 * Real.pi * t)⁻¹)
  change fderiv ℝ (planarHeatKernel t) r e = _
  rw [show fderiv ℝ (planarHeatKernel t) r = _ from hd.fderiv]
  simp only [smul_apply, smul_eq_mul, neg_apply, Pi.neg_apply,
    innerSL_apply_apply, planarHeatKernel]
  rw [real_inner_comm r e]
  ring_nf

theorem planarHeatKernel_partial_partial (t : ℝ) (e r : PlanarPosition) :
    planarPartial (planarPartial (planarHeatKernel t) e) e r =
      ((inner ℝ e r) ^ 2 / (4 * t ^ 2) - ‖e‖ ^ 2 / (2 * t)) * planarHeatKernel t r := by
  have hlin : ContDiff ℝ 1 (fun s : PlanarPosition => -inner ℝ e s / (2 * t)) :=
    ((innerSL ℝ e).contDiff.neg).div_const _
  have heq : planarPartial (planarHeatKernel t) e =
      fun s => (-inner ℝ e s / (2 * t)) * planarHeatKernel t s :=
    funext (planarHeatKernel_partial t e)
  rw [heq, planarPartial_mul _ _ hlin ((planarHeatKernel_C2 t).of_le (by norm_num)),
    planarHeatKernel_partial]
  have hpart : planarPartial (fun s : PlanarPosition => -inner ℝ e s / (2 * t)) e r =
      -‖e‖ ^ 2 / (2 * t) := by
    have hd := ((innerSL ℝ e).hasFDerivAt (x := r)).neg.mul_const (2 * t)⁻¹
    have hd' : HasFDerivAt (fun s : PlanarPosition => -inner ℝ e s / (2 * t))
        ((2 * t)⁻¹ • -(innerSL ℝ e)) r := by
      simpa only [Pi.neg_apply, innerSL_apply_apply, div_eq_mul_inv] using hd
    change fderiv ℝ (fun s : PlanarPosition => -inner ℝ e s / (2 * t)) r e = _
    rw [hd'.fderiv]
    simp only [smul_apply, smul_eq_mul, neg_apply,
      innerSL_apply_apply, real_inner_self_eq_norm_sq]
    ring
  rw [hpart]
  ring

theorem planarHeatKernel_laplacian (t : ℝ) (r : PlanarPosition) :
    planarLaplacian (planarHeatKernel t) r = planarHeatTimeDerivative t r := by
  have hn : ‖r‖ ^ 2 = ∑ a : Fin 2, (r a) ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using EuclideanSpace.norm_sq_eq r
  have ha (a : Fin 2) : inner ℝ (planarAxis a) r = r a := by
    simp [planarAxis, EuclideanSpace.inner_single_left]
  have he (a : Fin 2) : ‖planarAxis a‖ ^ 2 = 1 := by simp [planarAxis]
  simp only [planarLaplacian, planarHeatKernel_partial_partial, ha, he,
    planarHeatTimeDerivative, hn, Fin.sum_univ_two]
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarHeatEvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiation in time of the actual heat average. The compact forcing
allows a fixed compact dominating set on every positive time neighborhood. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ContinuumCoulomb

theorem planarHeatAverage_flip (t : ℝ) (r : PlanarPosition) :
    planarHeatAverage t r = ∫ b, planarHeatKernel t (r - b) * planarForcing b := by
  unfold planarHeatAverage
  rw [← integral_sub_left_eq_self _ volume r]
  simp only [sub_sub_self]

theorem planarHeatTimeDerivative_forcing_continuous (t : ℝ) (r : PlanarPosition) :
    Continuous (fun b => planarHeatTimeDerivative t (r - b) * planarForcing b) := by
  have hg : Continuous (fun b : PlanarPosition => planarHeatTimeDerivative t (r - b)) := by
    unfold planarHeatTimeDerivative planarHeatKernel
    fun_prop
  exact hg.mul planarForcing_C7.continuous

theorem planarHeatTimeDerivative_forcing_joint_continuousAt (r : PlanarPosition)
    {p : ℝ × PlanarPosition} (hp : 0 < p.1) :
    ContinuousAt (fun q : ℝ × PlanarPosition =>
      planarHeatTimeDerivative q.1 (r - q.2) * planarForcing q.2) p := by
  have h4 : 4 * p.1 ≠ 0 := by positivity
  have h42 : 4 * p.1 ^ 2 ≠ 0 := by positivity
  have hpi : 4 * Real.pi * p.1 ≠ 0 := by positivity
  have hne : p.1 ≠ 0 := hp.ne'
  have hcomp : ContinuousAt (fun q : ℝ × PlanarPosition => planarHeatTimeDerivative q.1 (r - q.2)) p := by
    unfold planarHeatTimeDerivative planarHeatKernel
    fun_prop
  have hf : Continuous (fun q : ℝ × PlanarPosition => planarForcing q.2) :=
    planarForcing_C7.continuous.comp continuous_snd
  exact hcomp.mul hf.continuousAt

theorem planarHeatTimeDerivative_local_bound {t : ℝ} (ht : 0 < t) (r : PlanarPosition) :
    ∃ bound : PlanarPosition → ℝ, Integrable bound ∧
      ∀ b s, s ∈ Set.Ioo (t / 2) (3 * t / 2) →
        ‖planarHeatTimeDerivative s (r - b) * planarForcing b‖ ≤ bound b := by
  let S : Set (ℝ × PlanarPosition) := Set.Icc (t / 2) (3 * t / 2) ×ˢ tsupport planarForcing
  let F : ℝ × PlanarPosition → ℝ := fun p =>
    planarHeatTimeDerivative p.1 (r - p.2) * planarForcing p.2
  have hS : IsCompact S := isCompact_Icc.prod planarForcing_hasCompactSupport
  have hF : ContinuousOn F S := by
    intro p hp
    have hpos : 0 < p.1 := lt_of_lt_of_le (by linarith) hp.1.1
    exact (planarHeatTimeDerivative_forcing_joint_continuousAt r hpos).continuousWithinAt
  obtain ⟨C, hC⟩ := hS.bddAbove_image hF.norm
  let bound : PlanarPosition → ℝ := (tsupport planarForcing).indicator (fun _ => max 0 C)
  refine ⟨bound, ?_, ?_⟩
  · exact (integrable_indicator_iff (isClosed_tsupport _).measurableSet).mpr
      (integrableOn_const planarForcing_hasCompactSupport.measure_ne_top)
  · intro b s hs
    by_cases hb : b ∈ tsupport planarForcing
    · have hf : ‖F (s, b)‖ ≤ C := hC ⟨(s, b), ⟨⟨hs.1.le, hs.2.le⟩, hb⟩, rfl⟩
      simpa only [bound, Set.indicator_of_mem hb] using hf.trans (le_max_right 0 C)
    · simp only [bound, Set.indicator_of_notMem hb, image_eq_zero_of_notMem_tsupport hb,
        mul_zero, norm_zero, le_refl]

theorem planarHeatAverage_hasDerivAt {t : ℝ} (ht : 0 < t) (r : PlanarPosition) :
    HasDerivAt (fun s => planarHeatAverage s r)
      (∫ b, planarHeatTimeDerivative t (r - b) * planarForcing b) t := by
  obtain ⟨bound, hbi, hb⟩ := planarHeatTimeDerivative_local_bound ht r
  have hn : Set.Ioo (t / 2) (3 * t / 2) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have hi : Integrable (fun b => planarHeatKernel t (r - b) * planarForcing b) :=
    ((planarHeatKernel_continuous t).comp (continuous_const.sub continuous_id)
      |>.mul planarForcing_C7.continuous).integrable_of_hasCompactSupport
      planarForcing_hasCompactSupport.mul_left
  have hmeas : ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable (fun b => planarHeatKernel s (r - b) * planarForcing b) :=
    Eventually.of_forall (fun s => ((planarHeatKernel_continuous s).comp
      (continuous_const.sub continuous_id) |>.mul planarForcing_C7.continuous).aestronglyMeasurable)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s b => planarHeatKernel s (r - b) * planarForcing b)
    (F' := fun s b => planarHeatTimeDerivative s (r - b) * planarForcing b)
    hn hmeas hi (planarHeatTimeDerivative_forcing_continuous t r).aestronglyMeasurable
    (Eventually.of_forall hb) hbi
    (Eventually.of_forall (fun b s hs => (planarHeatKernel_hasDerivAt
      (by linarith [hs.1] : 0 < s) (r - b)).mul_const (planarForcing b)))
  simpa only [← planarHeatAverage_flip] using hd.2

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarLaplaceIBP
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two integrations by parts transfer the planar Laplacian from the
Gaussian kernel to the compact forcing. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem planarPartial_reflect {f : PlanarPosition → ℝ} (hf : ContDiff ℝ 1 f)
    (r e x : PlanarPosition) :
    planarPartial (fun y => f (r - y)) e x = -planarPartial f e (r - x) := by
  have hd := ((hf.differentiable (by norm_num) (r - x)).hasFDerivAt).comp x
    ((hasFDerivAt_const r x).sub (hasFDerivAt_id x))
  change fderiv ℝ (fun y => f (r - y)) x e = -(fderiv ℝ f (r - x) e)
  rw [show fderiv ℝ (fun y => f (r - y)) x = _ from hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, zero_sub, neg_apply,
    ContinuousLinearMap.id_apply, map_neg]

theorem planarPartial_neg {f : PlanarPosition → ℝ} (hf : ContDiff ℝ 1 f)
    (e x : PlanarPosition) :
    planarPartial (fun y => -f y) e x = -planarPartial f e x := by
  have hd := (hf.differentiable (by norm_num) x).hasFDerivAt.neg
  change fderiv ℝ (fun y => -f y) x e = -(fderiv ℝ f x e)
  rw [show fderiv ℝ (fun y => -f y) x = _ from hd.fderiv]
  simp only [neg_apply]

theorem planarLaplacian_reflect {f : PlanarPosition → ℝ} (hf : ContDiff ℝ 2 f)
    (r x : PlanarPosition) :
    planarLaplacian (fun y => f (r - y)) x = planarLaplacian f (r - x) := by
  apply Finset.sum_congr rfl
  intro a _
  have hp := planarPartial_C1 hf (planarAxis a)
  have hpr : ContDiff ℝ 1 (fun y => planarPartial f (planarAxis a) (r - y)) :=
    hp.comp (contDiff_const.sub contDiff_id)
  rw [show planarPartial (fun y => f (r - y)) (planarAxis a) =
      fun y => -planarPartial f (planarAxis a) (r - y) from
    funext (planarPartial_reflect (hf.of_le (by norm_num)) r (planarAxis a)),
    planarPartial_neg hpr, planarPartial_reflect hp, neg_neg]

theorem planar_integral_mul_laplacian_C2 (f phi : PlanarPosition → ℝ)
    (hf : ContDiff ℝ 2 f) (hphi : ContDiff ℝ 2 phi) (hc : HasCompactSupport phi) :
    (∫ x, f x * planarLaplacian phi x) = ∫ x, planarLaplacian f x * phi x := by
  have hp (g : PlanarPosition → ℝ) (hg : ContDiff ℝ 2 g) (v : PlanarPosition) :
      ContDiff ℝ 1 (planarPartial g v) :=
    (hg.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).clm_apply contDiff_const
  have hpp (g : PlanarPosition → ℝ) (hg : ContDiff ℝ 2 g) (v : PlanarPosition) :
      Continuous (planarPartial (planarPartial g v) v) :=
    (((hp g hg v).fderiv_right (show (0 : WithTop ℕ∞) + 1 ≤ 1 by norm_num)).clm_apply
      contDiff_const).continuous
  have hpc (v : PlanarPosition) : HasCompactSupport (planarPartial phi v) :=
    hc.fderiv_apply ℝ v
  have hppc (v : PlanarPosition) : HasCompactSupport (planarPartial (planarPartial phi v) v) :=
    (hpc v).fderiv_apply ℝ v
  have hleft (v : PlanarPosition) : Integrable (fun x => f x * planarPartial (planarPartial phi v) v x) :=
    (hf.continuous.mul (hpp phi hphi v)).integrable_of_hasCompactSupport (hppc v).mul_left
  have hright (v : PlanarPosition) : Integrable (fun x => planarPartial (planarPartial f v) v x * phi x) :=
    ((hpp f hf v).mul hphi.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hcross (v : PlanarPosition) : Integrable (fun x => planarPartial f v x * planarPartial phi v x) :=
    ((hp f hf v).continuous.mul (hp phi hphi v).continuous).integrable_of_hasCompactSupport
      (hpc v).mul_left
  have hfg (v : PlanarPosition) : Integrable (fun x => f x * planarPartial phi v x) :=
    (hf.continuous.mul (hp phi hphi v).continuous).integrable_of_hasCompactSupport
      (hpc v).mul_left
  have hfpg (v : PlanarPosition) : Integrable (fun x => planarPartial f v x * phi x) :=
    ((hp f hf v).continuous.mul hphi.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hby (v : PlanarPosition) :
      (∫ x, f x * planarPartial (planarPartial phi v) v x) =
        ∫ x, planarPartial (planarPartial f v) v x * phi x := by
    calc
      _ = -(∫ x, planarPartial f v x * planarPartial phi v x) :=
        integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
          (hcross v) (hleft v) (hfg v)
          (fun x _ => hf.differentiable (by norm_num) x)
          (fun x _ => (hp phi hphi v).differentiable (by norm_num) x)
      _ = _ := by
        have h : (∫ x, planarPartial f v x * planarPartial phi v x) =
            -(∫ x, planarPartial (planarPartial f v) v x * phi x) :=
          integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
            (hright v) (hcross v) (hfpg v)
            (fun x _ => (hp f hf v).differentiable (by norm_num) x)
            (fun x _ => hphi.differentiable (by norm_num) x)
        rw [h, neg_neg]
  simp_rw [planarLaplacian, Finset.mul_sum]
  rw [integral_finsetSum _ (fun a _ => hleft (planarAxis a))]
  simp_rw [hby]
  rw [← integral_finsetSum _ (fun a _ => hright (planarAxis a))]
  simp_rw [Finset.sum_mul]

theorem planarLaplacian_continuous {f : PlanarPosition → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (planarLaplacian f) :=
  continuous_finsetSum _ (fun a _ =>
    planarPartial_continuous (planarPartial_C1 hf (planarAxis a)) (planarAxis a))

theorem planarLaplacian_hasCompactSupport {f : PlanarPosition → ℝ} (hc : HasCompactSupport f) :
    HasCompactSupport (planarLaplacian f) := by
  change HasCompactSupport (fun x => ∑ a : Fin 2,
    fderiv ℝ (fun y => fderiv ℝ f y (planarAxis a)) x (planarAxis a))
  have h := HasCompactSupport.finset_sum (s := Finset.univ)
    (fun a _ => (hc.fderiv_apply ℝ (planarAxis a)).fderiv_apply ℝ (planarAxis a))
  simpa only [Finset.sum_fn] using h

theorem planarHeatAverage_hasDerivAt_laplacian {t : ℝ} (ht : 0 < t) (r : PlanarPosition) :
    HasDerivAt (fun s => planarHeatAverage s r)
      (∫ b, planarHeatKernel t b * planarLaplacian planarForcing (r - b)) t := by
  have hf2 : ContDiff ℝ 2 planarForcing := planarForcing_C7.of_le (by norm_num)
  have hr : ContDiff ℝ 2 (fun b : PlanarPosition => planarForcing (r - b)) :=
    hf2.comp (contDiff_const.sub contDiff_id)
  have hrc : HasCompactSupport (fun b : PlanarPosition => planarForcing (r - b)) :=
    planarForcing_hasCompactSupport.comp_homeomorph (Homeomorph.subLeft r)
  have heq : (∫ b, planarHeatTimeDerivative t (r - b) * planarForcing b) =
      ∫ b, planarHeatKernel t b * planarLaplacian planarForcing (r - b) := by
    calc
      _ = ∫ b, planarHeatTimeDerivative t b * planarForcing (r - b) := by
        rw [← integral_sub_left_eq_self _ volume r]
        simp only [sub_sub_self]
      _ = ∫ b, planarLaplacian (planarHeatKernel t) b * planarForcing (r - b) := by
        simp only [planarHeatKernel_laplacian]
      _ = ∫ b, planarHeatKernel t b * planarLaplacian (fun y => planarForcing (r - y)) b :=
        (planar_integral_mul_laplacian_C2 _ _ (planarHeatKernel_C2 t) hr hrc).symm
      _ = _ := by simp only [planarLaplacian_reflect hf2]
  rw [← heq]
  exact planarHeatAverage_hasDerivAt ht r

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarModeDerivatives
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual first and second directional derivatives of the resolvent mode.
Differentiation is transferred to the compact forcing, which also gives
finite L¹ and L² derivatives without differentiating the singular kernel. -/

noncomputable section
open MeasureTheory
open scoped Convolution
namespace ContinuumCoulomb

theorem planarResolventMode_partial_partial (e v r : PlanarPosition) :
    planarPartial (planarPartial planarResolventMode e) v r =
      planarResolventOf (planarPartial (planarPartial planarForcing e) v) r := by
  rw [show planarPartial planarResolventMode e =
    planarResolventOf (planarPartial planarForcing e) from funext (planarResolventMode_partial e)]
  exact planarResolventOf_partial
    (planarPartial_C1 (planarForcing_C7.of_le (by norm_num)) e)
    (planarForcing_hasCompactSupport.fderiv_apply ℝ e) v r

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarResolventEquation
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The differential eigen-equation of the constructed resolvent mode is
obtained from its heat representation and the fundamental theorem of calculus,
not supplied as an assumption. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace ContinuumCoulomb

theorem planarResolvent_joint_integrable {g : PlanarPosition → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) (r : PlanarPosition) :
    Integrable (fun p : ℝ × PlanarPosition => planarResolventIntegrand p * g (r - p.2))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume : Measure PlanarPosition)) := by
  obtain ⟨B, hB⟩ := hg.bounded_above_of_compact_support hc
  apply planarResolventIntegrand_integrable.mul_bdd
    ((hg.comp (continuous_const.sub continuous_snd)).aestronglyMeasurable)
  exact Eventually.of_forall (fun p => by
    change ‖g (r - p.2)‖ ≤ B
    exact hB _)

theorem planarResolventOf_heat_representation {g : PlanarPosition → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) (r : PlanarPosition) :
    planarResolventOf g r = ∫ t in Set.Ioi (0 : ℝ),
      Real.exp (-t) * ∫ b, planarHeatKernel t b * g (r - b) := by
  unfold planarResolventOf planarResolventKernel
  simp_rw [← integral_mul_const]
  rw [← integral_integral_swap (planarResolvent_joint_integrable hg hc r)]
  simp_rw [planarResolventIntegrand, mul_assoc, integral_const_mul]

theorem planarResolventOf_heat_integrable {g : PlanarPosition → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) (r : PlanarPosition) :
    IntegrableOn (fun t => Real.exp (-t) * ∫ b, planarHeatKernel t b * g (r - b))
      (Set.Ioi (0 : ℝ)) := by
  have h := (planarResolvent_joint_integrable hg hc r).integral_prod_left
  change Integrable _ _
  simpa only [planarResolventIntegrand, mul_assoc, integral_const_mul] using h

theorem planarResolventMode_laplacian_integral (r : PlanarPosition) :
    planarLaplacian planarResolventMode r = planarResolventOf (planarLaplacian planarForcing) r := by
  have hi (a : Fin 2) : Integrable (fun b => planarResolventKernel b *
      planarPartial (planarPartial planarForcing (planarAxis a)) (planarAxis a) (r - b)) :=
    ((planarForcing_hasCompactSupport.fderiv_apply ℝ (planarAxis a)).fderiv_apply ℝ
      (planarAxis a)).convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
      planarResolventKernel_integrable.locallyIntegrable
      (planarPartial_continuous (planarPartial_C1 (planarForcing_C7.of_le (by norm_num)) _) _) r
  unfold planarLaplacian
  simp_rw [planarResolventMode_partial_partial]
  change (∑ a : Fin 2, ∫ b, planarResolventKernel b *
      planarPartial (planarPartial planarForcing (planarAxis a)) (planarAxis a) (r - b)) =
    ∫ b, planarResolventKernel b * ∑ a : Fin 2,
      planarPartial (planarPartial planarForcing (planarAxis a)) (planarAxis a) (r - b)
  rw [← integral_finsetSum _ (fun a _ => hi a)]
  simp only [Finset.mul_sum]

theorem planarHeatResolventPrimitive_hasDerivAt (r : PlanarPosition) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (planarHeatResolventPrimitive r) (planarHeatResolventDerivative r t) t := by
  have he : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    simpa only [Pi.neg_apply, id_eq, mul_neg, mul_one] using (hasDerivAt_id t).neg.exp
  have hd := he.mul (planarHeatAverage_hasDerivAt_laplacian ht r)
  have hd' : HasDerivAt (fun s => Real.exp (-s) * planarHeatAverage s r)
      (planarHeatResolventDerivative r t) t := by
    convert hd using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [planarHeatResolventDerivative]
    ring
  apply hd'.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  simp only [planarHeatResolventPrimitive, ite_eq_right (show s ≠ 0 from (show 0 < s from hs).ne')]

theorem planarHeatResolventPrimitive_continuousWithinAt (r : PlanarPosition) :
    ContinuousWithinAt (planarHeatResolventPrimitive r) (Set.Ici (0 : ℝ)) 0 := by
  have he : Tendsto (fun t : ℝ => Real.exp (-t)) (𝓝[>] 0) (𝓝 1) := by
    have he0 : Tendsto (fun t : ℝ => Real.exp (-t)) (𝓝 (0 : ℝ)) (𝓝 (Real.exp (-0))) :=
      (Real.continuous_exp.comp continuous_neg).continuousAt.tendsto
    simpa only [neg_zero, Real.exp_zero] using
      he0.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hlim := he.mul (planarHeatAverage_tendsto_zero r)
  apply continuousWithinAt_Ioi_iff_Ici.mp
  change Tendsto _ _ (𝓝 (planarHeatResolventPrimitive r 0))
  rw [planarHeatResolventPrimitive_zero]
  have hlim' : Tendsto (fun t => Real.exp (-t) * planarHeatAverage t r)
      (𝓝[>] (0 : ℝ)) (𝓝 (planarForcing r)) := by simpa only [one_mul] using hlim
  apply hlim'.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [planarHeatResolventPrimitive, ite_eq_right (show t ≠ 0 from (show 0 < t from ht).ne')]

theorem planarHeatResolventDerivative_integrable (r : PlanarPosition) :
    IntegrableOn (planarHeatResolventDerivative r) (Set.Ioi (0 : ℝ)) :=
  (planarResolventOf_heat_integrable
    (planarLaplacian_continuous (planarForcing_C7.of_le (by norm_num)))
    (planarLaplacian_hasCompactSupport planarForcing_hasCompactSupport) r).sub
    (planarResolventMode_heat_integrable r)

theorem planarHeatResolventPrimitive_integrable (r : PlanarPosition) :
    IntegrableOn (planarHeatResolventPrimitive r) (Set.Ioi (0 : ℝ)) := by
  apply (planarResolventMode_heat_integrable r).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [planarHeatResolventPrimitive, ite_eq_right (show t ≠ 0 from (show 0 < t from ht).ne')]

theorem planarResolventMode_equation (r : PlanarPosition) :
    planarLaplacian planarResolventMode r = planarResolventMode r - planarForcing r := by
  have hd := fun t (ht : t ∈ Set.Ioi (0 : ℝ)) => planarHeatResolventPrimitive_hasDerivAt r ht
  have hzero := tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi hd
    (planarHeatResolventDerivative_integrable r) (planarHeatResolventPrimitive_integrable r)
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto
    (planarHeatResolventPrimitive_continuousWithinAt r) hd
    (planarHeatResolventDerivative_integrable r) hzero
  have hL := planarResolventOf_heat_representation
    (planarLaplacian_continuous (planarForcing_C7.of_le (by norm_num)))
    (planarLaplacian_hasCompactSupport planarForcing_hasCompactSupport) r
  have hLi := planarResolventOf_heat_integrable
    (planarLaplacian_continuous (planarForcing_C7.of_le (by norm_num)))
    (planarLaplacian_hasCompactSupport planarForcing_hasCompactSupport) r
  simp only [planarHeatResolventDerivative, planarHeatResolventPrimitive_zero, zero_sub,
    integral_sub hLi (planarResolventMode_heat_integrable r), ← hL,
    ← planarResolventMode_heat_representation, ← planarResolventMode_laplacian_integral] at hFTC
  linarith

theorem manufacturedPlanarWell_eigen_equation (r : PlanarPosition) :
    planarLaplacian planarResolventMode r =
      (2 * manufacturedPlanarWell r + 1) * planarResolventMode r := by
  rw [planarResolventMode_equation]
  unfold manufacturedPlanarWell
  field_simp [(planarResolventMode_positive r).ne']
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarNormalized
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Analytic identities for the actual normalized planar mode. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem planarLaplacian_const_mul {f : PlanarPosition → ℝ} (hf : ContDiff ℝ 2 f)
    (c : ℝ) (r : PlanarPosition) :
    planarLaplacian (fun x => c * f x) r = c * planarLaplacian f r := by
  have h (e : PlanarPosition) : planarPartial (fun x => c * f x) e =
      fun x => c * planarPartial f e x :=
    funext (planarPartial_const_mul (hf.of_le (by norm_num)) c e)
  simp only [planarLaplacian]
  simp_rw [h]
  simp_rw [planarPartial_const_mul (planarPartial_C1 hf _)]
  exact (Finset.mul_sum _ _ _).symm

theorem normalizedPlanarMode_eigen_equation (r : PlanarPosition) :
    planarLaplacian normalizedPlanarMode r =
      (2 * manufacturedPlanarWell r + 1) * normalizedPlanarMode r := by
  rw [normalizedPlanarMode_eq_const_mul,
    planarLaplacian_const_mul (planarResolventMode_C7.of_le (by norm_num)),
    manufacturedPlanarWell_eigen_equation]
  ring

theorem planarPartial_translate (f : PlanarPosition → ℝ) (u e r : PlanarPosition) :
    planarPartial (fun x => f (x - u)) e r = planarPartial f e (r - u) := by
  simp only [planarPartial, fderiv_comp_sub]

theorem planarLaplacian_translate (f : PlanarPosition → ℝ) (u r : PlanarPosition) :
    planarLaplacian (fun x => f (x - u)) r = planarLaplacian f (r - u) := by
  have h (e : PlanarPosition) : planarPartial (fun x => f (x - u)) e =
      fun x => planarPartial f e (x - u) := funext (planarPartial_translate f u e)
  simp only [planarLaplacian]
  simp_rw [h, planarPartial_translate]

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

theorem verticalMode_second_hasDerivAt (freq z : ℝ) :
    HasDerivAt (deriv (verticalMode freq))
      ((freq ^ 2 * z ^ 2 - freq) * verticalMode freq z) z := by
  rw [show deriv (verticalMode freq) = (fun x => -freq * x * verticalMode freq x)
    from funext (verticalMode_deriv freq)]
  refine (((hasDerivAt_id z).const_mul (-freq)).mul (verticalMode_hasDerivAt freq z)).congr_deriv ?_
  · simp only [id_eq]
    ring

theorem verticalMode_second_deriv (freq z : ℝ) :
    deriv (deriv (verticalMode freq)) z = (freq ^ 2 * z ^ 2 - freq) * verticalMode freq z :=
  (verticalMode_second_hasDerivAt freq z).deriv

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
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

theorem localizedMode_planar_laplacian (freq : ℝ) (u : PlanarPosition) (p : SplitPosition) :
    planarLaplacian (fun r => localizedMode freq u (r, p.2)) p.1 =
      (2 * manufacturedPlanarWell (p.1 - u) + 1) * localizedMode freq u p := by
  have hc : ContDiff ℝ 2 (fun r => normalizedPlanarMode (r - u)) :=
    (normalizedPlanarMode_C7.comp (contDiff_id.sub contDiff_const)).of_le (by norm_num)
  change planarLaplacian (fun r => normalizedPlanarMode (r - u) * verticalMode freq p.2) p.1 = _
  rw [show (fun r => normalizedPlanarMode (r - u) * verticalMode freq p.2) =
    (fun r => verticalMode freq p.2 * normalizedPlanarMode (r - u))
    from funext (fun r => mul_comm _ _), planarLaplacian_const_mul hc,
    planarLaplacian_translate, normalizedPlanarMode_eigen_equation]
  simp only [localizedMode]
  ring

theorem localizedMode_vertical_second (freq : ℝ) (u : PlanarPosition) (p : SplitPosition) :
    deriv (deriv (fun z => localizedMode freq u (p.1, z))) p.2 =
      (freq ^ 2 * p.2 ^ 2 - freq) * localizedMode freq u p := by
  simp only [localizedMode, deriv_const_mul_field', deriv_const_mul_field,
    verticalMode_second_deriv]
  ring

theorem localizedMode_eigen_equation (freq : ℝ) (u : PlanarPosition) (p : SplitPosition) :
    -(1 / 2 : ℝ) * splitLaplacian (localizedMode freq u) p +
      localizedPotential freq u p * localizedMode freq u p =
        ((-1 / 2 : ℝ) + freq / 2) * localizedMode freq u p := by
  simp only [splitLaplacian, localizedMode_planar_laplacian,
    localizedMode_vertical_second, localizedPotential]
  ring

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

theorem localizedDensity_potential_nonnegative (freq : ℝ) (u : PlanarPosition) (x : Position) :
    0 ≤ NeutralAtom.potentialOf (localizedDensity freq u) x :=
  integral_nonneg (fun _ => mul_nonneg (NeutralAtom.coulombKernel_nonneg _)
    (localizedDensity_nonnegative freq u _))

theorem localizedCoulombCoeff_nonnegative (freq : ℝ) (u v : PlanarPosition) :
    0 ≤ localizedCoulombCoeff freq u v :=
  integral_nonneg (fun x => mul_nonneg (localizedDensity_nonnegative freq u x)
    (localizedDensity_potential_nonnegative freq v x))

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedTransition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual transition densities of localized three-dimensional modes
have normalized mass bounds and exponentially small off-site L1 mass. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem localizedTransition_mass {freq : ℝ} (hfreq : 0 < freq) (u v : PlanarPosition) :
    (∫ x, localizedTransition freq u v x) = planarModeOverlap u v := by
  change (∫ x, localizedMode freq u (positionSplitCoordinates x) *
    localizedMode freq v (positionSplitCoordinates x)) = _
  rw [positionSplitCoordinates_integral (fun p => localizedMode freq u p * localizedMode freq v p)]
  have he : (fun p : SplitPosition => localizedMode freq u p * localizedMode freq v p) =
      (fun p => (normalizedPlanarMode (p.1 - u) * normalizedPlanarMode (p.1 - v)) * verticalMode freq p.2 ^ 2) := by
    funext p
    unfold localizedMode
    ring
  rw [he, Measure.volume_eq_prod, integral_prod_mul
    (fun r => normalizedPlanarMode (r - u) * normalizedPlanarMode (r - v))
    (fun z => verticalMode freq z ^ 2)]
  rw [verticalMode_normalized hfreq, mul_one]
  rfl

end ContinuumCoulomb

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCounterterms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript's actual well-depth counterterms: direct Coulomb sums
divided by the fixed positive onsite well integral. Their diagonal action
cancels the required linear occupancy term exactly. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem localizedOffsiteSum_nonnegative (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) (i : Fin m) :
    0 ≤ localizedOffsiteSum freq u i := by
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact le_rfl
  · exact localizedCoulombCoeff_nonnegative freq _ _

theorem localizedCounterterm_nonnegative (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) (i : Fin m) :
    0 ≤ localizedCounterterm freq u i :=
  div_nonneg (localizedOffsiteSum_nonnegative freq u i) (planarHopping_positive 0).le

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

theorem manufacturedPlanarWell_zero_of_norm_ge_one {x : PlanarPosition} (hx : 1 ≤ ‖x‖) :
    manufacturedPlanarWell x = 0 := by
  simp only [manufacturedPlanarWell, planarForcing_zero_of_norm_ge_one hx, neg_zero, zero_div]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ExplicitVerticalCutoff
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

theorem slabWellCutoff_outer {S : ℝ} (hS : 0 < S) {z : ℝ} (hz : S ≤ |z|) :
    slabWellCutoff S z = 0 := by
  apply verticalCutoffBump.zero_of_le_dist
  change 2 ≤ dist ((2/S)*z) 0
  rw [dist_zero_right, Real.norm_eq_abs, abs_mul, abs_of_pos (div_pos (by norm_num) hS)]
  have hm := mul_le_mul_of_nonneg_left hz (div_pos (by norm_num : (0:ℝ)<2) hS).le
  have he : (2/S)*S = (2:ℝ) := by field_simp
  exact he.symm.le.trans hm

theorem countertermWellSum_nonpositive (freq : ℝ) {scale : ℝ} (hscale : 0 ≤ scale)
    {m : ℕ} (u : Fin m → PlanarPosition) (r : PlanarPosition) :
    countertermWellSum freq scale u r ≤ 0 := by
  apply Finset.sum_nonpos
  intro i _
  exact mul_nonpos_of_nonneg_of_nonpos
    (add_nonneg zero_le_one (div_nonneg (localizedCounterterm_nonnegative freq u i) hscale))
    (manufacturedPlanarWell_nonpositive _)

theorem manufacturedWellField_outer (freq scale : ℝ) {S : ℝ} (hS : 0 < S)
    {m : ℕ} (u : Fin m → PlanarPosition) (x : Position)
    (hx : S ≤ |(positionSplitCoordinates x).2|) :
    manufacturedWellField freq scale S u x = 0 := by
  simp only [manufacturedWellField, slabWellCutoff_outer hS hx, zero_mul]

theorem countertermWellSum_zero_far (freq scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (r : PlanarPosition)
    (hr : ∀ i, 1 ≤ ‖r-u i‖) : countertermWellSum freq scale u r = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  rw [manufacturedPlanarWell_zero_of_norm_ge_one (hr i), mul_zero]

theorem manufacturedWellField_support (freq scale : ℝ) {S R : ℝ}
    (hS : 0 < S) (hR : 0 ≤ R) {m : ℕ} (u : Fin m → PlanarPosition)
    (hu : ∀ i, ‖u i‖ ≤ R) :
    tsupport (manufacturedWellField freq scale S u) ⊆
      Metric.closedBall (0 : Position) (R+S+1) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  have hz : |(positionSplitCoordinates x).2| < S := by
    by_contra hn
    exact hx (manufacturedWellField_outer freq scale hS u x (le_of_not_gt hn))
  have hr : ‖(positionSplitCoordinates x).1‖ < R+1 := by
    by_contra hn
    apply hx
    unfold manufacturedWellField
    rw [countertermWellSum_zero_far freq scale u _ (fun i => ?_), mul_zero]
    have ht : ‖(positionSplitCoordinates x).1‖ ≤
        ‖(positionSplitCoordinates x).1-u i‖ + ‖u i‖ := by
      simpa only [sub_add_cancel] using norm_add_le ((positionSplitCoordinates x).1-u i) (u i)
    linarith [hu i, le_of_not_gt hn]
  rw [Metric.mem_closedBall, dist_zero_right]
  have hs := positionSplitCoordinates_norm_sq x
  have hr2 := (sq_le_sq₀ (norm_nonneg _) (by linarith : 0 ≤ R+1)).mpr hr.le
  have hz2 := (sq_le_sq₀ (abs_nonneg _) hS.le).mpr hz.le
  rw [sq_abs] at hz2
  nlinarith [norm_nonneg x]

theorem manufacturedWellField_compact (freq scale : ℝ) {S : ℝ} (hS : 0 < S)
    {m : ℕ} (u : Fin m → PlanarPosition) :
    HasCompactSupport (manufacturedWellField freq scale S u) := by
  let R : ℝ := ∑ i, ‖u i‖
  have hR : 0 ≤ R := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hu (i : Fin m) : ‖u i‖ ≤ R :=
    Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_univ i)
  exact (isCompact_closedBall (0 : Position) (R+S+1)).of_isClosed_subset
    (isClosed_tsupport _) (manufacturedWellField_support freq scale hS hR u hu)

theorem positionSplitCoordinates_fst_zero (x : Position) :
    (positionSplitCoordinates x).1 0 = x 0 := rfl

theorem positionSplitCoordinates_fst_one (x : Position) :
    (positionSplitCoordinates x).1 1 = x 1 := rfl

theorem positionSplitCoordinates_snd (x : Position) :
    (positionSplitCoordinates x).2 = x 2 := rfl

private theorem well_zero_away_from_near_site {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → 2 ≤ ‖u i-u j‖) (r : PlanarPosition)
    (i : Fin m) (hi : ‖r-u i‖ < 1) (j : Fin m) (hji : j ≠ i) :
    manufacturedPlanarWell (r-u j) = 0 := by
  apply manufacturedPlanarWell_zero_of_norm_ge_one
  have ht : ‖u i-u j‖ ≤ ‖r-u i‖ + ‖r-u j‖ := by
    simpa only [dist_eq_norm, norm_sub_rev (u i) r] using dist_triangle (u i) r (u j)
  linarith [hsep i j hji.symm]

/-- Disjoint planar supports prevent the counterterm perturbation from
growing with the number of sites. -/
theorem countertermWellSum_lower (freq scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → 2 ≤ ‖u i-u j‖)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i / scale ∧
      localizedCounterterm freq u i / scale ≤ δ) (r : PlanarPosition) :
    planarWellSum u r - δ*PlanarSobolev.wellBound ≤ countertermWellSum freq scale u r := by
  classical
  by_cases hnear : ∃ i, ‖r-u i‖ < 1
  · obtain ⟨i, hi⟩ := hnear
    have hz := well_zero_away_from_near_site u hsep r i hi
    have hsum : planarWellSum u r = manufacturedPlanarWell (r-u i) := by
      unfold planarWellSum
      exact Finset.sum_eq_single i (fun j _ hji => hz j hji) (by simp)
    have hsum' : countertermWellSum freq scale u r =
        (1+localizedCounterterm freq u i/scale)*manufacturedPlanarWell (r-u i) := by
      unfold countertermWellSum
      exact Finset.sum_eq_single i (fun j _ hji => by rw [hz j hji, mul_zero]) (by simp)
    rw [hsum, hsum']
    have hw : -PlanarSobolev.wellBound ≤ manufacturedPlanarWell (r-u i) := by
      exact (abs_le.mp (by simpa only [Real.norm_eq_abs] using
        PlanarSobolev.wellBound_spec (r-u i))).1
    have h1 := mul_le_mul_of_nonneg_left hw (hcoeff i).1
    have h2 := mul_le_mul_of_nonneg_right (hcoeff i).2 PlanarSobolev.wellBound_nonnegative
    nlinarith only [h1, h2]
  · have hz (i : Fin m) : manufacturedPlanarWell (r-u i) = 0 :=
      manufacturedPlanarWell_zero_of_norm_ge_one (le_of_not_gt (fun hi => hnear ⟨i, hi⟩))
    simp only [planarWellSum, countertermWellSum, hz, mul_zero, Finset.sum_const_zero]
    linarith [mul_nonneg hδ PlanarSobolev.wellBound_nonnegative]

/-- Global lower comparison to the separable uncapped multiwell field. -/
theorem manufacturedWellField_lower (freq : ℝ) {scale : ℝ} (hscale : 0 ≤ scale)
    (S : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → 2 ≤ ‖u i-u j‖) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i / scale ∧
      localizedCounterterm freq u i / scale ≤ δ) (x : Position) :
    planarWellSum u (positionSplitCoordinates x).1 - δ*PlanarSobolev.wellBound ≤
      manufacturedWellField freq scale S u x := by
  apply (countertermWellSum_lower freq scale u hsep hδ hcoeff _).trans
  exact le_mul_of_le_one_left (countertermWellSum_nonpositive freq hscale u _)
    (slabWellCutoff_bounds S _).2

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_SplitPullback
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact kinetic-energy pullback between physical Euclidean space and
planar/transverse product coordinates. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem splitCoordinate_planar_axis (a : Fin 2) :
    positionSplitCoordinates.symm (planarAxis a,0) =
      EuclideanSpace.single (Fin.castSucc a) (1:ℝ) := by
  apply positionSplitCoordinates.injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  apply Prod.ext
  · ext i
    fin_cases i <;> fin_cases a <;>
      simp [planarAxis, positionSplitCoordinates_fst_zero, positionSplitCoordinates_fst_one]
  · rw [positionSplitCoordinates_snd]
    fin_cases a <;> simp

theorem splitCoordinate_vertical_axis :
    positionSplitCoordinates.symm (0,1) = EuclideanSpace.single (2:Fin 3) (1:ℝ) := by
  apply positionSplitCoordinates.injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  apply Prod.ext
  · ext i
    fin_cases i <;> simp [positionSplitCoordinates_fst_zero, positionSplitCoordinates_fst_one]
  · rw [positionSplitCoordinates_snd]
    simp

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ComplexFormSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical complex one-electron quadratic form splits exactly into
its real and imaginary parts. Finite real-orbital penalties split as well. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem complex_norm_sq_parts (z : ℂ) : ‖z‖^2 = z.re^2+z.im^2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_SobolevDensityInput
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The Sobolev density input for conditional estimates

N. G. Meyers and J. Serrin, *H = W*, Proc. Natl. Acad. Sci. USA 51 (1964),
1055–1056, DOI 10.1073/pnas.51.6.1055, Theorem and the Lemma on p.1056.
We use only m=1, p=2 on the full Euclidean configuration space. The finite
spin index is handled componentwise. This is smooth approximation in the
value-and-weak-gradient norm; no compact support or Coulomb-form comparison
is included in the assumption.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

/-- A convenient actual-H1 version, preserving the published input explicitly. -/
theorem exists_smooth_h1_approximation (hpublished : PublishedSobolevSmoothDensity)
    {n : ℕ} (u : Coulomb.H1Vector n) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : Coulomb.H1Vector n,
      (∀ s, ContDiff ℝ (⊤ : ℕ∞) (v.value s)) ∧
      (∀ s a x, v.gradient s a x =
        fderiv ℝ (v.value s) x (EuclideanSpace.single a 1)) ∧
      h1GraphError u v < ε := by
  obtain ⟨f, hf, hL2, hpartial, he⟩ := hpublished n u ε hε
  exact ⟨classicalH1State f (fun s => (hf s).of_le (by first | simp | exact_mod_cast le_top)) hL2 hpartial,
    hf, fun _ _ _ => rfl, he⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_SmoothCutoffApproximation
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact cutoffs of actual smooth weak-H1 vectors. This is the cutoff
step needed after the published smooth-density theorem. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace ContinuumCoulomb

theorem smoothCutoffState_gradient {n : ℕ} (u : Coulomb.H1Vector n)
    (hu : ∀ s, ContDiff ℝ 1 (u.value s))
    (hd : ∀ s a x, fderiv ℝ (u.value s) x (EuclideanSpace.single a 1) = u.gradient s a x)
    (χ : Configuration n → ℝ) (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ)
    (s : SpinConfiguration n) (a : Fin n × Fin 3) (x : Configuration n) :
    (smoothCutoffState u hu χ hχ hc).gradient s a x =
      (fderiv ℝ χ x (EuclideanSpace.single a 1) : ℂ) * u.value s x +
        (χ x : ℂ) * u.gradient s a x := by
  change fderiv ℝ (fun y => (χ y : ℂ) * u.value s y) x (EuclideanSpace.single a 1) = _
  have hfχ := Complex.ofRealCLM.hasFDerivAt.comp x
    (hχ.differentiable (by norm_num) x).hasFDerivAt
  have hf := hfχ.mul (hu s |>.differentiable (by norm_num) x).hasFDerivAt
  have he := congrArg (fun L : Configuration n →L[ℝ] ℂ => L (EuclideanSpace.single a 1)) hf.fderiv
  calc
    _ = (χ x : ℂ) * u.gradient s a x +
        u.value s x * (fderiv ℝ χ x (EuclideanSpace.single a 1) : ℂ) := by
      simpa only [Pi.mul_def, Function.comp_def, add_apply, smul_apply,
        ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul, hd] using he
    _ = _ := by ring

/-- Dominated convergence for the two terms in the cutoff product rule. -/
theorem cutoff_product_error_tendsto {n : ℕ}
    (f g : Configuration n → ℂ) (hf : MemLp f 2) (hg : MemLp g 2)
    (a b : ℕ → Configuration n → ℝ)
    (ha : ∀ k, Continuous (a k)) (hb : ∀ k, Continuous (b k))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hab : ∀ k x, |a k x| ≤ A ∧ |b k x| ≤ B)
    (hat : ∀ x, Tendsto (fun k => a k x) atTop (𝓝 0))
    (hbt : ∀ x, Tendsto (fun k => b k x) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, ‖(a k x : ℂ) * f x + (b k x : ℂ) * g x‖^2)
      atTop (𝓝 0) := by
  have hfi : Integrable (fun x => ‖f x‖^2) :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hgi : Integrable (fun x => ‖g x‖^2) :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  suffices hlim : Tendsto
      (fun k => ∫ x, ‖(a k x : ℂ)*f x + (b k x : ℂ)*g x‖^2)
      atTop (𝓝 (∫ _ : Configuration n, (0 : ℝ))) by
    simpa only [integral_zero] using hlim
  apply tendsto_integral_of_dominated_convergence
    (fun x => 2*A^2*‖f x‖^2 + 2*B^2*‖g x‖^2)
  · intro k
    exact ((((Complex.continuous_ofReal.comp (ha k)).aestronglyMeasurable.mul
      hf.aestronglyMeasurable).add
      ((Complex.continuous_ofReal.comp (hb k)).aestronglyMeasurable.mul
      hg.aestronglyMeasurable)).norm.pow 2)
  · exact (hfi.const_mul (2*A^2)).add (hgi.const_mul (2*B^2))
  · intro k
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have he : ‖(a k x : ℂ)*f x + (b k x : ℂ)*g x‖ ≤ A*‖f x‖ + B*‖g x‖ := by
      apply (norm_add_le _ _).trans
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact add_le_add
        (mul_le_mul_of_nonneg_right (hab k x).1 (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (hab k x).2 (norm_nonneg _))
    have hs := (sq_le_sq₀ (norm_nonneg _)
      (add_nonneg (mul_nonneg hA (norm_nonneg _)) (mul_nonneg hB (norm_nonneg _)))).mpr he
    nlinarith [sq_nonneg (A*‖f x‖ - B*‖g x‖)]
  · filter_upwards [] with x
    have ht := (((Complex.continuous_ofReal.tendsto 0).comp (hat x)).mul_const (f x)).add
      (((Complex.continuous_ofReal.tendsto 0).comp (hbt x)).mul_const (g x))
    simpa using ht.norm.pow 2

theorem smoothCutoffState_error_tendsto {n : ℕ} (u : Coulomb.H1Vector n)
    (hu : ∀ s, ContDiff ℝ 1 (u.value s))
    (hd : ∀ s a x, fderiv ℝ (u.value s) x (EuclideanSpace.single a 1) = u.gradient s a x)
    (χ : ℕ → Configuration n → ℝ) (hχ : ∀ k, ContDiff ℝ 1 (χ k))
    (hc : ∀ k, HasCompactSupport (χ k))
    (D : ℝ) (hb : ∀ k x, |χ k x| ≤ 1)
    (hdb : ∀ k a x, |fderiv ℝ (χ k) x (EuclideanSpace.single a 1)| ≤ D)
    (ht : ∀ x, Tendsto (fun k => χ k x) atTop (𝓝 1))
    (hdt : ∀ a x, Tendsto (fun k => fderiv ℝ (χ k) x (EuclideanSpace.single a 1))
      atTop (𝓝 0)) :
    Tendsto (fun k => h1GraphError u (smoothCutoffState u hu (χ k) (hχ k) (hc k)))
      atTop (𝓝 0) := by
  have hχb (k : ℕ) (x : Configuration n) : |χ k x - 1| ≤ 2 := by
    calc
      _ ≤ |χ k x| + |(1 : ℝ)| := abs_sub _ _
      _ ≤ 2 := by simpa only [abs_one] using (show |χ k x| + 1 ≤ 2 by linarith [hb k x])
  have hv (s : SpinConfiguration n) :
      Tendsto (fun k => ∫ x, ‖u.value s x -
        (smoothCutoffState u hu (χ k) (hχ k) (hc k)).value s x‖^2) atTop (𝓝 0) := by
    have h := cutoff_product_error_tendsto (u.value s) (u.value s)
      (u.value_L2 s) (u.value_L2 s)
      (fun k x => χ k x - 1) (fun _ _ => 0)
      (fun k => (hχ k).continuous.sub continuous_const) (fun _ => continuous_const)
      2 0 (by norm_num) le_rfl (fun k x => ⟨hχb k x, by simp⟩)
      (fun x => by simpa using (ht x).sub_const 1) (fun _ => tendsto_const_nhds)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext k
    apply integral_congr_ae
    filter_upwards [] with x
    change ‖u.value s x - (χ k x : ℂ)*u.value s x‖^2 = _
    rw [norm_sub_rev]
    congr 2
    push_cast
    ring
  have hg (s : SpinConfiguration n) (a : Fin n × Fin 3) :
      Tendsto (fun k => ∫ x, ‖u.gradient s a x -
        (smoothCutoffState u hu (χ k) (hχ k) (hc k)).gradient s a x‖^2) atTop (𝓝 0) := by
    have h := cutoff_product_error_tendsto (u.value s) (u.gradient s a)
      (u.value_L2 s) (u.partial_L2 s a)
      (fun k x => fderiv ℝ (χ k) x (EuclideanSpace.single a 1)) (fun k x => χ k x - 1)
      (fun k => ((hχ k).continuous_fderiv (by norm_num)).clm_apply continuous_const)
      (fun k => (hχ k).continuous.sub continuous_const)
      |D| 2 (abs_nonneg D) (by norm_num)
      (fun k x => ⟨(hdb k a x).trans (le_abs_self D), hχb k x⟩)
      (hdt a) (fun x => by simpa using (ht x).sub_const 1)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext k
    apply integral_congr_ae
    filter_upwards [] with x
    rw [smoothCutoffState_gradient u hu hd, norm_sub_rev]
    congr 2
    push_cast
    ring
  simpa only [h1GraphError, Finset.sum_const_zero, zero_add] using
    (tendsto_finsetSum _ (fun s _ => hv s)).add
      (tendsto_finsetSum _ (fun s _ => tendsto_finsetSum _ (fun a _ => hg s a)))

/-- Every smooth actual H1 vector is the graph-norm limit of compactly
supported C1 vectors, using the existing full-space cutoff construction. -/
theorem exists_compact_approximation_of_smooth {n : ℕ} (u : Coulomb.H1Vector n)
    (hu : ∀ s, ContDiff ℝ (⊤ : ℕ∞) (u.value s))
    (hd : ∀ s a x, u.gradient s a x = fderiv ℝ (u.value s) x (EuclideanSpace.single a 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : Coulomb.H1Vector n,
      (∀ s, ContDiff ℝ 1 (v.value s) ∧ HasCompactSupport (v.value s)) ∧
      (∀ s a x, v.gradient s a x =
        fderiv ℝ (v.value s) x (EuclideanSpace.single a 1)) ∧
      h1GraphError u v < ε := by
  obtain ⟨χ, D, hχ, hc, hb, hdb, ht, hdt⟩ := Coulomb.exists_hardyCutoffs n
  have hu₁ : ∀ s, ContDiff ℝ 1 (u.value s) := fun s => (hu s).of_le (by first | simp | exact_mod_cast le_top)
  have hχ₁ : ∀ k, ContDiff ℝ 1 (χ k) := fun k => (hχ k).of_le (by first | simp | exact_mod_cast le_top)
  have he := smoothCutoffState_error_tendsto u hu₁ (fun s a x => (hd s a x).symm)
    χ hχ₁ hc D hb hdb ht hdt
  obtain ⟨k, hk⟩ := (he.eventually (gt_mem_nhds hε)).exists
  refine ⟨smoothCutoffState u hu₁ (χ k) (hχ₁ k) (hc k), fun s => ?_,
    fun _ _ _ => rfl, hk⟩
  exact ⟨(cutoff_complex_C1 _ (hχ₁ k)).mul (hu₁ s),
    ((hc k).comp_left Complex.ofReal_zero).mul_right⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CompactSobolevCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compactly supported C1 approximation on the full declared weak-H1
configuration domain. Only the explicitly cited smooth-density input is
conditional; the compactification step is proved here. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

private theorem integral_square_error_triangle {n : ℕ}
    (f g h : Configuration n → ℂ) (hf : MemLp f 2) (hg : MemLp g 2) (hh : MemLp h 2) :
    (∫ x, ‖f x-h x‖^2) ≤ 2*(∫ x, ‖f x-g x‖^2) + 2*(∫ x, ‖g x-h x‖^2) := by
  have hi (v w : Configuration n → ℂ) (hv : MemLp v 2) (hw : MemLp w 2) :
      Integrable (fun x => ‖v x-w x‖^2) :=
    (memLp_two_iff_integrable_sq_norm (hv.sub hw).aestronglyMeasurable).mp (hv.sub hw)
  calc
    _ ≤ ∫ x, 2*‖f x-g x‖^2 + 2*‖g x-h x‖^2 := by
      apply integral_mono (hi f h hf hh) ((hi f g hf hg).const_mul 2 |>.add
        ((hi g h hg hh).const_mul 2))
      intro x
      change ‖f x-h x‖^2 ≤ 2*‖f x-g x‖^2 + 2*‖g x-h x‖^2
      have he : ‖f x-h x‖ ≤ ‖f x-g x‖ + ‖g x-h x‖ := by
        calc
          _ = ‖(f x-g x)+(g x-h x)‖ := by congr 1; ring
          _ ≤ _ := norm_add_le _ _
      have hs := pow_le_pow_left₀ (norm_nonneg _) he 2
      nlinarith [sq_nonneg (‖f x-g x‖ - ‖g x-h x‖)]
    _ = _ := by
      rw [integral_add ((hi f g hf hg).const_mul 2) ((hi g h hg hh).const_mul 2),
        integral_const_mul, integral_const_mul]

theorem h1GraphError_triangle {n : ℕ} (u v w : Coulomb.H1Vector n) :
    h1GraphError u w ≤ 2*h1GraphError u v + 2*h1GraphError v w := by
  have hv := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) =>
    integral_square_error_triangle (u.value s) (v.value s) (w.value s)
      (u.value_L2 s) (v.value_L2 s) (w.value_L2 s))
  have hg := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) =>
    Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) =>
      integral_square_error_triangle (u.gradient s a) (v.gradient s a) (w.gradient s a)
        (u.partial_L2 s a) (v.partial_L2 s a) (w.partial_L2 s a)))
  have h := add_le_add hv hg
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  unfold h1GraphError
  linarith

/-- The smooth-density theorem plus the proved cutoff step gives a compact
core for the actual full weak-H1 vectors, with no symmetry restriction. -/
theorem exists_compact_h1_approximation (hpublished : PublishedSobolevSmoothDensity)
    {n : ℕ} (u : Coulomb.H1Vector n) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : Coulomb.H1Vector n,
      (∀ s, ContDiff ℝ 1 (v.value s) ∧ HasCompactSupport (v.value s)) ∧
      (∀ s a x, v.gradient s a x =
        fderiv ℝ (v.value s) x (EuclideanSpace.single a 1)) ∧
      h1GraphError u v < ε := by
  obtain ⟨v, hv, hd, hve⟩ := exists_smooth_h1_approximation hpublished u
    (by linarith : (0 : ℝ) < ε/4)
  obtain ⟨w, hw, hwd, hwe⟩ := exists_compact_approximation_of_smooth v hv hd
    (by linarith : (0 : ℝ) < ε/4)
  refine ⟨w, hw, hwd, ?_⟩
  have h := h1GraphError_triangle u v w
  linarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_H1GraphCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full weak-H1 graph as finitely many actual L2 coordinates. Compact
C1 states approximate every coordinate simultaneously, so continuous form
inequalities on this graph extend to the full weak-H1 domain. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace ContinuumCoulomb

theorem h1Coordinate_error {n : ℕ} (u v : Coulomb.H1Vector n) (a : H1Index n) :
    ‖h1Coordinates u a-h1Coordinates v a‖^2 =
      ∫ x, ‖h1CoordinateFunction u a x-h1CoordinateFunction v a x‖^2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (h1Coordinates u a) (h1Coordinates v a),
    (h1Coordinate_memLp u a).coeFn_toLp, (h1Coordinate_memLp v a).coeFn_toLp]
    with x hs hu hv
  rw [real_inner_self_eq_norm_sq]
  change ‖(h1Coordinates u a-h1Coordinates v a) x‖^2 = _
  rw [hs]
  change ‖h1Coordinates u a x-h1Coordinates v a x‖^2 = _
  change h1Coordinates u a x = h1CoordinateFunction u a x at hu
  change h1Coordinates v a x = h1CoordinateFunction v a x at hv
  rw [hu, hv]

theorem h1GraphError_eq_sum {n : ℕ} (u v : Coulomb.H1Vector n) :
    h1GraphError u v = ∑ a : H1Index n, ‖h1Coordinates u a-h1Coordinates v a‖^2 := by
  simp only [h1Coordinate_error, Fintype.sum_sum_type, Fintype.sum_prod_type,
    h1CoordinateFunction, h1GraphError]

theorem h1Coordinate_error_le {n : ℕ} (u v : Coulomb.H1Vector n) (a : H1Index n) :
    ‖h1Coordinates u a-h1Coordinates v a‖^2 ≤ h1GraphError u v := by
  rw [h1GraphError_eq_sum]
  exact Finset.single_le_sum (fun (i : H1Index n) _ =>
    sq_nonneg ‖h1Coordinates u i-h1Coordinates v i‖) (Finset.mem_univ a)

/-- Compact C1 states converge to every actual weak-H1 state in the finite
product of value and derivative L2 spaces. -/
theorem exists_compact_h1_graph_sequence (hpublished : PublishedSobolevSmoothDensity)
    {n : ℕ} (u : Coulomb.H1Vector n) :
    ∃ v : ℕ → Coulomb.H1Vector n,
      (∀ k s, ContDiff ℝ 1 ((v k).value s) ∧ HasCompactSupport ((v k).value s)) ∧
      (∀ k s a x, (v k).gradient s a x =
        fderiv ℝ ((v k).value s) x (EuclideanSpace.single a 1)) ∧
      Tendsto (fun k => h1Coordinates (v k)) atTop (𝓝 (h1Coordinates u)) := by
  have he (k : ℕ) := exists_compact_h1_approximation hpublished u
    (show (0 : ℝ) < 1/((k : ℝ)+1) by positivity)
  choose v hv hd herr using he
  refine ⟨v, hv, hd, ?_⟩
  apply tendsto_pi_nhds.2
  intro a
  rw [tendsto_iff_dist_tendsto_zero]
  have hs : Tendsto (fun k => ‖h1Coordinates (v k) a-h1Coordinates u a‖^2)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun k => sq_nonneg _) _
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    intro k
    rw [norm_sub_rev]
    exact (h1Coordinate_error_le u (v k) a).trans (herr k).le
  have ht := (Real.continuous_sqrt.tendsto 0).comp hs
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero,
    dist_eq_norm] using ht

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_H1BoundedForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous kinetic-plus-bounded-operator forms on the full H1 graph. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem h1Coordinates_norm_sq {n : ℕ} (u : Coulomb.H1Vector n) (a : H1Index n) :
    ‖h1Coordinates u a‖^2 = ∫ x, ‖h1CoordinateFunction u a x‖^2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(h1Coordinate_memLp u a).coeFn_toLp] with x hx
  simpa only [real_inner_self_eq_norm_sq, h1Coordinates] using congrArg (fun z : ℂ => ‖z‖^2) hx

theorem kinetic_eq_graphKinetic {n : ℕ} (u : Coulomb.H1Vector n) :
    Coulomb.kinetic u = graphKinetic (h1Coordinates u) := by
  simp only [Coulomb.kinetic, graphKinetic, h1Coordinates_norm_sq, h1CoordinateFunction]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_BoundedPotentialOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual bounded real multiplication potentials on the weak-H1 graph. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb
namespace BoundedPotential

variable {n : ℕ} (V : Configuration n → ℝ) (hV : Continuous V)
  (B : ℝ) (hB : ∀ x, |V x| ≤ B)

theorem operator_ae (u : Lp ℂ 2 (volume : Measure (Configuration n))) :
    operator V hV B hB u =ᵐ[volume] fun x => (V x : ℂ)*u x := value_ae V hV B hB u

theorem operator_pairing (u : Lp ℂ 2 (volume : Measure (Configuration n))) :
    inner ℝ u (operator V hV B hB u) = ∫ x, V x * ‖u x‖^2 := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [operator_ae V hV B hB u] with x hx
  rw [hx, ← Complex.real_smul, real_inner_smul_right, real_inner_self_eq_norm_sq]

end BoundedPotential

theorem boundedPotentialForm_eq_graph {n : ℕ} (V : Configuration n → ℝ)
    (hV : Continuous V) (B : ℝ) (hB : ∀ x, |V x| ≤ B) (u : Coulomb.H1Vector n) :
    boundedPotentialForm V u =
      graphBoundedForm (BoundedPotential.operator V hV B hB) (h1Coordinates u) := by
  unfold boundedPotentialForm graphBoundedForm
  rw [kinetic_eq_graphKinetic]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  rw [BoundedPotential.operator_pairing]
  apply integral_congr_ae
  filter_upwards [(h1Coordinate_memLp u (Sum.inl s)).coeFn_toLp] with x hx
  change h1Coordinates u (Sum.inl s) x = u.value s x at hx
  rw [hx]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_WeakH1Pairing
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integration by parts against a noncompact square-integrable C1 function
on the actual weak-H1 graph. Compact approximation is used only through the
explicit published Sobolev density input. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ContinuumCoulomb

theorem complex_C1_compact_test_ibp {n : ℕ} (f g : Configuration n → ℂ)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (a : Configuration n) :
    (∫ x, f x*fderiv ℝ g x a) = -(∫ x, fderiv ℝ f x a*g x) := by
  have hf' : Continuous (fun x => fderiv ℝ f x a) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hg' : Continuous (fun x => fderiv ℝ g x a) :=
    (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((hf'.mul hg.continuous).integrable_of_hasCompactSupport hc.mul_left)
    ((hf.continuous.mul hg').integrable_of_hasCompactSupport (hc.fderiv_apply ℝ a).mul_left)
    ((hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hc.mul_left)
    (fun x _ => hf.differentiable (by norm_num) x)
    (fun x _ => hg.differentiable (by norm_num) x)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_WeakH1Laplacian
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weak kinetic pairing with a C2 orbital only requires its Laplacian,
not each second partial separately, to belong to L2. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace ContinuumCoulomb

theorem configurationRealPartial_C1 {n : ℕ} {φ : Configuration n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (a : Fin n × Fin 3) :
    ContDiff ℝ 1 (configurationRealPartial φ a) :=
  (hφ.fderiv_right (show (1 : WithTop ℕ∞)+1 ≤ 2 by norm_num)).clm_apply contDiff_const

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FiniteOrbitalLaplacian
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite linear combinations commute with the actual weak-form coordinate
Laplacian. These identities are used only for Gram-corrected orbitals. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem configurationRealLaplacian_sum {m : ℕ} (c : Fin m → ℝ)
    (f : Fin m → Configuration 1 → ℝ) (hf : ∀ j, ContDiff ℝ 2 (f j))
    (x : Configuration 1) :
    configurationRealLaplacian (fun y => ∑ j, c j*f j y) x =
      ∑ j, c j*configurationRealLaplacian (f j) x := by
  have hfirst (a : Fin 1 × Fin 3) :
      configurationRealPartial (fun y => ∑ j, c j*f j y) a =
        (fun y => ∑ j, c j*configurationRealPartial (f j) a y) :=
    funext (configurationRealPartial_sum c f (fun j => (hf j).of_le (by norm_num)) a)
  unfold configurationRealLaplacian
  simp_rw [hfirst,configurationRealPartial_sum c _ (fun j => configurationRealPartial_C1 (hf j) _)]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FiniteTensorState
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite products of the actual smooth orbitals lie in the full H1 domain.
Their synthesis agrees with the orthogonal L2 tensor synthesis. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem finiteTensorState_toHilbert {n : ℕ} {α : Type*} [Fintype α]
    (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2) (c : (Fin n → α) → ℂ) :
    (finiteTensorState v hv hL2 hpartial c).toHilbert =
      ∑ p, c p • Coulomb.tensorHilbert v hL2 p := by
  apply PiLp.ext
  intro s
  simp only [WithLp.ofLp_sum,Finset.sum_apply,WithLp.ofLp_smul,Pi.smul_apply,
    Coulomb.tensorHilbert,Coulomb.H1Vector.toHilbert,WithLp.ofLp_toLp]
  exact Coulomb.orbital_sum_toLp (fun p => Coulomb.tensorOrbital v p s)
    (fun p => Coulomb.tensorOrbital_memLp v hL2 p s) Finset.univ c

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FiniteTensorNorm
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact coefficient norms for finite tensor synthesis. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem finiteTensorState_mass {n : ℕ} {α : Type*} [Fintype α]
    (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2)
    (ho : ∀ a b, (∑ t : Fin 2, ∫ y, star (v a y t)*v b y t) =
      if a=b then (1:ℂ) else 0) (c : (Fin n → α) → ℂ) :
    Coulomb.mass (finiteTensorState v hv hL2 hpartial c) = ∑ b, ‖c b‖^2 := by
  rw [← Coulomb.H1Vector.toHilbert_norm_sq,finiteTensorState_toHilbert]
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum]
  calc
    (↑(‖∑ b, c b • Coulomb.tensorHilbert v hL2 b‖^2) : ℂ) =
        inner ℂ (∑ b, c b • Coulomb.tensorHilbert v hL2 b)
          (∑ b, c b • Coulomb.tensorHilbert v hL2 b) := by
      simp only [inner_self_eq_norm_sq_to_K,Complex.ofReal_pow]
      rfl
    _ = ∑ b, (starRingEnd ℂ) (c b)*c b :=
      (Coulomb.tensorHilbert_orthonormal v hL2 ho).inner_sum c c Finset.univ
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      simpa only [starRingEnd_apply,Complex.ofReal_pow] using Complex.conj_mul' (c b)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_BoundedFormCross
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polarization of the actual bounded-potential quadratic form on the
full weak-H1 graph. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb


theorem Lp_real_inner_eq_re {n : ℕ}
    (f g : Lp ℂ 2 (volume : Measure (Configuration n))) :
    inner ℝ f g = (inner ℂ f g).re := by
  rw [L2.inner_def,L2.inner_def]
  have hr := integral_re (L2.integrable_inner (𝕜 := ℂ) f g)
  change (∫ x, (inner ℂ (f x) (g x)).re) = (∫ x, inner ℂ (f x) (g x)).re at hr
  rw [← hr]
  apply integral_congr_ae
  filter_upwards [] with x
  exact real_inner_eq_re_inner ℂ (f x) (g x)

private theorem re_finite_sum {ι : Type*} [Fintype ι] (z : ι → ℂ) :
    (∑ i, z i).re = ∑ i, (z i).re :=
  map_sum Complex.reLm z Finset.univ

theorem graphBoundedCross_eq_re {n : ℕ}
    (A : Lp ℂ 2 (volume : Measure (Configuration n)) →L[ℝ]
      Lp ℂ 2 (volume : Measure (Configuration n))) (f g : H1Coordinates n) :
    graphBoundedCross A f g = (graphComplexCross A f g).re := by
  simp only [graphBoundedCross,graphComplexCross,Lp_real_inner_eq_re,Complex.add_re,
    Complex.mul_re,re_finite_sum]
  norm_num

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

lemma correction_isHermitian (hG : G.IsHermitian) : (correction hG).IsHermitian := by
  rw [correction, ← hG.cfc_eq]
  exact (IsSelfAdjoint.cfc : IsSelfAdjoint (cfc (fun x : ℝ => (Real.sqrt x)⁻¹) G))

lemma correction_transpose (hG : G.IsHermitian) : (correction hG)ᵀ = correction hG := by
  simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using
    correction_isHermitian hG

lemma correction_gram (hG : G.IsHermitian) (hpos : ∀ i, 0 < hG.eigenvalues i) :
    (correction hG)ᵀ * G * correction hG = 1 := by
  rw [correction_transpose]
  conv_lhs => arg 1; arg 2; rw [hG.spectral_theorem]
  unfold correction Matrix.IsHermitian.cfc
  rw [← map_mul, ← map_mul, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  have hdiag : Matrix.diagonal (fun i =>
      (Real.sqrt (hG.eigenvalues i))⁻¹ * hG.eigenvalues i *
        (Real.sqrt (hG.eigenvalues i))⁻¹) = (1 : Matrix (Fin m) (Fin m) ℝ) := by
    have hscalar (i : Fin m) : (Real.sqrt (hG.eigenvalues i))⁻¹ * hG.eigenvalues i *
        (Real.sqrt (hG.eigenvalues i))⁻¹ = 1 := by
      have hs : Real.sqrt (hG.eigenvalues i) ≠ 0 := (Real.sqrt_pos.mpr (hpos i)).ne'
      calc
        _ = (Real.sqrt (hG.eigenvalues i))⁻¹ * Real.sqrt (hG.eigenvalues i) ^ 2 *
            (Real.sqrt (hG.eigenvalues i))⁻¹ := by rw [Real.sq_sqrt (hpos i).le]
        _ = 1 := by field_simp
    simp only [hscalar, Matrix.diagonal_one]
  simpa only [Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq] using
    congrArg (Unitary.conjStarAlgAut ℝ _ hG.eigenvectorUnitary) hdiag |>.trans (map_one _)

end ContinuumCoulomb.GramCorrection

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedLinearOrbitals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite linear combinations of localized orbitals. Their
classical partials remain L2, and their integral Gram matrix is the
corresponding finite congruence of the actual overlap matrix. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem localizedLinearOrbital_inner {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin m → PlanarPosition) (a b : Fin m → ℝ) :
    (∫ x, localizedLinearOrbital freq u a x * localizedLinearOrbital freq u b x) =
      ∑ j, ∑ k, (a j * b k) * planarModeOverlap (u j) (u k) := by
  have hi (j k : Fin m) : Integrable (fun x => (a j * b k) *
      localizedTransition freq (u j) (u k) x) :=
    (localizedTransition_integrable hfreq (u j) (u k)).const_mul _
  have he (x : Position) : localizedLinearOrbital freq u a x * localizedLinearOrbital freq u b x =
      ∑ j, ∑ k, (a j * b k) * localizedTransition freq (u j) (u k) x := by
    unfold localizedLinearOrbital
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    unfold localizedTransition
    ring
  simp_rw [he]
  rw [integral_finsetSum Finset.univ (fun j _ =>
    integrable_finsetSum Finset.univ (fun k _ => hi j k))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum Finset.univ (fun k _ => hi j k)]
  simp only [integral_const_mul, localizedTransition_mass hfreq]

end ContinuumCoulomb

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

theorem selectedRealSpinOrbitals_orthonormal {α : Type*} {n : ℕ}
    (f : α → Position → ℝ)
    (ho : ∀ i j, (∫ x, f i x * f j x) = if i = j then (1 : ℝ) else 0)
    (p : Fin n → α × Fin 2) (hp : Function.Injective p) (i j : Fin n) :
    (∑ s : Fin 2, ∫ x, star (realSpinOrbital (f (p i).1) (p i).2 x s) *
      realSpinOrbital (f (p j).1) (p j).2 x s) = if i = j then (1 : ℂ) else 0 := by
  classical
  rw [realSpinOrbital_inner, ho]
  by_cases hij : i = j
  · subst j
    simp
  · by_cases hs : (p i).2 = (p j).2
    · have hf : (p i).1 ≠ (p j).1 := by
        intro hf
        exact hij (hp (Prod.ext hf hs))
      simp only [hs, hf, hij, ite_true, if_true, ite_false, if_false, Complex.ofReal_zero]
    · simp only [hs, hij, ite_false, if_false]

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

theorem correctedLocalizedCoefficients_gram {D : ℝ} {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖) (hs : m * localizedOverlapBound D ≤ 1/2) :
    correctedLocalizedCoefficients u * localizedModeGram u * (correctedLocalizedCoefficients u)ᵀ = 1 := by
  have hpos (i : Fin m) : 0 < (localizedModeGram_isHermitian u).eigenvalues i := by
    have h := (GramCorrection.eigenvalue_bounds (localizedModeGram_isHermitian u)
      (localizedOverlapBound_nonnegative D) (fun j => planarModeOverlap_diagonal (u j))
      (planarModeOverlap_offsite u hsep) i).1
    linarith
  have h := GramCorrection.correction_gram (localizedModeGram_isHermitian u) hpos
  rw [GramCorrection.correction_transpose] at h
  simpa only [correctedLocalizedCoefficients, GramCorrection.correction_transpose] using h

theorem correctedLocalizedMode_inner {freq D : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : m * localizedOverlapBound D ≤ 1/2) (i j : Fin m) :
    (∫ x, correctedLocalizedMode freq u i x * correctedLocalizedMode freq u j x) =
      if i=j then (1 : ℝ) else 0 := by
  rw [correctedLocalizedMode, correctedLocalizedMode, localizedLinearOrbital_inner hfreq]
  have he : (∑ p, ∑ q, (correctedLocalizedCoefficients u i p * correctedLocalizedCoefficients u j q) *
      planarModeOverlap (u p) (u q)) =
      (correctedLocalizedCoefficients u * localizedModeGram u * (correctedLocalizedCoefficients u)ᵀ) i j := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, localizedModeGram]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [he, correctedLocalizedCoefficients_gram u hsep hs, Matrix.one_apply]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabLineIntegral
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

theorem centeredLineIntegral_even (f : ℝ → ℝ) (heven : ∀ t, f (-t) = f t)
    (H x : ℝ) : centeredLineIntegral f H (-x) = centeredLineIntegral f H x := by
  have h := intervalIntegral.integral_comp_neg (f := f) (a := x-H) (b := x+H)
  simp only [heven] at h
  have ha : -(x+H) = -x-H := by ring
  have hb : -(x-H) = -x+H := by ring
  rw [ha, hb] at h
  exact h.symm

theorem centeredLineIntegral_antitone (f : ℝ → ℝ) (hf : Continuous f)
    (hdec : ∀ a b : ℝ, |a| ≤ |b| → f b ≤ f a)
    {H : ℝ} (hH : 0 ≤ H) :
    AntitoneOn (centeredLineIntegral f H) (Set.Ici (0:ℝ)) := by
  have hd : Differentiable ℝ (centeredLineIntegral f H) :=
    fun x => (centeredLineIntegral_hasDerivAt f hf H x).differentiableAt
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0) hd.continuous.continuousOn
    hd.differentiableOn
  intro x hx
  have hx0 : 0 ≤ x := (interior_subset hx : x ∈ Set.Ici (0:ℝ))
  rw [(centeredLineIntegral_hasDerivAt f hf H x).deriv]
  apply sub_nonpos.mpr
  apply hdec
  rw [abs_of_nonneg (add_nonneg hx0 hH)]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem centeredLineIntegral_le_center (f : ℝ → ℝ) (hf : Continuous f)
    (hdec : ∀ a b : ℝ, |a| ≤ |b| → f b ≤ f a)
    {H : ℝ} (hH : 0 ≤ H) (x : ℝ) :
    centeredLineIntegral f H x ≤ centeredLineIntegral f H 0 := by
  have heven (t : ℝ) : f (-t) = f t := by
    apply le_antisymm
    · exact hdec t (-t) (by simp)
    · exact hdec (-t) t (by simp)
  have ha := centeredLineIntegral_antitone f hf hdec hH
  by_cases hx : 0 ≤ x
  · exact ha (Set.mem_Ici.mpr le_rfl) hx hx
  · have hn : 0 ≤ -x := by linarith
    rw [← centeredLineIntegral_even f heven H x]
    exact ha (Set.mem_Ici.mpr le_rfl) hn hn

theorem coulombLineKernel_continuous {A : ℝ} (hA : 0 < A) :
    Continuous (coulombLineKernel A) := by
  apply Continuous.inv₀
  · exact (continuous_const.add (continuous_id.pow 2)).sqrt
  · intro t
    exact (Real.sqrt_pos.mpr (by nlinarith [sq_nonneg t] : 0 < A+t^2)).ne'

theorem coulombLineKernel_radial_antitone {A : ℝ} (hA : 0 < A)
    {a b : ℝ} (hab : |a| ≤ |b|) : coulombLineKernel A b ≤ coulombLineKernel A a := by
  have hs : a^2 ≤ b^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg a) (abs_nonneg b)).mpr hab
  exact inv_anti₀ (Real.sqrt_pos.mpr (by nlinarith [sq_nonneg a] : 0 < A+a^2))
    (Real.sqrt_le_sqrt (by linarith : A+a^2 ≤ A+b^2))

theorem coulombLineIntegral_antitone {A H : ℝ} (hA : 0 < A) (hH : 0 ≤ H) :
    AntitoneOn (centeredLineIntegral (coulombLineKernel A) H) (Set.Ici (0:ℝ)) :=
  centeredLineIntegral_antitone _ (coulombLineKernel_continuous hA)
    (fun _ _ hab => coulombLineKernel_radial_antitone hA hab) hH

theorem coulombLineIntegral_le_center {A H : ℝ} (hA : 0 < A) (hH : 0 ≤ H) (x : ℝ) :
    centeredLineIntegral (coulombLineKernel A) H x ≤
      centeredLineIntegral (coulombLineKernel A) H 0 :=
  centeredLineIntegral_le_center _ (coulombLineKernel_continuous hA)
    (fun _ _ hab => coulombLineKernel_radial_antitone hA hab) hH x

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

private theorem coulombLine_setIntegral_le_center {A H : ℝ} (hA : 0 < A) (hH : 0 ≤ H)
    (x : ℝ) :
    (∫ t in Set.Icc (-H) H, coulombLineKernel A (x-t)) ≤
      ∫ t in Set.Icc (-H) H, coulombLineKernel A (0-t) := by
  have h := coulombLineIntegral_le_center hA hH x
  simp only [centeredLineIntegral_translate,
    intervalIntegral.integral_of_le (show -H ≤ H by linarith),
    ← integral_Icc_eq_integral_Ioc] at h
  exact h

/-- Centering one coordinate increases the attractive Coulomb integral.
The statement holds for the actual finite slab, before taking the singular limit. -/
theorem regularizedSlab_coordinate_max {epsilon H S : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (y : Position) (i : Fin 3) :
    (∫ x in slabDomain H S, NeutralAtom.regularizedKernel epsilon (y-x)) ≤
      ∫ x in slabDomain H S, NeutralAtom.regularizedKernel epsilon
        (zeroPositionCoordinate i y-x) := by
  rw [regularizedSlab_sectionIntegral hepsilon hH hS y i,
    regularizedSlab_sectionIntegral hepsilon hH hS (zeroPositionCoordinate i y) i]
  apply integral_mono
    (regularizedSection_integrable hepsilon hH hS y i).integral_prod_right
    (regularizedSection_integrable hepsilon hH hS (zeroPositionCoordinate i y) i).integral_prod_right
  intro v
  simp_rw [regularizedKernel_section, zeroPositionCoordinate_same, zeroPositionCoordinate_other]
  have hA : 0 < epsilon^2+∑ j : Fin 2, (y (i.succAbove j)-v j)^2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hepsilon)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hside : 0 ≤ slabSide H S i := by unfold slabSide; split <;> assumption
  exact coulombLine_setIntegral_le_center hA hside (y i)

/-- The actual singular finite-slab potential is minimized in each centered
coordinate. The regularized comparison passes through a dominated limit. -/
theorem slabPotential_coordinate_min {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (y : Position) (i : Fin 3) :
    slabPotential rho H S (zeroPositionCoordinate i y) ≤ slabPotential rho H S y := by
  let epsilon : ℕ → ℝ := fun n => ((n:ℝ)+1)⁻¹
  have hep (n : ℕ) : 0 < epsilon n := by dsimp [epsilon]; positivity
  have heps : Tendsto epsilon atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  apply le_of_tendsto_of_tendsto
    (regularizedSlabPotential_tendsto hep heps rho hH hS (zeroPositionCoordinate i y))
    (regularizedSlabPotential_tendsto hep heps rho hH hS y)
  exact Filter.Eventually.of_forall (fun n =>
    mul_le_mul_of_nonpos_left (regularizedSlab_coordinate_max (hep n).ne' hH hS y i)
      (neg_nonpos.mpr hrho))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabMonotonicity
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinatewise monotonicity of the actual singular slab potential.
This strengthens centering to comparison at any two absolute coordinates. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ContinuumCoulomb

theorem coulombLineIntegral_abs_antitone {A H x y : ℝ} (hA : 0 < A)
    (hH : 0 ≤ H) (hxy : |x| ≤ |y|) :
    centeredLineIntegral (coulombLineKernel A) H y ≤
      centeredLineIntegral (coulombLineKernel A) H x := by
  have he (t : ℝ) : coulombLineKernel A (-t) = coulombLineKernel A t := by
    simp [coulombLineKernel]
  have ha (t : ℝ) : centeredLineIntegral (coulombLineKernel A) H |t| =
      centeredLineIntegral (coulombLineKernel A) H t := by
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_nonpos ht]
      exact centeredLineIntegral_even _ he H t
  rw [← ha x, ← ha y]
  exact coulombLineIntegral_antitone hA hH (abs_nonneg x) (abs_nonneg y) hxy

private theorem coulombLine_setIntegral_abs_antitone {A H x y : ℝ}
    (hA : 0 < A) (hH : 0 ≤ H) (hxy : |x| ≤ |y|) :
    (∫ t in Set.Icc (-H) H, coulombLineKernel A (y-t)) ≤
      ∫ t in Set.Icc (-H) H, coulombLineKernel A (x-t) := by
  have h := coulombLineIntegral_abs_antitone hA hH hxy
  simp only [centeredLineIntegral_translate,
    intervalIntegral.integral_of_le (show -H ≤ H by linarith),
    ← integral_Icc_eq_integral_Ioc] at h
  exact h

private theorem regularizedSections_integrable {epsilon H S : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (y : Position) (i : Fin 3) :
    Integrable (fun p : ℝ × (Fin 2 → ℝ) => NeutralAtom.regularizedKernel epsilon
      (y-WithLp.toLp 2 (i.insertNth p.1 p.2)))
      ((slabAxisMeasure H S i).prod
        (Measure.pi (fun j : Fin 2 => slabAxisMeasure H S (i.succAbove j)))) := by
  have hp := (measurePreserving_piFinSuccAbove (slabAxisMeasure H S) i).symm
  exact (hp.integrable_comp_emb
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) i).symm.measurableEmbedding).mpr
      ((slabProduct_integrable H S _).mpr (regularizedSlab_integrableOn hepsilon hH hS y))

theorem regularizedSlab_coordinate_antitone {epsilon H S : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (x y : Position) (i : Fin 3)
    (hother : ∀ j : Fin 2, x (i.succAbove j) = y (i.succAbove j))
    (hxy : |x i| ≤ |y i|) :
    (∫ b in slabDomain H S, NeutralAtom.regularizedKernel epsilon (y-b)) ≤
      ∫ b in slabDomain H S, NeutralAtom.regularizedKernel epsilon (x-b) := by
  rw [regularizedSlab_sectionIntegral hepsilon hH hS y i,
    regularizedSlab_sectionIntegral hepsilon hH hS x i]
  apply integral_mono
    (regularizedSections_integrable hepsilon hH hS y i).integral_prod_right
    (regularizedSections_integrable hepsilon hH hS x i).integral_prod_right
  intro v
  simp_rw [regularizedKernel_section, hother]
  have hA : 0 < epsilon^2+∑ j : Fin 2, (y (i.succAbove j)-v j)^2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hepsilon)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hside : 0 ≤ slabSide H S i := by unfold slabSide; split <;> assumption
  exact coulombLine_setIntegral_abs_antitone hA hside hxy

/-- Increasing a single absolute coordinate increases the singular slab potential. -/
theorem slabPotential_coordinate_monotone {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (x y : Position) (i : Fin 3)
    (hother : ∀ j : Fin 2, x (i.succAbove j) = y (i.succAbove j))
    (hxy : |x i| ≤ |y i|) : slabPotential rho H S x ≤ slabPotential rho H S y := by
  let epsilon : ℕ → ℝ := fun n => ((n:ℝ)+1)⁻¹
  have hep (n : ℕ) : 0 < epsilon n := by dsimp [epsilon]; positivity
  have heps : Tendsto epsilon atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  apply le_of_tendsto_of_tendsto
    (regularizedSlabPotential_tendsto hep heps rho hH hS x)
    (regularizedSlabPotential_tendsto hep heps rho hH hS y)
  exact Filter.Eventually.of_forall (fun n =>
    mul_le_mul_of_nonpos_left
      (regularizedSlab_coordinate_antitone (hep n).ne' hH hS x y i hother hxy)
      (neg_nonpos.mpr hrho))

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

/-- Global capped-quadratic confinement in the physical vertical coordinate. -/
theorem slabPotential_confinement {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 < H) (hS : 0 ≤ S) (y : Position) :
    2*Real.pi*rho*min ((y 2)^2) (S^2)-6*Real.pi*rho*S^3/H ≤
      slabPotential rho H S y-slabPotential rho H S 0 := by
  let t : ℝ := min |y 2| S
  have ht0 : 0 ≤ t := le_min (abs_nonneg _) hS
  have htS : |t| ≤ S := by rw [abs_of_nonneg ht0]; exact min_le_right _ _
  have hty : |t| ≤ |y 2| := by rw [abs_of_nonneg ht0]; exact min_le_left _ _
  have ht2 : t^2 = min ((y 2)^2) (S^2) := by
    by_cases h : |y 2| ≤ S
    · have hs : (y 2)^2 ≤ S^2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hS).mpr h
      simp only [t, min_eq_left h, sq_abs, min_eq_left hs]
    · have hs : S^2 ≤ (y 2)^2 := by
        simpa only [sq_abs] using (sq_le_sq₀ hS (abs_nonneg _)).mpr (le_of_not_ge h)
      simp only [t, min_eq_right (le_of_not_ge h), min_eq_right hs]
  have haxis : slabPotential rho H S (slabAxisPoint t) ≤
      slabPotential rho H S (slabAxisPoint (y 2)) := by
    apply slabPotential_coordinate_monotone hrho hH.le hS _ _ 2
    · intro j
      fin_cases j <;> rfl
    · exact hty
  have h0 := slabPotential_coordinate_min hrho hH.le hS y 0
  have h1 := slabPotential_coordinate_min hrho hH.le hS (zeroPositionCoordinate 0 y) 1
  have he : zeroPositionCoordinate 1 (zeroPositionCoordinate 0 y) = slabAxisPoint (y 2) := by
    ext j
    fin_cases j <;> simp [zeroPositionCoordinate, slabAxisPoint]
  rw [he] at h1
  have hmono := haxis.trans (h1.trans h0)
  have herr := (abs_le.mp (slabPotential_axis_error hrho hH hS htS)).1
  rw [ht2] at herr
  linarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedSlabLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global comparison of the actual manufactured Coulomb field with the
separable capped oscillator and planar wells. -/

noncomputable section
namespace ContinuumCoulomb

theorem manufacturedSlabPotential_lower {rho H S freq scale δ : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 ≤ S) (hscale : 0 ≤ scale)
    (hfreq : freq^2 = 4*Real.pi*rho) {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → 2 ≤ ‖u i-u j‖) (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i / scale ∧
      localizedCounterterm freq u i / scale ≤ δ) (x : Position) :
    planarWellSum u (positionSplitCoordinates x).1 +
      verticalCapPotential freq S (positionSplitCoordinates x).2 -
      (δ*PlanarSobolev.wellBound+6*Real.pi*rho*S^3/H) ≤
      manufacturedSlabPotential rho H S freq scale u x := by
  have hs := slabPotential_confinement hrho hH hS x
  have hw := manufacturedWellField_lower freq hscale S u hsep hδ hcoeff x
  have he : verticalCapPotential freq S (positionSplitCoordinates x).2 =
      2*Real.pi*rho*min ((x 2)^2) (S^2) := by
    rw [verticalCapPotential,hfreq,positionSplitCoordinates_snd]
    ring
  rw [he]
  unfold manufacturedSlabPotential
  linarith

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

theorem manufacturedSlabPotential_bounded {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 ≤ H) (hS : 0 < S) (freq scale : ℝ)
    {m : ℕ} (u : Fin m → PlanarPosition) :
    ∃ B : ℝ, ∀ x, |manufacturedSlabPotential rho H S freq scale u x| ≤ B := by
  obtain ⟨C,hC⟩ := (manufacturedWellField_C7 freq scale S u).continuous.bounded_above_of_compact_support
    (manufacturedWellField_compact freq scale hS u)
  let A := rho*NeutralAtom.kernelBallMass 1+volume.real (slabDomain H S)*rho
  refine ⟨2*A+C,fun x => ?_⟩
  have hx := slabPotential_abs_bound hrho hH hS.le x
  have h0 := slabPotential_abs_bound hrho hH hS.le 0
  have hw := hC x
  change |manufacturedWellField freq scale S u x| ≤ C at hw
  unfold manufacturedSlabPotential
  exact (abs_add_le _ _).trans ((add_le_add
    ((abs_sub _ _).trans (add_le_add hx h0)) hw).trans_eq (by dsimp [A]; ring))

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

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedOneBody
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual differential action of the full multiwell operator on the
localized modes. Subtraction of the common ground energy leaves exactly the
sum of other wells, so its matrix is the checked hopping matrix plus the
explicit two-tail error. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem multiwellAction_localizedMode (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (j : Fin m) (p : SplitPosition) :
    multiwellAction freq u (localizedMode freq (u j)) p - ((-1 / 2 : ℝ) + freq / 2) * localizedMode freq (u j) p =
      ∑ k, if k = j then 0 else manufacturedPlanarWell (p.1 - u k) * localizedMode freq (u j) p := by
  classical
  have hs : (∑ k, manufacturedPlanarWell (p.1 - u k)) =
      manufacturedPlanarWell (p.1 - u j) + (∑ k, if k = j then 0 else manufacturedPlanarWell (p.1 - u k)) := by
    calc
      _ = ∑ k, ((if k = j then manufacturedPlanarWell (p.1 - u j) else 0) +
          (if k = j then 0 else manufacturedPlanarWell (p.1 - u k))) := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : k = j <;> simp [hk]
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  have he := localizedMode_eigen_equation freq (u j) p
  unfold localizedPotential at he
  unfold multiwellAction multiwellPotential
  rw [hs]
  have hm : (∑ k, if k = j then 0 else manufacturedPlanarWell (p.1 - u k)) * localizedMode freq (u j) p =
      ∑ k, if k = j then 0 else manufacturedPlanarWell (p.1 - u k) * localizedMode freq (u j) p := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> simp only [zero_mul]
  rw [← hm]
  nlinarith only [he]

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

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedMultiwellResidual
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

theorem localizedMultiwellResidual_eq (freq : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (j : Fin m) (x : Position) :
    localizedMultiwellResidual freq u j x =
      multiwellAction freq u (localizedMode freq (u j)) (positionSplitCoordinates x) -
        ((-1/2 : ℝ)+freq/2)*continuumLocalizedMode freq (u j) x := by
  rw [show continuumLocalizedMode freq (u j) x =
    localizedMode freq (u j) (positionSplitCoordinates x) from rfl,
    multiwellAction_localizedMode]
  rfl

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

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedOrbitalResidual
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

theorem manufacturedOrbitalResidual_eq {rho freq : ℝ} (hfreq : freq^2 = 4*Real.pi*rho)
    (H S scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) (j : Fin m) (x : Position) :
    manufacturedOrbitalResidual rho H S freq scale u j x =
      -(1/2 : ℝ)*splitLaplacian (localizedMode freq (u j)) (positionSplitCoordinates x)+
      manufacturedSlabPotential rho H S freq scale u x*continuumLocalizedMode freq (u j) x-
      ((-1/2 : ℝ)+freq/2)*continuumLocalizedMode freq (u j) x := by
  rw [manufacturedOrbitalResidual, localizedMultiwellResidual_eq]
  unfold multiwellAction multiwellPotential slabOrbitalResidual slabResidualMultiplier
    wellFieldOrbitalResidual manufacturedSlabPotential planarWellSum
  rw [hfreq]
  simp only [continuumLocalizedMode, positionSplitCoordinates_snd]
  ring

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

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CorrectedManufacturedResidual
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

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoordinateLaplacian
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate identities for the actual three-dimensional Laplacian. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

private theorem directionalSecond_affine {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : F → ℝ) (hf : ContDiff ℝ 2 f) (L : E →L[ℝ] F) (c : F) (e x : E) :
    directionalSecond (fun y => f (L y+c)) e x = directionalSecond f (L e) (L x+c) := by
  have hfirst (y : E) : fderiv ℝ (fun z => f (L z+c)) y e =
      fderiv ℝ f (L y+c) (L e) := by
    exact congrArg (fun M : E →L[ℝ] ℝ => M e)
      (((hf.differentiable (by norm_num) _).hasFDerivAt).comp y
        (L.hasFDerivAt.add_const c)).fderiv
  have hd : ContDiff ℝ 1 (fun y => fderiv ℝ f y (L e)) :=
    (hf.fderiv_right (show (1 : WithTop ℕ∞)+1 ≤ 2 by norm_num)).clm_apply contDiff_const
  unfold directionalSecond
  simp_rw [hfirst]
  exact congrArg (fun M : E →L[ℝ] ℝ => M e)
    (((hd.differentiable (by norm_num) _).hasFDerivAt).comp x
      (L.hasFDerivAt.add_const c)).fderiv

private theorem split_planar_second (f : SplitPosition → ℝ) (hf : ContDiff ℝ 2 f)
    (a : Fin 2) (p : SplitPosition) :
    planarPartial (planarPartial (fun r => f (r,p.2)) (planarAxis a)) (planarAxis a) p.1 =
      directionalSecond f (planarAxis a,0) p := by
  change directionalSecond (fun r => f (r,p.2)) (planarAxis a) p.1 = _
  have h := directionalSecond_affine f hf
    (ContinuousLinearMap.inl ℝ PlanarPosition ℝ) (0,p.2) (planarAxis a) p.1
  simpa only [ContinuousLinearMap.inl_apply,
    Prod.mk_add_mk, add_zero, zero_add] using h

private theorem split_vertical_second (f : SplitPosition → ℝ) (hf : ContDiff ℝ 2 f)
    (p : SplitPosition) :
    deriv (deriv (fun z => f (p.1,z))) p.2 = directionalSecond f (0,1) p := by
  have h := directionalSecond_affine f hf
    (ContinuousLinearMap.inr ℝ PlanarPosition ℝ) (p.1,0) 1 p.2
  simpa only [directionalSecond, fderiv_apply_one_eq_deriv, ContinuousLinearMap.inr_apply,
    Prod.mk_add_mk, add_zero, zero_add] using h

theorem oneElectron_split_laplacian (f : SplitPosition → ℝ) (hf : ContDiff ℝ 2 f)
    (x : Configuration 1) :
    configurationRealLaplacian (fun y => f (positionSplitCoordinates (oneElectronCoordinates y))) x =
      splitLaplacian f (positionSplitCoordinates (oneElectronCoordinates x)) := by
  let L : Configuration 1 →L[ℝ] SplitPosition :=
    positionSplitCoordinates.toContinuousLinearMap.comp oneElectronCoordinates.toContinuousLinearEquiv.toContinuousLinearMap
  have hs (a : Fin 3) :
      directionalSecond (fun y => f (positionSplitCoordinates (oneElectronCoordinates y)))
        (EuclideanSpace.single (0,a) 1) x =
      directionalSecond f (positionSplitCoordinates (EuclideanSpace.single a 1))
        (positionSplitCoordinates (oneElectronCoordinates x)) := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, oneElectronCoordinates_single, add_zero, L] using
      directionalSecond_affine f hf L 0 (EuclideanSpace.single (0,a) 1) x
  have hp (a : Fin 2) : positionSplitCoordinates (EuclideanSpace.single (Fin.castSucc a) 1) =
      (planarAxis a,0) := by
    rw [← splitCoordinate_planar_axis, ContinuousLinearEquiv.apply_symm_apply]
  have hz : positionSplitCoordinates (EuclideanSpace.single (2:Fin 3) 1) = (0,1) := by
    rw [← splitCoordinate_vertical_axis, ContinuousLinearEquiv.apply_symm_apply]
  unfold configurationRealLaplacian configurationRealPartial
  change (∑ a : Fin 1 × Fin 3, directionalSecond _ (EuclideanSpace.single a 1) x) = _
  rw [Fintype.sum_prod_type, Fin.sum_univ_one]
  simp_rw [hs]
  change positionSplitCoordinates (EuclideanSpace.single (Fin.last 2) 1) = (0,1) at hz
  rw [Fin.sum_univ_castSucc (n := 2),hz]
  simp_rw [hp]
  unfold splitLaplacian planarLaplacian
  simp_rw [split_planar_second f hf, split_vertical_second f hf]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedWeakResidual
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The differential residual is an actual weak-H1 kinetic/potential
pairing identity. This is the bridge used for the off-diagonal form bound. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem oneElectronLocalizedMode_laplacian (freq : ℝ) (u : PlanarPosition) (x : Configuration 1) :
    configurationRealLaplacian (oneElectronLocalizedMode freq u) x =
      splitLaplacian (localizedMode freq u) (positionSplitCoordinates (oneElectronCoordinates x)) :=
  oneElectron_split_laplacian _ ((localizedMode_C7 freq u).of_le (by norm_num)) x

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CorrectedResidualPairing
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual corrected-orbital mixed forms inherit the manufactured residual
bound on every state in the full one-electron weak-H1 domain. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem oneElectronCorrectedMode_C2 (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (i : Fin m) : ContDiff ℝ 2 (oneElectronCorrectedMode freq u i) :=
  ((localizedLinearOrbital_C7 freq u (correctedLocalizedCoefficients u i)).of_le (by norm_num)).comp oneElectronCoordinates.contDiff

theorem correctedManufacturedResidual_eq {rho freq : ℝ}
    (hrelation : freq^2 = 4*Real.pi*rho) (H S scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (i : Fin m) (x : Configuration 1) :
    correctedManufacturedResidual rho H S freq scale u i (oneElectronCoordinates x) =
      -(1/2:ℝ)*configurationRealLaplacian (oneElectronCorrectedMode freq u i) x+
      manufacturedSlabPotential rho H S freq scale u (oneElectronCoordinates x)*
        oneElectronCorrectedMode freq u i x-
      ((-1/2:ℝ)+freq/2)*oneElectronCorrectedMode freq u i x := by
  have hlap := configurationRealLaplacian_sum (correctedLocalizedCoefficients u i)
    (fun j => oneElectronLocalizedMode freq (u j)) (fun j => oneElectronLocalizedMode_C2 freq (u j)) x
  have he (j : Fin m) := manufacturedOrbitalResidual_eq hrelation H S scale u j (oneElectronCoordinates x)
  simp_rw [← oneElectronLocalizedMode_laplacian] at he
  change (∑ j, correctedLocalizedCoefficients u i j*
    manufacturedOrbitalResidual rho H S freq scale u j (oneElectronCoordinates x)) = _
  change configurationRealLaplacian (oneElectronCorrectedMode freq u i) x = _ at hlap
  rw [hlap]
  change _ = -(1/2:ℝ)*(∑ j, correctedLocalizedCoefficients u i j*
    configurationRealLaplacian (oneElectronLocalizedMode freq (u j)) x)+
    manufacturedSlabPotential rho H S freq scale u (oneElectronCoordinates x)*
      (∑ j, correctedLocalizedCoefficients u i j*oneElectronLocalizedMode freq (u j) x)-
    ((-1/2:ℝ)+freq/2)*(∑ j, correctedLocalizedCoefficients u i j*oneElectronLocalizedMode freq (u j) x)
  simp only [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [he j]
  simp only [oneElectronLocalizedMode]
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_TensorFirstReplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replacing one orbital in a finite tensor expansion costs the squared
L2 size of the replacement family, without an exponential dimension factor. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem tensorCoefficientSlice_memLp {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    {μ : Measure A} [SigmaFinite μ] {n : ℕ}
    (v : ι → A → ℂ) (hv : ∀ a, MemLp (v a) 2 μ)
    (c : ι → (Fin n → ι) → ℂ) (a : ι) :
    MemLp (tensorCoefficientSlice v c a) 2 (Measure.pi fun _ : Fin n => μ) := by
  unfold tensorCoefficientSlice
  exact memLp_finsetSum Finset.univ (fun b _ =>
    (Coulomb.scalarTensor_memLp v hv b).const_mul (c a b))

theorem tensorCoefficientSlice_norm {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    {μ : Measure A} [SigmaFinite μ] {n : ℕ}
    (v : ι → A → ℂ) (hv : ∀ a, MemLp (v a) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x)*v b x ∂μ) = if a=b then (1:ℂ) else 0)
    (c : ι → (Fin n → ι) → ℂ) (a : ι) :
    (∫ y, ‖tensorCoefficientSlice v c a y‖^2 ∂(Measure.pi fun _ : Fin n => μ)) =
      ∑ b, ‖c a b‖^2 := by
  have ht : ∀ b : Fin n → ι,
      MemLp (fun y : Fin n → A => ∏ i, v (b i) (y i)) 2
        (Measure.pi fun _ : Fin n => μ) :=
    Coulomb.scalarTensor_memLp (μ := μ) v hv
  simpa only [tensorCoefficientSlice] using
    (Coulomb.orbital_sum_sq (μ := Measure.pi fun _ : Fin n => μ)
      (fun (b : Fin n → ι) (y : Fin n → A) => ∏ i, v (b i) (y i)) ht
      (fun b d => by
        have h := Coulomb.scalarTensor_orthonormal (μ := μ) v ho b d
        by_cases hd : b=d <;> simpa only [hd,ite_true, if_true,ite_false, if_false] using h)
      Finset.univ (c a))

theorem tensorFirstReplacement_memLp {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    {μ : Measure A} [SigmaFinite μ] {n : ℕ}
    (v r : ι → A → ℂ) (hv : ∀ a, MemLp (v a) 2 μ) (hr : ∀ a, MemLp (r a) 2 μ)
    (c : ι → (Fin n → ι) → ℂ) :
    MemLp (tensorFirstReplacement v r c) 2 ((Measure.pi fun _ : Fin n => μ).prod μ) := by
  unfold tensorFirstReplacement
  exact memLp_finsetSum Finset.univ (fun a _ =>
    Coulomb.tensorPair_memLp (tensorCoefficientSlice_memLp v hv c a) (hr a))

theorem tensorFirstReplacement_pointwise {A ι : Type*} [Fintype ι] {n : ℕ}
    (v r : ι → A → ℂ) (c : ι → (Fin n → ι) → ℂ) (z : (Fin n → A) × A) :
    ‖tensorFirstReplacement v r c z‖^2 ≤
      (∑ a, ‖tensorCoefficientSlice v c a z.1‖^2)*(∑ a, ‖r a z.2‖^2) := by
  have ht : ‖tensorFirstReplacement v r c z‖ ≤
      ∑ a, ‖tensorCoefficientSlice v c a z.1‖*‖r a z.2‖ := by
    simpa only [tensorFirstReplacement,norm_mul] using norm_sum_le Finset.univ
      (fun a => tensorCoefficientSlice v c a z.1*r a z.2)
  exact (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _)

theorem tensorFirstReplacement_L2_bound {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    {μ : Measure A} [SigmaFinite μ] {n : ℕ}
    (v r : ι → A → ℂ) (hv : ∀ a, MemLp (v a) 2 μ) (hr : ∀ a, MemLp (r a) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x)*v b x ∂μ) = if a=b then (1:ℂ) else 0)
    (c : ι → (Fin n → ι) → ℂ) :
    (∫ z, ‖tensorFirstReplacement v r c z‖^2 ∂((Measure.pi fun _ : Fin n => μ).prod μ)) ≤
      (∑ a, ∫ x, ‖r a x‖^2 ∂μ)*(∑ a, ∑ b, ‖c a b‖^2) := by
  have hG : Integrable (fun y => ∑ a, ‖tensorCoefficientSlice v c a y‖^2)
      (Measure.pi fun _ : Fin n => μ) :=
    integrable_finsetSum _ (fun a _ => (tensorCoefficientSlice_memLp v hv c a).norm.integrable_sq)
  have hR : Integrable (fun x => ∑ a, ‖r a x‖^2) μ :=
    integrable_finsetSum _ (fun a _ => (hr a).norm.integrable_sq)
  calc
    _ ≤ ∫ z, (∑ a, ‖tensorCoefficientSlice v c a z.1‖^2)*(∑ a, ‖r a z.2‖^2)
        ∂((Measure.pi fun _ : Fin n => μ).prod μ) :=
      integral_mono (tensorFirstReplacement_memLp v r hv hr c).norm.integrable_sq
        (hG.mul_prod hR) (tensorFirstReplacement_pointwise v r c)
    _ = (∫ y, ∑ a, ‖tensorCoefficientSlice v c a y‖^2 ∂(Measure.pi fun _ : Fin n => μ))*
        (∫ x, ∑ a, ‖r a x‖^2 ∂μ) :=
      integral_prod_mul (μ := Measure.pi fun _ : Fin n => μ) (ν := μ)
        (fun y => ∑ a, ‖tensorCoefficientSlice v c a y‖^2)
        (fun x => ∑ a, ‖r a x‖^2)
    _ = _ := by
      rw [integral_finsetSum _ (fun a _ => (tensorCoefficientSlice_memLp v hv c a).norm.integrable_sq),
        integral_finsetSum _ (fun a _ => (hr a).norm.integrable_sq)]
      simp only [tensorCoefficientSlice_norm v hv ho c]
      ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_TensorSlotReplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The residual in any electron coordinate has the same polynomial bound.
The regrouping is an exact measure-preserving separation of that coordinate. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem tensorSlotReplacement_regroup {A ι : Type*} [Fintype ι] {n : ℕ}
    (v r : ι → A → ℂ) (c : (Fin (n+1) → ι) → ℂ)
    (i : Fin (n+1)) (x : Fin (n+1) → A) :
    tensorSlotReplacement v r c i x =
      tensorFirstReplacement v r (fun a b => c (i.insertNth a b)) (i.removeNth x,x i) := by
  unfold tensorSlotReplacement
  rw [← (Fin.insertNthEquiv (fun _ : Fin (n+1) => ι) i).sum_comp
    (fun b => c b * ∏ j, if j=i then r (b j) (x j) else v (b j) (x j))]
  rw [Fintype.sum_prod_type]
  unfold tensorFirstReplacement tensorCoefficientSlice
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  rw [Fin.prod_univ_succAbove _ i]
  simp only [Fin.insertNthEquiv_apply,Fin.insertNth_apply_same,ite_true, if_true,
    Fin.succAbove_ne,ite_false, if_false,Fin.insertNth_apply_succAbove]
  change c (i.insertNth a b) * (r a (x i) * ∏ j, v (b j) (x (i.succAbove j))) =
    (c (i.insertNth a b) * ∏ j, v (b j) (x (i.succAbove j))) * r a (x i)
  ring

theorem sum_insertNth_coefficient_norm {ι : Type*} [Fintype ι] {n : ℕ}
    (c : (Fin (n+1) → ι) → ℂ) (i : Fin (n+1)) :
    (∑ a, ∑ b : Fin n → ι, ‖c (i.insertNth a b)‖^2) = ∑ b, ‖c b‖^2 := by
  calc
    _ = ∑ p : ι × (Fin n → ι), ‖c (i.insertNth p.1 p.2)‖^2 :=
      (Fintype.sum_prod_type _).symm
    _ = _ := (Fin.insertNthEquiv (fun _ : Fin (n+1) => ι) i).sum_comp
      (fun b => ‖c b‖^2)

theorem separateTensorSlot_apply {A : Type*} [MeasurableSpace A] {n : ℕ}
    (i : Fin (n+1)) (x : Fin (n+1) → A) :
    separateTensorSlot i x = (i.removeNth x,x i) := rfl

theorem separateTensorSlot_measurePreserving {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [SigmaFinite μ] {n : ℕ} (i : Fin (n+1)) :
    MeasurePreserving (separateTensorSlot i)
      (Measure.pi fun _ : Fin (n+1) => μ) ((Measure.pi fun _ : Fin n => μ).prod μ) :=
  Measure.measurePreserving_swap.comp (measurePreserving_piFinSuccAbove (fun _ => μ) i)

theorem tensorSlotReplacement_memLp {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    {μ : Measure A} [SigmaFinite μ] {n : ℕ}
    (v r : ι → A → ℂ) (hv : ∀ a, MemLp (v a) 2 μ) (hr : ∀ a, MemLp (r a) 2 μ)
    (c : (Fin (n+1) → ι) → ℂ) (i : Fin (n+1)) :
    MemLp (tensorSlotReplacement v r c i) 2 (Measure.pi fun _ : Fin (n+1) => μ) := by
  have h := (tensorFirstReplacement_memLp v r hv hr (fun a b => c (i.insertNth a b))).comp_measurePreserving
    (separateTensorSlot_measurePreserving (μ := μ) i)
  simpa only [Function.comp_def,separateTensorSlot_apply,← tensorSlotReplacement_regroup] using h

theorem tensorSlotReplacement_L2_bound {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    {μ : Measure A} [SigmaFinite μ] {n : ℕ}
    (v r : ι → A → ℂ) (hv : ∀ a, MemLp (v a) 2 μ) (hr : ∀ a, MemLp (r a) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x)*v b x ∂μ) = if a=b then (1:ℂ) else 0)
    (c : (Fin (n+1) → ι) → ℂ) (i : Fin (n+1)) :
    (∫ x, ‖tensorSlotReplacement v r c i x‖^2 ∂(Measure.pi fun _ : Fin (n+1) => μ)) ≤
      (∑ a, ∫ x, ‖r a x‖^2 ∂μ)*(∑ b, ‖c b‖^2) := by
  have he := (separateTensorSlot_measurePreserving (μ := μ) i).integral_comp'
    (fun z => ‖tensorFirstReplacement v r (fun a b => c (i.insertNth a b)) z‖^2)
  simp only [separateTensorSlot_apply,← tensorSlotReplacement_regroup] at he
  rw [he]
  have h := tensorFirstReplacement_L2_bound v r hv hr ho (fun a b => c (i.insertNth a b))
  rwa [sum_insertNth_coefficient_norm] at h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_TensorTotalReplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing one-body residuals over electron coordinates costs only the square
of the electron count, even though the tensor coefficient space is exponential. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem finite_sum_norm_square_le {κ : Type*} [Fintype κ] (f : κ → ℂ) :
    ‖∑ i, f i‖^2 ≤ (Fintype.card κ:ℝ)*∑ i, ‖f i‖^2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : κ => (1:ℝ)) (fun i => ‖f i‖)
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at h
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le Finset.univ f) 2).trans h

theorem tensorTotalReplacement_memLp {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    {μ : Measure A} [SigmaFinite μ] {n : ℕ}
    (v r : ι → A → ℂ) (hv : ∀ a, MemLp (v a) 2 μ) (hr : ∀ a, MemLp (r a) 2 μ)
    (c : (Fin (n+1) → ι) → ℂ) :
    MemLp (tensorTotalReplacement v r c) 2 (Measure.pi fun _ : Fin (n+1) => μ) :=
  memLp_finsetSum Finset.univ (fun i _ => tensorSlotReplacement_memLp v r hv hr c i)

theorem tensorTotalReplacement_L2_bound {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    {μ : Measure A} [SigmaFinite μ] {n : ℕ}
    (v r : ι → A → ℂ) (hv : ∀ a, MemLp (v a) 2 μ) (hr : ∀ a, MemLp (r a) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x)*v b x ∂μ) = if a=b then (1:ℂ) else 0)
    (c : (Fin (n+1) → ι) → ℂ) :
    (∫ x, ‖tensorTotalReplacement v r c x‖^2 ∂(Measure.pi fun _ : Fin (n+1) => μ)) ≤
      (n+1:ℝ)^2*(∑ a, ∫ x, ‖r a x‖^2 ∂μ)*(∑ b, ‖c b‖^2) := by
  have hi (i : Fin (n+1)) := (tensorSlotReplacement_memLp v r hv hr c i).norm.integrable_sq
  calc
    _ ≤ ∫ x, (n+1:ℝ)*∑ i, ‖tensorSlotReplacement v r c i x‖^2
        ∂(Measure.pi fun _ : Fin (n+1) => μ) := by
      apply integral_mono (tensorTotalReplacement_memLp v r hv hr c).norm.integrable_sq
        ((integrable_finsetSum _ (fun i _ => hi i)).const_mul _)
      intro x
      simpa only [tensorTotalReplacement,Fintype.card_fin,Nat.cast_add,Nat.cast_one] using
        finite_sum_norm_square_le (fun i => tensorSlotReplacement v r c i x)
    _ = (n+1:ℝ)*∑ i, ∫ x, ‖tensorSlotReplacement v r c i x‖^2
        ∂(Measure.pi fun _ : Fin (n+1) => μ) := by
      rw [integral_const_mul,integral_finsetSum _ (fun i _ => hi i)]
    _ ≤ (n+1:ℝ)*∑ _i : Fin (n+1),
        (∑ a, ∫ x, ‖r a x‖^2 ∂μ)*(∑ b, ‖c b‖^2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ =>
        tensorSlotReplacement_L2_bound v r hv hr ho c i)) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        Nat.cast_add,Nat.cast_one]
      ring

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

theorem spinTensorResidual_L2_bound {n : ℕ} {α : Type*} [Fintype α]
    (v r : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2)
    (hr : ∀ a s, MemLp (fun x => r a x s) 2)
    (ho : ∀ a b, (∑ t : Fin 2, ∫ y, star (v a y t)*v b y t) =
      if a=b then (1:ℂ) else 0) (c : (Fin (n+1) → α) → ℂ) :
    (∫ x, ‖tensorTotalReplacement (fun a => Coulomb.flatSpinOrbital (v a))
      (fun a => Coulomb.flatSpinOrbital (r a)) c x‖^2
      ∂(Measure.pi fun _ : Fin (n+1) => Coulomb.spinSpaceMeasure)) ≤
      (n+1:ℝ)^2*(∑ a, ∫ x, ‖Coulomb.flatSpinOrbital (r a) x‖^2 ∂Coulomb.spinSpaceMeasure)*
        Coulomb.mass (finiteTensorState v hv hL2 hpartial c) := by
  have hflat (a b : α) :
      (∫ x, star (Coulomb.flatSpinOrbital (v a) x)*Coulomb.flatSpinOrbital (v b) x
        ∂Coulomb.spinSpaceMeasure) = if a=b then (1:ℂ) else 0 := by
    rw [Coulomb.flatSpinOrbital_inner _ _ (hL2 a) (hL2 b)]
    exact ho a b
  rw [finiteTensorState_mass v hv hL2 hpartial ho c]
  exact tensorTotalReplacement_L2_bound _ _
    (fun a => Coulomb.flatSpinOrbital_memLp (v a) (hL2 a))
    (fun a => Coulomb.flatSpinOrbital_memLp (r a) (hr a)) hflat c

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_WeakComplexLaplacian
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integration by parts for a complex C2 orbital against the full weak-H1
space. Only the sum of its second derivatives is required to lie in L2. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace ContinuumCoulomb

theorem configurationComplexPartial_C1 {n : ℕ} {φ : Configuration n → ℂ}
    (hφ : ContDiff ℝ 2 φ) (a : Fin n × Fin 3) :
    ContDiff ℝ 1 (configurationComplexPartial φ a) :=
  (hφ.fderiv_right (show (1 : WithTop ℕ∞)+1 ≤ 2 by norm_num)).clm_apply contDiff_const

theorem h1_inner_complex_coordinate {n : ℕ} (u : Coulomb.H1Vector n)
    (a : H1Index n) (φ : Configuration n → ℂ) (hφ : MemLp φ 2) :
    inner ℂ (hφ.toLp φ) (h1Coordinates u a) =
      ∫ x, star (φ x)*h1CoordinateFunction u a x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hφ.coeFn_toLp,(h1Coordinate_memLp u a).coeFn_toLp] with x hp hu
  change h1Coordinates u a x = h1CoordinateFunction u a x at hu
  rw [hp,hu,RCLike.inner_apply]
  exact mul_comm _ _

theorem weakH1_complex_laplacian_pairing (hdensity : PublishedSobolevSmoothDensity)
    {n : ℕ} (φ : Configuration n → ℂ) (hφ : ContDiff ℝ 2 φ)
    (hpartial : ∀ a, MemLp (configurationComplexPartial φ a) 2)
    (hlap : MemLp (configurationComplexLaplacian φ) 2)
    (v : Coulomb.H1Vector n) (s : SpinConfiguration n) :
    (∑ a, ∫ x, star (configurationComplexPartial φ a x)*v.gradient s a x) =
      -(∫ x, star (configurationComplexLaplacian φ x)*v.value s x) := by
  let G (a : Fin n × Fin 3) : Lp ℂ 2 (volume : Measure (Configuration n)) :=
    (hpartial a).toLp (configurationComplexPartial φ a)
  let L : Lp ℂ 2 (volume : Measure (Configuration n)) :=
    hlap.toLp (configurationComplexLaplacian φ)
  have hpair (w : Coulomb.H1Vector n) (a : Fin n × Fin 3) :
      inner ℂ (G a) (h1Coordinates w (Sum.inr (s,a))) =
        ∫ x, star (configurationComplexPartial φ a x)*w.gradient s a x :=
    h1_inner_complex_coordinate w (Sum.inr (s,a)) _ (hpartial a)
  have hlpair (w : Coulomb.H1Vector n) :
      inner ℂ L (h1Coordinates w (Sum.inl s)) =
        ∫ x, star (configurationComplexLaplacian φ x)*w.value s x :=
    h1_inner_complex_coordinate w (Sum.inl s) _ hlap
  have hcompact (w : Coulomb.H1Vector n)
      (hw : ∀ t, ContDiff ℝ 1 (w.value t) ∧ HasCompactSupport (w.value t))
      (hd : ∀ t a x, w.gradient t a x =
        fderiv ℝ (w.value t) x (EuclideanSpace.single a 1)) :
      (∑ a, inner ℂ (G a) (h1Coordinates w (Sum.inr (s,a)))) =
        -inner ℂ L (h1Coordinates w (Sum.inl s)) := by
    have hi (a : Fin n × Fin 3) : Integrable (fun x =>
        star (configurationComplexPartial (configurationComplexPartial φ a) a x)*w.value s x) :=
      (((configurationComplexPartial_C1 hφ a).continuous_fderiv (by norm_num)).clm_apply
        continuous_const).star.mul (hw s).1.continuous |>.integrable_of_hasCompactSupport (hw s).2.mul_left
    have he (a : Fin n × Fin 3) :
        (∫ x, star (configurationComplexPartial φ a x)*w.gradient s a x) =
          -(∫ x, star (configurationComplexPartial (configurationComplexPartial φ a) a x)*w.value s x) := by
      have hc := configurationComplexPartial_C1 hφ a
      have hstar (x : Configuration n) :
          fderiv ℝ (fun y => star (configurationComplexPartial φ a y)) x
            (EuclideanSpace.single a 1) =
          star (configurationComplexPartial (configurationComplexPartial φ a) a x) := by
        exact congrArg (fun B : Configuration n →L[ℝ] ℂ => B (EuclideanSpace.single a 1))
          (Complex.conjCLE.hasFDerivAt.comp x (hc.differentiable (by norm_num) x).hasFDerivAt).fderiv
      have hh := complex_C1_compact_test_ibp (fun x => star (configurationComplexPartial φ a x))
        (w.value s) (Complex.conjCLE.contDiff.comp hc) (hw s).1 (hw s).2
          (EuclideanSpace.single a 1)
      simpa only [hd,hstar] using hh
    simp only [hpair,hlpair]
    simp_rw [he]
    rw [Finset.sum_neg_distrib]
    congr 1
    rw [← integral_finsetSum Finset.univ (fun a _ => hi a)]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [configurationComplexLaplacian,star_sum,Finset.sum_mul]
  obtain ⟨w,hw,hd,ht⟩ := exists_compact_h1_graph_sequence hdensity v
  have hcG : Continuous (fun f : H1Coordinates n =>
      ∑ a, inner ℂ (G a) (f (Sum.inr (s,a)))) :=
    continuous_finsetSum _ (fun a _ => continuous_const.inner (continuous_apply _))
  have hcL : Continuous (fun f : H1Coordinates n => -inner ℂ L (f (Sum.inl s))) :=
    (continuous_const.inner (continuous_apply _)).neg
  have heq := tendsto_nhds_unique (hcG.continuousAt.tendsto.comp ht)
    ((hcL.continuousAt.tendsto.comp ht).congr' (Filter.Eventually.of_forall
      (fun k => (hcompact (w k) (hw k) (hd k)).symm)))
  simpa only [hpair,hlpair] using heq

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_TensorDifferential
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact coordinate derivatives of tensor products. Cross-coordinate
factors remain constant when differentiating a second time in one slot. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem coordinateProduct_C2 {n : ℕ} (f : Fin n → Position → ℂ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) : ContDiff ℝ 2 (coordinateProduct f) := by
  apply contDiff_prod
  intro i _
  exact (hf i).comp (Coulomb.positionCLM i).contDiff

theorem coordinateProduct_partial {n : ℕ} (f : Fin n → Position → ℂ)
    (hf : ∀ i, ContDiff ℝ 1 (f i)) (i : Fin n) (b : Fin 3) (x : Configuration n) :
    configurationComplexPartial (coordinateProduct f) (i,b) x =
      positionComplexPartial (f i) b (Coulomb.position x i)*
        ∏ j ∈ Finset.univ.erase i, f j (Coulomb.position x j) := by
  exact tensorOrbital_C1_fderiv (fun j y _ => f j y) (fun j _ => hf j) id
    (fun _ => 0) x i b

theorem coordinateProduct_partial_product {n : ℕ} (f : Fin n → Position → ℂ)
    (hf : ∀ i, ContDiff ℝ 1 (f i)) (i : Fin n) (b : Fin 3) :
    configurationComplexPartial (coordinateProduct f) (i,b) =
      coordinateProduct (fun j y => if j=i then positionComplexPartial (f j) b y else f j y) := by
  funext x
  rw [coordinateProduct_partial f hf i b x]
  change _ = Coulomb.slotTensor f (fun j => positionComplexPartial (f j) b) 1 i
    (fun j => Coulomb.position x j)
  rw [Coulomb.slotTensor_factor]
  rfl

theorem positionComplexPartial_C1 (f : Position → ℂ) (hf : ContDiff ℝ 2 f) (b : Fin 3) :
    ContDiff ℝ 1 (positionComplexPartial f b) :=
  (hf.fderiv_right (show (1 : WithTop ℕ∞)+1 ≤ 2 by norm_num)).clm_apply contDiff_const

theorem coordinateProduct_second {n : ℕ} (f : Fin n → Position → ℂ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (i : Fin n) (b : Fin 3) (x : Configuration n) :
    configurationComplexPartial (configurationComplexPartial (coordinateProduct f) (i,b)) (i,b) x =
      positionComplexPartial (positionComplexPartial (f i) b) b (Coulomb.position x i)*
        ∏ j ∈ Finset.univ.erase i, f j (Coulomb.position x j) := by
  let g : Fin n → Position → ℂ := fun j y => if j=i then positionComplexPartial (f j) b y else f j y
  have hg (j : Fin n) : ContDiff ℝ 1 (g j) := by
    by_cases hj : j=i
    · simpa only [g,hj,ite_true, if_true] using positionComplexPartial_C1 (f j) (hf j) b
    · simpa only [g,hj,ite_false, if_false] using (hf j).of_le (by norm_num)
  rw [coordinateProduct_partial_product f (fun j => (hf j).of_le (by norm_num)) i b]
  rw [coordinateProduct_partial _ hg i b x]
  change positionComplexPartial (g i) b (Coulomb.position x i)*_ = _
  have hgi : g i = positionComplexPartial (f i) b := by funext y; simp only [g,ite_true, if_true]
  rw [hgi]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp only [g,ite_eq_right (Finset.mem_erase.mp hj).1]

theorem coordinateProduct_laplacian {n : ℕ} (f : Fin n → Position → ℂ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (x : Configuration n) :
    configurationComplexLaplacian (coordinateProduct f) x =
      ∑ i, positionComplexLaplacian (f i) (Coulomb.position x i)*
        ∏ j ∈ Finset.univ.erase i, f j (Coulomb.position x j) := by
  unfold configurationComplexLaplacian
  rw [Fintype.sum_prod_type]
  simp_rw [coordinateProduct_second f hf]
  simp only [positionComplexLaplacian,Finset.sum_mul]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_TensorOperatorResidual
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The differential one-body residual of a product is the sum of the
one-orbital residuals in its electron slots. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem tensorOrbital_operator_residual {n : ℕ} {α : Type*}
    (v r : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 2 (fun x => v a x s))
    (V : Position → ℝ) (E : ℝ)
    (heq : ∀ a s x, r a x s = (-1/2:ℂ)*positionComplexLaplacian (fun y => v a y s) x+
      (V x:ℂ)*v a x s-(E:ℂ)*v a x s)
    (b : Fin n → α) (s : SpinConfiguration n) (x : Configuration n) :
    (-1/2:ℂ)*configurationComplexLaplacian (Coulomb.tensorOrbital v b s) x+
      ((∑ i, V (Coulomb.position x i)):ℝ)*Coulomb.tensorOrbital v b s x-
      ((n:ℝ)*E:ℝ)*Coulomb.tensorOrbital v b s x = tensorOrbitalResidual v r b s x := by
  have hL := coordinateProduct_laplacian (fun i y => v (b i) y (s i))
    (fun i => hv (b i) (s i)) x
  change configurationComplexLaplacian (Coulomb.tensorOrbital v b s) x = _ at hL
  have hf (i : Fin n) : v (b i) (Coulomb.position x i) (s i)*
      (∏ j ∈ Finset.univ.erase i, v (b j) (Coulomb.position x j) (s j)) =
      Coulomb.tensorOrbital v b s x :=
    Finset.mul_prod_erase Finset.univ
      (fun j => v (b j) (Coulomb.position x j) (s j)) (Finset.mem_univ i)
  have hR : tensorOrbitalResidual v r b s x =
      ∑ i, ((-1/2:ℂ)*
        (positionComplexLaplacian (fun y => v (b i) y (s i)) (Coulomb.position x i)*
          ∏ j ∈ Finset.univ.erase i, v (b j) (Coulomb.position x j) (s j))+
        (V (Coulomb.position x i):ℂ)*Coulomb.tensorOrbital v b s x-
        (E:ℂ)*Coulomb.tensorOrbital v b s x) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [heq]
    rw [show ((-1/2:ℂ)*positionComplexLaplacian (fun y => v (b i) y (s i)) (Coulomb.position x i)+
        (V (Coulomb.position x i):ℂ)*v (b i) (Coulomb.position x i) (s i)-
        (E:ℂ)*v (b i) (Coulomb.position x i) (s i))*
        (∏ j ∈ Finset.univ.erase i, v (b j) (Coulomb.position x j) (s j)) =
      (-1/2:ℂ)*(positionComplexLaplacian (fun y => v (b i) y (s i)) (Coulomb.position x i)*
        ∏ j ∈ Finset.univ.erase i, v (b j) (Coulomb.position x j) (s j))+
      (V (Coulomb.position x i):ℂ)*(v (b i) (Coulomb.position x i) (s i)*
        ∏ j ∈ Finset.univ.erase i, v (b j) (Coulomb.position x j) (s j))-
      (E:ℂ)*(v (b i) (Coulomb.position x i) (s i)*
        ∏ j ∈ Finset.univ.erase i, v (b j) (Coulomb.position x j) (s j)) by ring]
    rw [hf]
  rw [hR,hL]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,
    ← Finset.sum_mul,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_natCast]
  ring

theorem configurationComplexPartial_sum {n : ℕ} {α : Type*} [Fintype α]
    (c : α → ℂ) (f : α → Configuration n → ℂ) (hf : ∀ j, ContDiff ℝ 1 (f j))
    (a : Fin n × Fin 3) (x : Configuration n) :
    configurationComplexPartial (fun y => ∑ j, c j*f j y) a x =
      ∑ j, c j*configurationComplexPartial (f j) a x := by
  unfold configurationComplexPartial
  have hd (j : α) := (hf j).differentiable (by norm_num) x
  rw [fderiv_fun_sum (fun j _ => (hd j).const_mul (c j))]
  simp only [sum_apply,fderiv_const_mul (hd _),smul_apply,smul_eq_mul]

theorem configurationComplexLaplacian_sum {n : ℕ} {α : Type*} [Fintype α]
    (c : α → ℂ) (f : α → Configuration n → ℂ) (hf : ∀ j, ContDiff ℝ 2 (f j))
    (x : Configuration n) :
    configurationComplexLaplacian (fun y => ∑ j, c j*f j y) x =
      ∑ j, c j*configurationComplexLaplacian (f j) x := by
  have hfirst (a : Fin n × Fin 3) :
      configurationComplexPartial (fun y => ∑ j, c j*f j y) a =
        (fun y => ∑ j, c j*configurationComplexPartial (f j) a y) :=
    funext (configurationComplexPartial_sum c f (fun j => (hf j).of_le (by norm_num)) a)
  unfold configurationComplexLaplacian
  simp_rw [hfirst,configurationComplexPartial_sum c _
    (fun j => configurationComplexPartial_C1 (hf j) _)]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoreOrbitalProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrating the one-particle projection estimate over the other electron
coordinates. Slices belong to the full weak-H1 domain almost everywhere. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem bounded_state_potential_integrable {n : ℕ} (u : Coulomb.H1Vector n)
    (V : Configuration n → ℝ) (hV : Continuous V) (B : ℝ)
    (hB : ∀ x, |V x| ≤ B) (s : SpinConfiguration n) :
    Integrable (fun x => V x*‖u.value s x‖^2) := by
  apply ((u.value_L2 s).norm.integrable_sq.const_mul B).mono'
    (hV.aestronglyMeasurable.mul ((u.value_L2 s).aestronglyMeasurable.norm.pow 2))
  filter_upwards [] with x
  change ‖V x*‖u.value s x‖^2‖ ≤ B*‖u.value s x‖^2
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg ‖u.value s x‖)]
  exact mul_le_mul_of_nonneg_right (hB x) (sq_nonneg _)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoreTensorFiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The last-coordinate contraction in full spin space is exactly the
core-slice orbital coefficient used by the many-electron energy bound. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem spinConfigurationPoint_coordinates {n : ℕ}
    (z : Fin n → Fin 2 × (Fin 3 → ℝ)) :
    spinConfigurationPoint ((Coulomb.spinCubeEquiv n) z).1
      (WithLp.toLp 2 ((Coulomb.spinCubeEquiv n) z).2) = z := by
  rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FiniteTensorResidual
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The polynomial tensor residual is the actual differential residual of
finite tensor synthesis in the full physical spin space. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem tensorOrbitalResidual_memLp {n : ℕ} {α : Type*}
    (v r : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, MemLp (fun x => v a x s) 2)
    (hr : ∀ a s, MemLp (fun x => r a x s) 2)
    (b : Fin n → α) (s : SpinConfiguration n) :
    MemLp (tensorOrbitalResidual v r b s) 2 := by
  apply memLp_finsetSum Finset.univ
  intro i _
  have h := (Coulomb.slotTensor_memLp (fun j y => v (b j) y (s j))
    (fun j y => r (b j) y (s j)) (fun j => hv (b j) (s j)) (fun j => hr (b j) (s j)) 1 i).comp_measurePreserving
    (Coulomb.configurationMeasurableEquiv_measurePreserving n)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [Function.comp_apply,Coulomb.slotTensor_factor]
  rfl

theorem finiteTensorResidualValue_memLp {n : ℕ} {α : Type*} [Fintype α]
    (v r : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, MemLp (fun x => v a x s) 2)
    (hr : ∀ a s, MemLp (fun x => r a x s) 2)
    (c : (Fin n → α) → ℂ) (s : SpinConfiguration n) :
    MemLp (finiteTensorResidualValue v r c s) 2 :=
  memLp_finsetSum Finset.univ (fun b _ => (tensorOrbitalResidual_memLp v r hv hr b s).const_mul (c b))

theorem finiteTensorResidualValue_eq_flat {n : ℕ} {α : Type*} [Fintype α]
    (v r : α → Position → Fin 2 → ℂ) (c : (Fin n → α) → ℂ)
    (s : SpinConfiguration n) (x : Configuration n) :
    finiteTensorResidualValue v r c s x =
      tensorTotalReplacement (fun a => Coulomb.flatSpinOrbital (v a))
        (fun a => Coulomb.flatSpinOrbital (r a)) c (spinConfigurationPoint s x) := by
  unfold finiteTensorResidualValue tensorOrbitalResidual tensorTotalReplacement tensorSlotReplacement
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro b _
  change c b*(r (b i) (Coulomb.position x i) (s i)*
    ∏ j ∈ Finset.univ.erase i, v (b j) (Coulomb.position x j) (s j)) =
      c b*Coulomb.slotTensor (fun j y => v (b j) y (s j))
        (fun j y => r (b j) y (s j)) 1 i (fun j => Coulomb.position x j)
  rw [Coulomb.slotTensor_factor]
  rfl

theorem finiteTensorResidualValue_norm {n : ℕ} {α : Type*} [Fintype α]
    (v r : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, MemLp (fun x => v a x s) 2)
    (hr : ∀ a s, MemLp (fun x => r a x s) 2) (c : (Fin n → α) → ℂ) :
    (∑ s, ∫ x, ‖finiteTensorResidualValue v r c s x‖^2) =
      ∫ z, ‖tensorTotalReplacement (fun a => Coulomb.flatSpinOrbital (v a))
        (fun a => Coulomb.flatSpinOrbital (r a)) c z‖^2
        ∂(Measure.pi fun _ : Fin n => Coulomb.spinSpaceMeasure) := by
  have h := Coulomb.spinConfiguration_integral (fun s x => ‖finiteTensorResidualValue v r c s x‖^2)
    (fun s => (finiteTensorResidualValue_memLp v r hv hr c s).norm.integrable_sq)
  simp only [finiteTensorResidualValue_eq_flat,spinConfigurationPoint_coordinates] at h
  simpa only [finiteTensorResidualValue_eq_flat] using h.symm

theorem finiteTensorState_value_C2 {n : ℕ} {α : Type*} [Fintype α]
    (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 2 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2) (c : (Fin n → α) → ℂ) (s : SpinConfiguration n) :
    ContDiff ℝ 2 ((finiteTensorState v (fun a t => (hv a t).of_le (by norm_num)) hL2 hpartial c).value s) := by
  apply ContDiff.sum
  intro b _
  exact contDiff_const.mul (coordinateProduct_C2 (fun i y => v (b i) y (s i)) (fun i => hv (b i) (s i)))

theorem finiteTensorState_gradient_classical {n : ℕ} {α : Type*} [Fintype α]
    (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2) (c : (Fin n → α) → ℂ)
    (s : SpinConfiguration n) (a : Fin n × Fin 3) (x : Configuration n) :
    (finiteTensorState v hv hL2 hpartial c).gradient s a x =
      configurationComplexPartial ((finiteTensorState v hv hL2 hpartial c).value s) a x := by
  have h := configurationComplexPartial_sum c (fun b => Coulomb.tensorOrbital v b s)
    (fun b => tensorOrbital_C1 v hv b s) a x
  exact h.symm

theorem finiteTensorState_operator_residual {n : ℕ} {α : Type*} [Fintype α]
    (v r : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 2 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2)
    (V : Position → ℝ) (E : ℝ)
    (heq : ∀ a s x, r a x s = (-1/2:ℂ)*positionComplexLaplacian (fun y => v a y s) x+
      (V x:ℂ)*v a x s-(E:ℂ)*v a x s)
    (c : (Fin n → α) → ℂ) (s : SpinConfiguration n) (x : Configuration n) :
    let p := finiteTensorState v (fun a t => (hv a t).of_le (by norm_num)) hL2 hpartial c
    finiteTensorResidualValue v r c s x =
      (-1/2:ℂ)*configurationComplexLaplacian (p.value s) x+
      ((∑ i, V (Coulomb.position x i)):ℝ)*p.value s x-((n:ℝ)*E:ℝ)*p.value s x := by
  dsimp only
  change (∑ b, c b*tensorOrbitalResidual v r b s x) =
    (-1/2:ℂ)*configurationComplexLaplacian (fun y => ∑ b, c b*Coulomb.tensorOrbital v b s y) x+
    ((∑ i, V (Coulomb.position x i)):ℝ)*(∑ b, c b*Coulomb.tensorOrbital v b s x)-
    ((n:ℝ)*E:ℝ)*(∑ b, c b*Coulomb.tensorOrbital v b s x)
  rw [configurationComplexLaplacian_sum c (fun b => Coulomb.tensorOrbital v b s)
    (fun b => coordinateProduct_C2 (fun i y => v (b i) y (s i)) (fun i => hv (b i) (s i))) x]
  simp only [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [← tensorOrbital_operator_residual v r hv V E heq b s x]
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ClassicalResidualPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual differential residual controls the mixed bounded-potential
form against every weak-H1 state, without restricting its smoothness. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem h1Coordinates_complex_inner {n : ℕ} (u v : Coulomb.H1Vector n) (a : H1Index n) :
    inner ℂ (h1Coordinates u a) (h1Coordinates v a) =
      ∫ x, star (h1CoordinateFunction u a x)*h1CoordinateFunction v a x :=
  h1_inner_complex_coordinate v a _ (h1Coordinate_memLp u a)

theorem h1Coordinates_complex_mass_inner {n : ℕ} (u v : Coulomb.H1Vector n) :
    (∑ s, inner ℂ (h1Coordinates u (Sum.inl s)) (h1Coordinates v (Sum.inl s))) =
      inner ℂ u.toHilbert v.toHilbert := by
  rw [PiLp.inner_apply]
  rfl

theorem boundedPotential_complex_pairing {n : ℕ} (u v : Coulomb.H1Vector n)
    (V : Configuration n → ℝ) (hV : Continuous V) (B : ℝ) (hB : ∀ x, |V x| ≤ B)
    (s : SpinConfiguration n) :
    inner ℂ (h1Coordinates u (Sum.inl s))
      (BoundedPotential.operator V hV B hB (h1Coordinates v (Sum.inl s))) =
      ∫ x, star (u.value s x)*((V x:ℂ)*v.value s x) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(h1Coordinate_memLp u (Sum.inl s)).coeFn_toLp,
    (h1Coordinate_memLp v (Sum.inl s)).coeFn_toLp,
    BoundedPotential.operator_ae V hV B hB (h1Coordinates v (Sum.inl s))] with x hu hv hA
  change h1Coordinates u (Sum.inl s) x = u.value s x at hu
  change h1Coordinates v (Sum.inl s) x = v.value s x at hv
  rw [hA,hu,hv,RCLike.inner_apply]
  exact mul_comm _ _

theorem classical_residual_pairing (hdensity : PublishedSobolevSmoothDensity)
    {n : ℕ} (u v : Coulomb.H1Vector n)
    (V : Configuration n → ℝ) (hV : Continuous V) (B E : ℝ) (hB : ∀ x, |V x| ≤ B)
    (R : SpinConfiguration n → Configuration n → ℂ)
    (hR : ∀ s, MemLp (R s) 2)
    (hu : ∀ s, ContDiff ℝ 2 (u.value s))
    (hdu : ∀ s a x, u.gradient s a x = configurationComplexPartial (u.value s) a x)
    (heq : ∀ s x, R s x = (-1/2:ℂ)*configurationComplexLaplacian (u.value s) x+
      (V x:ℂ)*u.value s x-(E:ℂ)*u.value s x) :
    graphComplexCross (BoundedPotential.operator V hV B hB) (h1Coordinates u) (h1Coordinates v)-
      (E:ℂ)*inner ℂ u.toHilbert v.toHilbert =
      ∑ s, ∫ x, star (R s x)*v.value s x := by
  have hm (s : SpinConfiguration n) : MemLp (fun x => (V x:ℂ)*u.value s x) 2 := by
    apply (u.value_L2 s).of_le_mul (c := B)
      ((Complex.continuous_ofReal.comp hV).aestronglyMeasurable.mul (u.value_L2 s).aestronglyMeasurable)
    filter_upwards [] with x
    change ‖(V x:ℂ)*u.value s x‖ ≤ B*‖u.value s x‖
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)
  have hLap (s : SpinConfiguration n) : MemLp (configurationComplexLaplacian (u.value s)) 2 := by
    have hfun : configurationComplexLaplacian (u.value s) =
        (fun x => (2:ℂ)*((V x:ℂ)*u.value s x-(E:ℂ)*u.value s x-R s x)) := by
      funext x
      linear_combination 2*(heq s x)
    rw [hfun]
    exact ((hm s).sub ((u.value_L2 s).const_mul (E:ℂ)) |>.sub (hR s)).const_mul 2
  have hp (s : SpinConfiguration n) (a : Fin n × Fin 3) :
      MemLp (configurationComplexPartial (u.value s) a) 2 :=
    (memLp_congr_ae (Filter.Eventually.of_forall (hdu s a))).mp (u.partial_L2 s a)
  have hkin (s : SpinConfiguration n) := weakH1_complex_laplacian_pairing hdensity
    (u.value s) (hu s) (hp s) (hLap s) v s
  have hpoint (s : SpinConfiguration n) :
      (1/2:ℂ)*(∑ a, ∫ x, star (u.gradient s a x)*v.gradient s a x)+
        (∫ x, star (u.value s x)*((V x:ℂ)*v.value s x))-
        (E:ℂ)*(∫ x, star (u.value s x)*v.value s x) =
        ∫ x, star (R s x)*v.value s x := by
    have hLI := (hLap s).star.integrable_mul (v.value_L2 s)
    have hVI := (hm s).star.integrable_mul (v.value_L2 s)
    have hUI := (u.value_L2 s).star.integrable_mul (v.value_L2 s)
    have hhalf : star (-1/2:ℂ) = (-1/2:ℂ) := by
      change (starRingEnd ℂ) (-1/2) = (-1/2:ℂ)
      simp only [map_div₀,map_neg,map_one,map_ofNat]
    have hE : star (E:ℂ) = (E:ℂ) := Complex.conj_ofReal E
    have hprod (x : Configuration n) : star (R s x)*v.value s x =
        (-1/2:ℂ)*(star (configurationComplexLaplacian (u.value s) x)*v.value s x)+
          star ((V x:ℂ)*u.value s x)*v.value s x-
          (E:ℂ)*(star (u.value s x)*v.value s x) := by
      rw [heq]
      simp only [star_sub,star_add,star_mul,hhalf,hE]
      ring
    simp_rw [hprod]
    have hsub := integral_sub ((hLI.const_mul (-1/2:ℂ)).add hVI) (hUI.const_mul (E:ℂ))
    have hadd := integral_add (hLI.const_mul (-1/2:ℂ)) hVI
    simp only [Pi.add_apply,Pi.mul_apply,Pi.star_apply] at hsub hadd
    rw [hsub,hadd,integral_const_mul,integral_const_mul]
    simp_rw [← hdu] at hkin
    rw [hkin]
    have hvprod : (∫ x, star ((V x:ℂ)*u.value s x)*v.value s x) =
        ∫ x, star (u.value s x)*((V x:ℂ)*v.value s x) := by
      congr 1
      funext x
      simp only [star_mul,Complex.star_def,Complex.conj_ofReal]
      ring
    rw [hvprod]
    ring
  rw [← h1Coordinates_complex_mass_inner]
  simp only [graphComplexCross,h1Coordinates_complex_inner,boundedPotential_complex_pairing,
    h1CoordinateFunction]
  simp only [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun s _ => by simpa only [Finset.mul_sum] using hpoint s)

theorem residual_integral_square_bound {n : ℕ} (v : Coulomb.H1Vector n)
    (R : SpinConfiguration n → Configuration n → ℂ) (hR : ∀ s, MemLp (R s) 2) :
    ‖∑ s, ∫ x, star (R s x)*v.value s x‖^2 ≤
      (∑ s, ∫ x, ‖R s x‖^2)*Coulomb.mass v := by
  let r (s : SpinConfiguration n) : Lp ℂ 2 (volume : Measure (Configuration n)) :=
    (hR s).toLp (R s)
  have he (s : SpinConfiguration n) : (∫ x, star (R s x)*v.value s x) =
      inner ℂ (r s) (h1Coordinates v (Sum.inl s)) :=
    (h1_inner_complex_coordinate v (Sum.inl s) _ (hR s)).symm
  simp only [he]
  have ht : ‖∑ s, inner ℂ (r s) (h1Coordinates v (Sum.inl s))‖ ≤
      ∑ s, ‖r s‖*‖h1Coordinates v (Sum.inl s)‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum (fun s _ => norm_inner_le_norm _ _))
  have hb := (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _)
  simpa only [r,Coulomb.norm_toLp_sq_complex,h1Coordinates_norm_sq,h1CoordinateFunction,
    Coulomb.mass] using hb

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FiniteTensorDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The differential residual also controls the compressed diagonal energy.
This estimate retains polynomial dependence on the number of particles. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem graphBoundedCross_self {n : ℕ} (V : Configuration n → ℝ)
    (hV : Continuous V) (B : ℝ) (hB : ∀ x, |V x| ≤ B) (u : Coulomb.H1Vector n) :
    graphBoundedCross (BoundedPotential.operator V hV B hB)
      (h1Coordinates u) (h1Coordinates u) = boundedPotentialForm V u := by
  rw [boundedPotentialForm_eq_graph V hV B hB]
  simp only [graphBoundedCross,graphBoundedForm,graphKinetic,real_inner_self_eq_norm_sq]

theorem finiteTensorState_diagonal_square_bound (hdensity : PublishedSobolevSmoothDensity)
    {n : ℕ} {α : Type*} [Fintype α] (v r : α → Position → Fin 2 → ℂ)
    (hv₁ : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hv : ∀ a s, ContDiff ℝ 2 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2)
    (hr : ∀ a s, MemLp (fun x => r a x s) 2)
    (ho : ∀ a b, (∑ t : Fin 2, ∫ y, star (v a y t)*v b y t) =
      if a=b then (1:ℂ) else 0)
    (V : Position → ℝ) (hV : Continuous V) (E B : ℝ)
    (hB : ∀ x : Configuration (n+1), |∑ i, V (Coulomb.position x i)| ≤ B)
    (heq : ∀ a s x, r a x s = (-1/2:ℂ)*positionComplexLaplacian (fun y => v a y s) x+
      (V x:ℂ)*v a x s-(E:ℂ)*v a x s)
    (c : (Fin (n+1) → α) → ℂ) :
    let p : Coulomb.H1Vector (n+1) := finiteTensorState (n := n+1) v hv₁ hL2 hpartial c
    (boundedPotentialForm (fun x => ∑ i, V (Coulomb.position x i)) p-
      (n+1:ℝ)*E*Coulomb.mass p)^2 ≤
      (n+1:ℝ)^2*(∑ a, ∫ x, ‖Coulomb.flatSpinOrbital (r a) x‖^2 ∂Coulomb.spinSpaceMeasure)*
        Coulomb.mass p*Coulomb.mass p := by
  let p : Coulomb.H1Vector (n+1) := finiteTensorState (n := n+1) v hv₁ hL2 hpartial c
  let W : Configuration (n+1) → ℝ := fun x => ∑ i, V (Coulomb.position x i)
  have hW : Continuous W := continuous_finsetSum _ (fun i _ => hV.comp (Coulomb.positionCLM i).continuous)
  let R := finiteTensorResidualValue v r c
  have hR := finiteTensorResidualValue_memLp v r hL2 hr c
  have hid := classical_residual_pairing hdensity p p W hW B ((n+1:ℝ)*E) hB R hR
    (finiteTensorState_value_C2 v hv hL2 hpartial c)
    (finiteTensorState_gradient_classical v hv₁ hL2 hpartial c)
    (fun s x => by simpa only [Nat.cast_add,Nat.cast_one] using
      finiteTensorState_operator_residual v r hv hL2 hpartial V E heq c s x)
  have hself : (inner ℂ p.toHilbert p.toHilbert).re = Coulomb.mass p := by
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) p.toHilbert).symm.trans
      (Coulomb.H1Vector.toHilbert_norm_sq p)
  have hre := congrArg Complex.re hid
  simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,hself,← graphBoundedCross_eq_re,graphBoundedCross_self] at hre
  have hnorm := spinTensorResidual_L2_bound v r hv₁ hL2 hpartial hr ho c
  rw [← finiteTensorResidualValue_norm v r hL2 hr c] at hnorm
  have hb := (residual_integral_square_bound p R hR).trans
    (mul_le_mul_of_nonneg_right hnorm (Coulomb.mass_nonneg p))
  change (boundedPotentialForm W p-(n+1:ℝ)*E*Coulomb.mass p)^2 ≤ _
  rw [hre]
  apply le_trans _ hb
  rw [complex_norm_sq_parts]
  nlinarith only [sq_nonneg ((∑ s, ∫ x, star (R s x)*p.value s x).im)]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedFockStates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every state of the actual full half-filled Fock space is realized by
an antisymmetric weak-H1 continuum state in the corrected localized modes.
The continuum mass is exactly the finite occupation norm. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb
open HubbardGlobal

theorem localizedSpinMode_inner {freq D : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin (m+1) → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : (m+1 : ℕ) * localizedOverlapBound D ≤ 1/2) (i j : Fin ((2*m+1)+1)) :
    (∑ s : Fin 2, ∫ x, star (localizedSpinMode freq u i x s) * localizedSpinMode freq u j x s) =
      if i=j then (1 : ℂ) else 0 := by
  exact selectedRealSpinOrbitals_orthonormal (correctedLocalizedMode freq u) (by
    intro a b
    by_cases hab : a=b
    · simpa only [hab, ite_true, if_true] using correctedLocalizedMode_inner hfreq u hsep hs a b
    · simpa only [hab, ite_false, if_false] using correctedLocalizedMode_inner hfreq u hsep hs a b)
    (siteModes m).symm (siteModes m).symm.injective i j

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedTensorResidual
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

theorem localizedSpinResidual_memLp {rho H S freq : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 ≤ H) (hS : 0 ≤ S) (hfreq : 0 < freq)
    (scale : ℝ) {m : ℕ} (u : Fin (m+1) → PlanarPosition) {η : ℝ} (hη : 0 ≤ η)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ η) (j : Fin ((2*m+1)+1)) (s : Fin 2) :
    MemLp (fun x => localizedSpinResidual rho H S freq scale u j x s) 2 :=
  realSpinOrbital_memLp _
    (correctedManufacturedResidual_memLp hrho hH hS hfreq scale u hη hcoeff _) _ s

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_OneElectronComplexLaplacian
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The one-electron coordinate isometry identifies the physical complex
Laplacian with the Laplacian already used for the manufactured real orbitals. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem configurationComplexPartial_ofReal {n : ℕ} (f : Configuration n → ℝ)
    (hf : ContDiff ℝ 1 f) (a : Fin n × Fin 3) (x : Configuration n) :
    configurationComplexPartial (fun y => (f y:ℂ)) a x =
      (configurationRealPartial f a x:ℂ) := by
  exact congrArg (fun L : Configuration n →L[ℝ] ℂ => L (EuclideanSpace.single a 1))
    (Complex.ofRealCLM.hasFDerivAt.comp x (hf.differentiable (by norm_num) x).hasFDerivAt).fderiv

theorem configurationComplexLaplacian_ofReal {n : ℕ} (f : Configuration n → ℝ)
    (hf : ContDiff ℝ 2 f) (x : Configuration n) :
    configurationComplexLaplacian (fun y => (f y:ℂ)) x =
      (configurationRealLaplacian f x:ℂ) := by
  have hfirst (a : Fin n × Fin 3) :
      configurationComplexPartial (fun y => (f y:ℂ)) a =
        (fun y => (configurationRealPartial f a y:ℂ)) :=
    funext (configurationComplexPartial_ofReal f (hf.of_le (by norm_num)) a)
  simp only [configurationComplexLaplacian,hfirst,
    configurationComplexPartial_ofReal _ (configurationRealPartial_C1 hf _),
    configurationRealLaplacian,Complex.ofReal_sum]

theorem oneElectron_complex_partial (f : Position → ℂ) (hf : ContDiff ℝ 1 f)
    (b : Fin 3) (x : Configuration 1) :
    configurationComplexPartial (fun y => f (oneElectronCoordinates y)) (0,b) x =
      positionComplexPartial f b (oneElectronCoordinates x) := by
  have h := (hf.differentiable (by norm_num) (oneElectronCoordinates x)).hasFDerivAt.comp x
    oneElectronCoordinates.toContinuousLinearEquiv.hasFDerivAt
  simpa only [configurationComplexPartial,positionComplexPartial,Function.comp_def,
    ContinuousLinearMap.comp_apply,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe,oneElectronCoordinates_single] using
      congrArg (fun L : Configuration 1 →L[ℝ] ℂ => L (EuclideanSpace.single (0,b) 1)) h.fderiv

theorem oneElectron_complex_laplacian (f : Position → ℂ) (hf : ContDiff ℝ 2 f)
    (x : Configuration 1) :
    configurationComplexLaplacian (fun y => f (oneElectronCoordinates y)) x =
      positionComplexLaplacian f (oneElectronCoordinates x) := by
  have hfirst (b : Fin 3) :
      configurationComplexPartial (fun y => f (oneElectronCoordinates y)) (0,b) =
        (fun y => positionComplexPartial f b (oneElectronCoordinates y)) :=
    funext (oneElectron_complex_partial f (hf.of_le (by norm_num)) b)
  unfold configurationComplexLaplacian
  rw [Fintype.sum_prod_type,Fin.sum_univ_one]
  simp only [hfirst,oneElectron_complex_partial _ (positionComplexPartial_C1 f hf _),
    positionComplexLaplacian]

theorem correctedManufacturedResidual_complex_laplacian {rho freq : ℝ}
    (hrelation : freq^2 = 4*Real.pi*rho) (H S scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (i : Fin m) (x : Position) :
    (correctedManufacturedResidual rho H S freq scale u i x:ℂ) =
      (-1/2:ℂ)*positionComplexLaplacian (fun y => (correctedLocalizedMode freq u i y:ℂ)) x+
      (manufacturedSlabPotential rho H S freq scale u x:ℂ)*(correctedLocalizedMode freq u i x:ℂ)-
      (((-1/2:ℝ)+freq/2):ℂ)*(correctedLocalizedMode freq u i x:ℂ) := by
  have hf : ContDiff ℝ 2 (correctedLocalizedMode freq u i) :=
    (localizedLinearOrbital_C7 freq u (correctedLocalizedCoefficients u i)).of_le (by norm_num)
  have hx := correctedManufacturedResidual_eq hrelation H S scale u i (oneElectronCoordinates.symm x)
  have hL := oneElectron_complex_laplacian (fun y => (correctedLocalizedMode freq u i y:ℂ))
    (Complex.ofRealCLM.contDiff.comp hf) (oneElectronCoordinates.symm x)
  change configurationComplexLaplacian (fun y => (oneElectronCorrectedMode freq u i y:ℂ))
    (oneElectronCoordinates.symm x) = _ at hL
  rw [configurationComplexLaplacian_ofReal _ (oneElectronCorrectedMode_C2 freq u i)] at hL
  simp only [LinearIsometryEquiv.apply_symm_apply] at hx hL
  rw [← hL, hx]
  simp only [oneElectronCorrectedMode,LinearIsometryEquiv.apply_symm_apply]
  push_cast
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedSpinOperator
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual one-body differential residual of each corrected spatial-spin mode. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem localizedSpinMode_C2 (freq : ℝ) {m : ℕ} (u : Fin (m+1) → PlanarPosition)
    (j : Fin ((2*m+1)+1)) (s : Fin 2) : ContDiff ℝ 2 (fun x => localizedSpinMode freq u j x s) := by
  have hf : ContDiff ℝ 2 (correctedLocalizedMode freq u ((HubbardGlobal.siteModes m).symm j).1) :=
    (localizedLinearOrbital_C7 freq u (correctedLocalizedCoefficients u _)).of_le (by norm_num)
  by_cases hs : s=((HubbardGlobal.siteModes m).symm j).2
  · simpa only [localizedSpinMode,realSpinOrbital,hs,ite_true, if_true,Function.comp_def,
      Complex.ofRealCLM_apply] using Complex.ofRealCLM.contDiff.comp hf
  · simpa only [localizedSpinMode,realSpinOrbital,hs,ite_false, if_false] using
      (contDiff_const : ContDiff ℝ 2 (fun _ : Position => (0:ℂ)))

theorem localizedSpinResidual_operator {rho freq : ℝ} (hrelation : freq^2 = 4*Real.pi*rho)
    (H S scale : ℝ) {m : ℕ} (u : Fin (m+1) → PlanarPosition)
    (j : Fin ((2*m+1)+1)) (s : Fin 2) (x : Position) :
    localizedSpinResidual rho H S freq scale u j x s =
      (-1/2:ℂ)*positionComplexLaplacian (fun y => localizedSpinMode freq u j y s) x+
      (manufacturedSlabPotential rho H S freq scale u x:ℂ)*localizedSpinMode freq u j x s-
      (((-1/2:ℝ)+freq/2):ℂ)*localizedSpinMode freq u j x s := by
  by_cases hs : s=((HubbardGlobal.siteModes m).symm j).2
  · simpa only [localizedSpinResidual,localizedSpinMode,realSpinOrbital,hs,ite_true, if_true] using
      correctedManufacturedResidual_complex_laplacian hrelation H S scale u
        ((HubbardGlobal.siteModes m).symm j).1 x
  · simp [localizedSpinResidual,localizedSpinMode,realSpinOrbital,hs,
      positionComplexLaplacian,positionComplexPartial]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedCoercivity
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive tensor-complement gap retains kinetic coercivity. The
potential lower bound is uniform in the growing slab dimensions. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem planarWellSum_uniform_lower {m : ℕ} (u : Fin m → PlanarPosition)
    (x : PlanarPosition) : -(m:ℝ)*PlanarSobolev.wellBound ≤ planarWellSum u x := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    (abs_le.mp (by simpa only [Real.norm_eq_abs] using PlanarSobolev.wellBound_spec (x-u i))).1)
  simpa only [planarWellSum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    mul_neg,neg_mul] using h

theorem manufacturedSlab_uniform_lower {rho H S freq scale η : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hSH : S^3 ≤ H) (hscale : 0 ≤ scale)
    (hrelation : freq^2 = 4*Real.pi*rho) {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → 2 ≤ ‖u i-u j‖) (hη : 0 ≤ η)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ η) (x : Position) :
    -(((m:ℝ)+η)*PlanarSobolev.wellBound+6*Real.pi*rho) ≤
      manufacturedSlabPotential rho H S freq scale u x := by
  have h := manufacturedSlabPotential_lower hrho hH hS.le hscale hrelation u hsep hη hcoeff x
  have hp := planarWellSum_uniform_lower u (positionSplitCoordinates x).1
  have hv : 0 ≤ verticalCapPotential freq S (positionSplitCoordinates x).2 := by
    unfold verticalCapPotential
    positivity
  have hratio : 6*Real.pi*rho*S^3/H ≤ 6*Real.pi*rho := by
    apply (div_le_iff₀ hH).2
    exact mul_le_mul_of_nonneg_left hSH (by positivity)
  linarith

theorem boundedPotentialForm_kinetic_lower {n : ℕ}
    (V : Configuration n → ℝ) (hV : Continuous V) (B : ℝ) (hB : ∀ x, |V x| ≤ B)
    (C : ℝ) (hC : ∀ x, -C ≤ V x) (u : Coulomb.H1Vector n) :
    Coulomb.kinetic u-C*Coulomb.mass u ≤ boundedPotentialForm V u := by
  have hp (s : SpinConfiguration n) := integral_mono
    ((u.value_L2 s).norm.integrable_sq.const_mul (-C))
    (bounded_state_potential_integrable u V hV B hB s)
    (fun x => mul_le_mul_of_nonneg_right (hC x) (sq_nonneg ‖u.value s x‖))
  have h := Finset.sum_le_sum (s := Finset.univ) (fun s _ => hp s)
  simp only [integral_const_mul,← Finset.mul_sum] at h
  change (-C)*Coulomb.mass u ≤ Coulomb.potentialForm V u at h
  change Coulomb.kinetic u-C*Coulomb.mass u ≤ Coulomb.kinetic u+Coulomb.potentialForm V u
  linarith

theorem manufacturedSlab_manyElectron_kinetic_lower {rho H S freq scale η : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hSH : S^3 ≤ H) (hscale : 0 ≤ scale)
    (hrelation : freq^2 = 4*Real.pi*rho) {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → 2 ≤ ‖u i-u j‖) (hη : 0 ≤ η)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ η) {n : ℕ} (v : Coulomb.H1Vector n) :
    Coulomb.kinetic v-(n:ℝ)*(((m:ℝ)+η)*PlanarSobolev.wellBound+6*Real.pi*rho)*Coulomb.mass v ≤
      boundedPotentialForm (fun x => ∑ i, manufacturedSlabPotential rho H S freq scale u
        (Coulomb.position x i)) v := by
  let V (x : Configuration n) := ∑ i, manufacturedSlabPotential rho H S freq scale u (Coulomb.position x i)
  have hV : Continuous V := continuous_finsetSum _ (fun i _ =>
    (manufacturedSlabPotential_continuous hrho hH.le hS.le freq scale u).comp
      (Coulomb.positionCLM i).continuous)
  obtain ⟨B,hB⟩ := manufacturedSlabPotential_bounded hrho hH.le hS freq scale u
  have hb (x : Configuration n) : |V x| ≤ (n:ℝ)*B := by
    exact (Finset.abs_sum_le_sum_abs _ _).trans (by simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hB (Coulomb.position x i)))
  apply boundedPotentialForm_kinetic_lower V hV _ hb
  intro x
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    manufacturedSlab_uniform_lower hrho hH hS hSH hscale hrelation u hsep hη hcoeff (Coulomb.position x i))
  simpa only [V,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_neg] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedTensorDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual compressed manufactured-field energy and kinetic estimates. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem localizedTensorState_diagonal_square_bound
    (hdensity : PublishedSobolevSmoothDensity) {rho H S freq η D R : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hfreq : 0 < freq)
    (hrelation : freq^2 = 4*Real.pi*rho) (hR : 0 < R) (hRH : R ≤ H/2) (hRS : R ≤ S)
    (scale : ℝ) {m n : ℕ} (u : Fin (m+1) → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : (m+1:ℕ)*localizedOverlapBound D ≤ 1/2) (hη : 0 ≤ η)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ η)
    (c : (Fin (n+1) → Fin ((2*m+1)+1)) → ℂ) :
    let p := finiteTensorState (localizedSpinMode freq u) (localizedSpinMode_C1 freq u)
      (localizedSpinMode_memLp hfreq u) (localizedSpinMode_partial_memLp hfreq u) c
    (boundedPotentialForm (fun x => ∑ i, manufacturedSlabPotential rho H S freq scale u
        (Coulomb.position x i)) p-(n+1:ℝ)*((-1/2:ℝ)+freq/2)*Coulomb.mass p)^2 ≤
      (n+1:ℝ)^2*(8*(m+1:ℕ)^2*∑ j, manufacturedOrbitalSquaredError rho H S freq η D R u j)*
        Coulomb.mass p*Coulomb.mass p := by
  obtain ⟨B,hB⟩ := manufacturedSlabPotential_bounded hrho hH.le hS freq scale u
  have hsum (x : Configuration (n+1)) :
      |∑ i, manufacturedSlabPotential rho H S freq scale u (Coulomb.position x i)| ≤
        (n+1:ℝ)*B := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      Nat.cast_add,Nat.cast_one] using Finset.sum_le_sum (s := Finset.univ)
        (fun i _ => hB (Coulomb.position x i))
  have hc := finiteTensorState_diagonal_square_bound hdensity
    (localizedSpinMode freq u) (localizedSpinResidual rho H S freq scale u)
    (localizedSpinMode_C1 freq u) (localizedSpinMode_C2 freq u)
    (localizedSpinMode_memLp hfreq u) (localizedSpinMode_partial_memLp hfreq u)
    (localizedSpinResidual_memLp hrho hH.le hS.le hfreq scale u hη hcoeff)
    (fun a b => by
      have h := localizedSpinMode_inner hfreq u hsep hs a b
      by_cases hab : a=b <;> simpa only [hab,ite_true, if_true,ite_false, if_false] using h)
    (manufacturedSlabPotential rho H S freq scale u)
    (manufacturedSlabPotential_continuous hrho hH.le hS.le freq scale u)
    ((-1/2:ℝ)+freq/2) ((n+1:ℝ)*B) hsum
    (fun a s x => by
      simpa only [Complex.ofReal_add,Complex.ofReal_div,Complex.ofReal_neg,
        Complex.ofReal_one,Complex.ofReal_ofNat] using
        localizedSpinResidual_operator hrelation H S scale u a s x) c
  apply hc.trans
  apply mul_le_mul_of_nonneg_right _ (Coulomb.mass_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (Coulomb.mass_nonneg _)
  exact mul_le_mul_of_nonneg_left
    (localizedSpinResidual_sum_bound hrho hH hS hfreq hR hRH hRS scale u hsep hs hη hcoeff)
    (sq_nonneg _)

theorem localizedTensorState_kinetic_bound_oai
    (hdensity : PublishedSobolevSmoothDensity) {rho H S freq η D R ε : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hSH : S^3 ≤ H)
    (hfreq : 0 < freq) (hrelation : freq^2 = 4*Real.pi*rho)
    (hR : 0 < R) (hRH : R ≤ H/2) (hRS : R ≤ S)
    (scale : ℝ) (hscale : 0 ≤ scale) {m n : ℕ} (u : Fin (m+1) → PlanarPosition)
    (hD : 2 ≤ D) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : (m+1:ℕ)*localizedOverlapBound D ≤ 1/2) (hη : 0 ≤ η)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ η)
    (hε : 0 ≤ ε)
    (herr : (n+1:ℝ)^2*(8*(m+1:ℕ)^2*∑ j,
      manufacturedOrbitalSquaredError rho H S freq η D R u j) ≤ ε^2)
    (c : (Fin (n+1) → Fin ((2*m+1)+1)) → ℂ) :
    let p := finiteTensorState (localizedSpinMode freq u) (localizedSpinMode_C1 freq u)
      (localizedSpinMode_memLp hfreq u) (localizedSpinMode_partial_memLp hfreq u) c
    Coulomb.kinetic p ≤
      ((n+1:ℝ)*(((m+1:ℕ)+η)*PlanarSobolev.wellBound+6*Real.pi*rho+
        ((-1/2:ℝ)+freq/2))+ε)*Coulomb.mass p := by
  let p := finiteTensorState (localizedSpinMode freq u) (localizedSpinMode_C1 freq u)
    (localizedSpinMode_memLp hfreq u) (localizedSpinMode_partial_memLp hfreq u) c
  have hb := localizedTensorState_diagonal_square_bound hdensity hrho hH hS hfreq hrelation
    hR hRH hRS scale u hsep hs hη hcoeff c
  have hb' := hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right herr (Coulomb.mass_nonneg p)) (Coulomb.mass_nonneg p))
  have hnonneg : 0 ≤ ε*Coulomb.mass p := mul_nonneg hε (Coulomb.mass_nonneg p)
  have hupper : boundedPotentialForm (fun x => ∑ i,
      manufacturedSlabPotential rho H S freq scale u (Coulomb.position x i)) p ≤
      ((n+1:ℝ)*((-1/2:ℝ)+freq/2)+ε)*Coulomb.mass p := by
    change (_-(n+1:ℝ)*((-1/2:ℝ)+freq/2)*Coulomb.mass p)^2 ≤ _ at hb'
    nlinarith only [hb',hnonneg]
  have hk := manufacturedSlab_manyElectron_kinetic_lower hrho hH hS hSH hscale hrelation u
    (fun i j hij => hD.trans (hsep i j hij)) hη hcoeff p
  change Coulomb.kinetic p ≤
    ((n+1:ℝ)*(((m+1:ℕ)+η)*PlanarSobolev.wellBound+6*Real.pi*rho+
      ((-1/2:ℝ)+freq/2))+ε)*Coulomb.mass p
  simp only [Nat.cast_add,Nat.cast_one] at hk ⊢
  nlinarith only [hk,hupper]

end ContinuumCoulomb

end

end OAI
end

theorem solution : type_of% @OAI.ContinuumCoulomb.localizedTensorState_kinetic_bound_oai := @OAI.ContinuumCoulomb.localizedTensorState_kinetic_bound_oai
