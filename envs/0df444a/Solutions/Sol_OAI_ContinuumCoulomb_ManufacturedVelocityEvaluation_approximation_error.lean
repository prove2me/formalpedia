-- Prove2me | solution 1 for OAI.ContinuumCoulomb.ManufacturedVelocityEvaluation.approximation_error
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:16:33.051577+00:00
-- url     : https://prove2.me/submissions/87e78b4f-bf39-4d8a-82bb-9cedf0a9838e

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.RCLike.Lemmas
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
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_OAIQ092A008
import Definitions.Def_OAIQ092A009

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_UniformQuadrature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quantitative left-endpoint quadrature bound, including errors in the
sample values. It will be applied successively to the fixed-dimensional
truncated heat integral. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb.UniformQuadrature

theorem cell_error (f : ℝ → ℝ) {a h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hf : ContinuousOn f (Set.Icc a (a + h)))
    (hLip : ∀ x ∈ Set.Icc a (a + h), |f x - f a| ≤ L * |x - a|) :
    |h * f a - ∫ x in a..a + h, f x| ≤ L * h ^ 2 := by
  have hab : a ≤ a + h := by linarith
  have hfi : IntervalIntegrable f volume a (a + h) :=
    ContinuousOn.intervalIntegrable_of_Icc hab hf
  have heq : h * f a - (∫ x in a..a + h, f x) =
      ∫ x in a..a + h, (f a - f x) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hfi,
      intervalIntegral.integral_const]
    simp only [add_sub_cancel_left, smul_eq_mul]
  rw [heq]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun x => f a - f x) (a := a) (b := a + h) (C := L * h) (by
      intro x hx
      have hx' : x ∈ Set.Icc a (a + h) := by
        have hx'' : x ∈ Set.Ioc a (a + h) := by
          simpa only [Set.uIoc_of_le hab] using hx
        exact ⟨hx''.1.le, hx''.2⟩
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact (hLip x hx').trans (mul_le_mul_of_nonneg_left
        (by rw [abs_of_nonneg (sub_nonneg.mpr hx'.1)]; linarith [hx'.2]) hL))
  simpa only [Real.norm_eq_abs, add_sub_cancel_left, abs_of_nonneg hh, pow_two,
    mul_assoc] using hi

theorem cell_sample_error (f : ℝ → ℝ) (v : ℝ) {a h L ε : ℝ}
    (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hf : ContinuousOn f (Set.Icc a (a + h)))
    (hLip : ∀ x ∈ Set.Icc a (a + h), |f x - f a| ≤ L * |x - a|)
    (hv : |v - f a| ≤ ε) :
    |h * v - ∫ x in a..a + h, f x| ≤ L * h ^ 2 + h * ε := by
  have heq : h * v - (∫ x in a..a + h, f x) =
      h * (v - f a) + (h * f a - ∫ x in a..a + h, f x) := by ring
  rw [heq]
  calc
    _ ≤ |h * (v - f a)| + |h * f a - ∫ x in a..a + h, f x| := abs_add_le _ _
    _ ≤ h * ε + L * h ^ 2 := add_le_add
      (by rw [abs_mul, abs_of_nonneg hh]; exact mul_le_mul_of_nonneg_left hv hh)
      (cell_error f hh hL hf hLip)
    _ = _ := by ring

end ContinuumCoulomb.UniformQuadrature

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_UniformSamples
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Left-endpoint quadrature with a finite sequence of computed samples. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb.UniformQuadrature

theorem samples_error (f : ℝ → ℝ) (v : ℕ → ℝ) (a h : ℝ) (N : ℕ) {L ε : ℝ}
    (hh : 0 ≤ h) (hL : 0 ≤ L) (hf : Continuous f)
    (hLip : ∀ x ∈ Set.Icc a (node a h N), ∀ y ∈ Set.Icc a (node a h N),
      |f x - f y| ≤ L * |x - y|)
    (heval : ∀ i < N, |v i - f (node a h i)| ≤ ε) :
    |sampleSum h N v - ∫ x in a..node a h N, f x| ≤
      (N : ℝ) * (L * h ^ 2 + h * ε) := by
  have hnode (i j : ℕ) (hij : i ≤ j) : node a h i ≤ node a h j := by
    dsimp only [node]
    exact add_le_add_right (mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hh) a
  have hstep (i : ℕ) : node a h (i + 1) = node a h i + h := by
    simp only [node, Nat.cast_add, Nat.cast_one]
    ring
  have ht := intervalIntegral.sum_integral_adjacent_intervals
    (μ := volume) (a := node a h) (n := N) (f := f) (fun i _ => hf.intervalIntegrable _ _)
  have hzero : node a h 0 = a := by simp [node]
  rw [hzero] at ht
  have heq : sampleSum h N v - (∫ x in a..node a h N, f x) =
      ∑ i ∈ Finset.range N, (h * v i -
        ∫ x in node a h i..node a h (i + 1), f x) := by
    rw [Finset.sum_sub_distrib, ht, sampleSum, Finset.mul_sum]
  rw [heq]
  calc
    _ ≤ ∑ i ∈ Finset.range N, |h * v i -
        ∫ x in node a h i..node a h (i + 1), f x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range N, (L * h ^ 2 + h * ε) := by
      apply Finset.sum_le_sum
      intro i hi
      have hiN := Finset.mem_range.mp hi
      rw [hstep]
      apply cell_sample_error f _ hh hL hf.continuousOn _ (heval i hiN)
      intro x hx
      have hx' : x ∈ Set.Icc a (node a h N) := by
        refine ⟨?_, ?_⟩
        · have hi0 : a ≤ node a h i := by simpa only [hzero] using hnode 0 i (Nat.zero_le i)
          exact hi0.trans hx.1
        · exact hx.2.trans (by rw [← hstep]; exact hnode (i + 1) N hiN)
      have hi' : node a h i ∈ Set.Icc a (node a h N) :=
        ⟨by simpa only [hzero] using hnode 0 i (Nat.zero_le i), hnode i N hiN.le⟩
      exact hLip x hx' (node a h i) hi'
    _ = _ := by simp; ring

end ContinuumCoulomb.UniformQuadrature

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_UniformSamplesOn
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The quadrature estimate only needs a modulus on the integration
interval. This is the form used after cutting off the singular time zero. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb.UniformQuadrature

theorem continuousOn_of_abs_sub_le {f : ℝ → ℝ} {s : Set ℝ} {L : ℝ}
    (hLip : ∀ x ∈ s, ∀ y ∈ s, |f x - f y| ≤ L * |x - y|) : ContinuousOn f s := by
  have h := LipschitzOnWith.of_dist_le' (K := L) (f := f) (s := s) (by
    intro x hx y hy
    simpa only [Real.dist_eq] using hLip x hx y hy)
  exact h.continuousOn

theorem samples_error_lipschitz (f : ℝ → ℝ) (v : ℕ → ℝ)
    (a h : ℝ) (N : ℕ) {L ε : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hLip : ∀ x ∈ Set.Icc a (node a h N), ∀ y ∈ Set.Icc a (node a h N),
      |f x - f y| ≤ L * |x - y|)
    (heval : ∀ i < N, |v i - f (node a h i)| ≤ ε) :
    |sampleSum h N v - ∫ x in a..node a h N, f x| ≤
      (N : ℝ) * (L * h ^ 2 + h * ε) := by
  have hc := continuousOn_of_abs_sub_le hLip
  have hnode (i j : ℕ) (hij : i ≤ j) : node a h i ≤ node a h j := by
    dsimp only [node]
    exact add_le_add_right (mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hh) a
  have hstep (i : ℕ) : node a h (i + 1) = node a h i + h := by
    simp only [node, Nat.cast_add, Nat.cast_one]
    ring
  have hzero : node a h 0 = a := by simp [node]
  have hcell (i : ℕ) (hi : i < N) :
      Set.Icc (node a h i) (node a h (i + 1)) ⊆ Set.Icc a (node a h N) := by
    intro x hx
    have hi0 : a ≤ node a h i := by simpa only [hzero] using hnode 0 i (Nat.zero_le i)
    exact ⟨hi0.trans hx.1, hx.2.trans (hnode (i + 1) N hi)⟩
  have ht := intervalIntegral.sum_integral_adjacent_intervals
    (μ := volume) (a := node a h) (n := N) (f := f) (by
      intro i hi
      exact (hc.mono (hcell i hi)).intervalIntegrable_of_Icc (hnode i (i + 1) (Nat.le_succ i)))
  rw [hzero] at ht
  have heq : sampleSum h N v - (∫ x in a..node a h N, f x) =
      ∑ i ∈ Finset.range N, (h * v i -
        ∫ x in node a h i..node a h (i + 1), f x) := by
    rw [Finset.sum_sub_distrib, ht, sampleSum, Finset.mul_sum]
  rw [heq]
  calc
    _ ≤ ∑ i ∈ Finset.range N, |h * v i -
        ∫ x in node a h i..node a h (i + 1), f x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range N, (L * h ^ 2 + h * ε) := by
      apply Finset.sum_le_sum
      intro i hi
      have hiN := Finset.mem_range.mp hi
      have hci := hc.mono (hcell i hiN)
      rw [hstep] at hci ⊢
      apply cell_sample_error f _ hh hL hci _ (heval i hiN)
      intro x hx
      have hx' : x ∈ Set.Icc a (node a h N) := by
        apply hcell i hiN
        simpa only [hstep] using hx
      have hi' : node a h i ∈ Set.Icc a (node a h N) :=
        ⟨by simpa only [hzero] using hnode 0 i (Nat.zero_le i), hnode i N hiN.le⟩
      exact hLip x hx' (node a h i) hi'
    _ = _ := by simp; ring

theorem integral_parameter_lipschitz (f : ℝ → ℝ → ℝ) {a b c d L : ℝ}
    (hcd : c ≤ d)
    (hf : ∀ x ∈ Set.Icc a b, ContinuousOn (f x) (Set.Icc c d))
    (hLip : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, ∀ z ∈ Set.Icc c d,
      |f x z - f y z| ≤ L * |x - y|)
    {x y : ℝ} (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) :
    |(∫ z in c..d, f x z) - ∫ z in c..d, f y z| ≤ (d - c) * L * |x - y| := by
  rw [← intervalIntegral.integral_sub
    ((hf x hx).intervalIntegrable_of_Icc hcd) ((hf y hy).intervalIntegrable_of_Icc hcd)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun z => f x z - f y z) (a := c) (b := d) (C := L * |x - y|) (by
      intro z hz
      have hz' : z ∈ Set.Icc c d := by
        have hz'' : z ∈ Set.Ioc c d := by simpa only [Set.uIoc_of_le hcd] using hz
        exact ⟨hz''.1.le, hz''.2⟩
      simpa only [Real.norm_eq_abs] using hLip x hx y hy z hz')
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hcd), mul_assoc, mul_comm,
    mul_left_comm] using h

end ContinuumCoulomb.UniformQuadrature

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RectangleQuadrature
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative tensor quadrature in two coordinates, with independent
coordinate moduli and errors in each computed sample. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb.UniformQuadrature

theorem node_mem {a h : ℝ} {N i : ℕ} (hh : 0 ≤ h) (hi : i ≤ N) :
    node a h i ∈ Set.Icc a (node a h N) := by
  constructor
  · dsimp only [node]
    linarith [mul_nonneg (Nat.cast_nonneg i) hh]
  · dsimp only [node]
    exact add_le_add_right (mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hh) a

theorem rectangle_error (f : ℝ → ℝ → ℝ) (v : ℕ → ℕ → ℝ)
    (a hx : ℝ) (Nx : ℕ) (b hy : ℝ) (Ny : ℕ) {Lx Ly ε : ℝ}
    (hhx : 0 ≤ hx) (hhy : 0 ≤ hy) (hLx : 0 ≤ Lx) (hLy : 0 ≤ Ly)
    (hLipX : ∀ x ∈ Set.Icc a (node a hx Nx), ∀ x' ∈ Set.Icc a (node a hx Nx),
      ∀ y ∈ Set.Icc b (node b hy Ny), |f x y - f x' y| ≤ Lx * |x - x'|)
    (hLipY : ∀ x ∈ Set.Icc a (node a hx Nx), ∀ y ∈ Set.Icc b (node b hy Ny),
      ∀ y' ∈ Set.Icc b (node b hy Ny), |f x y - f x y'| ≤ Ly * |y - y'|)
    (heval : ∀ i < Nx, ∀ j < Ny,
      |v i j - f (node a hx i) (node b hy j)| ≤ ε) :
    |rectangleSum hx hy Nx Ny v -
      ∫ x in a..node a hx Nx, ∫ y in b..node b hy Ny, f x y| ≤
      ((Nx : ℝ) * hx) * ((Ny : ℝ) * hy) * (Lx * hx + Ly * hy + ε) := by
  have hylen : node b hy Ny - b = (Ny : ℝ) * hy := by dsimp [node]; ring
  have hys : b ≤ node b hy Ny := (node_mem hhy (Nat.le_refl Ny)).1
  have hL : 0 ≤ ((Ny : ℝ) * hy) * Lx := by positivity
  have hsection : ∀ x ∈ Set.Icc a (node a hx Nx),
      ContinuousOn (f x) (Set.Icc b (node b hy Ny)) := by
    intro x hx'
    exact continuousOn_of_abs_sub_le (hLipY x hx')
  have houterLip : ∀ x ∈ Set.Icc a (node a hx Nx),
      ∀ x' ∈ Set.Icc a (node a hx Nx),
      |(∫ y in b..node b hy Ny, f x y) - ∫ y in b..node b hy Ny, f x' y| ≤
        (((Ny : ℝ) * hy) * Lx) * |x - x'| := by
    intro x hx' x' hx''
    have h := integral_parameter_lipschitz f hys hsection hLipX hx' hx''
    simpa only [hylen] using h
  have hinner : ∀ i < Nx,
      |sampleSum hy Ny (v i) - ∫ y in b..node b hy Ny, f (node a hx i) y| ≤
        ((Ny : ℝ) * hy) * (Ly * hy + ε) := by
    intro i hi
    have h := samples_error_lipschitz (f (node a hx i)) (v i) b hy Ny hhy hLy
      (hLipY (node a hx i) (node_mem hhx hi.le)) (heval i hi)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have h := samples_error_lipschitz (fun x => ∫ y in b..node b hy Ny, f x y)
    (fun i => sampleSum hy Ny (v i)) a hx Nx hhx hL houterLip hinner
  change |rectangleSum hx hy Nx Ny v - _| ≤ _ at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

end ContinuumCoulomb.UniformQuadrature

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FiniteCubeQuadrature
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Product-interval integration and its uniform coordinate modulus. The
application uses dimension six; the recursion only avoids repeating six
identical one-dimensional estimates. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb.UniformQuadrature

theorem cubeMem_cons {n : ℕ} {a b x : ℝ} {v : Fin n → ℝ}
    (hx : x ∈ Set.Icc a b) (hv : cubeMem a b v) : cubeMem a b (Fin.cons x v) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hx
  · exact hv j

theorem cubeModulus_section {n : ℕ} {a b L : ℝ} {f : (Fin (n + 1) → ℝ) → ℝ}
    (hf : cubeModulus a b L f) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    cubeModulus a b L (fun v => f (Fin.cons x v)) := by
  intro v hv w hw
  have h := hf (Fin.cons x v) (cubeMem_cons hx hv) (Fin.cons x w) (cubeMem_cons hx hw)
  simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, sub_self, abs_zero, zero_add] using h

theorem cubeModulus_head {n : ℕ} {a b L x y : ℝ} {f : (Fin (n + 1) → ℝ) → ℝ}
    (hf : cubeModulus a b L f) (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b)
    {v : Fin n → ℝ} (hv : cubeMem a b v) :
    |f (Fin.cons x v) - f (Fin.cons y v)| ≤ L * |x - y| := by
  have h := hf (Fin.cons x v) (cubeMem_cons hx hv) (Fin.cons y v) (cubeMem_cons hy hv)
  simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, sub_self, abs_zero,
    Finset.sum_const_zero, add_zero] using h

theorem cubeIntegral_difference (n : ℕ) {a b Lf Lg ε : ℝ}
    (hab : a ≤ b) (hLf : 0 ≤ Lf) (hLg : 0 ≤ Lg) (hε : 0 ≤ ε)
    {f g : (Fin n → ℝ) → ℝ}
    (hf : cubeModulus a b Lf f) (hg : cubeModulus a b Lg g)
    (hfg : ∀ v, cubeMem a b v → |f v - g v| ≤ ε) :
    |cubeIntegral a b n f - cubeIntegral a b n g| ≤ (b - a) ^ n * ε := by
  induction n generalizing a b Lf Lg ε with
  | zero =>
    simpa only [cubeIntegral, pow_zero, one_mul] using hfg Fin.elim0 (by intro i; exact Fin.elim0 i)
  | succ n ih =>
    let F : ℝ → ℝ := fun x => cubeIntegral a b n (fun v => f (Fin.cons x v))
    let G : ℝ → ℝ := fun x => cubeIntegral a b n (fun v => g (Fin.cons x v))
    have hF : ContinuousOn F (Set.Icc a b) := by
      apply continuousOn_of_abs_sub_le (L := (b - a) ^ n * Lf)
      intro x hx y hy
      have hi := ih hab hLf hLf (mul_nonneg hLf (abs_nonneg (x - y)))
        (cubeModulus_section hf hx) (cubeModulus_section hf hy)
        (fun v hv => cubeModulus_head hf hx hy hv)
      convert hi using 1
      all_goals try with_reducible_and_instances rfl
      ring
    have hG : ContinuousOn G (Set.Icc a b) := by
      apply continuousOn_of_abs_sub_le (L := (b - a) ^ n * Lg)
      intro x hx y hy
      have hi := ih hab hLg hLg (mul_nonneg hLg (abs_nonneg (x - y)))
        (cubeModulus_section hg hx) (cubeModulus_section hg hy)
        (fun v hv => cubeModulus_head hg hx hy hv)
      convert hi using 1
      all_goals try with_reducible_and_instances rfl
      ring
    have hdiff (x : ℝ) (hx : x ∈ Set.Icc a b) : |F x - G x| ≤ (b - a) ^ n * ε :=
      ih hab hLf hLg hε (cubeModulus_section hf hx) (cubeModulus_section hg hx)
        (fun v hv => hfg (Fin.cons x v) (cubeMem_cons hx hv))
    change |(∫ x in a..b, F x) - ∫ x in a..b, G x| ≤ _
    rw [← intervalIntegral.integral_sub (hF.intervalIntegrable_of_Icc hab)
      (hG.intervalIntegrable_of_Icc hab)]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x => F x - G x) (a := a) (b := b) (C := (b - a) ^ n * ε) (by
        intro x hx
        have hx' : x ∈ Set.Ioc a b := by simpa only [Set.uIoc_of_le hab] using hx
        simpa only [Real.norm_eq_abs] using hdiff x ⟨hx'.1.le, hx'.2⟩)
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    rw [pow_succ]
    ring

theorem cubeIntegral_head_modulus {n : ℕ} {a b L : ℝ}
    (hab : a ≤ b) (hL : 0 ≤ L) {f : (Fin (n + 1) → ℝ) → ℝ}
    (hf : cubeModulus a b L f) {x y : ℝ}
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) :
    |cubeIntegral a b n (fun v => f (Fin.cons x v)) -
      cubeIntegral a b n (fun v => f (Fin.cons y v))| ≤
        ((b - a) ^ n * L) * |x - y| := by
  have h := cubeIntegral_difference n hab hL hL (mul_nonneg hL (abs_nonneg (x - y)))
    (cubeModulus_section hf hx) (cubeModulus_section hf hy)
    (fun v hv => cubeModulus_head hf hx hy hv)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring


theorem cube_quadrature_error (n : ℕ) {a h L ε : ℝ} {N : ℕ}
    (hh : 0 ≤ h) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    {f : (Fin n → ℝ) → ℝ} {v : (Fin n → ℕ) → ℝ}
    (hf : cubeModulus a (node a h N) L f)
    (hv : ∀ w, (∀ i, w i < N) →
      |v w - f (fun i => node a h (w i))| ≤ ε) :
    |cubeSample h N n v - cubeIntegral a (node a h N) n f| ≤
      ((N : ℝ) * h) ^ n * ((n : ℝ) * L * h + ε) := by
  induction n generalizing a h N L ε with
  | zero =>
    have hbase := hv Fin.elim0 (by intro i; exact Fin.elim0 i)
    have he : (fun i : Fin 0 => node a h (Fin.elim0 i)) = Fin.elim0 := Subsingleton.elim _ _
    simpa only [cubeSample, cubeIntegral, he, pow_zero, Nat.cast_zero, zero_mul,
      zero_add, one_mul] using hbase
  | succ n ih =>
    let b := node a h N
    let F : ℝ → ℝ := fun x => cubeIntegral a b n (fun w => f (Fin.cons x w))
    let V : ℕ → ℝ := fun i => cubeSample h N n (fun w => v (Fin.cons i w))
    have hab : a ≤ b := (node_mem hh (Nat.le_refl N)).1
    have hlen : b - a = (N : ℝ) * h := by dsimp [b, node]; ring
    have hLf : 0 ≤ (b - a) ^ n * L := mul_nonneg (pow_nonneg (sub_nonneg.mpr hab) _) hL
    have hLip : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
        |F x - F y| ≤ ((b - a) ^ n * L) * |x - y| := by
      intro x hx y hy
      exact cubeIntegral_head_modulus hab hL hf hx hy
    have hinner : ∀ i < N, |V i - F (node a h i)| ≤
        ((N : ℝ) * h) ^ n * ((n : ℝ) * L * h + ε) := by
      intro i hi
      apply ih hh hL hε (cubeModulus_section hf (node_mem hh hi.le))
      intro w hw
      have hwi : ∀ j : Fin (n + 1), (Fin.cons i w : Fin (n + 1) → ℕ) j < N := by
        intro j
        refine Fin.cases ?_ (fun k => ?_) j
        · simpa only [Fin.cons_zero] using hi
        · simpa only [Fin.cons_succ] using hw k
      have hpoint := hv (Fin.cons i w) hwi
      have he : (fun j : Fin (n + 1) => node a h ((Fin.cons i w : Fin (n + 1) → ℕ) j)) =
          Fin.cons (node a h i) (fun j => node a h (w j)) := by
        funext j
        exact Fin.cases rfl (fun _ => rfl) j
      simpa only [he] using hpoint
    have hout := samples_error_lipschitz F V a h N hh hLf hLip hinner
    change |cubeSample h N (n + 1) v - cubeIntegral a b (n + 1) f| ≤ _
    change |sampleSum h N V - ∫ x in a..b, F x| ≤ _
    apply hout.trans_eq
    rw [hlen, pow_succ, Nat.cast_add, Nat.cast_one]
    ring

end ContinuumCoulomb.UniformQuadrature

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FiniteDifferenceError
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform finite-difference error estimates including error in function
values. They will be applied to coordinate lines of the explicit C6 field. -/

namespace ContinuumCoulomb.FiniteDifferenceError

theorem linear_remainder (f f' : ℝ → ℝ) {a h b B : ℝ} (hh : 0 ≤ h)
    (hf : ∀ s ∈ Set.Icc a (a+h), HasDerivAt f (f' s) s)
    (hb : ∀ s ∈ Set.Ico a (a+h), |f' s-b| ≤ B) :
    |f (a+h)-f a-h*b| ≤ B*h := by
  let F : ℝ → ℝ := fun s => f s-(s-a)*b
  have hF (s : ℝ) (hs : s ∈ Set.Icc a (a+h)) :
      HasDerivWithinAt F (f' s-b) (Set.Icc a (a+h)) s := by
    have hd := ((hasDerivAt_id s).sub_const a).mul_const b
    simpa only [F,id_eq,one_mul] using ((hf s hs).fun_sub hd).hasDerivWithinAt
  have he := norm_image_sub_le_of_norm_deriv_le_segment' hF
    (fun s hs => by simpa only [Real.norm_eq_abs] using hb s hs)
    (a+h) (show a+h ∈ Set.Icc a (a+h) from ⟨by linarith,le_rfl⟩)
  have hid : f (a+h)-f a-h*b = F (a+h)-F a := by dsimp [F]; ring
  rw [hid]
  simpa only [Real.norm_eq_abs,add_sub_cancel_left] using he

theorem forward_difference (f f' evaluate : ℝ → ℝ) {x h L ε : ℝ}
    (hh : 0 < h) (hL : 0 ≤ L) (_hε : 0 ≤ ε)
    (hf : ∀ s ∈ Set.Icc x (x+h), HasDerivAt f (f' s) s)
    (hLip : ∀ s ∈ Set.Ico x (x+h), |f' s-f' x| ≤ L*|s-x|)
    (he0 : |evaluate x-f x| ≤ ε) (he1 : |evaluate (x+h)-f (x+h)| ≤ ε) :
    |(evaluate (x+h)-evaluate x)/h-f' x| ≤ L*h+2*ε/h := by
  have hr := linear_remainder f f' hh.le hf (b := f' x) (B := L*h) (by
    intro s hs
    have ht : |s-x| ≤ h := by rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]; linarith [hs.2]
    exact (hLip s hs).trans (mul_le_mul_of_nonneg_left ht hL))
  have hsum : |evaluate (x+h)-evaluate x-h*f' x| ≤ L*h^2+2*ε := by
    have hid : evaluate (x+h)-evaluate x-h*f' x =
        (evaluate (x+h)-f (x+h))-(evaluate x-f x)+(f (x+h)-f x-h*f' x) := by ring
    rw [hid]
    exact ((abs_add_le _ _).trans (add_le_add (abs_sub _ _ |>.trans (add_le_add he1 he0)) hr)).trans_eq (by ring)
  have hid : (evaluate (x+h)-evaluate x)/h-f' x =
      (evaluate (x+h)-evaluate x-h*f' x)/h := by field_simp
  rw [hid,abs_div,abs_of_pos hh]
  apply (div_le_div_of_nonneg_right hsum hh.le).trans_eq
  field_simp

theorem centered_remainder (f f' f'' : ℝ → ℝ) {x h L : ℝ}
    (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hf : ∀ s, HasDerivAt f (f' s) s)
    (hf' : ∀ s, HasDerivAt f' (f'' s) s)
    (hLip : ∀ s ∈ Set.Icc (x-h) (x+h), |f'' s-f'' x| ≤ L*|s-x|) :
    |f (x+h)+f (x-h)-2*f x-h^2*f'' x| ≤ L*h^3 := by
  let G : ℝ → ℝ := fun s => f (s+h)-f s
  let G' : ℝ → ℝ := fun s => f' (s+h)-f' s
  have hG (s : ℝ) (_hs : s ∈ Set.Icc (x-h) (x-h+h)) : HasDerivAt G (G' s) s := by
    exact ((hf (s+h)).comp s ((hasDerivAt_id s).add_const h)).sub (hf s) |>.congr_deriv (by ring)
  have hGbound (s : ℝ) (hs : s ∈ Set.Ico (x-h) (x-h+h)) :
      |G' s-h*f'' x| ≤ L*h^2 := by
    have hr := linear_remainder f' f'' hh (fun r _ => hf' r) (a := s) (b := f'' x)
      (B := L*h) (by
        intro r hr
        have hri : r ∈ Set.Icc (x-h) (x+h) := by constructor <;> linarith [hs.1,hs.2,hr.1,hr.2]
        have hdist : |r-x| ≤ h := abs_le.mpr ⟨by linarith [hri.1],by linarith [hri.2]⟩
        exact (hLip r hri).trans (mul_le_mul_of_nonneg_left hdist hL))
    exact hr.trans_eq (by ring)
  have hr := linear_remainder G G' hh hG hGbound
  have hid : G (x-h+h)-G (x-h)-h*(h*f'' x) =
      f (x+h)+f (x-h)-2*f x-h^2*f'' x := by
    dsimp [G]
    rw [sub_add_cancel]
    ring
  rw [hid] at hr
  exact hr.trans_eq (by ring)

theorem centered_difference (f f' f'' evaluate : ℝ → ℝ) {x h L ε : ℝ}
    (hh : 0 < h) (hL : 0 ≤ L)
    (hf : ∀ s, HasDerivAt f (f' s) s) (hf' : ∀ s, HasDerivAt f' (f'' s) s)
    (hLip : ∀ s ∈ Set.Icc (x-h) (x+h), |f'' s-f'' x| ≤ L*|s-x|)
    (he0 : |evaluate x-f x| ≤ ε) (hep : |evaluate (x+h)-f (x+h)| ≤ ε)
    (hem : |evaluate (x-h)-f (x-h)| ≤ ε) :
    |(evaluate (x+h)+evaluate (x-h)-2*evaluate x)/h^2-f'' x| ≤ L*h+4*ε/h^2 := by
  have hr := centered_remainder f f' f'' hh.le hL hf hf' hLip
  have herr : |evaluate (x+h)+evaluate (x-h)-2*evaluate x-h^2*f'' x| ≤ L*h^3+4*ε := by
    have hid : evaluate (x+h)+evaluate (x-h)-2*evaluate x-h^2*f'' x =
        (f (x+h)+f (x-h)-2*f x-h^2*f'' x)+
          ((evaluate (x+h)-f (x+h))+(evaluate (x-h)-f (x-h))-2*(evaluate x-f x)) := by ring
    rw [hid]
    have hnoise : |(evaluate (x+h)-f (x+h))+(evaluate (x-h)-f (x-h))-2*(evaluate x-f x)| ≤ 4*ε := by
      apply (abs_sub _ _).trans
      have hs := (abs_add_le _ _).trans (add_le_add hep hem)
      rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
      linarith
    exact (abs_add_le _ _).trans (add_le_add hr hnoise)
  have hid : (evaluate (x+h)+evaluate (x-h)-2*evaluate x)/h^2-f'' x =
      (evaluate (x+h)+evaluate (x-h)-2*evaluate x-h^2*f'' x)/h^2 := by field_simp
  rw [hid,abs_div,abs_of_nonneg (sq_nonneg h)]
  apply (div_le_div_of_nonneg_right herr (sq_nonneg h)).trans_eq
  field_simp

end ContinuumCoulomb.FiniteDifferenceError

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_MoserFlux
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit density homotopy and continuity equation used to transport
uniform slab density in the unit-charge construction. The identities describe
the explicit field and its density homotopy. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb
open NeutralAtom (dirPartial coordinateLaplacian axis)

theorem homotopyDensity_bounds {rho : ℝ} (V : Position → ℝ)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : Position) :
    rho / 2 ≤ homotopyDensity rho V t x ∧
      homotopyDensity rho V t x ≤ 3 * rho / 2 := by
  have hrho : 0 ≤ rho := by linarith [abs_nonneg (manufacturedCharge V x), hbound x]
  have hb := abs_le.mp (hbound x)
  have hlow := mul_le_mul_of_nonneg_left hb.1 ht0
  have hupp := mul_le_mul_of_nonneg_left hb.2 ht0
  have hscale := mul_le_mul_of_nonneg_right ht1 (by linarith : 0 ≤ rho / 2)
  dsimp [homotopyDensity]
  constructor <;> nlinarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_MoserChargeBounds
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform derivative control of the actual Poisson charge, from exactly
the six derivatives of the manufactured scalar potential. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb
open NeutralAtom (dirPartial coordinateLaplacian axis)

theorem dirPartial_iterated_norm_bound (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (v : Position) {k : ℕ} (hk : k ≤ 5) (x : Position) :
    ‖iteratedFDeriv ℝ k (dirPartial V v) x‖ ≤
      ‖v‖*‖iteratedFDeriv ℝ (k+1) V x‖ := by
  have hf : ContDiff ℝ 5 (fderiv ℝ V) := hV.fderiv_right (by norm_num)
  have h := norm_iteratedFDeriv_clm_apply_const (x := x) (c := v) hf.contDiffAt
    (show (k : WithTop ℕ∞) ≤ 5 by exact_mod_cast hk)
  rw [norm_iteratedFDeriv_fderiv] at h
  exact h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_MoserCoordinateDifferences
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! First and second coordinate differences approximate the actual
gradient and Laplacian of the manufactured C6 field. -/

noncomputable section
namespace ContinuumCoulomb.MoserCoordinateDifferences
open NeutralAtom (dirPartial axis)

private theorem partial_C5 (V : Position → ℝ) (hV : ContDiff ℝ 6 V) (a : Fin 3) :
    ContDiff ℝ 5 (dirPartial V (axis a)) :=
  (hV.fderiv_right (by norm_num)).clm_apply contDiff_const

private theorem second_C4 (V : Position → ℝ) (hV : ContDiff ℝ 6 V) (a : Fin 3) :
    ContDiff ℝ 4 (dirPartial (dirPartial V (axis a)) (axis a)) :=
  ((partial_C5 V hV a).fderiv_right (by norm_num)).clm_apply contDiff_const

private theorem partial_fderiv_bound (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    {B : ℝ} (hb : ∀ k ≤ 6, ∀ x, ‖iteratedFDeriv ℝ k V x‖ ≤ B) (a : Fin 3) (x : Position) :
    ‖fderiv ℝ (dirPartial V (axis a)) x‖ ≤ B := by
  have h := dirPartial_iterated_norm_bound V hV (axis a) (k := 1) (by norm_num) x
  rw [show ‖axis a‖ = 1 by simp [axis],one_mul,norm_iteratedFDeriv_one] at h
  exact h.trans (hb 2 (by norm_num) x)

private theorem second_fderiv_bound (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    {B : ℝ} (hb : ∀ k ≤ 6, ∀ x, ‖iteratedFDeriv ℝ k V x‖ ≤ B) (a : Fin 3) (x : Position) :
    ‖fderiv ℝ (dirPartial (dirPartial V (axis a)) (axis a)) x‖ ≤ B := by
  have hp := (partial_C5 V hV a).fderiv_right (by norm_num : (4:WithTop ℕ∞)+1 ≤ 5)
  have h := norm_iteratedFDeriv_clm_apply_const (x := x) (c := axis a) hp.contDiffAt
    (by norm_num : (1:WithTop ℕ∞) ≤ 4)
  rw [norm_iteratedFDeriv_fderiv] at h
  have h' := dirPartial_iterated_norm_bound V hV (axis a) (k := 2) (by norm_num) x
  rw [show ‖axis a‖ = 1 by simp [axis],one_mul] at h h'
  rw [norm_iteratedFDeriv_one] at h
  exact h.trans (h'.trans (hb 3 (by norm_num) x))

theorem along_axis_hasDerivAt (V : Position → ℝ) (hV : Differentiable ℝ V)
    (x : Position) (a : Fin 3) (t : ℝ) :
    HasDerivAt (fun s : ℝ => V (x+s • axis a)) (dirPartial V (axis a) (x+t • axis a)) t := by
  have hline : HasDerivAt (fun s : ℝ => x+s • axis a) (axis a) t := by
    simpa only [id_eq,one_smul] using ((hasDerivAt_id t).smul_const (axis a)).const_add x
  exact (hV _).hasFDerivAt.comp_hasDerivAt t hline

private theorem partial_axis_lipschitz (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    {B : ℝ} (hb : ∀ k ≤ 6, ∀ x, ‖iteratedFDeriv ℝ k V x‖ ≤ B)
    (x : Position) (a : Fin 3) (t : ℝ) :
    |dirPartial V (axis a) (x+t • axis a)-dirPartial V (axis a) x| ≤ B*|t| := by
  have h := (convex_univ : Convex ℝ (Set.univ : Set Position)).norm_image_sub_le_of_norm_fderiv_le
    (fun y _ => (partial_C5 V hV a).differentiable (by norm_num) y)
    (fun y _ => partial_fderiv_bound V hV hb a y) (Set.mem_univ x) (Set.mem_univ (x+t • axis a))
  simpa only [Real.norm_eq_abs,add_sub_cancel_left,norm_smul,show ‖axis a‖ = 1 by simp [axis],mul_one] using h

private theorem second_axis_lipschitz (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    {B : ℝ} (hb : ∀ k ≤ 6, ∀ x, ‖iteratedFDeriv ℝ k V x‖ ≤ B)
    (x : Position) (a : Fin 3) (t : ℝ) :
    |dirPartial (dirPartial V (axis a)) (axis a) (x+t • axis a)-
      dirPartial (dirPartial V (axis a)) (axis a) x| ≤ B*|t| := by
  have h := (convex_univ : Convex ℝ (Set.univ : Set Position)).norm_image_sub_le_of_norm_fderiv_le
    (fun y _ => (second_C4 V hV a).differentiable (by norm_num) y)
    (fun y _ => second_fderiv_bound V hV hb a y) (Set.mem_univ x) (Set.mem_univ (x+t • axis a))
  simpa only [Real.norm_eq_abs,add_sub_cancel_left,norm_smul,show ‖axis a‖ = 1 by simp [axis],mul_one] using h

theorem first_error (V evaluate : Position → ℝ) (hV : ContDiff ℝ 6 V)
    {B ε h : ℝ} (hB : 0 ≤ B) (hε : 0 ≤ ε) (hh : 0 < h)
    (hb : ∀ k ≤ 6, ∀ x, ‖iteratedFDeriv ℝ k V x‖ ≤ B)
    (he : ∀ y, |evaluate y-V y| ≤ ε) (x : Position) (a : Fin 3) :
    |(evaluate (x+h • axis a)-evaluate x)/h-dirPartial V (axis a) x| ≤ B*h+2*ε/h := by
  have ht := FiniteDifferenceError.forward_difference
    (fun s => V (x+s • axis a)) (fun s => dirPartial V (axis a) (x+s • axis a))
    (fun s => evaluate (x+s • axis a)) hh hB hε
    (fun s _ => along_axis_hasDerivAt V (hV.differentiable (by norm_num)) x a s)
    (x := 0) (fun s _ => by simpa using partial_axis_lipschitz V hV hb x a s)
    (he _) (he _)
  simpa only [zero_add,zero_smul,add_zero] using ht

theorem second_error (V evaluate : Position → ℝ) (hV : ContDiff ℝ 6 V)
    {B ε h : ℝ} (hB : 0 ≤ B) (hh : 0 < h)
    (hb : ∀ k ≤ 6, ∀ x, ‖iteratedFDeriv ℝ k V x‖ ≤ B)
    (he : ∀ y, |evaluate y-V y| ≤ ε) (x : Position) (a : Fin 3) :
    |(evaluate (x+h • axis a)+evaluate (x-h • axis a)-2*evaluate x)/h^2-
      dirPartial (dirPartial V (axis a)) (axis a) x| ≤ B*h+4*ε/h^2 := by
  have ht := FiniteDifferenceError.centered_difference
    (fun s => V (x+s • axis a)) (fun s => dirPartial V (axis a) (x+s • axis a))
    (fun s => dirPartial (dirPartial V (axis a)) (axis a) (x+s • axis a))
    (fun s => evaluate (x+s • axis a)) hh hB
    (fun s => along_axis_hasDerivAt V (hV.differentiable (by norm_num)) x a s)
    (fun s => along_axis_hasDerivAt _ ((partial_C5 V hV a).differentiable (by norm_num)) x a s)
    (x := 0) (fun s _ => by simpa using second_axis_lipschitz V hV hb x a s)
    (he _) (he _) (he _)
  simpa only [zero_add,zero_sub,zero_smul,add_zero,neg_smul,← sub_eq_add_neg] using ht

end ContinuumCoulomb.MoserCoordinateDifferences

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

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarModeProperties
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

theorem localizedDensity_coulomb_integrable_bound {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) (x : Position) :
    Integrable (fun y => NeutralAtom.coulombKernel (x - y) * localizedDensity freq u y) ∧
      NeutralAtom.potentialOf (localizedDensity freq u) x ≤ localizedPotentialBound freq := by
  have h := NeutralAtom.bounded_density_convolution NeutralAtom.measurable_coulombKernel
    NeutralAtom.coulombKernel_nonneg (NeutralAtom.coulombKernel_integrableOn_ball 1)
    (fun _ => NeutralAtom.coulombKernel_le_one) (localizedDensity_integrable hfreq u)
    (localizedDensity_nonnegative freq u) (localizedDensity_bound hfreq u) x
  simpa only [localizedDensity_mass hfreq u, localizedPotentialBound, NeutralAtom.kernelBallMass,
    NeutralAtom.potentialOf] using h

theorem localizedDensity_potential_nonnegative (freq : ℝ) (u : PlanarPosition) (x : Position) :
    0 ≤ NeutralAtom.potentialOf (localizedDensity freq u) x :=
  integral_nonneg (fun _ => mul_nonneg (NeutralAtom.coulombKernel_nonneg _)
    (localizedDensity_nonnegative freq u _))

theorem localizedDensity_potential_continuous {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) : Continuous (NeutralAtom.potentialOf (localizedDensity freq u)) :=
  NeutralAtom.potentialOf_continuous (localizedDensity_integrable hfreq u)
    (localizedDensity_nonnegative freq u) (localizedDensity_bound hfreq u)

theorem localizedCoulombCoeff_integrable {freq : ℝ} (hfreq : 0 < freq)
    (u v : PlanarPosition) :
    Integrable (fun x => localizedDensity freq u x *
      NeutralAtom.potentialOf (localizedDensity freq v) x) := by
  apply (localizedDensity_integrable hfreq u).mul_bdd (c := localizedPotentialBound freq)
    (localizedDensity_potential_continuous hfreq v).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_of_nonneg (localizedDensity_potential_nonnegative freq v x)]
    exact (localizedDensity_coulomb_integrable_bound hfreq v x).2)

theorem localizedCoulombCoeff_nonnegative (freq : ℝ) (u v : PlanarPosition) :
    0 ≤ localizedCoulombCoeff freq u v :=
  integral_nonneg (fun x => mul_nonneg (localizedDensity_nonnegative freq u x)
    (localizedDensity_potential_nonnegative freq v x))

theorem localizedCoulombCoeff_le {freq : ℝ} (hfreq : 0 < freq) (u v : PlanarPosition) :
    localizedCoulombCoeff freq u v ≤ localizedPotentialBound freq := by
  have hi := (localizedDensity_integrable hfreq u).mul_const (localizedPotentialBound freq)
  have h := integral_mono (localizedCoulombCoeff_integrable hfreq u v) hi
    (fun x => mul_le_mul_of_nonneg_left
      (localizedDensity_coulomb_integrable_bound hfreq v x).2
      (localizedDensity_nonnegative freq u x))
  simpa only [integral_mul_const, localizedDensity_mass hfreq u, one_mul,
    localizedCoulombCoeff] using h

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarHopping
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual positive contact hopping integral. Its Lipschitz control is
inherited from the compact forcing through the mass-one resolvent kernel. -/

noncomputable section
open MeasureTheory
open scoped NNReal
namespace ContinuumCoulomb

theorem planarResolventMode_integrand_integrable (r : PlanarPosition) :
    Integrable (fun b => planarResolventKernel b * planarForcing (r - b)) := by
  apply planarResolventKernel_integrable.mul_bdd (c := 1)
    (planarForcing_C7.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun b => by
    change ‖planarForcing (r - b)‖ ≤ (1 : ℝ)
    rw [Real.norm_of_nonneg (planarForcing_nonnegative _)]
    exact planarForcing_le_one _)

theorem planarAxis_zero_norm : ‖planarAxis 0‖ = 1 := by
  simp [planarAxis]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarRadial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rotation/reflection invariance of the actual manufactured planar data.
The hopping between arbitrary translated centers depends only on distance. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarForcing_isometry (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition) (r : PlanarPosition) :
    planarForcing (L r) = planarForcing r := by
  simp only [planarForcing, L.norm_map]

theorem planarResolventKernel_isometry (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition)
    (r : PlanarPosition) : planarResolventKernel (L r) = planarResolventKernel r := by
  simp only [planarResolventKernel, planarResolventIntegrand, planarHeatKernel, L.norm_map]

theorem planarResolventMode_isometry (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition)
    (r : PlanarPosition) : planarResolventMode (L r) = planarResolventMode r := by
  unfold planarResolventMode
  rw [← MeasureTheory.integral_comp L
    (fun b => planarResolventKernel b * planarForcing (L r - b))]
  apply integral_congr_ae
  filter_upwards [] with b
  rw [planarResolventKernel_isometry, ← L.map_sub, planarForcing_isometry]

theorem normalizedPlanarMode_isometry (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition)
    (r : PlanarPosition) : normalizedPlanarMode (L r) = normalizedPlanarMode r := by
  simp only [normalizedPlanarMode, planarResolventMode_isometry]

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

theorem planarCenter_sub (u v : PlanarPosition) : planarCenter (u - v) = planarCenter u - planarCenter v := by
  change positionSplitCoordinates.symm (u - v, 0) =
    positionSplitCoordinates.symm (u, 0) - positionSplitCoordinates.symm (v, 0)
  rw [← map_sub]
  simp only [Prod.mk_sub_mk, sub_self]

theorem planarCenter_norm_sub (u v : PlanarPosition) : ‖planarCenter u - planarCenter v‖ = ‖u - v‖ := by
  rw [← planarCenter_sub, planarCenter_norm]

theorem continuumLocalizedMode_translate (freq : ℝ) (u : PlanarPosition) (x : Position) :
    continuumLocalizedMode freq u x = continuumLocalizedMode freq 0 (x - planarCenter u) := by
  simp only [continuumLocalizedMode, localizedMode, map_sub, planarCenter,
    ContinuousLinearEquiv.apply_symm_apply, Prod.fst_sub, Prod.snd_sub, sub_zero]

theorem localizedDensity_translate (freq : ℝ) (u : PlanarPosition) (x : Position) :
    localizedDensity freq u x = localizedDensity freq 0 (x - planarCenter u) := by
  simp only [localizedDensity, continuumLocalizedMode_translate freq u]

theorem localizedDensity_potential_translate (freq : ℝ) (u : PlanarPosition) (x : Position) :
    NeutralAtom.potentialOf (localizedDensity freq u) x =
      NeutralAtom.potentialOf (localizedDensity freq 0) (x - planarCenter u) := by
  unfold NeutralAtom.potentialOf
  rw [← integral_add_right_eq_self
    (fun y => NeutralAtom.coulombKernel (x - y) * localizedDensity freq u y) (planarCenter u)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by
    dsimp only
    rw [localizedDensity_translate freq u, add_sub_cancel_right]
    congr 2
    abel)

theorem localizedCoulombProfileAt_eq (freq : ℝ) (u : PlanarPosition) :
    localizedCoulombProfileAt freq u = localizedCoulombCoeff freq 0 u := by
  unfold localizedCoulombProfileAt localizedCoulombCoeff
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x =>
    congrArg (fun z => localizedDensity freq 0 x * z)
      (localizedDensity_potential_translate freq u x).symm)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCoulombLipschitz
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform Lipschitz estimate for the actual direct-Coulomb profile. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem localizedDensity_potential_norm_sub {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) (x y : Position) :
    ‖NeutralAtom.potentialOf (localizedDensity freq u) x -
      NeutralAtom.potentialOf (localizedDensity freq u) y‖ ≤
        localizedCoulombLipschitzConstant freq * ‖x - y‖ := by
  simpa only [localizedDensity_mass hfreq u, localizedCoulombLipschitzConstant] using
    NeutralAtom.potentialOf_lipschitz_bound (localizedDensity_integrable hfreq u)
      (localizedDensity_nonnegative freq u) (localizedDensity_bound hfreq u) x y

theorem localizedCoulombProfileAt_integrable {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) : Integrable (fun x => localizedDensity freq 0 x *
      NeutralAtom.potentialOf (localizedDensity freq 0) (x - planarCenter u)) := by
  apply (localizedCoulombCoeff_integrable hfreq 0 u).congr
  exact Filter.Eventually.of_forall (fun x =>
    congrArg (fun z => localizedDensity freq 0 x * z)
      (localizedDensity_potential_translate freq u x))

theorem localizedCoulombProfileAt_norm_sub {freq : ℝ} (hfreq : 0 < freq)
    (u v : PlanarPosition) :
    ‖localizedCoulombProfileAt freq u - localizedCoulombProfileAt freq v‖ ≤
      localizedCoulombLipschitzConstant freq * ‖u - v‖ := by
  have hpt (x : Position) :
      ‖localizedDensity freq 0 x * NeutralAtom.potentialOf (localizedDensity freq 0) (x - planarCenter u) -
        localizedDensity freq 0 x * NeutralAtom.potentialOf (localizedDensity freq 0) (x - planarCenter v)‖ ≤
      (localizedCoulombLipschitzConstant freq * ‖u - v‖) * localizedDensity freq 0 x := by
    rw [← mul_sub, norm_mul, Real.norm_of_nonneg (localizedDensity_nonnegative freq 0 x)]
    have h := localizedDensity_potential_norm_sub hfreq 0 (x - planarCenter u) (x - planarCenter v)
    rw [show (x - planarCenter u) - (x - planarCenter v) = planarCenter v - planarCenter u by abel,
      norm_sub_rev (planarCenter v) (planarCenter u), planarCenter_norm_sub] at h
    calc
      _ ≤ localizedDensity freq 0 x *
          (localizedCoulombLipschitzConstant freq * ‖u - v‖) :=
        mul_le_mul_of_nonneg_left h (localizedDensity_nonnegative freq 0 x)
      _ = _ := mul_comm _ _
  unfold localizedCoulombProfileAt
  rw [← integral_sub (localizedCoulombProfileAt_integrable hfreq u)
    (localizedCoulombProfileAt_integrable hfreq v)]
  have h := norm_integral_le_of_norm_le
    (f := fun x => localizedDensity freq 0 x * NeutralAtom.potentialOf (localizedDensity freq 0) (x - planarCenter u) -
      localizedDensity freq 0 x * NeutralAtom.potentialOf (localizedDensity freq 0) (x - planarCenter v))
    ((localizedDensity_integrable hfreq 0).const_mul
      (localizedCoulombLipschitzConstant freq * ‖u - v‖))
    (Filter.Eventually.of_forall hpt)
  simpa only [integral_const_mul, localizedDensity_mass hfreq 0, mul_one] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCoulombRadial
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual direct Coulomb interaction depends only on planar separation. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem liftPlanarIsometry_coordinates (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition) (x : Position) :
    positionSplitCoordinates (liftPlanarIsometry L x) =
      (L (positionSplitCoordinates x).1, (positionSplitCoordinates x).2) := by
  change WithLp.ofLp (positionSplitIsometry (positionSplitIsometry.symm
    ((LinearIsometryEquiv.withLpProdCongr 2 L (LinearIsometryEquiv.refl ℝ ℝ))
      (positionSplitIsometry x)))) = _
  rw [positionSplitIsometry.apply_symm_apply]
  rfl

theorem localizedDensity_liftPlanarIsometry (freq : ℝ)
    (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition) (u : PlanarPosition) (x : Position) :
    localizedDensity freq (L u) (liftPlanarIsometry L x) = localizedDensity freq u x := by
  simp only [localizedDensity, continuumLocalizedMode, localizedMode,
    liftPlanarIsometry_coordinates, ← L.map_sub, normalizedPlanarMode_isometry]

theorem localizedDensity_potential_liftPlanarIsometry (freq : ℝ)
    (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition) (u : PlanarPosition) (x : Position) :
    NeutralAtom.potentialOf (localizedDensity freq (L u)) (liftPlanarIsometry L x) =
      NeutralAtom.potentialOf (localizedDensity freq u) x := by
  unfold NeutralAtom.potentialOf
  rw [← MeasureTheory.integral_comp (liftPlanarIsometry L)
    (fun y => NeutralAtom.coulombKernel (liftPlanarIsometry L x - y) * localizedDensity freq (L u) y)]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [localizedDensity_liftPlanarIsometry, ← (liftPlanarIsometry L).map_sub]
  simp only [NeutralAtom.coulombKernel, LinearIsometryEquiv.norm_map]

theorem localizedCoulombCoeff_isometry (freq : ℝ)
    (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition) (u v : PlanarPosition) :
    localizedCoulombCoeff freq (L u) (L v) = localizedCoulombCoeff freq u v := by
  unfold localizedCoulombCoeff
  rw [← MeasureTheory.integral_comp (liftPlanarIsometry L)
    (fun x => localizedDensity freq (L u) x * NeutralAtom.potentialOf (localizedDensity freq (L v)) x)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [localizedDensity_liftPlanarIsometry, localizedDensity_potential_liftPlanarIsometry]

theorem localizedCoulombProfileAt_isometry (freq : ℝ)
    (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition) (u : PlanarPosition) :
    localizedCoulombProfileAt freq (L u) = localizedCoulombProfileAt freq u := by
  rw [localizedCoulombProfileAt_eq, localizedCoulombProfileAt_eq]
  simpa only [map_zero] using localizedCoulombCoeff_isometry freq L 0 u

theorem localizedCoulombProfileAt_norm (freq : ℝ) (u : PlanarPosition) :
    localizedCoulombProfileAt freq u = localizedCoulombProfile freq ‖u‖ := by
  have hn : ‖‖u‖ • planarAxis 0‖ = ‖u‖ := by
    rw [norm_smul, planarAxis_zero_norm, mul_one, Real.norm_of_nonneg (norm_nonneg u)]
  have h := localizedCoulombProfileAt_isometry freq
    ((ℝ ∙ (‖u‖ • planarAxis 0 - u))ᗮ.reflection) (‖u‖ • planarAxis 0)
  rw [Submodule.reflection_sub hn] at h
  exact h

theorem localizedCoulombCoeff_displacement (freq : ℝ) (u v : PlanarPosition) :
    localizedCoulombCoeff freq u v = localizedCoulombProfileAt freq (v - u) := by
  unfold localizedCoulombCoeff localizedCoulombProfileAt
  rw [← integral_add_right_eq_self
    (fun x => localizedDensity freq u x * NeutralAtom.potentialOf (localizedDensity freq v) x)
    (planarCenter u)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [localizedDensity_translate freq u, add_sub_cancel_right, localizedDensity_potential_translate freq v]
  congr 2
  rw [planarCenter_sub]
  abel

theorem localizedCoulombCoeff_distance (freq : ℝ) (u v : PlanarPosition) :
    localizedCoulombCoeff freq u v = localizedCoulombProfile freq ‖u - v‖ := by
  rw [localizedCoulombCoeff_displacement, localizedCoulombProfileAt_norm, norm_sub_rev]

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

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarFieldBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual planar counterterm field has uniform derivative bounds,
independent of the number of sites. Separated unit supports leave at most
one nonzero summand at every point. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem planarWellDerivativeConstant_bound {k : ℕ} (hk : k ≤ 6) (r : PlanarPosition) :
    ‖iteratedFDeriv ℝ k manufacturedPlanarWell r‖ ≤ planarWellDerivativeConstant :=
  (Classical.choose_spec planarWell_derivatives_bounded).2 k hk r

private theorem well_derivative_near {k : ℕ} {r : PlanarPosition}
    (hr : iteratedFDeriv ℝ k manufacturedPlanarWell r ≠ 0) : ‖r‖ ≤ 1 := by
  have hs := (support_iteratedFDeriv_subset (𝕜 := ℝ) (f := manufacturedPlanarWell) k) hr
  have hb := (manufacturedPlanarWell_support.trans planarForcing_support) hs
  simpa only [Metric.mem_closedBall, dist_zero_right] using hb

private theorem countertermWellSum_derivative (freq scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) {k : ℕ} (hk : k ≤ 6) (r : PlanarPosition) :
    iteratedFDeriv ℝ k (countertermWellSum freq scale u) r =
      ∑ i, (1+localizedCounterterm freq u i/scale) •
        iteratedFDeriv ℝ k manufacturedPlanarWell (r-u i) := by
  have hw : ContDiff ℝ k manufacturedPlanarWell :=
    manufacturedPlanarWell_C7.of_le (by exact_mod_cast (show k ≤ 7 by omega))
  unfold countertermWellSum
  rw [iteratedFDeriv_fun_sum_apply
    (f := fun i x => (1+localizedCounterterm freq u i/scale)*manufacturedPlanarWell (x-u i))
    (fun i _ => (contDiff_const.mul (hw.comp (contDiff_id.sub contDiff_const))).contDiffAt)]
  apply Finset.sum_congr rfl
  intro i _
  change iteratedFDeriv ℝ k (fun x => (1+localizedCounterterm freq u i/scale) •
    manufacturedPlanarWell (x-u i)) r = _
  rw [iteratedFDeriv_const_smul_apply' (f := fun x => manufacturedPlanarWell (x-u i))
    (a := 1+localizedCounterterm freq u i/scale)
    (hw.comp (contDiff_id.sub contDiff_const)).contDiffAt,
    iteratedFDeriv_comp_sub]

/-- Uniformity in the number of separated sites is essential for the
polynomial-time transport/cubature constants. -/
theorem countertermWellSum_derivative_bound (freq : ℝ) {scale : ℝ} (hscale : 0 < scale)
    {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → 3 ≤ ‖u i-u j‖)
    (hcounter : ∀ i, localizedCounterterm freq u i ≤ scale)
    {k : ℕ} (hk : k ≤ 6) (r : PlanarPosition) :
    ‖iteratedFDeriv ℝ k (countertermWellSum freq scale u) r‖ ≤
      2*planarWellDerivativeConstant := by
  rw [countertermWellSum_derivative freq scale u hk r]
  have hcoef (i : Fin m) : |1+localizedCounterterm freq u i/scale| ≤ 2 := by
    have hlo := div_nonneg (localizedCounterterm_nonnegative freq u i) hscale.le
    have hhi := (div_le_one hscale).mpr (hcounter i)
    rw [abs_of_nonneg (by linarith)]
    linarith
  by_cases h : ∃ i, iteratedFDeriv ℝ k manufacturedPlanarWell (r-u i) ≠ 0
  · obtain ⟨i, hi⟩ := h
    have hzero (j : Fin m) (hji : j ≠ i) :
        iteratedFDeriv ℝ k manufacturedPlanarWell (r-u j) = 0 := by
      by_contra hj
      have hri := well_derivative_near hi
      have hrj := well_derivative_near hj
      have ht : ‖u i-u j‖ ≤ ‖r-u i‖+‖r-u j‖ := by
        calc
          _ = ‖(u i-r)+(r-u j)‖ := by congr 1; abel
          _ ≤ ‖u i-r‖+‖r-u j‖ := norm_add_le _ _
          _ = _ := by rw [norm_sub_rev (u i) r]
      have hd := hsep i j hji.symm
      linarith
    rw [Finset.sum_eq_single i (fun j _ hji => by rw [hzero j hji, smul_zero])
      (fun hn => (hn (Finset.mem_univ i)).elim), norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hcoef i) (planarWellDerivativeConstant_bound hk _) (norm_nonneg _)
      (by norm_num)
  · have hzero (i : Fin m) : iteratedFDeriv ℝ k manufacturedPlanarWell (r-u i) = 0 := by
      by_contra hi
      exact h ⟨i, hi⟩
    simp only [hzero, smul_zero, Finset.sum_const_zero, norm_zero]
    exact mul_nonneg (by norm_num) planarWellDerivativeConstant_positive.le

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedFieldBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform derivatives through order six of the actual three-dimensional
manufactured field. Constants do not grow with the number of wells or slab width. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

private theorem linear_comp_six_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) (f : F → ℝ)
    (hf : ContDiff ℝ 6 f) {B D : ℝ} (hB : 0 ≤ B) (hD : 1 ≤ D) (hL : ‖L‖ ≤ D)
    (hb : ∀ k ≤ 6, ∀ x, ‖iteratedFDeriv ℝ k f x‖ ≤ B) {k : ℕ} (hk : k ≤ 6) (x : E) :
    ‖iteratedFDeriv ℝ k (f ∘ L) x‖ ≤ B*D^6 := by
  rw [L.iteratedFDeriv_comp_right hf x (by exact_mod_cast hk)]
  have h := (iteratedFDeriv ℝ k f (L x)).norm_compContinuousLinearMap_le (fun _ => L)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  calc
    _ ≤ ‖iteratedFDeriv ℝ k f (L x)‖ * ‖L‖^k := h
    _ ≤ B*D^k := mul_le_mul (hb k hk (L x))
      (pow_le_pow_left₀ (norm_nonneg L) hL k) (pow_nonneg (norm_nonneg L) k) hB
    _ ≤ B*D^6 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hk) hB

private theorem wellPlanar_bound_nonnegative : 0 ≤ wellPlanarDerivativeBound := by
  have hC := planarWellDerivativeConstant_positive.le
  unfold wellPlanarDerivativeBound
  positivity

private theorem wellCutoff_bound_nonnegative : 0 ≤ wellCutoffDerivativeBound := by
  have h := (Classical.choose_spec cutoff_derivative_bound_exists).1
  unfold wellCutoffDerivativeBound wellCutoffDerivativeConstant
  positivity

private theorem manufacturedField_planar_bound (freq : ℝ) {scale : ℝ} (hscale : 0 < scale)
    {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → 3 ≤ ‖u i-u j‖)
    (hcounter : ∀ i, localizedCounterterm freq u i ≤ scale)
    {k : ℕ} (hk : k ≤ 6) (x : Position) :
    ‖iteratedFDeriv ℝ k (fun y : Position =>
      countertermWellSum freq scale u (positionSplitCoordinates y).1) x‖ ≤
        wellPlanarDerivativeBound := by
  have hC := planarWellDerivativeConstant_positive.le
  exact linear_comp_six_bound wellPlanarProjection (countertermWellSum freq scale u)
    ((countertermWellSum_C7 freq scale u).of_le (by norm_num))
    (by positivity) (le_max_left _ _) (le_max_right _ _)
    (fun j hj r => countertermWellSum_derivative_bound freq hscale u hsep hcounter hj r) hk x

private theorem manufacturedField_cutoff_bound {S : ℝ} (hS : 1 ≤ S)
    {k : ℕ} (hk : k ≤ 6) (x : Position) :
    ‖iteratedFDeriv ℝ k (fun y : Position => slabWellCutoff S (positionSplitCoordinates y).2) x‖ ≤
      wellCutoffDerivativeBound := by
  let L : Position →L[ℝ] ℝ := (2/S) • wellVerticalProjection
  have hS0 : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have hscale : |2/S| ≤ 2 := by
    rw [abs_of_nonneg (by positivity)]
    exact (div_le_iff₀ hS0).mpr (by linarith)
  have hL : ‖L‖ ≤ max 1 (2*‖wellVerticalProjection‖) := by
    dsimp only [L]
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hscale (norm_nonneg _)).trans (le_max_right _ _)
  exact linear_comp_six_bound L (verticalCutoffBump : ℝ → ℝ)
    (verticalCutoffBump.contDiff : ContDiff ℝ 6 (verticalCutoffBump : ℝ → ℝ))
    (Classical.choose_spec cutoff_derivative_bound_exists).1.le (le_max_left _ _) hL
    (Classical.choose_spec cutoff_derivative_bound_exists).2 hk x

/-- A fixed bound for all six derivatives, uniform over every separated
site family, every admissible counterterm and every slab width at least one. -/
theorem manufacturedWellField_derivative_bound (freq : ℝ) {scale S : ℝ}
    (hscale : 0 < scale) (hS : 1 ≤ S) {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → 3 ≤ ‖u i-u j‖)
    (hcounter : ∀ i, localizedCounterterm freq u i ≤ scale)
    {k : ℕ} (hk : k ≤ 6) (x : Position) :
    ‖iteratedFDeriv ℝ k (manufacturedWellField freq scale S u) x‖ ≤
      manufacturedFieldDerivativeConstant := by
  have hcut : ContDiff ℝ 6 (fun y : Position =>
      slabWellCutoff S (positionSplitCoordinates y).2) :=
    ((slabWellCutoff_smooth S).of_le (by first | simp | exact_mod_cast le_top)).comp
      positionSplitCoordinates.contDiff.snd
  have hplan : ContDiff ℝ 6 (fun y : Position =>
      countertermWellSum freq scale u (positionSplitCoordinates y).1) :=
    ((countertermWellSum_C7 freq scale u).of_le (show (6 : WithTop ℕ∞) ≤ 7 by norm_num)).comp
      positionSplitCoordinates.contDiff.fst
  have h := norm_iteratedFDeriv_mul_le hcut hplan x
    (show (k : WithTop ℕ∞) ≤ 6 by exact_mod_cast hk)
  change ‖iteratedFDeriv ℝ k (manufacturedWellField freq scale S u) x‖ ≤ _ at h
  apply h.trans
  calc
    _ ≤ ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ)*wellCutoffDerivativeBound*wellPlanarDerivativeBound := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (manufacturedField_cutoff_bound hS (hi'.trans hk) x)
          (Nat.cast_nonneg _))
        (manufacturedField_planar_bound freq hscale u hsep hcounter (Nat.sub_le k i |>.trans hk) x)
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) wellCutoff_bound_nonnegative)
    _ = (2:ℝ)^k*wellCutoffDerivativeBound*wellPlanarDerivativeBound := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose k
    _ ≤ 64*wellCutoffDerivativeBound*wellPlanarDerivativeBound := by
      apply mul_le_mul_of_nonneg_right _ wellPlanar_bound_nonnegative
      apply mul_le_mul_of_nonneg_right _ wellCutoff_bound_nonnegative
      exact (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hk).trans_eq (by norm_num)
    _ = _ := rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CappedCoulombKernel
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded Lipschitz kernel for literal Coulomb quadrature. The original
singular potential differs only inside the cap radius; the next theorem
controls that error by the actual Coulomb mass of the small ball. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem cappedCoulombKernel_nonnegative {ε : ℝ} (hε : 0 < ε) (x : Position) :
    0 ≤ cappedCoulombKernel ε x := by
  unfold cappedCoulombKernel
  exact inv_nonneg.mpr (hε.le.trans (le_max_left _ _))

theorem cappedCoulombKernel_le {ε : ℝ} (hε : 0 < ε) (x : Position) :
    cappedCoulombKernel ε x ≤ ε⁻¹ :=
  inv_anti₀ hε (le_max_left _ _)

theorem cappedCoulombKernel_continuous {ε : ℝ} (hε : 0 < ε) :
    Continuous (cappedCoulombKernel ε) := by
  apply (continuous_const.max continuous_norm).inv₀
  intro x
  exact (hε.trans_le (le_max_left _ _)).ne'

theorem cappedCoulombKernel_norm_sub {ε : ℝ} (hε : 0 < ε) (x y : Position) :
    |cappedCoulombKernel ε x - cappedCoulombKernel ε y| ≤ ε⁻¹ ^ 2 * ‖x - y‖ := by
  let a := max ε ‖x‖
  let b := max ε ‖y‖
  have ha : 0 < a := hε.trans_le (le_max_left _ _)
  have hb : 0 < b := hε.trans_le (le_max_left _ _)
  have hia : a⁻¹ ≤ ε⁻¹ := inv_anti₀ hε (le_max_left _ _)
  have hib : b⁻¹ ≤ ε⁻¹ := inv_anti₀ hε (le_max_left _ _)
  have hdiff : |a - b| ≤ ‖x - y‖ := by
    have hm := abs_max_sub_max_le_abs ‖x‖ ‖y‖ ε
    rw [max_comm ‖x‖ ε, max_comm ‖y‖ ε] at hm
    exact hm.trans (abs_norm_sub_norm_le x y)
  have he : cappedCoulombKernel ε x - cappedCoulombKernel ε y =
      (b - a) * a⁻¹ * b⁻¹ := by
    change a⁻¹ - b⁻¹ = _
    field_simp [ha.ne', hb.ne']
  rw [he, abs_mul, abs_mul, abs_of_pos (inv_pos.mpr ha),
    abs_of_pos (inv_pos.mpr hb), abs_sub_comm b a]
  calc
    _ ≤ ‖x - y‖ * ε⁻¹ * ε⁻¹ := by gcongr
    _ = _ := by ring

theorem cappedCoulombKernel_difference {ε : ℝ} (hε : 0 < ε)
    (x : Position) (hx : x ≠ 0) :
    |NeutralAtom.coulombKernel x - cappedCoulombKernel ε x| ≤
      (Metric.ball (0 : Position) ε).indicator NeutralAtom.coulombKernel x := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  by_cases he : ‖x‖ < ε
  · rw [Set.indicator_of_mem (by simpa only [Metric.mem_ball, dist_zero_right] using he)]
    have hc : cappedCoulombKernel ε x = ε⁻¹ := by
      unfold cappedCoulombKernel
      rw [max_eq_left he.le]
    rw [NeutralAtom.coulombKernel, hc, abs_of_nonneg (sub_nonneg.mpr (inv_anti₀ hn he.le))]
    have hi := inv_nonneg.mpr hε.le
    linarith
  · rw [Set.indicator_of_notMem (by simpa only [Metric.mem_ball, dist_zero_right] using he)]
    simp only [NeutralAtom.coulombKernel, cappedCoulombKernel, max_eq_right (le_of_not_gt he),
      sub_self, abs_zero, le_refl]

theorem cappedCoulombPotential_integrable {ε : ℝ} (hε : 0 < ε)
    {ρ : Position → ℝ} (hρ : Integrable ρ) (x : Position) :
    Integrable (fun y => cappedCoulombKernel ε (x - y) * ρ y) := by
  apply hρ.bdd_mul (c := ε⁻¹)
    ((cappedCoulombKernel_continuous hε).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun y => by
    change ‖cappedCoulombKernel ε (x - y)‖ ≤ ε⁻¹
    rw [Real.norm_of_nonneg (cappedCoulombKernel_nonnegative hε _)]
    exact cappedCoulombKernel_le hε _)

theorem cappedCoulombPotential_error {ε B : ℝ} (hε : 0 < ε)
    {ρ : Position → ℝ} (hρ : Integrable ρ) (hpos : ∀ x, 0 ≤ ρ x)
    (hbound : ∀ x, ρ x ≤ B) (x : Position) :
    |NeutralAtom.potentialOf ρ x - cappedCoulombPotential ε ρ x| ≤
      B * NeutralAtom.kernelBallMass ε := by
  have hi := (NeutralAtom.bounded_density_convolution NeutralAtom.measurable_coulombKernel
    NeutralAtom.coulombKernel_nonneg (NeutralAtom.coulombKernel_integrableOn_ball 1)
    (fun _ => NeutralAtom.coulombKernel_le_one) hρ hpos hbound x).1
  rw [NeutralAtom.potentialOf, cappedCoulombPotential,
    ← integral_sub hi (cappedCoulombPotential_integrable hε hρ x)]
  have hd := norm_integral_le_of_norm_le
    (f := fun y => NeutralAtom.coulombKernel (x - y) * ρ y -
      cappedCoulombKernel ε (x - y) * ρ y)
    ((NeutralAtom.translated_kernel_indicator_integrable x ε).const_mul B)
    (by
      filter_upwards [volume.ae_ne x] with y hy
      rw [← sub_mul, norm_mul, Real.norm_of_nonneg (hpos y), Real.norm_eq_abs]
      have hc := cappedCoulombKernel_difference hε (x - y) (sub_ne_zero.mpr hy.symm)
      have hs : (Metric.ball (0 : Position) ε).indicator NeutralAtom.coulombKernel (x - y) =
          (Metric.ball x ε).indicator (fun z => NeutralAtom.coulombKernel (x - z)) y := by
        rw [NeutralAtom.translated_kernel_indicator_eq]
      rw [hs] at hc
      have hp : 0 ≤ (Metric.ball x ε).indicator
          (fun z => NeutralAtom.coulombKernel (x - z)) y :=
        Set.indicator_nonneg (fun z _ => NeutralAtom.coulombKernel_nonneg (x - z)) y
      calc
        _ ≤ (Metric.ball x ε).indicator
            (fun z => NeutralAtom.coulombKernel (x - z)) y * B :=
          mul_le_mul hc (hbound y) (hpos y) hp
        _ = _ := mul_comm _ _)
  simpa only [Real.norm_eq_abs, integral_const_mul,
    NeutralAtom.translated_kernel_indicator_integral] using hd

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BinaryRoots
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


/-! Bounded binary-root search required by the appendix's perfect-power check.
The search uses only comparisons and powers with exponent at most the input
bit bound; no unbounded Nat.nthRoot primitive is used by the algorithm. -/
namespace ExactQuantumFactoring.Primality

lemma rootSearch_spec {m e : ℕ} (_he : 0 < e) (k guess : ℕ)
    (hlo : guess^e ≤ m) (hhi : m < (guess+2^k)^e) :
    (rootSearch m e k guess)^e ≤ m ∧ m < (rootSearch m e k guess+1)^e := by
  induction k generalizing guess with
  | zero => simpa only [rootSearch,pow_zero] using And.intro hlo hhi
  | succ k ih =>
    simp only [rootSearch]
    by_cases hnext : (guess+2^k)^e ≤ m
    · rw [ite_eq_left hnext]
      apply ih _ hnext
      have hh : guess+2^k+2^k=guess+2^(k+1) := by rw [pow_succ]; omega
      rw [hh]
      exact hhi
    · rw [ite_eq_right hnext]
      exact ih _ hlo (by omega)

lemma boundedRoot_spec {m e n : ℕ} (he : 0 < e) (hm : m < 2^n) :
    (boundedRoot m e n)^e ≤ m ∧ m < (boundedRoot m e n+1)^e := by
  apply rootSearch_spec he n 0
  · simp [Nat.ne_of_gt he]
  · simp only [zero_add]
    exact hm.trans_le (Nat.le_self_pow he.ne' (2^n))

end ExactQuantumFactoring.Primality


end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_SquareRootProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bitwise integer square-root search and its actual polynomial-time
Boolean-stack implementation. This supplies arithmetic for finite-precision
geometric constants and mediator amplitudes without a real square-root oracle. -/

namespace ContinuumCoulomb.SquareRootProgram
open ExactQuantumFactoring.BitStackProgram

/-- The returned integer brackets the true square root by adjacent integers. -/
theorem root_spec (m : ℕ) : root m ^ 2 ≤ m ∧ m < (root m + 1) ^ 2 := by
  apply ExactQuantumFactoring.Primality.boundedRoot_spec (by decide)
  simpa only [Nat.size_eq_bits_len] using Nat.lt_size_self m

end ContinuumCoulomb.SquareRootProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_DyadicRootProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A computed dyadic square root of a nonnegative rational, with strict
error below one unit in the requested binary precision. Precision is unary;
numerator, denominator, and result are binary. -/

namespace ContinuumCoulomb.DyadicRootProgram
open ExactQuantumFactoring.BitStackProgram

theorem value_error (b N F : ℕ) (hF : 0 < F) :
    0 ≤ Real.sqrt ((N : ℝ) / F) - (value b N F : ℝ) ∧
      Real.sqrt ((N : ℝ) / F) - (value b N F : ℝ) < 1 / (2 : ℝ) ^ b := by
  let p : ℕ := 2 ^ b
  let m : ℕ := N * p ^ 2 / F
  let r : ℕ := SquareRootProgram.root m
  have hp : (0 : ℝ) < p := by dsimp [p]; positivity
  have hFr : (0 : ℝ) < F := by exact_mod_cast hF
  have hlo : r ^ 2 * F ≤ N * p ^ 2 :=
    (Nat.mul_le_mul_right F (SquareRootProgram.root_spec m).1).trans (Nat.div_mul_le_self _ _)
  have hhi : N * p ^ 2 < (r + 1) ^ 2 * F :=
    (Nat.div_lt_iff_lt_mul hF).mp (SquareRootProgram.root_spec m).2
  have hlo' : (r : ℝ) ^ 2 * F ≤ (N : ℝ) * (p : ℝ) ^ 2 := by exact_mod_cast hlo
  have hhi' : (N : ℝ) * (p : ℝ) ^ 2 < ((r : ℝ) + 1) ^ 2 * F := by exact_mod_cast hhi
  have hrad : 0 ≤ (N : ℝ) / F := by positivity
  have hsquare : (Real.sqrt ((N : ℝ) / F) * p) ^ 2 * F = (N : ℝ) * (p : ℝ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hrad]
    field_simp [hFr.ne']
  have hs : 0 ≤ Real.sqrt ((N : ℝ) / F) * p := by positivity
  have hslo : (r : ℝ) ^ 2 ≤ (Real.sqrt ((N : ℝ) / F) * p) ^ 2 := by
    apply (mul_le_mul_iff_left₀ hFr).mp
    rw [hsquare]
    exact hlo'
  have hshi : (Real.sqrt ((N : ℝ) / F) * p) ^ 2 < ((r : ℝ) + 1) ^ 2 := by
    apply (mul_lt_mul_iff_left₀ hFr).mp
    rw [hsquare]
    exact hhi'
  have hl : (r : ℝ) ≤ Real.sqrt ((N : ℝ) / F) * p := by
    nlinarith only [hslo, hs, show 0 ≤ (r : ℝ) by positivity]
  have hu : Real.sqrt ((N : ℝ) / F) * p < (r : ℝ) + 1 := by
    nlinarith only [hshi, hs, show 0 ≤ (r : ℝ) by positivity]
  have hvalue : (value b N F : ℝ) = (r : ℝ) / p := by
    simp only [value, Rat.cast_div, Rat.cast_natCast, Rat.cast_pow, Rat.cast_ofNat, p, r, m,
      Nat.cast_pow, Nat.cast_ofNat]
  have hpcast : (p : ℝ) = (2 : ℝ) ^ b := by simp only [p, Nat.cast_pow, Nat.cast_ofNat]
  rw [hvalue, ← hpcast]
  constructor
  · exact sub_nonneg.mpr ((div_le_iff₀ hp).mpr hl)
  · apply (lt_div_iff₀ hp).mpr
    rw [sub_mul, div_mul_cancel₀ _ hp.ne']
    linarith

end ContinuumCoulomb.DyadicRootProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RationalSquareRoot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certified evaluation of square roots of nonnegative rational samples.
The same finite dyadic procedure serves the fixed Gaussian constants and
softened Coulomb distances. -/

namespace ContinuumCoulomb.RationalSquareRoot
open ExactQuantumFactoring.BitStackProgram

theorem value_error (b : ℕ) {q : ℚ} (hq : 0 ≤ q) :
    |(value (b, q) : ℝ) - Real.sqrt (q : ℝ)| ≤ (2 : ℝ)⁻¹ ^ b := by
  have hnum : (q.num.toNat : ℤ) = q.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq)
  have hnumq : (q.num.toNat : ℚ) = (q.num : ℚ) := by exact_mod_cast hnum
  have hrepr : (q.num.toNat : ℚ) / q.den = q := by rw [hnumq, Rat.num_div_den]
  have hre : (q.num.toNat : ℝ) / q.den = (q : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_natCast] using congrArg (fun x : ℚ => (x : ℝ)) hrepr
  have h := DyadicRootProgram.value_error b q.num.toNat q.den q.pos
  rw [hre] at h
  change |(DyadicRootProgram.value b q.num.toNat q.den : ℝ) - Real.sqrt (q : ℝ)| ≤ _
  rw [abs_sub_comm, abs_of_nonneg h.1]
  exact h.2.le.trans_eq (by simp only [one_div, inv_pow])

theorem sqrt_perturbation {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.sqrt a - Real.sqrt b| ≤ Real.sqrt |a - b| := by
  apply Real.abs_le_sqrt
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  by_cases hab : a ≤ b
  · have hs := Real.sqrt_le_sqrt hab
    have hm := mul_nonneg (Real.sqrt_nonneg a) (sub_nonneg.mpr hs)
    rw [abs_of_nonpos (sub_nonpos.mpr hab)]
    nlinarith
  · have hs := Real.sqrt_le_sqrt (le_of_not_ge hab)
    have hm := mul_nonneg (Real.sqrt_nonneg b) (sub_nonneg.mpr hs)
    rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hab))]
    nlinarith

end ContinuumCoulomb.RationalSquareRoot

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_CappedKernelProgram
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal rational approximation of the bounded three-dimensional
Coulomb kernel. Only a dyadic square root and rational arithmetic occur. -/

noncomputable section
namespace ContinuumCoulomb.CappedKernelProgram
open ExactQuantumFactoring.BitStackProgram

theorem normSquare_nonnegative (q : Triple) : 0 ≤ normSquare q := by
  unfold normSquare
  positivity

theorem position_norm_sq (q : Triple) : ‖position q‖ ^ 2 = (normSquare q : ℝ) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [position, normSquare, Fin.sum_univ_succ]
  ring

theorem position_norm (q : Triple) : ‖position q‖ = Real.sqrt (normSquare q : ℝ) := by
  rw [← position_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem approximation_error (x : Input) (hε : 0 < x.1.2) :
    |(approximate x : ℝ) - cappedCoulombKernel (x.1.2 : ℝ) (position x.2)| ≤
      ((x.1.2 : ℝ)⁻¹ ^ 2) * (2 : ℝ)⁻¹ ^ x.1.1 := by
  let a : ℝ := max (x.1.2 : ℝ) (RationalSquareRoot.value (x.1.1, normSquare x.2) : ℝ)
  let b : ℝ := max (x.1.2 : ℝ) ‖position x.2‖
  have hεr : (0 : ℝ) < x.1.2 := by exact_mod_cast hε
  have ha : 0 < a := hεr.trans_le (le_max_left _ _)
  have hb : 0 < b := hεr.trans_le (le_max_left _ _)
  have hroot := RationalSquareRoot.value_error x.1.1 (normSquare_nonnegative x.2)
  rw [← position_norm] at hroot
  have hdiff : |a - b| ≤ (2 : ℝ)⁻¹ ^ x.1.1 := by
    have h := abs_max_sub_max_le_abs
      (RationalSquareRoot.value (x.1.1, normSquare x.2) : ℝ) ‖position x.2‖ (x.1.2 : ℝ)
    rw [max_comm _ (x.1.2 : ℝ), max_comm _ (x.1.2 : ℝ)] at h
    exact h.trans hroot
  have hai : a⁻¹ ≤ (x.1.2 : ℝ)⁻¹ := inv_anti₀ hεr (le_max_left _ _)
  have hbi : b⁻¹ ≤ (x.1.2 : ℝ)⁻¹ := inv_anti₀ hεr (le_max_left _ _)
  have he : (approximate x : ℝ) - cappedCoulombKernel (x.1.2 : ℝ) (position x.2) =
      (b - a) * a⁻¹ * b⁻¹ := by
    have hcast : (approximate x : ℝ) = a⁻¹ := by
      simp only [approximate, Rat.cast_inv, Rat.cast_max, a]
    rw [hcast]
    change a⁻¹ - b⁻¹ = _
    field_simp [ha.ne', hb.ne']
  rw [he, abs_mul, abs_mul, abs_of_pos (inv_pos.mpr ha),
    abs_of_pos (inv_pos.mpr hb), abs_sub_comm b a]
  calc
    _ ≤ ((2 : ℝ)⁻¹ ^ x.1.1) * (x.1.2 : ℝ)⁻¹ * (x.1.2 : ℝ)⁻¹ := by gcongr
    _ = _ := by ring

end ContinuumCoulomb.CappedKernelProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RationalFieldDifferences
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate differences of a rational scalar sampler approximate the
actual gradient and Laplacian. The real extension below is only a proof
device; the numerical expressions evaluate the sampler at rational points. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb.RationalFieldDifferences
open CappedKernelProgram (Triple position)
open NeutralAtom (axis dirPartial coordinateLaplacian)

theorem extend_at (V : Position → ℝ) (sample : Triple → ℚ) (q : Triple) :
    extend V sample (position q) = (sample q:ℝ) := by
  rw [extend,dite_eq_left (show ∃ r, position r=position q from ⟨q,rfl⟩)]
  congr 1
  exact congrArg sample (position_injective
    (Classical.choose_spec (show ∃ r, position r=position q from ⟨q,rfl⟩)))

theorem extend_error (V : Position → ℝ) (sample : Triple → ℚ) {ε : ℝ}
    (hε : 0 ≤ ε) (he : ∀ q, |(sample q:ℝ)-V (position q)| ≤ ε) (x : Position) :
    |extend V sample x-V x| ≤ ε := by
  unfold extend
  split_ifs with h
  · have hs := he (Classical.choose h)
    simpa only [Classical.choose_spec h] using hs
  · simpa only [sub_self,abs_zero] using hε

theorem shift_position (q : Triple) (h : ℚ) (a : Fin 3) :
    position (shift q h a) = position q+(h:ℝ) • axis a := by
  ext b
  fin_cases a <;> fin_cases b <;> simp [position,shift,axis]

theorem first_error (V : Position → ℝ) (hV : ContDiff ℝ 6 V) (sample : Triple → ℚ)
    {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 ≤ ε) {h : ℚ} (hh : 0 < h)
    (hb : ∀ k ≤ 6, ∀ x, ‖iteratedFDeriv ℝ k V x‖ ≤ B)
    (he : ∀ q, |(sample q:ℝ)-V (position q)| ≤ ε) (q : Triple) (a : Fin 3) :
    |(first sample h q a:ℝ)-dirPartial V (axis a) (position q)| ≤ B*(h:ℝ)+2*ε/(h:ℝ) := by
  have hhR : (0:ℝ) < h := by exact_mod_cast hh
  have hd := MoserCoordinateDifferences.first_error V (extend V sample) hV hB hε hhR hb
    (extend_error V sample hε he) (position q) a
  rw [← shift_position,extend_at,extend_at] at hd
  simpa only [first,Rat.cast_div,Rat.cast_sub] using hd

theorem second_error (V : Position → ℝ) (hV : ContDiff ℝ 6 V) (sample : Triple → ℚ)
    {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 ≤ ε) {h : ℚ} (hh : 0 < h)
    (hb : ∀ k ≤ 6, ∀ x, ‖iteratedFDeriv ℝ k V x‖ ≤ B)
    (he : ∀ q, |(sample q:ℝ)-V (position q)| ≤ ε) (q : Triple) (a : Fin 3) :
    |(second sample h q a:ℝ)-dirPartial (dirPartial V (axis a)) (axis a) (position q)| ≤
      B*(h:ℝ)+4*ε/(h:ℝ)^2 := by
  have hhR : (0:ℝ) < h := by exact_mod_cast hh
  have hd := MoserCoordinateDifferences.second_error V (extend V sample) hV hB hhR hb
    (extend_error V sample hε he) (position q) a
  have hm : position q-(h:ℝ) • axis a = position (shift q (-h) a) := by
    rw [shift_position,Rat.cast_neg,neg_smul,sub_eq_add_neg]
  rw [← shift_position,hm,extend_at,extend_at,extend_at] at hd
  simpa only [second,Rat.cast_div,Rat.cast_add,Rat.cast_mul,Rat.cast_pow,Rat.cast_sub,Rat.cast_ofNat] using hd

theorem laplacian_error (V : Position → ℝ) (hV : ContDiff ℝ 6 V) (sample : Triple → ℚ)
    {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 ≤ ε) {h : ℚ} (hh : 0 < h)
    (hb : ∀ k ≤ 6, ∀ x, ‖iteratedFDeriv ℝ k V x‖ ≤ B)
    (he : ∀ q, |(sample q:ℝ)-V (position q)| ≤ ε) (q : Triple) :
    |(laplacian sample h q:ℝ)-coordinateLaplacian V (position q)| ≤
      3*(B*(h:ℝ)+4*ε/(h:ℝ)^2) := by
  rw [laplacian,Rat.cast_sum,NeutralAtom.coordinateLaplacian_eq_partials
    ((hV.of_le (by norm_num : (2:WithTop ℕ∞) ≤ 6)).contDiffAt),← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _a : Fin 3, (B*(h:ℝ)+4*ε/(h:ℝ)^2) :=
      Finset.sum_le_sum (fun a _ => second_error V hV sample hB hε hh hb he q a)
    _ = _ := by simp; ring

end ContinuumCoulomb.RationalFieldDifferences

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_MoserDifferenceBudget
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed polynomial precision parameters for coordinate differences of
the manufactured field. Both the spatial step and scalar accuracy are
chosen from its already proved uniform six-derivative bound. -/

noncomputable section
namespace ContinuumCoulomb.MoserDifferenceBudget

theorem guard_positive : 0 < guard := by unfold guard; omega

theorem guard_bound : manufacturedFieldDerivativeConstant ≤ (guard:ℝ) := by
  have h := Nat.le_ceil manufacturedFieldDerivativeConstant
  unfold guard
  push_cast
  linarith

theorem step_positive (P : ℕ) : 0 < step P := by
  have hg : (0:ℚ) < guard := by exact_mod_cast guard_positive
  unfold step
  positivity

theorem step_le_one (P : ℕ) : (step P:ℝ) ≤ 1 := by
  have hg : (1:ℝ) ≤ guard := by exact_mod_cast guard_positive
  have hp : (1:ℝ) ≤ (P:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) P]
  simp only [step,Rat.cast_inv,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast,Rat.cast_add,Rat.cast_one]
  apply (inv_le_one₀ (by positivity)).mpr
  nlinarith

theorem second_budget (P : ℕ) :
    (guard:ℝ)*(step P:ℝ)+4*((precision P:ℝ)+1)⁻¹/(step P:ℝ)^2 ≤
      (8*((P:ℝ)+1))⁻¹ := by
  let B : ℝ := guard
  let Q : ℝ := (P:ℝ)+1
  have hB : 0 < B := by dsimp [B]; exact_mod_cast guard_positive
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hs : (step P:ℝ) = (16*B*Q)⁻¹ := by
    simp only [step,Rat.cast_inv,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast,Rat.cast_add,Rat.cast_one,B,Q]
  have hp : (precision P:ℝ) = 16384*B^2*Q^3 := by
    simp only [precision,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,Nat.cast_add,Nat.cast_one,B,Q]
  have hbase : 0 < 16384*B^2*Q^3 :=
    mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hB)) (pow_pos hQ _)
  have he : ((precision P:ℝ)+1)⁻¹ ≤ (16384*B^2*Q^3)⁻¹ := by
    rw [hp]
    apply inv_anti₀ hbase
    linarith
  rw [hs]
  change B*(16*B*Q)⁻¹+4*((precision P:ℝ)+1)⁻¹/((16*B*Q)⁻¹)^2 ≤ (8*Q)⁻¹
  calc
    _ ≤ B*(16*B*Q)⁻¹+4*(16384*B^2*Q^3)⁻¹/((16*B*Q)⁻¹)^2 :=
      add_le_add le_rfl (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left he (by norm_num)) (sq_nonneg _))
    _ = _ := by
      field_simp [hB.ne',hQ.ne']
      norm_num

theorem first_budget (P : ℕ) :
    (guard:ℝ)*(step P:ℝ)+2*((precision P:ℝ)+1)⁻¹/(step P:ℝ) ≤
      (8*((P:ℝ)+1))⁻¹ := by
  have hs : (0:ℝ) < step P := by exact_mod_cast step_positive P
  have hs1 := step_le_one P
  have hcoeff : 2/(step P:ℝ) ≤ 4/(step P:ℝ)^2 := by
    apply (div_le_div_iff₀ hs (sq_pos_of_pos hs)).mpr
    have hh2 := mul_le_mul_of_nonneg_left hs1 hs.le
    nlinarith only [hh2,hs.le]
  have h := mul_le_mul_of_nonneg_right hcoeff
    (show 0 ≤ ((precision P:ℝ)+1)⁻¹ by positivity)
  have hnoise : 2*((precision P:ℝ)+1)⁻¹/(step P:ℝ) ≤
      4*((precision P:ℝ)+1)⁻¹/(step P:ℝ)^2 := by
    first | (convert h using 1 <;> ring) | exact (le_of_eq (by ring)).trans (h.trans (le_of_eq (by ring)))
  exact (add_le_add le_rfl hnoise).trans (second_budget P)

theorem laplacian_budget (P : ℕ) :
    3*((guard:ℝ)*(step P:ℝ)+4*((precision P:ℝ)+1)⁻¹/(step P:ℝ)^2) ≤
      ((P:ℝ)+1)⁻¹ := by
  have h := mul_le_mul_of_nonneg_left (second_budget P) (by norm_num : (0:ℝ) ≤ 3)
  apply h.trans
  rw [mul_inv]
  norm_num
  have hp : 0 ≤ ((P:ℝ)+1)⁻¹ := by positivity
  linarith

end ContinuumCoulomb.MoserDifferenceBudget

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_RationalQuadratureProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal tabulation and summation of rational quadrature samples.
The sample count is unary; bounds, spacing and evaluator data are encoded
as ordinary inputs to the machine. -/

namespace ContinuumCoulomb.RationalQuadratureProgram
open ExactQuantumFactoring.BitStackProgram
open scoped BigOperators

variable {E : Type}

theorem node_cast (a h : ℚ) (i : ℕ) :
    (node a h i : ℝ) = UniformQuadrature.node (a : ℝ) (h : ℝ) i := by
  simp [node, UniformQuadrature.node]

theorem value_cast (evaluate : E → ℚ → ℚ) (x : Input E) :
    (value evaluate x : ℝ) = UniformQuadrature.sampleSum (x.2.2.2 : ℝ) x.1
      (fun i => (sample evaluate x.2 i : ℝ)) := by
  simp [value, UniformQuadrature.sampleSum]

theorem error (evaluate : E → ℚ → ℚ) (x : Input E) (f : ℝ → ℝ) {L ε : ℝ}
    (hh : 0 ≤ (x.2.2.2 : ℝ)) (hL : 0 ≤ L) (hf : Continuous f)
    (hLip : ∀ u ∈ Set.Icc (x.2.2.1 : ℝ) (node x.2.2.1 x.2.2.2 x.1 : ℝ),
      ∀ v ∈ Set.Icc (x.2.2.1 : ℝ) (node x.2.2.1 x.2.2.2 x.1 : ℝ),
      |f u - f v| ≤ L * |u - v|)
    (heval : ∀ i < x.1, |(sample evaluate x.2 i : ℝ) -
      f (node x.2.2.1 x.2.2.2 i : ℝ)| ≤ ε) :
    |(value evaluate x : ℝ) - ∫ t in (x.2.2.1 : ℝ)..(node x.2.2.1 x.2.2.2 x.1 : ℝ), f t| ≤
      (x.1 : ℝ) * (L * (x.2.2.2 : ℝ) ^ 2 + (x.2.2.2 : ℝ) * ε) := by
  rw [value_cast, node_cast]
  apply UniformQuadrature.samples_error f _ _ _ _ hh hL hf
  · simpa only [node_cast] using hLip
  · simpa only [node_cast] using heval

end ContinuumCoulomb.RationalQuadratureProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_PiProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A rational polynomial-time approximation to π from the integral of
`4 / (1+x²)` on `[0,1]`. The unary sample count gives absolute error `8/N`.
This supplies the normalizing constant in the heat-kernel evaluator. -/

namespace ContinuumCoulomb.PiProgram
open ExactQuantumFactoring.BitStackProgram
open RationalQuadratureProgram

theorem reciprocal_continuous : Continuous (fun x : ℝ => (1 + x ^ 2)⁻¹) :=
  ((continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).add
    (continuous_id.pow 2)).inv₀ (by intro x; change (1 : ℝ) + x ^ 2 ≠ 0; positivity)

theorem reciprocal_lipschitz (x y : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |(1 + x ^ 2)⁻¹ - (1 + y ^ 2)⁻¹| ≤ 2 * |x - y| := by
  have hx0 : (1 : ℝ) + x ^ 2 ≠ 0 := by positivity
  have hy0 : (1 : ℝ) + y ^ 2 ≠ 0 := by positivity
  have hid : (1 + x ^ 2)⁻¹ - (1 + y ^ 2)⁻¹ =
      ((y - x) * (y + x)) / ((1 + x ^ 2) * (1 + y ^ 2)) := by
    field_simp
    ring
  have hd : 1 ≤ (1 + x ^ 2) * (1 + y ^ 2) := by
    nlinarith [sq_nonneg x, sq_nonneg y, mul_nonneg (sq_nonneg x) (sq_nonneg y)]
  rw [hid, abs_div, abs_mul, abs_of_nonneg (show 0 ≤ y + x by linarith [hx.1, hy.1]),
    abs_of_pos (show 0 < (1 + x ^ 2) * (1 + y ^ 2) by linarith), abs_sub_comm y x]
  apply (div_le_iff₀ (show 0 < (1 + x ^ 2) * (1 + y ^ 2) by linarith)).mpr
  have hnum := mul_le_mul_of_nonneg_left (show y + x ≤ (2 : ℝ) by linarith [hx.2, hy.2])
    (abs_nonneg (x - y))
  have hden := mul_le_mul_of_nonneg_left hd (show 0 ≤ 2 * |x - y| by positivity)
  nlinarith

theorem endpoint (N : ℕ) (hN : 0 < N) : node (0 : ℚ) (N : ℚ)⁻¹ N = 1 := by
  have hn : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  simp [node, hn]

theorem error (N : ℕ) (hN : 0 < N) :
    |(approximate N : ℝ) - Real.pi| ≤ 8 / (N : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have h := RationalQuadratureProgram.error evaluate (input N)
    (fun x : ℝ => (1 + x ^ 2)⁻¹) (L := 2) (ε := 0)
    (by dsimp [input]; positivity) (by norm_num) reciprocal_continuous
    (by
      intro x hx y hy
      simp only [input, endpoint N hN, Rat.cast_zero, Rat.cast_one] at hx hy
      exact reciprocal_lipschitz x y hx hy)
    (by
      intro i hi
      simp [sample, evaluate, input])
  have hi : (∫ x : ℝ in (0 : ℝ)..1, (1 + x ^ 2)⁻¹) = Real.pi / 4 := by
    rw [integral_inv_one_add_sq, Real.arctan_one, Real.arctan_zero, sub_zero]
  simp only [input, endpoint N hN, Rat.cast_zero, Rat.cast_one, Rat.cast_inv, Rat.cast_natCast,
    mul_zero, add_zero, hi] at h
  have heq : (approximate N : ℝ) - Real.pi =
      4 * ((value evaluate (input N) : ℝ) - Real.pi / 4) := by
    simp only [approximate, Rat.cast_mul, Rat.cast_ofNat]
    ring
  rw [heq, abs_mul]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 4)
  have hs : 4 * ((N : ℝ) * (2 * (N : ℝ)⁻¹ ^ 2)) = 8 / (N : ℝ) := by
    field_simp
    ring
  exact hm.trans_eq hs

end ContinuumCoulomb.PiProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_MoserVelocityNumerics
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Stable algebraic evaluation of the actual Moser velocity. The
denominator is clamped below by the fixed positive density; this clamp
does not affect the exact field and cannot increase denominator error. -/

noncomputable section
namespace ContinuumCoulomb.MoserVelocityNumerics
open NeutralAtom (dirPartial axis coordinateLaplacian)

theorem component_formula (rho : ℝ) (V : Position → ℝ) (t : ℝ) (x : Position) (a : Fin 3) :
    moserVelocity rho V t x a =
      -dirPartial V (axis a) x/(4*Real.pi*rho+t*coordinateLaplacian V x) := by
  have hden : 4*Real.pi*homotopyDensity rho V t x =
      4*Real.pi*rho+t*coordinateLaplacian V x := by
    unfold homotopyDensity manufacturedCharge
    field_simp [Real.pi_ne_zero]
  change -dirPartial V (axis a) x/(4*Real.pi*homotopyDensity rho V t x) = _
  rw [hden]

theorem denominator_lower {rho : ℝ} (hrho : 0 ≤ rho) (V : Position → ℝ)
    (hcharge : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) (x : Position) :
    rho ≤ 4*Real.pi*rho+t*coordinateLaplacian V x := by
  have h := mul_le_mul_of_nonneg_left (homotopyDensity_bounds V hcharge ht.1 ht.2 x).1
    (show (0:ℝ) ≤ 4*Real.pi by positivity)
  have heq : 4*Real.pi*homotopyDensity rho V t x =
      4*Real.pi*rho+t*coordinateLaplacian V x := by
    unfold homotopyDensity manufacturedCharge
    field_simp [Real.pi_ne_zero]
  rw [heq] at h
  have hp : rho ≤ 2*Real.pi*rho :=
    le_mul_of_one_le_left hrho (by linarith [Real.pi_gt_three])
  exact hp.trans (by convert h using 1; ring)

theorem clamp_error {rho q d ε : ℝ} (hd : rho ≤ d) (hq : |q-d| ≤ ε) :
    |max rho q-d| ≤ ε := by
  by_cases h : rho ≤ q
  · simpa only [max_eq_right h] using hq
  · rw [max_eq_left (le_of_not_ge h),abs_of_nonpos (sub_nonpos.mpr hd)]
    have hl := (abs_le.mp hq).1
    linarith

theorem quotient_error {g g' d d' B ε η : ℝ}
    (hd : 1 ≤ d) (hd' : 1 ≤ d') (hg : |g| ≤ B)
    (hgn : |g'-g| ≤ ε) (hden : |d'-d| ≤ η) :
    |(-g')/d'-(-g)/d| ≤ ε+B*η := by
  have hdp : 0 < d := by linarith
  have hdp' : 0 < d' := by linarith
  have hi : d⁻¹ ≤ 1 := (inv_le_one₀ hdp).mpr hd
  have hi' : d'⁻¹ ≤ 1 := (inv_le_one₀ hdp').mpr hd'
  have hB : 0 ≤ B := (abs_nonneg _).trans hg
  have hη : 0 ≤ η := (abs_nonneg _).trans hden
  have hε : 0 ≤ ε := (abs_nonneg _).trans hgn
  have heq : (-g')/d'-(-g)/d =
      -(g'-g)*d'⁻¹+g*(d'-d)*d'⁻¹*d⁻¹ := by
    field_simp [hdp.ne',hdp'.ne']
    ring
  rw [heq]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_neg,abs_mul,abs_mul,abs_mul,
    abs_of_pos (inv_pos.mpr hdp),abs_of_pos (inv_pos.mpr hdp')]
  have hfirst : |g'-g| * d'⁻¹ ≤ ε := by
    exact (mul_le_mul hgn hi' (inv_nonneg.mpr hdp'.le) hε).trans_eq (mul_one _)
  have hsecond : |g| * |d'-d| * d'⁻¹*d⁻¹ ≤ B*η := by
    calc
      _ ≤ B*η*1*1 := by gcongr
      _ = _ := by ring
  exact add_le_add hfirst hsecond

theorem component_error (rho : ℝ) (hrho : 1 ≤ rho)
    (V : Position → ℝ) (hcharge : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) (x : Position) (a : Fin 3)
    (g lap pi' : ℝ) {B ε : ℝ}
    (hB : |dirPartial V (axis a) x| ≤ B)
    (hg : |g-dirPartial V (axis a) x| ≤ ε)
    (hlap : |lap-coordinateLaplacian V x| ≤ ε)
    (hpi : |pi'-Real.pi| ≤ ε) :
    |(-g)/max rho (4*pi'*rho+t*lap)-moserVelocity rho V t x a| ≤
      (1+B*(4*rho+1))*ε := by
  have hrho0 : 0 ≤ rho := by linarith
  have hε : 0 ≤ ε := (abs_nonneg _).trans hg
  have hraw : |(4*pi'*rho+t*lap)-(4*Real.pi*rho+t*coordinateLaplacian V x)| ≤
      (4*rho+1)*ε := by
    have hid : (4*pi'*rho+t*lap)-(4*Real.pi*rho+t*coordinateLaplacian V x) =
        (4*rho)*(pi'-Real.pi)+t*(lap-coordinateLaplacian V x) := by ring
    rw [hid]
    apply (abs_add_le _ _).trans
    simp only [abs_mul,abs_of_nonneg hrho0,abs_of_nonneg ht.1,
      abs_of_pos (by norm_num : (0:ℝ)<4)]
    have hfirst := mul_le_mul_of_nonneg_left hpi (show 0 ≤ 4*rho by positivity)
    have hsecond : t*|lap-coordinateLaplacian V x| ≤ ε := by
      exact (mul_le_mul ht.2 hlap (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    nlinarith
  have hd := denominator_lower hrho0 V hcharge ht x
  rw [component_formula]
  have he := quotient_error (hrho.trans hd) (hrho.trans (le_max_left _ _)) hB hg
    (clamp_error hd hraw)
  exact he.trans_eq (by ring)

end ContinuumCoulomb.MoserVelocityNumerics

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabSections
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

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CappedCoulombMass
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact three-dimensional near-pole mass makes the cap error
quadratic in its rational radius. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem coulomb_kernelBallMass {ε : ℝ} (hε : 0 ≤ ε) :
    NeutralAtom.kernelBallMass ε = 2 * Real.pi * ε ^ 2 := by
  unfold NeutralAtom.kernelBallMass
  rw [← integral_indicator measurableSet_ball]
  have he : (Metric.ball (0 : Position) ε).indicator NeutralAtom.coulombKernel =
      (fun x : Position => (Set.Iio ε).indicator (fun r : ℝ => r⁻¹) ‖x‖) := by
    funext x
    by_cases hx : ‖x‖ < ε
    · simp [NeutralAtom.coulombKernel, Metric.mem_ball, dist_zero_right, hx]
    · simp [Metric.mem_ball, dist_zero_right, hx]
  rw [he, integral_fun_norm_addHaar volume]
  have hi : (∫ r in Set.Ioi (0 : ℝ), r ^ (Module.finrank ℝ Position - 1) •
      (Set.Iio ε).indicator (fun t : ℝ => t⁻¹) r) = ε ^ 2 / 2 := by
    simp only [finrank_euclideanSpace_fin, smul_eq_mul]
    norm_num
    have hm : (fun r : ℝ => r ^ 2 * (Set.Iio ε).indicator (fun t : ℝ => t⁻¹) r) =
        (Set.Iio ε).indicator (fun r : ℝ => r) := by
      funext r
      by_cases hr : r < ε
      · simp only [Set.indicator_apply, Set.mem_Iio, hr, ite_true, if_true]
        by_cases hzero : r = 0
        · simp [hzero]
        · field_simp [hzero]
      · simp [hr]
    rw [hm, setIntegral_indicator measurableSet_Iio]
    have hinter : Set.Ioi (0 : ℝ) ∩ Set.Iio ε = Set.Ioo 0 ε := by ext r; rfl
    rw [hinter, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hε, integral_id]
    ring
  rw [hi]
  simp only [Measure.real, EuclideanSpace.volume_ball_fin_three, ENNReal.ofReal_one, one_pow,
    one_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi * 4 / 3), smul_eq_mul,
    nsmul_eq_mul]
  norm_num [Position, finrank_euclideanSpace_fin]
  ring

theorem cappedCoulombPotential_error_explicit {ε B : ℝ} (hε : 0 < ε)
    {ρ : Position → ℝ} (hρ : Integrable ρ) (hpos : ∀ x, 0 ≤ ρ x)
    (hbound : ∀ x, ρ x ≤ B) (x : Position) :
    |NeutralAtom.potentialOf ρ x - cappedCoulombPotential ε ρ x| ≤
      2 * Real.pi * B * ε ^ 2 := by
  have h := cappedCoulombPotential_error hε hρ hpos hbound x
  rw [coulomb_kernelBallMass hε.le] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CappedCoulombTruncation
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-box truncation of the bounded Coulomb integral. The bound is
uniform in the displacement and uses only the discarded density masses. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem cappedPairIntegrand_integrable {ε : ℝ} (hε : 0 < ε) (shift : Position)
    {f g : Position → ℝ} (hf : Integrable f) (hg : Integrable g) :
    Integrable (cappedPairIntegrand ε shift f g) := by
  have hp : Integrable (fun p : Position × Position => f p.1 * g p.2) := by
    simpa only [Measure.volume_eq_prod] using hf.mul_prod hg
  unfold cappedPairIntegrand
  apply hp.mul_bdd (c := ε⁻¹)
    (((cappedCoulombKernel_continuous hε).comp
      ((continuous_fst.sub continuous_snd).sub continuous_const)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun p => by
    change ‖cappedCoulombKernel ε (p.1 - p.2 - shift)‖ ≤ ε⁻¹
    rw [Real.norm_of_nonneg (cappedCoulombKernel_nonnegative hε _)]
    exact cappedCoulombKernel_le hε _)

theorem cappedPair_truncation_error {ε : ℝ} (hε : 0 < ε) (shift : Position)
    {f g : Position → ℝ} (hf : Integrable f) (hg : Integrable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ y, 0 ≤ g y)
    {S T : Set Position} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    |(∫ p, cappedPairIntegrand ε shift f g p) -
      ∫ p in S ×ˢ T, cappedPairIntegrand ε shift f g p| ≤
      ε⁻¹ * ((∫ x in Sᶜ, f x) * (∫ y, g y) +
        (∫ x, f x) * (∫ y in Tᶜ, g y)) := by
  let F := cappedPairIntegrand ε shift f g
  let M : Position × Position → ℝ := fun p => ε⁻¹ *
    (Sᶜ.indicator f p.1 * g p.2 + f p.1 * Tᶜ.indicator g p.2)
  have hFi : Integrable F := cappedPairIntegrand_integrable hε shift hf hg
  have hSi := hf.indicator hS.compl
  have hTi := hg.indicator hT.compl
  have hfirst : Integrable (fun p : Position × Position => Sᶜ.indicator f p.1 * g p.2) := by
    simpa only [Measure.volume_eq_prod] using hSi.mul_prod hg
  have hsecond : Integrable (fun p : Position × Position => f p.1 * Tᶜ.indicator g p.2) := by
    simpa only [Measure.volume_eq_prod] using hf.mul_prod hTi
  have hMi : Integrable M := by
    simpa only [M, Pi.add_apply] using (hfirst.add hsecond).const_mul ε⁻¹
  have hpt (p : Position × Position) :
      ‖F p - (S ×ˢ T).indicator F p‖ ≤ M p := by
    have hF0 : 0 ≤ F p := mul_nonneg (mul_nonneg (hf0 _) (hg0 _))
      (cappedCoulombKernel_nonnegative hε _)
    have hFbound : F p ≤ ε⁻¹ * (f p.1 * g p.2) := by
      unfold F cappedPairIntegrand
      calc
        _ ≤ f p.1 * g p.2 * ε⁻¹ := mul_le_mul_of_nonneg_left
          (cappedCoulombKernel_le hε _) (mul_nonneg (hf0 _) (hg0 _))
        _ = _ := by ring
    have hM0 : 0 ≤ M p := mul_nonneg (inv_nonneg.mpr hε.le)
      (add_nonneg
        (mul_nonneg (Set.indicator_nonneg (fun x _ => hf0 x) _) (hg0 _))
        (mul_nonneg (hf0 _) (Set.indicator_nonneg (fun y _ => hg0 y) _)))
    by_cases hs : p.1 ∈ S <;> by_cases ht : p.2 ∈ T
    · rw [Set.indicator_of_mem (show p ∈ S ×ˢ T from ⟨hs, ht⟩), sub_self, norm_zero]
      exact hM0
    · have hp : p ∉ S ×ˢ T := by simp [ht]
      rw [Set.indicator_of_notMem hp, sub_zero, Real.norm_of_nonneg hF0]
      simpa only [M, Set.indicator_of_notMem (show p.1 ∉ Sᶜ by simpa using hs),
        Set.indicator_of_mem (show p.2 ∈ Tᶜ from ht), zero_mul, zero_add] using hFbound
    · have hp : p ∉ S ×ˢ T := by simp [hs]
      rw [Set.indicator_of_notMem hp, sub_zero, Real.norm_of_nonneg hF0]
      simpa only [M, Set.indicator_of_mem (show p.1 ∈ Sᶜ from hs),
        Set.indicator_of_notMem (show p.2 ∉ Tᶜ by simpa using ht), mul_zero, add_zero] using hFbound
    · have hp : p ∉ S ×ˢ T := by simp [hs]
      rw [Set.indicator_of_notMem hp, sub_zero, Real.norm_of_nonneg hF0]
      dsimp only [M]
      rw [Set.indicator_of_mem (show p.1 ∈ Sᶜ from hs),
        Set.indicator_of_mem (show p.2 ∈ Tᶜ from ht)]
      have hz := mul_nonneg (inv_nonneg.mpr hε.le) (mul_nonneg (hf0 p.1) (hg0 p.2))
      linarith
  rw [← integral_indicator (hS.prod hT), ← integral_sub hFi (hFi.indicator (hS.prod hT))]
  have h := norm_integral_le_of_norm_le
    (f := fun p => F p - (S ×ˢ T).indicator F p) hMi (Filter.Eventually.of_forall hpt)
  rw [Real.norm_eq_abs] at h
  apply h.trans_eq
  simp only [M, integral_const_mul]
  rw [integral_add hfirst hsecond, Measure.volume_eq_prod, integral_prod_mul, integral_prod_mul,
    integral_indicator hS.compl, integral_indicator hT.compl]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_HeatKernelModulus
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative bounds for the scalar heat-resolvent kernel away from
time zero. Every constant is elementary in the cutoff and radius. -/

noncomputable section
namespace ContinuumCoulomb.HeatKernelModulus

theorem kernel_eq_heat (t : ℝ) (r : PlanarPosition) :
    kernel t (‖r‖ ^ 2) = Real.exp (-t) * planarHeatKernel t r := by
  rw [kernel, exponent, sub_eq_add_neg, Real.exp_add, planarHeatKernel, neg_div]
  ring

theorem exp_nonpositive_lipschitz {x y : ℝ} (hx : x ≤ 0) (hy : y ≤ 0) :
    |Real.exp x - Real.exp y| ≤ |x - y| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := Real.exp) (f' := Real.exp) (s := Set.Iic (0 : ℝ)) (C := 1)
    (fun z _ => (Real.hasDerivAt_exp z).hasDerivWithinAt)
    (fun z hz => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos z)]
      exact Real.exp_le_one_iff.mpr hz)
    (convex_Iic (0 : ℝ)) hy hx
  simpa only [Real.norm_eq_abs, one_mul] using h

theorem reciprocal_lipschitz {η t s : ℝ} (hη : 0 < η) (ht : η ≤ t) (hs : η ≤ s) :
    |t⁻¹ - s⁻¹| ≤ |t - s| / η ^ 2 := by
  have ht0 : 0 < t := hη.trans_le ht
  have hs0 : 0 < s := hη.trans_le hs
  have hid : t⁻¹ - s⁻¹ = (s - t) / (t * s) := by field_simp
  rw [hid, abs_div, abs_of_pos (mul_pos ht0 hs0), abs_sub_comm s t]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
    (by nlinarith [mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hs)])

theorem exponent_nonpositive {t A : ℝ} (ht : 0 < t) (hA : 0 ≤ A) :
    exponent t A ≤ 0 := by
  have h := div_nonneg hA (show 0 ≤ 4 * t by positivity)
  dsimp only [exponent]
  linarith

theorem exponent_time_lipschitz {η t s A : ℝ}
    (hη : 0 < η) (ht : η ≤ t) (hs : η ≤ s) (hA : 0 ≤ A) :
    |exponent t A - exponent s A| ≤ (1 + A / (4 * η ^ 2)) * |t - s| := by
  have hid : exponent t A - exponent s A =
      -(t - s) - (A / 4) * (t⁻¹ - s⁻¹) := by unfold exponent; ring
  rw [hid]
  calc
    _ ≤ |-(t - s)| + |A / 4 * (t⁻¹ - s⁻¹)| := abs_sub _ _
    _ = |t - s| + A / 4 * |t⁻¹ - s⁻¹| := by
      rw [abs_neg, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ A / 4)]
    _ ≤ |t - s| + A / 4 * (|t - s| / η ^ 2) := by
      gcongr
      exact reciprocal_lipschitz hη ht hs
    _ = _ := by ring

theorem kernel_nonnegative {t A : ℝ} (ht : 0 < t) : 0 ≤ kernel t A := by
  unfold kernel
  positivity

theorem kernel_le_inverse {η t A : ℝ} (hη : 0 < η) (ht : η ≤ t) (hA : 0 ≤ A) :
    kernel t A ≤ η⁻¹ := by
  have ht0 : 0 < t := hη.trans_le ht
  have he : Real.exp (exponent t A) ≤ 1 :=
    Real.exp_le_one_iff.mpr (exponent_nonpositive ht0 hA)
  have hp : (1 : ℝ) ≤ 4 * Real.pi := by linarith [Real.two_le_pi]
  calc
    kernel t A ≤ 1 / (4 * Real.pi * t) := div_le_div_of_nonneg_right he (by positivity)
    _ ≤ 1 / η := div_le_div_of_nonneg_left (by norm_num) hη
      (by nlinarith [mul_le_mul_of_nonneg_right hp ht0.le])
    _ = _ := one_div _

theorem kernel_space_lipschitz {η t A B : ℝ}
    (hη : 0 < η) (ht : η ≤ t) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    |kernel t A - kernel t B| ≤ |A - B| / η ^ 2 := by
  have ht0 : 0 < t := hη.trans_le ht
  have hq := exp_nonpositive_lipschitz (exponent_nonpositive ht0 hA)
    (exponent_nonpositive ht0 hB)
  have he : exponent t A - exponent t B = -(A - B) / (4 * t) := by
    unfold exponent
    ring
  rw [he, abs_div, abs_neg, abs_of_pos (show 0 < 4 * t by positivity)] at hq
  have hd : 0 < 4 * Real.pi * t := by positivity
  have hp : (1 : ℝ) ≤ 4 * Real.pi := by linarith [Real.two_le_pi]
  have hden : η ^ 2 ≤ (4 * t) * (4 * Real.pi * t) := by
    have ht1 : η ^ 2 ≤ t ^ 2 := (sq_le_sq₀ hη.le ht0.le).mpr ht
    have hm := mul_le_mul_of_nonneg_right hp (show 0 ≤ 4 * t ^ 2 by positivity)
    nlinarith
  calc
    |kernel t A - kernel t B| =
        |Real.exp (exponent t A) - Real.exp (exponent t B)| / (4 * Real.pi * t) := by
      rw [kernel, kernel, ← sub_div, abs_div, abs_of_pos hd]
    _ ≤ (|A - B| / (4 * t)) / (4 * Real.pi * t) :=
      div_le_div_of_nonneg_right hq hd.le
    _ = |A - B| / ((4 * t) * (4 * Real.pi * t)) := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hden

theorem kernel_time_lipschitz {η t s A : ℝ}
    (hη : 0 < η) (ht : η ≤ t) (hs : η ≤ s) (hA : 0 ≤ A) :
    |kernel t A - kernel s A| ≤
      (η⁻¹ ^ 2 + η⁻¹ * (1 + A / (4 * η ^ 2))) * |t - s| := by
  have ht0 : 0 < t := hη.trans_le ht
  have hs0 : 0 < s := hη.trans_le hs
  have hqt := exponent_nonpositive ht0 hA
  have hqs := exponent_nonpositive hs0 hA
  have hEt : Real.exp (exponent t A) ≤ 1 := Real.exp_le_one_iff.mpr hqt
  have he := (exp_nonpositive_lipschitz hqt hqs).trans (exponent_time_lipschitz hη ht hs hA)
  have hi := reciprocal_lipschitz hη ht hs
  have hsInv : s⁻¹ ≤ η⁻¹ := inv_anti₀ hη hs
  have hprod : |t⁻¹ * Real.exp (exponent t A) - s⁻¹ * Real.exp (exponent s A)| ≤
      (η⁻¹ ^ 2 + η⁻¹ * (1 + A / (4 * η ^ 2))) * |t - s| := by
    have hid : t⁻¹ * Real.exp (exponent t A) - s⁻¹ * Real.exp (exponent s A) =
        (t⁻¹ - s⁻¹) * Real.exp (exponent t A) +
        s⁻¹ * (Real.exp (exponent t A) - Real.exp (exponent s A)) := by ring
    rw [hid]
    calc
      _ ≤ |(t⁻¹ - s⁻¹) * Real.exp (exponent t A)| +
          |s⁻¹ * (Real.exp (exponent t A) - Real.exp (exponent s A))| := abs_add_le _ _
      _ = |t⁻¹ - s⁻¹| * Real.exp (exponent t A) +
          s⁻¹ * |Real.exp (exponent t A) - Real.exp (exponent s A)| := by
        rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (inv_pos.mpr hs0)]
      _ ≤ |t - s| / η ^ 2 + η⁻¹ * ((1 + A / (4 * η ^ 2)) * |t - s|) := by
        apply add_le_add
        · exact (mul_le_of_le_one_right (abs_nonneg _) hEt).trans hi
        · exact mul_le_mul hsInv he (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hc : 0 ≤ (4 * Real.pi)⁻¹ := by positivity
  have hc1 : (4 * Real.pi)⁻¹ ≤ 1 := by
    apply (inv_le_one₀ (by positivity)).mpr
    linarith [Real.two_le_pi]
  have hid : kernel t A - kernel s A = (4 * Real.pi)⁻¹ *
      (t⁻¹ * Real.exp (exponent t A) - s⁻¹ * Real.exp (exponent s A)) := by
    unfold kernel
    ring
  rw [hid, abs_mul, abs_of_nonneg hc]
  exact (mul_le_of_le_one_left (abs_nonneg _) hc1).trans hprod

end ContinuumCoulomb.HeatKernelModulus

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCoulombNumerics
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual six-coordinate bounded integrand for Coulomb quadrature,
with an explicit error to the original full singular coefficient. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem localizedCappedIntegrand_integrable {freq ε : ℝ} (hfreq : 0 < freq) (hε : 0 < ε)
    (u v : PlanarPosition) : Integrable (localizedCappedIntegrand freq ε u v) := by
  have hp : Integrable (fun p : Position × Position =>
      localizedDensity freq u p.1 * localizedDensity freq v p.2) := by
    simpa only [Measure.volume_eq_prod] using
      (localizedDensity_integrable hfreq u).mul_prod (localizedDensity_integrable hfreq v)
  have hk : Continuous (fun p : Position × Position => cappedCoulombKernel ε (p.1 - p.2)) :=
    (cappedCoulombKernel_continuous hε).comp (continuous_fst.sub continuous_snd)
  have h := hp.mul_bdd (c := ε⁻¹) hk.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p => by
      rw [Real.norm_of_nonneg (cappedCoulombKernel_nonnegative hε _)]
      exact cappedCoulombKernel_le hε _))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  unfold localizedCappedIntegrand
  ring

theorem localizedCappedCoulombCoeff_nested {freq ε : ℝ} (hfreq : 0 < freq) (hε : 0 < ε)
    (u v : PlanarPosition) :
    localizedCappedCoulombCoeff freq ε u v =
      ∫ x, localizedDensity freq u x * cappedCoulombPotential ε (localizedDensity freq v) x := by
  unfold localizedCappedCoulombCoeff
  rw [Measure.volume_eq_prod, integral_prod _
    (by simpa only [Measure.volume_eq_prod] using localizedCappedIntegrand_integrable hfreq hε u v)]
  simp only [localizedCappedIntegrand, integral_const_mul, cappedCoulombPotential]

theorem localizedCappedCoulombCoeff_error {freq ε : ℝ} (hfreq : 0 < freq) (hε : 0 < ε)
    (u v : PlanarPosition) :
    |localizedCoulombCoeff freq u v - localizedCappedCoulombCoeff freq ε u v| ≤
      2 * Real.pi * localizedAmplitudeBound freq ^ 2 * ε ^ 2 := by
  have hic : Integrable (fun x => localizedDensity freq u x *
      cappedCoulombPotential ε (localizedDensity freq v) x) := by
    have h := (localizedCappedIntegrand_integrable hfreq hε u v).integral_prod_left
    simpa only [localizedCappedIntegrand, integral_const_mul, cappedCoulombPotential] using h
  rw [localizedCappedCoulombCoeff_nested hfreq hε, localizedCoulombCoeff,
    ← integral_sub (localizedCoulombCoeff_integrable hfreq u v) hic]
  have h := norm_integral_le_of_norm_le
    (f := fun x => localizedDensity freq u x * NeutralAtom.potentialOf (localizedDensity freq v) x -
      localizedDensity freq u x * cappedCoulombPotential ε (localizedDensity freq v) x)
    ((localizedDensity_integrable hfreq u).mul_const
      (2 * Real.pi * localizedAmplitudeBound freq ^ 2 * ε ^ 2))
    (Filter.Eventually.of_forall (fun x => by
      rw [← mul_sub, norm_mul, Real.norm_of_nonneg (localizedDensity_nonnegative freq u x),
        Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        (cappedCoulombPotential_error_explicit hε (localizedDensity_integrable hfreq v)
          (localizedDensity_nonnegative freq v) (localizedDensity_bound hfreq v) x)
        (localizedDensity_nonnegative freq u x)))
  simpa only [Real.norm_eq_abs, integral_mul_const, localizedDensity_mass hfreq u, one_mul] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedDensityMoment
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed finite second moment of the actual localized probability density.
It supplies a polynomial finite-box truncation radius, uniformly in the
relative displacement appearing in a direct Coulomb coefficient. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem quadratic_exponential_bound {t : ℝ} (ht : 0 ≤ t) :
    t ^ 2 * Real.exp (-(1 / 2 : ℝ) * t) ≤ 343 := by
  have h := exponential_inverse_cubic_bound (by norm_num : (0 : ℝ) < 1 / 2) ht
  norm_num at h
  have hp : 0 < (1 + t) ^ 3 := by positivity
  have hm := (le_div_iff₀ hp).mp h
  have hpoly : t ^ 2 ≤ (1 + t) ^ 3 := by
    nlinarith [mul_nonneg ht (sq_nonneg t), sq_nonneg t]
  calc
    _ = Real.exp (-(1 / 2 : ℝ) * t) * t ^ 2 := mul_comm _ _
    _ ≤ Real.exp (-(1 / 2 : ℝ) * t) * (1 + t) ^ 3 :=
      mul_le_mul_of_nonneg_left hpoly (Real.exp_pos _).le
    _ ≤ 343 := by simpa only [neg_mul] using hm

theorem planarResolventMode_second_moment_integrable :
    Integrable (fun r : PlanarPosition => ‖r‖ ^ 2 * planarResolventMode r ^ 2) := by
  let C := planarExponentialConstant (1 / 2) ^ 2 * 343
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply ((planar_exp_norm_integrable (by norm_num : (0 : ℝ) < 1 / 2)).const_mul C).mono'
    ((continuous_norm.pow 2).mul (planarResolventMode_C7.continuous.pow 2)).aestronglyMeasurable
  filter_upwards [] with r
  change ‖‖r‖ ^ 2 * planarResolventMode r ^ 2‖ ≤ C * Real.exp (-(1 / 2 : ℝ) * ‖r‖)
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  have hmode := pow_le_pow_left₀ (planarResolventMode_positive r).le
    (planarResolventMode_exponential_envelope (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) r) 2
  have hsq : Real.exp (-(1 / 2 : ℝ) * ‖r‖) ^ 2 =
      Real.exp (-(1 / 2 : ℝ) * ‖r‖) * Real.exp (-(1 / 2 : ℝ) * ‖r‖) := by ring
  rw [mul_pow, hsq] at hmode
  calc
    _ ≤ ‖r‖ ^ 2 * (planarExponentialConstant (1 / 2) ^ 2 *
        (Real.exp (-(1 / 2 : ℝ) * ‖r‖) * Real.exp (-(1 / 2 : ℝ) * ‖r‖))) :=
      mul_le_mul_of_nonneg_left hmode (sq_nonneg _)
    _ = (planarExponentialConstant (1 / 2) ^ 2 *
        (‖r‖ ^ 2 * Real.exp (-(1 / 2 : ℝ) * ‖r‖))) *
          Real.exp (-(1 / 2 : ℝ) * ‖r‖) := by ring
    _ ≤ C * Real.exp (-(1 / 2 : ℝ) * ‖r‖) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (quadratic_exponential_bound (norm_nonneg r))
          (sq_nonneg _)) (Real.exp_pos _).le

theorem normalizedPlanarMode_second_moment_integrable :
    Integrable (fun r : PlanarPosition => ‖r‖ ^ 2 * normalizedPlanarMode r ^ 2) := by
  simp_rw [normalizedPlanarMode, div_pow, ← mul_div_assoc]
  exact planarResolventMode_second_moment_integrable.div_const _

theorem localizedDensity_second_moment_integrable {freq : ℝ} (hfreq : 0 < freq) :
    Integrable (fun x : Position => ‖x‖ ^ 2 * localizedDensity freq 0 x) := by
  have hsplit : Integrable (fun p : SplitPosition =>
      (‖p.1‖ ^ 2 + p.2 ^ 2) * localizedMode freq 0 p ^ 2) := by
    have hp := normalizedPlanarMode_second_moment_integrable.mul_prod
      (verticalMode_square_integrable hfreq)
    have hz := normalizedPlanarMode_square_integrable.mul_prod
      (verticalMode_moment_integrable hfreq 2)
    convert hp.add hz using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    simp only [localizedMode, sub_zero, mul_pow, Pi.add_apply]
    ring
  have hc := positionSplitCoordinates_measurePreserving.integrable_comp_of_integrable hsplit
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [Function.comp_apply, localizedDensity, continuumLocalizedMode,
    positionSplitCoordinates_norm_sq]

theorem localizedDensity_tail_of_norm {freq R : ℝ} (hfreq : 0 < freq) (hR : 0 < R)
    {S : Set Position} (hS : MeasurableSet S)
    (hout : ∀ x ∉ S, R ≤ ‖x‖) :
    (∫ x in Sᶜ, localizedDensity freq 0 x) ≤ localizedDensitySecondMoment freq / R ^ 2 := by
  have hw := localizedDensity_second_moment_integrable hfreq
  have hd := (localizedDensity_integrable hfreq 0).const_mul (R ^ 2)
  have hle := setIntegral_mono_on hd.integrableOn hw.integrableOn hS.compl
    (fun x hx => mul_le_mul_of_nonneg_right
      (sq_le_sq₀ hR.le (norm_nonneg x) |>.mpr (hout x hx))
      (localizedDensity_nonnegative freq 0 x))
  have hfull := integral_mono_measure (μ := volume.restrict Sᶜ)
    Measure.restrict_le_self (Filter.Eventually.of_forall (fun x =>
      mul_nonneg (sq_nonneg ‖x‖) (localizedDensity_nonnegative freq 0 x))) hw
  rw [integral_const_mul] at hle
  apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
  simpa only [localizedDensitySecondMoment, mul_comm] using hle.trans hfull

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCoulombBox
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual direct coefficient is approximated by a bounded integral
on a six-dimensional rational cube. The cap and truncation errors are
uniform in the relative displacement of the two fixed density packets. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem coulombNumericalBox_measurable (L : ℝ) : MeasurableSet (coulombNumericalBox L) := by
  apply MeasurableSet.iInter
  intro i
  exact (isClosed_le (by fun_prop) continuous_const).measurableSet

theorem coulombNumericalBox_outside (L : ℝ) {x : Position}
    (hx : x ∉ coulombNumericalBox L) : L ≤ ‖x‖ := by
  simp only [coulombNumericalBox, Set.mem_iInter, Set.mem_ofPred_eq, not_forall] at hx
  obtain ⟨i, hi⟩ := hx
  exact (lt_of_not_ge hi).le.trans (by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i)

theorem localizedCappedProfile_eq {freq ε : ℝ} (hfreq : 0 < freq) (hε : 0 < ε)
    (u : PlanarPosition) :
    localizedCappedProfile freq ε u = localizedCappedCoulombCoeff freq ε 0 u := by
  rw [localizedCappedCoulombCoeff_nested hfreq hε]
  unfold localizedCappedProfile
  rw [Measure.volume_eq_prod, integral_prod _ (by
    simpa only [Measure.volume_eq_prod] using cappedPairIntegrand_integrable hε
      (planarCenter u) (localizedDensity_integrable hfreq 0)
      (localizedDensity_integrable hfreq 0))]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [cappedPairIntegrand, cappedCoulombPotential]
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  congr 1
  rw [← integral_add_right_eq_self
    (fun y => cappedCoulombKernel ε (x - y) * localizedDensity freq u y) (planarCenter u)]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [localizedDensity_translate freq u, add_sub_cancel_right]
  rw [mul_comm]
  congr 1
  abel_nf

theorem localizedCappedProfile_box_error {freq ε L : ℝ}
    (hfreq : 0 < freq) (hε : 0 < ε) (hL : 0 < L) (u : PlanarPosition) :
    |localizedCappedProfile freq ε u - localizedCoulombBoxIntegral freq ε L u| ≤
      2 * ε⁻¹ * localizedDensitySecondMoment freq / L ^ 2 := by
  have ht := cappedPair_truncation_error hε (planarCenter u)
    (localizedDensity_integrable hfreq 0) (localizedDensity_integrable hfreq 0)
    (localizedDensity_nonnegative freq 0) (localizedDensity_nonnegative freq 0)
    (coulombNumericalBox_measurable L) (coulombNumericalBox_measurable L)
  simp only [localizedDensity_mass hfreq 0, mul_one, one_mul] at ht
  have hb := localizedDensity_tail_of_norm hfreq hL (coulombNumericalBox_measurable L)
    (fun _ hx => coulombNumericalBox_outside L hx)
  apply ht.trans
  have hε0 : 0 ≤ ε⁻¹ := inv_nonneg.mpr hε.le
  calc
    _ ≤ ε⁻¹ * (localizedDensitySecondMoment freq / L ^ 2 +
        localizedDensitySecondMoment freq / L ^ 2) := by gcongr
    _ = _ := by ring

theorem localizedCoulombProfile_box_error {freq ε L : ℝ}
    (hfreq : 0 < freq) (hε : 0 < ε) (hL : 0 < L) (u : PlanarPosition) :
    |localizedCoulombProfileAt freq u - localizedCoulombBoxIntegral freq ε L u| ≤
      2 * Real.pi * localizedAmplitudeBound freq ^ 2 * ε ^ 2 +
        2 * ε⁻¹ * localizedDensitySecondMoment freq / L ^ 2 := by
  have hcap := localizedCappedCoulombCoeff_error hfreq hε 0 u
  rw [← localizedCoulombProfileAt_eq, ← localizedCappedProfile_eq hfreq hε] at hcap
  exact (abs_sub_le _ (localizedCappedProfile freq ε u) _).trans
    (add_le_add hcap (localizedCappedProfile_box_error hfreq hε hL u))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedRawDensity
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unnormalized packets used by the literal Coulomb quadrature. Squaring
the normalization cancels the Gaussian square root, so the final quotient
uses only the already certified planar mass, frequency and pi evaluators. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem localizedRawDensity_nonnegative (freq : ℝ) (x : Position) :
    0 ≤ localizedRawDensity freq x :=
  mul_nonneg (sq_nonneg _) (Real.exp_pos _).le

theorem localizedRawDensity_le_one {freq : ℝ} (hfreq : 0 ≤ freq) (x : Position) :
    localizedRawDensity freq x ≤ 1 := by
  have hp := (sq_le_sq₀ (planarResolventMode_positive _).le zero_le_one).mpr
    (planarResolventMode_le_one (positionSplitCoordinates x).1)
  have he : Real.exp (-freq * (positionSplitCoordinates x).2 ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hfreq) (sq_nonneg _))
  exact (mul_le_mul hp he (Real.exp_pos _).le (by positivity)).trans_eq (by norm_num)

theorem localizedRawDensity_eq_normalized {freq : ℝ} (hfreq : 0 < freq) (x : Position) :
    localizedRawDensity freq x = localizedRawMass freq * localizedDensity freq 0 x := by
  have hA := planarResolventMode_square_integral_positive
  have hB := Real.sqrt_pos.mpr (div_pos Real.pi_pos hfreq)
  simp only [localizedRawDensity, localizedRawMass, localizedDensity,
    continuumLocalizedMode, localizedMode, sub_zero, mul_pow, normalizedPlanarMode,
    div_pow, verticalMode_square hfreq, Real.sq_sqrt hA.le]
  field_simp

theorem localizedRawDensity_integrable {freq : ℝ} (hfreq : 0 < freq) :
    Integrable (localizedRawDensity freq) := by
  change Integrable (fun x => localizedRawDensity freq x)
  simp_rw [localizedRawDensity_eq_normalized hfreq]
  exact (localizedDensity_integrable hfreq 0).const_mul _

theorem localizedRawDensity_mass {freq : ℝ} (hfreq : 0 < freq) :
    (∫ x, localizedRawDensity freq x) = localizedRawMass freq := by
  simp_rw [localizedRawDensity_eq_normalized hfreq]
  rw [integral_const_mul, localizedDensity_mass hfreq 0, mul_one]

theorem localizedRawMass_square {freq : ℝ} (hfreq : 0 < freq) :
    localizedRawMass freq ^ 2 = (∫ r, planarResolventMode r ^ 2) ^ 2 * Real.pi / freq := by
  rw [localizedRawMass, mul_pow, Real.sq_sqrt (div_pos Real.pi_pos hfreq).le]
  ring

theorem localizedRawCoulombBox_eq {freq : ℝ} (hfreq : 0 < freq) (ε L : ℝ)
    (u : PlanarPosition) :
    localizedRawCoulombBox freq ε L u =
      localizedRawMass freq ^ 2 * localizedCoulombBoxIntegral freq ε L u := by
  unfold localizedRawCoulombBox localizedCoulombBoxIntegral
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with p
  simp only [cappedPairIntegrand, localizedRawDensity_eq_normalized hfreq]
  ring

theorem localizedRawCoulombBox_quotient {freq : ℝ} (hfreq : 0 < freq) (ε L : ℝ)
    (u : PlanarPosition) :
    localizedRawCoulombBox freq ε L u * freq /
      ((∫ r, planarResolventMode r ^ 2) ^ 2 * Real.pi) =
        localizedCoulombBoxIntegral freq ε L u := by
  rw [localizedRawCoulombBox_eq hfreq, localizedRawMass_square hfreq]
  have hA := planarResolventMode_square_integral_positive.ne'
  have hpi := Real.pi_pos.ne'
  field_simp

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarForcingModulus
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit global modulus for the forcing used by the numerical
quadrature. Unlike an unspecified compact-support derivative bound, the
constant is a fixed integer usable by the literal sample-count program. -/

noncomputable section
namespace ContinuumCoulomb

theorem clippedSquare_formula {r : ℝ} (hr : 0 ≤ r) :
    max (1 - r ^ 2) 0 = 1 - (min r 1) ^ 2 := by
  by_cases h : r ≤ 1
  · rw [min_eq_left h, max_eq_left]
    nlinarith
  · rw [min_eq_right (le_of_not_ge h), max_eq_right]
    · norm_num
    · nlinarith

theorem clippedSquare_lipschitz {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    |max (1 - r ^ 2) 0 - max (1 - s ^ 2) 0| ≤ 2 * |r - s| := by
  have har : 0 ≤ min r 1 := le_min hr zero_le_one
  have hbr : 0 ≤ min s 1 := le_min hs zero_le_one
  have hau : min r 1 ≤ 1 := min_le_right _ _
  have hbu : min s 1 ≤ 1 := min_le_right _ _
  have hmin : |min r 1 - min s 1| ≤ |r - s| := by
    simpa only [max_neg_neg, neg_sub_neg, abs_sub_comm] using
      abs_max_sub_max_le_abs (-r) (-s) (-1)
  rw [clippedSquare_formula hr, clippedSquare_formula hs]
  have heq : (1 - min r 1 ^ 2) - (1 - min s 1 ^ 2) =
      (min s 1 - min r 1) * (min s 1 + min r 1) := by ring
  rw [heq, abs_mul, abs_of_nonneg (add_nonneg hbr har), abs_sub_comm (min s 1) (min r 1)]
  have hsum : min s 1 + min r 1 ≤ 2 := by linarith
  calc
    _ ≤ |min r 1 - min s 1| * 2 :=
      mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ ≤ |r - s| * 2 := mul_le_mul_of_nonneg_right hmin (by norm_num)
    _ = _ := by ring

theorem planarForcing_norm_sub_explicit (x y : PlanarPosition) :
    |planarForcing x - planarForcing y| ≤ 32 * ‖x - y‖ := by
  let a := max (1 - ‖x‖ ^ 2) 0
  let b := max (1 - ‖y‖ ^ 2) 0
  have ha0 : 0 ≤ a := le_max_right _ _
  have hb0 : 0 ≤ b := le_max_right _ _
  have ha1 : a ≤ 1 := max_le (by nlinarith [sq_nonneg ‖x‖]) zero_le_one
  have hb1 : b ≤ 1 := max_le (by nlinarith [sq_nonneg ‖y‖]) zero_le_one
  have hab : |a - b| ≤ 2 * |‖x‖ - ‖y‖| :=
    clippedSquare_lipschitz (norm_nonneg x) (norm_nonneg y)
  have hm : max |a| |b| ≤ 1 := by
    rw [abs_of_nonneg ha0, abs_of_nonneg hb0]
    exact max_le ha1 hb1
  have hp := abs_pow_sub_pow_le a b 16
  have hp' : |a ^ 16 - b ^ 16| ≤ |a - b| * 16 := by
    calc
      _ ≤ |a - b| * 16 * max |a| |b| ^ (16 - 1) := hp
      _ ≤ |a - b| * 16 * 1 := mul_le_mul_of_nonneg_left
        (by simpa using pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg a)) hm 15)
        (by positivity)
      _ = _ := mul_one _
  change |a ^ 16 - b ^ 16| ≤ _
  have hnorm := abs_norm_sub_norm_le x y
  nlinarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarResolventModulus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit moduli for numerical normalization and contact integrals.
The constants come from the actual compact forcing and mass-one kernel. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarResolventMode_norm_sub_explicit (x y : PlanarPosition) :
    |planarResolventMode x - planarResolventMode y| ≤ 32 * ‖x - y‖ := by
  unfold planarResolventMode
  rw [← integral_sub (planarResolventMode_integrand_integrable x)
    (planarResolventMode_integrand_integrable y)]
  have h := norm_integral_le_of_norm_le
    (f := fun b => planarResolventKernel b * planarForcing (x - b) -
      planarResolventKernel b * planarForcing (y - b))
    (planarResolventKernel_integrable.mul_const (32 * ‖x - y‖))
    (Filter.Eventually.of_forall (fun b => by
      rw [← mul_sub, norm_mul, Real.norm_of_nonneg (planarResolventKernel_nonnegative b),
        Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (planarResolventKernel_nonnegative b)
      simpa only [show x - b - (y - b) = x - y by abel] using
        planarForcing_norm_sub_explicit (x - b) (y - b)))
  simpa only [integral_mul_const, planarResolventKernel_integral, one_mul,
    Real.norm_eq_abs] using h

theorem planarResolventMode_square_norm_sub (x y : PlanarPosition) :
    |planarResolventMode x ^ 2 - planarResolventMode y ^ 2| ≤ 64 * ‖x - y‖ := by
  have hx := (planarResolventMode_positive x).le
  have hy := (planarResolventMode_positive y).le
  have hsum : 0 ≤ planarResolventMode x + planarResolventMode y := add_nonneg hx hy
  have hsum' : planarResolventMode x + planarResolventMode y ≤ 2 :=
    by linarith [planarResolventMode_le_one x, planarResolventMode_le_one y]
  rw [show planarResolventMode x ^ 2 - planarResolventMode y ^ 2 =
    (planarResolventMode x - planarResolventMode y) *
      (planarResolventMode x + planarResolventMode y) by ring,
    abs_mul, abs_of_nonneg hsum]
  calc
    _ ≤ (32 * ‖x - y‖) * 2 :=
      mul_le_mul (planarResolventMode_norm_sub_explicit x y) hsum'
        hsum (by positivity)
    _ = _ := by ring

theorem planarHoppingIntegrand_norm_sub_explicit (d : ℝ) (x y : PlanarPosition) :
    |planarHoppingIntegrand d x - planarHoppingIntegrand d y| ≤ 64 * ‖x - y‖ := by
  have hx := planarForcing_nonnegative x
  have hy := planarForcing_nonnegative y
  have hz := (planarResolventMode_positive (y - d • planarAxis 0)).le
  have ha := planarResolventMode_le_one (y - d • planarAxis 0)
  have hb := planarForcing_le_one x
  have heq : planarHoppingIntegrand d x - planarHoppingIntegrand d y =
      planarForcing x * (planarResolventMode (x - d • planarAxis 0) -
        planarResolventMode (y - d • planarAxis 0)) +
      (planarForcing x - planarForcing y) * planarResolventMode (y - d • planarAxis 0) := by
    unfold planarHoppingIntegrand
    ring
  rw [heq]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul, abs_of_nonneg hx, abs_of_nonneg hz]
  have hr : |planarResolventMode (x - d • planarAxis 0) -
      planarResolventMode (y - d • planarAxis 0)| ≤ 32 * ‖x - y‖ := by
    simpa only [show x - d • planarAxis 0 - (y - d • planarAxis 0) = x - y by abel] using
      planarResolventMode_norm_sub_explicit (x - d • planarAxis 0) (y - d • planarAxis 0)
  have h₁ := mul_le_mul hb hr (abs_nonneg _) zero_le_one
  have h₂ := mul_le_mul (planarForcing_norm_sub_explicit x y) ha hz (by positivity)
  linarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_RawDensityModulus
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative continuity needed by the six-coordinate finite-box
quadrature. Only the box radius enters the Gaussian modulus. -/

noncomputable section
namespace ContinuumCoulomb

theorem gaussian_box_modulus {freq L z w : ℝ} (hf : 0 ≤ freq)
    (hz : |z| ≤ L) (hw : |w| ≤ L) :
    |Real.exp (-freq * z ^ 2) - Real.exp (-freq * w ^ 2)| ≤
      2 * freq * L * |z - w| := by
  have he := HeatKernelModulus.exp_nonpositive_lipschitz
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hf) (sq_nonneg z))
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hf) (sq_nonneg w))
  have hid : -freq * z ^ 2 - (-freq * w ^ 2) = -freq * (z - w) * (z + w) := by ring
  rw [hid, abs_mul, abs_mul, abs_neg, abs_of_nonneg hf] at he
  have hs : |z + w| ≤ 2 * L := (abs_add_le z w).trans (by linarith)
  calc
    _ ≤ freq * |z - w| * |z + w| := he
    _ ≤ freq * |z - w| * (2 * L) :=
      mul_le_mul_of_nonneg_left hs (mul_nonneg hf (abs_nonneg _))
    _ = _ := by ring

theorem splitRawDensity_eq (freq : ℝ) (x : Position) :
    splitRawDensity freq (positionSplitCoordinates x) = localizedRawDensity freq x := rfl

theorem splitRawDensity_modulus {freq L : ℝ} (hf : 0 ≤ freq)
    (p q : SplitPosition) (hp : |p.2| ≤ L) (hq : |q.2| ≤ L) :
    |splitRawDensity freq p - splitRawDensity freq q| ≤
      64 * ‖p.1 - q.1‖ + 2 * freq * L * |p.2 - q.2| := by
  have hφ : planarResolventMode q.1 ^ 2 ≤ 1 := by
    simpa only [one_pow] using
      (sq_le_sq₀ (planarResolventMode_positive q.1).le zero_le_one).mpr
        (planarResolventMode_le_one q.1)
  have he : Real.exp (-freq * p.2 ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hf) (sq_nonneg _))
  have hid : splitRawDensity freq p - splitRawDensity freq q =
      (planarResolventMode p.1 ^ 2 - planarResolventMode q.1 ^ 2) *
        Real.exp (-freq * p.2 ^ 2) +
      planarResolventMode q.1 ^ 2 *
        (Real.exp (-freq * p.2 ^ 2) - Real.exp (-freq * q.2 ^ 2)) := by
    unfold splitRawDensity
    ring
  rw [hid]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (sq_nonneg (planarResolventMode q.1))]
  have h1 := (mul_le_of_le_one_right (abs_nonneg _) he).trans
    (planarResolventMode_square_norm_sub p.1 q.1)
  have h2 := (mul_le_of_le_one_left (abs_nonneg _) hφ).trans
    (gaussian_box_modulus hf hp hq)
  exact add_le_add h1 h2

theorem positionSplit_planar_norm_sub_le (x y : Position) :
    ‖(positionSplitCoordinates x).1 - (positionSplitCoordinates y).1‖ ≤ ‖x - y‖ := by
  have h := positionSplitCoordinates_norm_sq (x - y)
  rw [map_sub] at h
  simp only [Prod.fst_sub, Prod.snd_sub] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by
    nlinarith [sq_nonneg ((positionSplitCoordinates x).2 - (positionSplitCoordinates y).2)])

theorem positionSplit_vertical_norm_sub_le (x y : Position) :
    |(positionSplitCoordinates x).2 - (positionSplitCoordinates y).2| ≤ ‖x - y‖ := by
  have h := positionSplitCoordinates_norm_sq (x - y)
  rw [map_sub] at h
  simp only [Prod.fst_sub, Prod.snd_sub] at h
  apply (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp
  rw [sq_abs]
  nlinarith [sq_nonneg ‖(positionSplitCoordinates x).1 - (positionSplitCoordinates y).1‖]

theorem localizedRawDensity_box_modulus {freq L : ℝ} (hf : 0 ≤ freq)
    (x y : Position) (hx : |(positionSplitCoordinates x).2| ≤ L)
    (hy : |(positionSplitCoordinates y).2| ≤ L) :
    |localizedRawDensity freq x - localizedRawDensity freq y| ≤
      (64 + 2 * freq * L) * ‖x - y‖ := by
  have hL : 0 ≤ L := (abs_nonneg _).trans hx
  have h := splitRawDensity_modulus hf (positionSplitCoordinates x) (positionSplitCoordinates y) hx hy
  rw [splitRawDensity_eq, splitRawDensity_eq] at h
  apply h.trans
  calc
    _ ≤ 64 * ‖x - y‖ + 2 * freq * L * ‖x - y‖ := by
      gcongr
      · exact positionSplit_planar_norm_sub_le x y
      · exact positionSplit_vertical_norm_sub_le x y
    _ = _ := by ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CappedRawModulus
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomial modulus for the actual six-coordinate capped density
integrand. Relative displacement has no effect on this modulus. -/

noncomputable section
namespace ContinuumCoulomb

theorem bounded_product_sub {a b c d : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    |a * b - c * d| ≤ |a - c| + |b - d| := by
  have he : a * b - c * d = a * (b - d) + (a - c) * d := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul, abs_of_nonneg ha0, abs_of_nonneg hd0]
  have h1 := mul_le_of_le_one_left (abs_nonneg (b - d)) ha1
  have h2 := mul_le_of_le_one_right (abs_nonneg (a - c)) hd1
  linarith

theorem cappedRawPair_modulus {freq ε L : ℝ} (hf : 0 ≤ freq) (hε : 0 < ε)
    (shift : Position) (x y x' y' : Position)
    (hx : |(positionSplitCoordinates x).2| ≤ L)
    (hy : |(positionSplitCoordinates y).2| ≤ L)
    (hx' : |(positionSplitCoordinates x').2| ≤ L)
    (hy' : |(positionSplitCoordinates y').2| ≤ L) :
    |cappedPairIntegrand ε shift (localizedRawDensity freq) (localizedRawDensity freq) (x, y) -
      cappedPairIntegrand ε shift (localizedRawDensity freq) (localizedRawDensity freq) (x', y')| ≤
      ((64 + 2 * freq * L) * ε⁻¹ + ε⁻¹ ^ 2) * (‖x - x'‖ + ‖y - y'‖) := by
  let a := localizedRawDensity freq x * localizedRawDensity freq y
  let b := localizedRawDensity freq x' * localizedRawDensity freq y'
  let k := cappedCoulombKernel ε (x - y - shift)
  let k' := cappedCoulombKernel ε (x' - y' - shift)
  have hb0 : 0 ≤ b := mul_nonneg (localizedRawDensity_nonnegative _ _) (localizedRawDensity_nonnegative _ _)
  have hb1 : b ≤ 1 := (mul_le_mul (localizedRawDensity_le_one hf _)
    (localizedRawDensity_le_one hf _) (localizedRawDensity_nonnegative _ _) zero_le_one).trans_eq (one_mul 1)
  have hk0 : 0 ≤ k := cappedCoulombKernel_nonnegative hε _
  have hk1 : k ≤ ε⁻¹ := cappedCoulombKernel_le hε _
  have hab : |a - b| ≤ (64 + 2 * freq * L) * (‖x - x'‖ + ‖y - y'‖) := by
    have h := bounded_product_sub (a := localizedRawDensity freq x)
      (b := localizedRawDensity freq y) (c := localizedRawDensity freq x')
      (d := localizedRawDensity freq y') (localizedRawDensity_nonnegative freq x)
      (localizedRawDensity_le_one hf x) (localizedRawDensity_nonnegative freq y')
      (localizedRawDensity_le_one hf y')
    apply h.trans
    have h1 := localizedRawDensity_box_modulus hf x x' hx hx'
    have h2 := localizedRawDensity_box_modulus hf y y' hy hy'
    linarith
  have hkk : |k - k'| ≤ ε⁻¹ ^ 2 * (‖x - x'‖ + ‖y - y'‖) := by
    have h := cappedCoulombKernel_norm_sub hε (x - y - shift) (x' - y' - shift)
    have hn : ‖x - y - shift - (x' - y' - shift)‖ ≤ ‖x - x'‖ + ‖y - y'‖ := by
      rw [show x - y - shift - (x' - y' - shift) = (x - x') - (y - y') by abel]
      exact norm_sub_le _ _
    exact h.trans (mul_le_mul_of_nonneg_left hn (sq_nonneg _))
  have he : cappedPairIntegrand ε shift (localizedRawDensity freq) (localizedRawDensity freq) (x, y) -
      cappedPairIntegrand ε shift (localizedRawDensity freq) (localizedRawDensity freq) (x', y') =
      (a - b) * k + b * (k - k') := by
    dsimp only [cappedPairIntegrand, a, b, k, k']
    ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul, abs_of_nonneg hk0, abs_of_nonneg hb0]
  have h1 := mul_le_mul hab hk1 hk0 (by
    have hL : 0 ≤ L := (abs_nonneg _).trans hx
    positivity)
  have h2 := (mul_le_of_le_one_left (abs_nonneg (k - k')) hb1).trans hkk
  nlinarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_HeatDensityModulus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit moduli of the actual forcing-weighted heat density. These
are the constants used for the fixed-dimensional quadrature mesh. -/

noncomputable section
namespace ContinuumCoulomb.HeatKernelModulus

theorem squared_norm_difference {u v : PlanarPosition} {D : ℝ}
    (hu : ‖u‖ ≤ D) (hv : ‖v‖ ≤ D) :
    |‖u‖ ^ 2 - ‖v‖ ^ 2| ≤ 2 * D * ‖u - v‖ := by
  have hD : 0 ≤ D := (norm_nonneg _).trans hu
  have hid : ‖u‖ ^ 2 - ‖v‖ ^ 2 = (‖u‖ - ‖v‖) * (‖u‖ + ‖v‖) := by ring
  rw [hid, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  calc
    _ ≤ ‖u - v‖ * (‖u‖ + ‖v‖) :=
      mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le u v) (by positivity)
    _ ≤ ‖u - v‖ * (2 * D) := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    _ = _ := by ring

theorem density_space_lipschitz {r p q : PlanarPosition} {η t D : ℝ}
    (hη : 0 < η) (ht : η ≤ t) (hp : ‖r - p‖ ≤ D) (hq : ‖r - q‖ ≤ D) :
    |density r t p - density r t q| ≤
      (2 * D / η ^ 2 + 32 * η⁻¹) * ‖p - q‖ := by
  have ht0 : 0 < t := hη.trans_le ht
  have hs : |‖r - p‖ ^ 2 - ‖r - q‖ ^ 2| ≤ 2 * D * ‖p - q‖ := by
    have h := squared_norm_difference hp hq
    simpa only [show (r - p) - (r - q) = -(p - q) by abel, norm_neg] using h
  have hk := kernel_space_lipschitz hη ht (sq_nonneg ‖r - p‖) (sq_nonneg ‖r - q‖)
  have hk' : |kernel t (‖r - p‖ ^ 2) - kernel t (‖r - q‖ ^ 2)| ≤
      (2 * D / η ^ 2) * ‖p - q‖ := by
    calc
      _ ≤ |‖r - p‖ ^ 2 - ‖r - q‖ ^ 2| / η ^ 2 := hk
      _ ≤ (2 * D * ‖p - q‖) / η ^ 2 := div_le_div_of_nonneg_right hs (sq_nonneg η)
      _ = _ := by ring
  have hkq := kernel_le_inverse hη ht (sq_nonneg ‖r - q‖)
  have hkq0 := kernel_nonnegative (A := ‖r - q‖ ^ 2) ht0
  have hf := planarForcing_norm_sub_explicit p q
  have hfp0 := planarForcing_nonnegative p
  have hfp1 := planarForcing_le_one p
  have hid : density r t p - density r t q =
      (kernel t (‖r - p‖ ^ 2) - kernel t (‖r - q‖ ^ 2)) * planarForcing p +
        kernel t (‖r - q‖ ^ 2) * (planarForcing p - planarForcing q) := by
    unfold density
    ring
  rw [hid]
  calc
    _ ≤ |(kernel t (‖r - p‖ ^ 2) - kernel t (‖r - q‖ ^ 2)) * planarForcing p| +
        |kernel t (‖r - q‖ ^ 2) * (planarForcing p - planarForcing q)| := abs_add_le _ _
    _ = |kernel t (‖r - p‖ ^ 2) - kernel t (‖r - q‖ ^ 2)| * planarForcing p +
        kernel t (‖r - q‖ ^ 2) * |planarForcing p - planarForcing q| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hfp0, abs_of_nonneg hkq0]
    _ ≤ (2 * D / η ^ 2) * ‖p - q‖ + η⁻¹ * (32 * ‖p - q‖) := by
      apply add_le_add
      · exact (mul_le_of_le_one_right (abs_nonneg _) hfp1).trans hk'
      · exact mul_le_mul hkq hf (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem density_time_lipschitz {r p : PlanarPosition} {η t s D : ℝ}
    (hη : 0 < η) (ht : η ≤ t) (hs : η ≤ s) (hp : ‖r - p‖ ≤ D) :
    |density r t p - density r s p| ≤
      (η⁻¹ ^ 2 + η⁻¹ * (1 + D ^ 2 / (4 * η ^ 2))) * |t - s| := by
  have hD : 0 ≤ D := (norm_nonneg _).trans hp
  have hsq : ‖r - p‖ ^ 2 ≤ D ^ 2 := (sq_le_sq₀ (norm_nonneg _) hD).mpr hp
  have h := kernel_time_lipschitz hη ht hs (sq_nonneg ‖r - p‖)
  rw [density, density, ← sub_mul, abs_mul, abs_of_nonneg (planarForcing_nonnegative p)]
  apply (mul_le_of_le_one_right (abs_nonneg _) (planarForcing_le_one p)).trans
  apply h.trans
  gcongr

end ContinuumCoulomb.HeatKernelModulus

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarHeatBoxCoordinates
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact two-coordinate box formula for the actual heat average.
The forcing vanishes outside this fixed square, so spatial truncation
introduces no error. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarPairEquiv_symm_apply (p : ℝ × ℝ) :
    planarPairEquiv.symm p = WithLp.toLp 2 ![p.1, p.2] := by
  ext i
  fin_cases i <;> rfl

theorem planarPairEquiv_measurePreserving : MeasurePreserving planarPairEquiv :=
  (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2))

theorem planarPairEquiv_symm_continuous : Continuous planarPairEquiv.symm := by
  rw [show (planarPairEquiv.symm : (ℝ × ℝ) → PlanarPosition) =
      (fun p => WithLp.toLp 2 ![p.1, p.2]) from funext planarPairEquiv_symm_apply]
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp (by fun_prop)

theorem planarPair_integral (f : PlanarPosition → ℝ) :
    (∫ r, f r) = ∫ p, f (planarPairEquiv.symm p) := by
  have h := planarPairEquiv_measurePreserving.integral_comp' (f ∘ planarPairEquiv.symm)
  simpa only [Function.comp_apply, MeasurableEquiv.symm_apply_apply] using h

theorem planarForcing_pair_zero {p : ℝ × ℝ}
    (hp : p ∉ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1) :
    planarForcing (planarPairEquiv.symm p) = 0 := by
  apply planarForcing_zero_of_norm_ge_one
  have h0 : |p.1| ≤ ‖planarPairEquiv.symm p‖ := by
    simpa only [planarPairEquiv_symm_apply, PiLp.toLp_apply, Matrix.cons_val_zero,
      Real.norm_eq_abs] using PiLp.norm_apply_le (planarPairEquiv.symm p) 0
  have h1 : |p.2| ≤ ‖planarPairEquiv.symm p‖ := by
    simpa only [planarPairEquiv_symm_apply, PiLp.toLp_apply, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Real.norm_eq_abs] using PiLp.norm_apply_le (planarPairEquiv.symm p) 1
  by_contra h
  have hn : ‖planarPairEquiv.symm p‖ < 1 := lt_of_not_ge h
  apply hp
  exact ⟨⟨by linarith [neg_abs_le p.1], by linarith [le_abs_self p.1]⟩,
    ⟨by linarith [neg_abs_le p.2], by linarith [le_abs_self p.2]⟩⟩

theorem planarHeatAverage_box (t : ℝ) (r : PlanarPosition) :
    planarHeatAverage t r = ∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1,
      planarHeatKernel t (r - planarPairEquiv.symm (x, y)) *
        planarForcing (planarPairEquiv.symm (x, y)) := by
  rw [planarHeatAverage_flip, planarPair_integral]
  let f := fun p : ℝ × ℝ => planarHeatKernel t (r - planarPairEquiv.symm p) *
    planarForcing (planarPairEquiv.symm p)
  have hf : Continuous f :=
    ((planarHeatKernel_continuous t).comp (continuous_const.sub planarPairEquiv_symm_continuous)).mul
      (planarForcing_C7.continuous.comp planarPairEquiv_symm_continuous)
  have hi : IntegrableOn f (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1)
      ((volume : Measure ℝ).prod volume) :=
    hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hs : (∫ p, f p) = ∫ p in Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1, f p := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro p hp
    simp only [f, planarForcing_pair_zero hp, mul_zero]
  change (∫ p, f p) = _
  rw [hs]
  rw [Measure.volume_eq_prod, setIntegral_prod f hi]
  simp_rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  rfl

theorem planarHeatResolvent_box (t : ℝ) (r : PlanarPosition) :
    Real.exp (-t) * planarHeatAverage t r =
      ∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1,
        HeatKernelModulus.kernel t (‖r - planarPairEquiv.symm (x, y)‖ ^ 2) *
          planarForcing (planarPairEquiv.symm (x, y)) := by
  rw [planarHeatAverage_box, ← intervalIntegral.integral_const_mul]
  congr 1
  funext x
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  funext y
  rw [HeatKernelModulus.kernel_eq_heat]
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarHeatBoxBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit coordinate bounds on the fixed forcing square. They turn
the kernel estimates into concrete quadrature constants for every input
point, with polynomial dependence on its magnitude. -/

noncomputable section
namespace ContinuumCoulomb

theorem planarPair_norm_sq (p : ℝ × ℝ) :
    ‖planarPairEquiv.symm p‖ ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, planarPairEquiv_symm_apply]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs]

theorem planarPair_norm_le_two {p : ℝ × ℝ}
    (hp : p ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1) :
    ‖planarPairEquiv.symm p‖ ≤ 2 := by
  have h1 : p.1 ^ 2 ≤ 1 := by
    have hz := mul_nonneg (sub_nonneg.mpr hp.1.2) (show 0 ≤ 1 + p.1 by linarith [hp.1.1])
    nlinarith
  have h2 : p.2 ^ 2 ≤ 1 := by
    have hz := mul_nonneg (sub_nonneg.mpr hp.2.2) (show 0 ≤ 1 + p.2 by linarith [hp.2.1])
    nlinarith
  have hn := planarPair_norm_sq p
  nlinarith [norm_nonneg (planarPairEquiv.symm p)]

theorem planarPair_distance_first (x x' y : ℝ) :
    ‖planarPairEquiv.symm (x, y) - planarPairEquiv.symm (x', y)‖ = |x - x'| := by
  have heq : planarPairEquiv.symm (x, y) - planarPairEquiv.symm (x', y) =
      planarPairEquiv.symm (x - x', 0) := by
    rw [planarPairEquiv_symm_apply, planarPairEquiv_symm_apply, planarPairEquiv_symm_apply]
    ext i
    fin_cases i <;> simp
  rw [heq]
  have h := planarPair_norm_sq (x - x', 0)
  nlinarith [norm_nonneg (planarPairEquiv.symm (x - x', 0)), abs_nonneg (x - x'), sq_abs (x - x')]

theorem planarPair_distance_second (x y y' : ℝ) :
    ‖planarPairEquiv.symm (x, y) - planarPairEquiv.symm (x, y')‖ = |y - y'| := by
  have heq : planarPairEquiv.symm (x, y) - planarPairEquiv.symm (x, y') =
      planarPairEquiv.symm (0, y - y') := by
    rw [planarPairEquiv_symm_apply, planarPairEquiv_symm_apply, planarPairEquiv_symm_apply]
    ext i
    fin_cases i <;> simp
  rw [heq]
  have h := planarPair_norm_sq (0, y - y')
  nlinarith [norm_nonneg (planarPairEquiv.symm (0, y - y')), abs_nonneg (y - y'), sq_abs (y - y')]

theorem planarPair_distance_bound (r : PlanarPosition) {p : ℝ × ℝ}
    (hp : p ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1) :
    ‖r - planarPairEquiv.symm p‖ ≤ ‖r‖ + 2 :=
  (norm_sub_le _ _).trans (add_le_add_right (planarPair_norm_le_two hp) _)

theorem planarBox_spatial_first (r : PlanarPosition) {η t x x' y : ℝ}
    (hη : 0 < η) (ht : η ≤ t)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) (hx' : x' ∈ Set.Icc (-1 : ℝ) 1)
    (hy : y ∈ Set.Icc (-1 : ℝ) 1) :
    |HeatKernelModulus.density r t (planarPairEquiv.symm (x, y)) -
      HeatKernelModulus.density r t (planarPairEquiv.symm (x', y))| ≤
      planarBoxSpatialConstant r η * |x - x'| := by
  simpa only [planarPair_distance_first, planarBoxSpatialConstant] using
    HeatKernelModulus.density_space_lipschitz hη ht
      (planarPair_distance_bound r (p := (x, y)) ⟨hx, hy⟩)
      (planarPair_distance_bound r (p := (x', y)) ⟨hx', hy⟩)

theorem planarBox_spatial_second (r : PlanarPosition) {η t x y y' : ℝ}
    (hη : 0 < η) (ht : η ≤ t)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) (hy : y ∈ Set.Icc (-1 : ℝ) 1)
    (hy' : y' ∈ Set.Icc (-1 : ℝ) 1) :
    |HeatKernelModulus.density r t (planarPairEquiv.symm (x, y)) -
      HeatKernelModulus.density r t (planarPairEquiv.symm (x, y'))| ≤
      planarBoxSpatialConstant r η * |y - y'| := by
  simpa only [planarPair_distance_second, planarBoxSpatialConstant] using
    HeatKernelModulus.density_space_lipschitz hη ht
      (planarPair_distance_bound r (p := (x, y)) ⟨hx, hy⟩)
      (planarPair_distance_bound r (p := (x, y')) ⟨hx, hy'⟩)

theorem planarBox_time (r : PlanarPosition) {η t s x y : ℝ}
    (hη : 0 < η) (ht : η ≤ t) (hs : η ≤ s)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) (hy : y ∈ Set.Icc (-1 : ℝ) 1) :
    |HeatKernelModulus.density r t (planarPairEquiv.symm (x, y)) -
      HeatKernelModulus.density r s (planarPairEquiv.symm (x, y))| ≤
      planarBoxTimeConstant r η * |t - s| :=
  HeatKernelModulus.density_time_lipschitz hη ht hs
    (planarPair_distance_bound r (p := (x, y)) ⟨hx, hy⟩)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_PlanarForcingProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact rational evaluation of the actual compact planar forcing.
Only rational arithmetic and a sign test occur. -/

namespace ContinuumCoulomb.PlanarForcingProgram
open ExactQuantumFactoring.BitStackProgram

theorem position_norm_sq (q : ℚ × ℚ) :
    ‖position q‖ ^ 2 = (q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_two, position, PiLp.toLp_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs]

theorem value_cast (q : ℚ × ℚ) : (value q : ℝ) = planarForcing (position q) := by
  rw [planarForcing, positivePartSixteen, position_norm_sq]
  unfold value
  push_cast
  rfl

end ContinuumCoulomb.PlanarForcingProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RationalExponential
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A rational Taylor approximation with an explicit magnitude and binary
precision parameter. This applies to the negative rational exponents in
the Gaussian heat kernel as well as to positive arguments. -/

open scoped BigOperators
namespace ContinuumCoulomb.RationalExponential

private theorem factorial_bound (M p : ℕ) :
    2 ^ (p + 2) * M ^ order M p ≤ (order M p).factorial := by
  let N := 2 * M ^ 2 + p + 2
  have hprec : 2 ^ (p + 2) ≤ 2 ^ N :=
    Nat.pow_le_pow_right (by decide) (by dsimp [N]; omega)
  have hpow : 2 ^ N * M ^ (2 * N) ≤ N ^ N := by
    rw [pow_mul, ← mul_pow]
    apply Nat.pow_le_pow_left
    dsimp [N]
    omega
  have hfac : N ^ N ≤ (2 * N).factorial := by
    have h1 : N ^ N ≤ (N + 1) ^ N := Nat.pow_le_pow_left (Nat.le_succ N) N
    have h2 : (N + 1) ^ N ≤ N.factorial * (N + 1) ^ N := by
      simpa only [one_mul] using Nat.mul_le_mul_right ((N + 1) ^ N)
        (show 1 ≤ N.factorial from Nat.factorial_pos N)
    have h3 := @Nat.factorial_mul_pow_le_factorial N N
    rw [show N + N = 2 * N by omega] at h3
    exact h1.trans (h2.trans h3)
  exact (Nat.mul_le_mul_right (M ^ (2 * N)) hprec).trans (hpow.trans hfac)

theorem error (M p : ℕ) (q : ℚ) (hq : |(q : ℝ)| ≤ M) :
    |Real.exp (q : ℝ) - (approximate M p q : ℝ)| ≤ (2 ^ p : ℝ)⁻¹ := by
  let n := order M p
  have hpnonneg : 0 ≤ (p : ℝ) := by positivity
  have hx : ‖((q : ℝ) : ℂ)‖ / (n + 1 : ℕ) ≤ (1 / 2 : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n + 1 : ℕ))).mpr
    dsimp [n, order]
    push_cast
    nlinarith [sq_nonneg ((M : ℝ) - 1 / 4)]
  have hc := Complex.exp_bound' (x := ((q : ℝ) : ℂ)) (n := n) hx
  have hr : |Real.exp (q : ℝ) - (approximate M p q : ℝ)| ≤
      |(q : ℝ)| ^ n / (n.factorial : ℝ) * 2 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, ← Complex.ofReal_exp,
      ← Complex.ofReal_pow, ← Complex.ofReal_natCast, ← Complex.ofReal_div,
      ← Complex.ofReal_sum, ← Complex.ofReal_sub, approximate, taylorSum,
      Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, n] using hc
  have hpow : |(q : ℝ)| ^ n ≤ (M : ℝ) ^ n := pow_le_pow_left₀ (abs_nonneg _) hq n
  have hfac : (2 ^ (p + 2) : ℝ) * (M : ℝ) ^ n ≤ (n.factorial : ℝ) := by
    exact_mod_cast factorial_bound M p
  have hratio : (M : ℝ) ^ n / (n.factorial : ℝ) ≤ (2 ^ (p + 2) : ℝ)⁻¹ := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < n.factorial)).mpr
    have hm : (M : ℝ) ^ n * 2 ^ (p + 2) ≤ (n.factorial : ℝ) := by
      simpa only [mul_comm] using hfac
    have hr' : (M : ℝ) ^ n ≤ (n.factorial : ℝ) / 2 ^ (p + 2) :=
      (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ (p + 2))).mpr hm
    simpa only [div_eq_mul_inv, mul_comm] using hr'
  have hprec : (2 ^ (p + 2) : ℝ)⁻¹ * 2 ≤ (2 ^ p : ℝ)⁻¹ := by
    rw [pow_add]
    norm_num
    have hp : 0 ≤ (2 ^ p : ℝ)⁻¹ := by positivity
    nlinarith
  exact hr.trans ((mul_le_mul_of_nonneg_right
    ((div_le_div_of_nonneg_right hpow (by positivity)).trans hratio) (by norm_num)).trans hprec)

end ContinuumCoulomb.RationalExponential

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_RationalExponentialProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomial-time rational exponential evaluator. Magnitude and
precision bounds are supplied in unary; the rational argument and result
are encoded in binary. Every arithmetic operation is an actual stack
program, including the shared-denominator Taylor recurrence. -/

namespace ContinuumCoulomb.RationalExponentialProgram
open ExactQuantumFactoring.BitStackProgram
open RationalTaylorRegisters

theorem error (x : Input) (hx : |(x.2.2 : ℝ)| ≤ x.1) :
    |Real.exp (x.2.2 : ℝ) - (approximate x : ℝ)| ≤ (2 ^ x.2.1 : ℝ)⁻¹ :=
  RationalExponential.error x.1 x.2.1 x.2.2 hx

end ContinuumCoulomb.RationalExponentialProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RationalHeatSample
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual rational evaluation of the heat-resolvent integrand. Both π and
the exponential are computed by rational approximation programs.
Clamping the computed π below by one keeps every denominator quantitative. -/

namespace ContinuumCoulomb.RationalHeatSample
open ExactQuantumFactoring.BitStackProgram

theorem safePi_ge_one (N : ℕ) : (1 : ℝ) ≤ (safePi N : ℝ) := by
  exact_mod_cast le_max_left (1 : ℚ) (PiProgram.approximate N)

theorem safePi_error (N : ℕ) (hN : 0 < N) :
    |(safePi N : ℝ) - Real.pi| ≤ 8 / (N : ℝ) := by
  have h := PiProgram.error N hN
  have hp : (1 : ℝ) ≤ Real.pi := by linarith [Real.two_le_pi]
  by_cases hq : (1 : ℚ) ≤ PiProgram.approximate N
  · simpa only [safePi, max_eq_right hq] using h
  · have hq' : (PiProgram.approximate N : ℝ) ≤ 1 := by exact_mod_cast le_of_not_ge hq
    rw [safePi, max_eq_left (le_of_not_ge hq), Rat.cast_one,
      abs_of_nonpos (by linarith)]
    rw [abs_of_nonpos (by linarith)] at h
    linarith

theorem ratio_error {E e P Q dE dP : ℝ}
    (hP : 1 ≤ P) (hQ : 1 ≤ Q) (he : 0 ≤ e) (he1 : e ≤ 1)
    (hE : |E - e| ≤ dE) (hPQ : |P - Q| ≤ dP) :
    |E / P - e / Q| ≤ dE + dP := by
  have hP0 : 0 < P := by linarith
  have hQ0 : 0 < Q := by linarith
  have hdE : 0 ≤ dE := (abs_nonneg _).trans hE
  have hdP : 0 ≤ dP := (abs_nonneg _).trans hPQ
  have hid : E / P - e / Q = (E - e) / P + e * (Q - P) / (P * Q) := by
    field_simp
    ring
  rw [hid]
  calc
    _ ≤ |(E - e) / P| + |e * (Q - P) / (P * Q)| := abs_add_le _ _
    _ ≤ dE + dP := by
      apply add_le_add
      · rw [abs_div, abs_of_pos hP0]
        apply (div_le_iff₀ hP0).mpr
        exact hE.trans (by nlinarith)
      · rw [abs_div, abs_mul, abs_of_nonneg he, abs_of_pos (mul_pos hP0 hQ0), abs_sub_comm Q P]
        apply (div_le_iff₀ (mul_pos hP0 hQ0)).mpr
        have hmul : 1 ≤ P * Q := by nlinarith
        have hnum := mul_le_mul_of_nonneg_left hPQ he
        nlinarith

theorem exponent_nonpos (a : Arguments) (ht : 0 < (a.1 : ℝ)) :
    (exponent a : ℝ) ≤ 0 := by
  simp only [exponent, Rat.cast_sub, Rat.cast_neg, Rat.cast_div, Rat.cast_add, Rat.cast_pow,
    Rat.cast_mul, Rat.cast_ofNat]
  have hpos : 0 ≤ (((a.2.1.1 : ℝ) - a.2.2.1) ^ 2 +
      ((a.2.1.2 : ℝ) - a.2.2.2) ^ 2) / (4 * (a.1 : ℝ)) := by positivity
  linarith

theorem position_sub_norm_sq (x y : Point) :
    ‖PlanarForcingProgram.position x - PlanarForcingProgram.position y‖ ^ 2 =
      ((x.1 : ℝ) - y.1) ^ 2 + ((x.2 : ℝ) - y.2) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_two, PlanarForcingProgram.position, PiLp.sub_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs]

theorem exact_density (a : Arguments) :
    Real.exp (exponent a : ℝ) * planarForcing (PlanarForcingProgram.position a.2.2) /
      (4 * Real.pi * (a.1 : ℝ)) =
    Real.exp (-(a.1 : ℝ)) * planarHeatKernel a.1
      (PlanarForcingProgram.position a.2.1 - PlanarForcingProgram.position a.2.2) *
      planarForcing (PlanarForcingProgram.position a.2.2) := by
  simp only [exponent, Rat.cast_sub, Rat.cast_neg, Rat.cast_div, Rat.cast_add,
    Rat.cast_pow, Rat.cast_mul, Rat.cast_ofNat, planarHeatKernel, position_sub_norm_sq]
  rw [show -(a.1 : ℝ) - (((a.2.1.1 : ℝ) - a.2.2.1) ^ 2 +
      ((a.2.1.2 : ℝ) - a.2.2.2) ^ 2) / (4 * (a.1 : ℝ)) =
      -(a.1 : ℝ) + (-((((a.2.1.1 : ℝ) - a.2.2.1) ^ 2 +
      ((a.2.1.2 : ℝ) - a.2.2.2) ^ 2) / (4 * (a.1 : ℝ)))) by ring,
    Real.exp_add]
  simp only [neg_div]
  ring

theorem error (x : Input) (ht : 0 < (x.2.1 : ℝ)) (hN : 0 < x.1.2.2)
    (hM : |(exponent x.2 : ℝ)| ≤ x.1.1) :
    |(value x : ℝ) - Real.exp (exponent x.2 : ℝ) *
      planarForcing (PlanarForcingProgram.position x.2.2.2) /
      (4 * Real.pi * (x.2.1 : ℝ))| ≤
      ((2 ^ x.1.2.1 : ℝ)⁻¹ + 8 / (x.1.2.2 : ℝ)) / (4 * (x.2.1 : ℝ)) := by
  let F := planarForcing (PlanarForcingProgram.position x.2.2.2)
  have hF : 0 ≤ F := planarForcing_nonnegative _
  have hF1 : F ≤ 1 := planarForcing_le_one _
  have he := RationalExponential.error x.1.1 x.1.2.1 (exponent x.2) hM
  have hr := ratio_error
    (E := (RationalExponential.approximate x.1.1 x.1.2.1 (exponent x.2) : ℝ))
    (e := Real.exp (exponent x.2 : ℝ)) (dE := (2 ^ x.1.2.1 : ℝ)⁻¹)
    (dP := 8 / (x.1.2.2 : ℝ))
    (safePi_ge_one x.1.2.2) (by linarith [Real.two_le_pi])
    (Real.exp_pos _).le ((Real.exp_le_one_iff).mpr (exponent_nonpos x.2 ht))
    (by simpa only [abs_sub_comm] using he) (safePi_error x.1.2.2 hN)
  have hd : 0 < 4 * (x.2.1 : ℝ) := by positivity
  have hv : (value x : ℝ) - Real.exp (exponent x.2 : ℝ) * F /
      (4 * Real.pi * (x.2.1 : ℝ)) =
      (((RationalExponential.approximate x.1.1 x.1.2.1 (exponent x.2) : ℝ) /
        (safePi x.1.2.2 : ℝ) - Real.exp (exponent x.2 : ℝ) / Real.pi) * F) /
        (4 * (x.2.1 : ℝ)) := by
    simp only [value, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, PlanarForcingProgram.value_cast]
    dsimp only [F]
    ring
  rw [hv, abs_div, abs_mul, abs_of_nonneg hF, abs_of_pos hd]
  apply div_le_div_of_nonneg_right _ hd.le
  have hn := mul_le_mul_of_nonneg_right hr hF
  have hb : 0 ≤ (2 ^ x.1.2.1 : ℝ)⁻¹ + 8 / (x.1.2.2 : ℝ) := by positivity
  exact hn.trans (by nlinarith)

end ContinuumCoulomb.RationalHeatSample

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_HeatSampleError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification and uniform error of the literal rational samples used
in the box quadrature. The required Taylor magnitude follows from the
input radius and the positive time cutoff. -/

namespace ContinuumCoulomb

theorem rationalPosition_eq_pair (q : ℚ × ℚ) :
    PlanarForcingProgram.position q = planarPairEquiv.symm ((q.1 : ℝ), (q.2 : ℝ)) := by
  rw [planarPairEquiv_symm_apply]
  rfl

namespace RationalHeatSample

theorem error_density (x : Input) (ht : 0 < (x.2.1 : ℝ)) (hN : 0 < x.1.2.2)
    (hM : |(exponent x.2 : ℝ)| ≤ x.1.1) :
    |(value x : ℝ) - HeatKernelModulus.density (PlanarForcingProgram.position x.2.2.1)
      (x.2.1 : ℝ) (PlanarForcingProgram.position x.2.2.2)| ≤
      ((2 ^ x.1.2.1 : ℝ)⁻¹ + 8 / (x.1.2.2 : ℝ)) / (4 * (x.2.1 : ℝ)) := by
  have h := error x ht hN hM
  rw [exact_density] at h
  simpa only [HeatKernelModulus.density, HeatKernelModulus.kernel_eq_heat] using h

theorem error_density_uniform (x : Input) {η : ℝ} (hη : 0 < η) (ht : η ≤ (x.2.1 : ℝ))
    (hN : 0 < x.1.2.2) (hM : |(exponent x.2 : ℝ)| ≤ x.1.1) :
    |(value x : ℝ) - HeatKernelModulus.density (PlanarForcingProgram.position x.2.2.1)
      (x.2.1 : ℝ) (PlanarForcingProgram.position x.2.2.2)| ≤
      ((2 ^ x.1.2.1 : ℝ)⁻¹ + 8 / (x.1.2.2 : ℝ)) / (4 * η) := by
  apply (error_density x (hη.trans_le ht) hN hM).trans
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  linarith

theorem exponent_abs_le (a : Arguments) {η T : ℝ} (hη : 0 < η)
    (ht : η ≤ (a.1 : ℝ)) (hT : (a.1 : ℝ) ≤ T)
    (hy₁ : (a.2.2.1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1)
    (hy₂ : (a.2.2.2 : ℝ) ∈ Set.Icc (-1 : ℝ) 1) :
    |(exponent a : ℝ)| ≤
      T + (‖PlanarForcingProgram.position a.2.1‖ + 2) ^ 2 / (4 * η) := by
  have ht0 := hη.trans_le ht
  have hd := planarPair_distance_bound (PlanarForcingProgram.position a.2.1)
    (p := ((a.2.2.1 : ℝ), (a.2.2.2 : ℝ))) ⟨hy₁, hy₂⟩
  rw [← rationalPosition_eq_pair] at hd
  have hsq : ‖PlanarForcingProgram.position a.2.1 - PlanarForcingProgram.position a.2.2‖ ^ 2 ≤
      (‖PlanarForcingProgram.position a.2.1‖ + 2) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hd
  rw [abs_of_nonpos (exponent_nonpos a ht0)]
  have he : (exponent a : ℝ) = -(a.1 : ℝ) -
      ‖PlanarForcingProgram.position a.2.1 - PlanarForcingProgram.position a.2.2‖ ^ 2 /
        (4 * (a.1 : ℝ)) := by
    simp only [exponent, Rat.cast_sub, Rat.cast_neg, Rat.cast_div, Rat.cast_add,
      Rat.cast_pow, Rat.cast_mul, Rat.cast_ofNat, position_sub_norm_sq]
  rw [he]
  have h₁ := div_le_div_of_nonneg_right hsq (show 0 ≤ 4 * (a.1 : ℝ) by positivity)
  have h₂ := div_le_div_of_nonneg_left
    (sq_nonneg (‖PlanarForcingProgram.position a.2.1‖ + 2))
    (show 0 < 4 * η by positivity) (show 4 * η ≤ 4 * (a.1 : ℝ) by linarith)
  linarith

end RationalHeatSample
end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_HoppingBox
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual contact numerator is an integral over the fixed forcing
square. Its translated sample point is represented exactly by rational
subtraction, so the concrete resolvent evaluator applies directly. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarHopping_eq_numerator (d : ℝ) :
    planarHopping d = planarHoppingNumerator d / (2 * ∫ r, planarResolventMode r ^ 2) := rfl

theorem planarHoppingNumerator_box (d : ℝ) :
    planarHoppingNumerator d = ∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1,
      planarHoppingIntegrand d (planarPairEquiv.symm (x, y)) := by
  unfold planarHoppingNumerator
  rw [planarPair_integral]
  let f := fun p : ℝ × ℝ => planarHoppingIntegrand d (planarPairEquiv.symm p)
  have hf : Continuous f := (planarHoppingIntegrand_continuous d).comp planarPairEquiv_symm_continuous
  have hi : IntegrableOn f (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1)
      ((volume : Measure ℝ).prod volume) :=
    hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hs : (∫ p, f p) = ∫ p in Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1, f p := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro p hp
    simp only [f, planarHoppingIntegrand, planarForcing_pair_zero hp, zero_mul]
  change (∫ p, f p) = _
  rw [hs, Measure.volume_eq_prod, setIntegral_prod f hi]
  simp_rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  rfl

theorem rationalPosition_shift_first (d a b : ℚ) :
    PlanarForcingProgram.position (a - d, b) =
      PlanarForcingProgram.position (a, b) - (d : ℝ) • planarAxis 0 := by
  ext i
  fin_cases i <;> simp [PlanarForcingProgram.position, planarAxis]

theorem rationalShift_norm_bound (d a b : ℚ) {R : ℝ}
    (hd : |(d : ℝ)| ≤ R)
    (ha : (a : ℝ) ∈ Set.Icc (-1 : ℝ) 1) (hb : (b : ℝ) ∈ Set.Icc (-1 : ℝ) 1) :
    ‖PlanarForcingProgram.position (a - d, b)‖ ≤ R + 2 := by
  rw [rationalPosition_shift_first]
  have hnorm : ‖PlanarForcingProgram.position (a, b)‖ ≤ 2 := by
    rw [rationalPosition_eq_pair]
    exact planarPair_norm_le_two ⟨ha, hb⟩
  have ht : ‖(d : ℝ) • planarAxis 0‖ ≤ R := by
    rw [norm_smul, Real.norm_eq_abs, planarAxis_zero_norm, mul_one]
    exact hd
  exact (norm_sub_le _ _).trans (by linarith)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactQuotientBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Stability of the actual contact quotient. A fixed natural guard for
the fixed positive normalization integral suffices for all inputs. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarHoppingNumerator_abs_le_four (d : ℝ) : |planarHoppingNumerator d| ≤ 4 := by
  rw [planarHoppingNumerator_box]
  have hpoint (a b : ℝ) :
      ‖planarHoppingIntegrand d (planarPairEquiv.symm (a, b))‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (planarHoppingIntegrand_nonnegative d _)]
    exact (mul_le_of_le_one_left (planarResolventMode_positive _).le
      (planarForcing_le_one _)).trans (planarResolventMode_le_one _)
  have hinner (a : ℝ) :
      ‖∫ b in (-1 : ℝ)..1, planarHoppingIntegrand d (planarPairEquiv.symm (a, b))‖ ≤ 2 := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun b => planarHoppingIntegrand d (planarPairEquiv.symm (a, b)))
      (a := (-1 : ℝ)) (b := 1) (C := 1) (fun b _ => hpoint a b)
    norm_num at h ⊢
    exact h
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun a => ∫ b in (-1 : ℝ)..1,
      planarHoppingIntegrand d (planarPairEquiv.symm (a, b)))
    (a := (-1 : ℝ)) (b := 1) (C := 2) (fun a _ => hinner a)
  norm_num at h ⊢
  exact h

theorem contactNormalizationGuard_positive : 0 < contactNormalizationGuard := by
  unfold contactNormalizationGuard
  omega

theorem contactNormalizationGuard_bound :
    2 ≤ (contactNormalizationGuard : ℝ) * (∫ r, planarResolventMode r ^ 2) := by
  have hp := planarResolventMode_square_integral_positive
  have hceil := Nat.le_ceil (2 / (∫ r, planarResolventMode r ^ 2))
  have hg : 2 / (∫ r, planarResolventMode r ^ 2) ≤ (contactNormalizationGuard : ℝ) := by
    unfold contactNormalizationGuard
    push_cast
    linarith
  exact (div_le_iff₀ hp).mp hg

theorem contact_quotient_error {C a a' b b' ε : ℝ}
    (hC : 1 ≤ C) (ha : 0 < a) (hguard : 2 ≤ C * a)
    (hε : 0 ≤ ε) (hsmall : C * ε ≤ 1)
    (hb : |b| ≤ 4) (hea : |a' - a| ≤ ε) (heb : |b' - b| ≤ ε) :
    |b' / (2 * a') - b / (2 * a)| ≤ 3 * C ^ 2 * ε := by
  have hC0 : 0 < C := by linarith
  have hlinear := mul_le_mul_of_nonneg_left (abs_le.mp hea).1 hC0.le
  have hga' : 1 ≤ C * a' := by nlinarith
  have ha' : 0 < a' := by
    by_contra hn
    have hn' := le_of_not_gt hn
    have hh := mul_nonpos_of_nonneg_of_nonpos hC0.le hn'
    linarith
  have hia : a⁻¹ ≤ C := (inv_le_iff_one_le_mul₀ ha).mpr (by linarith)
  have hia' : a'⁻¹ ≤ C := (inv_le_iff_one_le_mul₀ ha').mpr hga'
  have heq : b' / (2 * a') - b / (2 * a) =
      ((b' - b) * a'⁻¹ + b * (a - a') * a'⁻¹ * a⁻¹) / 2 := by
    field_simp [ha.ne', ha'.ne']
    ring
  have hfirst : |(b' - b) * a'⁻¹| ≤ ε * C := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr ha')]
    exact mul_le_mul heb hia' (inv_nonneg.mpr ha'.le) hε
  have hsecond : |b * (a - a') * a'⁻¹ * a⁻¹| ≤ 4 * ε * C ^ 2 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (inv_pos.mpr ha),
      abs_of_pos (inv_pos.mpr ha'), abs_sub_comm a a']
    calc
      _ ≤ 4 * ε * C * C := by gcongr
      _ = _ := by ring
  rw [heq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have htotal := (abs_add_le ((b' - b) * a'⁻¹) (b * (a - a') * a'⁻¹ * a⁻¹)).trans
    (add_le_add hfirst hsecond)
  have hCC : C ≤ C ^ 2 := by nlinarith
  have hmon := mul_le_mul_of_nonneg_left hCC hε
  apply (div_le_div_of_nonneg_right htotal (by norm_num)).trans
  nlinarith [mul_nonneg (sq_nonneg C) hε]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CubeMeasure
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The recursive quadrature integral is the actual product Lebesgue
integral on the cube. This identifies the six-coordinate computation with
the finite Coulomb box, rather than a separately defined integral. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb.UniformQuadrature

theorem cubeIntegral_eq_integral (n : ℕ) {a b : ℝ} (hab : a ≤ b)
    {f : (Fin n → ℝ) → ℝ} (hf : Integrable f (cubeMeasure a b n)) :
    cubeIntegral a b n f = ∫ x, f x ∂cubeMeasure a b n := by
  induction n with
  | zero =>
    have he : f = fun _ => f Fin.elim0 := funext (fun x => congrArg f (Subsingleton.elim x _))
    rw [he]
    simp [cubeIntegral, cubeMeasure, Measure.pi_empty_univ, measureReal_def]
  | succ n ih =>
    let μ : Measure ℝ := volume.restrict (Set.Icc a b)
    have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
    have hprod : Integrable (fun p : ℝ × (Fin n → ℝ) => f (Fin.cons p.1 p.2))
        (μ.prod (cubeMeasure a b n)) := by
      have ht := (hp.integrable_comp_emb
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm.measurableEmbedding).mpr hf
      simpa only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_zero', cubeMeasure, μ] using ht
    have hsplit : (∫ x, f x ∂cubeMeasure a b (n + 1)) =
        ∫ x, ∫ v, f (Fin.cons x v) ∂cubeMeasure a b n ∂μ := by
      change (∫ x, f x ∂Measure.pi (fun _ : Fin (n + 1) => μ)) = _
      rw [← hp.integral_comp']
      simpa only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_zero', cubeMeasure, μ] using integral_prod _ hprod
    rw [hsplit]
    change (∫ x in a..b, cubeIntegral a b n (fun v => f (Fin.cons x v))) = _
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    apply integral_congr_ae
    filter_upwards [hprod.prod_right_ae] with x hx
    exact ih hx

end ContinuumCoulomb.UniformQuadrature

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombCubeCoordinates
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Lebesgue coordinates for the two-particle finite Coulomb box. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb
open UniformQuadrature

theorem twoParticleCoordinates_fst (v : Fin 6 → ℝ) (i : Fin 3) :
    (twoParticleCoordinates v).1 i = v (i.castAdd 3) := by
  fin_cases i <;> rfl

theorem twoParticleCoordinates_snd (v : Fin 6 → ℝ) (i : Fin 3) :
    (twoParticleCoordinates v).2 i = v (i.natAdd 3) := by
  fin_cases i <;> rfl

theorem slabDomain_cube (L : ℝ) : slabDomain L L = coulombNumericalBox L := by
  ext x
  simp only [slabDomain, coulombNumericalBox, Set.mem_ofPred_eq, Set.mem_iInter]
  constructor
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i <;> assumption
  · intro h
    exact ⟨h 0, h 1, h 2⟩

theorem twoParticleCoordinates_measurePreserving (L : ℝ) :
    MeasurePreserving twoParticleCoordinates (cubeMeasure (-L) L 6)
      (volume.restrict (coulombNumericalBox L ×ˢ coulombNumericalBox L)) := by
  let μ : Measure ℝ := volume.restrict (Set.Icc (-L) L)
  have hindex := measurePreserving_piCongrLeft (fun _ : Fin 3 ⊕ Fin 3 => μ)
    (finSumFinEquiv (m := 3) (n := 3)).symm
  have hsplit := measurePreserving_sumPiEquivProdPi (fun _ : Fin 3 ⊕ Fin 3 => μ)
  have hcube : cubeMeasure (-L) L 3 = slabProductMeasure L L := by
    unfold cubeMeasure slabProductMeasure slabAxisMeasure
    congr 1
    funext i
    simp only [slabSide, ite_self]
  have hslot : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))
      (cubeMeasure (-L) L 3) (volume.restrict (coulombNumericalBox L)) := by
    rw [hcube, ← slabDomain_cube]
    exact slabProduct_measurePreserving L L
  have h := (hslot.prod hslot).comp (hsplit.comp hindex)
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at h
  exact h

theorem localizedRawCoulombBox_cube {freq ε L : ℝ}
    (hf : 0 < freq) (hε : 0 < ε) (hL : 0 ≤ L) (u : PlanarPosition) :
    localizedRawCoulombBox freq ε L u = cubeIntegral (-L) L 6
      (fun v => cappedPairIntegrand ε (planarCenter u)
        (localizedRawDensity freq) (localizedRawDensity freq) (twoParticleCoordinates v)) := by
  let f := cappedPairIntegrand ε (planarCenter u)
    (localizedRawDensity freq) (localizedRawDensity freq)
  have hfi : Integrable f := cappedPairIntegrand_integrable hε (planarCenter u)
    (localizedRawDensity_integrable hf) (localizedRawDensity_integrable hf)
  have hp := twoParticleCoordinates_measurePreserving L
  have hcomp : Integrable (fun v => f (twoParticleCoordinates v)) (cubeMeasure (-L) L 6) :=
    (hp.integrable_comp_emb twoParticleCoordinates.measurableEmbedding).mpr hfi.restrict
  rw [cubeIntegral_eq_integral 6 (by linarith) hcomp]
  exact (hp.integral_comp' f).symm

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombCubeModulus
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinatewise Lipschitz control of the actual Coulomb box integrand. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb
open UniformQuadrature

theorem position_norm_le_sum_abs (x : Position) : ‖x‖ ≤ ∑ i, |x i| := by
  apply (sq_le_sq₀ (norm_nonneg x) (Finset.sum_nonneg (fun i _ => abs_nonneg (x i)))).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  simpa only [sq_abs] using
    (Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun i : Fin 3 => |x i|)
      (fun i _ => abs_nonneg (x i)))

theorem twoParticleCoordinates_sum_abs (v w : Fin 6 → ℝ) :
    (∑ i : Fin 3, |(twoParticleCoordinates v).1 i - (twoParticleCoordinates w).1 i|) +
      (∑ i : Fin 3, |(twoParticleCoordinates v).2 i - (twoParticleCoordinates w).2 i|) =
        ∑ i : Fin 6, |v i - w i| := by
  simp only [twoParticleCoordinates_fst, twoParticleCoordinates_snd]
  exact (Fin.sum_univ_add (a := 3) (b := 3) (fun i : Fin 6 => |v i - w i|)).symm

theorem rawCoulombSix_modulus {freq ε L : ℝ} (hf : 0 ≤ freq) (hε : 0 < ε)
    (hL : 0 ≤ L) (shift : Position) :
    cubeModulus (-L) L ((64 + 2 * freq * L) * ε⁻¹ + ε⁻¹ ^ 2)
      (rawCoulombSix freq ε shift) := by
  intro v hv w hw
  have hv0 : |(positionSplitCoordinates (twoParticleCoordinates v).1).2| ≤ L := by
    change |(twoParticleCoordinates v).1 2| ≤ L
    rw [twoParticleCoordinates_fst]
    exact abs_le.mpr (hv _)
  have hv1 : |(positionSplitCoordinates (twoParticleCoordinates v).2).2| ≤ L := by
    change |(twoParticleCoordinates v).2 2| ≤ L
    rw [twoParticleCoordinates_snd]
    exact abs_le.mpr (hv _)
  have hw0 : |(positionSplitCoordinates (twoParticleCoordinates w).1).2| ≤ L := by
    change |(twoParticleCoordinates w).1 2| ≤ L
    rw [twoParticleCoordinates_fst]
    exact abs_le.mpr (hw _)
  have hw1 : |(positionSplitCoordinates (twoParticleCoordinates w).2).2| ≤ L := by
    change |(twoParticleCoordinates w).2 2| ≤ L
    rw [twoParticleCoordinates_snd]
    exact abs_le.mpr (hw _)
  have ht := cappedRawPair_modulus hf hε shift
    (twoParticleCoordinates v).1 (twoParticleCoordinates v).2
    (twoParticleCoordinates w).1 (twoParticleCoordinates w).2 hv0 hv1 hw0 hw1
  apply ht.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hx := position_norm_le_sum_abs ((twoParticleCoordinates v).1 - (twoParticleCoordinates w).1)
  have hy := position_norm_le_sum_abs ((twoParticleCoordinates v).2 - (twoParticleCoordinates w).2)
  simpa only [PiLp.sub_apply, twoParticleCoordinates_sum_abs] using add_le_add hx hy

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_RationalRectangleProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal two-coordinate rational quadrature. The same mesh in both
coordinates is enough for the normalization and compact contact integrals. -/

namespace ContinuumCoulomb.RationalRectangleProgram
open ExactQuantumFactoring.BitStackProgram

variable {E : Type}

theorem value_cast (evaluate : E → ℚ → ℚ → ℚ) (x : Input E) :
    (value evaluate x : ℝ) =
      UniformQuadrature.rectangleSum (x.2.2.2 : ℝ) (x.2.2.2 : ℝ) x.1 x.1
        (fun i j => (evaluate x.2.1
          (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 i)
          (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 j) : ℝ)) := by
  simp [value, outerInput, line, lineInput, RationalQuadratureProgram.value,
    RationalQuadratureProgram.sample, UniformQuadrature.rectangleSum, UniformQuadrature.sampleSum]

end ContinuumCoulomb.RationalRectangleProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RationalSixQuadrature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Six-coordinate rational cubature, as three literal rectangle programs.
The same finite mesh is retained in each register environment. -/

namespace ContinuumCoulomb.RationalSixQuadrature
open ExactQuantumFactoring.BitStackProgram

variable {E : Type}


theorem value_cast (f : Evaluator E) (x : Input E) :
    (value f x : ℝ) =
      UniformQuadrature.rectangleSum (x.2.2.2 : ℝ) (x.2.2.2 : ℝ) x.1 x.1 (fun i j =>
        UniformQuadrature.rectangleSum (x.2.2.2 : ℝ) (x.2.2.2 : ℝ) x.1 x.1 (fun k l =>
          UniformQuadrature.rectangleSum (x.2.2.2 : ℝ) (x.2.2.2 : ℝ) x.1 x.1 (fun m n =>
            (f x.2.1
              (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 i)
              (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 j)
              (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 k)
              (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 l)
              (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 m)
              (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 n) : ℝ)))) := by
  simp only [value, outer, middle, inner, remember, augment,
    RationalRectangleProgram.value_cast]

end ContinuumCoulomb.RationalSixQuadrature

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_NumericalSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Squaring a computed value is uniformly stable on the range of the
constructed planar resolvent. -/

namespace ContinuumCoulomb

theorem unitInterval_square_error {a b ε : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hε : ε ≤ 1) (herr : |a - b| ≤ ε) : |a ^ 2 - b ^ 2| ≤ 3 * ε := by
  have he0 : 0 ≤ ε := (abs_nonneg _).trans herr
  have ha : |a| ≤ 2 := by
    have h := abs_add_le (a - b) b
    rw [sub_add_cancel, abs_of_nonneg hb0] at h
    linarith
  have hs : |a + b| ≤ 3 := (abs_add_le a b).trans (by
    rw [abs_of_nonneg hb0]
    linarith)
  rw [show a ^ 2 - b ^ 2 = (a - b) * (a + b) by ring, abs_mul]
  calc
    _ ≤ ε * 3 := mul_le_mul herr hs (abs_nonneg _) he0
    _ = _ := by ring

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RationalClamp
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal rational clamp preserves approximation error to values in
[0,1]. It keeps numerical density samples nonnegative and bounded. -/

namespace ContinuumCoulomb
open ExactQuantumFactoring.BitStackProgram

theorem rationalUnitClamp_nonnegative (q : ℚ) : 0 ≤ rationalUnitClamp q :=
  le_max_left _ _

theorem rationalUnitClamp_le_one (q : ℚ) : rationalUnitClamp q ≤ 1 :=
  max_le (by norm_num) (min_le_left _ _)

theorem rationalUnitClamp_error (q : ℚ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    |(rationalUnitClamp q : ℝ) - r| ≤ |(q : ℝ) - r| := by
  by_cases hq0 : q < 0
  · have hq : (q : ℝ) < 0 := by exact_mod_cast hq0
    have he : rationalUnitClamp q = 0 := by
      unfold rationalUnitClamp
      rw [min_eq_right (by linarith), max_eq_left hq0.le]
    rw [he, Rat.cast_zero, zero_sub, abs_neg, abs_of_nonneg hr0,
      abs_of_nonpos (by linarith : (q : ℝ) - r ≤ 0)]
    linarith
  · by_cases hq1 : 1 < q
    · have hq : (1 : ℝ) < q := by exact_mod_cast hq1
      have he : rationalUnitClamp q = 1 := by
        unfold rationalUnitClamp
        rw [min_eq_left hq1.le, max_eq_right (by norm_num)]
      rw [he, Rat.cast_one, abs_of_nonneg (by linarith : 0 ≤ 1 - r),
        abs_of_nonneg (by linarith : 0 ≤ (q : ℝ) - r)]
      linarith
    · have he : rationalUnitClamp q = q := by
        unfold rationalUnitClamp
        rw [min_eq_right (le_of_not_gt hq1), max_eq_right (le_of_not_gt hq0)]
      rw [he]

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarHeatTimeModulus
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete time modulus for the actual planar heat average, obtained
by integrating the pointwise density modulus over the fixed square. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarHeatTime_lipschitz (r : PlanarPosition) {η t s : ℝ}
    (hη : 0 < η) (ht : η ≤ t) (hs : η ≤ s) :
    |Real.exp (-t) * planarHeatAverage t r - Real.exp (-s) * planarHeatAverage s r| ≤
      4 * planarBoxTimeConstant r η * |t - s| := by
  let f := fun u x y => HeatKernelModulus.density r u (planarPairEquiv.symm (x, y))
  have hsec (u : ℝ) (hu : η ≤ u) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
      ContinuousOn (f u x) (Set.Icc (-1 : ℝ) 1) := by
    apply UniformQuadrature.continuousOn_of_abs_sub_le
    intro y hy y' hy'
    exact planarBox_spatial_second r hη hu hx hy hy'
  have houter (u : ℝ) (hu : η ≤ u) :
      ContinuousOn (fun x => ∫ y in (-1 : ℝ)..1, f u x y) (Set.Icc (-1 : ℝ) 1) := by
    apply UniformQuadrature.continuousOn_of_abs_sub_le
    intro x hx x' hx'
    have h := UniformQuadrature.integral_parameter_lipschitz (f u) (by norm_num : (-1 : ℝ) ≤ 1)
      (hsec u hu) (by
        intro z hz z' hz' y hy
        exact planarBox_spatial_first r hη hu hz hz' hy) hx hx'
    convert h using 1
    all_goals try with_reducible_and_instances rfl
  have hinner (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
      |(∫ y in (-1 : ℝ)..1, f t x y) - ∫ y in (-1 : ℝ)..1, f s x y| ≤
        2 * planarBoxTimeConstant r η * |t - s| := by
    rw [← intervalIntegral.integral_sub
      ((hsec t ht x hx).intervalIntegrable_of_Icc (by norm_num))
      ((hsec s hs x hx).intervalIntegrable_of_Icc (by norm_num))]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun y => f t x y - f s x y) (a := -1) (b := 1)
      (C := planarBoxTimeConstant r η * |t - s|) (by
        intro y hy
        have hy' : y ∈ Set.Icc (-1 : ℝ) 1 := by
          have hy'' : y ∈ Set.Ioc (-1 : ℝ) 1 := by
            simpa only [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hy
          exact ⟨hy''.1.le, hy''.2⟩
        simpa only [Real.norm_eq_abs] using planarBox_time r hη ht hs hx hy')
    rw [show (1 : ℝ) - -1 = 2 by norm_num,
      abs_of_pos (by norm_num : (0 : ℝ) < 2), Real.norm_eq_abs] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  rw [planarHeatResolvent_box, planarHeatResolvent_box]
  change |(∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, f t x y) -
    ∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, f s x y| ≤ _
  rw [← intervalIntegral.integral_sub
    ((houter t ht).intervalIntegrable_of_Icc (by norm_num))
    ((houter s hs).intervalIntegrable_of_Icc (by norm_num))]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun x => (∫ y in (-1 : ℝ)..1, f t x y) - ∫ y in (-1 : ℝ)..1, f s x y)
    (a := -1) (b := 1) (C := 2 * planarBoxTimeConstant r η * |t - s|) (by
      intro x hx
      have hx' : x ∈ Set.Icc (-1 : ℝ) 1 := by
        have hx'' : x ∈ Set.Ioc (-1 : ℝ) 1 := by
          simpa only [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx
        exact ⟨hx''.1.le, hx''.2⟩
      simpa only [Real.norm_eq_abs] using hinner x hx')
  rw [show (1 : ℝ) - -1 = 2 by norm_num,
    abs_of_pos (by norm_num : (0 : ℝ) < 2), Real.norm_eq_abs] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarHeatTruncation
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit time truncation for the actual resolvent representation.
The omitted short-time interval costs at most its length; the long-time
tail is at most the elementary exponential tail. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarHeatTime_nonnegative (r : PlanarPosition) {t : ℝ} (ht : 0 < t) :
    0 ≤ Real.exp (-t) * planarHeatAverage t r :=
  mul_nonneg (Real.exp_pos _).le (planarHeatAverage_positive ht r).le

theorem planarHeatTime_le_exp (r : PlanarPosition) {t : ℝ} (ht : 0 < t) :
    Real.exp (-t) * planarHeatAverage t r ≤ Real.exp (-t) :=
  mul_le_of_le_one_right (Real.exp_pos _).le (planarHeatAverage_le_one ht r)

theorem planarHeatTime_short (r : PlanarPosition) {η : ℝ} (hη : 0 ≤ η) :
    |∫ t in (0 : ℝ)..η, Real.exp (-t) * planarHeatAverage t r| ≤ η := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t => Real.exp (-t) * planarHeatAverage t r) (a := 0) (b := η) (C := 1)
    (by
      intro t ht
      have ht' : t ∈ Set.Ioc (0 : ℝ) η := by simpa only [Set.uIoc_of_le hη] using ht
      rw [Real.norm_eq_abs, abs_of_nonneg (planarHeatTime_nonnegative r ht'.1)]
      exact (planarHeatTime_le_exp r ht'.1).trans
        (Real.exp_le_one_iff.mpr (by linarith [ht'.1])))
  simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hη, one_mul] using h

theorem planarHeatTime_tail (r : PlanarPosition) {T : ℝ} (hT : 0 ≤ T) :
    |∫ t in Set.Ioi T, Real.exp (-t) * planarHeatAverage t r| ≤ Real.exp (-T) := by
  have hn : 0 ≤ ∫ t in Set.Ioi T, Real.exp (-t) * planarHeatAverage t r :=
    integral_nonneg_of_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact planarHeatTime_nonnegative r (lt_of_le_of_lt hT ht))
  rw [abs_of_nonneg hn]
  have hi := (planarResolventMode_heat_integrable r).mono_set (Set.Ioi_subset_Ioi hT)
  have he : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Set.Ioi T) := by
    simpa only [neg_mul, one_mul] using exp_neg_integrableOn_Ioi T (by norm_num : (0 : ℝ) < 1)
  have hb := integral_mono_ae hi he (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact planarHeatTime_le_exp r (lt_of_le_of_lt hT ht))
  have ht : (∫ t in Set.Ioi T, Real.exp (-t)) = Real.exp (-T) := by
    simpa using integral_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) T
  exact hb.trans_eq ht

theorem planarTruncatedHeat_error (r : PlanarPosition) {η T : ℝ}
    (hη : 0 ≤ η) (hηT : η ≤ T) :
    |planarResolventMode r - planarTruncatedHeat r η T| ≤ η + Real.exp (-T) := by
  let f := fun t => Real.exp (-t) * planarHeatAverage t r
  have hi : IntegrableOn f (Set.Ioi 0) := planarResolventMode_heat_integrable r
  have hηi : IntegrableOn f (Set.Ioi η) := hi.mono_set (Set.Ioi_subset_Ioi hη)
  have hT : 0 ≤ T := hη.trans hηT
  have hfirst := intervalIntegral.integral_Ioi_sub_Ioi hi hη
  have hsecond := intervalIntegral.integral_Ioi_sub_Ioi hηi hηT
  have heq : planarResolventMode r - planarTruncatedHeat r η T =
      (∫ t in (0 : ℝ)..η, f t) + ∫ t in Set.Ioi T, f t := by
    rw [planarResolventMode_heat_representation]
    unfold planarTruncatedHeat
    change (∫ t in Set.Ioi 0, f t) - (∫ t in η..T, f t) = _
    linarith
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add (planarHeatTime_short r hη) (planarHeatTime_tail r hT))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RationalHeatPlaneError
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Error of the actual rational two-coordinate heat quadrature.
The sample evaluator is the concrete Taylor/π/forcing program. -/

namespace ContinuumCoulomb.RationalHeatBox

theorem spatialEndpoint (N : ℕ) (hN : 0 < N) : spatialNode N N = 1 := by
  have hn : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold spatialNode RationalQuadratureProgram.node spatialStep
  field_simp
  ring

theorem spatialNode_mem (N i : ℕ) (hN : 0 < N) (hi : i ≤ N) :
    (spatialNode N i : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by
  have hh : 0 ≤ (spatialStep N : ℝ) := by unfold spatialStep; positivity
  have h := UniformQuadrature.node_mem (a := (-1 : ℝ)) hh hi
  have hend : UniformQuadrature.node (-1 : ℝ) (spatialStep N : ℝ) N = 1 := by
    have hc := RationalQuadratureProgram.node_cast (-1) (spatialStep N) N
    norm_num only [Rat.cast_neg, Rat.cast_one] at hc
    rw [← hc]
    exact_mod_cast spatialEndpoint N hN
  simpa only [spatialNode, RationalQuadratureProgram.node_cast, Rat.cast_neg, Rat.cast_one,
    hend] using h

theorem plane_cast (e : Settings) (t : ℚ) :
    (plane e t : ℝ) =
      UniformQuadrature.rectangleSum (spatialStep e.2.2 : ℝ) (spatialStep e.2.2 : ℝ) e.2.2 e.2.2
        (fun i j => (RationalHeatSample.value
          (e.1, t, e.2.1, spatialNode e.2.2 i, spatialNode e.2.2 j) : ℝ)) := by
  simp [plane, planeInput, line, lineInput, sample, RationalQuadratureProgram.value,
    RationalQuadratureProgram.sample, spatialNode, spatialStep,
    UniformQuadrature.rectangleSum, UniformQuadrature.sampleSum]

theorem plane_error (e : Settings) (t : ℚ) {η : ℝ}
    (hη : 0 < η) (ht : η ≤ (t : ℝ)) (hN : 0 < e.2.2) (hpi : 0 < e.1.2.2)
    (hM : ∀ i < e.2.2, ∀ j < e.2.2,
      |(RationalHeatSample.exponent (t, e.2.1, spatialNode e.2.2 i, spatialNode e.2.2 j) : ℝ)|
        ≤ e.1.1) :
    |(plane e t : ℝ) - Real.exp (-(t : ℝ)) * planarHeatAverage t
      (PlanarForcingProgram.position e.2.1)| ≤
      4 * (2 * planarBoxSpatialConstant (PlanarForcingProgram.position e.2.1) η *
        (spatialStep e.2.2 : ℝ) +
        ((2 ^ e.1.2.1 : ℝ)⁻¹ + 8 / (e.1.2.2 : ℝ)) / (4 * η)) := by
  let r := PlanarForcingProgram.position e.2.1
  let L := planarBoxSpatialConstant r η
  let δ := ((2 ^ e.1.2.1 : ℝ)⁻¹ + 8 / (e.1.2.2 : ℝ)) / (4 * η)
  let f := fun x y => HeatKernelModulus.density r t (planarPairEquiv.symm (x, y))
  let v := fun i j => (RationalHeatSample.value
    (e.1, t, e.2.1, spatialNode e.2.2 i, spatialNode e.2.2 j) : ℝ)
  have hh : 0 ≤ (spatialStep e.2.2 : ℝ) := by unfold spatialStep; positivity
  have hL : 0 ≤ L := by dsimp [L, planarBoxSpatialConstant]; positivity
  have hend : UniformQuadrature.node (-1 : ℝ) (spatialStep e.2.2 : ℝ) e.2.2 = 1 := by
    have hc := RationalQuadratureProgram.node_cast (-1) (spatialStep e.2.2) e.2.2
    norm_num only [Rat.cast_neg, Rat.cast_one] at hc
    rw [← hc]
    exact_mod_cast spatialEndpoint e.2.2 hN
  have hLipX : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ x' ∈ Set.Icc (-1 : ℝ) 1,
      ∀ y ∈ Set.Icc (-1 : ℝ) 1, |f x y - f x' y| ≤ L * |x - x'| := by
    intro x hx x' hx' y hy
    exact planarBox_spatial_first r hη ht hx hx' hy
  have hLipY : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1,
      ∀ y' ∈ Set.Icc (-1 : ℝ) 1, |f x y - f x y'| ≤ L * |y - y'| := by
    intro x hx y hy y' hy'
    exact planarBox_spatial_second r hη ht hx hy hy'
  have hsample : ∀ i < e.2.2, ∀ j < e.2.2,
      |v i j - f (UniformQuadrature.node (-1) (spatialStep e.2.2 : ℝ) i)
        (UniformQuadrature.node (-1) (spatialStep e.2.2 : ℝ) j)| ≤ δ := by
    intro i hi j hj
    have h := RationalHeatSample.error_density_uniform
      (e.1, t, e.2.1, spatialNode e.2.2 i, spatialNode e.2.2 j) hη ht hpi (hM i hi j hj)
    dsimp only [v, f, r, δ]
    simpa only [rationalPosition_eq_pair, spatialNode, RationalQuadratureProgram.node_cast,
      Rat.cast_neg, Rat.cast_one] using h
  have h := UniformQuadrature.rectangle_error f v (-1) (spatialStep e.2.2 : ℝ) e.2.2
    (-1) (spatialStep e.2.2 : ℝ) e.2.2 hh hh hL hL
    (by simpa only [hend] using hLipX) (by simpa only [hend] using hLipY) hsample
  have hlen : (e.2.2 : ℝ) * (spatialStep e.2.2 : ℝ) = 2 := by
    have hn : (e.2.2 : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    simp only [spatialStep, Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast]
    field_simp
  rw [hend, hlen] at h
  rw [plane_cast, planarHeatResolvent_box]
  change |UniformQuadrature.rectangleSum _ _ _ _ v - ∫ x in (-1 : ℝ)..1,
    ∫ y in (-1 : ℝ)..1, f x y| ≤ _
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem plane_error_of_magnitude (e : Settings) (t : ℚ) {η : ℝ}
    (hη : 0 < η) (ht : η ≤ (t : ℝ)) (hN : 0 < e.2.2) (hpi : 0 < e.1.2.2)
    (hM : (t : ℝ) + (‖PlanarForcingProgram.position e.2.1‖ + 2) ^ 2 / (4 * η) ≤ e.1.1) :
    |(plane e t : ℝ) - Real.exp (-(t : ℝ)) * planarHeatAverage t
      (PlanarForcingProgram.position e.2.1)| ≤
      4 * (2 * planarBoxSpatialConstant (PlanarForcingProgram.position e.2.1) η *
        (spatialStep e.2.2 : ℝ) +
        ((2 ^ e.1.2.1 : ℝ)⁻¹ + 8 / (e.1.2.2 : ℝ)) / (4 * η)) := by
  apply plane_error e t hη ht hN hpi
  intro i hi j hj
  exact (RationalHeatSample.exponent_abs_le _ hη ht le_rfl
    (spatialNode_mem _ _ hN hi.le) (spatialNode_mem _ _ hN hj.le)).trans hM

end ContinuumCoulomb.RationalHeatBox

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RationalResolventError
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual computed three-dimensional heat quadrature approximates
the constructed planar resolvent. The bound includes both numerical
quadrature and the explicitly proved short/long-time tails. -/

noncomputable section
namespace ContinuumCoulomb.RationalHeatBox

theorem resolvent_error (x : Input)
    (hη : 0 < (x.2.2.1 : ℝ)) (hh : 0 ≤ (x.2.2.2 : ℝ))
    (hN : 0 < x.2.1.2.2) (hpi : 0 < x.2.1.1.2.2)
    (hM : (timeEndpoint x : ℝ) +
      (‖PlanarForcingProgram.position x.2.1.2.1‖ + 2) ^ 2 / (4 * (x.2.2.1 : ℝ)) ≤ x.2.1.1.1) :
    |(value x : ℝ) - planarResolventMode (PlanarForcingProgram.position x.2.1.2.1)| ≤
      resolventErrorBound x := by
  let r := PlanarForcingProgram.position x.2.1.2.1
  let η := (x.2.2.1 : ℝ)
  let h := (x.2.2.2 : ℝ)
  let T := (timeEndpoint x : ℝ)
  let f := fun t => Real.exp (-t) * planarHeatAverage t r
  have hT : T = UniformQuadrature.node η h x.1 :=
    RationalQuadratureProgram.node_cast _ _ _
  have hηT : η ≤ T := by rw [hT]; exact (UniformQuadrature.node_mem hh (Nat.le_refl x.1)).1
  have hL : 0 ≤ 4 * planarBoxTimeConstant r η := by
    dsimp [planarBoxTimeConstant, η]
    positivity
  have hLip : ∀ t ∈ Set.Icc η (UniformQuadrature.node η h x.1),
      ∀ s ∈ Set.Icc η (UniformQuadrature.node η h x.1),
      |f t - f s| ≤ (4 * planarBoxTimeConstant r η) * |t - s| := by
    intro t ht s hs
    exact planarHeatTime_lipschitz r hη ht.1 hs.1
  have hSample : ∀ i < x.1,
      |(plane x.2.1 (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 i) : ℝ) -
        f (UniformQuadrature.node η h i)| ≤ planeErrorBound x.2.1 η := by
    intro i hi
    have htmem := UniformQuadrature.node_mem (a := η) hh hi.le
    have htmem' : (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 i : ℝ) ∈ Set.Icc η T := by
      rw [RationalQuadratureProgram.node_cast, hT]
      exact htmem
    have hm : (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 i : ℝ) +
        (‖r‖ + 2) ^ 2 / (4 * η) ≤ x.2.1.1.1 := by
      linarith [htmem'.2, hM]
    have hp := plane_error_of_magnitude x.2.1
      (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 i) hη htmem'.1 hN hpi hm
    dsimp only [f, r, η, h, planeErrorBound]
    simpa only [RationalQuadratureProgram.node_cast] using hp
  have hQuad := UniformQuadrature.samples_error_lipschitz f
    (fun i => (plane x.2.1 (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 i) : ℝ))
    η h x.1 hh hL hLip hSample
  have hQuad' : |(value x : ℝ) - planarTruncatedHeat r η T| ≤
      (x.1 : ℝ) * (4 * planarBoxTimeConstant r η * h ^ 2 + h * planeErrorBound x.2.1 η) := by
    rw [value, RationalQuadratureProgram.value_cast]
    rw [← hT] at hQuad
    exact hQuad
  have hTail : |planarTruncatedHeat r η T - planarResolventMode r| ≤ η + Real.exp (-T) := by
    rw [abs_sub_comm]
    exact planarTruncatedHeat_error r hη.le hηT
  calc
    _ = |((value x : ℝ) - planarTruncatedHeat r η T) +
        (planarTruncatedHeat r η T - planarResolventMode r)| := by congr 1; ring
    _ ≤ |(value x : ℝ) - planarTruncatedHeat r η T| +
        |planarTruncatedHeat r η T - planarResolventMode r| := abs_add_le _ _
    _ ≤ (x.1 : ℝ) * (4 * planarBoxTimeConstant r η * h ^ 2 + h * planeErrorBound x.2.1 η) +
        (η + Real.exp (-T)) := add_le_add hQuad' hTail
    _ = _ := by dsimp [resolventErrorBound, r, η, h, T]; ring

end ContinuumCoulomb.RationalHeatBox

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ResolventSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial-sized mesh and precision choices for the resolvent
quadrature. The radius and requested inverse accuracy are unary inputs. -/

namespace ContinuumCoulomb.ResolventSchedule
open ExactQuantumFactoring.BitStackProgram

theorem scale_positive (P : ℕ) : 0 < scale P := by unfold scale; omega

theorem count_positive (R P : ℕ) : 0 < count R P := by
  have hscale := scale_positive P
  unfold count countPrefix
  positivity

end ContinuumCoulomb.ResolventSchedule

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ResolventNumericalBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary quantitative bounds for the fixed polynomial schedule.
These estimates keep all mesh choices explicit. -/

noncomputable section
namespace ContinuumCoulomb.ResolventSchedule

theorem succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    omega

theorem taylor_precision_bound (Q : ℕ) (hQ : 1 ≤ Q) :
    (Q : ℝ) ^ 2 * (2 ^ (4 * Q) : ℝ)⁻¹ ≤ (Q : ℝ)⁻¹ := by
  have hn : Q ^ 3 ≤ 2 ^ (4 * Q) := by
    calc
      Q ^ 3 ≤ Q ^ 4 := pow_le_pow_right₀ hQ (by norm_num)
      _ ≤ (Q + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
      _ ≤ (2 ^ Q) ^ 4 := Nat.pow_le_pow_left (succ_le_two_pow Q) 4
      _ = 2 ^ (4 * Q) := by rw [← pow_mul]; congr 1; omega
  have hQr : (0 : ℝ) < Q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hQ)
  have hnr : (Q : ℝ) ^ 3 ≤ 2 ^ (4 * Q) := by exact_mod_cast hn
  have hp : (0 : ℝ) < 2 ^ (4 * Q) := by positivity
  apply (mul_le_mul_iff_left₀ hQr).mp
  rw [inv_mul_cancel₀ hQr.ne']
  calc
    (Q : ℝ) ^ 2 * (2 ^ (4 * Q) : ℝ)⁻¹ * Q = Q ^ 3 / (2 ^ (4 * Q) : ℝ) := by ring
    _ ≤ 1 := (div_le_one hp).mpr hnr

theorem exp_tail_le_inverse {Q : ℝ} (hQ : 0 < Q) : Real.exp (-Q) ≤ Q⁻¹ := by
  rw [Real.exp_neg]
  exact inv_anti₀ hQ (by linarith [Real.add_one_le_exp Q])

theorem mesh_fraction_bound {A Q : ℝ} (hA : 1 ≤ A) (hQ : 1 ≤ Q) :
    (4 * A ^ 2 * Q ^ 5 + 192 * A * Q ^ 3 + 8 * Q ^ 2) /
      (4096 * A ^ 4 * Q ^ 8) ≤ Q⁻¹ := by
  have hA0 : 0 < A := by linarith
  have hQ0 : 0 < Q := by linarith
  have hN : 0 < 4096 * A ^ 4 * Q ^ 8 := by positivity
  have h₂ : A ^ 2 * Q ^ 6 ≤ A ^ 4 * Q ^ 8 :=
    mul_le_mul (pow_le_pow_right₀ hA (by norm_num)) (pow_le_pow_right₀ hQ (by norm_num))
      (by positivity) (by positivity)
  have h₁ : A * Q ^ 4 ≤ A ^ 4 * Q ^ 8 := by
    have ha : A ≤ A ^ 4 := by simpa using pow_le_pow_right₀ hA (show 1 ≤ 4 by norm_num)
    exact mul_le_mul ha (pow_le_pow_right₀ hQ (by norm_num)) (by positivity) (by positivity)
  have h₀ : Q ^ 3 ≤ A ^ 4 * Q ^ 8 := by
    calc
      Q ^ 3 ≤ Q ^ 8 := pow_le_pow_right₀ hQ (by norm_num)
      _ ≤ A ^ 4 * Q ^ 8 := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hA)
  have hn : (4 * A ^ 2 * Q ^ 5 + 192 * A * Q ^ 3 + 8 * Q ^ 2) * Q ≤
      4096 * A ^ 4 * Q ^ 8 := by
    calc
      _ = 4 * (A ^ 2 * Q ^ 6) + 192 * (A * Q ^ 4) + 8 * Q ^ 3 := by ring
      _ ≤ 204 * (A ^ 4 * Q ^ 8) := by linarith
      _ ≤ _ := by nlinarith [show 0 ≤ A ^ 4 * Q ^ 8 by positivity]
  calc
    _ ≤ ((4096 * A ^ 4 * Q ^ 8) / Q) / (4096 * A ^ 4 * Q ^ 8) :=
      div_le_div_of_nonneg_right ((le_div_iff₀ hQ0).mpr hn) hN.le
    _ = Q⁻¹ := by field_simp

theorem spatial_constant_bound (r : PlanarPosition) {R Q : ℝ}
    (hR : ‖r‖ ≤ R) (hQ : 1 ≤ Q) :
    planarBoxSpatialConstant r Q⁻¹ ≤ 12 * (R + 3) * Q ^ 2 := by
  have hR0 : 0 ≤ R := (norm_nonneg r).trans hR
  have hQsq : Q ≤ Q ^ 2 := by nlinarith
  have hmain := mul_le_mul_of_nonneg_right (show 2 * (‖r‖ + 2) ≤ 2 * (R + 2) by linarith)
    (sq_nonneg Q)
  have hnonneg := mul_nonneg hR0 (sq_nonneg Q)
  simp only [planarBoxSpatialConstant, inv_inv, inv_pow, div_inv_eq_mul]
  nlinarith

theorem time_constant_bound (r : PlanarPosition) {R Q : ℝ}
    (hR : ‖r‖ ≤ R) (hQ : 1 ≤ Q) :
    planarBoxTimeConstant r Q⁻¹ ≤ (R + 3) ^ 2 * Q ^ 3 := by
  have hR0 : 0 ≤ R := (norm_nonneg r).trans hR
  have hQ0 : 0 ≤ Q := by linarith
  have hQ2 : Q ^ 2 ≤ Q ^ 3 := by nlinarith
  have hQ1 : Q ≤ Q ^ 3 := by nlinarith
  have hsquare : (‖r‖ + 2) ^ 2 ≤ (R + 2) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr (by linarith)
  have hc : 2 + (‖r‖ + 2) ^ 2 / 4 ≤ (R + 3) ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hc (show 0 ≤ Q ^ 3 by positivity)
  have hQne : Q ≠ 0 := by linarith
  have heq : planarBoxTimeConstant r Q⁻¹ =
      Q ^ 2 + Q + (‖r‖ + 2) ^ 2 * Q ^ 3 / 4 := by
    unfold planarBoxTimeConstant
    field_simp [hQne]
    ring
  rw [heq]
  nlinarith

theorem scalar_error_bound {A Q N w Lt Ls e : ℝ}
    (hA : 1 ≤ A) (hQ : 1 ≤ Q) (hN : N = 4096 * A ^ 4 * Q ^ 8)
    (hw0 : 0 ≤ w) (hw : w ≤ Q)
    (hLt : Lt ≤ A ^ 2 * Q ^ 3) (hLs : Ls ≤ 12 * A * Q ^ 2)
    (he0 : 0 ≤ e) (he : Q ^ 2 * e ≤ Q⁻¹) :
    N * (4 * Lt * (w / N) ^ 2 + (w / N) *
      (4 * (2 * Ls * (2 / N) + (e + 8 / N) / (4 * Q⁻¹)))) +
      Q⁻¹ + Real.exp (-Q) ≤ 4 * Q⁻¹ := by
  have hQ0 : 0 < Q := by linarith
  have hA0 : 0 < A := by linarith
  have hN0 : 0 < N := by rw [hN]; positivity
  have hw2 : w ^ 2 ≤ Q ^ 2 := (sq_le_sq₀ hw0 hQ0.le).mpr hw
  have h₁ := mul_le_mul hLt hw2 (sq_nonneg w) (show 0 ≤ A ^ 2 * Q ^ 3 by positivity)
  have h₂ := mul_le_mul hLs hw hw0 (show 0 ≤ 12 * A * Q ^ 2 by positivity)
  have h₃ := mul_le_mul_of_nonneg_left hw hQ0.le
  have hnum : 4 * Lt * w ^ 2 + 16 * Ls * w + 8 * Q * w ≤
      4 * A ^ 2 * Q ^ 5 + 192 * A * Q ^ 3 + 8 * Q ^ 2 := by
    nlinarith
  have hmesh : (4 * Lt * w ^ 2 + 16 * Ls * w + 8 * Q * w) / N ≤ Q⁻¹ := by
    apply (div_le_div_of_nonneg_right hnum hN0.le).trans
    rw [hN]
    exact mesh_fraction_bound hA hQ
  have hsample : Q * w * e ≤ Q⁻¹ :=
    (mul_le_mul_of_nonneg_right (show Q * w ≤ Q ^ 2 by nlinarith [h₃]) he0).trans he
  have hid : N * (4 * Lt * (w / N) ^ 2 + (w / N) *
      (4 * (2 * Ls * (2 / N) + (e + 8 / N) / (4 * Q⁻¹)))) =
      (4 * Lt * w ^ 2 + 16 * Ls * w + 8 * Q * w) / N + Q * w * e := by
    field_simp [hN0.ne', hQ0.ne']
    ring
  rw [hid]
  linarith [exp_tail_le_inverse hQ0]

theorem argument_endpoint (x : Input) :
    RationalHeatBox.timeEndpoint (argument x) = (scale x.1.2 : ℚ) := by
  have hN : (count x.1.1 x.1.2 : ℚ) ≠ 0 := by
    exact_mod_cast (count_positive x.1.1 x.1.2).ne'
  have hQ : (scale x.1.2 : ℚ) ≠ 0 := by
    exact_mod_cast (scale_positive x.1.2).ne'
  change (scale x.1.2 : ℚ)⁻¹ + (count x.1.1 x.1.2 : ℚ) *
    (((scale x.1.2 : ℚ) - (scale x.1.2 : ℚ)⁻¹) / count x.1.1 x.1.2) = _
  field_simp [hN, hQ]
  ring

theorem argument_start_positive (x : Input) : 0 < ((argument x).2.2.1 : ℝ) := by
  have hQ := scale_positive x.1.2
  change 0 < (((scale x.1.2 : ℚ)⁻¹ : ℚ) : ℝ)
  rw [Rat.cast_inv, Rat.cast_natCast]
  positivity

theorem argument_step_nonnegative (x : Input) : 0 ≤ ((argument x).2.2.2 : ℝ) := by
  have hQ : (1 : ℚ) ≤ scale x.1.2 := by
    exact_mod_cast (Nat.succ_le_iff.mpr (scale_positive x.1.2))
  have hN : (0 : ℚ) < count x.1.1 x.1.2 := by exact_mod_cast count_positive x.1.1 x.1.2
  have hi : (scale x.1.2 : ℚ)⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).mpr hQ
  have hh : 0 ≤ ((scale x.1.2 : ℚ) - (scale x.1.2 : ℚ)⁻¹) / count x.1.1 x.1.2 :=
    div_nonneg (by linarith) hN.le
  exact_mod_cast hh

theorem magnitude_bound (r : PlanarPosition) {R Q : ℝ}
    (hR : ‖r‖ ≤ R) (hQ : 0 < Q) :
    Q + (‖r‖ + 2) ^ 2 / (4 * Q⁻¹) ≤ (R + 3) ^ 2 * Q := by
  have hR0 : 0 ≤ R := (norm_nonneg r).trans hR
  have hsquare : (‖r‖ + 2) ^ 2 ≤ (R + 2) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr (by linarith)
  have hc : 1 + (‖r‖ + 2) ^ 2 / 4 ≤ (R + 3) ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hc hQ.le
  have hid : Q + (‖r‖ + 2) ^ 2 / (4 * Q⁻¹) =
      (1 + (‖r‖ + 2) ^ 2 / 4) * Q := by field_simp [hQ.ne']
  rw [hid]
  exact hm

end ContinuumCoulomb.ResolventSchedule

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_GaussianFrequency
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certified approximation of the manuscript's actual transverse frequency
`sqrt (4*pi*rho)`. The integer density is fixed once for the construction;
it is not assumed that the resulting frequency is rational. -/

noncomputable section
namespace ContinuumCoulomb.GaussianFrequency
open scoped BigOperators

theorem count_positive (rho P : ℕ) : 0 < count rho P := by unfold count; positivity

theorem pi_approximate_nonnegative (N : ℕ) : 0 ≤ PiProgram.approximate N := by
  unfold PiProgram.approximate RationalQuadratureProgram.value
  apply mul_nonneg (by norm_num)
  apply mul_nonneg (by dsimp [PiProgram.input]; positivity)
  apply Finset.sum_nonneg
  intro i _
  dsimp [RationalQuadratureProgram.sample, PiProgram.evaluate]
  positivity

theorem radicand_nonnegative (rho P : ℕ) : 0 ≤ radicand rho P := by
  unfold radicand
  exact mul_nonneg (by positivity) (pi_approximate_nonnegative _)

theorem radicand_error (rho P : ℕ) :
    |(radicand rho P : ℝ) - 4 * Real.pi * (rho : ℝ)| ≤
      ((4 * ((P : ℝ) + 1))⁻¹) ^ 2 := by
  let S := (P : ℝ) + 1
  have hS : 0 < S := by dsimp [S]; positivity
  have hrho : (0 : ℝ) ≤ rho := Nat.cast_nonneg _
  have hp := PiProgram.error (count rho P) (count_positive rho P)
  have he : (radicand rho P : ℝ) - 4 * Real.pi * (rho : ℝ) =
      4 * (rho : ℝ) * ((PiProgram.approximate (count rho P) : ℝ) - Real.pi) := by
    simp only [radicand, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast]
    ring
  rw [he, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 4 * (rho : ℝ))]
  apply (mul_le_mul_of_nonneg_left hp (by positivity)).trans
  have hc : (count rho P : ℝ) = 512 * ((rho : ℝ) + 1) * S ^ 2 := by
    dsimp [count, S]
    push_cast
    rfl
  rw [hc]
  calc
    4 * (rho : ℝ) * (8 / (512 * ((rho : ℝ) + 1) * S ^ 2)) ≤
        4 * ((rho : ℝ) + 1) * (8 / (512 * ((rho : ℝ) + 1) * S ^ 2)) := by
      gcongr
      linarith
    _ = ((4 * S)⁻¹) ^ 2 := by
      field_simp [hS.ne', show (rho : ℝ) + 1 ≠ 0 by positivity]
      ring

theorem root_precision_bound (P : ℕ) :
    (2 : ℝ)⁻¹ ^ precision P ≤ (4 * ((P : ℝ) + 1))⁻¹ := by
  have hn : 4 * (P + 1) ≤ 2 ^ precision P := by
    have hh := ResolventSchedule.succ_le_two_pow (precision P)
    unfold precision at *
    omega
  have hr : 4 * ((P : ℝ) + 1) ≤ (2 : ℝ) ^ precision P := by exact_mod_cast hn
  rw [inv_pow]
  exact inv_anti₀ (by positivity) hr

theorem approximation_error (rho P : ℕ) :
    |(approximate rho P : ℝ) - frequency rho| ≤ ((P : ℝ) + 1)⁻¹ := by
  let S := (P : ℝ) + 1
  have hS : 0 < S := by dsimp [S]; positivity
  have hsqrt := RationalSquareRoot.sqrt_perturbation
    (show 0 ≤ (radicand rho P : ℝ) by exact_mod_cast radicand_nonnegative rho P)
    (show 0 ≤ 4 * Real.pi * (rho : ℝ) by positivity)
  have hquad := Real.sqrt_le_sqrt (radicand_error rho P)
  rw [Real.sqrt_sq_eq_abs, abs_of_pos (by positivity : 0 < (4 * ((P : ℝ) + 1))⁻¹)] at hquad
  have hnum := RationalSquareRoot.value_error (precision P) (radicand_nonnegative rho P)
  have h := (abs_sub_le (approximate rho P : ℝ) (Real.sqrt (radicand rho P : ℝ))
    (frequency rho)).trans (add_le_add (hnum.trans (root_precision_bound P)) (hsqrt.trans hquad))
  apply h.trans
  change (4 * S)⁻¹ + (4 * S)⁻¹ ≤ S⁻¹
  rw [mul_inv]
  norm_num
  nlinarith [inv_pos.mpr hS]

end ContinuumCoulomb.GaussianFrequency

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_GaussianPacket
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A certified rational sample of the actual transverse Gaussian. The
frequency is sqrt(4*pi*rho), with rho fixed, and is evaluated internally. -/

noncomputable section
namespace ContinuumCoulomb.GaussianPacket

theorem frequencyApprox_nonnegative (rho P : ℕ) :
    0 ≤ GaussianFrequency.approximate rho P := by
  unfold GaussianFrequency.approximate RationalSquareRoot.value DyadicRootProgram.value
  positivity

theorem frequency_le (rho : ℕ) : GaussianFrequency.frequency rho ≤ 4 * (rho : ℝ) + 2 := by
  unfold GaussianFrequency.frequency
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have hpi := Real.pi_lt_four
    nlinarith [sq_nonneg (rho : ℝ), show (0 : ℝ) ≤ rho from Nat.cast_nonneg _]

theorem frequencyApprox_le (rho P : ℕ) :
    (GaussianFrequency.approximate rho P : ℝ) ≤ 4 * (rho : ℝ) + 3 := by
  have h := (abs_le.mp (GaussianFrequency.approximation_error rho P)).2
  have hp : ((P : ℝ) + 1)⁻¹ ≤ 1 :=
    (inv_le_one₀ (by positivity)).mpr (by linarith [show (0 : ℝ) ≤ P from Nat.cast_nonneg _])
  linarith [frequency_le rho]

theorem exponent_nonpositive (rho : ℕ) (x : Input) : (exponent rho x : ℝ) ≤ 0 := by
  simp only [exponent, Rat.cast_mul, Rat.cast_neg, Rat.cast_pow]
  exact mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (by exact_mod_cast frequencyApprox_nonnegative rho _)) (sq_nonneg _)

theorem exponent_abs_le (rho : ℕ) (x : Input) (hz : |(x.2 : ℝ)| ≤ x.1.1) :
    |(exponent rho x : ℝ)| ≤ (magnitude rho x.1.1 : ℝ) := by
  rw [abs_of_nonpos (exponent_nonpositive rho x)]
  simp only [exponent, Rat.cast_mul, Rat.cast_neg, Rat.cast_pow, neg_mul, neg_neg]
  have hz'' : (x.2 : ℝ) ^ 2 ≤ ((x.1.1 : ℝ) + 1) ^ 2 := by
    have habs := (sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg _)).mpr hz
    rw [sq_abs] at habs
    nlinarith [show (0 : ℝ) ≤ x.1.1 from Nat.cast_nonneg _]
  calc
    _ ≤ (4 * (rho : ℝ) + 3) * (((x.1.1 : ℝ) + 1) ^ 2) :=
      mul_le_mul (frequencyApprox_le rho _) hz'' (sq_nonneg _)
        (by positivity)
    _ ≤ _ := by
      simp only [magnitude, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_one]
      nlinarith [sq_nonneg ((x.1.1 : ℝ) + 1)]

theorem exponent_error (rho : ℕ) (x : Input) (hz : |(x.2 : ℝ)| ≤ x.1.1) :
    |(exponent rho x : ℝ) - (-GaussianFrequency.frequency rho * (x.2 : ℝ) ^ 2)| ≤
      (8 * ((x.1.2 : ℝ) + 1))⁻¹ := by
  have hfreq := GaussianFrequency.approximation_error rho (frequencyPrecision x.1.1 x.1.2)
  have hzsq : (x.2 : ℝ) ^ 2 ≤ ((x.1.1 : ℝ) + 1) ^ 2 := by
    have habs := (sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg _)).mpr hz
    rw [sq_abs] at habs
    nlinarith [show (0 : ℝ) ≤ x.1.1 from Nat.cast_nonneg _]
  have he : (exponent rho x : ℝ) - (-GaussianFrequency.frequency rho * (x.2 : ℝ) ^ 2) =
      -(GaussianFrequency.approximate rho (frequencyPrecision x.1.1 x.1.2) -
        GaussianFrequency.frequency rho) * (x.2 : ℝ) ^ 2 := by
    simp only [exponent, Rat.cast_mul, Rat.cast_neg, Rat.cast_pow]
    ring
  rw [he, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg (x.2 : ℝ))]
  apply (mul_le_mul hfreq hzsq (sq_nonneg _) (by positivity)).trans
  have hR : 0 < ((x.1.1 : ℝ) + 1) ^ 2 := by positivity
  have hP : 0 < (x.1.2 : ℝ) + 1 := by positivity
  have hprec : (frequencyPrecision x.1.1 x.1.2 : ℝ) =
      16 * ((x.1.1 : ℝ) + 1) ^ 2 * ((x.1.2 : ℝ) + 1) := by
    simp only [frequencyPrecision, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add,
      Nat.cast_one, Nat.cast_pow]
  rw [hprec]
  calc
    _ ≤ (16 * ((x.1.1 : ℝ) + 1) ^ 2 * ((x.1.2 : ℝ) + 1))⁻¹ *
        ((x.1.1 : ℝ) + 1) ^ 2 := by gcongr; linarith
    _ = (16 * ((x.1.2 : ℝ) + 1))⁻¹ := by
      field_simp [hR.ne', hP.ne']
    _ ≤ _ := inv_anti₀ (by positivity) (by nlinarith)

theorem exponential_precision_bound (P : ℕ) :
    (2 : ℝ)⁻¹ ^ exponentialPrecision P ≤ (8 * ((P : ℝ) + 1))⁻¹ := by
  have hn := ResolventSchedule.succ_le_two_pow (exponentialPrecision P)
  have hp : 8 * (P + 1) ≤ 2 ^ exponentialPrecision P := by unfold exponentialPrecision at *; omega
  have hr : 8 * ((P : ℝ) + 1) ≤ (2 : ℝ) ^ exponentialPrecision P := by exact_mod_cast hp
  rw [inv_pow]
  exact inv_anti₀ (by positivity) hr

theorem approximation_error (rho : ℕ) (x : Input) (hz : |(x.2 : ℝ)| ≤ x.1.1) :
    |(approximate rho x : ℝ) - Real.exp (-GaussianFrequency.frequency rho * (x.2 : ℝ) ^ 2)| ≤
      ((x.1.2 : ℝ) + 1)⁻¹ := by
  have ht := RationalExponentialProgram.error (argument rho x) (exponent_abs_le rho x hz)
  rw [abs_sub_comm] at ht
  have hprec := exponential_precision_bound x.1.2
  rw [inv_pow] at hprec
  have htaylor := ht.trans hprec
  have harg : -GaussianFrequency.frequency rho * (x.2 : ℝ) ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.sqrt_nonneg _)) (sq_nonneg _)
  have hexp := HeatKernelModulus.exp_nonpositive_lipschitz (exponent_nonpositive rho x) harg
  have hbase := (abs_sub_le (RationalExponentialProgram.approximate (argument rho x) : ℝ)
    (Real.exp (exponent rho x : ℝ))
    (Real.exp (-GaussianFrequency.frequency rho * (x.2 : ℝ) ^ 2))).trans
      (add_le_add htaylor
        (hexp.trans (exponent_error rho x hz)))
  apply (rationalUnitClamp_error _ (Real.exp_pos _).le
    (Real.exp_le_one_iff.mpr harg)).trans
  apply hbase.trans
  rw [mul_inv]
  norm_num
  nlinarith [inv_pos.mpr (show 0 < (x.1.2 : ℝ) + 1 by positivity)]

end ContinuumCoulomb.GaussianPacket

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_ComputableResolvent
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit rational machine approximates the actual planar
resolvent to inverse-polynomial accuracy. No numerical oracle occurs in
the statement or the program. -/

noncomputable section
namespace ContinuumCoulomb.ResolventSchedule

theorem scheduled_error_bound (x : Input)
    (hR : ‖PlanarForcingProgram.position x.2‖ ≤ (x.1.1 : ℝ)) :
    RationalHeatBox.resolventErrorBound (argument x) ≤ 4 * (scale x.1.2 : ℝ)⁻¹ := by
  let r := PlanarForcingProgram.position x.2
  let R := (x.1.1 : ℝ)
  let Q := (scale x.1.2 : ℝ)
  let N := (count x.1.1 x.1.2 : ℝ)
  let w := Q - Q⁻¹
  let e := (2 ^ precision x.1.2 : ℝ)⁻¹
  have hQnat : 1 ≤ scale x.1.2 := Nat.succ_le_iff.mpr (scale_positive x.1.2)
  have hQ : 1 ≤ Q := by
    dsimp only [Q]
    exact_mod_cast hQnat
  have hQ0 : 0 < Q := by linarith
  have hA : 1 ≤ R + 3 := by
    have hR0 : 0 ≤ R := Nat.cast_nonneg _
    linarith
  have hN : N = 4096 * (R + 3) ^ 4 * Q ^ 8 := by
    dsimp only [N, R, Q, count, countPrefix]
    push_cast
    rfl
  have hw0 : 0 ≤ w := by
    have hi : Q⁻¹ ≤ 1 := (inv_le_one₀ hQ0).mpr hQ
    dsimp only [w]
    linarith
  have hw : w ≤ Q := by
    have hi : 0 ≤ Q⁻¹ := by positivity
    dsimp only [w]
    linarith
  have he0 : 0 ≤ e := by dsimp only [e]; positivity
  have he : Q ^ 2 * e ≤ Q⁻¹ := taylor_precision_bound (scale x.1.2) hQnat
  have h := scalar_error_bound hA hQ hN hw0 hw
    (time_constant_bound r hR hQ) (spatial_constant_bound r hR hQ) he0 he
  have hid : RationalHeatBox.resolventErrorBound (argument x) =
      N * (4 * planarBoxTimeConstant r Q⁻¹ * (w / N) ^ 2 + (w / N) *
        (4 * (2 * planarBoxSpatialConstant r Q⁻¹ * (2 / N) +
          (e + 8 / N) / (4 * Q⁻¹)))) + Q⁻¹ + Real.exp (-Q) := by
    rw [RationalHeatBox.resolventErrorBound, argument_endpoint]
    simp only [argument, RationalHeatBox.planeErrorBound, RationalHeatBox.spatialStep,
      Rat.cast_inv, Rat.cast_natCast, Rat.cast_div, Rat.cast_sub, Rat.cast_ofNat]
    rfl
  rw [hid]
  exact h

theorem approximation_error (x : Input)
    (hR : ‖PlanarForcingProgram.position x.2‖ ≤ (x.1.1 : ℝ)) :
    |(approximate x : ℝ) - planarResolventMode (PlanarForcingProgram.position x.2)| ≤
      ((x.1.2 : ℝ) + 1)⁻¹ := by
  let r := PlanarForcingProgram.position x.2
  have hQ : (0 : ℝ) < scale x.1.2 := by exact_mod_cast scale_positive x.1.2
  have hM : (RationalHeatBox.timeEndpoint (argument x) : ℝ) +
      (‖PlanarForcingProgram.position (argument x).2.1.2.1‖ + 2) ^ 2 /
        (4 * ((argument x).2.2.1 : ℝ)) ≤ (argument x).2.1.1.1 := by
    rw [argument_endpoint]
    simp only [argument, Rat.cast_inv, Rat.cast_natCast, magnitude, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_add, Nat.cast_ofNat]
    exact magnitude_bound r hR hQ
  have h := RationalHeatBox.resolvent_error (argument x) (argument_start_positive x)
    (argument_step_nonnegative x) (count_positive x.1.1 x.1.2) (count_positive x.1.1 x.1.2) hM
  have h' := h.trans (scheduled_error_bound x hR)
  have hlast : 4 * (scale x.1.2 : ℝ)⁻¹ ≤ ((x.1.2 : ℝ) + 1)⁻¹ := by
    have hp : (0 : ℝ) < (x.1.2 : ℝ) + 1 := by positivity
    simp only [scale, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    apply (mul_le_mul_iff_left₀ hp).mp
    field_simp
    norm_num
  exact h'.trans hlast

end ContinuumCoulomb.ResolventSchedule

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_RawDensitySample
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal bounded samples of the actual unnormalized three-dimensional
localized density, including the irrational fixed transverse frequency. -/

noncomputable section
namespace ContinuumCoulomb.RawDensitySample
open ExactQuantumFactoring.BitStackProgram

theorem value_nonnegative (rho : ℕ) (x : Input) : 0 ≤ value rho x :=
  mul_nonneg (sq_nonneg _) (rationalUnitClamp_nonnegative _)

theorem value_le_one (rho : ℕ) (x : Input) : value rho x ≤ 1 := by
  have hs := (sq_le_sq₀ (rationalUnitClamp_nonnegative _) zero_le_one).mpr
    (rationalUnitClamp_le_one (ResolventSchedule.approximate (planarArgument x)))
  exact (mul_le_mul hs (rationalUnitClamp_le_one _)
    (rationalUnitClamp_nonnegative _) (by positivity)).trans_eq (by norm_num)

theorem position_split (q : CappedKernelProgram.Triple) :
    positionSplitCoordinates (CappedKernelProgram.position q) =
      (PlanarForcingProgram.position (q.1, q.2.1), (q.2.2 : ℝ)) := by
  apply Prod.ext
  · ext i
    fin_cases i <;> rfl
  · rfl

theorem planar_norm_le (x : Input)
    (hx : |(x.2.1 : ℝ)| ≤ (x.1.1 : ℝ)) (hy : |(x.2.2.1 : ℝ)| ≤ (x.1.1 : ℝ)) :
    ‖PlanarForcingProgram.position (x.2.1, x.2.2.1)‖ ≤ (2 * x.1.1 : ℕ) := by
  have hx2 := (sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg _)).mpr hx
  have hy2 := (sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg _)).mpr hy
  rw [sq_abs] at hx2 hy2
  apply (sq_le_sq₀ (norm_nonneg _) (Nat.cast_nonneg _)).mp
  rw [PlanarForcingProgram.position_norm_sq]
  push_cast
  nlinarith [sq_nonneg (x.1.1 : ℝ)]

theorem unit_product_error {a b a' b' ε δ : ℝ}
    (ha'0 : 0 ≤ a') (ha'1 : a' ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (ha : |a' - a| ≤ ε) (hb : |b' - b| ≤ δ) :
    |a' * b' - a * b| ≤ ε + δ := by
  have he : a' * b' - a * b = a' * (b' - b) + (a' - a) * b := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul, abs_of_nonneg ha'0, abs_of_nonneg hb0]
  have h1 := mul_le_of_le_one_left (abs_nonneg (b' - b)) ha'1
  have h2 := mul_le_of_le_one_right (abs_nonneg (a' - a)) hb1
  linarith

theorem value_error (rho : ℕ) (x : Input)
    (hx : |(x.2.1 : ℝ)| ≤ (x.1.1 : ℝ)) (hy : |(x.2.2.1 : ℝ)| ≤ (x.1.1 : ℝ))
    (hz : |(x.2.2.2 : ℝ)| ≤ (x.1.1 : ℝ)) :
    |(value rho x : ℝ) -
      localizedRawDensity (GaussianFrequency.frequency rho) (CappedKernelProgram.position x.2)| ≤
      4 * ((x.1.2 : ℝ) + 1)⁻¹ := by
  let r := PlanarForcingProgram.position (x.2.1, x.2.2.1)
  let a : ℝ := rationalUnitClamp (ResolventSchedule.approximate (planarArgument x))
  let b : ℝ := GaussianPacket.approximate rho (verticalArgument x)
  have hφ := ResolventSchedule.approximation_error (planarArgument x) (planar_norm_le x hx hy)
  have ha : |a - planarResolventMode r| ≤ ((x.1.2 : ℝ) + 1)⁻¹ :=
    (rationalUnitClamp_error _ (planarResolventMode_positive r).le
      (planarResolventMode_le_one r)).trans hφ
  have hε : ((x.1.2 : ℝ) + 1)⁻¹ ≤ 1 :=
    (inv_le_one₀ (by positivity)).mpr (by linarith [show (0 : ℝ) ≤ x.1.2 from Nat.cast_nonneg _])
  have ha2 := unitInterval_square_error (planarResolventMode_positive r).le
    (planarResolventMode_le_one r) hε ha
  have hb := GaussianPacket.approximation_error rho (verticalArgument x) hz
  have ha0 : 0 ≤ a := by
    dsimp only [a]
    exact_mod_cast rationalUnitClamp_nonnegative (ResolventSchedule.approximate (planarArgument x))
  have ha1 : a ≤ 1 := by
    dsimp only [a]
    exact_mod_cast rationalUnitClamp_le_one (ResolventSchedule.approximate (planarArgument x))
  have hsq : a ^ 2 ≤ 1 := by simpa only [one_pow] using (sq_le_sq₀ ha0 zero_le_one).mpr ha1
  have hexp : Real.exp (-GaussianFrequency.frequency rho * (x.2.2.2 : ℝ) ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (Real.sqrt_nonneg _)) (sq_nonneg _))
  have hp := unit_product_error (sq_nonneg a) hsq (Real.exp_pos _).le hexp ha2 hb
  have hout : |(value rho x : ℝ) -
      localizedRawDensity (GaussianFrequency.frequency rho) (CappedKernelProgram.position x.2)| ≤
      3 * ((x.1.2 : ℝ) + 1)⁻¹ + ((x.1.2 : ℝ) + 1)⁻¹ := by
    simpa only [value, Rat.cast_mul, Rat.cast_pow, localizedRawDensity, position_split,
      Prod.fst, Prod.snd, r, a, b, verticalArgument] using hp
  convert hout using 1
  all_goals try with_reducible_and_instances rfl
  ring

end ContinuumCoulomb.RawDensitySample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_RawCoulombSample
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal rational sample of the six-coordinate Coulomb integrand.
Both density factors and the capped kernel use the certified programs. -/

noncomputable section
namespace ContinuumCoulomb.RawCoulombSample
open CappedKernelProgram

theorem position_difference (x y s : Triple) :
    position (difference x y s) = position x - position y - position s := by
  ext i
  fin_cases i <;> simp [position, difference]

theorem kernel_nonnegative (b : ℕ) {ε : ℚ} (hε : 0 < ε) (q : Triple) :
    (0 : ℝ) ≤ approximate ((b, ε), q) := by
  simp only [approximate, Rat.cast_inv, Rat.cast_max]
  exact inv_nonneg.mpr ((show (0 : ℝ) ≤ ε by exact_mod_cast hε.le).trans (le_max_left _ _))

theorem kernel_le (b : ℕ) {ε : ℚ} (hε : 0 < ε) (q : Triple) :
    (approximate ((b, ε), q) : ℝ) ≤ (ε : ℝ)⁻¹ := by
  simp only [approximate, Rat.cast_inv, Rat.cast_max]
  exact inv_anti₀ (by exact_mod_cast hε) (le_max_left _ _)

theorem value_error (rho R P b : ℕ) {ε : ℚ} (hε : 0 < ε)
    (s x y : Triple) (hx : inBox R x) (hy : inBox R y) :
    |(value rho R P b ε s x y : ℝ) -
      cappedPairIntegrand (ε : ℝ) (position s)
        (localizedRawDensity (GaussianFrequency.frequency rho))
        (localizedRawDensity (GaussianFrequency.frequency rho)) (position x, position y)| ≤
      8 * (ε : ℝ)⁻¹ * ((P : ℝ) + 1)⁻¹ + (ε : ℝ)⁻¹ ^ 2 * (2 : ℝ)⁻¹ ^ b := by
  let f := localizedRawDensity (GaussianFrequency.frequency rho)
  let a : ℝ := RawDensitySample.value rho ((R, P), x)
  let c : ℝ := RawDensitySample.value rho ((R, P), y)
  let k : ℝ := approximate ((b, ε), difference x y s)
  let t := cappedCoulombKernel (ε : ℝ) (position x - position y - position s)
  have hfreq : 0 ≤ GaussianFrequency.frequency rho := Real.sqrt_nonneg _
  have ha0 : 0 ≤ a := by
    dsimp only [a]
    exact_mod_cast RawDensitySample.value_nonnegative rho ((R, P), x)
  have ha1 : a ≤ 1 := by
    dsimp only [a]
    exact_mod_cast RawDensitySample.value_le_one rho ((R, P), x)
  have hprod := bounded_product_sub (a := a) (b := c) (c := f (position x))
    (d := f (position y)) ha0 ha1
    (localizedRawDensity_nonnegative _ _) (localizedRawDensity_le_one hfreq _)
  have hxerr := RawDensitySample.value_error rho ((R, P), x) hx.1 hx.2.1 hx.2.2
  have hyerr := RawDensitySample.value_error rho ((R, P), y) hy.1 hy.2.1 hy.2.2
  have herr : |a * c - f (position x) * f (position y)| ≤ 8 * ((P : ℝ) + 1)⁻¹ := by
    exact hprod.trans (by dsimp only [a, c, f] at *; linarith)
  have hk0 : 0 ≤ k := kernel_nonnegative b hε _
  have hk1 : k ≤ (ε : ℝ)⁻¹ := kernel_le b hε _
  have hkerr : |k - t| ≤ (ε : ℝ)⁻¹ ^ 2 * (2 : ℝ)⁻¹ ^ b := by
    have h := approximation_error ((b, ε), difference x y s) hε
    simpa only [position_difference] using h
  have hf0 : 0 ≤ f (position x) * f (position y) :=
    mul_nonneg (localizedRawDensity_nonnegative _ _) (localizedRawDensity_nonnegative _ _)
  have hf1 : f (position x) * f (position y) ≤ 1 := by
    exact (mul_le_mul (localizedRawDensity_le_one hfreq _) (localizedRawDensity_le_one hfreq _)
      (localizedRawDensity_nonnegative _ _) zero_le_one).trans_eq (one_mul 1)
  have he : (value rho R P b ε s x y : ℝ) -
      cappedPairIntegrand (ε : ℝ) (position s) f f (position x, position y) =
      (a * c - f (position x) * f (position y)) * k +
        f (position x) * f (position y) * (k - t) := by
    simp only [value, Rat.cast_mul, cappedPairIntegrand, a, c, k, t]
    ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul, abs_of_nonneg hk0, abs_of_nonneg hf0]
  have h1 := mul_le_mul herr hk1 hk0 (by positivity)
  have h2 := (mul_le_of_le_one_left (abs_nonneg (k - t)) hf1).trans hkerr
  nlinarith

end ContinuumCoulomb.RawCoulombSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombQuadrature
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual six-coordinate cubature of the finite Coulomb integral. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb.RawCoulombSample
open UniformQuadrature

theorem quadrature_cast (rho R P b : ℕ) (ε : ℚ) (s : CappedKernelProgram.Triple) (N : ℕ) :
    (RationalSixQuadrature.value (sixEvaluator rho) (quadratureInput R P b ε s N) : ℝ) =
      cubeSample (2 * (R : ℝ) / (N : ℝ)) N 6
        (sampled rho R P b ε s (-(R : ℚ)) (2 * (R : ℚ) / (N : ℚ))) := by
  rw [RationalSixQuadrature.value_cast]
  simp only [quadratureInput, sixEvaluator, evaluate, sampled, cubeSample, rectangleSum,
    Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast,
    Fin.cons_zero]
  rfl

theorem position_sampled (a h : ℚ) (w : Fin 6 → ℕ) :
    (CappedKernelProgram.position
      (RationalQuadratureProgram.node a h (w 0),
        RationalQuadratureProgram.node a h (w 1),
        RationalQuadratureProgram.node a h (w 2)),
     CappedKernelProgram.position
      (RationalQuadratureProgram.node a h (w 3),
        RationalQuadratureProgram.node a h (w 4),
        RationalQuadratureProgram.node a h (w 5))) =
      twoParticleCoordinates (fun i => node (a : ℝ) (h : ℝ) (w i)) := by
  apply Prod.ext
  · ext i
    rw [twoParticleCoordinates_fst]
    fin_cases i <;> simp [CappedKernelProgram.position, RationalQuadratureProgram.node_cast]
  · ext i
    rw [twoParticleCoordinates_snd]
    fin_cases i <;> simp [CappedKernelProgram.position, RationalQuadratureProgram.node_cast]

theorem quadrature_error (rho R P b N : ℕ) {ε : ℚ} (hε : 0 < ε)
    (hN : 0 < N) (s : CappedKernelProgram.Triple) :
    |(RationalSixQuadrature.value (sixEvaluator rho) (quadratureInput R P b ε s N) : ℝ) -
      cubeIntegral (-(R : ℝ)) (R : ℝ) 6
        (rawCoulombSix (GaussianFrequency.frequency rho) (ε : ℝ) (CappedKernelProgram.position s))| ≤
      (2 * (R : ℝ)) ^ 6 *
        (6 * ((64 + 2 * GaussianFrequency.frequency rho * R) * (ε : ℝ)⁻¹ + (ε : ℝ)⁻¹ ^ 2) *
          (2 * (R : ℝ) / N) +
          (8 * (ε : ℝ)⁻¹ * ((P : ℝ) + 1)⁻¹ + (ε : ℝ)⁻¹ ^ 2 * (2 : ℝ)⁻¹ ^ b)) := by
  let h : ℚ := 2 * (R : ℚ) / (N : ℚ)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hfreq : 0 ≤ GaussianFrequency.frequency rho := Real.sqrt_nonneg _
  have hh : (0 : ℝ) ≤ h := by dsimp only [h]; push_cast; positivity
  have he : node (-(R : ℝ)) (h : ℝ) N = R := by
    dsimp only [node, h]
    push_cast
    field_simp [hNr.ne']
    ring
  have hεr : (0 : ℝ) < ε := by exact_mod_cast hε
  have hmod := rawCoulombSix_modulus hfreq hεr
    (Nat.cast_nonneg R) (CappedKernelProgram.position s)
  have hsamp : ∀ w : Fin 6 → ℕ, (∀ i, w i < N) →
      |sampled rho R P b ε s (-(R : ℚ)) h w -
        rawCoulombSix (GaussianFrequency.frequency rho) (ε : ℝ) (CappedKernelProgram.position s)
          (fun i => node (-(R : ℝ)) (h : ℝ) (w i))| ≤
        8 * (ε : ℝ)⁻¹ * ((P : ℝ) + 1)⁻¹ + (ε : ℝ)⁻¹ ^ 2 * (2 : ℝ)⁻¹ ^ b := by
    intro w hw
    have hbnd (i : Fin 6) : |(RationalQuadratureProgram.node (-(R : ℚ)) h (w i) : ℝ)| ≤ R := by
      rw [RationalQuadratureProgram.node_cast]
      have hi := node_mem (a := -(R : ℝ)) hh (hw i).le
      rw [he] at hi
      simpa only [Rat.cast_neg, Rat.cast_natCast] using abs_le.mpr hi
    have ht := value_error rho R P b hε s
      (RationalQuadratureProgram.node (-(R : ℚ)) h (w 0),
        RationalQuadratureProgram.node (-(R : ℚ)) h (w 1),
        RationalQuadratureProgram.node (-(R : ℚ)) h (w 2))
      (RationalQuadratureProgram.node (-(R : ℚ)) h (w 3),
        RationalQuadratureProgram.node (-(R : ℚ)) h (w 4),
        RationalQuadratureProgram.node (-(R : ℚ)) h (w 5))
      ⟨hbnd 0, hbnd 1, hbnd 2⟩ ⟨hbnd 3, hbnd 4, hbnd 5⟩
    rw [position_sampled] at ht
    simpa only [sampled, rawCoulombSix, Rat.cast_neg, Rat.cast_natCast] using ht
  have ht := cube_quadrature_error 6
    (L := (64 + 2 * GaussianFrequency.frequency rho * R) * (ε : ℝ)⁻¹ + (ε : ℝ)⁻¹ ^ 2)
    hh (by positivity) (by positivity) (by simpa only [he] using hmod) hsamp
  rw [he] at ht
  rw [quadrature_cast]
  have hlen : (N : ℝ) * (h : ℝ) = 2 * R := by
    dsimp only [h]
    push_cast
    field_simp [hNr.ne']
  rw [hlen] at ht
  simpa only [Nat.cast_ofNat, h, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] using ht

end ContinuumCoulomb.RawCoulombSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombQuadratureBudget
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial mesh and precision budgets for the six-coordinate
Coulomb quadrature. All varying parameters below are unary naturals. -/

noncomputable section
namespace ContinuumCoulomb.CoulombQuadratureSchedule

theorem dyadic_le_inverse (b : ℕ) : (2 : ℝ)⁻¹ ^ b ≤ ((b : ℝ) + 1)⁻¹ := by
  have hb : (b : ℝ) + 1 ≤ (2 : ℝ) ^ b := by
    exact_mod_cast Nat.succ_le_of_lt b.lt_two_pow_self
  rw [inv_pow]
  exact inv_anti₀ (by positivity) hb

theorem scalar_budget {R D L S V N Q : ℝ} {b : ℕ}
    (hR : 0 < R) (hD : 0 < D) (hL : 0 < L) (hS : 0 < S)
    (hV : V = (2 * R) ^ 6) (hN : N = 48 * R * L * V * S)
    (hQ : Q = 32 * D * V * S) (hb : (b : ℝ) = 4 * D ^ 2 * V * S) :
    V * (6 * L * (2 * R / N) + 8 * D * (Q + 1)⁻¹ + D ^ 2 * (2 : ℝ)⁻¹ ^ b) ≤
      3 * (4 * S)⁻¹ := by
  have hV0 : 0 < V := by rw [hV]; positivity
  have hN0 : 0 < N := by rw [hN]; positivity
  have hQ0 : 0 < Q := by rw [hQ]; positivity
  have hb0 : (0 : ℝ) < b := by rw [hb]; positivity
  have hmesh : V * (6 * L * (2 * R / N)) = (4 * S)⁻¹ := by
    rw [hN]
    field_simp [hR.ne', hL.ne', hV0.ne', hS.ne']
    ring
  have hsample : V * (8 * D * (Q + 1)⁻¹) ≤ (4 * S)⁻¹ := by
    calc
      _ ≤ V * (8 * D * Q⁻¹) := by
        gcongr
        linarith
      _ = _ := by
        rw [hQ]
        field_simp [hD.ne', hV0.ne', hS.ne']
        ring
  have hkernel : V * (D ^ 2 * (2 : ℝ)⁻¹ ^ b) ≤ (4 * S)⁻¹ := by
    calc
      _ ≤ V * (D ^ 2 * ((b : ℝ) + 1)⁻¹) := by
        gcongr
        exact dyadic_le_inverse b
      _ ≤ V * (D ^ 2 * (b : ℝ)⁻¹) := by
        gcongr
        linarith
      _ = _ := by
        rw [hb]
        field_simp [hD.ne', hV0.ne', hS.ne']
  nlinarith

end ContinuumCoulomb.CoulombQuadratureSchedule

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombTruncationSchedule
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial cap and box schedules. The single natural guard
is fixed by the fixed one-well density; it is not an input or an oracle. -/

noncomputable section
namespace ContinuumCoulomb.CoulombTruncationSchedule

theorem guard_one_le (freq : ℝ) : 1 ≤ (guard freq : ℝ) := by
  have hc := Nat.le_ceil (max 1 (max (2 * Real.pi * localizedAmplitudeBound freq ^ 2)
    (2 * localizedDensitySecondMoment freq)))
  have h := (le_max_left (1 : ℝ) _).trans hc
  simp only [guard, Nat.cast_add, Nat.cast_one]
  linarith

theorem guard_cap (freq : ℝ) :
    2 * Real.pi * localizedAmplitudeBound freq ^ 2 ≤ (guard freq : ℝ) := by
  have hc := Nat.le_ceil (max 1 (max (2 * Real.pi * localizedAmplitudeBound freq ^ 2)
    (2 * localizedDensitySecondMoment freq)))
  have h := (le_max_left (2 * Real.pi * localizedAmplitudeBound freq ^ 2)
    (2 * localizedDensitySecondMoment freq)).trans ((le_max_right (1 : ℝ) _).trans hc)
  simp only [guard, Nat.cast_add, Nat.cast_one]
  linarith

theorem guard_tail (freq : ℝ) :
    2 * localizedDensitySecondMoment freq ≤ (guard freq : ℝ) := by
  have hc := Nat.le_ceil (max 1 (max (2 * Real.pi * localizedAmplitudeBound freq ^ 2)
    (2 * localizedDensitySecondMoment freq)))
  have h := (le_max_right (2 * Real.pi * localizedAmplitudeBound freq ^ 2)
    (2 * localizedDensitySecondMoment freq)).trans ((le_max_right (1 : ℝ) _).trans hc)
  simp only [guard, Nat.cast_add, Nat.cast_one]
  linarith

theorem scale_eight_le (P : ℕ) : (8 : ℝ) ≤ scale P := by
  simp only [scale, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  linarith [show (0 : ℝ) ≤ P from Nat.cast_nonneg _]

theorem epsilon_positive (freq : ℝ) (P : ℕ) : 0 < (epsilon freq P : ℝ) := by
  have hg := guard_one_le freq
  have hs := scale_eight_le P
  simp only [epsilon, Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_natCast]
  positivity

theorem radius_positive (freq : ℝ) (P : ℕ) : 0 < (radius freq P : ℝ) := by
  have hg := guard_one_le freq
  have hs := scale_eight_le P
  simp only [radius, Nat.cast_mul, Nat.cast_pow]
  positivity

theorem scalar_budget {C S B M : ℝ} (hC : 1 ≤ C) (hS : 1 ≤ S)
    (hB : B ≤ C) (hM : 2 * M ≤ C) :
    B * (1 / (C * S)) ^ 2 + 2 * (1 / (C * S))⁻¹ * M / (C * S ^ 2) ^ 2 ≤
      2 / S ^ 2 := by
  have hC0 : 0 < C := by linarith
  have hS0 : 0 < S := by linarith
  have hcap : B * (1 / (C * S)) ^ 2 ≤ 1 / S ^ 2 := by
    calc
      _ ≤ C * (1 / (C * S)) ^ 2 := mul_le_mul_of_nonneg_right hB (sq_nonneg _)
      _ = C⁻¹ * (1 / S ^ 2) := by field_simp [hC0.ne', hS0.ne']
      _ ≤ 1 / S ^ 2 := mul_le_of_le_one_left (by positivity)
        ((inv_le_one₀ hC0).mpr hC)
  have htail : 2 * (1 / (C * S))⁻¹ * M / (C * S ^ 2) ^ 2 ≤ 1 / S ^ 2 := by
    calc
      _ = (2 * M) * (C * S) / (C * S ^ 2) ^ 2 := by field_simp [hC0.ne', hS0.ne']
      _ ≤ C * (C * S) / (C * S ^ 2) ^ 2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hM (by positivity)) (by positivity)
      _ = (1 / S ^ 2) * S⁻¹ := by field_simp [hC0.ne', hS0.ne']
      _ ≤ 1 / S ^ 2 := mul_le_of_le_one_right (by positivity) ((inv_le_one₀ hS0).mpr hS)
  calc
    _ ≤ 1 / S ^ 2 + 1 / S ^ 2 := add_le_add hcap htail
    _ = _ := by ring

theorem error {freq : ℝ} (hfreq : 0 < freq) (P : ℕ) (u : PlanarPosition) :
    |localizedCoulombProfileAt freq u -
      localizedCoulombBoxIntegral freq (epsilon freq P : ℝ) (radius freq P : ℝ) u| ≤
      (4 * ((P : ℝ) + 1))⁻¹ := by
  have h := localizedCoulombProfile_box_error hfreq (epsilon_positive freq P)
    (radius_positive freq P) u
  have hg := guard_one_le freq
  have hs := scale_eight_le P
  have hb := scalar_budget hg (by linarith : (1 : ℝ) ≤ scale P)
    (guard_cap freq) (guard_tail freq)
  have hcast : (epsilon freq P : ℝ) = 1 / ((guard freq : ℝ) * (scale P : ℝ)) := by
    simp only [epsilon, Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_natCast]
  rw [hcast] at h
  simp only [radius, Nat.cast_mul, Nat.cast_pow] at h
  rw [hcast]
  simp only [radius, Nat.cast_mul, Nat.cast_pow]
  apply (h.trans hb).trans
  have hP : 1 ≤ (P : ℝ) + 1 := by linarith [show (0 : ℝ) ≤ P from Nat.cast_nonneg _]
  simp only [scale, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  calc
    2 / (8 * ((P : ℝ) + 1)) ^ 2 =
        (4 * ((P : ℝ) + 1))⁻¹ * (8 * ((P : ℝ) + 1))⁻¹ := by
      field_simp
      ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity)
      ((inv_le_one₀ (by positivity)).mpr (by linarith))

end ContinuumCoulomb.CoulombTruncationSchedule

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_NormalizationQuadrature
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal quadrature of the actual squared resolvent. Each sample is
computed by the fixed Taylor/heat program, with its proved error. -/

namespace ContinuumCoulomb.NormalizationQuadrature
open ExactQuantumFactoring.BitStackProgram

theorem sample_error (e : Settings) (a b : ℚ)
    (hR : ‖PlanarForcingProgram.position (a, b)‖ ≤ (e.1 : ℝ)) :
    |(sample e a b : ℝ) - planarResolventMode (PlanarForcingProgram.position (a, b)) ^ 2| ≤
      3 * ((e.2 : ℝ) + 1)⁻¹ := by
  rw [sample, Rat.cast_pow]
  apply unitInterval_square_error (planarResolventMode_positive _).le (planarResolventMode_le_one _)
  · exact (inv_le_one₀ (show (0 : ℝ) < (e.2 : ℝ) + 1 by positivity)).mpr
      (show (1 : ℝ) ≤ (e.2 : ℝ) + 1 by
        linarith [show (0 : ℝ) ≤ (e.2 : ℝ) from Nat.cast_nonneg _])
  · exact ResolventSchedule.approximation_error (e, (a, b)) hR

theorem error (x : Input) (hh : 0 ≤ (x.2.2.2 : ℝ))
    (hR : ∀ i < x.1, ∀ j < x.1,
      ‖PlanarForcingProgram.position
        (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 i,
         RationalQuadratureProgram.node x.2.2.1 x.2.2.2 j)‖ ≤ (x.2.1.1 : ℝ)) :
    |(value x : ℝ) -
      ∫ a in (x.2.2.1 : ℝ)..(RationalQuadratureProgram.node x.2.2.1 x.2.2.2 x.1 : ℝ),
        ∫ b in (x.2.2.1 : ℝ)..(RationalQuadratureProgram.node x.2.2.1 x.2.2.2 x.1 : ℝ),
          planarResolventMode (planarPairEquiv.symm (a, b)) ^ 2| ≤
      ((x.1 : ℝ) * (x.2.2.2 : ℝ)) ^ 2 *
        (128 * (x.2.2.2 : ℝ) + 3 * ((x.2.1.2 : ℝ) + 1)⁻¹) := by
  let f := fun a b => planarResolventMode (planarPairEquiv.symm (a, b)) ^ 2
  let v := fun i j => (sample x.2.1
    (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 i)
    (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 j) : ℝ)
  have hx : ∀ a a' b, |f a b - f a' b| ≤ 64 * |a - a'| := by
    intro a a' b
    simpa only [f, planarPair_distance_first] using
      planarResolventMode_square_norm_sub (planarPairEquiv.symm (a, b)) (planarPairEquiv.symm (a', b))
  have hy : ∀ a b b', |f a b - f a b'| ≤ 64 * |b - b'| := by
    intro a b b'
    simpa only [f, planarPair_distance_second] using
      planarResolventMode_square_norm_sub (planarPairEquiv.symm (a, b)) (planarPairEquiv.symm (a, b'))
  have hs : ∀ i < x.1, ∀ j < x.1,
      |v i j - f (UniformQuadrature.node (x.2.2.1 : ℝ) (x.2.2.2 : ℝ) i)
        (UniformQuadrature.node (x.2.2.1 : ℝ) (x.2.2.2 : ℝ) j)| ≤
        3 * ((x.2.1.2 : ℝ) + 1)⁻¹ := by
    intro i hi j hj
    have h := sample_error x.2.1 _ _ (hR i hi j hj)
    simpa only [v, f, rationalPosition_eq_pair, RationalQuadratureProgram.node_cast] using h
  have h := UniformQuadrature.rectangle_error f v _ _ x.1 _ _ x.1 hh hh
    (by norm_num : (0 : ℝ) ≤ 64) (by norm_num : (0 : ℝ) ≤ 64)
    (fun a _ a' _ b _ => hx a a' b) (fun a _ b _ b' _ => hy a b b') hs
  rw [value, RationalRectangleProgram.value_cast]
  simp only [RationalQuadratureProgram.node_cast]
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

end ContinuumCoulomb.NormalizationQuadrature

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarNormalizationTail
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative truncation of the actual planar normalization integral.
All constants below depend only on the fixed manufactured forcing. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem real_quarter_exponential_integral :
    (∫ x : ℝ, Real.exp (-(1 / 4 : ℝ) * |x|)) = 8 := by
  rw [integral_comp_abs (f := fun x : ℝ => Real.exp (-(1 / 4 : ℝ) * x))]
  have h := integral_exp_mul_Ioi (by norm_num : -(1 / 4 : ℝ) < 0) 0
  norm_num at h ⊢
  linarith

theorem planar_half_exponential_integral_le :
    (∫ r : PlanarPosition, Real.exp (-(1 / 2 : ℝ) * ‖r‖)) ≤ 64 := by
  let g := fun x : ℝ => Real.exp (-(1 / 4 : ℝ) * |x|)
  have hg : Integrable g := Integrable.of_integral_ne_zero (by
    change (∫ x : ℝ, Real.exp (-(1 / 4 : ℝ) * |x|)) ≠ 0
    rw [real_quarter_exponential_integral]
    norm_num)
  have hprod : Integrable (fun p : ℝ × ℝ => g p.1 * g p.2) := by
    simpa only [Measure.volume_eq_prod] using hg.mul_prod hg
  have hbound (p : ℝ × ℝ) : Real.exp (-(1 / 2 : ℝ) * ‖planarPairEquiv.symm p‖) ≤
      g p.1 * g p.2 := by
    have h0 : |p.1| ≤ ‖planarPairEquiv.symm p‖ := by
      simpa only [planarPairEquiv_symm_apply, PiLp.toLp_apply, Matrix.cons_val_zero,
        Real.norm_eq_abs] using PiLp.norm_apply_le (planarPairEquiv.symm p) 0
    have h1 : |p.2| ≤ ‖planarPairEquiv.symm p‖ := by
      simpa only [planarPairEquiv_symm_apply, PiLp.toLp_apply, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Real.norm_eq_abs] using PiLp.norm_apply_le (planarPairEquiv.symm p) 1
    dsimp only [g]
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hi : Integrable (fun p : ℝ × ℝ =>
      Real.exp (-(1 / 2 : ℝ) * ‖planarPairEquiv.symm p‖)) := by
    apply hprod.mono' (by fun_prop)
    exact Filter.Eventually.of_forall (fun p => by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact hbound p)
  rw [planarPair_integral]
  apply (integral_mono hi hprod hbound).trans_eq
  rw [Measure.volume_eq_prod, integral_prod_mul]
  change (∫ x : ℝ, Real.exp (-(1 / 4 : ℝ) * |x|)) *
    (∫ x : ℝ, Real.exp (-(1 / 4 : ℝ) * |x|)) = 64
  rw [real_quarter_exponential_integral]
  norm_num

theorem planarNormalizationTailConstant_le : planarNormalizationTailConstant ≤ 1024 := by
  have he := Real.exp_bound_div_one_sub_of_interval (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  norm_num at he
  have hC : 0 ≤ planarExponentialConstant (1 / 2) :=
    (planarExponentialConstant_positive (by norm_num) (by norm_num)).le
  have hC' : planarExponentialConstant (1 / 2) ≤ 4 := by
    unfold planarExponentialConstant
    norm_num
    linarith
  have hm := planar_half_exponential_integral_le
  have hm0 : 0 ≤ ∫ r : PlanarPosition, Real.exp (-(1 / 2 : ℝ) * ‖r‖) :=
    integral_nonneg (fun _ => (Real.exp_pos _).le)
  unfold planarNormalizationTailConstant
  nlinarith

theorem planarResolvent_square_tail_pointwise {L : ℝ} (r : PlanarPosition)
    (hr : L ≤ ‖r‖) :
    planarResolventMode r ^ 2 ≤
      (planarExponentialConstant (1 / 2) ^ 2 * Real.exp (-(1 / 2 : ℝ) * L)) *
        Real.exp (-(1 / 2 : ℝ) * ‖r‖) := by
  have he := pow_le_pow_left₀ (planarResolventMode_positive r).le
    (planarResolventMode_exponential_envelope (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) r) 2
  rw [mul_pow, ← Real.exp_nat_mul] at he
  have hexp : Real.exp ((2 : ℝ) * (-(1 / 2 : ℝ) * ‖r‖)) ≤
      Real.exp (-(1 / 2 : ℝ) * L) * Real.exp (-(1 / 2 : ℝ) * ‖r‖) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  exact he.trans ((mul_le_mul_of_nonneg_left hexp
    (sq_nonneg (planarExponentialConstant (1 / 2)))).trans_eq (by ring))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarNormalizationBox
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite square approximates the actual normalization integral with
an explicit exponential error; no compact-support surrogate is used. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarPair_norm_box {L : ℝ} (hL : 0 ≤ L) {p : ℝ × ℝ}
    (hp : p ∈ Set.Icc (-L) L ×ˢ Set.Icc (-L) L) :
    ‖planarPairEquiv.symm p‖ ≤ 2 * L := by
  have hx : p.1 ^ 2 ≤ L ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg p.1) hL).mpr (abs_le.mpr hp.1)
    simpa only [sq_abs] using h
  have hy : p.2 ^ 2 ≤ L ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg p.2) hL).mpr (abs_le.mpr hp.2)
    simpa only [sq_abs] using h
  have heq := planarPair_norm_sq p
  nlinarith [norm_nonneg (planarPairEquiv.symm p)]

theorem planarNormalizationBox_error {L : ℝ} (hL : 0 ≤ L) :
    |planarNormalizationBox L - (∫ r, planarResolventMode r ^ 2)| ≤
      1024 * Real.exp (-(1 / 2 : ℝ) * L) := by
  let f := fun p : ℝ × ℝ => planarResolventMode (planarPairEquiv.symm p) ^ 2
  let S := Set.Icc (-L) L ×ˢ Set.Icc (-L) L
  let C := planarExponentialConstant (1 / 2) ^ 2 * Real.exp (-(1 / 2 : ℝ) * L)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hf : Continuous f :=
    (planarResolventMode_C7.continuous.comp planarPairEquiv_symm_continuous).pow 2
  have hfi : Integrable f := by
    apply (planarPairEquiv_measurePreserving.integrable_comp hf.aestronglyMeasurable).mp
    change Integrable (fun r : PlanarPosition =>
      planarResolventMode (planarPairEquiv.symm (planarPairEquiv r)) ^ 2)
    simpa only [MeasurableEquiv.symm_apply_apply] using planarResolventMode_square_integrable
  have hg : Continuous (fun p : ℝ × ℝ => Real.exp (-(1 / 2 : ℝ) * ‖planarPairEquiv.symm p‖)) := by
    exact Real.continuous_exp.comp (continuous_const.mul planarPairEquiv_symm_continuous.norm)
  have hgi : Integrable (fun p : ℝ × ℝ => Real.exp (-(1 / 2 : ℝ) * ‖planarPairEquiv.symm p‖)) := by
    apply (planarPairEquiv_measurePreserving.integrable_comp hg.aestronglyMeasurable).mp
    change Integrable (fun r : PlanarPosition =>
      Real.exp (-(1 / 2 : ℝ) * ‖planarPairEquiv.symm (planarPairEquiv r)‖))
    simpa only [MeasurableEquiv.symm_apply_apply] using
      planar_exp_norm_integrable (by norm_num : (0 : ℝ) < 1 / 2)
  have hS : MeasurableSet S := measurableSet_Icc.prod measurableSet_Icc
  have hbox : (∫ p in S, f p) = planarNormalizationBox L := by
    change (∫ p in Set.Icc (-L) L ×ˢ Set.Icc (-L) L, f p) = _
    rw [Measure.volume_eq_prod, setIntegral_prod f hfi.integrableOn]
    simp_rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -L ≤ L)]
    rfl
  have hnorm (p : ℝ × ℝ) (hp : p ∈ Sᶜ) : L ≤ ‖planarPairEquiv.symm p‖ := by
    have h0 : |p.1| ≤ ‖planarPairEquiv.symm p‖ := by
      simpa only [planarPairEquiv_symm_apply, PiLp.toLp_apply, Matrix.cons_val_zero,
        Real.norm_eq_abs] using PiLp.norm_apply_le (planarPairEquiv.symm p) 0
    have h1 : |p.2| ≤ ‖planarPairEquiv.symm p‖ := by
      simpa only [planarPairEquiv_symm_apply, PiLp.toLp_apply, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Real.norm_eq_abs] using PiLp.norm_apply_le (planarPairEquiv.symm p) 1
    by_contra hn
    have hn' : ‖planarPairEquiv.symm p‖ < L := lt_of_not_ge hn
    apply hp
    exact ⟨⟨by linarith [neg_abs_le p.1], by linarith [le_abs_self p.1]⟩,
      ⟨by linarith [neg_abs_le p.2], by linarith [le_abs_self p.2]⟩⟩
  have hout := setIntegral_mono_on hfi.integrableOn (hgi.const_mul C).integrableOn
    hS.compl (fun p hp => planarResolvent_square_tail_pointwise (planarPairEquiv.symm p) (hnorm p hp))
  have htotal := integral_mono_measure (μ := volume.restrict Sᶜ) Measure.restrict_le_self
    (Filter.Eventually.of_forall (fun p =>
      mul_nonneg hC (Real.exp_pos (-(1 / 2 : ℝ) * ‖planarPairEquiv.symm p‖)).le))
    (hgi.const_mul C)
  have heval : (∫ p : ℝ × ℝ, C * Real.exp (-(1 / 2 : ℝ) * ‖planarPairEquiv.symm p‖)) =
      planarNormalizationTailConstant * Real.exp (-(1 / 2 : ℝ) * L) := by
    rw [integral_const_mul,
      ← planarPair_integral (fun r : PlanarPosition => Real.exp (-(1 / 2 : ℝ) * ‖r‖))]
    unfold C planarNormalizationTailConstant
    ring
  have houtBound : (∫ p in Sᶜ, f p) ≤ 1024 * Real.exp (-(1 / 2 : ℝ) * L) :=
    ((hout.trans htotal).trans_eq heval).trans
      (mul_le_mul_of_nonneg_right planarNormalizationTailConstant_le (Real.exp_pos _).le)
  have hout0 : 0 ≤ ∫ p in Sᶜ, f p := integral_nonneg (fun p => sq_nonneg _)
  have heq := integral_add_compl hS hfi
  have hfull : (∫ p, f p) = ∫ r, planarResolventMode r ^ 2 :=
    (planarPair_integral (fun r => planarResolventMode r ^ 2)).symm
  rw [hbox, hfull] at heq
  rw [show planarNormalizationBox L - (∫ r, planarResolventMode r ^ 2) =
    -(∫ p in Sᶜ, f p) by linarith, abs_neg, abs_of_nonneg hout0]
  exact houtBound

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_NormalizationSchedule
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed polynomial schedule for the actual normalization integral.
The outer square grows linearly with inverse accuracy; both nested mesh
counts and the inner resolvent accuracy are explicit natural polynomials. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb.NormalizationSchedule

theorem radius_positive (P : ℕ) : 0 < radius P := by rw [radius_def]; positivity

theorem mesh_positive (P : ℕ) : 0 < mesh P := by
  have h := radius_positive P
  unfold mesh meshPrefix
  positivity

theorem input_step_nonnegative (P : ℕ) : 0 ≤ ((input P).2.2.2 : ℝ) := by
  have hL : (0 : ℚ) < radius P := by exact_mod_cast radius_positive P
  have hN : (0 : ℚ) < mesh P := by exact_mod_cast mesh_positive P
  change 0 ≤ (((2 * (radius P : ℚ)) / (mesh P : ℚ) : ℚ) : ℝ)
  exact_mod_cast (div_nonneg (by positivity : (0 : ℚ) ≤ 2 * radius P) hN.le)

theorem input_endpoint (P : ℕ) :
    RationalQuadratureProgram.node (input P).2.2.1 (input P).2.2.2 (mesh P) = (radius P : ℚ) := by
  have hN : (mesh P : ℚ) ≠ 0 := by exact_mod_cast (mesh_positive P).ne'
  change -(radius P : ℚ) + (mesh P : ℚ) * (2 * (radius P : ℚ) / (mesh P : ℚ)) = _
  field_simp
  ring

theorem input_node_mem (P i : ℕ) (hi : i ≤ mesh P) :
    (RationalQuadratureProgram.node (input P).2.2.1 (input P).2.2.2 i : ℝ) ∈
      Set.Icc (-(radius P : ℝ)) (radius P : ℝ) := by
  have h := UniformQuadrature.node_mem (a := ((input P).2.2.1 : ℝ))
    (input_step_nonnegative P) hi
  rw [← RationalQuadratureProgram.node_cast, ← RationalQuadratureProgram.node_cast,
    input_endpoint P] at h
  simpa only [input, Rat.cast_neg, Rat.cast_natCast] using h

theorem input_nodes_norm (P i j : ℕ) (hi : i < mesh P) (hj : j < mesh P) :
    ‖PlanarForcingProgram.position
      (RationalQuadratureProgram.node (input P).2.2.1 (input P).2.2.2 i,
       RationalQuadratureProgram.node (input P).2.2.1 (input P).2.2.2 j)‖ ≤
      (2 * radius P : ℕ) := by
  rw [rationalPosition_eq_pair, Nat.cast_mul, Nat.cast_ofNat]
  exact planarPair_norm_box (by exact_mod_cast (radius_positive P).le)
    ⟨input_node_mem P i hi.le, input_node_mem P j hj.le⟩

theorem numerical_budget {L S N K : ℝ} (hL : 0 < L) (hS : 0 < S)
    (hN : N = 4096 * L ^ 3 * S) (hK : K = 48 * L ^ 2 * S)
    (hLS : L = 8192 * S) :
    (N * (2 * L / N)) ^ 2 * (128 * (2 * L / N) + 3 / (K + 1)) +
      1024 * Real.exp (-(1 / 2 : ℝ) * L) ≤ S⁻¹ := by
  have hN0 : 0 < N := by rw [hN]; positivity
  have hK0 : 0 < K := by rw [hK]; positivity
  have hlen : N * (2 * L / N) = 2 * L := by field_simp [hN0.ne']
  have hs : (2 * L) ^ 2 * (128 * (2 * L / N)) = (4 * S)⁻¹ := by
    rw [hN]
    field_simp [hL.ne', hS.ne']
    ring
  have hb : (2 * L) ^ 2 * (3 / (K + 1)) ≤ (4 * S)⁻¹ := by
    calc
      _ ≤ (2 * L) ^ 2 * (3 / K) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (by norm_num) hK0 (by linarith)) (sq_nonneg _)
      _ = _ := by rw [hK]; field_simp [hL.ne', hS.ne']; ring
  have ht : 1024 * Real.exp (-(1 / 2 : ℝ) * L) ≤ (4 * S)⁻¹ := by
    calc
      _ ≤ 1024 * (L / 2)⁻¹ := by
        have he := ResolventSchedule.exp_tail_le_inverse (show 0 < L / 2 by positivity)
        have he' : Real.exp (-(1 / 2 : ℝ) * L) ≤ (L / 2)⁻¹ := by
          rw [show -(1 / 2 : ℝ) * L = -(L / 2) by ring]
          exact he
        exact mul_le_mul_of_nonneg_left he' (by norm_num)
      _ = _ := by rw [hLS]; field_simp [hS.ne']; ring
  rw [hlen, mul_add, hs]
  have hsmall : 3 * (4 * S)⁻¹ ≤ S⁻¹ := by
    rw [mul_inv]
    norm_num
    nlinarith [inv_pos.mpr hS]
  linarith

theorem approximation_error (P : ℕ) :
    |(approximate P : ℝ) - (∫ r, planarResolventMode r ^ 2)| ≤ ((P : ℝ) + 1)⁻¹ := by
  let L := (radius P : ℝ)
  let N := (mesh P : ℝ)
  let K := (accuracy P : ℝ)
  let S := (P : ℝ) + 1
  have hL : 0 < L := by
    dsimp only [L]
    exact_mod_cast radius_positive P
  have hS : 0 < S := by dsimp [S]; positivity
  have hN : N = 4096 * L ^ 3 * S := by
    dsimp [N, L, S, mesh, meshPrefix]
    push_cast
    rfl
  have hK : K = 48 * L ^ 2 * S := by
    dsimp [K, L, S, accuracy, accuracyPrefix]
    push_cast
    rfl
  have hLS : L = 8192 * S := by
    dsimp only [L, S]
    rw [radius_def]
    push_cast
    rfl
  have hquad := NormalizationQuadrature.error (input P) (input_step_nonnegative P)
    (fun i hi j hj => input_nodes_norm P i j hi hj)
  have hend : RationalQuadratureProgram.node (input P).2.2.1 (input P).2.2.2
      (input P).1 = (radius P : ℚ) := input_endpoint P
  rw [hend] at hquad
  have hquad' : |(approximate P : ℝ) - planarNormalizationBox L| ≤
      (N * (2 * L / N)) ^ 2 * (128 * (2 * L / N) + 3 / (K + 1)) := by
    dsimp only [L, N, K]
    simpa only [approximate, planarNormalizationBox, input, Rat.cast_neg, Rat.cast_natCast,
      Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, div_eq_mul_inv, Rat.cast_inv] using hquad
  have htail := planarNormalizationBox_error hL.le
  have htotal := (abs_sub_le (approximate P : ℝ) (planarNormalizationBox L)
    (∫ r, planarResolventMode r ^ 2)).trans (add_le_add hquad' htail)
  exact htotal.trans (numerical_budget hL hS hN hK hLS)

end ContinuumCoulomb.NormalizationSchedule

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombNormalizationError
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Stability of the exact fixed normalization factor ω/(A²π). -/

noncomputable section
namespace ContinuumCoulomb

theorem guarded_inverse_error {C a a' ε : ℝ} (hC : 0 < C) (ha : 0 < a)
    (hguard : 2 ≤ C * a) (hε : 0 ≤ ε) (hsmall : C * ε ≤ 1)
    (he : |a' - a| ≤ ε) :
    0 < a' ∧ a⁻¹ ≤ C ∧ a'⁻¹ ≤ C ∧ |a'⁻¹ - a⁻¹| ≤ C ^ 2 * ε := by
  have hl := mul_le_mul_of_nonneg_left (abs_le.mp he).1 hC.le
  have hguard' : 1 ≤ C * a' := by nlinarith
  have ha' : 0 < a' := by
    by_contra hn
    have hm := mul_nonpos_of_nonneg_of_nonpos hC.le (le_of_not_gt hn)
    linarith
  have hi : a⁻¹ ≤ C := (inv_le_iff_one_le_mul₀ ha).mpr (by linarith)
  have hi' : a'⁻¹ ≤ C := (inv_le_iff_one_le_mul₀ ha').mpr hguard'
  refine ⟨ha', hi, hi', ?_⟩
  have hid : a'⁻¹ - a⁻¹ = (a - a') * a'⁻¹ * a⁻¹ := by
    field_simp [ha.ne', ha'.ne']
  rw [hid, abs_mul, abs_mul, abs_sub_comm a a',
    abs_of_pos (inv_pos.mpr ha'), abs_of_pos (inv_pos.mpr ha)]
  calc
    _ ≤ ε * C * C := by gcongr
    _ = _ := by ring

theorem coulomb_normalization_error {C a a' p p' f f' ε : ℝ}
    (hC : 1 ≤ C) (ha : 0 < a) (hp : 0 < p)
    (hga : 2 ≤ C * a) (hgp : 2 ≤ C * p) (hf : |f| ≤ C)
    (hε : 0 ≤ ε) (hsmall : C * ε ≤ 1)
    (hea : |a' - a| ≤ ε) (hep : |p' - p| ≤ ε) (hef : |f' - f| ≤ ε) :
    |f' / (a' ^ 2 * p') - f / (a ^ 2 * p)| ≤ (C ^ 3 + 3 * C ^ 5) * ε := by
  have hC0 : 0 < C := by linarith
  obtain ⟨ha', hia, hia', heia⟩ := guarded_inverse_error hC0 ha hga hε hsmall hea
  obtain ⟨hp', hip, hip', heip⟩ := guarded_inverse_error hC0 hp hgp hε hsmall hep
  have hsq : |a'⁻¹ ^ 2 - a⁻¹ ^ 2| ≤ 2 * C ^ 3 * ε := by
    have hid : a'⁻¹ ^ 2 - a⁻¹ ^ 2 = (a'⁻¹ - a⁻¹) * (a'⁻¹ + a⁻¹) := by ring
    rw [hid, abs_mul, abs_of_pos (add_pos (inv_pos.mpr ha') (inv_pos.mpr ha))]
    calc
      _ ≤ (C ^ 2 * ε) * (C + C) := by gcongr
      _ = _ := by ring
  have hid : f' / (a' ^ 2 * p') - f / (a ^ 2 * p) =
      (f' - f) * a'⁻¹ ^ 2 * p'⁻¹ +
        f * (a'⁻¹ ^ 2 - a⁻¹ ^ 2) * p'⁻¹ +
        f * a⁻¹ ^ 2 * (p'⁻¹ - p⁻¹) := by
    field_simp [ha.ne', ha'.ne', hp.ne', hp'.ne']
    ring
  have h1 : |(f' - f) * a'⁻¹ ^ 2 * p'⁻¹| ≤ C ^ 3 * ε := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg a'⁻¹), abs_of_pos (inv_pos.mpr hp')]
    calc
      _ ≤ ε * C ^ 2 * C := by gcongr
      _ = _ := by ring
  have h2 : |f * (a'⁻¹ ^ 2 - a⁻¹ ^ 2) * p'⁻¹| ≤ 2 * C ^ 5 * ε := by
    rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hp')]
    calc
      _ ≤ C * (2 * C ^ 3 * ε) * C := by gcongr
      _ = _ := by ring
  have h3 : |f * a⁻¹ ^ 2 * (p'⁻¹ - p⁻¹)| ≤ C ^ 5 * ε := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg a⁻¹)]
    calc
      _ ≤ C * C ^ 2 * (C ^ 2 * ε) := by gcongr
      _ = _ := by ring
  rw [hid]
  exact ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
    ((add_le_add (add_le_add h1 h2) h3).trans_eq (by ring))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_CoulombNormalizationProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A certified rational evaluator for the fixed Coulomb normalization
factor. The natural guard depends only on the fixed one-well model. -/

noncomputable section
namespace ContinuumCoulomb.CoulombNormalization
open ExactQuantumFactoring.BitStackProgram

theorem guard_bounds (freq : ℝ) :
    1 ≤ (guard freq : ℝ) ∧ |freq| ≤ (guard freq : ℝ) ∧
      2 ≤ (guard freq : ℝ) * (∫ r, planarResolventMode r ^ 2) ∧
      2 ≤ (guard freq : ℝ) * Real.pi := by
  let M := max 1 (max |freq| (max (2 / (∫ r, planarResolventMode r ^ 2)) (2 / Real.pi)))
  have hm : M ≤ (guard freq : ℝ) := by
    have hh := Nat.le_ceil M
    simp only [guard, Nat.cast_add, Nat.cast_one]
    linarith
  have h1 : (1 : ℝ) ≤ M := le_max_left _ _
  have hf : |freq| ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have ha : 2 / (∫ r, planarResolventMode r ^ 2) ≤ M :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hp : 2 / Real.pi ≤ M :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  exact ⟨h1.trans hm, hf.trans hm,
    (div_le_iff₀ planarResolventMode_square_integral_positive).mp (ha.trans hm),
    (div_le_iff₀ Real.pi_pos).mp (hp.trans hm)⟩

theorem precision_bounds (rho P : ℕ) :
    (guard (GaussianFrequency.frequency rho) : ℝ) * ((precision rho P : ℝ) + 1)⁻¹ ≤ 1 ∧
      (factorBound (guard (GaussianFrequency.frequency rho)) : ℝ) *
        ((precision rho P : ℝ) + 1)⁻¹ ≤ ((P : ℝ) + 1)⁻¹ := by
  let C := (guard (GaussianFrequency.frequency rho) : ℝ)
  let K := (factorBound (guard (GaussianFrequency.frequency rho)) : ℝ)
  let S := (P : ℝ) + 1
  have hC : 0 ≤ C := Nat.cast_nonneg _
  have hK : 0 ≤ K := Nat.cast_nonneg _
  have hS : 1 ≤ S := by
    dsimp [S]
    linarith [show (0 : ℝ) ≤ P from Nat.cast_nonneg _]
  have hN : (precision rho P : ℝ) = (C + K) * S := by
    simp only [precision, Nat.cast_mul, Nat.cast_add, Nat.cast_one, C, K, S]
  have hn : (0 : ℝ) < precision rho P + 1 := by positivity
  have hCa : C ≤ (precision rho P : ℝ) + 1 := by
    rw [hN]
    nlinarith [mul_nonneg hK (show 0 ≤ S by linarith)]
  have hKa : K * S ≤ (precision rho P : ℝ) + 1 := by
    rw [hN]
    nlinarith [mul_nonneg hC (show 0 ≤ S by linarith)]
  constructor
  · change C * ((precision rho P : ℝ) + 1)⁻¹ ≤ 1
    rw [← div_eq_mul_inv]
    exact (div_le_one hn).mpr hCa
  · change K * ((precision rho P : ℝ) + 1)⁻¹ ≤ S⁻¹
    rw [← div_eq_mul_inv, ← one_div]
    exact (div_le_div_iff₀ hn (by linarith : 0 < S)).mpr (by simpa using hKa)

theorem approximation_error (rho P : ℕ) :
    |(approximate rho P : ℝ) - coefficient (GaussianFrequency.frequency rho)| ≤
      ((P : ℝ) + 1)⁻¹ := by
  let N := precision rho P
  have hc := guard_bounds (GaussianFrequency.frequency rho)
  have hπ := PiProgram.error (8 * (N + 1)) (by omega)
  have hπ' : |(PiProgram.approximate (8 * (N + 1)) : ℝ) - Real.pi| ≤ ((N : ℝ) + 1)⁻¹ := by
    convert hπ using 1
    all_goals try with_reducible_and_instances rfl
    push_cast
    field_simp
  have h := coulomb_normalization_error hc.1 planarResolventMode_square_integral_positive
    Real.pi_pos hc.2.2.1 hc.2.2.2 hc.2.1 (by positivity) (precision_bounds rho P).1
    (NormalizationSchedule.approximation_error N) hπ' (GaussianFrequency.approximation_error rho N)
  have he : (factorBound (guard (GaussianFrequency.frequency rho)) : ℝ) =
      (guard (GaussianFrequency.frequency rho) : ℝ) ^ 3 +
        3 * (guard (GaussianFrequency.frequency rho) : ℝ) ^ 5 := by
    simp only [factorBound, Nat.cast_add, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]
  rw [← he] at h
  have h' : |(approximate rho P : ℝ) - coefficient (GaussianFrequency.frequency rho)| ≤
      (factorBound (guard (GaussianFrequency.frequency rho)) : ℝ) * ((N : ℝ) + 1)⁻¹ := by
    simpa only [approximate, coefficient, Rat.cast_div, Rat.cast_mul, Rat.cast_pow, N] using h
  exact h'.trans (precision_bounds rho P).2

end ContinuumCoulomb.CoulombNormalization

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_RawCoulombMassBound
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform raw-integral bounds for certified normalization of the
finite-box numerical output. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem localizedRawCoulombBox_bound {freq ε : ℝ} (hf : 0 < freq) (hε : 0 < ε)
    (L : ℝ) (u : PlanarPosition) :
    |localizedRawCoulombBox freq ε L u| ≤ ε⁻¹ * localizedRawMass freq ^ 2 := by
  let f := localizedRawDensity freq
  let S := coulombNumericalBox L ×ˢ coulombNumericalBox L
  let F := cappedPairIntegrand ε (planarCenter u) f f
  have hfi := localizedRawDensity_integrable hf
  have hm : Integrable (fun p : Position × Position => ε⁻¹ * (f p.1 * f p.2)) := by
    have hp : Integrable (fun p : Position × Position => f p.1 * f p.2) := by
      simpa only [Measure.volume_eq_prod] using hfi.mul_prod hfi
    exact hp.const_mul _
  have hpoint (p : Position × Position) : ‖S.indicator F p‖ ≤ ε⁻¹ * (f p.1 * f p.2) := by
    by_cases hp : p ∈ S
    · rw [Set.indicator_of_mem hp, Real.norm_of_nonneg (show 0 ≤ F p from
        mul_nonneg (mul_nonneg (localizedRawDensity_nonnegative _ _)
          (localizedRawDensity_nonnegative _ _)) (cappedCoulombKernel_nonnegative hε _))]
      change f p.1 * f p.2 * cappedCoulombKernel ε _ ≤ _
      calc
        _ ≤ f p.1 * f p.2 * ε⁻¹ := mul_le_mul_of_nonneg_left (cappedCoulombKernel_le hε _)
          (mul_nonneg (localizedRawDensity_nonnegative _ _) (localizedRawDensity_nonnegative _ _))
        _ = _ := by ring
    · rw [Set.indicator_of_notMem hp, norm_zero]
      exact mul_nonneg (inv_nonneg.mpr hε.le)
        (mul_nonneg (localizedRawDensity_nonnegative _ _) (localizedRawDensity_nonnegative _ _))
  have hb := norm_integral_le_of_norm_le (f := S.indicator F) hm (Filter.Eventually.of_forall hpoint)
  rw [integral_indicator ((coulombNumericalBox_measurable L).prod
    (coulombNumericalBox_measurable L)), Real.norm_eq_abs] at hb
  apply hb.trans_eq
  rw [integral_const_mul, Measure.volume_eq_prod, integral_prod_mul]
  change ε⁻¹ * ((∫ x, localizedRawDensity freq x) * ∫ x, localizedRawDensity freq x) = _
  rw [localizedRawDensity_mass hf]
  ring

theorem localizedCoulombBox_eq_normalizedRaw {freq : ℝ} (hf : 0 < freq)
    (ε L : ℝ) (u : PlanarPosition) :
    localizedCoulombBoxIntegral freq ε L u =
      CoulombNormalization.coefficient freq * localizedRawCoulombBox freq ε L u := by
  rw [← localizedRawCoulombBox_quotient hf ε L u]
  unfold CoulombNormalization.coefficient
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombEvaluationParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One fixed set of polynomial precision parameters for the actual
localized Coulomb coefficient. Only the requested accuracy varies. -/

noncomputable section
namespace ContinuumCoulomb.CoulombEvaluation

theorem frequencyBound_le (rho : ℕ) : GaussianFrequency.frequency rho ≤ (frequencyBound rho : ℝ) := by
  have h := Nat.le_ceil (GaussianFrequency.frequency rho)
  simp only [frequencyBound, Nat.cast_add, Nat.cast_one]
  linarith

theorem normalizationBound_bounds (rho : ℕ) :
    1 ≤ (normalizationBound rho : ℝ) ∧
      CoulombNormalization.coefficient (GaussianFrequency.frequency rho) ≤ normalizationBound rho := by
  have h := Nat.le_ceil (max 1 (CoulombNormalization.coefficient (GaussianFrequency.frequency rho)))
  have h1 := (le_max_left (1 : ℝ) _).trans h
  have h2 := (le_max_right (1 : ℝ) _).trans h
  simp only [normalizationBound, Nat.cast_add, Nat.cast_one]
  constructor <;> linarith

theorem rawMassBound_le (rho : ℕ) :
    localizedRawMass (GaussianFrequency.frequency rho) ^ 2 + 1 ≤ (rawMassBound rho : ℝ) := by
  have h := Nat.le_ceil (localizedRawMass (GaussianFrequency.frequency rho) ^ 2 + 1)
  simp only [rawMassBound, Nat.cast_add, Nat.cast_one]
  linarith

theorem denominator_positive (rho P : ℕ) : 0 < denominator rho P := by
  have hg := CoulombTruncationSchedule.guard_one_le (GaussianFrequency.frequency rho)
  have hs := CoulombTruncationSchedule.scale_eight_le (truncationPrecision P)
  have h : (0 : ℝ) < denominator rho P := by
    simp only [denominator, Nat.cast_mul]
    positivity
  exact_mod_cast h

theorem radius_positive (rho P : ℕ) : 0 < radius rho P := by
  exact_mod_cast CoulombTruncationSchedule.radius_positive
    (GaussianFrequency.frequency rho) (truncationPrecision P)

theorem rawPrecision_positive (rho P : ℕ) : 0 < rawPrecision rho P := by
  have hc : 0 < normalizationBound rho := by
    have h := (normalizationBound_bounds rho).1
    exact_mod_cast (show (0 : ℝ) < normalizationBound rho by linarith)
  unfold rawPrecision
  positivity

theorem mesh_positive (rho P : ℕ) : 0 < mesh rho P := by
  have hR := radius_positive rho P
  have hD := denominator_positive rho P
  have hS := rawPrecision_positive rho P
  have hA : 0 < 64 + 2 * frequencyBound rho * radius rho P := by omega
  have hL : 0 < CoulombQuadratureSchedule.lipschitz (frequencyBound rho)
      (radius rho P) (denominator rho P) := by
    unfold CoulombQuadratureSchedule.lipschitz
    exact lt_of_lt_of_le (Nat.mul_pos hA hD) (Nat.le_add_right _ _)
  have hV : 0 < CoulombQuadratureSchedule.volume (radius rho P) := by
    change 0 < (2 * radius rho P) ^ 6
    exact pow_pos (Nat.mul_pos (by decide) hR) _
  change 0 < 48 * radius rho P *
    CoulombQuadratureSchedule.lipschitz (frequencyBound rho) (radius rho P) (denominator rho P) *
      CoulombQuadratureSchedule.volume (radius rho P) * rawPrecision rho P
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) hR) hL) hV) hS

theorem epsilon_eq (rho P : ℕ) :
    (1 / (denominator rho P : ℚ) : ℝ) =
      (CoulombTruncationSchedule.epsilon (GaussianFrequency.frequency rho) (truncationPrecision P) : ℝ) := by
  simp only [denominator, CoulombTruncationSchedule.epsilon, Rat.cast_div, Rat.cast_one,
    Rat.cast_natCast, Rat.cast_mul, Nat.cast_mul]

end ContinuumCoulomb.CoulombEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombRawEvaluation
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed polynomial schedule approximates the actual unnormalized
Coulomb box integral uniformly in every rational separation. -/

noncomputable section
namespace ContinuumCoulomb.CoulombEvaluation
open UniformQuadrature

theorem position_shift (d : ℚ) :
    CappedKernelProgram.position (d, 0, 0) = planarCenter ((d : ℝ) • planarAxis 0) := by
  apply positionSplitCoordinates.injective
  rw [RawDensitySample.position_split]
  simp only [planarCenter, ContinuousLinearEquiv.apply_symm_apply]
  apply Prod.ext
  · ext i
    fin_cases i <;> simp [PlanarForcingProgram.position, planarAxis]
  · simp

theorem denominator_inverse (rho P : ℕ) :
    (1 / (denominator rho P : ℚ) : ℝ)⁻¹ = (denominator rho P : ℝ) := by
  simp only [Rat.cast_natCast, one_div, inv_inv]

theorem rational_box_quadrature_error (rho R Q b N D : ℕ) (hD : 0 < D) (hN : 0 < N) (d : ℚ)
    (hf : 0 < GaussianFrequency.frequency rho) :
    |(RationalSixQuadrature.value (RawCoulombSample.sixEvaluator rho)
        (RawCoulombSample.quadratureInput R Q b (1 / (D : ℚ)) (d, 0, 0) N) : ℝ) -
      localizedRawCoulombBox (GaussianFrequency.frequency rho) (1 / (D : ℝ)) R
        ((d : ℝ) • planarAxis 0)| ≤
      (2 * (R : ℝ)) ^ 6 *
        (6 * ((64 + 2 * GaussianFrequency.frequency rho * R) * D + (D : ℝ) ^ 2) *
          (2 * (R : ℝ) / N) +
          (8 * D * ((Q : ℝ) + 1)⁻¹ + (D : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ b)) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hε : (0 : ℚ) < 1 / (D : ℚ) := by positivity
  have hεr : (0 : ℝ) < 1 / (D : ℝ) := by positivity
  have hq := RawCoulombSample.quadrature_error rho R Q b N hε hN (d, 0, 0)
  have hbox := localizedRawCoulombBox_cube hf hεr (Nat.cast_nonneg R) ((d : ℝ) • planarAxis 0)
  rw [← position_shift] at hbox
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast] at hq
  have hbox' : cubeIntegral (-(R : ℝ)) (R : ℝ) 6
      (rawCoulombSix (GaussianFrequency.frequency rho) (1 / (D : ℝ))
        (CappedKernelProgram.position (d, 0, 0))) =
      localizedRawCoulombBox (GaussianFrequency.frequency rho) (1 / (D : ℝ))
        (R : ℝ) ((d : ℝ) • planarAxis 0) := hbox.symm
  rw [hbox'] at hq
  simpa only [one_div, inv_inv] using hq

theorem natural_quadrature_budget (F R D S : ℕ) {f : ℝ}
    (hRnat : 0 < R) (hDnat : 0 < D) (hSnat : 0 < S) (hf : f ≤ F) :
    (2 * (R : ℝ)) ^ 6 *
        (6 * ((64 + 2 * f * R) * D + (D : ℝ) ^ 2) *
          (2 * (R : ℝ) / CoulombQuadratureSchedule.mesh F R D S) +
          (8 * D * ((CoulombQuadratureSchedule.accuracy R D S : ℝ) + 1)⁻¹ +
            (D : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ CoulombQuadratureSchedule.kernelPrecision R D S)) ≤
      3 * (4 * (S : ℝ))⁻¹ := by
  let L := CoulombQuadratureSchedule.lipschitz F R D
  let V := CoulombQuadratureSchedule.volume R
  have hR : (0 : ℝ) < R := by exact_mod_cast hRnat
  have hD : (0 : ℝ) < D := by exact_mod_cast hDnat
  have hS : (0 : ℝ) < S := by exact_mod_cast hSnat
  have hV : (V : ℝ) = (2 * (R : ℝ)) ^ 6 := by
    simp only [V, CoulombQuadratureSchedule.volume, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]
  have hL : (L : ℝ) = (64 + 2 * (F : ℝ) * R) * D + (D : ℝ) ^ 2 := by
    simp only [L, CoulombQuadratureSchedule.lipschitz, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_pow]
  have hL0 : (0 : ℝ) < L := by rw [hL]; positivity
  have hN : (CoulombQuadratureSchedule.mesh F R D S : ℝ) = 48 * R * L * V * S := by
    simp only [CoulombQuadratureSchedule.mesh, Nat.cast_mul, Nat.cast_ofNat, L, V]
  have hQ : (CoulombQuadratureSchedule.accuracy R D S : ℝ) = 32 * D * V * S := by
    simp only [CoulombQuadratureSchedule.accuracy, Nat.cast_mul, Nat.cast_ofNat, V]
  have hb : (CoulombQuadratureSchedule.kernelPrecision R D S : ℝ) = 4 * (D : ℝ) ^ 2 * V * S := by
    simp only [CoulombQuadratureSchedule.kernelPrecision,
      Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, V]
  have hLip : (64 + 2 * f * R) * D + (D : ℝ) ^ 2 ≤ L := by
    rw [hL]
    gcongr
  have hupper := CoulombQuadratureSchedule.scalar_budget hR hD hL0 hS hV hN hQ hb
  apply le_trans _ hupper
  rw [hV]
  simp only [add_assoc]
  gcongr

theorem raw_approximation_error (rho P : ℕ) (hrho : 0 < rho) (d : ℚ) :
    |(rawApproximate rho P d : ℝ) -
      localizedRawCoulombBox (GaussianFrequency.frequency rho)
        (1 / (denominator rho P : ℚ) : ℝ) (radius rho P : ℝ) ((d : ℝ) • planarAxis 0)| ≤
      3 * (4 * (rawPrecision rho P : ℝ))⁻¹ := by
  have hf : 0 < GaussianFrequency.frequency rho := Real.sqrt_pos.mpr (by
    change 0 < 4 * Real.pi * (rho : ℝ)
    positivity)
  have hq := rational_box_quadrature_error rho (radius rho P) (samplePrecision rho P)
    (kernelPrecision rho P) (mesh rho P) (denominator rho P) (denominator_positive rho P)
      (mesh_positive rho P) d hf
  have hb := natural_quadrature_budget (frequencyBound rho) (radius rho P)
    (denominator rho P) (rawPrecision rho P) (radius_positive rho P)
      (denominator_positive rho P) (rawPrecision_positive rho P) (frequencyBound_le rho)
  have hc := hq.trans hb
  simpa only [rawApproximate, input, Rat.cast_natCast] using hc

end ContinuumCoulomb.CoulombEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombEvaluationError
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! End-to-end error accounting for the actual Coulomb coefficient. -/

noncomputable section
namespace ContinuumCoulomb.CoulombEvaluation

theorem truncation_error (rho P : ℕ) (hrho : 0 < rho) (d : ℚ) :
    |localizedCoulombProfile (GaussianFrequency.frequency rho) (d : ℝ) -
      localizedCoulombBoxIntegral (GaussianFrequency.frequency rho)
        (1 / (denominator rho P : ℚ) : ℝ) (radius rho P : ℝ) ((d : ℝ) • planarAxis 0)| ≤
      (4 * ((P : ℝ) + 1))⁻¹ := by
  have hf : 0 < GaussianFrequency.frequency rho := Real.sqrt_pos.mpr (by
    change 0 < 4 * Real.pi * (rho : ℝ)
    positivity)
  have ht := CoulombTruncationSchedule.error hf (truncationPrecision P) ((d : ℝ) • planarAxis 0)
  rw [← epsilon_eq] at ht
  apply ht.trans
  apply inv_anti₀ (by positivity)
  have h : P ≤ truncationPrecision P := by unfold truncationPrecision; omega
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.add_le_add_right h 1) (by norm_num)

theorem rawPrecision_one_le (rho P : ℕ) : 1 ≤ (rawPrecision rho P : ℝ) := by
  have hc := (normalizationBound_bounds rho).1
  have hp : 1 ≤ (P : ℝ) + 1 := by linarith [show (0 : ℝ) ≤ P from Nat.cast_nonneg _]
  have hprod : 1 ≤ (normalizationBound rho : ℝ) * ((P : ℝ) + 1) :=
    one_le_mul_of_one_le_of_one_le hc hp
  simp only [rawPrecision, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  nlinarith

theorem rawApproximate_bound (rho P : ℕ) (hrho : 0 < rho) (d : ℚ) :
    |(rawApproximate rho P d : ℝ)| ≤ (rawMassBound rho : ℝ) * denominator rho P := by
  let I := localizedRawCoulombBox (GaussianFrequency.frequency rho)
    (1 / (denominator rho P : ℚ) : ℝ) (radius rho P : ℝ) ((d : ℝ) • planarAxis 0)
  have hf : 0 < GaussianFrequency.frequency rho := Real.sqrt_pos.mpr (by
    change 0 < 4 * Real.pi * (rho : ℝ)
    positivity)
  have hD : (1 : ℝ) ≤ denominator rho P := by exact_mod_cast denominator_positive rho P
  have hε : (0 : ℝ) < (1 / (denominator rho P : ℚ) : ℝ) := by
    simp only [Rat.cast_natCast]
    positivity
  have hI := localizedRawCoulombBox_bound hf hε (radius rho P : ℝ) ((d : ℝ) • planarAxis 0)
  rw [denominator_inverse] at hI
  have he := raw_approximation_error rho P hrho d
  have hS := rawPrecision_one_le rho P
  have he1 : |(rawApproximate rho P d : ℝ) - I| ≤ 1 := by
    apply he.trans
    rw [← div_eq_mul_inv]
    exact (div_le_one (by positivity : 0 < 4 * (rawPrecision rho P : ℝ))).mpr (by linarith)
  have htriangle : |(rawApproximate rho P d : ℝ)| ≤ |(rawApproximate rho P d : ℝ) - I| + |I| := by
    calc
      _ = |((rawApproximate rho P d : ℝ) - I) + I| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  have hM := rawMassBound_le rho
  have hMD := mul_le_mul_of_nonneg_right hM (show (0 : ℝ) ≤ denominator rho P by linarith)
  nlinarith

theorem raw_normalization_budget (rho P : ℕ) :
    CoulombNormalization.coefficient (GaussianFrequency.frequency rho) *
      (3 * (4 * (rawPrecision rho P : ℝ))⁻¹) ≤ (4 * ((P : ℝ) + 1))⁻¹ := by
  have hC := (normalizationBound_bounds rho).1
  have hα := (normalizationBound_bounds rho).2
  have hp : (0 : ℝ) < P + 1 := by positivity
  calc
    _ ≤ (normalizationBound rho : ℝ) * (3 * (4 * (rawPrecision rho P : ℝ))⁻¹) :=
      mul_le_mul_of_nonneg_right hα (by positivity)
    _ = (3 / 16 : ℝ) * ((P : ℝ) + 1)⁻¹ := by
      simp only [rawPrecision, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
      have hc0 : (normalizationBound rho : ℝ) ≠ 0 := ne_of_gt (by linarith)
      field_simp [hc0, hp.ne']
      ring
    _ ≤ _ := by rw [mul_inv]; norm_num; nlinarith [inv_pos.mpr hp]

theorem normalization_rounding_budget (rho P : ℕ) :
    (rawMassBound rho : ℝ) * denominator rho P *
      ((normalizationPrecision rho P : ℝ) + 1)⁻¹ ≤ (4 * ((P : ℝ) + 1))⁻¹ := by
  have hM : (0 : ℝ) < rawMassBound rho := by
    have h := rawMassBound_le rho
    nlinarith [sq_nonneg (localizedRawMass (GaussianFrequency.frequency rho))]
  have hD : (0 : ℝ) < denominator rho P := by exact_mod_cast denominator_positive rho P
  have hp : (0 : ℝ) < P + 1 := by positivity
  have hn : (0 : ℝ) < normalizationPrecision rho P := by
    simp only [normalizationPrecision, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
    positivity
  calc
    _ ≤ (rawMassBound rho : ℝ) * denominator rho P * (normalizationPrecision rho P : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left (inv_anti₀ hn (by linarith)) (by positivity)
    _ = (8 * ((P : ℝ) + 1))⁻¹ := by
      simp only [normalizationPrecision, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
      field_simp [hM.ne', hD.ne', hp.ne']
    _ ≤ _ := inv_anti₀ (by positivity) (by linarith)

theorem approximation_error (rho P : ℕ) (hrho : 0 < rho) (d : ℚ) :
    |(approximate rho P d : ℝ) - localizedCoulombProfile (GaussianFrequency.frequency rho) (d : ℝ)| ≤
      ((P : ℝ) + 1)⁻¹ := by
  let α := CoulombNormalization.coefficient (GaussianFrequency.frequency rho)
  let α' : ℝ := CoulombNormalization.approximate rho (normalizationPrecision rho P)
  let q : ℝ := rawApproximate rho P d
  let I := localizedRawCoulombBox (GaussianFrequency.frequency rho)
    (1 / (denominator rho P : ℚ) : ℝ) (radius rho P : ℝ) ((d : ℝ) • planarAxis 0)
  have hf : 0 < GaussianFrequency.frequency rho := Real.sqrt_pos.mpr (by
    change 0 < 4 * Real.pi * (rho : ℝ)
    positivity)
  have hα0 : 0 ≤ α := by unfold α CoulombNormalization.coefficient; positivity
  have heq : α' * q - α * I = (α' - α) * q + α * (q - I) := by ring
  have hfirst : |(α' - α) * q| ≤ (4 * ((P : ℝ) + 1))⁻¹ := by
    rw [abs_mul]
    have h := mul_le_mul (CoulombNormalization.approximation_error rho (normalizationPrecision rho P))
      (rawApproximate_bound rho P hrho d) (abs_nonneg q) (by positivity)
    apply h.trans
    simpa only [mul_comm] using normalization_rounding_budget rho P
  have hsecond : |α * (q - I)| ≤ (4 * ((P : ℝ) + 1))⁻¹ := by
    rw [abs_mul, abs_of_nonneg hα0]
    exact (mul_le_mul_of_nonneg_left (raw_approximation_error rho P hrho d) hα0).trans
      (raw_normalization_budget rho P)
  have hbox := localizedCoulombBox_eq_normalizedRaw hf (1 / (denominator rho P : ℚ) : ℝ)
    (radius rho P : ℝ) ((d : ℝ) • planarAxis 0)
  have ht := truncation_error rho P hrho d
  rw [hbox, abs_sub_comm] at ht
  have hinner := (abs_add_le ((α' - α) * q) (α * (q - I))).trans (add_le_add hfirst hsecond)
  rw [← heq] at hinner
  have hsum := (abs_sub_le (α' * q) (α * I)
    (localizedCoulombProfile (GaussianFrequency.frequency rho) (d : ℝ))).trans
      (add_le_add hinner ht)
  have hfinal : |α' * q - localizedCoulombProfile (GaussianFrequency.frequency rho) (d : ℝ)| ≤
      ((P : ℝ) + 1)⁻¹ := by
    apply hsum.trans
    rw [mul_inv]
    norm_num
    nlinarith [inv_pos.mpr (show (0 : ℝ) < P + 1 by positivity)]
  simpa only [approximate, Rat.cast_mul, α', q] using hfinal

end ContinuumCoulomb.CoulombEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombTargetLipschitz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quantitative modulus for the actual calibrated hopping residual.
The Coulomb gap keeps the square root away from zero, so ordinary dyadic
bisection needs no lower derivative bound. -/

noncomputable section
namespace ContinuumCoulomb

theorem localizedCoulombProfile_abs_sub {freq : ℝ} (hfreq : 0 < freq) (d e : ℝ) :
    |localizedCoulombProfile freq d-localizedCoulombProfile freq e| ≤
      localizedCoulombLipschitzConstant freq*|d-e| := by
  have h := localizedCoulombProfileAt_norm_sub hfreq (d • planarAxis 0) (e • planarAxis 0)
  rw [← sub_smul, norm_smul, planarAxis_zero_norm, mul_one] at h
  simpa only [localizedCoulombProfile, Real.norm_eq_abs] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombPairEvaluation
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual direct Coulomb coefficients at arbitrary rational planar sites.
The distance is computed by the certified dyadic square-root program. -/

noncomputable section
namespace ContinuumCoulomb.CoulombPairEvaluation

theorem lipschitzGuard_positive (rho : ℕ) : 0 < lipschitzGuard rho := by
  unfold lipschitzGuard
  omega

theorem lipschitzGuard_bound (rho : ℕ) :
    localizedCoulombLipschitzConstant (GaussianFrequency.frequency rho) ≤ (lipschitzGuard rho:ℝ) := by
  have h := Nat.le_ceil (localizedCoulombLipschitzConstant (GaussianFrequency.frequency rho))
  unfold lipschitzGuard
  push_cast
  linarith

theorem squaredDistance_cast (a b : ℚ×ℚ) :
    (squaredDistance a b:ℝ) =
      ‖PlanarForcingProgram.position a-PlanarForcingProgram.position b‖^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [squaredDistance,PlanarForcingProgram.position,PiLp.sub_apply,
    Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
    Real.norm_eq_abs,sq_abs,Rat.cast_add,Rat.cast_pow,Rat.cast_sub]

private theorem nat_pow_bound (n : ℕ) : n+1 ≤ 2^n := by
  induction n with
  | zero => norm_num
  | succ n ih => rw [pow_succ]; omega

theorem distance_error (rho P : ℕ) (a b : ℚ×ℚ) :
    |(distance rho P a b:ℝ)-‖PlanarForcingProgram.position a-PlanarForcingProgram.position b‖| ≤
      ((rootPrecision rho P:ℝ)+1)⁻¹ := by
  have h := RationalSquareRoot.value_error (rootPrecision rho P)
    (show (0:ℚ) ≤ squaredDistance a b from add_nonneg (sq_nonneg _) (sq_nonneg _))
  rw [squaredDistance_cast,Real.sqrt_sq (norm_nonneg _)] at h
  have hb : (2:ℝ)⁻¹^(rootPrecision rho P) ≤ ((rootPrecision rho P:ℝ)+1)⁻¹ := by
    rw [inv_pow]
    apply inv_anti₀ (by positivity)
    exact_mod_cast nat_pow_bound (rootPrecision rho P)
  exact h.trans hb

theorem approximation_error (rho P : ℕ) (hrho : 0 < rho) (a b : ℚ×ℚ) :
    |(approximate rho P a b:ℝ)-localizedCoulombCoeff (GaussianFrequency.frequency rho)
      (PlanarForcingProgram.position a) (PlanarForcingProgram.position b)| ≤ ((P:ℝ)+1)⁻¹ := by
  have hf : 0 < GaussianFrequency.frequency rho := by
    apply Real.sqrt_pos.mpr
    change 0 < 4*Real.pi*(rho:ℝ)
    positivity
  have he := CoulombEvaluation.approximation_error rho (precision P) hrho (distance rho P a b)
  have hd := localizedCoulombProfile_abs_sub hf (distance rho P a b)
    ‖PlanarForcingProgram.position a-PlanarForcingProgram.position b‖
  have hp : (0:ℝ) < (P:ℝ)+1 := by positivity
  have hC : (1:ℝ) ≤ lipschitzGuard rho := by exact_mod_cast lipschitzGuard_positive rho
  have hCp : (0:ℝ) < lipschitzGuard rho := by linarith
  have hmove : localizedCoulombLipschitzConstant (GaussianFrequency.frequency rho) *
      |(distance rho P a b:ℝ)-‖PlanarForcingProgram.position a-PlanarForcingProgram.position b‖| ≤
        (4*((P:ℝ)+1))⁻¹ := by
    apply (mul_le_mul (lipschitzGuard_bound rho) (distance_error rho P a b)
      (abs_nonneg _) hCp.le).trans
    simp only [rootPrecision,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one]
    apply (mul_inv_le_iff₀ (by positivity)).mpr
    rw [show (4*((P:ℝ)+1))⁻¹*(4*(lipschitzGuard rho:ℝ)*((P:ℝ)+1)+1) =
      (4*(lipschitzGuard rho:ℝ)*((P:ℝ)+1)+1)/(4*((P:ℝ)+1)) by ring]
    exact (le_div_iff₀ (by positivity)).mpr (by nlinarith)
  have heBound : ((precision P:ℝ)+1)⁻¹ ≤ (2*((P:ℝ)+1))⁻¹ := by
    apply inv_anti₀ (by positivity)
    simp only [precision,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one]
    linarith
  rw [localizedCoulombCoeff_distance]
  have htriangle := abs_sub_le (approximate rho P a b:ℝ)
    (localizedCoulombProfile (GaussianFrequency.frequency rho) (distance rho P a b))
    (localizedCoulombProfile (GaussianFrequency.frequency rho)
      ‖PlanarForcingProgram.position a-PlanarForcingProgram.position b‖)
  apply htriangle.trans
  have hsum := add_le_add (he.trans heBound) (hd.trans hmove)
  apply hsum.trans
  rw [mul_inv,mul_inv]
  norm_num
  nlinarith [inv_pos.mpr hp]

end ContinuumCoulomb.CoulombPairEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_HoppingQuadrature
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal compact contact quadrature, using the already certified
resolvent program at each translated rational point. -/

namespace ContinuumCoulomb.HoppingQuadrature
open ExactQuantumFactoring.BitStackProgram

theorem sample_error (e : Settings) (a b : ℚ)
    (hR : ‖PlanarForcingProgram.position (a - e.2, b)‖ ≤ (e.1.1 : ℝ)) :
    |(sample e a b : ℝ) -
      planarHoppingIntegrand (e.2 : ℝ) (PlanarForcingProgram.position (a, b))| ≤
        ((e.1.2 : ℝ) + 1)⁻¹ := by
  rw [sample, Rat.cast_mul, PlanarForcingProgram.value_cast, planarHoppingIntegrand,
    ← rationalPosition_shift_first, ← mul_sub, abs_mul,
    abs_of_nonneg (planarForcing_nonnegative _)]
  exact (mul_le_mul_of_nonneg_left
    (ResolventSchedule.approximation_error (e.1, (a - e.2, b)) hR)
    (planarForcing_nonnegative _)).trans
      (mul_le_of_le_one_left (by positivity) (planarForcing_le_one _))

theorem error (x : Input) (hh : 0 ≤ (x.2.2.2 : ℝ))
    (hR : ∀ i < x.1, ∀ j < x.1,
      ‖PlanarForcingProgram.position
        (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 i - x.2.1.2,
         RationalQuadratureProgram.node x.2.2.1 x.2.2.2 j)‖ ≤ (x.2.1.1.1 : ℝ)) :
    |(value x : ℝ) -
      ∫ a in (x.2.2.1 : ℝ)..(RationalQuadratureProgram.node x.2.2.1 x.2.2.2 x.1 : ℝ),
        ∫ b in (x.2.2.1 : ℝ)..(RationalQuadratureProgram.node x.2.2.1 x.2.2.2 x.1 : ℝ),
          planarHoppingIntegrand (x.2.1.2 : ℝ) (planarPairEquiv.symm (a, b))| ≤
      ((x.1 : ℝ) * (x.2.2.2 : ℝ)) ^ 2 *
        (128 * (x.2.2.2 : ℝ) + ((x.2.1.1.2 : ℝ) + 1)⁻¹) := by
  let f := fun a b => planarHoppingIntegrand (x.2.1.2 : ℝ) (planarPairEquiv.symm (a, b))
  let v := fun i j => (sample x.2.1
    (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 i)
    (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 j) : ℝ)
  have hx : ∀ a a' b, |f a b - f a' b| ≤ 64 * |a - a'| := by
    intro a a' b
    simpa only [f, planarPair_distance_first] using
      planarHoppingIntegrand_norm_sub_explicit (x.2.1.2 : ℝ)
        (planarPairEquiv.symm (a, b)) (planarPairEquiv.symm (a', b))
  have hy : ∀ a b b', |f a b - f a b'| ≤ 64 * |b - b'| := by
    intro a b b'
    simpa only [f, planarPair_distance_second] using
      planarHoppingIntegrand_norm_sub_explicit (x.2.1.2 : ℝ)
        (planarPairEquiv.symm (a, b)) (planarPairEquiv.symm (a, b'))
  have hs : ∀ i < x.1, ∀ j < x.1,
      |v i j - f (UniformQuadrature.node (x.2.2.1 : ℝ) (x.2.2.2 : ℝ) i)
        (UniformQuadrature.node (x.2.2.1 : ℝ) (x.2.2.2 : ℝ) j)| ≤
        ((x.2.1.1.2 : ℝ) + 1)⁻¹ := by
    intro i hi j hj
    have h := sample_error x.2.1 _ _ (hR i hi j hj)
    simpa only [v, f, rationalPosition_eq_pair, RationalQuadratureProgram.node_cast] using h
  have h := UniformQuadrature.rectangle_error f v _ _ x.1 _ _ x.1 hh hh
    (by norm_num : (0 : ℝ) ≤ 64) (by norm_num : (0 : ℝ) ≤ 64)
    (fun a _ a' _ b _ => hx a a' b) (fun a _ b _ b' _ => hy a b b') hs
  rw [value, RationalRectangleProgram.value_cast]
  simp only [RationalQuadratureProgram.node_cast]
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

end ContinuumCoulomb.HoppingQuadrature

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_HoppingSchedule
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit polynomial mesh and inner precision for the actual compact
hopping numerator. The displacement is an input rational, not an oracle. -/

noncomputable section
namespace ContinuumCoulomb.HoppingSchedule

theorem mesh_positive (P : ℕ) : 0 < mesh P := by unfold mesh; positivity

theorem argument_step_nonnegative (x : Input) : 0 ≤ ((argument x).2.2.2 : ℝ) := by
  change 0 ≤ ((2 / (mesh x.1.2 : ℚ) : ℚ) : ℝ)
  positivity

theorem argument_endpoint (x : Input) :
    RationalQuadratureProgram.node (argument x).2.2.1 (argument x).2.2.2
      (argument x).1 = 1 := by
  have hN : (mesh x.1.2 : ℚ) ≠ 0 := by exact_mod_cast (mesh_positive x.1.2).ne'
  change -(1 : ℚ) + (mesh x.1.2 : ℚ) * (2 / (mesh x.1.2 : ℚ)) = 1
  field_simp
  ring

theorem argument_node_mem (x : Input) (i : ℕ) (hi : i ≤ (argument x).1) :
    (RationalQuadratureProgram.node (argument x).2.2.1 (argument x).2.2.2 i : ℝ) ∈
      Set.Icc (-1 : ℝ) 1 := by
  have h := UniformQuadrature.node_mem (a := ((argument x).2.2.1 : ℝ))
    (argument_step_nonnegative x) hi
  rw [← RationalQuadratureProgram.node_cast, ← RationalQuadratureProgram.node_cast,
    argument_endpoint x] at h
  simpa only [argument, Rat.cast_neg, Rat.cast_one] using h

theorem argument_nodes_norm (x : Input) (hd : |(x.2 : ℝ)| ≤ (x.1.1 : ℝ))
    (i j : ℕ) (hi : i < (argument x).1) (hj : j < (argument x).1) :
    ‖PlanarForcingProgram.position
      (RationalQuadratureProgram.node (argument x).2.2.1 (argument x).2.2.2 i -
          (argument x).2.1.2,
       RationalQuadratureProgram.node (argument x).2.2.1 (argument x).2.2.2 j)‖ ≤
      ((argument x).2.1.1.1 : ℝ) := by
  have h := rationalShift_norm_bound x.2 _ _ hd
    (argument_node_mem x i hi.le) (argument_node_mem x j hj.le)
  simpa only [argument, Nat.cast_add, Nat.cast_ofNat] using h

theorem numerical_budget {S : ℝ} (hS : 0 < S) :
    4 * (128 * (2 / (4096 * S)) + (16 * S + 1)⁻¹) ≤ S⁻¹ := by
  have hm : 4 * (128 * (2 / (4096 * S))) = (4 * S)⁻¹ := by
    field_simp [hS.ne']
    ring
  have ha : 4 * (16 * S + 1)⁻¹ ≤ (4 * S)⁻¹ := by
    calc
      _ ≤ 4 * (16 * S)⁻¹ := mul_le_mul_of_nonneg_left
        (inv_anti₀ (by positivity) (by linarith)) (by norm_num)
      _ = _ := by field_simp [hS.ne']; ring
  rw [mul_add, hm]
  have he : 2 * (4 * S)⁻¹ ≤ S⁻¹ := by
    rw [mul_inv]
    norm_num
    nlinarith [inv_pos.mpr hS]
  linarith

theorem approximation_error (x : Input) (hd : |(x.2 : ℝ)| ≤ (x.1.1 : ℝ)) :
    |(approximate x : ℝ) - planarHoppingNumerator (x.2 : ℝ)| ≤ ((x.1.2 : ℝ) + 1)⁻¹ := by
  have hquad := HoppingQuadrature.error (argument x) (argument_step_nonnegative x)
    (fun i hi j hj => argument_nodes_norm x hd i j hi hj)
  rw [argument_endpoint x] at hquad
  have hlen : (mesh x.1.2 : ℝ) * (2 / (mesh x.1.2 : ℝ)) = 2 := by
    have hn : (mesh x.1.2 : ℝ) ≠ 0 := by exact_mod_cast (mesh_positive x.1.2).ne'
    field_simp
  have hquad' : |(approximate x : ℝ) - planarHoppingNumerator (x.2 : ℝ)| ≤
      4 * (128 * (2 / (mesh x.1.2 : ℝ)) + ((accuracy x.1.2 : ℝ) + 1)⁻¹) := by
    rw [planarHoppingNumerator_box]
    simpa only [approximate, argument, Rat.cast_neg, Rat.cast_one, Rat.cast_div,
      Rat.cast_ofNat, Rat.cast_natCast, hlen, show (2 : ℝ) ^ 2 = 4 by norm_num]
      using hquad
  apply hquad'.trans
  convert numerical_budget (S := (x.1.2 : ℝ) + 1) (by positivity) using 1
  all_goals try with_reducible_and_instances rfl
  simp only [mesh, accuracy, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]

end ContinuumCoulomb.HoppingSchedule

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_ComputableHopping
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual normalized hopping coefficient has a polynomial TM2
approximation. The sole fixed guard is chosen from the already proved
positive normalization integral; it is independent of every input. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb.ComputableHopping
open ExactQuantumFactoring.BitStackProgram

theorem precision_cast (P : ℕ) :
    (precision P : ℝ) = 16 * (contactNormalizationGuard : ℝ) ^ 2 * ((P : ℝ) + 1) := by
  simp only [precision, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_add, Nat.cast_one]

theorem precision_budget (P : ℕ) :
    (contactNormalizationGuard : ℝ) * ((precision P : ℝ) + 1)⁻¹ ≤ 1 ∧
    3 * (contactNormalizationGuard : ℝ) ^ 2 * ((precision P : ℝ) + 1)⁻¹ ≤
      ((P : ℝ) + 1)⁻¹ := by
  let C := (contactNormalizationGuard : ℝ)
  let S := (P : ℝ) + 1
  have hC : 1 ≤ C := by
    dsimp only [C]
    have hc : (1 : ℕ) ≤ contactNormalizationGuard := contactNormalizationGuard_positive
    exact_mod_cast hc
  have hS : 1 ≤ S := by
    dsimp only [S]
    linarith [show (0 : ℝ) ≤ (P : ℝ) from Nat.cast_nonneg _]
  have hC0 : 0 < C := by linarith
  have hS0 : 0 < S := by linarith
  have hC2 : C ≤ C ^ 2 := by nlinarith
  have hCs : C ^ 2 ≤ C ^ 2 * S := by nlinarith [sq_nonneg C]
  rw [precision_cast]
  change C * (16 * C ^ 2 * S + 1)⁻¹ ≤ 1 ∧
    3 * C ^ 2 * (16 * C ^ 2 * S + 1)⁻¹ ≤ S⁻¹
  constructor
  · exact (mul_inv_le_iff₀ (by positivity)).mpr (by nlinarith)
  · apply (mul_inv_le_iff₀ (by positivity)).mpr
    rw [show S⁻¹ * (16 * C ^ 2 * S + 1) = (16 * C ^ 2 * S + 1) / S by ring]
    exact (le_div_iff₀ hS0).mpr (by nlinarith)

theorem approximation_error (x : Input) (hd : |(x.2 : ℝ)| ≤ (x.1.1 : ℝ)) :
    |(approximate x : ℝ) - planarHopping (x.2 : ℝ)| ≤ ((x.1.2 : ℝ) + 1)⁻¹ := by
  let A := ∫ r, planarResolventMode r ^ 2
  let ε := ((precision x.1.2 : ℝ) + 1)⁻¹
  have ha : 0 < A := planarResolventMode_square_integral_positive
  have hC : (1 : ℝ) ≤ contactNormalizationGuard := by
    have hc : (1 : ℕ) ≤ contactNormalizationGuard := contactNormalizationGuard_positive
    exact_mod_cast hc
  have hn := NormalizationSchedule.approximation_error (precision x.1.2)
  have hb := HoppingSchedule.approximation_error (argument x) hd
  have hq := contact_quotient_error hC ha contactNormalizationGuard_bound
    (show 0 ≤ ε by dsimp [ε]; positivity) (precision_budget x.1.2).1
    (planarHoppingNumerator_abs_le_four (x.2 : ℝ)) hn hb
  have hq' : |(approximate x : ℝ) - planarHopping (x.2 : ℝ)| ≤
      3 * (contactNormalizationGuard : ℝ) ^ 2 * ε := by
    simpa only [approximate, argument, planarHopping_eq_numerator,
      Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, A, ε] using hq
  exact hq'.trans (precision_budget x.1.2).2

end ContinuumCoulomb.ComputableHopping

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CountertermEvaluation
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual well-depth counterterms are finite sums of certified Coulomb
entries divided by the fixed onsite hopping. A fixed positive denominator
guard makes every rational evaluation well defined. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb.CountertermEvaluation

theorem guard_bounds (rho : ℕ) : 1 ≤ guard rho ∧
    2 ≤ (guard rho:ℝ)*planarHopping 0 ∧
    localizedPotentialBound (GaussianFrequency.frequency rho) ≤ guard rho ∧
    planarWellDerivativeConstant ≤ guard rho := Classical.choose_spec (guard_exists rho)

theorem entry_error (rho p : ℕ) (hrho : 0 < rho) (a b : ℚ×ℚ) :
    |(entry rho p a b:ℝ)-
      localizedCoulombCoeff (GaussianFrequency.frequency rho)
        (PlanarForcingProgram.position a) (PlanarForcingProgram.position b)/planarHopping 0| ≤
      2*(guard rho:ℝ)^3*((p:ℝ)+1)⁻¹ := by
  let C : ℝ := guard rho
  let T : ℝ := planarHopping 0
  let A : ℝ := localizedCoulombCoeff (GaussianFrequency.frequency rho)
    (PlanarForcingProgram.position a) (PlanarForcingProgram.position b)
  let ε : ℝ := ((p:ℝ)+1)⁻¹
  have hC : 1 ≤ C := by dsimp [C]; exact_mod_cast (guard_bounds rho).1
  have hCp : 0 < C := by linarith
  have hT : 0 < T := planarHopping_positive 0
  have hCT : 1 ≤ C*T := by have h := (guard_bounds rho).2.1; dsimp [C,T]; linarith
  have hf : 0 < GaussianFrequency.frequency rho := by
    apply Real.sqrt_pos.mpr
    change 0 < 4*Real.pi*(rho:ℝ)
    positivity
  have hA : |A| ≤ C := by
    rw [abs_of_nonneg (localizedCoulombCoeff_nonnegative _ _ _)]
    exact (localizedCoulombCoeff_le hf _ _).trans (guard_bounds rho).2.2.1
  have he := CoulombPairEvaluation.approximation_error rho p hrho a b
  have ht : |(ComputableHopping.approximate ((1,p),0):ℝ)-T| ≤ ε := by
    simpa only [Prod.fst,Prod.snd,Rat.cast_zero,T,ε] using
      ComputableHopping.approximation_error ((1,p),0) (by norm_num)
  have hden : |(denominator rho p:ℝ)-C*T| ≤ C*ε := by
    have hm : |C*(ComputableHopping.approximate ((1,p),0):ℝ)-C*T| ≤ C*ε := by
      rw [← mul_sub,abs_mul,abs_of_pos hCp]
      exact mul_le_mul_of_nonneg_left ht hCp.le
    simpa only [denominator,Rat.cast_max,Rat.cast_one,Rat.cast_mul,Rat.cast_natCast,C,T]
      using MoserVelocityNumerics.clamp_error hCT hm
  have hden1 : (1:ℝ) ≤ denominator rho p := by
    exact_mod_cast le_max_left (1:ℚ) ((guard rho:ℚ)*ComputableHopping.approximate ((1,p),0))
  have hnum : |-(C*(CoulombPairEvaluation.approximate rho p a b:ℝ))- -(C*A)| ≤ C*ε := by
    rw [show -(C*(CoulombPairEvaluation.approximate rho p a b:ℝ))- -(C*A) =
      -(C*((CoulombPairEvaluation.approximate rho p a b:ℝ)-A)) by ring,
      abs_neg,abs_mul,abs_of_pos hCp]
    exact mul_le_mul_of_nonneg_left he hCp.le
  have hAb : |-(C*A)| ≤ C^2 := by
    rw [abs_neg,abs_mul,abs_of_pos hCp]
    exact (mul_le_mul_of_nonneg_left hA hCp.le).trans_eq (by ring)
  have h := MoserVelocityNumerics.quotient_error hCT hden1 hAb hnum hden
  have hid : C*A/(C*T) = A/T := by field_simp
  simp only [neg_neg,hid] at h
  have hsmall : C*ε+C^2*(C*ε) ≤ 2*C^3*ε := by
    have heps : 0 ≤ ε := by dsimp [ε]; positivity
    have hc3 : C ≤ C^3 := le_self_pow₀ hC (by decide)
    have hm := mul_le_mul_of_nonneg_right hc3 heps
    nlinarith only [hm]
  exact (show |(entry rho p a b:ℝ)-A/T| ≤ C*ε+C^2*(C*ε) by
    simpa only [entry,Rat.cast_div,Rat.cast_mul,Rat.cast_natCast,C] using h).trans hsmall

theorem squaredDistance_eq_zero (a b : ℚ×ℚ) :
    CoulombPairEvaluation.squaredDistance a b = 0 ↔ a=b := by
  constructor
  · intro h
    unfold CoulombPairEvaluation.squaredDistance at h
    have h1 : (a.1-b.1)^2 = 0 := by nlinarith [sq_nonneg (a.2-b.2)]
    have h2 : (a.2-b.2)^2 = 0 := by nlinarith [sq_nonneg (a.1-b.1)]
    apply Prod.ext <;> nlinarith
  · rintro rfl
    simp [CoulombPairEvaluation.squaredDistance]

theorem row_ofFn (rho p : ℕ) {m : ℕ} (u : Fin m → ℚ×ℚ) (i : Fin m) :
    row rho p (u i) (List.ofFn u) = ∑ j, offsite rho p (u i) (u j) := by
  simp only [row,List.map_ofFn,List.sum_ofFn,Function.comp_apply]

theorem row_error (rho p : ℕ) (hrho : 0 < rho) {m : ℕ}
    (u : Fin m → ℚ×ℚ) (hu : Function.Injective u) (i : Fin m) :
    |(row rho p (u i) (List.ofFn u):ℝ)-
      localizedCounterterm (GaussianFrequency.frequency rho)
        (fun j => PlanarForcingProgram.position (u j)) i| ≤
      (m:ℝ)*2*(guard rho:ℝ)^3*((p:ℝ)+1)⁻¹ := by
  rw [row_ofFn]
  simp only [Rat.cast_sum,localizedCounterterm,localizedOffsiteSum,Finset.sum_div]
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _j : Fin m, 2*(guard rho:ℝ)^3*((p:ℝ)+1)⁻¹ := by
      apply Finset.sum_le_sum
      intro j _
      by_cases h : i=j
      · subst j
        simp only [offsite,squaredDistance_eq_zero,ite_true, if_true,Rat.cast_zero,zero_div,sub_self,abs_zero]
        positivity
      · have huij : u i ≠ u j := fun hij => h (hu hij)
        simpa only [offsite,squaredDistance_eq_zero,ite_eq_right huij,ite_eq_right h]
          using entry_error rho p hrho (u i) (u j)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

end ContinuumCoulomb.CountertermEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarWellNumerics
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed guard turns the actual heat-resolvent evaluator into an
evaluator of the compact manufactured planar well. The guard is chosen
once on the unit disk; no instance-dependent real parameter is encoded. -/

noncomputable section
namespace ContinuumCoulomb.PlanarWellNumerics

theorem guard_positive : 0 < guard := (Classical.choose_spec guard_exists).1

theorem guard_bound (r : PlanarPosition) (hr : ‖r‖ ≤ 1) :
    2 ≤ (guard:ℝ)*planarResolventMode r := (Classical.choose_spec guard_exists).2 r hr

theorem outside_norm {q : ℚ×ℚ} (hq : outside q) :
    1 ≤ ‖PlanarForcingProgram.position q‖ := by
  have hqR : (1:ℝ) ≤ (q.1:ℝ)^2+(q.2:ℝ)^2 := by exact_mod_cast hq
  rw [← PlanarForcingProgram.position_norm_sq] at hqR
  nlinarith [norm_nonneg (PlanarForcingProgram.position q)]

theorem inside_norm {q : ℚ×ℚ} (hq : ¬ outside q) :
    ‖PlanarForcingProgram.position q‖ ≤ 1 := by
  have hqR : (q.1:ℝ)^2+(q.2:ℝ)^2 < 1 := by exact_mod_cast lt_of_not_ge hq
  rw [← PlanarForcingProgram.position_norm_sq] at hqR
  nlinarith [norm_nonneg (PlanarForcingProgram.position q)]

theorem approximation_error (p : ℕ) (q : ℚ×ℚ) :
    |(approximate p q:ℝ)-manufacturedPlanarWell (PlanarForcingProgram.position q)| ≤
      ((p:ℝ)+1)⁻¹ := by
  by_cases hq : outside q
  · rw [approximate,ite_eq_left hq,manufacturedPlanarWell_zero_of_norm_ge_one (outside_norm hq)]
    simp only [Rat.cast_zero,sub_self,abs_zero]
    positivity
  · have hr := inside_norm hq
    let r := PlanarForcingProgram.position q
    let ε : ℝ := ((precision p:ℝ)+1)⁻¹
    have hC : (1:ℝ) ≤ guard := by exact_mod_cast guard_positive
    have hCp : (0:ℝ) < guard := by linarith
    have hp : (0:ℝ) < (p:ℝ)+1 := by positivity
    have hprec : (precision p:ℝ) = 4*(guard:ℝ)^2*((p:ℝ)+1) := by
      simp only [precision,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one]
    have hsmall : (guard:ℝ)*ε ≤ 1 := by
      dsimp [ε]
      apply (mul_inv_le_iff₀ (by positivity)).mpr
      rw [hprec]
      nlinarith [sq_nonneg ((guard:ℝ)-1),Nat.cast_nonneg (α := ℝ) p]
    have heval := ResolventSchedule.approximation_error ((2,precision p),q)
      (by exact hr.trans (by norm_num))
    have hb : |-planarForcing r| ≤ 4 := by
      rw [abs_neg,abs_of_nonneg (planarForcing_nonnegative r)]
      linarith [planarForcing_le_one r]
    have h := contact_quotient_error hC (planarResolventMode_positive r)
      (guard_bound r hr) (by dsimp [ε]; positivity) hsmall hb heval
      (show |-planarForcing r - -planarForcing r| ≤ ε by simp only [sub_self,abs_zero]; dsimp [ε]; positivity)
    have hlast : 3*(guard:ℝ)^2*ε ≤ ((p:ℝ)+1)⁻¹ := by
      dsimp [ε]
      rw [hprec]
      apply (mul_le_mul_iff_left₀ hp).mp
      field_simp
      nlinarith [sq_nonneg (guard:ℝ)]
    apply (le_trans ?_ hlast)
    simpa only [approximate,ite_eq_right hq,manufacturedPlanarWell,PlanarForcingProgram.value_cast,
      Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_neg,r] using h

end ContinuumCoulomb.PlanarWellNumerics

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RationalSmoothTransition
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational approximation of the explicit smooth transition. Exponents
near the flat junction are truncated before Taylor evaluation, keeping
both the magnitude parameter and the error polynomial in the precision. -/

namespace ContinuumCoulomb.RationalSmoothTransition

theorem clip_bounds (q : ℚ) : 0 ≤ clip q ∧ clip q ≤ 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem clip_error (q : ℚ) {a ε : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hq : |(q:ℝ)-a| ≤ ε) : |(clip q:ℝ)-a| ≤ ε := by
  have he := abs_le.mp hq
  by_cases hq0 : q ≤ 0
  · have hqR : (q:ℝ) ≤ 0 := by exact_mod_cast hq0
    simp only [clip, min_eq_right (hq0.trans (by norm_num : (0:ℚ) ≤ 1)),
      max_eq_left hq0, Rat.cast_zero, zero_sub, abs_neg, abs_of_nonneg ha0]
    linarith
  · by_cases hq1 : 1 ≤ q
    · have hqR : (1:ℝ) ≤ q := by exact_mod_cast hq1
      simp only [clip, min_eq_left hq1, max_eq_right (by norm_num : (0:ℚ) ≤ 1),
        Rat.cast_one, abs_of_nonneg (sub_nonneg.mpr ha1)]
      linarith
    · simpa only [clip, min_eq_right (le_of_not_ge hq1),
        max_eq_right (le_of_not_ge hq0)] using hq

private theorem two_pow_bound (p : ℕ) : p+1 ≤ 2^(p+1) := by
  induction p with
  | zero => norm_num
  | succ p ih =>
    rw [pow_succ]
    omega

theorem flat_error (p : ℕ) (q : ℚ) :
    |(flat p q:ℝ)-expNegInvGlue (q:ℝ)| ≤ ((p:ℝ)+1)⁻¹ := by
  have hp : (0:ℝ) < (p:ℝ)+1 := by positivity
  have hpQ : (0:ℚ) < (p+1:ℚ) := by positivity
  have hg0 : 0 ≤ expNegInvGlue (q:ℝ) := expNegInvGlue.nonneg _
  have hg1 : expNegInvGlue (q:ℝ) ≤ 1 := by
    by_cases hq : (q:ℝ) ≤ 0
    · rw [expNegInvGlue.zero_of_nonpos hq]; norm_num
    · rw [expNegInvGlue, ite_eq_right hq]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (inv_nonneg.mpr (le_of_not_ge hq)))
  unfold flat
  split_ifs with hq
  · have hqR : ((p:ℝ)+1)⁻¹ < (q:ℝ) := by
      have hh := (Rat.cast_lt (K := ℝ)).mpr hq
      simpa only [Rat.cast_inv, Rat.cast_add, Rat.cast_natCast, Rat.cast_one] using hh
    have hqp : (0:ℝ) < (q:ℝ) := (inv_pos.mpr hp).trans hqR
    have hinv : (q:ℝ)⁻¹ ≤ (p:ℝ)+1 := by
      exact (inv_le_comm₀ hqp hp).mpr hqR.le
    have he := RationalExponential.error (p+1) (p+1) (-q⁻¹) (by
      push_cast
      rw [abs_neg, abs_of_pos (inv_pos.mpr hqp)]
      simpa only [Nat.cast_add, Nat.cast_one] using hinv)
    have hprec : (2^(p+1):ℝ)⁻¹ ≤ ((p:ℝ)+1)⁻¹ := by
      apply (inv_le_inv₀ (by positivity) hp).mpr
      exact_mod_cast two_pow_bound p
    have he' : |(RationalExponential.approximate (p+1) (p+1) (-q⁻¹):ℝ) -
        expNegInvGlue (q:ℝ)| ≤ ((p:ℝ)+1)⁻¹ := by
      rw [expNegInvGlue, ite_eq_right (not_le.mpr hqp)]
      simpa only [Rat.cast_neg, Rat.cast_inv, abs_sub_comm] using he.trans hprec
    exact clip_error _ hg0 hg1 he'
  · have hqR : (q:ℝ) ≤ ((p:ℝ)+1)⁻¹ := by
      have hh := (Rat.cast_le (K := ℝ)).mpr (le_of_not_gt hq)
      simpa only [Rat.cast_inv, Rat.cast_add, Rat.cast_natCast, Rat.cast_one] using hh
    by_cases hqp : (q:ℝ) ≤ 0
    · rw [expNegInvGlue.zero_of_nonpos hqp]
      simpa using (inv_nonneg.mpr hp.le)
    · have hqp' : (0:ℝ) < (q:ℝ) := lt_of_not_ge hqp
      have hexp : (q:ℝ)⁻¹ ≤ Real.exp (q:ℝ)⁻¹ := by
        linarith [Real.add_one_le_exp ((q:ℝ)⁻¹)]
      have hinv : (Real.exp (q:ℝ)⁻¹)⁻¹ ≤ (q:ℝ) := by
        simpa only [inv_inv] using
          (inv_le_inv₀ (Real.exp_pos _) (inv_pos.mpr hqp')).mpr hexp
      rw [Rat.cast_zero, zero_sub, abs_neg, abs_of_nonneg hg0, expNegInvGlue, ite_eq_right hqp,
        Real.exp_neg]
      exact hinv.trans hqR

theorem transition_denominator_lower (x : ℝ) :
    (1/9:ℝ) ≤ expNegInvGlue x + expNegInvGlue (1-x) := by
  have he : Real.exp 2 ≤ 9 := by
    rw [show (2:ℝ) = 1+1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
  have hinv : (1/9:ℝ) ≤ expNegInvGlue (1/2) := by
    norm_num only [expNegInvGlue, show ¬ ((1/2:ℝ) ≤ 0) by norm_num, ite_false,
      one_div, inv_inv, inv_div, mul_one]
    rw [Real.exp_neg]
    exact (le_inv_comm₀ (by norm_num) (Real.exp_pos _)).mpr (by simpa using he)
  by_cases hx : (1/2:ℝ) ≤ x
  · exact hinv.trans ((expNegInvGlue.monotone hx).trans
      (le_add_of_nonneg_right (expNegInvGlue.nonneg _)))
  · have hy : (1/2:ℝ) ≤ 1-x := by linarith
    exact hinv.trans ((expNegInvGlue.monotone hy).trans
      (le_add_of_nonneg_left (expNegInvGlue.nonneg _)))

theorem quotient_error {a b a' b' ε : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 1/9 ≤ a+b)
    (hε : 0 ≤ ε) (hsmall : ε ≤ 1/1000)
    (hea : |a'-a| ≤ ε) (heb : |b'-b| ≤ ε) :
    |a'/(a'+b')-a/(a+b)| ≤ 342*ε := by
  have hden : |(a'+b')-(a+b)| ≤ 2*ε := by
    have h := (abs_add_le (a'-a) (b'-b)).trans (add_le_add hea heb)
    convert h using 1 <;> first | (with_reducible_and_instances rfl) | (ring_nf)
  have hd : 0 < a+b := by linarith
  have hd' : 1/18 ≤ a'+b' := by linarith [(abs_le.mp hden).1]
  have hd'p : 0 < a'+b' := by linarith
  have hi : (a+b)⁻¹ ≤ 9 := (inv_le_iff_one_le_mul₀ hd).mpr (by linarith)
  have hi' : (a'+b')⁻¹ ≤ 18 := (inv_le_iff_one_le_mul₀ hd'p).mpr (by linarith)
  have hnum : |a'/(a'+b')-a/(a+b)| ≤
      ε*(a'+b')⁻¹ + 2*ε*(a'+b')⁻¹*(a+b)⁻¹ := by
    have heq : a'/(a'+b')-a/(a+b) =
        (a'-a)*(a'+b')⁻¹ + a*((a+b)-(a'+b'))*(a'+b')⁻¹*(a+b)⁻¹ := by
      field_simp [hd.ne',hd'p.ne']
      ring
    rw [heq]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg ha,
      abs_of_pos (inv_pos.mpr hd), abs_of_pos (inv_pos.mpr hd'p),
      abs_sub_comm (a+b) (a'+b')]
    apply add_le_add
    · exact mul_le_mul_of_nonneg_right hea (inv_nonneg.mpr hd'p.le)
    · apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hd.le)
      apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hd'p.le)
      calc
        _ ≤ 1*(2*ε) := mul_le_mul ha1 hden (abs_nonneg _) (by norm_num)
        _ = 2*ε := one_mul _
  apply hnum.trans
  calc
    _ ≤ ε*18 + 2*ε*18*9 := by gcongr
    _ = 342*ε := by ring

theorem approximation_error (p : ℕ) (q : ℚ) :
    |(approximate p q:ℝ)-Real.smoothTransition (q:ℝ)| ≤ ((p:ℝ)+1)⁻¹ := by
  let ε : ℝ := ((precision p:ℝ)+1)⁻¹
  have hp : (0:ℝ) < (p:ℝ)+1 := by positivity
  have he : 0 ≤ ε := by dsimp [ε]; positivity
  have hesmall : ε ≤ 1/1000 := by
    dsimp [ε,precision]
    push_cast
    apply (inv_le_iff_one_le_mul₀ (by positivity)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) p]
  have ha1 : expNegInvGlue (q:ℝ) ≤ 1 := by
    by_cases hq : (q:ℝ) ≤ 0
    · rw [expNegInvGlue.zero_of_nonpos hq]; norm_num
    · rw [expNegInvGlue, ite_eq_right hq]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (inv_nonneg.mpr (le_of_not_ge hq)))
  have heb : |(flat (precision p) (1-q):ℝ)-expNegInvGlue (1-(q:ℝ))| ≤ ε := by
    simpa only [Rat.cast_sub, Rat.cast_one] using flat_error (precision p) (1-q)
  have h := quotient_error (expNegInvGlue.nonneg _) ha1
    (transition_denominator_lower (q:ℝ)) he hesmall
    (flat_error (precision p) q) heb
  have hbound : 342*ε ≤ ((p:ℝ)+1)⁻¹ := by
    dsimp [ε,precision]
    push_cast
    apply (mul_le_mul_iff_left₀ hp).mp
    field_simp
    nlinarith [Nat.cast_nonneg (α := ℝ) p]
  apply (le_trans ?_ hbound)
  simpa only [approximate, Real.smoothTransition, Rat.cast_div, Rat.cast_add,
    Rat.cast_sub, Rat.cast_one] using h

end ContinuumCoulomb.RationalSmoothTransition

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_VerticalCutoffProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial-time approximation of the actual transverse cutoff in the
manufactured well field. The rational slab width and coordinate are arbitrary. -/

namespace ContinuumCoulomb.VerticalCutoffProgram
open ExactQuantumFactoring.BitStackProgram

theorem cutoff_error (p : ℕ) (q : ℚ) :
    |(SmoothTransitionProgram.cutoff p q:ℝ)-verticalCutoffBump (q:ℝ)| ≤
      ((p:ℝ)+1)⁻¹ := by
  simpa only [SmoothTransitionProgram.cutoff,SmoothTransitionProgram.cutoffArgument,
    verticalCutoffBump,Rat.cast_div,Rat.cast_sub,Rat.cast_pow,Rat.cast_ofNat]
    using RationalSmoothTransition.approximation_error p (SmoothTransitionProgram.cutoffArgument q)

theorem approximation_error (x : Input) :
    |(value x:ℝ)-slabWellCutoff (x.2.1:ℝ) (x.2.2:ℝ)| ≤ ((x.1:ℝ)+1)⁻¹ := by
  simpa only [value,argument,slabWellCutoff,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat]
    using cutoff_error x.1 (argument x)

end ContinuumCoulomb.VerticalCutoffProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedFieldEvaluation
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A rational scalar evaluator for the actual manufactured well field.
The well-depth factors are clipped to their proved interval [1,2]. This
stabilizes every encoded input and preserves the valid-instance estimate. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb.ManufacturedFieldEvaluation

theorem coefficient_bounds (rho p : ℕ) (scale : ℚ) (sites : List (ℚ×ℚ)) (a : ℚ×ℚ) :
    1 ≤ coefficient rho p scale sites a ∧ coefficient rho p scale sites a ≤ 2 := by
  have h := RationalSmoothTransition.clip_bounds (CountertermEvaluation.row rho p a sites/scale)
  unfold coefficient
  constructor <;> linarith

theorem translate_position (r a : ℚ×ℚ) :
    PlanarForcingProgram.position (translate r a) =
      PlanarForcingProgram.position r-PlanarForcingProgram.position a := by
  ext i
  fin_cases i <;> simp [translate,PlanarForcingProgram.position]

theorem coefficient_error (rho p : ℕ) (hrho : 0 < rho) {scale : ℚ}
    (hscale : (1:ℝ) ≤ scale) {m : ℕ} (u : Fin m → ℚ×ℚ) (hu : Function.Injective u)
    (i : Fin m)
    (hc : localizedCounterterm (GaussianFrequency.frequency rho)
      (fun j => PlanarForcingProgram.position (u j)) i ≤ scale) :
    |(coefficient rho p scale (List.ofFn u) (u i):ℝ)-
      (1+localizedCounterterm (GaussianFrequency.frequency rho)
        (fun j => PlanarForcingProgram.position (u j)) i/(scale:ℝ))| ≤
      (m:ℝ)*2*(CountertermEvaluation.guard rho:ℝ)^3*((p:ℝ)+1)⁻¹ := by
  let c := localizedCounterterm (GaussianFrequency.frequency rho)
    (fun j => PlanarForcingProgram.position (u j)) i
  let E := (m:ℝ)*2*(CountertermEvaluation.guard rho:ℝ)^3*((p:ℝ)+1)⁻¹
  have hs : (0:ℝ) < scale := by linarith
  have he : |((CountertermEvaluation.row rho p (u i) (List.ofFn u)/scale:ℚ):ℝ)-
      c/(scale:ℝ)| ≤ E := by
    rw [Rat.cast_div,← sub_div,abs_div,abs_of_pos hs]
    exact ((div_le_div_of_nonneg_right (CountertermEvaluation.row_error rho p hrho u hu i)
      hs.le).trans (div_le_self (by positivity) hscale))
  have hc0 : 0 ≤ c/(scale:ℝ) := div_nonneg (localizedCounterterm_nonnegative _ _ _) hs.le
  have hc1 : c/(scale:ℝ) ≤ 1 := (div_le_one hs).mpr hc
  simpa only [coefficient,Rat.cast_add,Rat.cast_one,add_sub_add_left_eq_sub]
    using RationalSmoothTransition.clip_error _ hc0 hc1 he

theorem well_abs_le_guard (rho : ℕ) (r : PlanarPosition) :
    |manufacturedPlanarWell r| ≤ (CountertermEvaluation.guard rho:ℝ) := by
  have h := planarWellDerivativeConstant_bound (k := 0) (by omega) r
  rw [norm_iteratedFDeriv_zero,Real.norm_eq_abs] at h
  exact h.trans (CountertermEvaluation.guard_bounds rho).2.2.2

private theorem product_error {a a' b b' A B ε η : ℝ}
    (ha : |a'| ≤ A) (hb : |b| ≤ B) (he : |a'-a| ≤ ε) (hf : |b'-b| ≤ η) :
    |a'*b'-a*b| ≤ A*η+ε*B := by
  have hA : 0 ≤ A := (abs_nonneg _).trans ha
  have he0 : 0 ≤ ε := (abs_nonneg _).trans he
  rw [show a'*b'-a*b = a'*(b'-b)+(a'-a)*b by ring]
  exact (abs_add_le _ _).trans (by
    rw [abs_mul,abs_mul]
    exact add_le_add (mul_le_mul ha hf (abs_nonneg _) hA)
      (mul_le_mul he hb (abs_nonneg _) he0))

theorem planar_error (rho p : ℕ) (hrho : 0 < rho) {scale : ℚ}
    (hscale : (1:ℝ) ≤ scale) {m : ℕ} (u : Fin m → ℚ×ℚ) (hu : Function.Injective u)
    (hc : ∀ i, localizedCounterterm (GaussianFrequency.frequency rho)
      (fun j => PlanarForcingProgram.position (u j)) i ≤ scale) (r : ℚ×ℚ) :
    |(planar rho p scale (List.ofFn u) r:ℝ)-
      countertermWellSum (GaussianFrequency.frequency rho) scale
        (fun i => PlanarForcingProgram.position (u i)) (PlanarForcingProgram.position r)| ≤
      ((m:ℝ)*2+(m:ℝ)^2*2*(CountertermEvaluation.guard rho:ℝ)^4)*((p:ℝ)+1)⁻¹ := by
  rw [planar,List.map_ofFn,List.sum_ofFn,Rat.cast_sum]
  unfold countertermWellSum
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hs : ∀ i : Fin m,
      |(coefficient rho p scale (List.ofFn u) (u i):ℝ) *
          (PlanarWellNumerics.approximate p (translate r (u i)):ℝ)-
        (1+localizedCounterterm (GaussianFrequency.frequency rho)
          (fun j => PlanarForcingProgram.position (u j)) i/(scale:ℝ))*
          manufacturedPlanarWell (PlanarForcingProgram.position r-PlanarForcingProgram.position (u i))| ≤
      2*((p:ℝ)+1)⁻¹+
        ((m:ℝ)*2*(CountertermEvaluation.guard rho:ℝ)^3*((p:ℝ)+1)⁻¹)*
          (CountertermEvaluation.guard rho:ℝ) := by
    intro i
    have hb := coefficient_bounds rho p scale (List.ofFn u) (u i)
    have hab : |(coefficient rho p scale (List.ofFn u) (u i):ℝ)| ≤ 2 := by
      have hl : (1:ℝ) ≤ coefficient rho p scale (List.ofFn u) (u i) := by exact_mod_cast hb.1
      have hh : (coefficient rho p scale (List.ofFn u) (u i):ℝ) ≤ 2 := by exact_mod_cast hb.2
      rw [abs_of_nonneg (by linarith)]
      exact hh
    have he := PlanarWellNumerics.approximation_error p (translate r (u i))
    rw [translate_position] at he
    exact product_error hab (well_abs_le_guard rho _) (coefficient_error rho p hrho hscale u hu i (hc i)) he
  calc
    _ ≤ ∑ _i : Fin m, (2*((p:ℝ)+1)⁻¹+
        ((m:ℝ)*2*(CountertermEvaluation.guard rho:ℝ)^3*((p:ℝ)+1)⁻¹)*
          (CountertermEvaluation.guard rho:ℝ)) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Function.comp_apply,Rat.cast_mul] using hs i
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring

theorem planar_exact_bound (rho : ℕ) {scale : ℚ} (hscale : (1:ℝ) ≤ scale)
    {m : ℕ} (u : Fin m → ℚ×ℚ)
    (hc : ∀ i, localizedCounterterm (GaussianFrequency.frequency rho)
      (fun j => PlanarForcingProgram.position (u j)) i ≤ scale) (r : PlanarPosition) :
    |countertermWellSum (GaussianFrequency.frequency rho) scale
      (fun i => PlanarForcingProgram.position (u i)) r| ≤
      2*(m:ℝ)*(CountertermEvaluation.guard rho:ℝ) := by
  have hs : (0:ℝ) < scale := by linarith
  unfold countertermWellSum
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _i : Fin m, 2*(CountertermEvaluation.guard rho:ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have hc0 := div_nonneg (localizedCounterterm_nonnegative
        (GaussianFrequency.frequency rho) (fun j => PlanarForcingProgram.position (u j)) i) hs.le
      have hc1 := (div_le_one hs).mpr (hc i)
      rw [abs_mul,abs_of_nonneg (by linarith : 0 ≤ 1+
        localizedCounterterm (GaussianFrequency.frequency rho)
          (fun j => PlanarForcingProgram.position (u j)) i/(scale:ℝ))]
      exact mul_le_mul (by linarith) (well_abs_le_guard rho _) (abs_nonneg _) (by norm_num)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring

theorem raw_error (rho p : ℕ) (hrho : 0 < rho) {scale : ℚ}
    (hscale : (1:ℝ) ≤ scale) (S : ℚ) {m : ℕ} (u : Fin m → ℚ×ℚ)
    (hu : Function.Injective u)
    (hc : ∀ i, localizedCounterterm (GaussianFrequency.frequency rho)
      (fun j => PlanarForcingProgram.position (u j)) i ≤ scale)
    (x : CappedKernelProgram.Triple) :
    |(rawValue rho p scale S (List.ofFn u) x:ℝ)-
      manufacturedWellField (GaussianFrequency.frequency rho) scale S
        (fun i => PlanarForcingProgram.position (u i)) (CappedKernelProgram.position x)| ≤
      (2*(m:ℝ)+2*(m:ℝ)*(CountertermEvaluation.guard rho:ℝ)+
        2*(m:ℝ)^2*(CountertermEvaluation.guard rho:ℝ)^4)*((p:ℝ)+1)⁻¹ := by
  have hcut := slabWellCutoff_bounds (S:ℝ) (x.2.2:ℝ)
  have hecut := RationalSmoothTransition.clip_error
    (VerticalCutoffProgram.value (p,(S,x.2.2))) hcut.1 hcut.2
    (VerticalCutoffProgram.approximation_error (p,(S,x.2.2)))
  have hcb := RationalSmoothTransition.clip_bounds (VerticalCutoffProgram.value (p,(S,x.2.2)))
  have hab : |(RationalSmoothTransition.clip (VerticalCutoffProgram.value (p,(S,x.2.2))):ℝ)| ≤ 1 := by
    have hl : (0:ℝ) ≤ RationalSmoothTransition.clip (VerticalCutoffProgram.value (p,(S,x.2.2))) :=
      by exact_mod_cast hcb.1
    have hh : (RationalSmoothTransition.clip (VerticalCutoffProgram.value (p,(S,x.2.2))):ℝ) ≤ 1 :=
      by exact_mod_cast hcb.2
    simpa only [abs_of_nonneg hl] using hh
  have he := product_error hab
    (planar_exact_bound rho hscale u hc (PlanarForcingProgram.position (x.1,x.2.1))) hecut
    (planar_error rho p hrho hscale u hu hc (x.1,x.2.1))
  calc
    _ ≤ 1*((m:ℝ)*2+(m:ℝ)^2*2*(CountertermEvaluation.guard rho:ℝ)^4)*((p:ℝ)+1)⁻¹+
        ((p:ℝ)+1)⁻¹*(2*(m:ℝ)*(CountertermEvaluation.guard rho:ℝ)) := by
      simpa only [rawValue,Rat.cast_mul,manufacturedWellField,RawDensitySample.position_split,
        Prod.fst,Prod.snd,one_mul] using he
    _ = _ := by ring

theorem precision_budget (rho m P : ℕ) :
    (2*(m:ℝ)+2*(m:ℝ)*(CountertermEvaluation.guard rho:ℝ)+
      2*(m:ℝ)^2*(CountertermEvaluation.guard rho:ℝ)^4)*
        ((precision rho m P:ℝ)+1)⁻¹ ≤ ((P:ℝ)+1)⁻¹ := by
  let C : ℝ := CountertermEvaluation.guard rho
  let M : ℝ := m
  have hC : 1 ≤ C := by dsimp [C]; exact_mod_cast (CountertermEvaluation.guard_bounds rho).1
  have hM : 0 ≤ M := Nat.cast_nonneg _
  have hC4 : 1 ≤ C^4 := one_le_pow₀ hC
  have hc4 : C ≤ C^4 := le_self_pow₀ hC (by decide)
  have hm : M ≤ (M+1)^2 := by nlinarith
  have hm2 : M^2 ≤ (M+1)^2 := by nlinarith
  have h1 : M ≤ (M+1)^2*C^4 := hm.trans (le_mul_of_one_le_right (sq_nonneg _) hC4)
  have h2 : M*C ≤ (M+1)^2*C^4 := mul_le_mul hm hc4 (by linarith) (sq_nonneg _)
  have h3 : M^2*C^4 ≤ (M+1)^2*C^4 := mul_le_mul_of_nonneg_right hm2 (by positivity)
  have hb : 2*M+2*M*C+2*M^2*C^4 ≤ 16*C^4*(M+1)^2 := by nlinarith
  have hP : (0:ℝ) < (P:ℝ)+1 := by positivity
  have hprec : (precision rho m P:ℝ) = 16*C^4*(M+1)^2*((P:ℝ)+1) := by
    simp only [precision,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,Nat.cast_add,Nat.cast_one,C,M]
  change (2*M+2*M*C+2*M^2*C^4)*((precision rho m P:ℝ)+1)⁻¹ ≤ ((P:ℝ)+1)⁻¹
  apply (mul_inv_le_iff₀ (by positivity : (0:ℝ) < (precision rho m P:ℝ)+1)).mpr
  rw [hprec]
  have heq : ((P:ℝ)+1)⁻¹*(16*C^4*(M+1)^2*((P:ℝ)+1)+1) =
      16*C^4*(M+1)^2+((P:ℝ)+1)⁻¹ := by field_simp
  rw [heq]
  exact hb.trans (le_add_of_nonneg_right (inv_nonneg.mpr hP.le))

theorem approximation_error (rho P : ℕ) (hrho : 0 < rho) {scale : ℚ}
    (hscale : (1:ℝ) ≤ scale) (S : ℚ) {m : ℕ} (u : Fin m → ℚ×ℚ)
    (hu : Function.Injective u)
    (hc : ∀ i, localizedCounterterm (GaussianFrequency.frequency rho)
      (fun j => PlanarForcingProgram.position (u j)) i ≤ scale)
    (x : CappedKernelProgram.Triple) :
    |(value rho P scale S (List.ofFn u) x:ℝ)-
      manufacturedWellField (GaussianFrequency.frequency rho) scale S
        (fun i => PlanarForcingProgram.position (u i)) (CappedKernelProgram.position x)| ≤
      ((P:ℝ)+1)⁻¹ := by
  unfold value
  rw [List.length_ofFn]
  exact (raw_error rho (precision rho m P) hrho hscale S u hu hc x).trans (precision_budget rho m P)

end ContinuumCoulomb.ManufacturedFieldEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedVelocityEvaluation
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual manufactured Moser velocity is sampled using rational
coordinate differences, the certified scalar field evaluator and π.
No value or derivative evaluator is assumed. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb.ManufacturedVelocityEvaluation
open CappedKernelProgram (Triple position)
open NeutralAtom (dirPartial axis)

theorem pi_error (p : ℕ) : |(pi p:ℝ)-Real.pi| ≤ ((p:ℝ)+1)⁻¹ := by
  have h := PiProgram.error (8*(p+1)) (by omega)
  have he : 8/((8*(p+1):ℕ):ℝ) = ((p:ℝ)+1)⁻¹ := by
    push_cast
    field_simp
  exact h.trans_eq he

theorem precision_budget (rho P : ℕ) :
    3*(1+(MoserDifferenceBudget.guard:ℝ)*(4*(rho:ℝ)+1))*
      ((precision rho P:ℝ)+1)⁻¹ ≤ ((P:ℝ)+1)⁻¹ := by
  let A : ℝ := 1+(MoserDifferenceBudget.guard:ℝ)*(4*(rho:ℝ)+1)
  have hA : 0 < A := by dsimp [A]; positivity
  have hP : 0 < (P:ℝ)+1 := by positivity
  have hp : (precision rho P:ℝ) = 12*A*((P:ℝ)+1) := by
    simp only [precision,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one,A]
  change 3*A*((precision rho P:ℝ)+1)⁻¹ ≤ ((P:ℝ)+1)⁻¹
  apply (mul_inv_le_iff₀ (by positivity : (0:ℝ) < (precision rho P:ℝ)+1)).mpr
  rw [hp]
  have he : ((P:ℝ)+1)⁻¹*(12*A*((P:ℝ)+1)+1) = 12*A+((P:ℝ)+1)⁻¹ := by field_simp
  rw [he]
  linarith [inv_nonneg.mpr hP.le]

theorem gradient_laplacian_error (rho p : ℕ) (hrho : 0 < rho)
    {scale S : ℚ} (hscale : (1:ℝ) ≤ scale) (hS : (1:ℝ) ≤ S)
    {m : ℕ} (u : Fin m → ℚ×ℚ) (hu : Function.Injective u)
    (hsep : ∀ i j, i ≠ j → 3 ≤ ‖PlanarForcingProgram.position (u i)-PlanarForcingProgram.position (u j)‖)
    (hc : ∀ i, localizedCounterterm (GaussianFrequency.frequency rho)
      (fun j => PlanarForcingProgram.position (u j)) i ≤ scale) (q : Triple) :
    (∀ a, |(gradient rho p scale S (List.ofFn u) q a:ℝ)-
      dirPartial (manufacturedWellField (GaussianFrequency.frequency rho) scale S
        (fun i => PlanarForcingProgram.position (u i))) (axis a) (position q)| ≤ ((p:ℝ)+1)⁻¹) ∧
    |(laplacian rho p scale S (List.ofFn u) q:ℝ)-
      NeutralAtom.coordinateLaplacian (manufacturedWellField (GaussianFrequency.frequency rho) scale S
        (fun i => PlanarForcingProgram.position (u i))) (position q)| ≤ ((p:ℝ)+1)⁻¹ := by
  let V := manufacturedWellField (GaussianFrequency.frequency rho) scale S
    (fun i => PlanarForcingProgram.position (u i))
  have hV : ContDiff ℝ 6 V := (manufacturedWellField_C7 _ _ _ _).of_le (by norm_num)
  have hb (k : ℕ) (hk : k ≤ 6) (x : Position) :
      ‖iteratedFDeriv ℝ k V x‖ ≤ (MoserDifferenceBudget.guard:ℝ) :=
    (manufacturedWellField_derivative_bound (GaussianFrequency.frequency rho)
      (show (0:ℝ) < scale by linarith) hS _ hsep hc hk x).trans MoserDifferenceBudget.guard_bound
  have hs (r : Triple) : |(sample rho p scale S (List.ofFn u) r:ℝ)-V (position r)| ≤
      ((MoserDifferenceBudget.precision p:ℝ)+1)⁻¹ :=
    ManufacturedFieldEvaluation.approximation_error rho (MoserDifferenceBudget.precision p)
      hrho hscale S u hu hc r
  have hB : (0:ℝ) ≤ MoserDifferenceBudget.guard := Nat.cast_nonneg _
  have hε : 0 ≤ ((MoserDifferenceBudget.precision p:ℝ)+1)⁻¹ :=
    inv_nonneg.mpr (add_nonneg (Nat.cast_nonneg _) zero_le_one)
  constructor
  · intro a
    have he := RationalFieldDifferences.first_error V hV _ hB hε
      (MoserDifferenceBudget.step_positive p) hb hs q a
    apply he.trans
    apply (MoserDifferenceBudget.first_budget p).trans
    apply inv_anti₀ (by positivity)
    linarith [Nat.cast_nonneg (α := ℝ) p]
  · exact (RationalFieldDifferences.laplacian_error V hV _ hB hε
      (MoserDifferenceBudget.step_positive p) hb hs q).trans (MoserDifferenceBudget.laplacian_budget p)

theorem approximation_error_oai (rho P : ℕ) (hrho : 0 < rho)
    {scale S : ℚ} (hscale : (1:ℝ) ≤ scale) (hS : (1:ℝ) ≤ S)
    {m : ℕ} (u : Fin m → ℚ×ℚ) (hu : Function.Injective u)
    (hsep : ∀ i j, i ≠ j → 3 ≤ ‖PlanarForcingProgram.position (u i)-PlanarForcingProgram.position (u j)‖)
    (hc : ∀ i, localizedCounterterm (GaussianFrequency.frequency rho)
      (fun j => PlanarForcingProgram.position (u j)) i ≤ scale)
    (hcharge : ∀ x, |manufacturedCharge (manufacturedWellField (GaussianFrequency.frequency rho)
      scale S (fun i => PlanarForcingProgram.position (u i))) x| ≤ (rho:ℝ)/2)
    {t : ℚ} (ht : (t:ℝ) ∈ Set.Icc (0:ℝ) 1) (q : Triple) :
    ‖position (value rho P scale S (List.ofFn u) t q)-
      moserVelocity (rho:ℝ) (manufacturedWellField (GaussianFrequency.frequency rho)
        scale S (fun i => PlanarForcingProgram.position (u i))) t (position q)‖ ≤ ((P:ℝ)+1)⁻¹ := by
  let V := manufacturedWellField (GaussianFrequency.frequency rho) scale S
    (fun i => PlanarForcingProgram.position (u i))
  let p := precision rho P
  let E : ℝ := (1+(MoserDifferenceBudget.guard:ℝ)*(4*(rho:ℝ)+1))*((p:ℝ)+1)⁻¹
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hg := gradient_laplacian_error rho p hrho hscale hS u hu hsep hc q
  have hbound (a : Fin 3) : |dirPartial V (axis a) (position q)| ≤ (MoserDifferenceBudget.guard:ℝ) := by
    have he := dirPartial_iterated_norm_bound V
      ((manufacturedWellField_C7 _ _ _ _).of_le (by norm_num)) (axis a) (k := 0) (by omega) (position q)
    rw [norm_iteratedFDeriv_zero,Real.norm_eq_abs,show ‖axis a‖=1 by simp [axis],one_mul] at he
    exact he.trans ((manufacturedWellField_derivative_bound (GaussianFrequency.frequency rho)
      (show (0:ℝ) < scale by linarith) hS _ hsep hc (k := 1) (by omega) _).trans
      MoserDifferenceBudget.guard_bound)
  have he (a : Fin 3) : |(component rho P scale S (List.ofFn u) t q a:ℝ)-
      moserVelocity (rho:ℝ) V t (position q) a| ≤ E := by
    have hh := MoserVelocityNumerics.component_error (rho:ℝ) (by exact_mod_cast (Nat.succ_le_of_lt hrho))
      V hcharge ht (position q) a
      (gradient rho p scale S (List.ofFn u) q a) (laplacian rho p scale S (List.ofFn u) q)
      (pi p) (hbound a) (hg.1 a) hg.2 (pi_error p)
    simpa only [component,Rat.cast_div,Rat.cast_neg,Rat.cast_max,Rat.cast_natCast,Rat.cast_add,
      Rat.cast_mul,Rat.cast_ofNat,p,E] using hh
  let e : Position := position (value rho P scale S (List.ofFn u) t q)-moserVelocity (rho:ℝ) V t (position q)
  have hecoord (a : Fin 3) : |e a| ≤ E := by
    fin_cases a
    · simpa [e,value,position] using he 0
    · simpa [e,value,position] using he 1
    · simpa [e,value,position] using he 2
  have hsq : ‖e‖^2 ≤ 3*E^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have h := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin 3))) =>
      (sq_le_sq₀ (abs_nonneg _) hE).mpr (hecoord a))
    simpa only [sq_abs,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] using h
  have hn : ‖e‖ ≤ 3*E := by nlinarith [norm_nonneg e,sq_nonneg E]
  apply hn.trans
  simpa only [E,p,mul_assoc] using precision_budget rho P

end ContinuumCoulomb.ManufacturedVelocityEvaluation

end

end OAI
end

theorem solution : type_of% @OAI.ContinuumCoulomb.ManufacturedVelocityEvaluation.approximation_error_oai := @OAI.ContinuumCoulomb.ManufacturedVelocityEvaluation.approximation_error_oai
