-- Prove2me | solution 1 for OAI.TotientAsymptotic.ford_scale_lower
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:34:08.799105+00:00
-- url     : https://prove2.me/submissions/4b1b3653-5c4b-4f3e-a8b6-08156de3a929

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
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
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
import Mathlib.MeasureTheory.Group.Measure
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
import Mathlib.Order.Fin.Tuple
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
import Theorems.Thm_OAI_TotientAsymptotic_full_fiber_scale_family

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FullFiberValueCount
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A full fiber with seed one gives an injective family of totient values. -/
noncomputable section
namespace TotientAsymptotic

lemma fullFiber_one_totient_injective {b c : ℕ} (hb : 0 < b) (hc : 0 < c)
    (hbfull : FullFiber 1 b) (hcfull : FullFiber 1 c)
    (he : b.totient=c.totient) : b=c := by
  obtain ⟨u,hu,_huφ,heu⟩ := (hcfull b).mp ⟨hb,by simpa only [one_mul] using he⟩
  obtain ⟨v,hv,_hvφ,hev⟩ := (hbfull c).mp ⟨hc,by simpa only [one_mul] using he.symm⟩
  have hcb : c ≤ b := by rw [heu]; exact Nat.le_mul_of_pos_right _ hu
  have hbc : b ≤ c := by rw [hev]; exact Nat.le_mul_of_pos_right _ hv
  exact Nat.le_antisymm hbc hcb

theorem fullFiber_one_card_le_V {x : ℝ} (S : Finset ℕ)
    (hS : ∀ b ∈ S,0 < b ∧ (b.totient:ℝ) ≤ x ∧ FullFiber 1 b) :
    (S.card:ℝ) ≤ V x := by
  classical
  have hinj : Set.InjOn Nat.totient (S : Set ℕ) := by
    intro b hb c hc he
    exact fullFiber_one_totient_injective (hS b hb).1 (hS c hc).1
      (hS b hb).2.2 (hS c hc).2.2 he
  have hsub : S.image Nat.totient ⊆ (Finset.Icc 1 ⌊x⌋₊).filter IsTotient := by
    intro v hv
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hbpos,hbx,_hbfull⟩ := hS b hb
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨Nat.totient_pos.mpr hbpos,?_⟩,b,hbpos,rfl⟩
    exact Nat.le_floor hbx
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj] at hc
  unfold V
  exact_mod_cast hc

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalFullCandidateScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert a positive fixed-prefix family into the natural counting scale.
These finite-family bridges will be applied after the regular residual
comparison estimate has been proved. -/
noncomputable section
open scoped Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

/-- With seed one the totient map is injective on the constructed family,
so its positive mass proves Ford's lower counting bound. -/
theorem ford_scale_lower_of_one_family
    (hfamily : ∃ a K : ℝ,0<a ∧ 0<K ∧ ∀ᶠ x : ℝ in atTop,
      0<x ∧ ∃ S : Finset ℕ,a*(x/Real.log x)*G x (m x) ≤ (S.card:ℝ) ∧
        ∀ b∈S,0<b ∧ ((1*b.totient:ℕ):ℝ)≤x ∧
          FullFiber 1 b ∧ (b:ℝ)/b.totient≤K) :
    ∃ a : ℝ,0<a ∧ ∀ᶠ x : ℝ in atTop,a*(x/Real.log x)*G x (m x)≤V x := by
  obtain ⟨a,K,ha,_hK,hfamily⟩ := hfamily
  refine ⟨a,ha,?_⟩
  filter_upwards [hfamily] with x hx
  obtain ⟨_hx,S,hcard,hS⟩ := hx
  apply hcard.trans (fullFiber_one_card_le_V S ?_)
  intro b hb
  obtain ⟨hpos,hvalue,hfull,_hratio⟩ := hS b hb
  exact ⟨hpos,by simpa only [one_mul] using hvalue,hfull⟩

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FiberPropagationInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Discharge the fixed-seed fiber propagation input by pruning the actual
normal candidate family. Seed one also supplies Ford's lower counting bound. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

theorem ford_scale_lower_oai :
    ∃ a : ℝ,0 < a ∧ ∀ᶠ x : ℝ in atTop,a*(x/Real.log x)*G x (m x) ≤ V x := by
  apply ford_scale_lower_of_one_family
  exact full_fiber_scale_family 1 ⟨1,by decide,by simp⟩

end TotientAsymptotic

end

end OAI
end

theorem solution : type_of% @OAI.TotientAsymptotic.ford_scale_lower_oai := @OAI.TotientAsymptotic.ford_scale_lower_oai
