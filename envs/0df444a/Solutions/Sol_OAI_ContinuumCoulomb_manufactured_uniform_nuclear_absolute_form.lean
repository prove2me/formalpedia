-- Prove2me | solution 1 for OAI.ContinuumCoulomb.manufactured_uniform_nuclear_absolute_form
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:27:39.691614+00:00
-- url     : https://prove2.me/submissions/6927ac12-7b05-4174-a7f6-c0242634b515

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
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
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.ODE.ExistUnique
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
import Mathlib.Data.List.Nodup
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Tactic
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_OAIQ092A008
import Definitions.Def_OAIQ092A009

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FormDomain_HardyMollifier
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
open ContinuousLinearMap
open scoped Convolution

lemma hardyCoulomb_nonneg {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    (x : Configuration n) : 0 ≤ hardyCoulomb i R x := inv_nonneg.mpr (Real.sqrt_nonneg _)

lemma quadratic_young_reciprocal (t : ℝ) {η : ℝ} (hη : 0 < η) :
    t ≤ η * t^2 + 1 / (4 * η) := by
  calc
    t ≤ (4 * η^2 * t^2 + 1) / (4 * η) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * η)).mpr
      nlinarith [sq_nonneg (2 * η * t - 1)]
    _ = η * t^2 + 1 / (4 * η) := by field_simp

lemma H1Vector.coulomb_integrable_bound {n : ℕ} (ψ : H1Vector n) (s : Spins n)
    (i : Fin n) (R : HardyCoordinates n i) {η : ℝ} (hη : 0 < η) :
    Integrable (fun x => hardyCoulomb i R x * ‖ψ.value s x‖^2) ∧
    (∫ x, hardyCoulomb i R x * ‖ψ.value s x‖^2) ≤
      4 * η * (∑ b : Fin 3, ∫ x, ‖ψ.gradient s (i,b) x‖^2) +
      (1 / (4 * η)) * (∫ x, ‖ψ.value s x‖^2) := by
  have hH := ψ.hardy s i R
  have hρ : Integrable (fun x => ‖ψ.value s x‖^2) :=
    (memLp_two_iff_integrable_sq_norm (ψ.value_L2 s).aestronglyMeasurable).mp (ψ.value_L2 s)
  have hB : Integrable (fun x => η * ((blockRadiusSq i R x)⁻¹ * ‖ψ.value s x‖^2) +
      (1 / (4 * η)) * ‖ψ.value s x‖^2) :=
    (hH.1.const_mul η).add (hρ.const_mul (1 / (4 * η)))
  have hpoint : ∀ x, hardyCoulomb i R x * ‖ψ.value s x‖^2 ≤
      η * ((blockRadiusSq i R x)⁻¹ * ‖ψ.value s x‖^2) +
      (1 / (4 * η)) * ‖ψ.value s x‖^2 := by
    intro x
    have ht := mul_le_mul_of_nonneg_right
      (quadratic_young_reciprocal (hardyCoulomb i R x) hη) (sq_nonneg ‖ψ.value s x‖)
    simpa only [hardyCoulomb_sq, add_mul, mul_assoc] using ht
  have hI : Integrable (fun x => hardyCoulomb i R x * ‖ψ.value s x‖^2) := by
    apply hB.mono' ((measurable_hardyCoulomb i R).aestronglyMeasurable.mul
      ((ψ.value_L2 s).aestronglyMeasurable.norm.pow 2))
    apply Filter.Eventually.of_forall
    intro x
    simpa only [Pi.mul_apply, Pi.pow_apply, Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (hardyCoulomb_nonneg i R x) (sq_nonneg _))] using hpoint x
  refine ⟨hI, ?_⟩
  have hm := integral_mono hI hB hpoint
  rw [integral_add (hH.1.const_mul η) (hρ.const_mul (1 / (4 * η))),
    integral_const_mul, integral_const_mul] at hm
  have hhard := mul_le_mul_of_nonneg_left hH.2 hη.le
  nlinarith

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FormDomain_Add
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
open ContinuousLinearMap
open scoped Convolution

lemma blockRadiusSq_nuclear {n : ℕ} (i : Fin n) (R : Space) (x : Configuration n) :
    blockRadiusSq i (nuclearHardyCoordinates i R) x = ‖position x i - R‖^2 := by
  simp [blockRadiusSq, nuclearHardyCoordinates, position, EuclideanSpace.norm_sq_eq,
    Real.norm_eq_abs]

lemma hardyCoulomb_nuclear {n : ℕ} (i : Fin n) (R : Space) (x : Configuration n) :
    hardyCoulomb i (nuclearHardyCoordinates i R) x = coulombKernel (position x i - R) := by
  rw [hardyCoulomb, blockRadiusSq_nuclear, Real.sqrt_sq (norm_nonneg _)]
  rfl

lemma H1Vector.nuclear_coulomb_integrable_bound {n : ℕ} (ψ : H1Vector n)
    (s : Spins n) (i : Fin n) (R : Space) {η : ℝ} (hη : 0 < η) :
    Integrable (fun x => coulombKernel (position x i - R) * ‖ψ.value s x‖^2) ∧
    (∫ x, coulombKernel (position x i - R) * ‖ψ.value s x‖^2) ≤
      4 * η * (∑ b : Fin 3, ∫ x, ‖ψ.gradient s (i,b) x‖^2) +
      (1 / (4 * η)) * (∫ x, ‖ψ.value s x‖^2) := by
  simpa only [hardyCoulomb_nuclear] using
    ψ.coulomb_integrable_bound s i (nuclearHardyCoordinates i R) hη

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_NuclearRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Stability under rounding a nuclear position

Translated Hardy estimates uniformly control rational rounding on arbitrary
form-domain states. The constant eight permits a pointwise kernel inequality
also at the poles, using Lean's convention `0⁻¹ = 0`, and suffices for the
polynomial precision budget.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace ContinuumCoulomb

/-- Translated Hardy as a bound for the square of the physical Coulomb kernel. -/
theorem nuclear_hardy_square {n : ℕ} (state : Coulomb.H1Vector n)
    (spin : Coulomb.Spins n) (i : Fin n) (a : Coulomb.Space) :
    Integrable (fun x => Coulomb.coulombKernel (Coulomb.position x i - a) ^ 2 *
      ‖state.value spin x‖ ^ 2) ∧
    (∫ x, Coulomb.coulombKernel (Coulomb.position x i - a) ^ 2 *
      ‖state.value spin x‖ ^ 2) ≤
      4 * ∑ k : Fin 3, ∫ x, ‖state.gradient spin (i, k) x‖ ^ 2 := by
  have h := state.hardy spin i (Coulomb.nuclearHardyCoordinates i a)
  simpa only [← Coulomb.hardyCoulomb_sq,
    Coulomb.hardyCoulomb_nuclear] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedNuclearHardy
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.Coulomb.complexWindow_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A cutoff Hardy estimate for the near-node part of the nuclear mesh. The
right side is localized, allowing bounded-overlap summation over nuclei. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem localized_nuclear_hardy {n : ℕ} (u : Coulomb.H1Vector n)
    (s : SpinConfiguration n) (i : Fin n) (a : Position) {r D : ℝ} (hr : 0 < r)
    (f : Configuration n → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfB : ∀ x, |f x| ≤ 1)
    (hdfB : ∀ j x, |fderiv ℝ f x (EuclideanSpace.single j 1)| ≤ D)
    (A B : Set (Configuration n)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hnear : ∀ x ∈ A, ‖Coulomb.position x i-a‖ ≤ r)
    (hone : ∀ x ∈ A, f x = 1)
    (hzero : ∀ x ∉ B, f x = 0)
    (hdzero : ∀ k x, x ∉ B → fderiv ℝ f x (EuclideanSpace.single (i,k) 1) = 0) :
    (∫ x in A, Coulomb.coulombKernel (Coulomb.position x i-a)*‖u.value s x‖^2) ≤
      24*r*D^2*(∫ x in B, ‖u.value s x‖^2)+
      8*r*(∑ k : Fin 3, ∫ x in B, ‖u.gradient s (i,k) x‖^2) := by
  let v := u.smoothMul f hf 1 D hfB hdfB
  obtain ⟨hvi,hvh⟩ := nuclear_hardy_square v s i a
  have hpoint (x : Configuration n) :
      A.indicator (fun x => Coulomb.coulombKernel (Coulomb.position x i-a)*‖u.value s x‖^2) x ≤
      r*(Coulomb.coulombKernel (Coulomb.position x i-a)^2*‖v.value s x‖^2) := by
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx]
      have hv : v.value s x = u.value s x := by
        change (f x:ℂ)*u.value s x = _
        rw [hone x hx,Complex.ofReal_one,one_mul]
      rw [hv,← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      by_cases hz : ‖Coulomb.position x i-a‖ = 0
      · simp only [Coulomb.coulombKernel,hz,inv_zero,zero_pow (by decide : 2 ≠ 0),mul_zero,le_refl]
      · have hp : 0 < ‖Coulomb.position x i-a‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
        have hh := mul_le_mul_of_nonneg_right (hnear x hx) (sq_nonneg ‖Coulomb.position x i-a‖⁻¹)
        have he : ‖Coulomb.position x i-a‖*‖Coulomb.position x i-a‖⁻¹^2 =
            ‖Coulomb.position x i-a‖⁻¹ := by field_simp
        simpa only [Coulomb.coulombKernel,he] using hh
    · rw [Set.indicator_of_notMem hx]
      positivity
  have hnearint : (∫ x in A, Coulomb.coulombKernel (Coulomb.position x i-a)*‖u.value s x‖^2) ≤
      r*(∫ x, Coulomb.coulombKernel (Coulomb.position x i-a)^2*‖v.value s x‖^2) := by
    rw [← integral_indicator hA,← integral_const_mul]
    exact integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => by
      apply Set.indicator_nonneg
      intro y _
      exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (sq_nonneg _)))
      (hvi.const_mul r) (Filter.Eventually.of_forall hpoint)
  have hg (k : Fin 3) :
      (∫ x, ‖v.gradient s (i,k) x‖^2) ≤
        2*D^2*(∫ x in B, ‖u.value s x‖^2)+2*(∫ x in B, ‖u.gradient s (i,k) x‖^2) := by
    have hp (x : Configuration n) : ‖v.gradient s (i,k) x‖^2 ≤
        B.indicator (fun x => 2*D^2*‖u.value s x‖^2+2*‖u.gradient s (i,k) x‖^2) x := by
      by_cases hx : x ∈ B
      · rw [Set.indicator_of_mem hx]
        have h₁ : ‖(fderiv ℝ f x (EuclideanSpace.single (i,k) 1):ℂ)*u.value s x‖ ≤ D*‖u.value s x‖ := by
          rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (hdfB (i,k) x) (norm_nonneg _)
        have h₂ : ‖(f x:ℂ)*u.gradient s (i,k) x‖ ≤ ‖u.gradient s (i,k) x‖ := by
          rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
          simpa only [one_mul] using mul_le_mul_of_nonneg_right (hfB x) (norm_nonneg (u.gradient s (i,k) x))
        have ht := norm_add_le ((fderiv ℝ f x (EuclideanSpace.single (i,k) 1):ℂ)*u.value s x)
          ((f x:ℂ)*u.gradient s (i,k) x)
        change ‖(fderiv ℝ f x (EuclideanSpace.single (i,k) 1):ℂ)*u.value s x+
          (f x:ℂ)*u.gradient s (i,k) x‖^2 ≤ _
        nlinarith [norm_nonneg ((fderiv ℝ f x (EuclideanSpace.single (i,k) 1):ℂ)*u.value s x+
          (f x:ℂ)*u.gradient s (i,k) x),sq_nonneg (D*‖u.value s x‖-‖u.gradient s (i,k) x‖)]
      · rw [Set.indicator_of_notMem hx]
        change ‖(fderiv ℝ f x (EuclideanSpace.single (i,k) 1):ℂ)*u.value s x+
          (f x:ℂ)*u.gradient s (i,k) x‖^2 ≤ 0
        simp only [hdzero k x hx,hzero x hx,Complex.ofReal_zero,zero_mul,add_zero,norm_zero,
          zero_pow (by decide : 2 ≠ 0),le_refl]
    have hu := (u.value_L2 s).integrable_norm_pow (p := 2) (by decide)
    have hd := (u.partial_L2 s (i,k)).integrable_norm_pow (p := 2) (by decide)
    have hb := ((hu.const_mul (2*D^2)).add (hd.const_mul 2)).integrableOn.integrable_indicator hB
    have hi := integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => sq_nonneg ‖v.gradient s (i,k) x‖))
      hb (Filter.Eventually.of_forall hp)
    rw [integral_indicator hB] at hi
    simp only [Pi.add_apply] at hi
    rw [integral_add (hu.integrableOn.const_mul _) (hd.integrableOn.const_mul _),
      integral_const_mul,integral_const_mul] at hi
    exact hi
  have hs := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 3))) => hg k)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,← Finset.mul_sum,Nat.cast_ofNat] at hs
  have hh := mul_le_mul_of_nonneg_left hvh hr.le
  have hsum := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 4*r)
  nlinarith only [hnearint,hh,hsum]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FiniteOverlap
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing localized estimates using spatial overlap rather than the number
of nuclei. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem finite_overlap_integral {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    {μ : Measure X} (B : ι → Set X) (hB : ∀ i, MeasurableSet (B i))
    (f : X → ℝ) (hf : Integrable f μ) (hpos : ∀ x, 0 ≤ f x) (M : ℝ)
    (hoverlap : ∀ x, (∑ i, if x ∈ B i then (1:ℝ) else 0) ≤ M) :
    (∑ i, ∫ x in B i, f x ∂μ) ≤ M*∫ x, f x ∂μ := by
  classical
  simp_rw [← integral_indicator (hB _)]
  rw [← integral_finsetSum Finset.univ (fun i _ => hf.integrableOn.integrable_indicator (hB i)),
    ← integral_const_mul]
  apply integral_mono_of_nonneg
  · filter_upwards [] with x
    exact Finset.sum_nonneg (fun i _ => Set.indicator_nonneg (fun y _ => hpos y) x)
  · exact hf.const_mul M
  · filter_upwards [] with x
    have he : (∑ i, (B i).indicator f x) = (∑ i, if x ∈ B i then (1:ℝ) else 0)*f x := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hx : x ∈ B i <;> simp [hx]
    rw [he]
    exact mul_le_mul_of_nonneg_right (hoverlap x) (hpos x)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_Cubature
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Equal-mass two-point Gauss rule

The tensor product of this degree-three rule uses eight equal masses in each
three-dimensional cell. Exact moment identities and fourth-derivative estimates
control its error.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace ContinuumCoulomb

/-- Exactness for all four monomial moments needed in each coordinate. -/
theorem gaussTwoPoint_moment (k : ℕ) (hk : k ≤ 3) :
    gaussTwoPoint (fun x => x ^ k) = ∫ x : ℝ in (-1)..1, x ^ k := by
  interval_cases k
  · norm_num [gaussTwoPoint, integral_pow]
  · norm_num [gaussTwoPoint, integral_pow]
  · norm_num [gaussTwoPoint, integral_pow, gaussAbscissa_sq]
  · norm_num [gaussTwoPoint, integral_pow]
    ring

/-- Equal-weight quadrature integrates every cubic exactly. -/
theorem gaussTwoPoint_cubic (coefficient : Fin 4 → ℝ) :
    gaussTwoPoint (fun x => ∑ k : Fin 4, coefficient k * x ^ (k : ℕ)) =
      ∫ x : ℝ in (-1)..1, ∑ k : Fin 4, coefficient k * x ^ (k : ℕ) := by
  have hsum :
      gaussTwoPoint (fun x => ∑ k : Fin 4, coefficient k * x ^ (k : ℕ)) =
        ∑ k : Fin 4, coefficient k * gaussTwoPoint (fun x => x ^ (k : ℕ)) := by
    unfold gaussTwoPoint
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsum, intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    rw [gaussTwoPoint_moment k (by omega), intervalIntegral.integral_const_mul]
  · intro k _
    exact (continuous_const.mul (continuous_id.pow (k : ℕ))).intervalIntegrable _ _

/-- Uniform cubic approximation controls the quadrature and integral errors
separately, using the positivity and total mass of the rule. -/
theorem gaussTwoPoint_remainder_bound
    (f : ℝ → ℝ) (coefficient : Fin 4 → ℝ) {epsilon : ℝ}
    (hf : ContinuousOn f (Set.Icc (-1) 1))
    (happrox : ∀ x ∈ Set.Icc (-1) 1,
      |f x - ∑ k : Fin 4, coefficient k * x ^ (k : ℕ)| ≤ epsilon) :
    |gaussTwoPoint f - ∫ x : ℝ in (-1)..1, f x| ≤ 4 * epsilon := by
  let p : ℝ → ℝ := fun x => ∑ k : Fin 4, coefficient k * x ^ (k : ℕ)
  have hp : Continuous p := by unfold p; fun_prop
  have hg0 := gaussAbscissa_pos.le
  have hg1 : gaussAbscissa ≤ 1 := by nlinarith [gaussAbscissa_sq]
  have hleft := happrox (-gaussAbscissa) ⟨by linarith, by linarith⟩
  have hright := happrox gaussAbscissa ⟨by linarith, hg1⟩
  have hint : |∫ x : ℝ in (-1)..1, (f x - p x)| ≤ 2 * epsilon := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x => f x - p x) (a := -1) (b := 1) (C := epsilon) ?_
    · norm_num [Real.norm_eq_abs] at h
      simpa only [mul_comm] using h
    · intro x hx
      have hx' : -1 < x ∧ x ≤ 1 := by
        simpa only [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1), Set.mem_Ioc] using hx
      simpa only [Real.norm_eq_abs, p] using happrox x ⟨hx'.1.le, hx'.2⟩
  have hfi : IntervalIntegrable f volume (-1) 1 :=
    ContinuousOn.intervalIntegrable_of_Icc (by norm_num) hf
  have hpi : IntervalIntegrable p volume (-1) 1 := hp.intervalIntegrable _ _
  have heq : gaussTwoPoint f - (∫ x : ℝ in (-1)..1, f x) =
      (f (-gaussAbscissa) - p (-gaussAbscissa)) +
        (f gaussAbscissa - p gaussAbscissa) -
          (∫ x : ℝ in (-1)..1, f x - p x) := by
    rw [intervalIntegral.integral_sub hfi hpi]
    have h := gaussTwoPoint_cubic coefficient
    change p (-gaussAbscissa) + p gaussAbscissa = ∫ x : ℝ in (-1)..1, p x at h
    unfold gaussTwoPoint
    linarith
  rw [heq]
  calc
    _ ≤ |f (-gaussAbscissa) - p (-gaussAbscissa)| +
        |f gaussAbscissa - p gaussAbscissa| + |∫ x : ℝ in (-1)..1, f x - p x| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 4 * epsilon := by dsimp [p] at *; linarith

/-- A genuine fourth-derivative error bound for the normalized cell. The
coarse constant suffices for the manuscript's polynomial error budgets. -/
theorem gaussTwoPoint_C4_error (f : ℝ → ℝ) {C : ℝ} (hCnonneg : 0 ≤ C)
    (hf : ContDiffOn ℝ 4 f (Set.Icc (-1) 1))
    (hC : ∀ x ∈ Set.Icc (-1) 1,
      ‖iteratedDerivWithin 4 f (Set.Icc (-1) 1) x‖ ≤ C) :
    |gaussTwoPoint f - ∫ x : ℝ in (-1)..1, f x| ≤ (32 / 3 : ℝ) * C := by
  let d : Fin 4 → ℝ := fun k => taylorCoeffWithin f (k : ℕ) (Set.Icc (-1) 1) (-1)
  let coefficient : Fin 4 → ℝ :=
    ![d 0 + d 1 + d 2 + d 3, d 1 + 2 * d 2 + 3 * d 3, d 2 + 3 * d 3, d 3]
  have htaylor (x : ℝ) :
      taylorWithinEval f 3 (Set.Icc (-1) 1) (-1) x =
        ∑ k : Fin 4, coefficient k * x ^ (k : ℕ) := by
    rw [taylor_within_apply]
    norm_num [coefficient, d, taylorCoeffWithin, Fin.sum_univ_succ,
      Finset.sum_range_succ, smul_eq_mul]
    ring
  have happrox : ∀ x ∈ Set.Icc (-1) 1,
      |f x - ∑ k : Fin 4, coefficient k * x ^ (k : ℕ)| ≤ (8 / 3 : ℝ) * C := by
    intro x hx
    have h := taylor_mean_remainder_bound (n := 3) (by norm_num : (-1 : ℝ) ≤ 1)
      hf hx hC
    rw [htaylor x] at h
    norm_num [Real.norm_eq_abs, sub_neg_eq_add] at h
    have hp : (x + 1) ^ 4 ≤ (16 : ℝ) := by
      calc
        (x + 1) ^ 4 ≤ (2 : ℝ) ^ 4 :=
          pow_le_pow_left₀ (by linarith [hx.1]) (by linarith [hx.2]) 4
        _ = 16 := by norm_num
    have hm := mul_le_mul_of_nonneg_left hp hCnonneg
    nlinarith
  have h := gaussTwoPoint_remainder_bound f coefficient hf.continuousOn happrox
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_Variational_Axis
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

theorem norm_sq_axis_shift (x : Position) (a : Fin 3) (t : ℝ) :
    ‖x+t • axis a‖^2 = ‖x‖^2 + 2*t*x a + t^2 := by
  rw [norm_add_sq_real]
  simp [axis, inner_smul_right, EuclideanSpace.inner_single_right, norm_smul,
    Real.norm_eq_abs, sq_abs]
  ring

theorem second_deriv_quadratic_rpow {q b p : ℝ} (hq : 0 < q) :
    deriv (deriv (fun t : ℝ => (q+2*t*b+t^2)^p)) 0 =
      p*(p-1)*q^(p-2)*(2*b)^2 + 2*p*q^(p-1) := by
  let Q : ℝ → ℝ := fun t => q+2*t*b+t^2
  have hQ (t : ℝ) : HasDerivAt Q (2*b+2*t) t := by
    convert (((hasDerivAt_const t q).add
      (((hasDerivAt_id t).const_mul 2).mul_const b)).add
      ((hasDerivAt_id t).pow 2)) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | norm_num [Q]
  have hQ0 : Q 0 = q := by simp [Q]
  have hQe : ∀ᶠ t in 𝓝 (0 : ℝ), Q t ≠ 0 :=
    (hQ 0).continuousAt.eventually_ne (by simpa [hQ0] using ne_of_gt hq)
  have hder : deriv (fun t => Q t ^ p) =ᶠ[𝓝 0]
      fun t => p*Q t^(p-1)*(2*b+2*t) := by
    filter_upwards [hQe] with t ht
    convert ((hQ t).rpow_const (Or.inl ht)).deriv using 1
    all_goals try with_reducible_and_instances rfl
    ring
  rw [hder.deriv_eq]
  have hh := (((hQ 0).rpow_const (p := p-1)
      (Or.inl (by simpa [hQ0] using ne_of_gt hq))).const_mul p).mul
    ((hasDerivAt_const 0 (2*b)).add ((hasDerivAt_id 0).const_mul 2))
  have hh' : HasDerivAt (fun t => p*Q t^(p-1)*(2*b+2*t))
      (p*((2*b)*(p-1)*q^(p-1-1))*(2*b)+p*q^(p-1)*2) 0 := by
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | norm_num [Q]
  rw [hh'.deriv]
  rw [show p-1-1 = p-2 by ring]
  ring

open scoped Convolution
open ContinuousLinearMap

theorem hasCompactSupport_partial {f : Position → ℝ} (hf : HasCompactSupport f)
    (v : Position) : HasCompactSupport (dirPartial f v) := hf.fderiv_apply ℝ v

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_Variational_WeakLaplacian
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

theorem tsupport_dirPartial_subset (f : Position → ℝ) (v : Position) :
    tsupport (dirPartial f v) ⊆ tsupport f := tsupport_fderiv_apply_subset ℝ v

theorem hasCompactSupport_coordinateLaplacian {f : Position → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (coordinateLaplacian f) := by
  apply hf.mono'
  intro x hx
  by_contra hn
  exact hx (coordinateLaplacian_eq_zero_of_notMem_tsupport hn)

end NeutralAtom
end
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

theorem laplacian_regularizedKernel {ε : ℝ} (hε : ε ≠ 0) (x : Position) :
    coordinateLaplacian (regularizedKernel ε) x = -regularizedCharge ε x := by
  have hq : 0 < ‖x‖^2+ε^2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hε)
  have he : ∀ a : Fin 3, (fun t : ℝ => regularizedKernel ε (x+t • axis a)) =
      (fun t => ((‖x‖^2+ε^2)+2*t*x a+t^2)^(-1/2 : ℝ)) := by
    intro a
    ext t
    unfold regularizedKernel
    rw [norm_sq_axis_shift]
    congr 1
    ring
  unfold coordinateLaplacian
  simp_rw [he, second_deriv_quadratic_rpow hq]
  norm_num
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  have hpow : (‖x‖^2+ε^2)^(-5/2 : ℝ)*(‖x‖^2+ε^2) =
      (‖x‖^2+ε^2)^(-3/2 : ℝ) := by
    rw [← Real.rpow_add_one hq.ne']
    norm_num
  calc
    _ = 3*(‖x‖^2+ε^2)^(-5/2 : ℝ)*(∑ a : Fin 3, (x a)^2) -
        3*(‖x‖^2+ε^2)^(-3/2 : ℝ) := by
      rw [Finset.mul_sum]
      congr 1
      all_goals ring_nf
    _ = _ := by
      rw [← EuclideanSpace.real_norm_sq_eq]
      unfold regularizedCharge
      rw [← hpow]
      ring

theorem hasDerivAt_chargePrimitive (r : ℝ) :
    HasDerivAt chargePrimitive (3*r^2*(1+r^2)^(-5/2 : ℝ)) r := by
  have hp : 0 < 1+r^2 := by positivity
  have hd := ((hasDerivAt_id r).pow 3).mul
    (((hasDerivAt_const r 1).add ((hasDerivAt_id r).pow 2)).rpow_const
      (p := (-3/2 : ℝ)) (Or.inl hp.ne'))
  unfold chargePrimitive
  apply hd.congr_deriv
  norm_num
  have he : (1+r^2)^(-5/2 : ℝ)*(1+r^2) = (1+r^2)^(-3/2 : ℝ) := by
    rw [← Real.rpow_add_one hp.ne']; norm_num
  norm_num at he
  rw [← he]
  ring

theorem chargePrimitive_eq_ratio {r : ℝ} (hr : 0 ≤ r) :
    chargePrimitive r = (1-(1+r^2)⁻¹)^(3/2 : ℝ) := by
  have hp : 0 < 1+r^2 := by positivity
  have hh : 1-(1+r^2)⁻¹ = r^2/(1+r^2) := by field_simp; ring
  rw [hh, Real.div_rpow (sq_nonneg _) hp.le]
  have hn : (r^2)^(3/2 : ℝ) = r^3 := by
    rw [← Real.rpow_natCast_mul hr]
    norm_num
  rw [hn]
  unfold chargePrimitive
  rw [show (-3/2:ℝ) = -(3/2:ℝ) by ring, Real.rpow_neg hp.le]
  rfl

theorem tendsto_chargePrimitive : Tendsto chargePrimitive atTop (𝓝 1) := by
  have hp : Tendsto (fun r : ℝ => 1+r^2) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0))
  have hi := tendsto_inv_atTop_zero.comp hp
  have hh := (tendsto_const_nhds.sub hi).rpow tendsto_const_nhds
    (Or.inl (by norm_num : (1:ℝ)-0 ≠ 0) : (1:ℝ)-0 ≠ 0 ∨ 0 < (3/2:ℝ))
  apply Filter.Tendsto.congr' _ (by simpa using hh)
  filter_upwards [eventually_ge_atTop (0:ℝ)] with r hr
  exact (chargePrimitive_eq_ratio hr).symm

theorem integrable_radial_regularizedCharge_one :
    IntegrableOn (fun r : ℝ => 3*r^2*(1+r^2)^(-5/2 : ℝ)) (Set.Ioi 0) := by
  exact integrableOn_Ioi_deriv_of_nonneg' (fun r _ => hasDerivAt_chargePrimitive r)
    (fun r _ => by positivity) tendsto_chargePrimitive

theorem integral_radial_regularizedCharge_one :
    (∫ r : ℝ in Set.Ioi 0, 3*r^2*(1+r^2)^(-5/2 : ℝ)) = 1 := by
  have hder := integral_Ioi_of_hasDerivAt_of_nonneg'
    (a := (0:ℝ)) (fun r _ => hasDerivAt_chargePrimitive r)
    (fun r _ => by positivity : ∀ r ∈ Set.Ioi (0:ℝ), 0 ≤ 3*r^2*(1+r^2)^(-5/2 : ℝ))
    tendsto_chargePrimitive
  simpa [chargePrimitive] using hder

theorem regularizedCharge_one_eq : regularizedCharge 1 =
    fun x : Position => 3*(1+‖x‖^2)^(-5/2 : ℝ) := by
  ext x
  simp [regularizedCharge, add_comm]

theorem integrable_regularizedCharge_one : Integrable (regularizedCharge 1) := by
  rw [regularizedCharge_one_eq, integrable_fun_norm_addHaar volume
    (f := fun r : ℝ => 3*(1+r^2)^(-5/2:ℝ))]
  simpa [finrank_euclideanSpace_fin, smul_eq_mul, mul_comm, mul_assoc,
    mul_left_comm] using integrable_radial_regularizedCharge_one

theorem integral_regularizedCharge_one : (∫ x, regularizedCharge 1 x) = 4*Real.pi := by
  rw [regularizedCharge_one_eq, integral_fun_norm_addHaar volume
    (fun r : ℝ => 3*(1+r^2)^(-5/2:ℝ))]
  simp only [finrank_euclideanSpace_fin, smul_eq_mul, nsmul_eq_mul]
  norm_num
  have hi : (∫ r : ℝ in Set.Ioi 0, r^2*(3*(1+r^2)^(-(5/2): ℝ))) = 1 := by
    simpa only [neg_div, mul_assoc, mul_comm, mul_left_comm] using
      integral_radial_regularizedCharge_one
  rw [hi]
  simp only [Measure.real, EuclideanSpace.volume_ball_fin_three, ENNReal.ofReal_one,
    one_pow, one_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi*4/3)]
  ring

theorem regularizedCharge_smul {ε : ℝ} (hε : 0 < ε) (x : Position) :
    regularizedCharge ε (ε • x) = (ε^3)⁻¹*regularizedCharge 1 x := by
  unfold regularizedCharge
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
  have he : (ε*‖x‖)^2+ε^2 = ε^2*(‖x‖^2+1) := by ring
  rw [he, Real.mul_rpow (sq_nonneg _) (by positivity)]
  have hp : (ε^2)^(-5/2:ℝ) = (ε^5)⁻¹ := by
    rw [← Real.rpow_natCast_mul hε.le]
    norm_num [Real.rpow_neg hε.le]
  rw [hp]
  norm_num
  field_simp

theorem integral_regularizedCharge_scale {ε : ℝ} (hε : 0 < ε) (φ : Position → ℝ) :
    (∫ x, regularizedCharge ε x*φ x) = ∫ x, regularizedCharge 1 x*φ (ε • x) := by
  have hs := Measure.integral_comp_smul_of_nonneg volume
    (fun x => regularizedCharge ε x*φ x) ε (hR := hε.le)
  simp only [finrank_euclideanSpace_fin, smul_eq_mul] at hs
  have ht : (∫ x, regularizedCharge ε (ε • x)*φ (ε • x)) =
      (ε^3)⁻¹*(∫ x, regularizedCharge 1 x*φ (ε • x)) := by
    simp_rw [regularizedCharge_smul hε, mul_assoc]
    exact integral_const_mul _ _
  rw [ht] at hs
  exact (mul_left_cancel₀ (inv_ne_zero (pow_ne_zero _ hε.ne')) hs).symm

theorem regularizedCharge_nonneg (ε : ℝ) (x : Position) :
    0 ≤ regularizedCharge ε x := by unfold regularizedCharge; positivity

theorem continuous_regularizedCharge_one : Continuous (regularizedCharge 1) := by
  rw [regularizedCharge_one_eq]
  apply Continuous.const_mul
  apply Continuous.rpow_const
  · fun_prop
  · intro x
    left
    positivity

theorem regularizedCharge_tendsto_dirac {ε : ℕ → ℝ}
    (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    {φ : Position → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Tendsto (fun n => ∫ x, regularizedCharge (ε n) x*φ x)
      atTop (𝓝 (4*Real.pi*φ 0)) := by
  obtain ⟨C, hC⟩ := hφ.bounded_above_of_compact_support hφc
  have hD := tendsto_integral_of_dominated_convergence
    (μ := (volume : Measure Position)) (fun x => regularizedCharge 1 x*C)
    (F := fun n x => regularizedCharge 1 x*φ (ε n • x))
    (f := fun x => regularizedCharge 1 x*φ 0)
    (fun n => (continuous_regularizedCharge_one.mul
      (hφ.comp (show Continuous (fun x : Position => ε n • x) by fun_prop))).aestronglyMeasurable)
    (integrable_regularizedCharge_one.mul_const C)
    (fun n => Filter.Eventually.of_forall (fun x => by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (regularizedCharge_nonneg 1 x)]
      exact mul_le_mul_of_nonneg_left (hC _) (regularizedCharge_nonneg 1 x)))
    (Filter.Eventually.of_forall (fun x => by
      have he : Tendsto (fun n => ε n • x) atTop (𝓝 (0 : Position)) := by
        simpa using hlim.smul_const x
      exact tendsto_const_nhds.mul (hφ.continuousAt.tendsto.comp he)))
  simp only [integral_mul_const, integral_regularizedCharge_one] at hD
  simpa only [integral_regularizedCharge_scale (hε _)] using hD

theorem locallyIntegrable_coulombKernel : LocallyIntegrable coulombKernel volume := by
  intro x
  refine ⟨Metric.ball 0 (‖x‖+1), IsOpen.mem_nhds Metric.isOpen_ball ?_,
    coulombKernel_integrableOn_ball _⟩
  simpa only [Metric.mem_ball, dist_zero_right] using lt_add_one ‖x‖

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

theorem regularizedKernel_integral_tendsto {ε : ℕ → ℝ}
    (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    {φ : Position → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Tendsto (fun n => ∫ x, regularizedKernel (ε n) x*φ x)
      atTop (𝓝 (∫ x, coulombKernel x*φ x)) := by
  have hae : ∀ᵐ x : Position ∂volume, x ≠ 0 := volume.ae_ne 0
  have hb : Integrable (fun x => coulombKernel x*‖φ x‖) := by
    simpa only [smul_eq_mul] using
      locallyIntegrable_coulombKernel.integrable_smul_right_of_hasCompactSupport hφ.norm hφc.norm
  apply tendsto_integral_of_dominated_convergence (fun x => coulombKernel x*‖φ x‖)
  · intro n
    exact ((contDiff_regularizedKernel (hε n).ne').continuous.mul hφ).aestronglyMeasurable
  · exact hb
  · intro n
    filter_upwards [hae] with x hx
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (regularizedKernel_nonneg _ _)]
    exact mul_le_mul_of_nonneg_right (regularizedKernel_le hx) (norm_nonneg _)
  · filter_upwards [hae] with x hx
    exact (regularizedKernel_tendsto hlim hx).mul_const (φ x)

theorem coordinateLaplacian_translate (φ : Position → ℝ) (x y : Position) :
    coordinateLaplacian (fun z => φ (z+y)) x = coordinateLaplacian φ (x+y) := by
  unfold coordinateLaplacian
  simp only [add_right_comm _ _ y]

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombPoisson
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.Coulomb.complexWindow_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The Coulomb fundamental solution with finite smoothness

The manufactured planar well in the unit-charge paper has bounded continuous
derivatives through a finite order. Its density synthesis therefore needs
the fundamental-solution identity for compactly supported C² functions.
This extends the smooth-test identity by the same regularized
kernel argument, using only two integrations by parts.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace ContinuumCoulomb
open NeutralAtom (dirPartial coordinateLaplacian axis)

theorem integral_mul_laplacian_C2 (f phi : Position → ℝ)
    (hf : ContDiff ℝ 2 f) (hphi : ContDiff ℝ 2 phi) (hc : HasCompactSupport phi) :
    (∫ x, f x * coordinateLaplacian phi x) = ∫ x, coordinateLaplacian f x * phi x := by
  have hp (g : Position → ℝ) (hg : ContDiff ℝ 2 g) (v : Position) :
      ContDiff ℝ 1 (dirPartial g v) :=
    (hg.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).clm_apply contDiff_const
  have hpp (g : Position → ℝ) (hg : ContDiff ℝ 2 g) (v : Position) :
      Continuous (dirPartial (dirPartial g v) v) :=
    (((hp g hg v).fderiv_right (show (0 : WithTop ℕ∞) + 1 ≤ 1 by norm_num)).clm_apply
      contDiff_const).continuous
  have hpc (v : Position) : HasCompactSupport (dirPartial phi v) :=
    NeutralAtom.hasCompactSupport_partial hc v
  have hppc (v : Position) : HasCompactSupport (dirPartial (dirPartial phi v) v) :=
    NeutralAtom.hasCompactSupport_partial (hpc v) v
  have hleft (v : Position) : Integrable (fun x => f x * dirPartial (dirPartial phi v) v x) :=
    (hf.continuous.mul (hpp phi hphi v)).integrable_of_hasCompactSupport (hppc v).mul_left
  have hright (v : Position) : Integrable (fun x => dirPartial (dirPartial f v) v x * phi x) :=
    ((hpp f hf v).mul hphi.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hcross (v : Position) : Integrable (fun x => dirPartial f v x * dirPartial phi v x) :=
    ((hp f hf v).continuous.mul (hp phi hphi v).continuous).integrable_of_hasCompactSupport
      (hpc v).mul_left
  have hfg (v : Position) : Integrable (fun x => f x * dirPartial phi v x) :=
    (hf.continuous.mul (hp phi hphi v).continuous).integrable_of_hasCompactSupport
      (hpc v).mul_left
  have hfpg (v : Position) : Integrable (fun x => dirPartial f v x * phi x) :=
    ((hp f hf v).continuous.mul hphi.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hby (v : Position) :
      (∫ x, f x * dirPartial (dirPartial phi v) v x) =
        ∫ x, dirPartial (dirPartial f v) v x * phi x := by
    calc
      _ = -(∫ x, dirPartial f v x * dirPartial phi v x) :=
        integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
          (hcross v) (hleft v) (hfg v)
          (fun x _ => hf.differentiable (by norm_num) x)
          (fun x _ => (hp phi hphi v).differentiable (by norm_num) x)
      _ = _ := by
        have h : (∫ x, dirPartial f v x * dirPartial phi v x) =
            -(∫ x, dirPartial (dirPartial f v) v x * phi x) :=
          integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
            (hright v) (hcross v) (hfpg v)
            (fun x _ => (hp f hf v).differentiable (by norm_num) x)
            (fun x _ => hphi.differentiable (by norm_num) x)
        rw [h, neg_neg]
  have hphi_eq (x : Position) : coordinateLaplacian phi x =
      ∑ a : Fin 3, dirPartial (dirPartial phi (axis a)) (axis a) x :=
    NeutralAtom.coordinateLaplacian_eq_partials hphi.contDiffAt
  have hf_eq (x : Position) : coordinateLaplacian f x =
      ∑ a : Fin 3, dirPartial (dirPartial f (axis a)) (axis a) x :=
    NeutralAtom.coordinateLaplacian_eq_partials hf.contDiffAt
  simp_rw [hphi_eq, Finset.mul_sum]
  rw [integral_finsetSum _ (fun a _ => hleft (axis a))]
  simp_rw [hby]
  rw [← integral_finsetSum _ (fun a _ => hright (axis a))]
  simp_rw [hf_eq, Finset.sum_mul]

theorem coulomb_laplacian_C2 (phi : Position → ℝ)
    (hphi : ContDiff ℝ 2 phi) (hc : HasCompactSupport phi) :
    (∫ x, Coulomb.coulombKernel x * coordinateLaplacian phi x) =
      -(4 * Real.pi * phi 0) := by
  let epsilon : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hepsilon (n : ℕ) : 0 < epsilon n := by dsimp [epsilon]; positivity
  have hlim : Tendsto epsilon atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hl := NeutralAtom.regularizedKernel_integral_tendsto hepsilon hlim
    (NeutralAtom.continuous_coordinateLaplacian hphi)
    (NeutralAtom.hasCompactSupport_coordinateLaplacian hc)
  have hr := (NeutralAtom.regularizedCharge_tendsto_dirac hepsilon hlim hphi.continuous hc).neg
  have heq : (fun n => ∫ x, NeutralAtom.regularizedKernel (epsilon n) x *
      coordinateLaplacian phi x) =
      (fun n => -(∫ x, NeutralAtom.regularizedCharge (epsilon n) x * phi x)) := by
    funext n
    rw [integral_mul_laplacian_C2 _ _
      ((NeutralAtom.contDiff_regularizedKernel (hepsilon n).ne').of_le (by first | simp | exact_mod_cast le_top)) hphi hc]
    simp_rw [NeutralAtom.laplacian_regularizedKernel (hepsilon n).ne', neg_mul, integral_neg]
  rw [heq] at hl
  exact tendsto_nhds_unique hl hr

theorem coulomb_translated_laplacian_C2 (phi : Position → ℝ)
    (hphi : ContDiff ℝ 2 phi) (hc : HasCompactSupport phi) (a : Position) :
    (∫ x, Coulomb.coulombKernel (x - a) * coordinateLaplacian phi x) =
      -(4 * Real.pi * phi a) := by
  have ht : ContDiff ℝ 2 (fun z => phi (z + a)) := hphi.comp (contDiff_id.add contDiff_const)
  have htc : HasCompactSupport (fun z => phi (z + a)) :=
    hc.comp_homeomorph (Homeomorph.addRight a)
  have h := coulomb_laplacian_C2 _ ht htc
  simp only [NeutralAtom.coordinateLaplacian_translate, zero_add] at h
  rw [← integral_add_right_eq_self
    (fun x => Coulomb.coulombKernel (x - a) * coordinateLaplacian phi x) a]
  simpa only [add_sub_cancel_right] using h

/-- Exact Green identity, with the sign for an attractive positive density. -/
theorem manufacturedCharge_potential (V : Position → ℝ) (hV : ContDiff ℝ 2 V)
    (hc : HasCompactSupport V) (y : Position) :
    -(∫ x, Coulomb.coulombKernel (y - x) * manufacturedCharge V x) = V y := by
  have h := coulomb_translated_laplacian_C2 V hV hc y
  have heq : (fun x => Coulomb.coulombKernel (y - x) * manufacturedCharge V x) =
      (fun x => (Coulomb.coulombKernel (x - y) * coordinateLaplacian V x) / (4 * Real.pi)) := by
    funext x
    dsimp [manufacturedCharge, Coulomb.coulombKernel]
    rw [norm_sub_rev]
    ring
  rw [heq, integral_div, h]
  field_simp

end ContinuumCoulomb

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

lemma coulombKernel_ball_integral {R : ℝ} (hR : 0 ≤ R) :
    (∫ x : Space in Metric.ball 0 R, coulombKernel x) = 2 * Real.pi * R^2 := by
  have H := integral_fun_norm_addHaar (volume : Measure Space)
    (fun t : ℝ => if t < R then t⁻¹ else 0)
  have hleft : (∫ x : Space in Metric.ball 0 R, coulombKernel x) =
      ∫ x : Space, (if ‖x‖ < R then ‖x‖⁻¹ else 0) := by
    rw [← integral_indicator measurableSet_ball]
    simp only [Set.indicator, Metric.mem_ball, dist_zero_right, coulombKernel]
  rw [hleft, H]
  have hball : volume.real (Metric.ball (0 : Space) 1) = 4 * Real.pi / 3 := by
    rw [Measure.real, EuclideanSpace.volume_ball_fin_three]
    norm_num
    rw [ENNReal.toReal_ofReal (by positivity)]
    ring
  have hdim : Module.finrank ℝ Space = 3 := by simp [Space]
  simp only [hdim, hball, nsmul_eq_mul, smul_eq_mul]
  have hint : (∫ t in Ioi (0:ℝ), t^(3-1) * (if t < R then t⁻¹ else 0)) = ∫ t in Ioo 0 R, t := by
    calc
      _ = ∫ t in Ioi (0:ℝ), (Iio R).indicator (fun u : ℝ => u) t := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        change 0 < t at ht
        by_cases h : t < R
        · simp only [h, ite_true, if_true, Set.indicator, mem_Iio]
          norm_num
          field_simp
        · simp [Set.indicator, h]
      _ = _ := by rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio, inter_comm, Ioi_inter_Iio]
  rw [hint, setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le hR]
  norm_num [integral_id]
  ring

lemma truncatedCoulomb_nonneg (R : ℝ) (x : Space) : 0 ≤ truncatedCoulomb R x :=
  Set.indicator_nonneg (fun _ _ => coulombKernel_nonneg _) x
lemma truncatedCoulomb_integrable (R : ℝ) : Integrable (truncatedCoulomb R) :=
  (coulombKernel_integrableOn_ball R).integrable_indicator measurableSet_ball
lemma truncatedCoulomb_integral {R : ℝ} (hR : 0 ≤ R) :
    (∫ x, truncatedCoulomb R x) = 2*Real.pi*R^2 := by
  unfold truncatedCoulomb
  rw [integral_indicator measurableSet_ball, coulombKernel_ball_integral hR]

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
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

theorem manufacturedCharge_continuous (V : Position → ℝ) (hV : ContDiff ℝ 2 V) :
    Continuous (manufacturedCharge V) :=
  (NeutralAtom.continuous_coordinateLaplacian hV).div_const _

theorem manufacturedCharge_compact (V : Position → ℝ) (hc : HasCompactSupport V) :
    HasCompactSupport (manufacturedCharge V) := by
  exact (NeutralAtom.hasCompactSupport_coordinateLaplacian hc).comp_left
    (g := fun t : ℝ => t / (4 * Real.pi)) (by simp)

theorem manufacturedCharge_zero {V : Position → ℝ} {x : Position} (hx : x ∉ tsupport V) :
    manufacturedCharge V x = 0 := by
  simp only [manufacturedCharge, NeutralAtom.coordinateLaplacian_eq_zero_of_notMem_tsupport hx,
    zero_div]

theorem synthesizedDensity_bounds {rho H S : ℝ} (hrho : 0 ≤ rho)
    (V : Position → ℝ) (hsupport : tsupport V ⊆ slabDomain H S)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2) (x : Position) :
    0 ≤ synthesizedDensity rho H S V x ∧
      synthesizedDensity rho H S V x ≤ 3 * rho / 2 := by
  by_cases hx : x ∈ slabDomain H S
  · obtain ⟨hl, hu⟩ := abs_le.mp (hbound x)
    simp only [synthesizedDensity, slabDensity, Set.indicator_of_mem hx]
    constructor <;> linarith
  · have hzero := manufacturedCharge_zero (fun hv => hx (hsupport hv))
    simp only [synthesizedDensity, slabDensity, Set.indicator_of_notMem hx, hzero, add_zero]
    exact ⟨le_rfl, by linarith⟩

/-- Equation (4) of the unit-charge manuscript, as an identity of the actual
three-dimensional Coulomb integrals at every evaluation point. -/
theorem synthesizedDensity_potential {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (V : Position → ℝ)
    (hV : ContDiff ℝ 2 V) (hc : HasCompactSupport V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2) (y : Position) :
    -(∫ x, Coulomb.coulombKernel (y - x) * synthesizedDensity rho H S V x) =
      slabPotential rho H S y + V y := by
  have hslabMeas : Measurable (slabDensity rho H S) :=
    measurable_const.indicator (slabDomain_isClosed H S).measurableSet
  have hslabBound (x : Position) : ‖slabDensity rho H S x‖ ≤ rho := by
    by_cases hx : x ∈ slabDomain H S
    · simp only [slabDensity, Set.indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg hrho]
      exact le_rfl
    · simp only [slabDensity, Set.indicator_of_notMem hx, norm_zero]
      exact hrho
  have hIslab := Coulomb.coulomb_signed_convolution_integrable
    (slabDensity_integrable hH hS rho) hslabMeas hslabBound y
  have hIcharge := Coulomb.coulomb_signed_convolution_integrable
    ((manufacturedCharge_continuous V hV).integrable_of_hasCompactSupport
      (manufacturedCharge_compact V hc))
    (manufacturedCharge_continuous V hV).measurable
    (fun x => by simpa only [Real.norm_eq_abs] using hbound x) y
  have heq : (fun x => Coulomb.coulombKernel (y - x) * synthesizedDensity rho H S V x) =
      (fun x => Coulomb.coulombKernel (y - x) * slabDensity rho H S x +
        Coulomb.coulombKernel (y - x) * manufacturedCharge V x) := by
    funext x
    simp only [synthesizedDensity, mul_add]
  rw [heq, integral_add hIslab hIcharge, neg_add]
  rw [manufacturedCharge_potential V hV hc y]
  rfl

end ContinuumCoulomb

end

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

theorem homotopyDensity_pos {rho : ℝ} (hrho : 0 < rho) (V : Position → ℝ)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : Position) :
    0 < homotopyDensity rho V t x :=
  (by positivity : (0 : ℝ) < rho / 2).trans_le
    (homotopyDensity_bounds V hbound ht0 ht1 x).1

theorem homotopyDensity_endpoints (rho : ℝ) (V : Position → ℝ) (x : Position) :
    homotopyDensity rho V 0 x = rho ∧
      homotopyDensity rho V 1 x = rho + manufacturedCharge V x := by
  simp only [homotopyDensity, zero_mul, one_mul, add_zero, and_self]

theorem homotopyDensity_time_deriv (rho : ℝ) (V : Position → ℝ) (t : ℝ) (x : Position) :
    deriv (fun s => homotopyDensity rho V s x) t = manufacturedCharge V x := by
  simpa only [homotopyDensity, one_mul, id_eq] using
    ((hasDerivAt_id t).mul_const (manufacturedCharge V x)).const_add rho |>.deriv

theorem moserVelocity_zero {rho t : ℝ} {V : Position → ℝ} {x : Position}
    (hx : x ∉ tsupport V) : moserVelocity rho V t x = 0 := by
  ext a
  have hp : x ∉ tsupport (dirPartial V (axis a)) :=
    fun hp => hx (NeutralAtom.tsupport_dirPartial_subset V (axis a) hp)
  change -(dirPartial V (axis a) x) / (4 * Real.pi * homotopyDensity rho V t x) = 0
  rw [image_eq_zero_of_notMem_tsupport hp, neg_zero, zero_div]

theorem moser_flux (rho : ℝ) (V : Position → ℝ) (t : ℝ) (x : Position)
    (hpos : homotopyDensity rho V t x ≠ 0) (a : Fin 3) :
    homotopyDensity rho V t x * moserVelocity rho V t x a =
      -(dirPartial V (axis a) x) / (4 * Real.pi) := by
  change homotopyDensity rho V t x *
    (-(dirPartial V (axis a) x) / (4 * Real.pi * homotopyDensity rho V t x)) = _
  field_simp [hpos]

/-- The continuity equation holds as an exact identity before any use of
flow transport or a numerical approximation to the flow. -/
theorem moser_continuity_equation {rho : ℝ} (hrho : 0 < rho)
    (V : Position → ℝ) (hV : ContDiff ℝ 2 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : Position) :
    deriv (fun s => homotopyDensity rho V s x) t +
      (∑ a : Fin 3, dirPartial
        (fun y => homotopyDensity rho V t y * moserVelocity rho V t y a) (axis a) x) = 0 := by
  have hflux (a : Fin 3) :
      (fun y => homotopyDensity rho V t y * moserVelocity rho V t y a) =
      (fun y => -(4 * Real.pi)⁻¹ * dirPartial V (axis a) y) := by
    funext y
    rw [moser_flux rho V t y (homotopyDensity_pos hrho V hbound ht0 ht1 y).ne' a]
    ring
  have hp (a : Fin 3) : Differentiable ℝ (dirPartial V (axis a)) :=
    ((hV.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).clm_apply
      contDiff_const).differentiable (by norm_num)
  rw [homotopyDensity_time_deriv]
  simp_rw [hflux]
  have hpartial (a : Fin 3) :
      dirPartial (fun y => -(4 * Real.pi)⁻¹ * dirPartial V (axis a) y) (axis a) x =
      -(4 * Real.pi)⁻¹ * dirPartial (dirPartial V (axis a)) (axis a) x := by
    change (fderiv ℝ (fun y => -(4 * Real.pi)⁻¹ * dirPartial V (axis a) y) x) (axis a) = _
    rw [fderiv_const_mul (hp a x)]
    rfl
  simp_rw [hpartial]
  rw [← Finset.mul_sum, ← NeutralAtom.coordinateLaplacian_eq_partials hV.contDiffAt]
  dsimp [manufacturedCharge]
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_MoserRegularity
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite C⁶ regularity of the manufactured well gives the C⁴ transport
field required by the unit-charge cubature. No C∞ assumption is added. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb
open NeutralAtom (dirPartial coordinateLaplacian axis)

theorem manufacturedCharge_C4 (V : Position → ℝ) (hV : ContDiff ℝ 6 V) :
    ContDiff ℝ 4 (manufacturedCharge V) := by
  have hp (v : Position) : ContDiff ℝ 5 (dirPartial V v) :=
    (hV.fderiv_right (show (5 : WithTop ℕ∞) + 1 ≤ 6 by norm_num)).clm_apply contDiff_const
  have hpp (v : Position) : ContDiff ℝ 4 (dirPartial (dirPartial V v) v) :=
    ((hp v).fderiv_right (show (4 : WithTop ℕ∞) + 1 ≤ 5 by norm_num)).clm_apply contDiff_const
  have heq : coordinateLaplacian V = fun x =>
      ∑ a : Fin 3, dirPartial (dirPartial V (axis a)) (axis a) x :=
    funext (fun _ => NeutralAtom.coordinateLaplacian_eq_partials
      (hV.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 6)).contDiffAt)
  change ContDiff ℝ 4 (fun x => coordinateLaplacian V x / (4 * Real.pi))
  rw [heq]
  exact (ContDiff.sum (fun a _ => hpp (axis a))).div_const _

theorem homotopyDensity_joint_C4 (rho : ℝ) (V : Position → ℝ) (hV : ContDiff ℝ 6 V) :
    ContDiff ℝ 4 (fun p : ℝ × Position => homotopyDensity rho V p.1 p.2) :=
  contDiff_const.add (contDiff_fst.mul ((manufacturedCharge_C4 V hV).comp contDiff_snd))

theorem moserDomain_isOpen (rho : ℝ) (V : Position → ℝ) (hV : ContDiff ℝ 6 V) :
    IsOpen (moserDomain rho V) :=
  isOpen_ne.preimage (homotopyDensity_joint_C4 rho V hV).continuous

theorem moserVelocity_joint_C4 (rho : ℝ) (V : Position → ℝ) (hV : ContDiff ℝ 6 V) :
    ContDiffOn ℝ 4 (fun p : ℝ × Position => moserVelocity rho V p.1 p.2)
      (moserDomain rho V) := by
  apply (contDiffOn_piLp 2).mpr
  intro a
  have hp : ContDiff ℝ 4 (dirPartial V (axis a)) :=
    ((hV.fderiv_right (show (4 : WithTop ℕ∞) + 1 ≤ 6 by norm_num)).clm_apply contDiff_const)
  have hden : ContDiffOn ℝ 4
      (fun p : ℝ × Position => 4 * Real.pi * homotopyDensity rho V p.1 p.2)
      (moserDomain rho V) :=
    (contDiff_const.mul (homotopyDensity_joint_C4 rho V hV)).contDiffOn
  exact (hp.comp contDiff_snd).neg.contDiffOn.div hden (fun p hp =>
    mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hp)

theorem moserDomain_contains_time_slab {rho : ℝ} (hrho : 0 < rho)
    (V : Position → ℝ) (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2) :
    Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set Position) ⊆ moserDomain rho V := by
  intro p hp
  exact (homotopyDensity_pos hrho V hbound hp.1.1 hp.1.2 p.2).ne'

/-- Actual spatial C⁴ regularity at each transport time, sufficient for
four differentiated flow equations and fourth-order cubature composition. -/
theorem moserVelocity_C4 {rho : ℝ} (hrho : 0 < rho)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : ContDiff ℝ 4 (moserVelocity rho V t) := by
  apply (contDiff_piLp 2).mpr
  intro a
  have hp : ContDiff ℝ 4 (dirPartial V (axis a)) :=
    ((hV.fderiv_right (show (4 : WithTop ℕ∞) + 1 ≤ 6 by norm_num)).clm_apply contDiff_const)
  have hdensity : ContDiff ℝ 4 (homotopyDensity rho V t) :=
    contDiff_const.add (contDiff_const.mul (manufacturedCharge_C4 V hV))
  exact hp.neg.div (contDiff_const.mul hdensity) (fun x =>
    mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      (homotopyDensity_pos hrho V hbound ht0 ht1 x).ne')

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_MoserBounds
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform boundedness and spatial Lipschitz regularity of the actual Moser
field on the complete transport interval. Compact support is used only to
obtain finite constants; quantitative cubature constants are a separate step. -/

noncomputable section
open scoped Topology NNReal
namespace ContinuumCoulomb

theorem moserVelocity_joint_tsupport_subset (rho : ℝ) (V : Position → ℝ) :
    tsupport (fun p : ℝ × Position => moserVelocity rho V p.1 p.2) ⊆
      Set.univ ×ˢ tsupport V := by
  apply closure_minimal _ (isClosed_univ.prod (isClosed_tsupport V))
  intro p hp
  refine ⟨Set.mem_univ _, ?_⟩
  by_contra hx
  exact hp (moserVelocity_zero hx)

/-- Bounds are uniform over every position and all times from zero to one. -/
theorem moserVelocity_uniform_bounds {rho : ℝ} (hrho : 0 < rho)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V) (hc : HasCompactSupport V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2) :
    ∃ L K : ℝ≥0, (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖moserVelocity rho V t x‖ ≤ L) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, LipschitzWith K (moserVelocity rho V t)) ∧
      (∀ x, ContinuousOn (fun t => moserVelocity rho V t x) (Set.Icc (0 : ℝ) 1)) := by
  let F : ℝ × Position → Position := fun p => moserVelocity rho V p.1 p.2
  let S : Set (ℝ × Position) := Set.Icc (0 : ℝ) 1 ×ˢ Set.univ
  let T : Set (ℝ × Position) := Set.Icc (0 : ℝ) 1 ×ˢ tsupport V
  have hT : IsCompact T := isCompact_Icc.prod hc
  have hdom : S ⊆ moserDomain rho V := moserDomain_contains_time_slab hrho V hbound
  have hTD : T ⊆ moserDomain rho V := fun p hp => hdom ⟨hp.1, Set.mem_univ _⟩
  have hreg : ContDiffOn ℝ 4 F (moserDomain rho V) := moserVelocity_joint_C4 rho V hV
  have hopen := moserDomain_isOpen rho V hV
  have hDcont : ContinuousOn (fderiv ℝ F) (moserDomain rho V) :=
    hreg.continuousOn_fderiv_of_isOpen hopen (by norm_num)
  obtain ⟨A, hA⟩ := hT.bddAbove_image ((hreg.continuousOn.mono hTD).norm)
  obtain ⟨B, hB⟩ := hT.bddAbove_image ((hDcont.mono hTD).norm)
  let L : ℝ≥0 := ⟨max 0 A, le_max_left _ _⟩
  let K : ℝ≥0 := ⟨max 0 B, le_max_left _ _⟩
  have hnorm (p : ℝ × Position) (hp : p ∈ S) : ‖F p‖ ≤ L := by
    by_cases hx : p.2 ∈ tsupport V
    · exact (hA ⟨p, ⟨hp.1, hx⟩, rfl⟩).trans (le_max_right _ _)
    · rw [show F p = 0 from moserVelocity_zero hx, norm_zero]
      exact L.coe_nonneg
  have hderiv (p : ℝ × Position) (hp : p ∈ S) : ‖fderiv ℝ F p‖ ≤ K := by
    by_cases hx : p.2 ∈ tsupport V
    · exact (hB ⟨p, ⟨hp.1, hx⟩, rfl⟩).trans (le_max_right _ _)
    · have hn : p ∉ tsupport F := fun h => hx ((moserVelocity_joint_tsupport_subset rho V h).2)
      rw [fderiv_of_notMem_tsupport ℝ hn, norm_zero]
      exact K.coe_nonneg
  have hLip : LipschitzOnWith K F S :=
    Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun p hp => (hreg.contDiffAt (hopen.mem_nhds (hdom hp))).differentiableAt (by norm_num))
      (fun p hp => by exact_mod_cast hderiv p hp)
      ((convex_Icc (0 : ℝ) 1).prod convex_univ)
  refine ⟨L, K, fun t ht x => hnorm (t, x) ⟨ht, Set.mem_univ _⟩, ?_, ?_⟩
  · intro t ht
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [F, dist_prod_same_left] using
      hLip.dist_le_mul (t, x) (show (t, x) ∈ S from ⟨ht, Set.mem_univ _⟩)
        (t, y) (show (t, y) ∈ S from ⟨ht, Set.mem_univ _⟩)
  · intro x
    exact (hreg.continuousOn.mono hdom).comp
      (continuous_id.prodMk continuous_const).continuousOn (fun t ht => ⟨ht, Set.mem_univ _⟩)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_MoserFlow
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual integral curves of the manufactured-density field exist through
time one. The flow is stationary outside the well support. No transport map
or ODE solution is introduced as an assumed analytic input. -/

noncomputable section
open scoped Topology NNReal
namespace ContinuumCoulomb

theorem moser_trajectory_exists {rho : ℝ} (hrho : 0 < rho)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V) (hc : HasCompactSupport V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2)
    (t₀ : Set.Icc (0 : ℝ) 1) (x : Position) :
    ∃ α : ℝ → Position, α t₀ = x ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt α (moserVelocity rho V t (α t)) (Set.Icc (0 : ℝ) 1) t := by
  obtain ⟨L, K, hL, hK, ht⟩ := moserVelocity_uniform_bounds hrho V hV hc hbound
  have hf : IsPicardLindelof (moserVelocity rho V) t₀ x L 0 L K := {
    lipschitzOnWith := fun t ht => (hK t ht).lipschitzOnWith
    continuousOn := fun y _ => ht y
    norm_le := fun t ht y _ => hL t ht y
    mul_max_le := by
      have hm : max (1 - (t₀ : ℝ)) ((t₀ : ℝ) - 0) ≤ 1 :=
        max_le (by linarith [t₀.2.1]) (by linarith [t₀.2.2])
      simpa only [mul_one, NNReal.coe_zero, sub_zero] using
        mul_le_mul_of_nonneg_left hm L.coe_nonneg }
  exact hf.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

/-- Uniqueness is on the closed transport interval, including both endpoints. -/
theorem moser_trajectory_unique {rho : ℝ} (hrho : 0 < rho)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V) (hc : HasCompactSupport V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2)
    {α β : ℝ → Position}
    (hα : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt α (moserVelocity rho V t (α t)) (Set.Icc (0 : ℝ) 1) t)
    (hβ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt β (moserVelocity rho V t (β t)) (Set.Icc (0 : ℝ) 1) t)
    (hzero : α 0 = β 0) : Set.EqOn α β (Set.Icc (0 : ℝ) 1) := by
  obtain ⟨L, K, hL, hK, ht⟩ := moserVelocity_uniform_bounds hrho V hV hc hbound
  have hright (γ : ℝ → Position)
      (hγ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt γ (moserVelocity rho V t (γ t)) (Set.Icc (0 : ℝ) 1) t)
      (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
      HasDerivWithinAt γ (moserVelocity rho V t (γ t)) (Set.Ici t) t := by
    apply (hγ t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin
    apply Filter.mem_of_superset (Icc_mem_nhdsGE ht.2)
    exact Set.Icc_subset_Icc_left ht.1
  exact ODE_solution_unique_of_mem_Icc_right (s := fun _ => Set.univ)
    (fun t ht => (hK t ⟨ht.1, ht.2.le⟩).lipschitzOnWith)
    (HasDerivWithinAt.continuousOn hα) (hright α hα) (fun _ _ => Set.mem_univ _)
    (HasDerivWithinAt.continuousOn hβ) (hright β hβ) (fun _ _ => Set.mem_univ _) hzero

/-- A single family of actual trajectories, stationary outside the well,
with a uniform Lipschitz bound in time. -/
theorem moser_flow_exists {rho : ℝ} (hrho : 0 < rho)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V) (hc : HasCompactSupport V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2) :
    ∃ (G : Position → ℝ → Position) (L : ℝ≥0),
      (∀ x, G x 0 = x) ∧
      (∀ x, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt (G x) (moserVelocity rho V t (G x t)) (Set.Icc (0 : ℝ) 1) t) ∧
      (∀ x, LipschitzOnWith L (G x) (Set.Icc (0 : ℝ) 1)) ∧
      (∀ x, x ∉ tsupport V → ∀ t ∈ Set.Icc (0 : ℝ) 1, G x t = x) := by
  have hex (x : Position) := moser_trajectory_exists hrho V hV hc hbound
    ⟨0, by constructor <;> norm_num⟩ x
  choose G hG0 hG using hex
  obtain ⟨L, K, hL, hK, ht⟩ := moserVelocity_uniform_bounds hrho V hV hc hbound
  refine ⟨G, L, hG0, hG, ?_, ?_⟩
  · intro x
    exact (convex_Icc (0 : ℝ) 1).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (hG x) (fun t ht => by exact_mod_cast hL t ht (G x t))
  · intro x hx t ht
    have hconst (s : ℝ) (_hs : s ∈ Set.Icc (0 : ℝ) 1) :
        HasDerivWithinAt (fun _ : ℝ => x) (moserVelocity rho V s x)
          (Set.Icc (0 : ℝ) 1) s := by
      rw [moserVelocity_zero hx]
      exact hasDerivWithinAt_const s _ x
    exact moser_trajectory_unique hrho V hV hc hbound (hG x) hconst (hG0 x) ht

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_MoserEndpoint
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual time-one map is a bijection of physical space. This follows
from forward uniqueness and trajectories with terminal data, rather than
from assuming that the continuity equation already produces a diffeomorphism. -/

noncomputable section
open scoped Topology NNReal
namespace ContinuumCoulomb

theorem moser_trajectory_unique_terminal {rho : ℝ} (hrho : 0 < rho)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V) (hc : HasCompactSupport V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2)
    {α β : ℝ → Position}
    (hα : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt α (moserVelocity rho V t (α t)) (Set.Icc (0 : ℝ) 1) t)
    (hβ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt β (moserVelocity rho V t (β t)) (Set.Icc (0 : ℝ) 1) t)
    (hone : α 1 = β 1) : Set.EqOn α β (Set.Icc (0 : ℝ) 1) := by
  obtain ⟨L, K, hL, hK, ht⟩ := moserVelocity_uniform_bounds hrho V hV hc hbound
  have hleft (γ : ℝ → Position)
      (hγ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt γ (moserVelocity rho V t (γ t)) (Set.Icc (0 : ℝ) 1) t)
      (t : ℝ) (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
      HasDerivWithinAt γ (moserVelocity rho V t (γ t)) (Set.Iic t) t := by
    apply (hγ t ⟨ht.1.le, ht.2⟩).mono_of_mem_nhdsWithin
    apply Filter.mem_of_superset (Icc_mem_nhdsLE ht.1)
    exact Set.Icc_subset_Icc_right ht.2
  exact ODE_solution_unique_of_mem_Icc_left (s := fun _ => Set.univ)
    (fun t ht => (hK t ⟨ht.1.le, ht.2⟩).lipschitzOnWith)
    (HasDerivWithinAt.continuousOn hα) (hleft α hα) (fun _ _ => Set.mem_univ _)
    (HasDerivWithinAt.continuousOn hβ) (hleft β hβ) (fun _ _ => Set.mem_univ _) hone

/-- The usual exponential spatial-dependence bound for these actual curves. -/
theorem moser_trajectory_spatial_bound {rho : ℝ} (hrho : 0 < rho)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V) (hc : HasCompactSupport V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2) :
    ∃ K : ℝ≥0, ∀ (α β : ℝ → Position),
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt α (moserVelocity rho V t (α t)) (Set.Icc (0 : ℝ) 1) t) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt β (moserVelocity rho V t (β t)) (Set.Icc (0 : ℝ) 1) t) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        dist (α t) (β t) ≤ dist (α 0) (β 0) * Real.exp ((K : ℝ) * t) := by
  obtain ⟨L, K, hL, hK, ht⟩ := moserVelocity_uniform_bounds hrho V hV hc hbound
  refine ⟨K, fun α β hα hβ t ht => ?_⟩
  have hright (γ : ℝ → Position)
      (hγ : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt γ (moserVelocity rho V s (γ s)) (Set.Icc (0 : ℝ) 1) s)
      (s : ℝ) (hs : s ∈ Set.Ico (0 : ℝ) 1) :
      HasDerivWithinAt γ (moserVelocity rho V s (γ s)) (Set.Ici s) s := by
    apply (hγ s ⟨hs.1, hs.2.le⟩).mono_of_mem_nhdsWithin
    apply Filter.mem_of_superset (Icc_mem_nhdsGE hs.2)
    exact Set.Icc_subset_Icc_left hs.1
  simpa only [sub_zero] using
    dist_le_of_trajectories_ODE_of_mem (s := fun _ => Set.univ)
      (fun s hs => (hK s ⟨hs.1, hs.2.le⟩).lipschitzOnWith)
      (HasDerivWithinAt.continuousOn hα) (hright α hα) (fun _ _ => Set.mem_univ _)
      (HasDerivWithinAt.continuousOn hβ) (hright β hβ) (fun _ _ => Set.mem_univ _)
      (le_refl (dist (α 0) (β 0))) t ht

/-- The generated time-one map is globally Lipschitz, bijective, and fixes
the complement of the compact well support. -/
theorem moser_time_one_exists {rho : ℝ} (hrho : 0 < rho)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V) (hc : HasCompactSupport V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2) :
    ∃ G : Position → ℝ → Position,
      (∀ x, G x 0 = x) ∧
      (∀ x, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt (G x) (moserVelocity rho V t (G x t)) (Set.Icc (0 : ℝ) 1) t) ∧
      Function.Bijective (fun x => G x 1) ∧
      (∃ C : ℝ≥0, LipschitzWith C (fun x => G x 1)) ∧
      (∀ x, x ∉ tsupport V → G x 1 = x) := by
  obtain ⟨G, L, hG0, hG, hGt, hfix⟩ := moser_flow_exists hrho V hV hc hbound
  have h01 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h11 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  refine ⟨G, hG0, hG, ⟨?_, ?_⟩, ?_, fun x hx => hfix x hx 1 h11⟩
  · intro x y hxy
    have h := moser_trajectory_unique_terminal hrho V hV hc hbound (hG x) (hG y) hxy h01
    simpa only [hG0] using h
  · intro y
    obtain ⟨β, hβ1, hβ⟩ := moser_trajectory_exists hrho V hV hc hbound ⟨1, h11⟩ y
    refine ⟨β 0, ?_⟩
    have h := moser_trajectory_unique hrho V hV hc hbound (hG (β 0)) hβ (hG0 (β 0)) h11
    exact h.trans hβ1
  · obtain ⟨K, hK⟩ := moser_trajectory_spatial_bound hrho V hV hc hbound
    refine ⟨⟨Real.exp (K : ℝ), (Real.exp_pos _).le⟩, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    change dist (G x 1) (G y 1) ≤ Real.exp (K : ℝ) * dist x y
    simpa only [hG0, mul_one, mul_comm] using hK (G x) (G y) (hG x) (hG y) 1 h11

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_MoserInverse
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Backward stability gives the separation bound required for mapped
quadrature nodes. Compactly supported motion also preserves the enclosing slab. -/

noncomputable section
open scoped Topology NNReal
namespace ContinuumCoulomb

theorem moser_trajectory_backward_bound {rho : ℝ} (hrho : 0 < rho)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V) (hc : HasCompactSupport V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2) :
    ∃ K : ℝ≥0, ∀ (α β : ℝ → Position),
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt α (moserVelocity rho V t (α t)) (Set.Icc (0 : ℝ) 1) t) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt β (moserVelocity rho V t (β t)) (Set.Icc (0 : ℝ) 1) t) →
      dist (α 0) (β 0) ≤ Real.exp (K : ℝ) * dist (α 1) (β 1) := by
  obtain ⟨L, K, hL, hK, ht⟩ := moserVelocity_uniform_bounds hrho V hV hc hbound
  refine ⟨K, fun α β hα hβ => ?_⟩
  let v : ℝ → Position → Position := fun s x => -(moserVelocity rho V (-s) x)
  have hmap : Set.MapsTo (Neg.neg : ℝ → ℝ) (Set.Icc (-1 : ℝ) 0) (Set.Icc (0 : ℝ) 1) := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  have hd (γ : ℝ → Position)
      (hγ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt γ (moserVelocity rho V t (γ t)) (Set.Icc (0 : ℝ) 1) t)
      (s : ℝ) (hs : s ∈ Set.Ico (-1 : ℝ) 0) :
      HasDerivWithinAt (γ ∘ Neg.neg) (v s ((γ ∘ Neg.neg) s)) (Set.Ici s) s := by
    have hmem : -s ∈ Set.Ioc (0 : ℝ) 1 := by constructor <;> linarith [hs.1, hs.2]
    have hdγ : HasDerivWithinAt γ (moserVelocity rho V (-s) (γ (-s))) (Set.Iic (-s)) (-s) := by
      apply (hγ (-s) ⟨hmem.1.le, hmem.2⟩).mono_of_mem_nhdsWithin
      apply Filter.mem_of_superset (Icc_mem_nhdsLE hmem.1)
      exact Set.Icc_subset_Icc_right hmem.2
    have hm : Set.MapsTo (Neg.neg : ℝ → ℝ) (Set.Ici s) (Set.Iic (-s)) :=
      fun _ ht => neg_le_neg (Set.mem_Ici.mp ht)
    convert! HasFDerivWithinAt.comp_hasDerivWithinAt s hdγ
      (hasDerivAt_neg s).hasDerivWithinAt hm using 1
    all_goals try with_reducible_and_instances rfl
    simp [v]
  have hv (s : ℝ) (hs : s ∈ Set.Ico (-1 : ℝ) 0) :
      LipschitzOnWith K (v s) (Set.univ : Set Position) := by
    have hm : -s ∈ Set.Icc (0 : ℝ) 1 := hmap ⟨hs.1, hs.2.le⟩
    exact (hK (-s) hm).neg.lipschitzOnWith
  have h := dist_le_of_trajectories_ODE_of_mem (v := v) (s := fun _ => Set.univ) hv
    ((HasDerivWithinAt.continuousOn hα).comp continuous_neg.continuousOn hmap)
    (hd α hα) (fun _ _ => Set.mem_univ _)
    ((HasDerivWithinAt.continuousOn hβ).comp continuous_neg.continuousOn hmap)
    (hd β hβ) (fun _ _ => Set.mem_univ _)
    (le_refl (dist ((α ∘ Neg.neg) (-1)) ((β ∘ Neg.neg) (-1))))
    0 (show (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 0 by constructor <;> norm_num)
  simpa only [Function.comp_apply, neg_zero, neg_neg, sub_neg_eq_add, zero_add, mul_one,
    mul_comm] using h

/-- Both Lipschitz bounds refer to the actual map generated by the ODE. -/
theorem moser_bilipschitz_time_one_exists {rho : ℝ} (hrho : 0 < rho)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V) (hc : HasCompactSupport V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2) :
    ∃ (G : Position → ℝ → Position) (C Cinv : ℝ≥0),
      (∀ x, G x 0 = x) ∧
      (∀ x, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt (G x) (moserVelocity rho V t (G x t)) (Set.Icc (0 : ℝ) 1) t) ∧
      Function.Bijective (fun x => G x 1) ∧
      LipschitzWith C (fun x => G x 1) ∧
      AntilipschitzWith Cinv (fun x => G x 1) ∧
      (∀ x, x ∉ tsupport V → G x 1 = x) := by
  obtain ⟨G, hG0, hG, hbij, ⟨C, hC⟩, hfix⟩ := moser_time_one_exists hrho V hV hc hbound
  obtain ⟨K, hK⟩ := moser_trajectory_backward_bound hrho V hV hc hbound
  refine ⟨G, C, ⟨Real.exp (K : ℝ), (Real.exp_pos _).le⟩,
    hG0, hG, hbij, hC, AntilipschitzWith.of_le_mul_dist ?_, hfix⟩
  intro x y
  change dist x y ≤ Real.exp (K : ℝ) * dist (G x 1) (G y 1)
  simpa only [hG0] using hK (G x) (G y) (hG x) (hG y)

theorem moser_time_one_preserves_slab (V : Position → ℝ) {H S : ℝ}
    (hsupport : tsupport V ⊆ slabDomain H S) (G : Position → Position)
    (hbij : Function.Bijective G) (hfix : ∀ x, x ∉ tsupport V → G x = x) :
    G '' slabDomain H S = slabDomain H S := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    by_contra hy
    have hn : G x ∉ tsupport V := fun h => hy (hsupport h)
    have heq : x = G x := hbij.1 (hfix (G x) hn).symm
    exact hy (heq ▸ hx)
  · intro y hy
    obtain ⟨x, rfl⟩ := hbij.2 y
    refine ⟨x, ?_, rfl⟩
    by_contra hx
    have hn : x ∉ tsupport V := fun h => hx (hsupport h)
    exact hx ((hfix x hn) ▸ hy)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_NuclearCutoff
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.Coulomb.complexWindow_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One fixed smooth cutoff supplies all translated and scaled near-nucleus
Hardy estimates; its constants are independent of the mesh and particle count. -/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace ContinuumCoulomb

theorem nuclearBump_derivative_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x, ‖fderiv ℝ (nuclearBump : Position → ℝ) x‖ ≤ C := by
  have hβ : ContDiff ℝ ∞ (nuclearBump : Position → ℝ) := nuclearBump.contDiff
  have hc := ((nuclearBump.hasCompactSupport.fderiv ℝ).isCompact_range
    (hβ.continuous_fderiv (by simp))).exists_bound_of_continuousOn
      (f := fun z => z) continuous_id.continuousOn
  obtain ⟨C,hC⟩ := hc
  exact ⟨max C 1,le_max_right _ _,fun x => (hC _ ⟨x,rfl⟩).trans (le_max_left _ _)⟩

theorem nuclearCutoff_contDiff {n : ℕ} (r : ℝ) (a : Position) (i : Fin n) :
    ContDiff ℝ ∞ (nuclearCutoff r a i) :=
  nuclearBump.contDiff.comp (((Coulomb.positionCLM i).contDiff.sub contDiff_const).const_smul r⁻¹)

theorem nuclearCutoff_abs_le_one {n : ℕ} (r : ℝ) (a : Position) (i : Fin n) (x : Configuration n) :
    |nuclearCutoff r a i x| ≤ 1 := by
  unfold nuclearCutoff
  rw [abs_of_nonneg nuclearBump.nonneg]
  exact nuclearBump.le_one

theorem nuclearCutoff_fderiv {n : ℕ} (r : ℝ) (a : Position) (i : Fin n) (x : Configuration n) :
    fderiv ℝ (nuclearCutoff r a i) x =
      (fderiv ℝ (nuclearBump : Position → ℝ) (r⁻¹ • (Coulomb.position x i-a))).comp
        (r⁻¹ • Coulomb.positionCLM i) := by
  have hβ : ContDiff ℝ ∞ (nuclearBump : Position → ℝ) := nuclearBump.contDiff
  exact ((hβ.differentiable (by simp) _).hasFDerivAt.comp x
    (((Coulomb.positionCLM i).hasFDerivAt.sub_const a).const_smul r⁻¹)).fderiv

theorem nuclearCutoff_partial_bound {C r : ℝ} (hC : ∀ x, ‖fderiv ℝ (nuclearBump : Position → ℝ) x‖ ≤ C)
    (hr : 0 < r) {n : ℕ} (a : Position) (i : Fin n) (j : Fin n × Fin 3) (x : Configuration n) :
    |fderiv ℝ (nuclearCutoff r a i) x (EuclideanSpace.single j 1)| ≤ C/r := by
  rw [nuclearCutoff_fderiv,ContinuousLinearMap.comp_apply,smul_apply,
    map_smul,smul_eq_mul,abs_mul,abs_of_pos (inv_pos.mpr hr)]
  have hv : ‖Coulomb.positionCLM i (EuclideanSpace.single j 1)‖ ≤ 1 := by
    rcases j with ⟨j,k⟩
    rw [Coulomb.positionCLM_single]
    split_ifs <;> simp [PiLp.norm_single]
  have h := (fderiv ℝ (nuclearBump : Position → ℝ) (r⁻¹ • (Coulomb.position x i-a))).le_opNorm
    (Coulomb.positionCLM i (EuclideanSpace.single j 1))
  rw [Real.norm_eq_abs] at h
  calc
    _ ≤ r⁻¹*(‖fderiv ℝ (nuclearBump : Position → ℝ) (r⁻¹ • (Coulomb.position x i-a))‖*1) :=
      mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_left hv (norm_nonneg _))) (inv_pos.mpr hr).le
    _ ≤ r⁻¹*C := by gcongr; simpa only [mul_one] using hC _
    _ = _ := by ring

theorem nuclearCutoff_one {n : ℕ} {r : ℝ} (hr : 0 < r) (a : Position) (i : Fin n)
    (x : Configuration n) (hx : ‖Coulomb.position x i-a‖ ≤ r) : nuclearCutoff r a i x = 1 := by
  apply nuclearBump.one_of_mem_closedBall
  change ‖r⁻¹ • (Coulomb.position x i-a)-0‖ ≤ 1
  rw [sub_zero,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
  have h := mul_le_mul_of_nonneg_left hx (inv_pos.mpr hr).le
  simpa only [inv_mul_cancel₀ hr.ne'] using h

theorem nuclearCutoff_outside {n : ℕ} {r : ℝ} (hr : 0 < r) (a : Position) (i : Fin n)
    (x : Configuration n) (hx : 2*r < ‖Coulomb.position x i-a‖) :
    nuclearCutoff r a i x = 0 ∧ fderiv ℝ (nuclearCutoff r a i) x = 0 := by
  have hs : 2 < ‖r⁻¹ • (Coulomb.position x i-a)‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr),mul_comm,← div_eq_mul_inv]
    exact (lt_div_iff₀ hr).mpr hx
  constructor
  · apply nuclearBump.zero_of_le_dist
    simpa only [dist_zero_right,nuclearBump] using hs.le
  · rw [nuclearCutoff_fderiv]
    have hnot : r⁻¹ • (Coulomb.position x i-a) ∉ tsupport (nuclearBump : Position → ℝ) := by
      rw [nuclearBump.tsupport_eq,Metric.mem_closedBall,dist_zero_right]
      exact not_le.mpr hs
    rw [fderiv_of_notMem_tsupport ℝ hnot]
    rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_NuclearNearEstimate
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.Coulomb.complexWindow_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The singular near-node term has a localized form bound uniform over all
weak-H1 states. No smoothness of the state or orbital restriction is imposed. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem electronBall_measurable {n : ℕ} (i : Fin n) (a : Position) (r : ℝ) :
    MeasurableSet (electronBall i a r) :=
  isClosed_le (((Coulomb.positionCLM i).continuous.sub continuous_const).norm)
    continuous_const |>.measurableSet

theorem nuclear_near_form_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (n : ℕ) (u : Coulomb.H1Vector n)
      (s : SpinConfiguration n) (i : Fin n) (a : Position) (r : ℝ), 0 < r →
      (∫ x in electronBall i a r,
        Coulomb.coulombKernel (Coulomb.position x i-a)*‖u.value s x‖^2) ≤
      (24*C^2/r)*(∫ x in electronBall i a (2*r), ‖u.value s x‖^2)+
        8*r*(∑ k : Fin 3, ∫ x in electronBall i a (2*r), ‖u.gradient s (i,k) x‖^2) := by
  obtain ⟨C,hC,hder⟩ := nuclearBump_derivative_bound
  refine ⟨C,hC,fun n u s i a r hr => ?_⟩
  have hzero (x : Configuration n) (hx : x ∉ electronBall i a (2*r)) :
      nuclearCutoff r a i x = 0 ∧ fderiv ℝ (nuclearCutoff r a i) x = 0 :=
    nuclearCutoff_outside hr a i x (lt_of_not_ge hx)
  have hb := localized_nuclear_hardy u s i a hr (nuclearCutoff r a i)
    (nuclearCutoff_contDiff r a i) (nuclearCutoff_abs_le_one r a i)
    (nuclearCutoff_partial_bound hder hr a i) (electronBall i a r) (electronBall i a (2*r))
    (electronBall_measurable i a r) (electronBall_measurable i a (2*r))
    (fun _ hx => hx) (fun x hx => nuclearCutoff_one hr a i x hx)
    (fun x hx => (hzero x hx).1)
    (fun k x hx => by rw [(hzero x hx).2]; rfl)
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  field_simp

theorem nuclear_near_sum_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (m n : ℕ) (u : Coulomb.H1Vector n)
      (s : SpinConfiguration n) (i : Fin n) (R : Fin m → Position) (r M : ℝ), 0 < r →
      (∀ x : Configuration n, (∑ a, if x ∈ electronBall i (R a) (2*r) then (1:ℝ) else 0) ≤ M) →
      (∑ a, ∫ x in electronBall i (R a) r,
        Coulomb.coulombKernel (Coulomb.position x i-R a)*‖u.value s x‖^2) ≤
      M*((24*C^2/r)*(∫ x, ‖u.value s x‖^2)+
        8*r*(∑ k : Fin 3, ∫ x, ‖u.gradient s (i,k) x‖^2)) := by
  obtain ⟨C,hC,hnear⟩ := nuclear_near_form_bound
  refine ⟨C,hC,fun m n u s i R r M hr hoverlap => ?_⟩
  have hm := finite_overlap_integral (fun a => electronBall i (R a) (2*r))
    (fun a => electronBall_measurable i (R a) (2*r)) (fun x => ‖u.value s x‖^2)
    ((u.value_L2 s).integrable_norm_pow (p := 2) (by decide)) (fun _ => sq_nonneg _) M hoverlap
  have hg (k : Fin 3) := finite_overlap_integral (fun a => electronBall i (R a) (2*r))
    (fun a => electronBall_measurable i (R a) (2*r)) (fun x => ‖u.gradient s (i,k) x‖^2)
    ((u.partial_L2 s (i,k)).integrable_norm_pow (p := 2) (by decide)) (fun _ => sq_nonneg _) M hoverlap
  have hgall := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 3))) => hg k)
  simp only [← Finset.mul_sum] at hgall
  have hs := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin m))) =>
    hnear n u s i (R a) r hr)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hs
  apply hs.trans
  rw [Finset.sum_comm]
  calc
    _ ≤ (24*C^2/r)*(M*∫ x, ‖u.value s x‖^2)+
        8*r*(M*∑ k : Fin 3, ∫ x, ‖u.gradient s (i,k) x‖^2) :=
      add_le_add (mul_le_mul_of_nonneg_left hm (by positivity))
        (mul_le_mul_of_nonneg_left hgall (by positivity))
    _ = _ := by ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_NuclearPacking
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded overlap needed by the near-node form estimate follows from
separation of the actual nuclear positions, by disjoint small balls. -/

noncomputable section
open MeasureTheory Metric
open scoped BigOperators Classical ENNReal
namespace ContinuumCoulomb

theorem separated_position_card_bound {ι : Type*} [Fintype ι]
    (R : ι → Position) (y : Position) {d L : ℝ} (hd : 0 < d) (hL : 0 ≤ L)
    (hsep : ∀ i j, i ≠ j → d ≤ ‖R i-R j‖)
    (hball : ∀ i, ‖R i-y‖ ≤ L) :
    (Fintype.card ι : ℝ)*d^3 ≤ (2*L+d)^3 := by
  let δ := d/2
  let ρ := L+δ
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hρ : 0 < ρ := add_pos_of_nonneg_of_pos hL hδ
  have hdisj : Pairwise (fun i j => Disjoint (ball (R i) δ) (ball (R j) δ)) := by
    intro i j hij
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    calc
      δ+δ = d := by dsimp [δ]; ring
      _ ≤ _ := hsep i j hij
  have hsub : (⋃ i, ball (R i) δ) ⊆ ball y ρ := by
    apply Set.iUnion_subset
    intro i
    apply ball_subset_ball'
    rw [dist_eq_norm]
    dsimp only [ρ]
    linarith only [hball i]
  have hv : (Fintype.card ι : ℝ≥0∞)*ENNReal.ofReal (δ^3)*volume (ball (0:Position) 1) ≤
      ENNReal.ofReal (ρ^3)*volume (ball (0:Position) 1) := by
    calc
      _ = volume (⋃ i, ball (R i) δ) := by
        rw [measure_iUnion hdisj (fun _ => measurableSet_ball)]
        simp only [tsum_fintype,volume.addHaar_ball_of_pos _ hδ,
          finrank_euclideanSpace_fin,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc]
      _ ≤ volume (ball y ρ) := measure_mono hsub
      _ = _ := by
        simpa only [finrank_euclideanSpace_fin] using volume.addHaar_ball_of_pos y hρ
  have hj : (Fintype.card ι : ℝ≥0∞)*ENNReal.ofReal (δ^3) ≤ ENNReal.ofReal (ρ^3) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos volume (0:Position) zero_lt_one).ne'
      measure_ball_lt_top.ne).mp hv
  have hr := ENNReal.toReal_le_of_le_ofReal (pow_nonneg hρ.le 3) hj
  simp only [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_ofReal (pow_nonneg hδ.le 3)] at hr
  calc
    _ = 8*((Fintype.card ι:ℝ)*δ^3) := by dsimp [δ]; ring
    _ ≤ 8*ρ^3 := mul_le_mul_of_nonneg_left hr (by norm_num)
    _ = _ := by dsimp [ρ,δ]; ring

theorem separated_ball_overlap {m : ℕ} (R : Fin m → Position) (y : Position)
    {d L : ℝ} (hd : 0 < d) (hL : 0 ≤ L)
    (hsep : ∀ i j, i ≠ j → d ≤ ‖R i-R j‖) :
    ((Finset.univ.filter (fun i => ‖R i-y‖ ≤ L)).card : ℝ)*d^3 ≤ (2*L+d)^3 := by
  let s := Finset.univ.filter (fun i => ‖R i-y‖ ≤ L)
  have h := separated_position_card_bound (ι := {i // i ∈ s}) (fun i => R i.val) y hd hL
    (fun i j hij => hsep i j (fun h => hij (Subtype.ext h)))
    (fun i => (Finset.mem_filter.mp i.property).2)
  simpa only [Fintype.card_coe] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_SeparatedNuclearNear
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separation of the actual point nuclei supplies the bounded-overlap
hypothesis in the weak-H1 near-node estimate. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem separated_electron_ball_overlap {m n : ℕ} (R : Fin m → Position) (i : Fin n)
    {d L : ℝ} (hd : 0 < d) (hL : 0 ≤ L)
    (hsep : ∀ a b, a ≠ b → d ≤ ‖R a-R b‖) (x : Configuration n) :
    (∑ a, if x ∈ electronBall i (R a) L then (1:ℝ) else 0) ≤ (2*L+d)^3/d^3 := by
  have h := separated_ball_overlap R (Coulomb.position x i) hd hL hsep
  apply (le_div_iff₀ (pow_pos hd 3)).mpr
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  simp only [electronBall,Set.mem_ofPred_eq,norm_sub_rev,← Finset.sum_filter,
    Finset.sum_const,nsmul_eq_mul,mul_one]

theorem separated_nuclear_near_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (m n : ℕ) (u : Coulomb.H1Vector n)
      (s : SpinConfiguration n) (i : Fin n) (R : Fin m → Position) (r d : ℝ),
      0 < r → 0 < d → (∀ a b, a ≠ b → d ≤ ‖R a-R b‖) →
      (∑ a, ∫ x in electronBall i (R a) r,
        Coulomb.coulombKernel (Coulomb.position x i-R a)*‖u.value s x‖^2) ≤
      ((4*r+d)^3/d^3)*((24*C^2/r)*(∫ x, ‖u.value s x‖^2)+
        8*r*(∑ k : Fin 3, ∫ x, ‖u.gradient s (i,k) x‖^2)) := by
  obtain ⟨C,hC,hbound⟩ := nuclear_near_sum_bound
  refine ⟨C,hC,fun m n u s i R r d hr hd hsep => ?_⟩
  have hb := hbound m n u s i R r ((2*(2*r)+d)^3/d^3) hr
    (separated_electron_ball_overlap R i hd (by positivity) hsep)
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ScaledNuclearNear
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.Coulomb.complexWindow_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Equal-mass near-node errors have the required square-mesh scaling.
The constant depends on the separation and near-ball ratios, not on the
number of nuclei or the size of the box. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem scaled_nuclear_near_bound {κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (m n : ℕ) (u : Coulomb.H1Vector n)
      (s : SpinConfiguration n) (i : Fin n) (R : Fin m → Position) (h ρ : ℝ),
      0 < h → h ≤ 1 → 0 ≤ ρ →
      (∀ a b, a ≠ b → σ*h ≤ ‖R a-R b‖) →
      (ρ*h^3/8)*(∑ a, ∫ x in electronBall i (R a) (κ*h),
        Coulomb.coulombKernel (Coulomb.position x i-R a)*‖u.value s x‖^2) ≤
      ρ*A*h^2*((∫ x, ‖u.value s x‖^2)+
        ∑ k : Fin 3, ∫ x, ‖u.gradient s (i,k) x‖^2) := by
  obtain ⟨C,hC,hbound⟩ := separated_nuclear_near_bound
  let M : ℝ := (4*κ+σ)^3/σ^3
  let B : ℝ := max (24*C^2/κ) (8*κ)
  let A : ℝ := max 1 (M/8*B)
  refine ⟨A,le_max_left _ _,fun m n u s i R h ρ hh hh1 hρ hsep => ?_⟩
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hB : 0 ≤ B := (by positivity : 0 ≤ 24*C^2/κ).trans (le_max_left _ _)
  have hmass : 0 ≤ ∫ x, ‖u.value s x‖^2 := integral_nonneg (fun _ => sq_nonneg _)
  have hgrad : 0 ≤ ∑ k : Fin 3, ∫ x, ‖u.gradient s (i,k) x‖^2 :=
    Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
  have hh2 : h^2 ≤ 1 := by nlinarith
  have he := hbound m n u s i R (κ*h) (σ*h) (mul_pos hκ hh) (mul_pos hσ hh) hsep
  have hr : (4*(κ*h)+σ*h)^3/(σ*h)^3 = M := by
    dsimp [M]
    field_simp [hσ.ne',hh.ne']
  rw [hr] at he
  have hb : (24*C^2/κ)*(∫ x, ‖u.value s x‖^2)+
      8*κ*h^2*(∑ k : Fin 3, ∫ x, ‖u.gradient s (i,k) x‖^2) ≤
      B*((∫ x, ‖u.value s x‖^2)+∑ k : Fin 3, ∫ x, ‖u.gradient s (i,k) x‖^2) := by
    rw [mul_add]
    apply add_le_add
    · exact mul_le_mul_of_nonneg_right (le_max_left _ _) hmass
    · apply mul_le_mul_of_nonneg_right _ hgrad
      exact (mul_le_mul_of_nonneg_left hh2 (by positivity : 0 ≤ 8*κ)).trans
        (by simpa only [mul_one] using (le_max_right (24*C^2/κ) (8*κ)))
  calc
    _ ≤ (ρ*h^3/8)*(M*((24*C^2/(κ*h))*(∫ x, ‖u.value s x‖^2)+
        8*(κ*h)*(∑ k : Fin 3, ∫ x, ‖u.gradient s (i,k) x‖^2))) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = (ρ*h^2)*(M/8)*((24*C^2/κ)*(∫ x, ‖u.value s x‖^2)+
        8*κ*h^2*(∑ k : Fin 3, ∫ x, ‖u.gradient s (i,k) x‖^2)) := by
      field_simp [hκ.ne',hh.ne']
    _ ≤ (ρ*h^2)*(M/8)*(B*((∫ x, ‖u.value s x‖^2)+
        ∑ k : Fin 3, ∫ x, ‖u.gradient s (i,k) x‖^2)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ ρ*A*h^2*((∫ x, ‖u.value s x‖^2)+
        ∑ k : Fin 3, ∫ x, ‖u.gradient s (i,k) x‖^2) := by
      have ha : M/8*B ≤ A := le_max_right _ _
      nlinarith [mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right ha (add_nonneg hmass hgrad))
        (show 0 ≤ ρ*h^2 by positivity)]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_TransportedNearForm
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual transported Gauss nuclei satisfy the separation hypothesis
in the full weak-H1 near-field bound, uniformly over the chosen finite grid. -/

noncomputable section
open MeasureTheory
open scoped BigOperators NNReal
namespace ContinuumCoulomb

theorem transportedGauss_separation {m : ℕ} {h : ℝ} (hh : 0 < h)
    (index : Fin m → GaussLatticeIndex) (hindex : Function.Injective index)
    (G : Position → Position) {K : ℝ≥0} (hK : 0 < K) (hG : AntilipschitzWith K G)
    (a b : Fin m) (hab : a ≠ b) :
    h/(3*(K:ℝ)) ≤ ‖G (gaussLatticePoint h (index a))-G (gaussLatticePoint h (index b))‖ := by
  have hb := gaussLatticePoint_separation hh (index a) (index b) (fun he => hab (hindex he))
  have ht := hG.le_mul_dist (gaussLatticePoint h (index a)) (gaussLatticePoint h (index b))
  simp only [dist_eq_norm] at ht
  apply (div_le_iff₀ (show 0 < 3*(K:ℝ) by positivity)).mpr
  nlinarith

theorem transportedGauss_near_form {κ : ℝ} (hκ : 0 < κ)
    (K : ℝ≥0) (hK : 0 < K) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (m n : ℕ) (u : Coulomb.H1Vector n)
      (s : SpinConfiguration n) (i : Fin n) (h ρ : ℝ),
      0 < h → h ≤ 1 → 0 ≤ ρ →
      ∀ (index : Fin m → GaussLatticeIndex), Function.Injective index →
      ∀ (G : Position → Position), AntilipschitzWith K G →
      (ρ*h^3/8)*(∑ a, ∫ x in electronBall i (G (gaussLatticePoint h (index a))) (κ*h),
        Coulomb.coulombKernel (Coulomb.position x i-G (gaussLatticePoint h (index a)))*
          ‖u.value s x‖^2) ≤
      ρ*A*h^2*((∫ x, ‖u.value s x‖^2)+
        ∑ k : Fin 3, ∫ x, ‖u.gradient s (i,k) x‖^2) := by
  have hσ : 0 < 1/(3*(K:ℝ)) := by positivity
  obtain ⟨A,hA,hbound⟩ := scaled_nuclear_near_bound hκ hσ
  refine ⟨A,hA,fun m n u s i h ρ hh hh1 hρ index hindex G hG => ?_⟩
  apply hbound m n u s i (fun a => G (gaussLatticePoint h (index a))) h ρ hh hh1 hρ
  intro a b hab
  have he := transportedGauss_separation hh index hindex G hK hG a b hab
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_TruncatedNuclearForm
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.Coulomb.complexWindow_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The truncated point kernels in the mesh error are controlled on the
entire weak-H1 domain by the separated-nucleus near-field estimate. -/

noncomputable section
open MeasureTheory
open scoped BigOperators NNReal
namespace ContinuumCoulomb

theorem truncated_nuclear_integrable_bound {n : ℕ} (u : Coulomb.H1Vector n)
    (s : SpinConfiguration n) (i : Fin n) (a : Position) (r : ℝ) :
    Integrable (fun x => Coulomb.truncatedCoulomb r (Coulomb.position x i-a)*‖u.value s x‖^2) ∧
    (∫ x, Coulomb.truncatedCoulomb r (Coulomb.position x i-a)*‖u.value s x‖^2) ≤
      ∫ x in electronBall i a r, Coulomb.coulombKernel (Coulomb.position x i-a)*‖u.value s x‖^2 := by
  have hi := (u.nuclear_coulomb_integrable_bound s i a (by norm_num : (0:ℝ) < 1)).1
  have hk (z : Position) : Coulomb.truncatedCoulomb r z ≤ Coulomb.coulombKernel z := by
    by_cases hz : z ∈ Metric.ball (0:Position) r
    · simp only [Coulomb.truncatedCoulomb,Set.indicator_of_mem hz,le_refl]
    · simpa only [Coulomb.truncatedCoulomb,Set.indicator_of_notMem hz] using
        Coulomb.coulombKernel_nonneg z
  have hm : AEStronglyMeasurable
      (fun x : Configuration n => Coulomb.truncatedCoulomb r (Coulomb.position x i-a)) volume :=
    ((Coulomb.coulombKernel_measurable.indicator measurableSet_ball).comp
    ((Coulomb.positionCLM i).continuous.sub continuous_const).measurable).aestronglyMeasurable
  have ht : Integrable (fun x =>
      Coulomb.truncatedCoulomb r (Coulomb.position x i-a)*‖u.value s x‖^2) := by
    apply hi.mono' (hm.mul ((u.value_L2 s).aestronglyMeasurable.norm.pow 2))
    exact Filter.Eventually.of_forall (fun x => by
      change ‖Coulomb.truncatedCoulomb r (Coulomb.position x i-a)*‖u.value s x‖^2‖ ≤ _
      rw [Real.norm_of_nonneg (mul_nonneg (Coulomb.truncatedCoulomb_nonneg _ _) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_right (hk _) (sq_nonneg _))
  refine ⟨ht,?_⟩
  rw [← integral_indicator (electronBall_measurable i a r)]
  apply integral_mono ht (hi.indicator (electronBall_measurable i a r))
  intro x
  by_cases hx : x ∈ electronBall i a r
  · rw [Set.indicator_of_mem hx]
    exact mul_le_mul_of_nonneg_right (hk _) (sq_nonneg _)
  · rw [Set.indicator_of_notMem hx]
    have hn : Coulomb.position x i-a ∉ Metric.ball (0:Position) r := by
      simp only [Metric.mem_ball,dist_zero_right]
      exact not_lt.mpr (le_of_lt (lt_of_not_ge hx))
    simp only [Coulomb.truncatedCoulomb,Set.indicator_of_notMem hn,zero_mul,le_refl]

theorem transportedGauss_truncated_form {κ : ℝ} (hκ : 0 < κ)
    (K : ℝ≥0) (hK : 0 < K) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {ι : Type} [Fintype ι] (n : ℕ) (u : Coulomb.H1Vector n)
      (s : SpinConfiguration n) (i : Fin n) (h ρ : ℝ),
      0 < h → h ≤ 1 → 0 ≤ ρ →
      ∀ (index : ι → GaussLatticeIndex), Function.Injective index →
      ∀ (G : Position → Position), AntilipschitzWith K G →
      (ρ*h^3/8)*(∑ a, ∫ x,
        Coulomb.truncatedCoulomb (κ*h) (Coulomb.position x i-G (gaussLatticePoint h (index a)))*
          ‖u.value s x‖^2) ≤
      ρ*A*h^2*((∫ x, ‖u.value s x‖^2)+
        ∑ k : Fin 3, ∫ x, ‖u.gradient s (i,k) x‖^2) := by
  obtain ⟨A,hA,hbound⟩ := transportedGauss_near_form hκ K hK
  refine ⟨A,hA,?_⟩
  intro ι _ n u s i h ρ hh hh1 hρ index hindex G hG
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have he := hbound (Fintype.card ι) n u s i h ρ hh hh1 hρ (index ∘ e)
    (hindex.comp e.injective) G hG
  have hs : (∑ a : ι, ∫ x in electronBall i (G (gaussLatticePoint h (index a))) (κ*h),
        Coulomb.coulombKernel (Coulomb.position x i-G (gaussLatticePoint h (index a)))*‖u.value s x‖^2) =
      ∑ a : Fin (Fintype.card ι), ∫ x in electronBall i (G (gaussLatticePoint h (index (e a)))) (κ*h),
        Coulomb.coulombKernel (Coulomb.position x i-G (gaussLatticePoint h (index (e a))))*‖u.value s x‖^2 :=
    (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
  apply le_trans _ (by simpa only [Function.comp_apply,← hs] using he)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum (fun a _ =>
    (truncated_nuclear_integrable_bound u s i (G (gaussLatticePoint h (index a))) (κ*h)).2)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_WeightedPotentialBound
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrate a pointwise potential error with explicit near-pole terms on
an arbitrary weak-H1 state. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem weighted_potential_truncated_bound {α : Type*} [Fintype α]
    {n : ℕ} (u : Coulomb.H1Vector n) (s : SpinConfiguration n) (i : Fin n)
    (F : Position → ℝ) (hF : Measurable F) (R : α → Position) (r B c : ℝ)
    (hbound : ∀ y, |F y| ≤ B+c*(∑ a, Coulomb.truncatedCoulomb r (y-R a))) :
    Integrable (fun x => F (Coulomb.position x i)*‖u.value s x‖^2) ∧
    |∫ x, F (Coulomb.position x i)*‖u.value s x‖^2| ≤
      B*(∫ x, ‖u.value s x‖^2)+c*(∑ a, ∫ x,
        Coulomb.truncatedCoulomb r (Coulomb.position x i-R a)*‖u.value s x‖^2) := by
  let T : α → Configuration n → ℝ := fun a x =>
    Coulomb.truncatedCoulomb r (Coulomb.position x i-R a)*‖u.value s x‖^2
  have hT (a : α) : Integrable (T a) := (truncated_nuclear_integrable_bound u s i (R a) r).1
  have hmass := (u.value_L2 s).integrable_norm_pow (p := 2) (by decide)
  have hdom : Integrable (fun x => B*‖u.value s x‖^2+c*(∑ a, T a x)) :=
    (hmass.const_mul B).add ((integrable_finsetSum _ (fun a _ => hT a)).const_mul c)
  have hnorm (x : Configuration n) :
      ‖F (Coulomb.position x i)*‖u.value s x‖^2‖ ≤ B*‖u.value s x‖^2+c*(∑ a, T a x) := by
    rw [norm_mul,Real.norm_eq_abs,Real.norm_of_nonneg (sq_nonneg _)]
    have hb := mul_le_mul_of_nonneg_right (hbound (Coulomb.position x i)) (sq_nonneg ‖u.value s x‖)
    apply hb.trans_eq
    simp only [add_mul,mul_assoc,Finset.sum_mul,T]
  have hI : Integrable (fun x => F (Coulomb.position x i)*‖u.value s x‖^2) :=
    hdom.mono' (((hF.comp (Coulomb.positionCLM i).continuous.measurable).aestronglyMeasurable).mul
      ((u.value_L2 s).aestronglyMeasurable.norm.pow 2)) (Filter.Eventually.of_forall hnorm)
  refine ⟨hI,?_⟩
  calc
    _ ≤ ∫ x, ‖F (Coulomb.position x i)*‖u.value s x‖^2‖ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun x => F (Coulomb.position x i)*‖u.value s x‖^2)
    _ ≤ ∫ x, B*‖u.value s x‖^2+c*(∑ a, T a x) := integral_mono hI.norm hdom hnorm
    _ = B*(∫ x, ‖u.value s x‖^2)+c*(∑ a, ∫ x, T a x) := by
      rw [integral_add (hmass.const_mul B) ((integrable_finsetSum _ (fun a _ => hT a)).const_mul c),
        integral_const_mul,integral_const_mul,integral_finsetSum _ (fun a _ => hT a)]

theorem weighted_potential_absolute_bound {α : Type*} [Fintype α]
    {n : ℕ} (u : Coulomb.H1Vector n) (s : SpinConfiguration n) (i : Fin n)
    (F : Position → ℝ) (hF : Measurable F) (R : α → Position) (r B c : ℝ)
    (hbound : ∀ y, |F y| ≤ B+c*(∑ a, Coulomb.truncatedCoulomb r (y-R a))) :
    Integrable (fun x => |F (Coulomb.position x i)| * ‖u.value s x‖^2) ∧
    (∫ x, |F (Coulomb.position x i)| * ‖u.value s x‖^2) ≤
      B*(∫ x, ‖u.value s x‖^2)+c*(∑ a, ∫ x,
        Coulomb.truncatedCoulomb r (Coulomb.position x i-R a)*‖u.value s x‖^2) := by
  have he := weighted_potential_truncated_bound u s i (fun y => |F y|) hF.abs R r B c
    (fun y => by simpa only [abs_abs] using hbound y)
  rw [abs_of_nonneg (integral_nonneg (fun x => mul_nonneg (abs_nonneg _) (sq_nonneg _)))] at he
  exact he

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_GaussTensorError
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tensorizing the one-dimensional Gauss error without differentiating a
parameter integral. This is used for the transported nuclear cubature. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem gaussTwoPoint_sub (f g : ℝ → ℝ) :
    gaussTwoPoint (fun x => f x-g x) = gaussTwoPoint f-gaussTwoPoint g := by
  unfold gaussTwoPoint
  ring

theorem gaussTwoPoint_comm (f : ℝ → ℝ → ℝ) :
    gaussTwoPoint (fun x => gaussTwoPoint (f x)) =
      gaussTwoPoint (fun y => gaussTwoPoint (fun x => f x y)) := by
  unfold gaussTwoPoint
  ring

theorem gaussTwoPoint_abs_bound (f : ℝ → ℝ) {E : ℝ}
    (h : ∀ x ∈ Set.Icc (-1) 1, |f x| ≤ E) : |gaussTwoPoint f| ≤ 2*E := by
  have hg : gaussAbscissa ≤ 1 := by nlinarith only [gaussAbscissa_sq,gaussAbscissa_pos]
  have hp := gaussAbscissa_pos.le
  have h₁ := h (-gaussAbscissa) ⟨by linarith,by linarith⟩
  have h₂ := h gaussAbscissa ⟨by linarith,hg⟩
  exact (abs_add_le _ _).trans (by linarith)

theorem gaussTwoPoint_integral_comm (f : ℝ → ℝ → ℝ)
    (hf : Continuous f.uncurry) :
    gaussTwoPoint (fun x => ∫ y : ℝ in (-1)..1, f x y) =
      ∫ y : ℝ in (-1)..1, gaussTwoPoint (fun x => f x y) := by
  have hc (x : ℝ) : Continuous (f x) := hf.comp (continuous_const.prodMk continuous_id)
  exact (intervalIntegral.integral_add (hc (-gaussAbscissa) |>.intervalIntegrable _ _)
    (hc gaussAbscissa |>.intervalIntegrable _ _)).symm

theorem gaussTwoPoint_integral_continuous {X : Type*} [TopologicalSpace X] (f : X → ℝ → ℝ)
    (hf : Continuous f.uncurry) :
    Continuous (fun x => ∫ y : ℝ in (-1)..1, f x y) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf _ _

theorem gaussTwoPoint_function_continuous {X : Type*} [TopologicalSpace X] (f : X → ℝ → ℝ)
    (hf : Continuous f.uncurry) : Continuous (fun x => gaussTwoPoint (f x)) :=
  (hf.comp (continuous_id.prodMk continuous_const)).add
    (hf.comp (continuous_id.prodMk continuous_const))

theorem interval_abs_bound {E : ℝ} (f : ℝ → ℝ)
    (h : ∀ x ∈ Set.Icc (-1) 1, |f x| ≤ E) :
    |∫ x : ℝ in (-1)..1, f x| ≤ 2*E := by
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := f) (a := (-1:ℝ)) (b := 1) (C := E) (fun x hx => by
      have hx' : -1 < x ∧ x ≤ 1 := by
        simpa only [Set.uIoc_of_le (by norm_num : (-1:ℝ) ≤ 1),Set.mem_Ioc] using hx
      simpa only [Real.norm_eq_abs] using h x ⟨hx'.1.le,hx'.2⟩)
  norm_num [Real.norm_eq_abs] at hi
  simpa only [mul_comm] using hi

theorem gaussTensor2_error (f : ℝ → ℝ → ℝ) (hf : Continuous f.uncurry) {E : ℝ}
    (hx : ∀ y ∈ Set.Icc (-1) 1,
      |gaussTwoPoint (fun x => f x y)-(∫ x : ℝ in (-1)..1, f x y)| ≤ E)
    (hy : ∀ x ∈ Set.Icc (-1) 1,
      |gaussTwoPoint (f x)-(∫ y : ℝ in (-1)..1, f x y)| ≤ E) :
    |gaussTwoPoint (fun x => gaussTwoPoint (f x))-
      (∫ x : ℝ in (-1)..1, ∫ y : ℝ in (-1)..1, f x y)| ≤ 4*E := by
  let A := gaussTwoPoint (fun x => gaussTwoPoint (f x))
  let B := ∫ x : ℝ in (-1)..1, gaussTwoPoint (f x)
  let C := ∫ x : ℝ in (-1)..1, ∫ y : ℝ in (-1)..1, f x y
  have h₁ : |A-B| ≤ 2*E := by
    have hid : A-B = gaussTwoPoint (fun y => gaussTwoPoint (fun x => f x y)-
        (∫ x : ℝ in (-1)..1, f x y)) := by
      rw [gaussTwoPoint_sub,gaussTwoPoint_comm]
      dsimp only [A,B]
      rw [gaussTwoPoint_integral_comm (fun y x => f x y)
        (hf.comp continuous_swap)]
    rw [hid]
    exact gaussTwoPoint_abs_bound _ hx
  have h₂ : |B-C| ≤ 2*E := by
    rw [show B-C = ∫ x : ℝ in (-1)..1,
      gaussTwoPoint (f x)-(∫ y : ℝ in (-1)..1, f x y) from
      (intervalIntegral.integral_sub
        ((gaussTwoPoint_function_continuous f hf).intervalIntegrable _ _)
        ((gaussTwoPoint_integral_continuous f hf).intervalIntegrable _ _)).symm]
    exact interval_abs_bound _ hy
  exact (abs_sub_le A B C).trans (by linarith only [h₁,h₂])

theorem gaussTensor3_first_comm (f : ℝ → ℝ → ℝ → ℝ) :
    gaussTwoPoint (fun x => gaussTwoPoint (fun y => gaussTwoPoint (f x y))) =
      gaussTwoPoint (fun y => gaussTwoPoint (fun z => gaussTwoPoint (fun x => f x y z))) := by
  unfold gaussTwoPoint
  ring

theorem gaussTensor2_integral_comm (f : ℝ → ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2)) :
    gaussTwoPoint (fun y => gaussTwoPoint (fun z => ∫ x : ℝ in (-1)..1, f x y z)) =
      ∫ x : ℝ in (-1)..1, gaussTwoPoint (fun y => gaussTwoPoint (f x y)) := by
  have hz (y : ℝ) : Continuous (fun p : ℝ × ℝ => f p.2 y p.1) :=
    hf.comp (show Continuous (fun p : ℝ × ℝ => (p.2,y,p.1)) by fun_prop)
  have hg : Continuous (fun p : ℝ × ℝ => gaussTwoPoint (f p.2 p.1)) := by
    unfold gaussTwoPoint
    exact (hf.comp (show Continuous (fun p : ℝ × ℝ => (p.2,p.1,-gaussAbscissa)) by fun_prop)).add
      (hf.comp (show Continuous (fun p : ℝ × ℝ => (p.2,p.1,gaussAbscissa)) by fun_prop))
  calc
    _ = gaussTwoPoint (fun y => ∫ x : ℝ in (-1)..1, gaussTwoPoint (f x y)) := by
      congr 1
      funext y
      exact gaussTwoPoint_integral_comm _ (hz y)
    _ = _ := gaussTwoPoint_integral_comm _ hg

theorem gaussTensor3_error (f : ℝ → ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2)) {E : ℝ}
    (hx : ∀ y ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1,
      |gaussTwoPoint (fun x => f x y z)-(∫ x : ℝ in (-1)..1, f x y z)| ≤ E)
    (hy : ∀ x ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1,
      |gaussTwoPoint (fun y => f x y z)-(∫ y : ℝ in (-1)..1, f x y z)| ≤ E)
    (hz : ∀ x ∈ Set.Icc (-1) 1, ∀ y ∈ Set.Icc (-1) 1,
      |gaussTwoPoint (f x y)-(∫ z : ℝ in (-1)..1, f x y z)| ≤ E) :
    |gaussTwoPoint (fun x => gaussTwoPoint (fun y => gaussTwoPoint (f x y)))-
      (∫ x : ℝ in (-1)..1, ∫ y : ℝ in (-1)..1, ∫ z : ℝ in (-1)..1, f x y z)| ≤ 12*E := by
  let A := gaussTwoPoint (fun x => gaussTwoPoint (fun y => gaussTwoPoint (f x y)))
  let B := ∫ x : ℝ in (-1)..1, gaussTwoPoint (fun y => gaussTwoPoint (f x y))
  let C := ∫ x : ℝ in (-1)..1, ∫ y : ℝ in (-1)..1, ∫ z : ℝ in (-1)..1, f x y z
  have h₁ : |A-B| ≤ 4*E := by
    have hid : A-B = gaussTwoPoint (fun y => gaussTwoPoint (fun z =>
        gaussTwoPoint (fun x => f x y z)-(∫ x : ℝ in (-1)..1, f x y z))) := by
      simp_rw [gaussTwoPoint_sub]
      rw [gaussTensor2_integral_comm f hf,← gaussTensor3_first_comm]
    rw [hid]
    have h := gaussTwoPoint_abs_bound _ (fun y hy' => gaussTwoPoint_abs_bound _ (hx y hy'))
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hg : Continuous (fun p : ℝ × ℝ => gaussTwoPoint (f p.1 p.2)) := by
    unfold gaussTwoPoint
    exact (hf.comp (show Continuous (fun p : ℝ × ℝ => (p.1,p.2,-gaussAbscissa)) by fun_prop)).add
      (hf.comp (show Continuous (fun p : ℝ × ℝ => (p.1,p.2,gaussAbscissa)) by fun_prop))
  have hI : Continuous (fun p : ℝ × ℝ => ∫ z : ℝ in (-1)..1, f p.1 p.2 z) :=
    gaussTwoPoint_integral_continuous (fun (p : ℝ × ℝ) z => f p.1 p.2 z)
      (hf.comp (show Continuous (fun p : (ℝ × ℝ) × ℝ => (p.1.1,p.1.2,p.2)) by fun_prop))
  have h₂ : |B-C| ≤ 8*E := by
    have hb := gaussTwoPoint_function_continuous (fun x y => gaussTwoPoint (f x y)) hg
    have hc := gaussTwoPoint_integral_continuous
      (fun x y => ∫ z : ℝ in (-1)..1, f x y z) hI
    rw [show B-C = ∫ x : ℝ in (-1)..1,
      gaussTwoPoint (fun y => gaussTwoPoint (f x y))-
        (∫ y : ℝ in (-1)..1, ∫ z : ℝ in (-1)..1, f x y z) from
      (intervalIntegral.integral_sub (hb.intervalIntegrable _ _) (hc.intervalIntegrable _ _)).symm]
    have h := interval_abs_bound _ (fun x hx' =>
      gaussTensor2_error (f x)
        (hf.comp (show Continuous (fun p : ℝ × ℝ => (x,p.1,p.2)) by fun_prop)) (hy x hx') (hz x hx'))
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  exact (abs_sub_le A B C).trans (by linarith only [h₁,h₂])

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombKernelSmooth
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.Coulomb.complexWindow_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothness of the actual Coulomb kernel away from its pole, with
uniform derivative bounds on the fixed annulus used in cell estimates. -/

noncomputable section
open scoped ContDiff BigOperators Classical
namespace ContinuumCoulomb

theorem coulombKernel_contDiffAt {x : Position} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ Coulomb.coulombKernel x := by
  exact (contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)

theorem coulombKernel_iteratedFDeriv_continuousAt (k : ℕ) {x : Position} (hx : x ≠ 0) :
    ContinuousAt (iteratedFDeriv ℝ k Coulomb.coulombKernel) x :=
  ((coulombKernel_contDiffAt hx).differentiableAt_iteratedFDeriv (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k)).continuousAt

theorem coulombKernel_fixed_annulus_bounds :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ k : Fin 5, ∀ x : Position, 1/2 ≤ ‖x‖ → ‖x‖ ≤ 2 →
      ‖iteratedFDeriv ℝ (k:ℕ) Coulomb.coulombKernel x‖ ≤ C := by
  let K := Metric.closedBall (0:Position) 2 \ Metric.ball 0 (1/2)
  have hK : IsCompact K := (isCompact_closedBall (0:Position) 2).diff Metric.isOpen_ball
  have hk (k : Fin 5) : ContinuousOn (iteratedFDeriv ℝ (k:ℕ) Coulomb.coulombKernel) K := by
    intro x hx
    apply (coulombKernel_iteratedFDeriv_continuousAt k ?_).continuousWithinAt
    intro he
    have hn := hx.2
    apply hn
    rw [he,Metric.mem_ball,dist_self]
    norm_num
  choose C hC using fun k : Fin 5 => hK.exists_bound_of_continuousOn (hk k)
  refine ⟨1+∑ k, |C k|,?_,fun k x hx₁ hx₂ => ?_⟩
  · exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  · have hx : x ∈ K := by
      refine ⟨?_,?_⟩
      · simpa only [Metric.mem_closedBall,dist_zero_right] using hx₂
      · simpa only [Metric.mem_ball,dist_zero_right,not_lt] using hx₁
    have hb := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 5))) =>
      abs_nonneg (C j)) (Finset.mem_univ k)
    exact (hC k x hx).trans ((le_abs_self _).trans (by linarith))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_Dilation
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Spatial dilation on the actual weak H¹ domain

The physical-energy amplification in both manuscripts changes coordinates
on the full fermionic form domain. Here weak derivatives are transformed
by changing variables in the compact-test identity, rather than assuming
pointwise differentiability of an arbitrary state.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem coulombKernel_smul (x : Position) {scale : ℝ} (hscale : 0 < scale) :
    Coulomb.coulombKernel (scale • x) = scale⁻¹ * Coulomb.coulombKernel x := by
  simp only [Coulomb.coulombKernel, norm_smul, Real.norm_eq_abs,
    abs_of_pos hscale, mul_inv_rev]
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombKernelHomogeneity
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.Coulomb.complexWindow_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Derivatives through order four of the actual inverse-distance kernel
decay by the appropriate inverse power. -/

noncomputable section
open scoped ContDiff
namespace ContinuumCoulomb

theorem coulombKernel_iteratedFDeriv_scaling (k : ℕ) {c : ℝ} (hc : 0 < c)
    {x : Position} (hx : x ≠ 0) :
    c^k*‖iteratedFDeriv ℝ k Coulomb.coulombKernel (c • x)‖ =
      c⁻¹*‖iteratedFDeriv ℝ k Coulomb.coulombKernel x‖ := by
  let e : Position ≃L[ℝ] Position := ContinuousLinearEquiv.smulLeft (Units.mk0 c hc.ne')
  have he (z : Position) : e z = c • z := rfl
  have hd := e.iteratedFDerivWithin_comp_right Coulomb.coulombKernel uniqueDiffOn_univ
    (Set.mem_univ (e x)) k
  simp only [Set.preimage_univ,iteratedFDerivWithin_univ] at hd
  have hright : iteratedFDeriv ℝ k (Coulomb.coulombKernel ∘ e) x =
      c^k • iteratedFDeriv ℝ k Coulomb.coulombKernel (c • x) := by
    rw [hd]
    ext v
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      smul_apply,ContinuousLinearEquiv.coe_coe,he]
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
      (iteratedFDeriv ℝ k Coulomb.coulombKernel (c • x)).map_smul_univ (fun _ => c) v
  have hfun : Coulomb.coulombKernel ∘ e = c⁻¹ • Coulomb.coulombKernel := by
    funext z
    exact coulombKernel_smul z hc
  rw [hfun,iteratedFDeriv_const_smul_apply
    ((coulombKernel_contDiffAt hx).of_le (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k).le : ContDiffAt ℝ k Coulomb.coulombKernel x)] at hright
  have hn := congrArg norm hright.symm
  simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos (pow_pos hc k),
    abs_of_pos (inv_pos.mpr hc)] using hn

theorem coulombKernel_derivative_decay :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ k : Fin 5, ∀ x : Position, x ≠ 0 →
      ‖iteratedFDeriv ℝ (k:ℕ) Coulomb.coulombKernel x‖*‖x‖^((k:ℕ)+1) ≤ C := by
  obtain ⟨C,hC,hbound⟩ := coulombKernel_fixed_annulus_bounds
  refine ⟨C,hC,fun k x hx => ?_⟩
  let y : Position := ‖x‖⁻¹ • x
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hy : ‖y‖ = 1 := by
    simp only [y,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn)]
    exact inv_mul_cancel₀ hn.ne'
  have hyne : y ≠ 0 := by intro he; simp only [he,norm_zero] at hy; norm_num at hy
  have hxy : ‖x‖ • y = x := by
    simp only [y,smul_smul,mul_inv_cancel₀ hn.ne',one_smul]
  have h := coulombKernel_iteratedFDeriv_scaling k hn hyne
  rw [hxy] at h
  have hb := hbound k y (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  calc
    _ = ‖x‖*(‖x‖^(k:ℕ)*‖iteratedFDeriv ℝ (k:ℕ) Coulomb.coulombKernel x‖) := by ring
    _ = ‖x‖*(‖x‖⁻¹*‖iteratedFDeriv ℝ (k:ℕ) Coulomb.coulombKernel y‖) := by rw [h]
    _ = ‖iteratedFDeriv ℝ (k:ℕ) Coulomb.coulombKernel y‖ := by
      rw [← mul_assoc,mul_inv_cancel₀ hn.ne',one_mul]
    _ ≤ C := hb

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_DirectionalFourthDerivative
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fourth derivatives along the affine coordinate lines used by cubature. -/

noncomputable section
namespace ContinuumCoulomb

/-- Local smoothness suffices; the function may be singular away from the line point. -/
theorem fourthDeriv_affine_line (f : Position → ℝ) (b v : Position) (t : ℝ)
    (hf : ContDiffAt ℝ 4 f (b+t • v)) :
    iteratedDeriv 4 (fun s : ℝ => f (b+s • v)) t =
      iteratedFDeriv ℝ 4 f (b+t • v) (fun _ => v) := by
  let L : ℝ →L[ℝ] Position := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  let g : Position → ℝ := fun z => f (b+z)
  have hg : ContDiffAt ℝ 4 g (L t) :=
    hf.comp (L t) (contDiffAt_const.add contDiffAt_id)
  obtain ⟨U,hU,ht,hgU⟩ := hg.contDiffOn' le_rfl (by norm_num)
  have hgU : ContDiffOn ℝ 4 g U := by simpa using hgU
  have hpre : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  have hgt : ContDiffAt ℝ 4 (g ∘ L) t := hg.comp t L.contDiff.contDiffAt
  have h := L.iteratedFDerivWithin_comp_right hgU hU.uniqueDiffOn hpre.uniqueDiffOn ht
    (i := 4) le_rfl
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hpre.uniqueDiffOn hgt ht,
    iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn hg ht] at h
  change iteratedFDeriv ℝ 4 (g ∘ L) t (fun _ => 1) = _
  rw [h]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hL (s : ℝ) : L s = s • v := rfl
  simp only [hL,one_smul]
  change iteratedFDeriv ℝ 4 (fun z => f (b+z)) (t • v) (fun _ => v) = _
  rw [iteratedFDeriv_comp_add_left]

theorem fourthDeriv_affine_line_bound (f : Position → ℝ) (b v : Position) (t : ℝ)
    (hf : ContDiffAt ℝ 4 f (b+t • v)) :
    |iteratedDeriv 4 (fun s : ℝ => f (b+s • v)) t| ≤
      ‖iteratedFDeriv ℝ 4 f (b+t • v)‖*‖v‖^4 := by
  rw [fourthDeriv_affine_line f b v t hf,← Real.norm_eq_abs]
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
    (iteratedFDeriv ℝ 4 f (b+t • v)).le_opNorm (fun _ => v)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_GaussPositionCell
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual eight equal masses on any translated cube, with a fourth-order
error bound from the ambient fourth Fréchet derivative. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem cubePoint_contDiff (b : Position) (d : ℝ) :
    ContDiff ℝ 4 (fun p : ℝ × ℝ × ℝ => cubePoint b d p.1 p.2.1 p.2.2) := by
  unfold cubePoint
  fun_prop

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_GaussEightNodes
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identify tensor quadrature with the actual eight equal point masses and
with the already separated Gauss lattice used by the nuclear construction. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem gaussTensor3_eq_node_sum (f : ℝ → ℝ → ℝ → ℝ) :
    gaussTwoPoint (fun x => gaussTwoPoint (fun y => gaussTwoPoint (f x y))) =
      ∑ v : Fin 3 → Fin 2, f (gaussNode (v 0)) (gaussNode (v 1)) (gaussNode (v 2)) := by
  have h := Fintype.sum_equiv gaussNodeTriple
    (fun v => f (gaussNode (v 0)) (gaussNode (v 1)) (gaussNode (v 2)))
    (fun p => f (gaussNode p.1) (gaussNode p.2.1) (gaussNode p.2.2)) (fun _ => rfl)
  rw [h]
  simp only [Fintype.sum_prod_type,Fin.sum_univ_two,gaussNode,Fin.isValue,ite_true, if_true]
  rfl

theorem positionCellGauss_eq_node_sum (b : Position) (h : ℝ) (f : Position → ℝ) :
    positionCellGauss b h f = (h^3/8)*∑ v : Fin 3 → Fin 2,
      f (cubePoint b (h/2) (gaussNode (v 0)) (gaussNode (v 1)) (gaussNode (v 2))) := by
  rw [positionCellGauss,gaussTensor3_eq_node_sum]
  congr 1
  ring

theorem cubePoint_gaussLatticePoint (h : ℝ) (k : Fin 3 → ℤ) (v : Fin 3 → Fin 2) :
    cubePoint (gaussCellCenter h k) (h/2) (gaussNode (v 0)) (gaussNode (v 1)) (gaussNode (v 2)) =
      gaussLatticePoint h (k,v) := by
  ext i
  fin_cases i <;> simp [cubePoint,gaussCellCenter,gaussLatticePoint] <;> ring

theorem gaussCell_quadrature_lattice (h : ℝ) (k : Fin 3 → ℤ) (f : Position → ℝ) :
    positionCellGauss (gaussCellCenter h k) h f =
      (h^3/8)*∑ v : Fin 3 → Fin 2, f (gaussLatticePoint h (k,v)) := by
  rw [positionCellGauss_eq_node_sum]
  simp only [cubePoint_gaussLatticePoint]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_GaussGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Error accounting for a finite rectangular selection of equal-mass Gauss
cells. The constants may vary between cells, retaining spatial decay. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

/-- The fourth-order total estimate retains the sum of volume-weighted local
fourth derivative bounds, rather than multiplying by the entire box volume. -/
theorem weighted_cubature_error {ι : Type*} [Fintype ι] (h rho : ℝ)
    (Q I C : ι → ℝ) (hrho : 0 ≤ rho)
    (herr : ∀ i, |Q i-I i| ≤ C i*h^7) :
    |rho*(∑ i, Q i)-rho*(∑ i, I i)| ≤ rho*h^4*(∑ i, C i*h^3) := by
  rw [← mul_sub,abs_mul,abs_of_nonneg hrho,← Finset.sum_sub_distrib]
  apply (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hrho).trans
  apply (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => herr i)) hrho).trans_eq
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_GaussLocal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local versions of tensor cubature: regularity is only needed on the
integration cube, which may be far from a Coulomb singularity. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem unitClamp_mem (x : ℝ) : unitClamp x ∈ Set.Icc (-1:ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem unitClamp_eq {x : ℝ} (hx : x ∈ Set.Icc (-1:ℝ) 1) : unitClamp x = x := by
  simp only [unitClamp,min_eq_right hx.2,max_eq_right hx.1]

theorem unitClamp_continuous : Continuous unitClamp :=
  continuous_const.max (continuous_const.min continuous_id)

theorem gaussTwoPoint_congr_on {f g : ℝ → ℝ}
    (h : Set.EqOn f g (Set.Icc (-1:ℝ) 1)) : gaussTwoPoint f = gaussTwoPoint g := by
  have ha : gaussAbscissa ≤ 1 := by nlinarith only [gaussAbscissa_sq,gaussAbscissa_pos]
  have hp := gaussAbscissa_pos.le
  unfold gaussTwoPoint
  rw [h (x := -gaussAbscissa) ⟨by linarith,by linarith⟩,
    h (x := gaussAbscissa) ⟨by linarith,ha⟩]

theorem unitInterval_integral_congr {f g : ℝ → ℝ}
    (h : Set.EqOn f g (Set.Icc (-1:ℝ) 1)) :
    (∫ x : ℝ in (-1)..1, f x) = ∫ x : ℝ in (-1)..1, g x := by
  apply intervalIntegral.integral_congr
  simpa only [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 1)] using h

theorem gaussTensor3_congr_on {f g : ℝ → ℝ → ℝ → ℝ}
    (h : ∀ x ∈ Set.Icc (-1:ℝ) 1, ∀ y ∈ Set.Icc (-1:ℝ) 1,
      ∀ z ∈ Set.Icc (-1:ℝ) 1, f x y z = g x y z) :
    gaussTwoPoint (fun x => gaussTwoPoint (fun y => gaussTwoPoint (f x y))) =
      gaussTwoPoint (fun x => gaussTwoPoint (fun y => gaussTwoPoint (g x y))) := by
  apply gaussTwoPoint_congr_on
  intro x hx
  apply gaussTwoPoint_congr_on
  intro y hy
  exact gaussTwoPoint_congr_on (h x hx y hy)

theorem unitCube_integral_congr {f g : ℝ → ℝ → ℝ → ℝ}
    (h : ∀ x ∈ Set.Icc (-1:ℝ) 1, ∀ y ∈ Set.Icc (-1:ℝ) 1,
      ∀ z ∈ Set.Icc (-1:ℝ) 1, f x y z = g x y z) :
    (∫ x : ℝ in (-1)..1, ∫ y : ℝ in (-1)..1, ∫ z : ℝ in (-1)..1, f x y z) =
      ∫ x : ℝ in (-1)..1, ∫ y : ℝ in (-1)..1, ∫ z : ℝ in (-1)..1, g x y z := by
  apply unitInterval_integral_congr
  intro x hx
  apply unitInterval_integral_congr
  intro y hy
  exact unitInterval_integral_congr (h x hx y hy)

theorem gaussTensor3_error_on_cube (f : ℝ → ℝ → ℝ → ℝ)
    (hf : ContinuousOn (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2) unitCube3) {E : ℝ}
    (hx : ∀ y ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1,
      |gaussTwoPoint (fun x => f x y z)-(∫ x : ℝ in (-1)..1, f x y z)| ≤ E)
    (hy : ∀ x ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1,
      |gaussTwoPoint (fun y => f x y z)-(∫ y : ℝ in (-1)..1, f x y z)| ≤ E)
    (hz : ∀ x ∈ Set.Icc (-1) 1, ∀ y ∈ Set.Icc (-1) 1,
      |gaussTwoPoint (f x y)-(∫ z : ℝ in (-1)..1, f x y z)| ≤ E) :
    |gaussTwoPoint (fun x => gaussTwoPoint (fun y => gaussTwoPoint (f x y)))-
      (∫ x : ℝ in (-1)..1, ∫ y : ℝ in (-1)..1, ∫ z : ℝ in (-1)..1, f x y z)| ≤ 12*E := by
  let g : ℝ → ℝ → ℝ → ℝ := fun x y z => f (unitClamp x) (unitClamp y) (unitClamp z)
  have hg : Continuous (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) :=
    hf.comp_continuous
      ((unitClamp_continuous.comp continuous_fst).prodMk
        ((unitClamp_continuous.comp (continuous_fst.comp continuous_snd)).prodMk
          (unitClamp_continuous.comp (continuous_snd.comp continuous_snd))))
      (fun p => ⟨unitClamp_mem p.1,unitClamp_mem p.2.1,unitClamp_mem p.2.2⟩)
  have heq : ∀ x ∈ Set.Icc (-1:ℝ) 1, ∀ y ∈ Set.Icc (-1:ℝ) 1,
      ∀ z ∈ Set.Icc (-1:ℝ) 1, g x y z = f x y z := by
    intro x hx y hy z hz
    simp only [g,unitClamp_eq hx,unitClamp_eq hy,unitClamp_eq hz]
  have hxe : ∀ y ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1,
      |gaussTwoPoint (fun x => g x y z)-(∫ x : ℝ in (-1)..1, g x y z)| ≤ E := by
    intro y hy z hz
    have he : Set.EqOn (fun x => g x y z) (fun x => f x y z) (Set.Icc (-1:ℝ) 1) :=
      fun x hx => heq x hx y hy z hz
    rw [gaussTwoPoint_congr_on he,unitInterval_integral_congr he]
    exact hx y hy z hz
  have hye : ∀ x ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1,
      |gaussTwoPoint (fun y => g x y z)-(∫ y : ℝ in (-1)..1, g x y z)| ≤ E := by
    intro x hx z hz
    have he : Set.EqOn (fun y => g x y z) (fun y => f x y z) (Set.Icc (-1:ℝ) 1) :=
      fun y hy => heq x hx y hy z hz
    rw [gaussTwoPoint_congr_on he,unitInterval_integral_congr he]
    exact hy x hx z hz
  have hze : ∀ x ∈ Set.Icc (-1) 1, ∀ y ∈ Set.Icc (-1) 1,
      |gaussTwoPoint (g x y)-(∫ z : ℝ in (-1)..1, g x y z)| ≤ E := by
    intro x hx y hy
    have he : Set.EqOn (g x y) (f x y) (Set.Icc (-1:ℝ) 1) :=
      fun z hz => heq x hx y hy z hz
    rw [gaussTwoPoint_congr_on he,unitInterval_integral_congr he]
    exact hz x hx y hy
  have he := gaussTensor3_error g hg hxe hye hze
  rw [gaussTensor3_congr_on heq,unitCube_integral_congr heq] at he
  exact he

theorem gaussTensor3_C4_error_on_cube (f : ℝ → ℝ → ℝ → ℝ)
    (hf : ContinuousOn (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2) unitCube3) {C : ℝ} (hC : 0 ≤ C)
    (hfx : ∀ y ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1,
      ContDiffOn ℝ 4 (fun x => f x y z) (Set.Icc (-1) 1))
    (hfy : ∀ x ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1,
      ContDiffOn ℝ 4 (fun y => f x y z) (Set.Icc (-1) 1))
    (hfz : ∀ x ∈ Set.Icc (-1) 1, ∀ y ∈ Set.Icc (-1) 1,
      ContDiffOn ℝ 4 (f x y) (Set.Icc (-1) 1))
    (hCx : ∀ y ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1, ∀ x ∈ Set.Icc (-1) 1,
      ‖iteratedDerivWithin 4 (fun x => f x y z) (Set.Icc (-1) 1) x‖ ≤ C)
    (hCy : ∀ x ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1, ∀ y ∈ Set.Icc (-1) 1,
      ‖iteratedDerivWithin 4 (fun y => f x y z) (Set.Icc (-1) 1) y‖ ≤ C)
    (hCz : ∀ x ∈ Set.Icc (-1) 1, ∀ y ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1,
      ‖iteratedDerivWithin 4 (f x y) (Set.Icc (-1) 1) z‖ ≤ C) :
    |gaussTwoPoint (fun x => gaussTwoPoint (fun y => gaussTwoPoint (f x y)))-
      (∫ x : ℝ in (-1)..1, ∫ y : ℝ in (-1)..1, ∫ z : ℝ in (-1)..1, f x y z)| ≤ 128*C := by
  have h := gaussTensor3_error_on_cube f hf
    (fun y hy z hz => gaussTwoPoint_C4_error _ hC (hfx y hy z hz) (hCx y hy z hz))
    (fun x hx z hz => gaussTwoPoint_C4_error _ hC (hfy x hx z hz) (hCy x hx z hz))
    (fun x hx y hy => gaussTwoPoint_C4_error _ hC (hfz x hx y hy) (hCz x hx y hy))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring


end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_GaussLocalPositionCell
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cell estimate requires smoothness only near the cell. -/
noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

private theorem fourthDerivWithin_line_bound_local (f : Position → ℝ) (b v : Position) (t : ℝ)
    (hf : ContDiffAt ℝ 4 f (b+t • v)) (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    ‖iteratedDerivWithin 4 (fun s : ℝ => f (b+s • v)) (Set.Icc (-1) 1) t‖ ≤
      ‖iteratedFDeriv ℝ 4 f (b+t • v)‖*‖v‖^4 := by
  have hline : ContDiffAt ℝ 4 (fun s : ℝ => f (b+s • v)) t :=
    hf.comp t (show ContDiffAt ℝ 4 (fun s : ℝ => b+s • v) t by fun_prop)
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
    hline ht,Real.norm_eq_abs]
  exact fourthDeriv_affine_line_bound f b v t hf

private theorem cube_axis_fourth_bound_local (f : Position → ℝ) (b v : Position) (t d C : ℝ)
    (hf : ContDiffAt ℝ 4 f (b+t • v)) (ht : t ∈ Set.Icc (-1:ℝ) 1)
    (hD : ‖iteratedFDeriv ℝ 4 f (b+t • v)‖ ≤ C) (hv : ‖v‖ = d) :
    ‖iteratedDerivWithin 4 (fun s : ℝ => f (b+s • v)) (Set.Icc (-1) 1) t‖ ≤ C*d^4 := by
  apply (fourthDerivWithin_line_bound_local f b v t hf ht).trans
  rw [hv]
  exact mul_le_mul_of_nonneg_right hD (pow_nonneg (norm_nonneg v |>.trans_eq hv) _)

theorem positionCellGauss_error_local (f : Position → ℝ) (b : Position) {h C : ℝ} (hh : 0 ≤ h) (hC : 0 ≤ C)
    (hf : ∀ x ∈ Set.Icc (-1:ℝ) 1, ∀ y ∈ Set.Icc (-1:ℝ) 1,
      ∀ z ∈ Set.Icc (-1:ℝ) 1, ContDiffAt ℝ 4 f (cubePoint b (h/2) x y z))
    (hD : ∀ x ∈ Set.Icc (-1:ℝ) 1, ∀ y ∈ Set.Icc (-1:ℝ) 1,
      ∀ z ∈ Set.Icc (-1:ℝ) 1,
      ‖iteratedFDeriv ℝ 4 f (cubePoint b (h/2) x y z)‖ ≤ C) :
    |positionCellGauss b h f-positionCellIntegral b h f| ≤ C*h^7 := by
  let d := h/2
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hv (i : Fin 3) : ‖d • (EuclideanSpace.single i 1 : Position)‖ = d := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hd,PiLp.norm_single]
    norm_num
  have hxline (x y z : ℝ) : cubePoint b d x y z =
      (b+y • (d • EuclideanSpace.single 1 1)+z • (d • EuclideanSpace.single 2 1))+
      x • (d • EuclideanSpace.single 0 1) := by unfold cubePoint; module
  have hyline (x y z : ℝ) : cubePoint b d x y z =
      (b+x • (d • EuclideanSpace.single 0 1)+z • (d • EuclideanSpace.single 2 1))+
      y • (d • EuclideanSpace.single 1 1) := by unfold cubePoint; module
  have hzline (x y z : ℝ) : cubePoint b d x y z =
      (b+x • (d • EuclideanSpace.single 0 1)+y • (d • EuclideanSpace.single 1 1))+
      z • (d • EuclideanSpace.single 2 1) := rfl
  have hc : ContinuousOn (fun p : ℝ × ℝ × ℝ => f (cubePoint b d p.1 p.2.1 p.2.2)) unitCube3 := by
    intro p hp
    exact (ContinuousAt.comp (f := fun q : ℝ × ℝ × ℝ => cubePoint b d q.1 q.2.1 q.2.2)
      (hf p.1 hp.1 p.2.1 hp.2.1 p.2.2 hp.2.2).continuousAt
      (cubePoint_contDiff b d).continuous.continuousAt).continuousWithinAt
  have hfx (y : ℝ) (hy : y ∈ Set.Icc (-1:ℝ) 1) (z : ℝ) (hz : z ∈ Set.Icc (-1:ℝ) 1) :
      ContDiffOn ℝ 4 (fun x => f (cubePoint b d x y z)) (Set.Icc (-1) 1) := by
    intro x hx
    exact ((hf x hx y hy z hz).comp x
      (show ContDiffAt ℝ 4 (fun x => cubePoint b d x y z) x by unfold cubePoint; fun_prop)).contDiffWithinAt
  have hfy (x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 1) (z : ℝ) (hz : z ∈ Set.Icc (-1:ℝ) 1) :
      ContDiffOn ℝ 4 (fun y => f (cubePoint b d x y z)) (Set.Icc (-1) 1) := by
    intro y hy
    exact ((hf x hx y hy z hz).comp y
      (show ContDiffAt ℝ 4 (fun y => cubePoint b d x y z) y by unfold cubePoint; fun_prop)).contDiffWithinAt
  have hfz (x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 1) (y : ℝ) (hy : y ∈ Set.Icc (-1:ℝ) 1) :
      ContDiffOn ℝ 4 (fun z => f (cubePoint b d x y z)) (Set.Icc (-1) 1) := by
    intro z hz
    exact ((hf x hx y hy z hz).comp z
      (show ContDiffAt ℝ 4 (fun z => cubePoint b d x y z) z by unfold cubePoint; fun_prop)).contDiffWithinAt
  have hDx (y : ℝ) (hy : y ∈ Set.Icc (-1:ℝ) 1) (z : ℝ) (hz : z ∈ Set.Icc (-1:ℝ) 1)
      (x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 1) :
      ‖iteratedDerivWithin 4 (fun x => f (cubePoint b d x y z)) (Set.Icc (-1) 1) x‖ ≤ C*d^4 := by
    simp_rw [hxline]
    exact cube_axis_fourth_bound_local f _ _ x d C (by rw [← hxline]; exact hf x hx y hy z hz) hx
      (by rw [← hxline]; exact hD x hx y hy z hz) (hv 0)
  have hDy (x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 1) (z : ℝ) (hz : z ∈ Set.Icc (-1:ℝ) 1)
      (y : ℝ) (hy : y ∈ Set.Icc (-1:ℝ) 1) :
      ‖iteratedDerivWithin 4 (fun y => f (cubePoint b d x y z)) (Set.Icc (-1) 1) y‖ ≤ C*d^4 := by
    simp_rw [hyline]
    exact cube_axis_fourth_bound_local f _ _ y d C (by rw [← hyline]; exact hf x hx y hy z hz) hy
      (by rw [← hyline]; exact hD x hx y hy z hz) (hv 1)
  have hDz (x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 1) (y : ℝ) (hy : y ∈ Set.Icc (-1:ℝ) 1)
      (z : ℝ) (hz : z ∈ Set.Icc (-1:ℝ) 1) :
      ‖iteratedDerivWithin 4 (fun z => f (cubePoint b d x y z)) (Set.Icc (-1) 1) z‖ ≤ C*d^4 := by
    simp_rw [hzline]
    exact cube_axis_fourth_bound_local f _ _ z d C (by rw [← hzline]; exact hf x hx y hy z hz) hz
      (by rw [← hzline]; exact hD x hx y hy z hz) (hv 2)
  have he := gaussTensor3_C4_error_on_cube (fun x y z => f (cubePoint b d x y z)) hc
    (mul_nonneg hC (pow_nonneg hd 4))
    hfx
    hfy
    hfz hDx hDy hDz
  change |d^3*_ - d^3*_| ≤ _
  rw [← mul_sub,abs_mul,abs_of_nonneg (pow_nonneg hd 3)]
  apply (mul_le_mul_of_nonneg_left he (pow_nonneg hd 3)).trans_eq
  dsimp [d]
  ring


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

private theorem axis_second_partial_bound (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (a : Fin 3) {k : ℕ} (hk : k ≤ 4) (x : Position) :
    ‖iteratedFDeriv ℝ k (dirPartial (dirPartial V (axis a)) (axis a)) x‖ ≤
      ‖iteratedFDeriv ℝ (k+2) V x‖ := by
  have hp : ContDiff ℝ 5 (dirPartial V (axis a)) :=
    (hV.fderiv_right (by norm_num : (5 : WithTop ℕ∞)+1 ≤ 6)).clm_apply contDiff_const
  have hpp : ContDiff ℝ 4 (fderiv ℝ (dirPartial V (axis a))) :=
    hp.fderiv_right (by norm_num)
  have h := norm_iteratedFDeriv_clm_apply_const (x := x) (c := axis a) hpp.contDiffAt
    (show (k : WithTop ℕ∞) ≤ 4 by exact_mod_cast hk)
  rw [norm_iteratedFDeriv_fderiv] at h
  have h' := dirPartial_iterated_norm_bound V hV (axis a) (show k+1 ≤ 5 by omega) x
  have hn : ‖axis a‖ = 1 := by simp [axis]
  simp only [hn, one_mul] at h h'
  exact h.trans (by simpa only [Nat.add_assoc] using h')

/-- All derivatives of the manufactured charge through order four have a
bound depending only on the scalar field's order-six bound. -/
theorem manufacturedCharge_derivative_bound (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    {B : ℝ} (_hB : 0 ≤ B)
    (hbound : ∀ k ≤ 6, ∀ x, ‖iteratedFDeriv ℝ k V x‖ ≤ B)
    {k : ℕ} (hk : k ≤ 4) (x : Position) :
    ‖iteratedFDeriv ℝ k (manufacturedCharge V) x‖ ≤ 3*B/(4*Real.pi) := by
  have hpp (a : Fin 3) : ContDiff ℝ 4 (dirPartial (dirPartial V (axis a)) (axis a)) :=
    (((hV.fderiv_right (by norm_num : (5 : WithTop ℕ∞)+1 ≤ 6)).clm_apply contDiff_const).fderiv_right
      (by norm_num : (4 : WithTop ℕ∞)+1 ≤ 5)).clm_apply contDiff_const
  have he : coordinateLaplacian V = fun y =>
      ∑ a : Fin 3, dirPartial (dirPartial V (axis a)) (axis a) y :=
    funext (fun _ => NeutralAtom.coordinateLaplacian_eq_partials
      (hV.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 6)).contDiffAt)
  have hl : ‖iteratedFDeriv ℝ k (coordinateLaplacian V) x‖ ≤ 3*B := by
    rw [he, iteratedFDeriv_fun_sum_apply (fun a _ =>
      ((hpp a).of_le (show (k : WithTop ℕ∞) ≤ 4 by exact_mod_cast hk)).contDiffAt)]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _a : Fin 3, B := Finset.sum_le_sum (fun a _ =>
        (axis_second_partial_bound V hV a hk x).trans (hbound (k+2) (by omega) x))
      _ = _ := by simp
  have hlreg : ContDiff ℝ 4 (coordinateLaplacian V) := by
    rw [he]
    exact ContDiff.sum (fun a _ => hpp a)
  have hc : (manufacturedCharge V) = fun y => (4*Real.pi)⁻¹ • coordinateLaplacian V y := by
    funext y
    unfold manufacturedCharge
    simp only [smul_eq_mul]
    ring
  rw [hc, iteratedFDeriv_const_smul_apply'
    (hlreg.of_le (show (k : WithTop ℕ∞) ≤ 4 by exact_mod_cast hk)).contDiffAt]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact (mul_le_mul_of_nonneg_left hl (by positivity)).trans_eq (by ring)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_MoserDerivatives
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform finite bounds for all joint field derivatives through order four.
These bounds control the explicit velocity in the differentiated flow equations. -/

noncomputable section
open scoped Topology NNReal BigOperators
namespace ContinuumCoulomb

theorem moserVelocity_iterated_derivative_bound {rho : ℝ} (hrho : 0 < rho)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V) (hc : HasCompactSupport V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2)
    (r : ℕ) (hr : r ≤ 4) :
    ∃ B : ℝ≥0, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x,
      ‖iteratedFDeriv ℝ r (fun p : ℝ × Position => moserVelocity rho V p.1 p.2) (t, x)‖ ≤ B := by
  let F : ℝ × Position → Position := fun p => moserVelocity rho V p.1 p.2
  let T : Set (ℝ × Position) := Set.Icc (0 : ℝ) 1 ×ˢ tsupport V
  have hT : IsCompact T := isCompact_Icc.prod hc
  have hopen := moserDomain_isOpen rho V hV
  have hreg : ContDiffOn ℝ 4 F (moserDomain rho V) := moserVelocity_joint_C4 rho V hV
  have hcont : ContinuousOn (iteratedFDeriv ℝ r F) (moserDomain rho V) := by
    apply (hreg.continuousOn_iteratedFDerivWithin (by exact_mod_cast hr) hopen.uniqueDiffOn).congr
    intro p hp
    exact (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := F) r hopen hp).symm
  have hTD : T ⊆ moserDomain rho V := fun p hp =>
    moserDomain_contains_time_slab hrho V hbound ⟨hp.1, Set.mem_univ _⟩
  obtain ⟨A, hA⟩ := hT.bddAbove_image ((hcont.mono hTD).norm)
  refine ⟨⟨max 0 A, le_max_left _ _⟩, fun t ht x => ?_⟩
  by_cases hx : x ∈ tsupport V
  · exact (hA ⟨(t, x), ⟨ht, hx⟩, rfl⟩).trans (le_max_right _ _)
  · have hn : (t, x) ∉ tsupport (iteratedFDeriv ℝ r F) := fun hp =>
      hx ((moserVelocity_joint_tsupport_subset rho V (tsupport_iteratedFDeriv_subset r hp)).2)
    rw [image_eq_zero_of_notMem_tsupport hn, norm_zero]
    exact le_max_left _ _

/-- A common finite bound works for all five derivative orders. -/
theorem moserVelocity_four_derivative_bounds {rho : ℝ} (hrho : 0 < rho)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V) (hc : HasCompactSupport V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2) :
    ∃ B : ℝ≥0, ∀ r ≤ 4, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x,
      ‖iteratedFDeriv ℝ r (fun p : ℝ × Position => moserVelocity rho V p.1 p.2) (t, x)‖ ≤ B := by
  have h (r : Fin 5) := moserVelocity_iterated_derivative_bound hrho V hV hc hbound
    r (by omega)
  choose B hB using h
  refine ⟨∑ r : Fin 5, B r, fun r hr t ht x => ?_⟩
  let i : Fin 5 := ⟨r, by omega⟩
  exact (hB i t ht x).trans (by
    exact_mod_cast (Finset.single_le_sum (fun j _ => (show (0 : ℝ≥0) ≤ B j from zero_le))
      (Finset.mem_univ i)))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_MoserFlowRegularity
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-dimensional flow regularity for the Moser trajectories. -/

noncomputable section
open scoped BigOperators NNReal
namespace ContinuumCoulomb

theorem moser_flow_C4 (hpublished : PublishedC4FlowInput) {rho : ℝ} (hrho : 0 < rho)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow (moserVelocity rho V) G) :
    (∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiff ℝ 4 (fun x => G x t)) ∧
      (∀ x t, t ∈ Set.Icc (0 : ℝ) 1 →
        HasDerivWithinAt (fun s => flowJacobian G s x)
          (fieldDivergence (moserVelocity rho V t) (G x t) * flowJacobian G t x)
          (Set.Icc (0 : ℝ) 1) t) :=
  hpublished.regularity (moserDomain rho V) (moserDomain_isOpen rho V hV)
    (moserDomain_contains_time_slab hrho V hbound) (moserVelocity rho V)
    (moserVelocity_joint_C4 rho V hV) G hG

theorem moser_flow_uniform_derivatives (hpublished : PublishedC4FlowInput) {rho : ℝ}
    (hrho : 0 < rho) (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hc : HasCompactSupport V) (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ G : Position → ℝ → Position,
      IsUnitTimeFlow (moserVelocity rho V) G →
      ∀ r : ℕ, 1 ≤ r → r ≤ 4 → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x,
        ‖iteratedFDeriv ℝ r (fun y => G y t) x‖ ≤ C := by
  obtain ⟨B, hB⟩ := moserVelocity_four_derivative_bounds hrho V hV hc hbound
  obtain ⟨C, hC, hboundC⟩ := hpublished.uniform B B.coe_nonneg
  exact ⟨C, hC, hboundC (moserDomain rho V) (moserDomain_isOpen rho V hV)
    (moserDomain_contains_time_slab hrho V hbound) (moserVelocity rho V)
    (moserVelocity_joint_C4 rho V hV) hB⟩

/-- All properties concern a single family of actual ODE trajectories. -/
theorem moser_C4_bilipschitz_flow_exists (hpublished : PublishedC4FlowInput)
    {rho : ℝ} (hrho : 0 < rho) (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hc : HasCompactSupport V) (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2) :
    ∃ (G : Position → ℝ → Position) (C Cinv : ℝ≥0) (D : ℝ),
      0 < D ∧ IsUnitTimeFlow (moserVelocity rho V) G ∧
      Function.Bijective (fun x => G x 1) ∧
      LipschitzWith C (fun x => G x 1) ∧
      AntilipschitzWith Cinv (fun x => G x 1) ∧
      (∀ x, x ∉ tsupport V → G x 1 = x) ∧
      ContDiff ℝ 4 (fun x => G x 1) ∧
      (∀ r : ℕ, 1 ≤ r → r ≤ 4 → ∀ x,
        ‖iteratedFDeriv ℝ r (fun y => G y 1) x‖ ≤ D) := by
  obtain ⟨G, C, Cinv, hG0, hG, hbij, hC, hCinv, hfix⟩ :=
    moser_bilipschitz_time_one_exists hrho V hV hc hbound
  have hflow : IsUnitTimeFlow (moserVelocity rho V) G := ⟨hG0, hG⟩
  have hreg := (moser_flow_C4 hpublished hrho V hV hbound G hflow).1
  obtain ⟨D, hD, hderiv⟩ := moser_flow_uniform_derivatives hpublished hrho V hV hc hbound
  have h1 : (1 : ℝ) ∈ Set.Icc 0 1 := ⟨by norm_num, le_rfl⟩
  exact ⟨G, C, Cinv, D, hD, hflow, hbij, hC, hCinv, hfix, hreg 1 h1,
    fun r hr hr' x => hderiv G hflow r hr hr' 1 h1 x⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_MoserJacobian
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The continuity equation yields the density-Jacobian identity along the
flow. The proof uses finite-dimensional ODE regularity. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb
open NeutralAtom (dirPartial axis)

private theorem linear_apply_coordinates (L : Position →L[ℝ] ℝ) (v : Position) :
    L v = ∑ a : Fin 3, v a * L (axis a) := by
  have he : v = ∑ a : Fin 3, v a • axis a := by
    ext b
    simp [axis, Pi.single_apply]
  calc
    L v = L (∑ a : Fin 3, v a • axis a) := congrArg L he
    _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]

private theorem divergence_scalar_mul (f : Position → ℝ) (v : Position → Position)
    (hf : Differentiable ℝ f) (hv : Differentiable ℝ v) (x : Position) :
    (∑ a : Fin 3, dirPartial (fun y => f y * v y a) (axis a) x) =
      fderiv ℝ f x (v x) + f x * fieldDivergence v x := by
  have hcoord (a : Fin 3) : Differentiable ℝ (fun y => v y a) := by
    intro y
    exact ((PiLp.hasFDerivAt_apply 2 (v y) a).comp y (hv y).hasFDerivAt).differentiableAt
  have hp (a : Fin 3) : dirPartial (fun y => f y * v y a) (axis a) x =
      v x a * dirPartial f (axis a) x + f x * dirPartial (fun y => v y a) (axis a) x := by
    unfold dirPartial
    rw [fderiv_fun_mul (hf x) (hcoord a x)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  simp_rw [hp]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum,
    linear_apply_coordinates (fderiv ℝ f x) (v x)]
  rfl

theorem moser_continuity_expanded {rho : ℝ} (hrho : 0 < rho)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (x : Position) :
    manufacturedCharge V x +
      t * fderiv ℝ (manufacturedCharge V) x (moserVelocity rho V t x) +
      homotopyDensity rho V t x * fieldDivergence (moserVelocity rho V t) x = 0 := by
  have hσ : Differentiable ℝ (manufacturedCharge V) :=
    (manufacturedCharge_C4 V hV).differentiable (by norm_num)
  have hρc : ContDiff ℝ 4 (homotopyDensity rho V t) :=
    contDiff_const.add (contDiff_const.mul (manufacturedCharge_C4 V hV))
  have hρ : Differentiable ℝ (homotopyDensity rho V t) :=
    hρc.differentiable (by norm_num)
  have hv := (moserVelocity_C4 hrho V hV hbound ht.1 ht.2).differentiable (by norm_num)
  have h := moser_continuity_equation hrho V (hV.of_le (by norm_num)) hbound ht.1 ht.2 x
  rw [homotopyDensity_time_deriv, divergence_scalar_mul _ _ hρ hv] at h
  have hd : fderiv ℝ (homotopyDensity rho V t) x = t • fderiv ℝ (manufacturedCharge V) x := by
    unfold homotopyDensity
    rw [fderiv_const_add, fderiv_const_mul (hσ x)]
  rw [hd, smul_apply, smul_eq_mul] at h
  simpa only [add_assoc] using h

theorem flowJacobian_zero (G : Position → ℝ → Position) (hG : ∀ x, G x 0 = x)
    (x : Position) : flowJacobian G 0 x = 1 := by
  have he : (fun y => G y 0) = id := funext hG
  simp [flowJacobian, he, ContinuousLinearMap.det]

/-- Density times the determinant of the actual flow derivative is exactly
constant, including the endpoint used by cubature. -/
theorem moser_density_jacobian (hpublished : PublishedC4FlowInput)
    {rho : ℝ} (hrho : 0 < rho) (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow (moserVelocity rho V) G)
    (x : Position) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    homotopyDensity rho V t (G x t) * flowJacobian G t x = rho := by
  have hJ := (moser_flow_C4 hpublished hrho V hV hbound G hG).2
  let P : ℝ → ℝ := fun s => homotopyDensity rho V s (G x s) * flowJacobian G s x
  have hσ : Differentiable ℝ (manufacturedCharge V) :=
    (manufacturedCharge_C4 V hV).differentiable (by norm_num)
  have hP (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
      HasDerivWithinAt P 0 (Set.Icc (0 : ℝ) 1) s := by
    have hσG := (hσ (G x s)).hasFDerivAt.comp_hasDerivWithinAt s (hG.2 x s hs)
    have hρG := (((hasDerivAt_id s).hasDerivWithinAt.mul hσG).const_add rho)
    have hmul := hρG.mul (hJ x s hs)
    have hzero := moser_continuity_expanded hrho V hV hbound hs (G x s)
    convert hmul using 1 <;> first | rfl | (
      simp only [id_eq, one_mul, Function.comp_apply, Pi.mul_apply]
      dsimp only [homotopyDensity] at hzero ⊢
      linear_combination -(flowJacobian G s x) * hzero)
  have hn := norm_image_sub_le_of_norm_deriv_le_segment' hP
    (fun _ _ => (by simp : ‖(0 : ℝ)‖ ≤ 0)) t ht
  have he : P t = P 0 := by simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using hn
  simpa only [P, (homotopyDensity_endpoints rho V (G x 0)).1,
    flowJacobian_zero G hG.1 x, mul_one] using he

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_MoserTransport
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact change of variables from uniform slab density to the actual
manufactured density. The identity is for arbitrary scalar integrands,
including the Coulomb kernel used by the nuclear cubature. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem moser_flowJacobian_pos (hpublished : PublishedC4FlowInput)
    {rho : ℝ} (hrho : 0 < rho) (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow (moserVelocity rho V) G)
    (x : Position) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 < flowJacobian G t x := by
  have he := moser_density_jacobian hpublished hrho V hV hbound G hG x ht
  have hp : 0 < homotopyDensity rho V t (G x t) :=
    homotopyDensity_pos hrho V hbound ht.1 ht.2 _
  have hm : 0 < homotopyDensity rho V t (G x t) * flowJacobian G t x := by
    rw [he]
    exact hrho
  rcases mul_pos_iff.mp hm with h | h
  · exact h.2
  · exact False.elim (not_lt_of_ge hp.le h.1)

/-- The actual Moser map pushes uniform density to the synthesized
nonnegative nuclear density, with the entire slab preserved. -/
theorem moser_density_integral (hpublished : PublishedC4FlowInput)
    {rho H S : ℝ} (hrho : 0 < rho) (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    (hsupport : tsupport V ⊆ slabDomain H S)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow (moserVelocity rho V) G)
    (hbij : Function.Bijective (fun x => G x 1))
    (hfix : ∀ x, x ∉ tsupport V → G x 1 = x) (f : Position → ℝ) :
    (∫ y in slabDomain H S, synthesizedDensity rho H S V y * f y) =
      rho * ∫ x in slabDomain H S, f (G x 1) := by
  have hs := (slabDomain_isClosed H S).measurableSet
  have h1 : (1 : ℝ) ∈ Set.Icc 0 1 := ⟨by norm_num, le_rfl⟩
  have hreg := (moser_flow_C4 hpublished hrho V hV hbound G hG).1 1 h1
  have himage := moser_time_one_preserves_slab V hsupport (fun x => G x 1) hbij hfix
  have hchange := integral_image_eq_integral_abs_det_fderiv_smul volume hs
    (fun x (_hx : x ∈ slabDomain H S) =>
      (hreg.differentiable (by norm_num) x).hasFDerivAt.hasFDerivWithinAt)
    hbij.1.injOn (fun y => synthesizedDensity rho H S V y * f y)
  rw [himage] at hchange
  rw [hchange, ← integral_const_mul]
  apply setIntegral_congr_fun hs
  intro x hx
  have hGx : G x 1 ∈ slabDomain H S := by
    rw [← himage]
    exact ⟨x, hx, rfl⟩
  have hJ := moser_density_jacobian hpublished hrho V hV hbound G hG x h1
  have hp := moser_flowJacobian_pos hpublished hrho V hV hbound G hG x h1
  change |flowJacobian G 1 x| * (synthesizedDensity rho H S V (G x 1) * f (G x 1)) = _
  rw [abs_of_pos hp]
  simp only [synthesizedDensity, slabDensity, Set.indicator_of_mem hGx] at hJ ⊢
  simp only [homotopyDensity, one_mul] at hJ
  calc
    flowJacobian G 1 x * ((rho + manufacturedCharge V (G x 1)) * f (G x 1)) =
      ((rho + manufacturedCharge V (G x 1)) * flowJacobian G 1 x) * f (G x 1) := by ring
    _ = rho * f (G x 1) := by rw [hJ]

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

theorem positionSplitCoordinates_norm_sq (x : Position) :
    ‖x‖ ^ 2 = ‖(positionSplitCoordinates x).1‖ ^ 2 +
      (positionSplitCoordinates x).2 ^ 2 := by
  change ‖x‖ ^ 2 = ‖(positionSplitIsometry x).fst‖ ^ 2 + (positionSplitIsometry x).snd ^ 2
  have h := WithLp.prod_norm_sq_eq_of_L2 (positionSplitIsometry x)
  rw [positionSplitIsometry.norm_map] at h
  simpa only [Real.norm_eq_abs, sq_abs] using h

end ContinuumCoulomb

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombInverseFifth
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inverse-fifth-power tail is integrable in three dimensions, with the
exact inverse-square dependence needed when summing far-cell errors. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

private theorem inverseFifthRadial_weight {r : ℝ} (hr : 0 < r) (t : ℝ) :
    t^2*inverseFifthRadial r t = (Set.Ioi r).indicator (fun t => t^(-3:ℝ)) t := by
  by_cases ht : r < t
  · simp only [inverseFifthRadial,Set.indicator_of_mem (Set.mem_Ioi.mpr ht)]
    have hp : 0 < t := hr.trans ht
    rw [show (-3:ℝ) = 2+(-5) by norm_num,Real.rpow_add hp,Real.rpow_two]
  · simp [inverseFifthRadial,ht]

private theorem inverseFifthRadial_weight_integrable {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t^2*inverseFifthRadial r t) (Set.Ioi 0) := by
  have hi := integrableOn_Ioi_rpow_of_lt (by norm_num : (-3:ℝ) < -1) hr
  have h := (integrable_indicator_iff measurableSet_Ioi).mpr hi
  simpa only [inverseFifthRadial_weight hr] using h.integrableOn

private theorem inverseFifthRadial_weight_integral {r : ℝ} (hr : 0 < r) :
    (∫ t in Set.Ioi (0:ℝ), t^2*inverseFifthRadial r t) = 1/(2*r^2) := by
  simp_rw [inverseFifthRadial_weight hr]
  rw [integral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi,
    Set.Ioi_inter_Ioi,max_eq_left hr.le]
  have hi := integral_Ioi_rpow_of_lt (by norm_num : (-3:ℝ) < -1) hr
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  norm_num [Real.rpow_neg,Real.rpow_two]
  ring

theorem inverseFifthTail_integrable {r : ℝ} (hr : 0 < r) : Integrable (inverseFifthTail r) := by
  apply (integrable_fun_norm_addHaar (E := Position) volume (f := inverseFifthRadial r)).mpr
  simpa only [finrank_euclideanSpace_fin,Nat.reduceSub,smul_eq_mul] using
    inverseFifthRadial_weight_integrable hr

theorem inverseFifthTail_integral {r : ℝ} (hr : 0 < r) :
    (∫ x : Position, inverseFifthTail r x) = 2*Real.pi/r^2 := by
  change (∫ x : Position, inverseFifthRadial r ‖x‖) = _
  rw [integral_fun_norm_addHaar volume]
  simp only [finrank_euclideanSpace_fin,Nat.reduceSub,smul_eq_mul]
  rw [inverseFifthRadial_weight_integral hr]
  simp only [Measure.real,EuclideanSpace.volume_ball_fin_three,ENNReal.ofReal_one,one_pow,
    one_mul,ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi*4/3),nsmul_eq_mul]
  norm_num [Position,finrank_euclideanSpace_fin]
  ring

theorem inverseFifthTail_of_gt {r : ℝ} (x : Position) (hx : r < ‖x‖) :
    inverseFifthTail r x = ‖x‖^(-5:ℝ) := by
  unfold inverseFifthTail inverseFifthRadial
  exact Set.indicator_of_mem (Set.mem_Ioi.mpr hx) _

theorem inverseFifthTail_nonneg (r : ℝ) (x : Position) : 0 ≤ inverseFifthTail r x := by
  by_cases hx : r < ‖x‖
  · rw [inverseFifthTail_of_gt x hx]
    exact Real.rpow_nonneg (norm_nonneg x) _
  · simp [inverseFifthTail,inverseFifthRadial,hx]

theorem inverseFifthTail_eq_inv_pow {r : ℝ} (x : Position) (hx : r < ‖x‖) :
    inverseFifthTail r x = 1/‖x‖^5 := by
  rw [inverseFifthTail_of_gt x hx]
  simp

theorem inverseFifthTail_measurable (r : ℝ) : Measurable (inverseFifthTail r) := by
  have he : inverseFifthTail r = {x : Position | r < ‖x‖}.indicator (fun x => 1/‖x‖^5) := by
    funext x
    by_cases hx : r < ‖x‖
    · rw [inverseFifthTail_eq_inv_pow x hx,
        Set.indicator_of_mem (show x ∈ {x : Position | r < ‖x‖} from hx)]
    · simp [inverseFifthTail,inverseFifthRadial,hx]
  rw [he]
  exact (measurable_const.div (continuous_norm.measurable.pow_const 5)).indicator
    (isOpen_lt continuous_const continuous_norm).measurableSet

theorem inverseFifthTail_le {r : ℝ} (hr : 0 < r) (x : Position) :
    inverseFifthTail r x ≤ 1/r^5 := by
  by_cases hx : r < ‖x‖
  · rw [inverseFifthTail_eq_inv_pow x hx]
    exact one_div_le_one_div_of_le (pow_pos hr 5) (pow_le_pow_left₀ hr.le hx.le 5)
  · have he : inverseFifthTail r x = 0 := by simp [inverseFifthTail,inverseFifthRadial,hx]
    rw [he]
    positivity

theorem translatedInverseFifth_integrable (y : Position) {r : ℝ} (hr : 0 < r) :
    Integrable (fun x => inverseFifthTail r (y-x)) :=
  (volume.measurePreserving_sub_left y).integrable_comp_of_integrable
    (inverseFifthTail_integrable hr)

theorem translatedInverseFifth_integral (y : Position) {r : ℝ} (hr : 0 < r) :
    (∫ x, inverseFifthTail r (y-x)) = 2*Real.pi/r^2 := by
  rw [integral_sub_left_eq_self,inverseFifthTail_integral hr]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_MoserIntegralBound
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform integral domination for the actual Moser flow. In particular,
the transported inverse-fifth tail keeps its inverse-square integral bound. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem transportedInverseFifth_integrableOn {H S r : ℝ}
    (hH : 0 ≤ H) (hS : 0 ≤ S) (hr : 0 < r)
    (G : Position → Position) (hG : Continuous G) (y : Position) :
    IntegrableOn (fun x => inverseFifthTail r (y-G x)) (slabDomain H S) := by
  apply IntegrableOn.of_bound (slabDomain_isCompact hH hS).measure_lt_top
    (((inverseFifthTail_measurable r).comp (continuous_const.sub hG).measurable).aestronglyMeasurable.restrict)
    (1/r^5)
  exact Filter.Eventually.of_forall (fun x => by
    change ‖inverseFifthTail r (y-G x)‖ ≤ 1/r^5
    rw [Real.norm_of_nonneg (inverseFifthTail_nonneg _ _)]
    exact inverseFifthTail_le hr _)

theorem moser_nonnegative_integral_bound (hpublished : PublishedC4FlowInput)
    {rho H S : ℝ} (hrho : 0 < rho) (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    (hsupport : tsupport V ⊆ slabDomain H S)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow (moserVelocity rho V) G)
    (hbij : Function.Bijective (fun x => G x 1))
    (hfix : ∀ x, x ∉ tsupport V → G x 1 = x)
    (f : Position → ℝ) (hf : Integrable f) (hpos : ∀ x, 0 ≤ f x) :
    (∫ x in slabDomain H S, f (G x 1)) ≤ (3/2:ℝ)*(∫ x, f x) := by
  have hs := (slabDomain_isClosed H S).measurableSet
  have hb := synthesizedDensity_bounds hrho.le V hsupport hbound
  have hm : Measurable (synthesizedDensity rho H S V) :=
    (measurable_const.indicator hs).add
      (manufacturedCharge_continuous V (hV.of_le (by norm_num))).measurable
  have hi : Integrable (fun x => synthesizedDensity rho H S V x*f x) :=
    hf.bdd_mul (c := 3*rho/2) hm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => by rw [Real.norm_of_nonneg (hb x).1]; exact (hb x).2))
  have htrans := moser_density_integral hpublished hrho V hV hbound hsupport G hG hbij hfix f
  have he : rho*(∫ x in slabDomain H S, f (G x 1)) ≤ (3*rho/2)*(∫ x, f x) := by
    calc
      _ = ∫ x in slabDomain H S, synthesizedDensity rho H S V x*f x := htrans.symm
      _ ≤ ∫ x in slabDomain H S, (3*rho/2)*f x :=
        setIntegral_mono_on hi.integrableOn (hf.const_mul _).integrableOn hs
          (fun x _ => mul_le_mul_of_nonneg_right (hb x).2 (hpos x))
      _ ≤ ∫ x, (3*rho/2)*f x :=
        setIntegral_le_integral (hf.const_mul _)
          (Filter.Eventually.of_forall (fun x => mul_nonneg (by positivity) (hpos x)))
      _ = _ := integral_const_mul _ _
  apply (mul_le_mul_iff_right₀ hrho).mp
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem moser_inverseFifth_tail_bound (hpublished : PublishedC4FlowInput)
    {rho H S : ℝ} (hrho : 0 < rho) (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    (hsupport : tsupport V ⊆ slabDomain H S)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow (moserVelocity rho V) G)
    (hbij : Function.Bijective (fun x => G x 1))
    (hfix : ∀ x, x ∉ tsupport V → G x 1 = x)
    (y : Position) {r : ℝ} (hr : 0 < r) :
    (∫ x in slabDomain H S, inverseFifthTail r (y-G x 1)) ≤ 3*Real.pi/r^2 := by
  have he := moser_nonnegative_integral_bound hpublished hrho V hV hbound hsupport G hG hbij hfix
    (fun x => inverseFifthTail r (y-x)) (translatedInverseFifth_integrable y hr)
    (fun x => inverseFifthTail_nonneg r (y-x))
  rw [translatedInverseFifth_integral y hr] at he
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_MoserIntegrability
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.Coulomb.complexWindow_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrability across the transported Coulomb pole follows from the
actual Jacobian identity, including a uniform lower bound on the Jacobian. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem moser_flowJacobian_lower (hpublished : PublishedC4FlowInput)
    {rho : ℝ} (hrho : 0 < rho) (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow (moserVelocity rho V) G)
    (x : Position) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (2/3:ℝ) ≤ flowJacobian G t x := by
  have he := moser_density_jacobian hpublished hrho V hV hbound G hG x ht
  have hp := moser_flowJacobian_pos hpublished hrho V hV hbound G hG x ht
  have hb := (homotopyDensity_bounds V hbound ht.1 ht.2 (G x t)).2
  have hm := mul_le_mul_of_nonneg_right hb hp.le
  nlinarith

theorem moser_integrableOn_comp (hpublished : PublishedC4FlowInput)
    {rho H S : ℝ} (hrho : 0 < rho) (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    (hsupport : tsupport V ⊆ slabDomain H S)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow (moserVelocity rho V) G)
    (hbij : Function.Bijective (fun x => G x 1))
    (hfix : ∀ x, x ∉ tsupport V → G x 1 = x)
    (f : Position → ℝ) (hf : Measurable f) (hi : IntegrableOn f (slabDomain H S)) :
    IntegrableOn (fun x => f (G x 1)) (slabDomain H S) := by
  have h1 : (1:ℝ) ∈ Set.Icc 0 1 := ⟨by norm_num,le_rfl⟩
  have hreg := (moser_flow_C4 hpublished hrho V hV hbound G hG).1 1 h1
  have himage := moser_time_one_preserves_slab V hsupport (fun x => G x 1) hbij hfix
  have he := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
    (μ := volume) (slabDomain_isClosed H S).measurableSet
    (fun x (_hx : x ∈ slabDomain H S) =>
      (hreg.differentiable (by norm_num) x).hasFDerivAt.hasFDerivWithinAt)
    hbij.1.injOn f
  rw [himage] at he
  have hw := he.mp hi
  apply (hw.norm.const_mul (3/2:ℝ)).mono'
    ((hf.comp hreg.continuous.measurable).aestronglyMeasurable.restrict)
  exact Filter.Eventually.of_forall (fun x => by
    change ‖f (G x 1)‖ ≤ (3/2:ℝ)*‖|flowJacobian G 1 x| • f (G x 1)‖
    rw [norm_smul,Real.norm_of_nonneg (abs_nonneg _),
      abs_of_pos (moser_flowJacobian_pos hpublished hrho V hV hbound G hG x h1)]
    have hb := moser_flowJacobian_lower hpublished hrho V hV hbound G hG x h1
    nlinarith [norm_nonneg (f (G x 1))])

theorem moser_truncatedCoulomb_integrable (hpublished : PublishedC4FlowInput)
    {rho H S : ℝ} (hrho : 0 < rho) (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    (hsupport : tsupport V ⊆ slabDomain H S)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow (moserVelocity rho V) G)
    (hbij : Function.Bijective (fun x => G x 1))
    (hfix : ∀ x, x ∉ tsupport V → G x 1 = x) (y : Position) (r : ℝ) :
    IntegrableOn (fun x => Coulomb.truncatedCoulomb r (y-G x 1)) (slabDomain H S) := by
  apply moser_integrableOn_comp hpublished hrho V hV hbound hsupport G hG hbij hfix
    (fun x => Coulomb.truncatedCoulomb r (y-x))
  · exact ((Coulomb.coulombKernel_measurable.indicator measurableSet_ball).comp
      (continuous_const.sub continuous_id).measurable)
  · exact ((Coulomb.truncatedCoulomb_integrable r).comp_sub_left y).integrableOn

theorem moser_truncatedCoulomb_bound (hpublished : PublishedC4FlowInput)
    {rho H S : ℝ} (hrho : 0 < rho) (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    (hsupport : tsupport V ⊆ slabDomain H S)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow (moserVelocity rho V) G)
    (hbij : Function.Bijective (fun x => G x 1))
    (hfix : ∀ x, x ∉ tsupport V → G x 1 = x) (y : Position) {r : ℝ} (hr : 0 ≤ r) :
    (∫ x in slabDomain H S, Coulomb.truncatedCoulomb r (y-G x 1)) ≤ 3*Real.pi*r^2 := by
  have he := moser_nonnegative_integral_bound hpublished hrho V hV hbound hsupport G hG hbij hfix
    (fun x => Coulomb.truncatedCoulomb r (y-x))
    ((Coulomb.truncatedCoulomb_integrable r).comp_sub_left y)
    (fun x => Coulomb.truncatedCoulomb_nonneg r (y-x))
  rw [integral_sub_left_eq_self,Coulomb.truncatedCoulomb_integral hr] at he
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem moser_coulomb_integrableOn (hpublished : PublishedC4FlowInput)
    {rho H S : ℝ} (hrho : 0 < rho) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    (hsupport : tsupport V ⊆ slabDomain H S)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow (moserVelocity rho V) G)
    (hbij : Function.Bijective (fun x => G x 1))
    (hfix : ∀ x, x ∉ tsupport V → G x 1 = x) (y : Position) :
    IntegrableOn (fun x => Coulomb.coulombKernel (y-G x 1)) (slabDomain H S) := by
  have ht := moser_truncatedCoulomb_integrable hpublished hrho V hV hbound hsupport
    G hG hbij hfix y 1
  have hc : IntegrableOn (fun _ : Position => (1:ℝ)) (slabDomain H S) :=
    integrableOn_const ((slabDomain_isCompact hH hS).measure_lt_top (μ := volume)).ne
  have hreg := (moser_flow_C4 hpublished hrho V hV hbound G hG).1 1 ⟨by norm_num,le_rfl⟩
  apply (ht.add hc).mono'
    ((Coulomb.coulombKernel_measurable.comp
      (continuous_const.sub hreg.continuous).measurable).aestronglyMeasurable.restrict)
  exact Filter.Eventually.of_forall (fun x => by
    change ‖Coulomb.coulombKernel (y-G x 1)‖ ≤ Coulomb.truncatedCoulomb 1 (y-G x 1)+1
    rw [Real.norm_of_nonneg (Coulomb.coulombKernel_nonneg _)]
    simpa only [one_mul,mul_one,inv_one] using
      Coulomb.coulomb_integrand_bound (f := fun _ => (1:ℝ))
        (fun _ => zero_le_one) (fun _ => le_rfl) (by norm_num : (0:ℝ) < 1) y (G x 1))

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

theorem slabTripleEquiv_apply (x : Position) : slabTripleEquiv x = (x 0, x 1, x 2) := rfl

theorem slabTripleEquiv_symm_apply (p : SlabTriple) :
    slabTripleEquiv.symm p = WithLp.toLp 2 ![p.1, p.2.1, p.2.2] := by
  ext a
  fin_cases a <;> rfl

theorem slabTripleEquiv_measurePreserving : MeasurePreserving slabTripleEquiv := by
  exact ((MeasurePreserving.id volume).prod
    (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ))).comp
      ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).comp
        (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CubeGeometry
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual Euclidean mesh cells: volume, radius, node containment, and
disjoint interiors. These retain the volume normalization of the Gauss rule. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem mem_positionCube {x b : Position} {h : ℝ} :
    x ∈ positionCube b h ↔ ∀ i, |x i-b i| ≤ h/2 := by
  change ((fun i => b i-h/2) ≤ WithLp.ofLp x ∧
    WithLp.ofLp x ≤ (fun i => b i+h/2)) ↔ _
  constructor
  · rintro ⟨hl,hu⟩ i
    exact abs_le.mpr ⟨by linarith [hl i],by linarith [hu i]⟩
  · intro hx
    constructor <;> intro i <;> have hi := abs_le.mp (hx i) <;> linarith

theorem mem_positionOpenCube {x b : Position} {h : ℝ} :
    x ∈ positionOpenCube b h ↔ ∀ i, |x i-b i| < h/2 := by
  change (∀ i ∈ Set.univ, x i ∈ Set.Ioo (b i-h/2) (b i+h/2)) ↔ _
  simp only [Set.mem_univ,true_implies,Set.mem_Ioo]
  constructor
  · intro hx i
    exact abs_lt.mpr ⟨by linarith [(hx i).1],by linarith [(hx i).2]⟩
  · intro hx i
    have hi := abs_lt.mp (hx i)
    constructor <;> linarith

theorem positionCube_isClosed (b : Position) (h : ℝ) : IsClosed (positionCube b h) :=
  isClosed_Icc.preimage (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ))

theorem positionOpenCube_measurable (b : Position) (h : ℝ) :
    MeasurableSet (positionOpenCube b h) :=
  (MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)).preimage
    (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ)).measurable

theorem positionOpenCube_subset (b : Position) (h : ℝ) :
    positionOpenCube b h ⊆ positionCube b h := by
  intro x hx
  exact mem_positionCube.mpr (fun i => (mem_positionOpenCube.mp hx i).le)

theorem positionCube_volume (b : Position) {h : ℝ} (hh : 0 ≤ h) :
    volume.real (positionCube b h) = h^3 := by
  have he := (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
    (s := Set.Icc (fun i => b i-h/2) (fun i => b i+h/2)) measurableSet_Icc.nullMeasurableSet
  unfold positionCube Measure.real
  rw [he,Real.volume_Icc_pi_toReal (by intro i; linarith)]
  simp only [show ∀ i : Fin 3, b i+h/2-(b i-h/2) = h by intro; ring]
  simp

theorem positionOpenCube_volume (b : Position) {h : ℝ} (hh : 0 ≤ h) :
    volume.real (positionOpenCube b h) = h^3 := by
  have he := (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
    (s := Set.univ.pi (fun i => Set.Ioo (b i-h/2) (b i+h/2)))
    (MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)).nullMeasurableSet
  unfold positionOpenCube Measure.real
  rw [he,Real.volume_pi_Ioo_toReal (by intro i; linarith)]
  simp only [show ∀ i : Fin 3, b i+h/2-(b i-h/2) = h by intro; ring]
  simp

theorem positionOpenCube_ae_eq (b : Position) (h : ℝ) :
    positionOpenCube b h =ᵐ[volume] positionCube b h := by
  have he := Measure.univ_pi_Ioo_ae_eq_Icc
    (μ := fun _ : Fin 3 => (volume : Measure ℝ))
    (f := fun i => b i-h/2) (g := fun i => b i+h/2)
  exact (PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae he

theorem cubePoint_mem_positionCube (b : Position) {h : ℝ} (hh : 0 ≤ h)
    {x y z : ℝ} (hx : x ∈ Set.Icc (-1:ℝ) 1)
    (hy : y ∈ Set.Icc (-1:ℝ) 1) (hz : z ∈ Set.Icc (-1:ℝ) 1) :
    cubePoint b (h/2) x y z ∈ positionCube b h := by
  rw [mem_positionCube]
  intro i
  have he : cubePoint b (h/2) x y z i-b i = (h/2)*(![x,y,z] i) := by
    fin_cases i <;> simp [cubePoint] <;> ring
  rw [he,abs_mul,abs_of_nonneg (by positivity : 0 ≤ h/2)]
  apply (mul_le_mul_of_nonneg_left (show |![x,y,z] i| ≤ 1 from ?_) (by positivity)).trans_eq
    (mul_one _)
  fin_cases i
  · exact abs_le.mpr hx
  · exact abs_le.mpr hy
  · exact abs_le.mpr hz

theorem positionCube_norm_sub_le {b x : Position} {h : ℝ} (hh : 0 ≤ h)
    (hx : x ∈ positionCube b h) : ‖x-b‖ ≤ h := by
  have hi := mem_positionCube.mp hx
  have hs : ‖x-b‖^2 ≤ 3*(h/2)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin 3, (h/2)^2 := by
        apply Finset.sum_le_sum
        intro i _
        change (x i-b i)^2 ≤ _
        nlinarith [abs_le.mp (hi i),sq_abs (x i-b i)]
      _ = _ := by simp
  nlinarith [norm_nonneg (x-b)]

theorem positionCube_isCompact (b : Position) {h : ℝ} (hh : 0 ≤ h) :
    IsCompact (positionCube b h) := by
  apply (isCompact_closedBall b h).of_isClosed_subset (positionCube_isClosed b h)
  intro x hx
  exact positionCube_norm_sub_le hh hx

theorem positionCube_diameter_bound {b x y : Position} {h : ℝ} (hh : 0 ≤ h)
    (hx : x ∈ positionCube b h) (hy : y ∈ positionCube b h) : ‖x-y‖ ≤ 2*h := by
  have ht := norm_sub_le_norm_sub_add_norm_sub x b y
  rw [norm_sub_rev b y] at ht
  linarith [positionCube_norm_sub_le hh hx,positionCube_norm_sub_le hh hy]

theorem grid_openCubes_disjoint {h : ℝ} (hh : 0 < h) {k l : Fin 3 → ℤ} (hkl : k ≠ l) :
    Disjoint (positionOpenCube (gaussCellCenter h k) h)
      (positionOpenCube (gaussCellCenter h l) h) := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hkl
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hx := abs_lt.mp (mem_positionOpenCube.mp hx i)
  have hy := abs_lt.mp (mem_positionOpenCube.mp hy i)
  change -(h/2) < x i-h*(k i:ℝ) ∧ x i-h*(k i:ℝ) < h/2 at hx
  change -(h/2) < x i-h*(l i:ℝ) ∧ x i-h*(l i:ℝ) < h/2 at hy
  rcases lt_or_gt_of_ne hi with hi | hi
  · have hd : (k i:ℝ)+1 ≤ l i := by exact_mod_cast (show k i+1 ≤ l i by omega)
    nlinarith [mul_le_mul_of_nonneg_left hd hh.le]
  · have hd : (l i:ℝ)+1 ≤ k i := by exact_mod_cast (show l i+1 ≤ k i by omega)
    nlinarith [mul_le_mul_of_nonneg_left hd hh.le]

theorem grid_cell_integral_sum_le_on {ι : Type*} [Fintype ι]
    (index : ι → Fin 3 → ℤ) (hindex : Function.Injective index)
    {h : ℝ} (hh : 0 < h) {B : Set Position}
    (hsub : ∀ i, positionCube (gaussCellCenter h (index i)) h ⊆ B)
    (f : Position → ℝ) (hf : IntegrableOn f B) (hpos : ∀ x, 0 ≤ f x) :
    (∑ i, ∫ x in positionCube (gaussCellCenter h (index i)) h, f x) ≤
      ∫ x in B, f x := by
  have ho (i : ι) : positionOpenCube (gaussCellCenter h (index i)) h ⊆ B :=
    (positionOpenCube_subset _ _).trans (hsub i)
  have he (i : ι) := setIntegral_congr_set
    (f := f) (positionOpenCube_ae_eq (gaussCellCenter h (index i)) h)
  simp_rw [← he]
  rw [← integral_iUnion_fintype
    (fun i => positionOpenCube_measurable (gaussCellCenter h (index i)) h)
    (fun i j hij => grid_openCubes_disjoint hh (fun he => hij (hindex he)))
    (fun i => hf.mono_set (ho i))]
  exact setIntegral_mono_set hf (Filter.Eventually.of_forall hpos)
    (Filter.Eventually.of_forall (Set.iUnion_subset ho))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CubeIntegral
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized tensor cell integral is the ordinary Euclidean volume
integral on the translated cube, with no change of volume convention. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem cubeTripleBox_measurable (b : Position) (h : ℝ) :
    MeasurableSet (cubeTripleBox b h) :=
  measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc)

theorem cubeTripleBox_preimage (b : Position) (h : ℝ) :
    slabTripleEquiv ⁻¹' cubeTripleBox b h = positionCube b h := by
  ext x
  simp only [Set.mem_preimage,cubeTripleBox,slabTripleEquiv_apply,Set.mem_prod,
    Set.mem_Icc,mem_positionCube]
  constructor
  · rintro ⟨h0,h1,h2⟩ i
    fin_cases i
    · change |x 0-b 0| ≤ h/2
      exact abs_le.mpr ⟨by linarith [h0.1],by linarith [h0.2]⟩
    · change |x 1-b 1| ≤ h/2
      exact abs_le.mpr ⟨by linarith [h1.1],by linarith [h1.2]⟩
    · change |x 2-b 2| ≤ h/2
      exact abs_le.mpr ⟨by linarith [h2.1],by linarith [h2.2]⟩
  · intro hx
    have h0 := abs_le.mp (hx 0)
    have h1 := abs_le.mp (hx 1)
    have h2 := abs_le.mp (hx 2)
    exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩,
      ⟨by linarith,by linarith⟩⟩

theorem cube_setIntegral_triple (b : Position) (h : ℝ) (f : Position → ℝ) :
    (∫ x in positionCube b h, f x) =
      ∫ p in cubeTripleBox b h, f (slabTripleEquiv.symm p) := by
  have hm := slabTripleEquiv_measurePreserving.restrict_preimage (cubeTripleBox_measurable b h)
  rw [cubeTripleBox_preimage] at hm
  simpa only [Function.comp_apply,MeasurableEquiv.symm_apply_apply] using
    hm.integral_comp' (f ∘ slabTripleEquiv.symm)

theorem centered_interval_integral (c h : ℝ) (f : ℝ → ℝ) :
    (h/2)*(∫ t : ℝ in (-1)..1, f (c+h/2*t)) =
      ∫ t : ℝ in (c-h/2)..(c+h/2), f t := by
  have he := intervalIntegral.smul_integral_comp_add_mul
    (f := f) (a := (-1:ℝ)) (b := 1) (h/2) c
  simpa only [smul_eq_mul,mul_neg_one,mul_one,← sub_eq_add_neg] using he

theorem centered_triple_integral (c₀ c₁ c₂ h : ℝ) (f : ℝ → ℝ → ℝ → ℝ) :
    (h/2)^3*(∫ x : ℝ in (-1)..1, ∫ y : ℝ in (-1)..1, ∫ z : ℝ in (-1)..1,
      f (c₀+h/2*x) (c₁+h/2*y) (c₂+h/2*z)) =
      ∫ x : ℝ in (c₀-h/2)..(c₀+h/2),
        ∫ y : ℝ in (c₁-h/2)..(c₁+h/2),
          ∫ z : ℝ in (c₂-h/2)..(c₂+h/2), f x y z := by
  let d := h/2
  have hz (x y : ℝ) : d*(∫ z : ℝ in (-1)..1, f x y (c₂+d*z)) =
      ∫ z : ℝ in (c₂-d)..(c₂+d), f x y z := centered_interval_integral c₂ h (f x y)
  have hy (x : ℝ) : d^2*(∫ y : ℝ in (-1)..1, ∫ z : ℝ in (-1)..1,
      f x (c₁+d*y) (c₂+d*z)) =
      ∫ y : ℝ in (c₁-d)..(c₁+d), ∫ z : ℝ in (c₂-d)..(c₂+d), f x y z := by
    calc
      _ = d*(∫ y : ℝ in (-1)..1, d*(∫ z : ℝ in (-1)..1, f x (c₁+d*y) (c₂+d*z))) := by
        rw [intervalIntegral.integral_const_mul]
        ring
      _ = d*(∫ y : ℝ in (-1)..1, ∫ z : ℝ in (c₂-d)..(c₂+d), f x (c₁+d*y) z) := by
        simp_rw [hz]
      _ = _ := centered_interval_integral c₁ h (fun y => ∫ z : ℝ in (c₂-d)..(c₂+d), f x y z)
  change d^3*_ = _
  calc
    _ = d*(∫ x : ℝ in (-1)..1, d^2*(∫ y : ℝ in (-1)..1,
        ∫ z : ℝ in (-1)..1, f (c₀+d*x) (c₁+d*y) (c₂+d*z))) := by
      rw [intervalIntegral.integral_const_mul]
      ring
    _ = d*(∫ x : ℝ in (-1)..1, ∫ y : ℝ in (c₁-d)..(c₁+d),
        ∫ z : ℝ in (c₂-d)..(c₂+d), f (c₀+d*x) y z) := by simp_rw [hy]
    _ = _ := centered_interval_integral c₀ h
      (fun x => ∫ y : ℝ in (c₁-d)..(c₁+d), ∫ z : ℝ in (c₂-d)..(c₂+d), f x y z)

theorem positionCellIntegral_eq_setIntegral (b : Position) {h : ℝ} (hh : 0 ≤ h)
    (f : Position → ℝ) (hf : IntegrableOn f (positionCube b h)) :
    positionCellIntegral b h f = ∫ x in positionCube b h, f x := by
  let F : SlabTriple → ℝ := fun p => f (slabTripleEquiv.symm p)
  have hm := slabTripleEquiv_measurePreserving.restrict_preimage (cubeTripleBox_measurable b h)
  rw [cubeTripleBox_preimage] at hm
  have hF : IntegrableOn F (cubeTripleBox b h) :=
    (hm.integrable_comp_emb slabTripleEquiv.measurableEmbedding).mp
      (by simpa only [IntegrableOn,F,Function.comp_def,MeasurableEquiv.symm_apply_apply] using hf)
  have ht : (∫ p in cubeTripleBox b h, F p) =
      ∫ x in Set.Icc (b 0-h/2) (b 0+h/2),
        ∫ y in Set.Icc (b 1-h/2) (b 1+h/2),
          ∫ z in Set.Icc (b 2-h/2) (b 2+h/2), F (x,y,z) := by
    rw [cubeTripleBox,Measure.volume_eq_prod] at hF ⊢
    rw [setIntegral_prod _ hF]
    apply integral_congr_ae
    have hFa := hF
    rw [IntegrableOn,← Measure.prod_restrict] at hFa
    filter_upwards [hFa.prod_right_ae] with x hx
    exact setIntegral_prod _ hx
  rw [cube_setIntegral_triple,ht]
  have hi (i : Fin 3) : b i-h/2 ≤ b i+h/2 := by linarith
  have he (x y z : ℝ) : cubePoint b (h/2) x y z =
      slabTripleEquiv.symm (b 0+h/2*x,b 1+h/2*y,b 2+h/2*z) := by
    rw [slabTripleEquiv_symm_apply]
    ext i
    fin_cases i <;> simp [cubePoint] <;> ring
  unfold positionCellIntegral
  simp_rw [he]
  rw [centered_triple_integral (b 0) (b 1) (b 2) h
    (fun x y z => f (slabTripleEquiv.symm (x,y,z)))]
  simp_rw [intervalIntegral.integral_of_le (hi _),← integral_Icc_eq_integral_Ioc]
  rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CenteredGrid
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete finite family of lattice cubes tiles the enclosing rectangular
slab, including its boundary. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem grid_cell_integral_sum_eq {ι : Type*} [Fintype ι]
    (index : ι → Fin 3 → ℤ) (hindex : Function.Injective index)
    {h : ℝ} (hh : 0 < h) {B : Set Position}
    (hcover : (⋃ i, positionCube (gaussCellCenter h (index i)) h) = B)
    (f : Position → ℝ) (hf : IntegrableOn f B) :
    (∑ i, ∫ x in positionCube (gaussCellCenter h (index i)) h, f x) = ∫ x in B, f x := by
  have he (i : ι) := positionOpenCube_ae_eq (gaussCellCenter h (index i)) h
  have hsets : (⋃ i, positionOpenCube (gaussCellCenter h (index i)) h) =ᵐ[volume]
      (⋃ i, positionCube (gaussCellCenter h (index i)) h) := by
    filter_upwards [ae_all_iff.mpr he] with x hx
    show (x ∈ ⋃ i, positionOpenCube (gaussCellCenter h (index i)) h) =
      (x ∈ ⋃ i, positionCube (gaussCellCenter h (index i)) h)
    simp only [Set.mem_iUnion]
    exact propext (exists_congr fun i => (hx i).to_iff)
  have hi (i : ι) : IntegrableOn f (positionOpenCube (gaussCellCenter h (index i)) h) := by
    apply hf.mono_set
    intro x hx
    rw [← hcover]
    exact Set.mem_iUnion.mpr ⟨i,positionOpenCube_subset _ _ hx⟩
  calc
    _ = ∑ i, ∫ x in positionOpenCube (gaussCellCenter h (index i)) h, f x := by
      apply Finset.sum_congr rfl
      intro i _
      exact (setIntegral_congr_set (he i)).symm
    _ = ∫ x in ⋃ i, positionOpenCube (gaussCellCenter h (index i)) h, f x :=
      (integral_iUnion_fintype (fun i => positionOpenCube_measurable _ _)
        (fun i j hij => grid_openCubes_disjoint hh (fun he => hij (hindex he))) hi).symm
    _ = ∫ x in ⋃ i, positionCube (gaussCellCenter h (index i)) h, f x :=
      setIntegral_congr_set hsets
    _ = _ := by rw [hcover]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_MoserGridPotential
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.Coulomb.complexWindow_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact identification of the continuous part of the finite transported
cubature with the manufactured slab-plus-well potential. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem moser_grid_potential (hpublished : PublishedC4FlowInput)
    {rho H S h : ℝ} (hrho : 0 < rho) (hH : 0 ≤ H) (hS : 0 ≤ S) (hh : 0 < h)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V) (hc : HasCompactSupport V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    (hsupport : tsupport V ⊆ slabDomain H S)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow (moserVelocity rho V) G)
    (hbij : Function.Bijective (fun x => G x 1))
    (hfix : ∀ x, x ∉ tsupport V → G x 1 = x)
    {ι : Type*} [Fintype ι] (index : ι → Fin 3 → ℤ) (hindex : Function.Injective index)
    (hcover : (⋃ i, positionCube (gaussCellCenter h (index i)) h) = slabDomain H S)
    (y : Position) :
    -rho*(∑ i, positionCellIntegral (gaussCellCenter h (index i)) h
      (fun x => Coulomb.coulombKernel (y-G x 1))) = slabPotential rho H S y+V y := by
  have hsub (i : ι) : positionCube (gaussCellCenter h (index i)) h ⊆ slabDomain H S := by
    rw [← hcover]
    exact Set.subset_iUnion_of_subset i (fun _ hx => hx)
  have hi := moser_coulomb_integrableOn hpublished hrho hH hS V hV hbound hsupport G hG hbij hfix y
  have hsum : (∑ i, positionCellIntegral (gaussCellCenter h (index i)) h
      (fun x => Coulomb.coulombKernel (y-G x 1))) =
      ∫ x in slabDomain H S, Coulomb.coulombKernel (y-G x 1) := by
    simp_rw [positionCellIntegral_eq_setIntegral _ hh.le _ (hi.mono_set (hsub _))]
    exact grid_cell_integral_sum_eq index hindex hh hcover _ hi
  have htrans := moser_density_integral hpublished hrho V hV hbound hsupport G hG hbij hfix
    (fun x => Coulomb.coulombKernel (y-x))
  have he : (∫ x in slabDomain H S, synthesizedDensity rho H S V x*Coulomb.coulombKernel (y-x)) =
      ∫ x, Coulomb.coulombKernel (y-x)*synthesizedDensity rho H S V x := by
    calc
      _ = ∫ x in slabDomain H S, Coulomb.coulombKernel (y-x)*synthesizedDensity rho H S V x := by
        apply setIntegral_congr_fun (slabDomain_isClosed H S).measurableSet
        intro x _
        ring
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        have hv : x ∉ tsupport V := fun h => hx (hsupport h)
        simp only [synthesizedDensity,slabDensity,Set.indicator_of_notMem hx,
          manufacturedCharge_zero hv,add_zero,mul_zero])
  calc
    _ = -(rho*(∫ x in slabDomain H S, Coulomb.coulombKernel (y-G x 1))) := by rw [hsum]; ring
    _ = -(∫ x in slabDomain H S, synthesizedDensity rho H S V x*Coulomb.coulombKernel (y-x)) :=
      congrArg Neg.neg htrans.symm
    _ = -(∫ x, Coulomb.coulombKernel (y-x)*synthesizedDensity rho H S V x) := congrArg Neg.neg he
    _ = _ := synthesizedDensity_potential hrho.le hH hS V (hV.of_le (by norm_num)) hc hbound y

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_UniformReciprocal
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform four-derivative reciprocal estimate away from zero, used
only for the positive density in the Moser field. -/

noncomputable section
open scoped BigOperators ContDiff
namespace ContinuumCoulomb

private theorem reciprocal_derivatives_bounded {rho : ℝ} (hrho : 0 < rho) :
    ∃ C : ℝ, 0 < C ∧ ∀ k ≤ 4, ∀ y ∈ Set.Icc (rho/2) (3*rho/2),
      ‖iteratedFDeriv ℝ k (fun z : ℝ => z⁻¹) y‖ ≤ C := by
  let T : Set ℝ := {0}ᶜ
  have hT : IsOpen T := isClosed_singleton.isOpen_compl
  have hg : ContDiffOn ℝ 4 (fun z : ℝ => z⁻¹) T :=
    contDiffOn_id.inv (fun z hz => hz)
  have hsub : Set.Icc (rho/2) (3*rho/2) ⊆ T := by
    intro z hz
    exact ne_of_gt (lt_of_lt_of_le (by positivity : 0 < rho/2) hz.1)
  have hb (k : Fin 5) : ∃ A : ℝ, ∀ y ∈ Set.Icc (rho/2) (3*rho/2),
      ‖iteratedFDeriv ℝ k.val (fun z : ℝ => z⁻¹) y‖ ≤ A := by
    have hc : ContinuousOn (iteratedFDeriv ℝ k.val (fun z : ℝ => z⁻¹)) T := by
      apply (hg.continuousOn_iteratedFDerivWithin (by exact_mod_cast (show k.val ≤ 4 by omega))
        hT.uniqueDiffOn).congr
      intro z hz
      exact (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := fun z : ℝ => z⁻¹)
        k.val hT hz).symm
    obtain ⟨A,hA⟩ := isCompact_Icc.bddAbove_image ((hc.mono hsub).norm)
    exact ⟨A, fun y hy => hA ⟨y,hy,rfl⟩⟩
  choose B hB using hb
  let C : ℝ := 1+∑ k : Fin 5, max (B k) 0
  have hn : 0 ≤ ∑ k : Fin 5, max (B k) 0 :=
    Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro k hk y hy
  let i : Fin 5 := ⟨k, by omega⟩
  have hs : max (B i) 0 ≤ ∑ j : Fin 5, max (B j) 0 :=
    Finset.single_le_sum (fun _ _ => le_max_right _ _) (Finset.mem_univ i)
  exact (hB i y hy).trans ((le_max_left _ _).trans (by dsimp [C]; linarith))

/-- The constant depends on the density floor and on the four-derivative
bound, not on the support or the number of wells. -/
theorem uniform_reciprocal_four_bound {rho B : ℝ} (hrho : 0 < rho) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ × Position → ℝ, ContDiff ℝ 4 f →
      ∀ x, f x ∈ Set.Icc (rho/2) (3*rho/2) →
      (∀ j ≤ 4, ‖iteratedFDeriv ℝ j f x‖ ≤ B) →
      ∀ k ≤ 4, ‖iteratedFDeriv ℝ k (fun y => (f y)⁻¹) x‖ ≤ C := by
  obtain ⟨A,hA,hAb⟩ := reciprocal_derivatives_bounded hrho
  let D : ℝ := max 1 B
  refine ⟨24*A*D^4, by dsimp [D]; positivity, ?_⟩
  intro f hf x hx hb k hk
  let U : Set (ℝ × Position) := {y | f y ≠ 0}
  let T : Set ℝ := {0}ᶜ
  have hT : IsOpen T := isClosed_singleton.isOpen_compl
  have hU : IsOpen U := isOpen_ne.preimage hf.continuous
  have hxU : x ∈ U := ne_of_gt (lt_of_lt_of_le (by positivity : 0 < rho/2) hx.1)
  have hg : ContDiffOn ℝ 4 (fun z : ℝ => z⁻¹) T :=
    contDiffOn_id.inv (fun z hz => hz)
  have hcomp := norm_iteratedFDerivWithin_comp_le hg hf.contDiffOn
    (show (k : WithTop ℕ∞) ≤ 4 by exact_mod_cast hk)
    hT.uniqueDiffOn hU.uniqueDiffOn (fun y hy => hy) hxU
    (C := A) (D := D) (fun j hj => by
      rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := fun z : ℝ => z⁻¹)
        j hT (show f x ∈ T from hxU)]
      exact hAb j (hj.trans hk) (f x) hx)
    (fun j hj hjk => by
      rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := f) j hU hxU]
      exact (hb j (hjk.trans hk)).trans ((le_max_right 1 B).trans (by
        simpa only [pow_one] using pow_le_pow_right₀ (le_max_left 1 B) hj)))
  rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
    (f := (fun z : ℝ => z⁻¹) ∘ f) k hU hxU] at hcomp
  apply hcomp.trans
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_right (by
      exact_mod_cast (show k.factorial ≤ 24 from
        (Nat.factorial_le hk).trans (by decide))) hA.le
  · exact pow_le_pow_right₀ (le_max_left 1 B) hk
  · exact pow_nonneg (le_trans zero_le_one (le_max_left 1 B)) k
  · positivity

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_MoserUniformDensity
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform joint density bounds for the actual Moser homotopy. -/

noncomputable section
open scoped BigOperators ContDiff
namespace ContinuumCoulomb

theorem contraction_four_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1) (f : F → ℝ) (hf : ContDiff ℝ 4 f)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ j ≤ 4, ∀ y, ‖iteratedFDeriv ℝ j f y‖ ≤ B)
    {k : ℕ} (hk : k ≤ 4) (x : E) : ‖iteratedFDeriv ℝ k (f ∘ L) x‖ ≤ B := by
  rw [L.iteratedFDeriv_comp_right hf x (by exact_mod_cast hk)]
  have h := (iteratedFDeriv ℝ k f (L x)).norm_compContinuousLinearMap_le (fun _ => L)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  apply h.trans
  exact (mul_le_mul (hb k hk _) (pow_le_one₀ (norm_nonneg L) hL)
    (pow_nonneg (norm_nonneg L) _) hB).trans_eq (mul_one B)

private theorem fst_four_bound {k : ℕ} (x : ℝ × Position) (hx : |x.1| ≤ 1) :
    ‖iteratedFDeriv ℝ k (fun y : ℝ × Position => y.1) x‖ ≤ 1 := by
  cases k with
  | zero => simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hx
  | succ k =>
    rw [← norm_iteratedFDeriv_fderiv]
    change ‖iteratedFDeriv ℝ k (fderiv ℝ (ContinuousLinearMap.fst ℝ ℝ Position)) x‖ ≤ 1
    have hder : fderiv ℝ (ContinuousLinearMap.fst ℝ ℝ Position) =
        fun _ => ContinuousLinearMap.fst ℝ ℝ Position :=
      funext (fun _ => (ContinuousLinearMap.fst ℝ ℝ Position).fderiv)
    rw [hder]
    cases k with
    | zero => simpa only [norm_iteratedFDeriv_zero] using
        (ContinuousLinearMap.norm_fst_le (𝕜 := ℝ) (E := ℝ) (F := Position))
    | succ k => simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero, zero_le_one]

/-- A uniform bound for the four joint derivatives of rho+t*charge. -/
theorem homotopyDensity_uniform_derivatives {rho B : ℝ} (hB : 0 ≤ B)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hb : ∀ k ≤ 6, ∀ x, ‖iteratedFDeriv ℝ k V x‖ ≤ B)
    {k : ℕ} (hk : k ≤ 4) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (x : Position) :
    ‖iteratedFDeriv ℝ k (fun p : ℝ × Position => homotopyDensity rho V p.1 p.2) (t,x)‖ ≤
      |rho|+16*(3*B/(4*Real.pi)) := by
  let C : ℝ := 3*B/(4*Real.pi)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hcharge (j : ℕ) (hj : j ≤ 4) (y : ℝ × Position) :
      ‖iteratedFDeriv ℝ j (fun p : ℝ × Position => manufacturedCharge V p.2) y‖ ≤ C :=
    contraction_four_bound (ContinuousLinearMap.snd ℝ ℝ Position)
      (ContinuousLinearMap.norm_snd_le ℝ ℝ Position) (manufacturedCharge V) (manufacturedCharge_C4 V hV)
      hC (fun j hj z => manufacturedCharge_derivative_bound V hV hB hb hj z) hj y
  have hf : ContDiff ℝ 4 (fun p : ℝ × Position => p.1 * manufacturedCharge V p.2) :=
    contDiff_fst.mul ((manufacturedCharge_C4 V hV).comp contDiff_snd)
  have hprod : ‖iteratedFDeriv ℝ k (fun p : ℝ × Position =>
      p.1*manufacturedCharge V p.2) (t,x)‖ ≤ 16*C := by
    apply (norm_iteratedFDeriv_mul_le contDiff_fst
      ((manufacturedCharge_C4 V hV).comp contDiff_snd) (t,x)
      (show (k : WithTop ℕ∞) ≤ 4 by exact_mod_cast hk)).trans
    calc
      _ ≤ ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ)*C := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        have ht' : |(t,x).1| ≤ 1 := by
          change |t| ≤ 1
          rw [abs_of_nonneg ht.1]
          exact ht.2
        exact (mul_le_mul
          (mul_le_mul_of_nonneg_left (fst_four_bound (k := i) (t,x) ht')
            (Nat.cast_nonneg _))
          (hcharge (k-i) ((Nat.sub_le k i).trans hk) (t,x))
          (norm_nonneg _) (by positivity)).trans_eq (by ring)
      _ = (2:ℝ)^k*C := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose k
      _ ≤ 16*C := mul_le_mul_of_nonneg_right
        ((pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hk).trans_eq (by norm_num)) hC
  change ‖iteratedFDeriv ℝ k (fun p : ℝ × Position =>
    rho + p.1*manufacturedCharge V p.2) (t,x)‖ ≤ _
  rw [fun_iteratedFDeriv_add_apply contDiff_const.contDiffAt
    (hf.of_le (by exact_mod_cast hk)).contDiffAt]
  apply (norm_add_le _ _).trans
  apply add_le_add _ hprod
  cases k with
  | zero => simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, le_refl]
  | succ k => simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero, abs_nonneg]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_MoserUniformVelocity
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Moser velocity and flow have a common derivative bound over all
potentials with a common order-six bound. -/

noncomputable section
open scoped BigOperators ContDiff
namespace ContinuumCoulomb
open NeutralAtom (dirPartial axis)

private theorem product_four_bound (U : Set (ℝ × Position)) (hU : IsOpen U)
    (f g : ℝ × Position → ℝ) (hf : ContDiffOn ℝ 4 f U) (hg : ContDiffOn ℝ 4 g U)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) {x : ℝ × Position} (hx : x ∈ U)
    (hb : ∀ j ≤ 4, ‖iteratedFDeriv ℝ j f x‖ ≤ B)
    (hc : ∀ j ≤ 4, ‖iteratedFDeriv ℝ j g x‖ ≤ C)
    {k : ℕ} (hk : k ≤ 4) :
    ‖iteratedFDeriv ℝ k (fun y => f y*g y) x‖ ≤ 16*B*C := by
  have h := norm_iteratedFDerivWithin_mul_le hf hg hU.uniqueDiffOn hx
    (show (k : WithTop ℕ∞) ≤ 4 by exact_mod_cast hk)
  simp_rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (s := U) _ hU hx] at h
  apply h.trans
  calc
    _ ≤ ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ)*B*C := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hb i (hi'.trans hk)) (Nat.cast_nonneg _))
        (hc (k-i) ((Nat.sub_le k i).trans hk)) (norm_nonneg _) (by positivity)
    _ = (2:ℝ)^k*B*C := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose k
    _ ≤ 16*B*C := by
      apply mul_le_mul_of_nonneg_right _ hC
      apply mul_le_mul_of_nonneg_right _ hB
      exact (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hk).trans_eq (by norm_num)

private theorem partial_C4 (V : Position → ℝ) (hV : ContDiff ℝ 6 V) (a : Fin 3) :
    ContDiff ℝ 4 (dirPartial V (axis a)) :=
  (hV.fderiv_right (by norm_num : (4 : WithTop ℕ∞)+1 ≤ 6)).clm_apply contDiff_const

private theorem partial_joint_bound (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ k ≤ 6, ∀ x, ‖iteratedFDeriv ℝ k V x‖ ≤ B)
    (a : Fin 3) {k : ℕ} (hk : k ≤ 4) (x : ℝ × Position) :
    ‖iteratedFDeriv ℝ k (fun p : ℝ × Position => dirPartial V (axis a) p.2) x‖ ≤ B := by
  apply contraction_four_bound (ContinuousLinearMap.snd ℝ ℝ Position)
    (ContinuousLinearMap.norm_snd_le ℝ ℝ Position) (dirPartial V (axis a)) (partial_C4 V hV a) hB
    (fun j hj y => ?_) hk x
  have h := dirPartial_iterated_norm_bound V hV (axis a) (show j ≤ 5 by omega) y
  have hn : ‖axis a‖ = 1 := by simp [axis]
  rw [hn, one_mul] at h
  exact h.trans (hb (j+1) (by omega) y)

/-- One bound controls all joint velocity derivatives through order four
for the entire bounded family of potentials. -/
theorem moserVelocity_family_derivative_bound {rho B : ℝ} (hrho : 0 < rho) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Position → ℝ), ContDiff ℝ 6 V →
      (∀ k ≤ 6, ∀ x, ‖iteratedFDeriv ℝ k V x‖ ≤ B) →
      (∀ x, |manufacturedCharge V x| ≤ rho/2) →
      ∀ k ≤ 4, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x,
        ‖iteratedFDeriv ℝ k (fun p : ℝ × Position => moserVelocity rho V p.1 p.2) (t,x)‖ ≤ C := by
  let D : ℝ := |rho|+16*(3*B/(4*Real.pi))
  obtain ⟨A,hA,hAb⟩ := uniform_reciprocal_four_bound (B := D) hrho
  refine ⟨48*(B+1)*A/(4*Real.pi), by positivity, ?_⟩
  intro V hV hb hcharge k hk t ht x
  let U := moserDomain rho V
  have hU : IsOpen U := moserDomain_isOpen rho V hV
  have hxU : (t,x) ∈ U := moserDomain_contains_time_slab hrho V hcharge ⟨ht,Set.mem_univ _⟩
  let d : ℝ × Position → ℝ := fun p => homotopyDensity rho V p.1 p.2
  let invd : ℝ × Position → ℝ := fun p => (d p)⁻¹
  have hd : ContDiff ℝ 4 d := homotopyDensity_joint_C4 rho V hV
  have hi : ContDiffOn ℝ 4 invd U := hd.contDiffOn.inv (fun p hp => hp)
  have hiB (j : ℕ) (hj : j ≤ 4) : ‖iteratedFDeriv ℝ j invd (t,x)‖ ≤ A :=
    hAb d hd (t,x) (homotopyDensity_bounds V hcharge ht.1 ht.2 x)
      (fun i hi => homotopyDensity_uniform_derivatives hB V hV hb hi ht x) j hj
  let f : Fin 3 → ℝ × Position → ℝ := fun a p =>
    -(4*Real.pi)⁻¹ * dirPartial V (axis a) p.2
  have hf (a : Fin 3) : ContDiff ℝ 4 (f a) :=
    contDiff_const.mul ((partial_C4 V hV a).comp contDiff_snd)
  have hfB (a : Fin 3) (j : ℕ) (hj : j ≤ 4) :
      ‖iteratedFDeriv ℝ j (f a) (t,x)‖ ≤ B/(4*Real.pi) := by
    change ‖iteratedFDeriv ℝ j (fun p : ℝ × Position =>
      (-(4*Real.pi)⁻¹) • dirPartial V (axis a) p.2) (t,x)‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply'
      (f := fun p : ℝ × Position => dirPartial V (axis a) p.2)
      (a := -(4*Real.pi)⁻¹)
      (((partial_C4 V hV a).comp contDiff_snd).of_le (by exact_mod_cast hj)).contDiffAt,
      norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
    exact (mul_le_mul_of_nonneg_left (partial_joint_bound V hV hB hb a hj (t,x))
      (by positivity)).trans_eq (by ring)
  let F : Fin 3 → ℝ × Position → ℝ := fun a p => f a p * invd p
  have hF (a : Fin 3) : ContDiffOn ℝ 4 (F a) U := (hf a).contDiffOn.mul hi
  have hFB (a : Fin 3) : ‖iteratedFDeriv ℝ k (F a) (t,x)‖ ≤ 16*(B/(4*Real.pi))*A :=
    product_four_bound U hU (f a) invd (hf a).contDiffOn hi
      (by positivity) hA.le hxU (hfB a) hiB hk
  let L : Fin 3 → ℝ →L[ℝ] Position := fun a =>
    (ContinuousLinearMap.id ℝ ℝ).smulRight (axis a)
  have hL (a : Fin 3) : ‖L a‖ = 1 := by
    simp [L, ContinuousLinearMap.norm_smulRight_apply, axis]
  have hsum : (fun p : ℝ × Position => moserVelocity rho V p.1 p.2) =
      fun p => ∑ a : Fin 3, L a (F a p) := by
    funext p
    ext a
    simp [moserVelocity, L, F, f, invd, d, axis, Pi.single_apply, eq_comm, div_eq_mul_inv, mul_inv_rev, mul_assoc]; ring
  rw [hsum, iteratedFDeriv_fun_sum_apply
    (f := fun a p => L a (F a p)) (fun a _ =>
    (((L a).contDiff.comp_contDiffOn (hF a)).contDiffAt (hU.mem_nhds hxU)).of_le
      (show (k : WithTop ℕ∞) ≤ 4 by exact_mod_cast hk))]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _a : Fin 3, 16*(B/(4*Real.pi))*A := by
      apply Finset.sum_le_sum
      intro a _
      have h := (L a).norm_iteratedFDeriv_comp_left
        ((hF a).contDiffAt (hU.mem_nhds hxU))
        (show (k : WithTop ℕ∞) ≤ 4 by exact_mod_cast hk)
      rw [hL, one_mul] at h
      exact h.trans (hFB a)
    _ ≤ 48*(B+1)*A/(4*Real.pi) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
      have hp : 0 < 4*Real.pi := by positivity
      apply (le_div_iff₀ hp).mpr
      field_simp
      nlinarith

/-- The variational estimate has a constant fixed before the potential is chosen. -/
theorem moserFlow_family_derivative_bound (hpublished : PublishedC4FlowInput)
    {rho B : ℝ} (hrho : 0 < rho) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Position → ℝ), ContDiff ℝ 6 V →
      (∀ k ≤ 6, ∀ x, ‖iteratedFDeriv ℝ k V x‖ ≤ B) →
      (∀ x, |manufacturedCharge V x| ≤ rho/2) →
      ∀ G : Position → ℝ → Position, IsUnitTimeFlow (moserVelocity rho V) G →
      ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x,
        ‖iteratedFDeriv ℝ k (fun y => G y t) x‖ ≤ C := by
  obtain ⟨A,hA,hAb⟩ := moserVelocity_family_derivative_bound hrho hB
  obtain ⟨C,hC,hCb⟩ := hpublished.uniform A hA.le
  refine ⟨C,hC,fun V hV hb hc G hG => ?_⟩
  exact hCb (moserDomain rho V) (moserDomain_isOpen rho V hV)
    (moserDomain_contains_time_slab hrho V hc) (moserVelocity rho V)
    (moserVelocity_joint_C4 rho V hV) (hAb V hV hb hc) G hG

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_MoserUniformInverse
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform separation of transported nodes: the inverse Lipschitz
constant is fixed over the same bounded family as the forward flow. -/

noncomputable section
open scoped Topology NNReal
namespace ContinuumCoulomb

private theorem velocity_lipschitz_of_joint_bound {rho C : ℝ} (hC : 0 ≤ C)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hc : ∀ x, |manufacturedCharge V x| ≤ rho/2) (hrho : 0 < rho)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x,
      ‖iteratedFDeriv ℝ 1 (fun p : ℝ × Position => moserVelocity rho V p.1 p.2) (t,x)‖ ≤ C) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, LipschitzWith ⟨C,hC⟩ (moserVelocity rho V t) := by
  let F : ℝ × Position → Position := fun p => moserVelocity rho V p.1 p.2
  let S := Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set Position)
  have hdom : S ⊆ moserDomain rho V := moserDomain_contains_time_slab hrho V hc
  have hopen := moserDomain_isOpen rho V hV
  have hreg : ContDiffOn ℝ 4 F (moserDomain rho V) := moserVelocity_joint_C4 rho V hV
  have hLip : LipschitzOnWith ⟨C,hC⟩ F S :=
    Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun p hp => (hreg.contDiffAt (hopen.mem_nhds (hdom hp))).differentiableAt (by norm_num))
      (fun p hp => by
        have h := hb p.1 hp.1 p.2
        rw [norm_iteratedFDeriv_one] at h
        exact_mod_cast h)
      ((convex_Icc (0 : ℝ) 1).prod convex_univ)
  intro t ht
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [F, dist_prod_same_left] using hLip.dist_le_mul (t,x) ⟨ht,Set.mem_univ _⟩
    (t,y) ⟨ht,Set.mem_univ _⟩

private theorem trajectory_backward_of_lipschitz (rho : ℝ) (V : Position → ℝ)
    (K : ℝ≥0) (hK : ∀ t ∈ Set.Icc (0 : ℝ) 1, LipschitzWith K (moserVelocity rho V t))
    (α β : ℝ → Position)
    (hα : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt α (moserVelocity rho V t (α t)) (Set.Icc (0 : ℝ) 1) t)
    (hβ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt β (moserVelocity rho V t (β t)) (Set.Icc (0 : ℝ) 1) t) :
    dist (α 0) (β 0) ≤ Real.exp (K:ℝ)*dist (α 1) (β 1) := by
  let v : ℝ → Position → Position := fun s x => -(moserVelocity rho V (-s) x)
  have hmap : Set.MapsTo (Neg.neg : ℝ → ℝ) (Set.Icc (-1:ℝ) 0) (Set.Icc (0:ℝ) 1) := by
    intro s hs
    constructor <;> linarith [hs.1,hs.2]
  have hd (γ : ℝ → Position)
      (hγ : ∀ t ∈ Set.Icc (0:ℝ) 1,
        HasDerivWithinAt γ (moserVelocity rho V t (γ t)) (Set.Icc (0:ℝ) 1) t)
      (s : ℝ) (hs : s ∈ Set.Ico (-1:ℝ) 0) :
      HasDerivWithinAt (γ ∘ Neg.neg) (v s ((γ ∘ Neg.neg) s)) (Set.Ici s) s := by
    have hmem : -s ∈ Set.Ioc (0:ℝ) 1 := by constructor <;> linarith [hs.1,hs.2]
    have hdγ : HasDerivWithinAt γ (moserVelocity rho V (-s) (γ (-s))) (Set.Iic (-s)) (-s) := by
      apply (hγ (-s) ⟨hmem.1.le,hmem.2⟩).mono_of_mem_nhdsWithin
      apply Filter.mem_of_superset (Icc_mem_nhdsLE hmem.1)
      exact Set.Icc_subset_Icc_right hmem.2
    have hm : Set.MapsTo (Neg.neg : ℝ → ℝ) (Set.Ici s) (Set.Iic (-s)) :=
      fun _ ht => neg_le_neg (Set.mem_Ici.mp ht)
    convert! HasFDerivWithinAt.comp_hasDerivWithinAt s hdγ
      (hasDerivAt_neg s).hasDerivWithinAt hm using 1
    all_goals try with_reducible_and_instances rfl
    simp [v]
  have hv (s : ℝ) (hs : s ∈ Set.Ico (-1:ℝ) 0) :
      LipschitzOnWith K (v s) (Set.univ : Set Position) :=
    (hK (-s) (hmap ⟨hs.1,hs.2.le⟩)).neg.lipschitzOnWith
  have h := dist_le_of_trajectories_ODE_of_mem (v := v) (s := fun _ => Set.univ) hv
    ((HasDerivWithinAt.continuousOn hα).comp continuous_neg.continuousOn hmap)
    (hd α hα) (fun _ _ => Set.mem_univ _)
    ((HasDerivWithinAt.continuousOn hβ).comp continuous_neg.continuousOn hmap)
    (hd β hβ) (fun _ _ => Set.mem_univ _)
    (le_refl (dist ((α ∘ Neg.neg) (-1)) ((β ∘ Neg.neg) (-1))))
    0 (show (0:ℝ) ∈ Set.Icc (-1:ℝ) 0 by constructor <;> norm_num)
  simpa only [Function.comp_apply, neg_zero, neg_neg, sub_neg_eq_add, zero_add, mul_one,
    mul_comm] using h

/-- One inverse Lipschitz constant works for every actual trajectory family
of every potential with the stated six-derivative bound. -/
theorem moserFlow_family_inverse_bound {rho B : ℝ} (hrho : 0 < rho) (hB : 0 ≤ B) :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ (V : Position → ℝ), ContDiff ℝ 6 V →
      (∀ k ≤ 6, ∀ x, ‖iteratedFDeriv ℝ k V x‖ ≤ B) →
      (∀ x, |manufacturedCharge V x| ≤ rho/2) →
      ∀ G : Position → ℝ → Position, IsUnitTimeFlow (moserVelocity rho V) G →
        AntilipschitzWith K (fun x => G x 1) := by
  obtain ⟨C,hC,hCb⟩ := moserVelocity_family_derivative_bound hrho hB
  refine ⟨⟨Real.exp C,(Real.exp_pos C).le⟩,by exact_mod_cast Real.exp_pos C,?_⟩
  intro V hV hb hc G hG
  have hLip := velocity_lipschitz_of_joint_bound hC.le V hV hc hrho
    (fun t ht x => hCb V hV hb hc 1 (by norm_num) t ht x)
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  change dist x y ≤ Real.exp C * dist (G x 1) (G y 1)
  have h := trajectory_backward_of_lipschitz rho V ⟨C,hC.le⟩ hLip
    (G x) (G y) (hG.2 x) (hG.2 y)
  change dist (G x 0) (G y 0) ≤ Real.exp C * dist (G x 1) (G y 1) at h
  simpa only [hG.1] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_TransportedGrid
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The far-cell inverse-fifth sum after the actual density transport.
Its constant does not depend on the slab's horizontal extent. -/

noncomputable section
open MeasureTheory
open scoped BigOperators NNReal
namespace ContinuumCoulomb

theorem transported_far_cube_distances {h : ℝ} (hh : 0 < h)
    (G : Position → Position) {L : ℝ≥0} (hL : 0 < L) (hG : LipschitzWith L G)
    {y b x : Position} (hfar : 4*(L:ℝ)*h ≤ ‖y-G b‖) (hx : x ∈ positionCube b h) :
    (L:ℝ)*h < ‖y-G x‖ ∧ ‖y-G b‖/2 ≤ ‖y-G x‖ ∧ ‖y-G x‖ ≤ 2*‖y-G b‖ := by
  have hhL : 0 < (L:ℝ)*h := mul_pos (by exact_mod_cast hL) hh
  have hn : ‖G x-G b‖ ≤ (L:ℝ)*h :=
    (hG.norm_sub_le x b).trans (mul_le_mul_of_nonneg_left
      (positionCube_norm_sub_le hh.le hx) L.coe_nonneg)
  have ha := norm_sub_le_norm_sub_add_norm_sub y (G x) (G b)
  have hb := norm_sub_le_norm_sub_add_norm_sub y (G b) (G x)
  rw [norm_sub_rev (G b) (G x)] at hb
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem transported_inverseFifth_far_cube_bound {h : ℝ} (hh : 0 < h)
    (G : Position → Position) {L : ℝ≥0} (hL : 0 < L) (hG : LipschitzWith L G)
    (y b : Position) (hfar : 4*(L:ℝ)*h ≤ ‖y-G b‖) :
    h^3/‖y-G b‖^5 ≤
      32*(∫ x in positionCube b h, inverseFifthTail ((L:ℝ)*h) (y-G x)) := by
  have hr : 0 < (L:ℝ)*h := mul_pos (by exact_mod_cast hL) hh
  have hd : 0 < ‖y-G b‖ := lt_of_lt_of_le (by positivity) hfar
  have hi : IntegrableOn (fun x => inverseFifthTail ((L:ℝ)*h) (y-G x)) (positionCube b h) := by
    apply IntegrableOn.of_bound (positionCube_isCompact b hh.le).measure_lt_top
      (((inverseFifthTail_measurable _).comp (continuous_const.sub hG.continuous).measurable).aestronglyMeasurable.restrict)
      (1/((L:ℝ)*h)^5)
    exact Filter.Eventually.of_forall (fun x => by
      change ‖inverseFifthTail ((L:ℝ)*h) (y-G x)‖ ≤ 1/((L:ℝ)*h)^5
      rw [Real.norm_of_nonneg (inverseFifthTail_nonneg _ _)]
      exact inverseFifthTail_le hr _)
  have hp (x : Position) (hx : x ∈ positionCube b h) :
      1/‖y-G b‖^5 ≤ 32*inverseFifthTail ((L:ℝ)*h) (y-G x) := by
    obtain ⟨hxgt,_hxl,hxu⟩ := transported_far_cube_distances hh G hL hG hfar hx
    have hdx := hr.trans hxgt
    rw [inverseFifthTail_eq_inv_pow _ hxgt,mul_one_div]
    apply (div_le_div_iff₀ (pow_pos hd 5) (pow_pos hdx 5)).mpr
    have hb := pow_le_pow_left₀ (norm_nonneg (y-G x)) hxu 5
    nlinarith [show (2*‖y-G b‖)^5 = 32*‖y-G b‖^5 by ring]
  have he := setIntegral_mono_on
    (integrableOn_const (C := 1/‖y-G b‖^5)
      ((positionCube_isCompact b hh.le).measure_lt_top (μ := volume)).ne)
    (hi.const_mul 32) (positionCube_isClosed b h).measurableSet hp
  have hv : (volume.restrict (positionCube b h)).real Set.univ = h^3 := by
    simpa only [Measure.real,Measure.restrict_apply_univ] using positionCube_volume b hh.le
  simpa only [integral_const,smul_eq_mul,hv,integral_const_mul,div_eq_mul_inv,mul_one,one_mul] using he

theorem moser_inverseFifth_grid_sum_bound (hpublished : PublishedC4FlowInput)
    {rho H S : ℝ} (hrho : 0 < rho) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    (hsupport : tsupport V ⊆ slabDomain H S)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow (moserVelocity rho V) G)
    (hbij : Function.Bijective (fun x => G x 1))
    (hfix : ∀ x, x ∉ tsupport V → G x 1 = x)
    {L : ℝ≥0} (hL : 0 < L) (hLip : LipschitzWith L (fun x => G x 1))
    {ι : Type*} [Fintype ι] (index : ι → Fin 3 → ℤ) (hindex : Function.Injective index)
    {h : ℝ} (hh : 0 < h)
    (hsub : ∀ i, positionCube (gaussCellCenter h (index i)) h ⊆ slabDomain H S)
    (y : Position) (hfar : ∀ i, 4*(L:ℝ)*h ≤ ‖y-G (gaussCellCenter h (index i)) 1‖) :
    (∑ i, h^3/‖y-G (gaussCellCenter h (index i)) 1‖^5) ≤ 96*Real.pi/((L:ℝ)*h)^2 := by
  have hr : 0 < (L:ℝ)*h := mul_pos (by exact_mod_cast hL) hh
  calc
    _ ≤ ∑ i, 32*(∫ x in positionCube (gaussCellCenter h (index i)) h,
        inverseFifthTail ((L:ℝ)*h) (y-G x 1)) :=
      Finset.sum_le_sum (fun i _ => transported_inverseFifth_far_cube_bound hh
        (fun x => G x 1) hL hLip y _ (hfar i))
    _ = 32*(∑ i, ∫ x in positionCube (gaussCellCenter h (index i)) h,
        inverseFifthTail ((L:ℝ)*h) (y-G x 1)) := (Finset.mul_sum _ _ _).symm
    _ ≤ 32*(∫ x in slabDomain H S, inverseFifthTail ((L:ℝ)*h) (y-G x 1)) :=
      mul_le_mul_of_nonneg_left (grid_cell_integral_sum_le_on index hindex hh hsub _
        (transportedInverseFifth_integrableOn hH hS hr _ hLip.continuous y)
        (fun x => inverseFifthTail_nonneg _ _)) (by norm_num)
    _ ≤ 32*(3*Real.pi/((L:ℝ)*h)^2) := mul_le_mul_of_nonneg_left
      (moser_inverseFifth_tail_bound hpublished hrho V hV hbound hsupport G hG hbij hfix y hr)
      (by norm_num)
    _ = _ := by ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_TransportedNearGrid
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Near cells have uniformly bounded continuous Coulomb mass after the
actual Moser transport. The bound is independent of the enclosing box. -/

noncomputable section
open MeasureTheory
open scoped BigOperators NNReal
namespace ContinuumCoulomb

theorem transported_near_cube_distance {h : ℝ} (hh : 0 < h)
    (G : Position → Position) {L : ℝ≥0} (hL : 0 < L) (hG : LipschitzWith L G)
    {y b x : Position} (hnear : ‖y-G b‖ ≤ 4*(L:ℝ)*h) (hx : x ∈ positionCube b h) :
    ‖y-G x‖ < 6*(L:ℝ)*h := by
  have hn : ‖G x-G b‖ ≤ (L:ℝ)*h :=
    (hG.norm_sub_le x b).trans (mul_le_mul_of_nonneg_left
      (positionCube_norm_sub_le hh.le hx) L.coe_nonneg)
  have ht := norm_sub_le_norm_sub_add_norm_sub y (G b) (G x)
  rw [norm_sub_rev (G b) (G x)] at ht
  have hp : 0 < (L:ℝ)*h := mul_pos (by exact_mod_cast hL) hh
  linarith

theorem transported_near_kernel_eq {h : ℝ} (hh : 0 < h)
    (G : Position → Position) {L : ℝ≥0} (hL : 0 < L) (hG : LipschitzWith L G)
    {y b x : Position} (hnear : ‖y-G b‖ ≤ 4*(L:ℝ)*h) (hx : x ∈ positionCube b h) :
    Coulomb.coulombKernel (y-G x) = Coulomb.truncatedCoulomb (6*(L:ℝ)*h) (y-G x) := by
  have hm : y-G x ∈ Metric.ball (0:Position) (6*(L:ℝ)*h) := by
    simpa only [Metric.mem_ball,dist_zero_right] using
      transported_near_cube_distance hh G hL hG hnear hx
  exact (Set.indicator_of_mem hm _).symm

theorem moser_near_grid_integral_bound (hpublished : PublishedC4FlowInput)
    {rho H S : ℝ} (hrho : 0 < rho) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    (hsupport : tsupport V ⊆ slabDomain H S)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow (moserVelocity rho V) G)
    (hbij : Function.Bijective (fun x => G x 1))
    (hfix : ∀ x, x ∉ tsupport V → G x 1 = x)
    {L : ℝ≥0} (hL : 0 < L) (hLip : LipschitzWith L (fun x => G x 1))
    {ι : Type*} [Fintype ι] (index : ι → Fin 3 → ℤ) (hindex : Function.Injective index)
    {h : ℝ} (hh : 0 < h)
    (hsub : ∀ i, positionCube (gaussCellCenter h (index i)) h ⊆ slabDomain H S)
    (y : Position) (hnear : ∀ i, ‖y-G (gaussCellCenter h (index i)) 1‖ ≤ 4*(L:ℝ)*h) :
    (∑ i, positionCellIntegral (gaussCellCenter h (index i)) h
      (fun x => Coulomb.coulombKernel (y-G x 1))) ≤ 108*Real.pi*(L:ℝ)^2*h^2 := by
  have hi := moser_coulomb_integrableOn hpublished hrho hH hS V hV hbound hsupport G hG hbij hfix y
  have ht := moser_truncatedCoulomb_integrable hpublished hrho V hV hbound hsupport
    G hG hbij hfix y (6*(L:ℝ)*h)
  calc
    _ = ∑ i, ∫ x in positionCube (gaussCellCenter h (index i)) h,
        Coulomb.truncatedCoulomb (6*(L:ℝ)*h) (y-G x 1) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [positionCellIntegral_eq_setIntegral _ hh.le _ (hi.mono_set (hsub i))]
      apply setIntegral_congr_fun (positionCube_isClosed _ _).measurableSet
      intro x hx
      exact transported_near_kernel_eq hh (fun x => G x 1) hL hLip (hnear i) hx
    _ ≤ ∫ x in slabDomain H S, Coulomb.truncatedCoulomb (6*(L:ℝ)*h) (y-G x 1) :=
      grid_cell_integral_sum_le_on index hindex hh hsub _ ht
        (fun x => Coulomb.truncatedCoulomb_nonneg _ _)
    _ ≤ 3*Real.pi*(6*(L:ℝ)*h)^2 :=
      moser_truncatedCoulomb_bound hpublished hrho V hV hbound hsupport G hG hbij hfix y (by positivity)
    _ = _ := by ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombFarCell
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fourth-order quadrature on a cube separated from an actual Coulomb pole. -/

noncomputable section
namespace ContinuumCoulomb

theorem translatedCoulomb_derivative_norm (k : ℕ) (y z : Position) :
    ‖iteratedFDeriv ℝ k (fun w => Coulomb.coulombKernel (y-w)) z‖ =
      ‖iteratedFDeriv ℝ k Coulomb.coulombKernel (y-z)‖ := by
  let e : Position ≃ₗᵢ[ℝ] Position := LinearIsometryEquiv.neg ℝ
  have he := e.norm_iteratedFDeriv_comp_right (fun w => Coulomb.coulombKernel (y+w)) z k
  change ‖iteratedFDeriv ℝ k (fun w => Coulomb.coulombKernel (y + -w)) z‖ =
    ‖iteratedFDeriv ℝ k (fun w => Coulomb.coulombKernel (y+w)) (-z)‖ at he
  rw [iteratedFDeriv_comp_add_left] at he
  simpa only [sub_eq_add_neg] using he

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_TransportedCoulombDerivative
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fourth derivatives of the Coulomb integrand after the Moser map. The
estimate is local at a point and needs no regularity across the pole. -/

noncomputable section
namespace ContinuumCoulomb

theorem fourth_composite_norm_bound (f : Position → ℝ) (G : Position → Position) (x : Position)
    (hf : ContDiffAt ℝ 4 f (G x)) (hG : ContDiff ℝ 4 G) {C D : ℝ}
    (hC : ∀ k : ℕ, k ≤ 4 → ‖iteratedFDeriv ℝ k f (G x)‖ ≤ C)
    (hD : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ‖iteratedFDeriv ℝ k G x‖ ≤ D^k) :
    ‖iteratedFDeriv ℝ 4 (f ∘ G) x‖ ≤ 24*C*D^4 := by
  obtain ⟨U,hU,hx,hfU⟩ := hf.contDiffOn' le_rfl (by norm_num)
  have hfU : ContDiffOn ℝ 4 f U := by simpa using hfU
  have hS : IsOpen (G ⁻¹' U) := hU.preimage hG.continuous
  have hc := norm_iteratedFDerivWithin_comp_le hfU hG.contDiffOn (n := 4) le_rfl
    hU.uniqueDiffOn hS.uniqueDiffOn (fun _ hy => hy) hx
    (fun k hk => by
      rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn (hf.of_le (by exact_mod_cast hk)) hx]
      exact hC k hk)
    (fun k hk hk' => by
      rw [iteratedFDerivWithin_eq_iteratedFDeriv (f := G) (x := x) (s := G ⁻¹' U) hS.uniqueDiffOn
        (hG.of_le (by exact_mod_cast hk')).contDiffAt hx]
      exact hD k hk hk')
  rw [iteratedFDerivWithin_eq_iteratedFDeriv (f := f ∘ G) (x := x) (s := G ⁻¹' U) hS.uniqueDiffOn (hf.comp x hG.contDiffAt) hx] at hc
  norm_num only [Nat.factorial] at hc
  exact hc

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_TransportedHybrid
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.Coulomb.complexWindow_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The transport correction is confined to the support of the field. Outside
that set only the integrable inverse-fifth Coulomb derivative remains. -/

noncomputable section
open Filter
open scoped Topology Classical
namespace ContinuumCoulomb

theorem coulomb_kernel_jets_hybrid_bound :
    ∃ C : ℝ, 1 ≤ C ∧
      (∀ (z : Position), z ≠ 0 → ∀ k : ℕ, k ≤ 4 →
        ‖iteratedFDeriv ℝ k Coulomb.coulombKernel z‖ ≤ C*(1+1/‖z‖^5)) ∧
      (∀ (z : Position), z ≠ 0 →
        ‖iteratedFDeriv ℝ 4 Coulomb.coulombKernel z‖ ≤ C/‖z‖^5) := by
  obtain ⟨C,hC,hbound⟩ := coulombKernel_derivative_decay
  have hC0 : 0 ≤ C := (by norm_num : (0:ℝ) ≤ 1).trans hC
  refine ⟨C,hC,?_,?_⟩
  · intro z hz k hk
    have hd : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hb := hbound ⟨k,by omega⟩ z hz
    by_cases hd1 : ‖z‖ ≤ 1
    · have hp : ‖z‖^5 ≤ ‖z‖^(k+1) :=
        pow_le_pow_of_le_one hd.le hd1 (by omega)
      have he : ‖iteratedFDeriv ℝ k Coulomb.coulombKernel z‖ ≤ C/‖z‖^5 := by
        apply (le_div_iff₀ (pow_pos hd 5)).mpr
        exact (mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans hb
      rw [mul_add,mul_one,mul_one_div]
      linarith
    · have hp : 1 ≤ ‖z‖^(k+1) := one_le_pow₀ (le_of_not_ge hd1)
      have hm : ‖iteratedFDeriv ℝ k Coulomb.coulombKernel z‖ ≤
          ‖iteratedFDeriv ℝ k Coulomb.coulombKernel z‖*‖z‖^(k+1) := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hp (norm_nonneg (iteratedFDeriv ℝ k Coulomb.coulombKernel z))
      have he := hm.trans hb
      rw [mul_add,mul_one,mul_one_div]
      linarith [div_nonneg hC0 (pow_nonneg hd.le 5)]
  · intro z hz
    apply (le_div_iff₀ (pow_pos (norm_pos_iff.mpr hz) 5)).mpr
    exact hbound (4:Fin 5) z hz

theorem transportedCoulomb_hybrid_fourth_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (G : Position → Position), ContDiff ℝ 4 G →
      ∀ (E : Set Position), IsClosed E → (∀ x, x ∉ E → G x = x) →
      ∀ (D : ℝ), 1 ≤ D →
      (∀ x, ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ‖iteratedFDeriv ℝ k G x‖ ≤ D^k) →
      ∀ (y x : Position), y-G x ≠ 0 →
      ‖iteratedFDeriv ℝ 4 (fun b => Coulomb.coulombKernel (y-G b)) x‖ ≤
        24*C*D^4*(1/‖y-G x‖^5 + if x ∈ E then 1 else 0) := by
  classical
  obtain ⟨C,hC,hbound,hpure⟩ := coulomb_kernel_jets_hybrid_bound
  refine ⟨C,hC,fun G hG E hE hfix D hD hGD y x hne => ?_⟩
  have hC0 : 0 ≤ C := (by norm_num : (0:ℝ) ≤ 1).trans hC
  have hf : ContDiffAt ℝ 4 (fun z => Coulomb.coulombKernel (y-z)) (G x) :=
    ((coulombKernel_contDiffAt hne).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4)).comp (G x)
        (contDiffAt_const.sub contDiffAt_id)
  by_cases hx : x ∈ E
  · have he := fourth_composite_norm_bound (fun z => Coulomb.coulombKernel (y-z)) G x hf hG
      (fun k hk => by rw [translatedCoulomb_derivative_norm]; exact hbound _ hne k hk)
      (hGD x)
    simp only [ite_eq_left hx]
    apply he.trans_eq
    ring
  · have hlocal : G =ᶠ[𝓝 x] id := by
      filter_upwards [hE.isOpen_compl.mem_nhds hx] with z hz
      exact hfix z hz
    have heq : (fun b => Coulomb.coulombKernel (y-G b)) =ᶠ[𝓝 x]
        (fun b => Coulomb.coulombKernel (y-b)) := by
      filter_upwards [hlocal] with b hb
      rw [hb]
      rfl
    rw [(heq.iteratedFDeriv ℝ 4).eq_of_nhds,translatedCoulomb_derivative_norm]
    have he := hpure (y-x) (by simpa only [hfix x hx] using hne)
    have hfac : C ≤ 24*C*D^4 := by nlinarith [one_le_pow₀ hD (n := 4)]
    simp only [ite_eq_right hx,add_zero,hfix x hx]
    exact he.trans (by simpa only [div_eq_mul_inv,mul_one,one_mul] using
      mul_le_mul_of_nonneg_right hfac (inv_nonneg.mpr (pow_nonneg (norm_nonneg (y-x)) 5)))

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

theorem slabWellCutoff_outer {S : ℝ} (hS : 0 < S) {z : ℝ} (hz : S ≤ |z|) :
    slabWellCutoff S z = 0 := by
  apply verticalCutoffBump.zero_of_le_dist
  change 2 ≤ dist ((2/S)*z) 0
  rw [dist_zero_right, Real.norm_eq_abs, abs_mul, abs_of_pos (div_pos (by norm_num) hS)]
  have hm := mul_le_mul_of_nonneg_left hz (div_pos (by norm_num : (0:ℝ)<2) hS).le
  have he : (2/S)*S = (2:ℝ) := by field_simp
  exact he.symm.le.trans hm

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

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_WellCover
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A cover of the actual well support by boxes whose total volume is
linear in the number of wells and the vertical cutoff radius. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem mem_wellCoverBox {u : PlanarPosition} {r S : ℝ} {x : Position} :
    x ∈ wellCoverBox u r S ↔ |x 0-u 0| ≤ r ∧ |x 1-u 1| ≤ r ∧ |x 2| ≤ S := by
  constructor
  · rintro ⟨hl,hu⟩
    have h0l := hl 0; have h0u := hu 0
    have h1l := hl 1; have h1u := hu 1
    have h2l := hl 2; have h2u := hu 2
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val] at *
    exact ⟨abs_le.mpr ⟨by linarith,by linarith⟩,
      abs_le.mpr ⟨by linarith,by linarith⟩,abs_le.mpr ⟨h2l,h2u⟩⟩
  · rintro ⟨h0,h1,h2⟩
    obtain ⟨h0l,h0u⟩ := abs_le.mp h0
    obtain ⟨h1l,h1u⟩ := abs_le.mp h1
    obtain ⟨h2l,h2u⟩ := abs_le.mp h2
    constructor <;> intro i <;> fin_cases i <;> simp <;> linarith

theorem wellCoverBox_isClosed (u : PlanarPosition) (r S : ℝ) :
    IsClosed (wellCoverBox u r S) :=
  isClosed_Icc.preimage (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ))

theorem wellCoverBox_measure_ne_top (u : PlanarPosition) (r S : ℝ) :
    volume (wellCoverBox u r S) ≠ ⊤ := by
  unfold wellCoverBox
  rw [(PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage measurableSet_Icc.nullMeasurableSet]
  exact isCompact_Icc.measure_ne_top

theorem wellCoverBox_volume (u : PlanarPosition) {r S : ℝ} (hr : 0 ≤ r) (hS : 0 ≤ S) :
    volume.real (wellCoverBox u r S) = 8*r^2*S := by
  unfold wellCoverBox Measure.real
  rw [(PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage measurableSet_Icc.nullMeasurableSet]
  rw [Real.volume_Icc_pi_toReal (by intro i; fin_cases i <;> simp <;> linarith)]
  simp [Fin.prod_univ_succ]
  ring

theorem manufacturedWellField_support_cover (freq scale : ℝ) {S : ℝ} (hS : 0 < S)
    {m : ℕ} (u : Fin m → PlanarPosition) :
    tsupport (manufacturedWellField freq scale S u) ⊆ ⋃ i, wellCoverBox (u i) 1 S := by
  apply closure_minimal _ (isClosed_iUnion_of_finite (fun i => wellCoverBox_isClosed (u i) 1 S))
  intro x hx
  have hz : |(positionSplitCoordinates x).2| < S := by
    by_contra hn
    exact hx (manufacturedWellField_outer freq scale hS u x (le_of_not_gt hn))
  have hnear : ∃ i, ‖(positionSplitCoordinates x).1-u i‖ < 1 := by
    by_contra hn
    apply hx
    unfold manufacturedWellField
    rw [countertermWellSum_zero_far freq scale u _ (fun i =>
      le_of_not_gt (fun hi => hn ⟨i,hi⟩)),mul_zero]
  obtain ⟨i,hi⟩ := hnear
  apply Set.mem_iUnion.mpr
  refine ⟨i,mem_wellCoverBox.mpr ⟨?_,?_,?_⟩⟩
  · simpa only [Real.norm_eq_abs,PiLp.sub_apply,positionSplitCoordinates_fst_zero] using
      (PiLp.norm_apply_le ((positionSplitCoordinates x).1-u i) 0).trans hi.le
  · simpa only [Real.norm_eq_abs,PiLp.sub_apply,positionSplitCoordinates_fst_one] using
      (PiLp.norm_apply_le ((positionSplitCoordinates x).1-u i) 1).trans hi.le
  · simpa only [positionSplitCoordinates_snd] using hz.le

theorem wellCover_volume_bound {m : ℕ} (u : Fin m → PlanarPosition)
    {r S : ℝ} (hr : 0 ≤ r) (hS : 0 ≤ S) :
    volume.real (⋃ i, wellCoverBox (u i) r S) ≤ 8*m*r^2*S := by
  apply (measureReal_iUnion_fintype_le (fun i => wellCoverBox (u i) r S)).trans
  simp only [wellCoverBox_volume _ hr hS,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  apply le_of_eq
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ExceptionalCellVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cells meeting the well support have total volume O(m*S), rather than
the volume of the surrounding slab. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem cube_meets_wellCover_subset {b z : Position} {u : PlanarPosition}
    {h r S : ℝ} (hh : 0 ≤ h) (hz : z ∈ positionCube b h)
    (hzu : z ∈ wellCoverBox u r S) :
    positionCube b h ⊆ wellCoverBox u (r+2*h) (S+2*h) := by
  intro x hx
  have hd := positionCube_diameter_bound hh hx hz
  have hi (i : Fin 3) : |x i-z i| ≤ 2*h := by
    exact (PiLp.norm_apply_le (x-z) i).trans hd
  obtain ⟨hz0,hz1,hz2⟩ := mem_wellCoverBox.mp hzu
  apply mem_wellCoverBox.mpr
  refine ⟨?_,?_,?_⟩
  · linarith [abs_sub_le (x 0) (z 0) (u 0),hi 0]
  · linarith [abs_sub_le (x 1) (z 1) (u 1),hi 1]
  · have he := abs_sub_le (x 2) (z 2) 0
    simp only [sub_zero] at he
    linarith [hi 2]

theorem exceptional_cell_volume_bound {ι : Type*} [Fintype ι]
    (index : ι → Fin 3 → ℤ) (hindex : Function.Injective index)
    {h S : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hS : 1 ≤ S)
    (freq scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (hmeet : ∀ i, ∃ z ∈ positionCube (gaussCellCenter h (index i)) h,
      z ∈ tsupport (manufacturedWellField freq scale S u)) :
    (Fintype.card ι:ℝ)*h^3 ≤ 216*m*S := by
  let A : ι → Set Position := fun i => positionOpenCube (gaussCellCenter h (index i)) h
  let B : Fin m → Set Position := fun j => wellCoverBox (u j) (1+2*h) (S+2*h)
  have hsub : (⋃ i, A i) ⊆ ⋃ j, B j := by
    intro x hx
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨z,hz,hzs⟩ := hmeet i
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp
      (manufacturedWellField_support_cover freq scale (by linarith : 0 < S) u hzs)
    exact Set.mem_iUnion.mpr ⟨j,cube_meets_wellCover_subset hh.le hz hj
      (positionOpenCube_subset _ _ hi)⟩
  have hBfinite : volume (⋃ j, B j) ≠ ⊤ := by
    apply ne_of_lt
    apply lt_of_le_of_lt (measure_iUnion_fintype_le volume B)
    exact ENNReal.sum_lt_top.mpr (fun j _ => (wellCoverBox_measure_ne_top (u j) _ _).lt_top)
  have hA : volume.real (⋃ i, A i) = (Fintype.card ι:ℝ)*h^3 := by
    rw [measureReal_iUnion_fintype
      (fun i j hij => grid_openCubes_disjoint hh (fun he => hij (hindex he)))
      (fun i => positionOpenCube_measurable _ _)
      (fun i => by
        rw [measure_congr (positionOpenCube_ae_eq (gaussCellCenter h (index i)) h)]
        exact (positionCube_isCompact _ hh.le).measure_ne_top)]
    simp only [positionOpenCube_volume _ hh.le,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  calc
    _ = volume.real (⋃ i, A i) := hA.symm
    _ ≤ volume.real (⋃ j, B j) := measureReal_mono hsub hBfinite
    _ ≤ 8*m*(1+2*h)^2*(S+2*h) :=
      wellCover_volume_bound u (by positivity) (by linarith)
    _ ≤ 8*m*9*(3*S) := by
      gcongr
      · nlinarith
      · linarith
    _ = _ := by ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_TransportedFarQuadrature
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local fourth-order error with the nondecaying transport correction
charged only to cells meeting the compact well support. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical NNReal
namespace ContinuumCoulomb

theorem cellHits_nonneg (E : Set Position) (b : Position) (h : ℝ) : 0 ≤ cellHits E b h := by
  unfold cellHits
  split_ifs <;> norm_num

theorem cellHits_indicator_le (E : Set Position) (b : Position) (h : ℝ)
    {x : Position} (hx : x ∈ positionCube b h) :
    (if x ∈ E then (1:ℝ) else 0) ≤ cellHits E b h := by
  by_cases hE : x ∈ E
  · simp [hE,cellHits,show ∃ z ∈ positionCube b h, z ∈ E from ⟨x,hx,hE⟩]
  · simpa only [ite_eq_right hE] using cellHits_nonneg E b h

theorem manufactured_cellHits_volume_bound {ι : Type*} [Fintype ι]
    (index : ι → Fin 3 → ℤ) (hindex : Function.Injective index)
    {h S : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hS : 1 ≤ S)
    (freq scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) :
    (∑ i, cellHits (tsupport (manufacturedWellField freq scale S u))
      (gaussCellCenter h (index i)) h*h^3) ≤ 216*m*S := by
  let s := Finset.univ.filter (fun i => ∃ z ∈ positionCube (gaussCellCenter h (index i)) h,
    z ∈ tsupport (manufacturedWellField freq scale S u))
  have hi : Function.Injective (fun i : {i // i ∈ s} => index i.val) := by
    intro i j hij
    exact Subtype.ext (hindex hij)
  have he := exceptional_cell_volume_bound (fun i : {i // i ∈ s} => index i.val) hi
    hh hh1 hS freq scale u (fun i => (Finset.mem_filter.mp i.property).2)
  simpa only [Fintype.card_coe,s,cellHits,ite_mul,one_mul,zero_mul,← Finset.sum_filter,
    Finset.sum_const,nsmul_eq_mul] using he

theorem transportedCoulomb_far_cell_hybrid_error :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (G : Position → Position), ContDiff ℝ 4 G →
      ∀ (E : Set Position), IsClosed E → (∀ x, x ∉ E → G x = x) →
      ∀ (D : ℝ), 1 ≤ D →
      (∀ x, ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ‖iteratedFDeriv ℝ k G x‖ ≤ D^k) →
      ∀ (L : ℝ≥0), 0 < L → LipschitzWith L G →
      ∀ (y b : Position) (h : ℝ), 0 < h → 4*(L:ℝ)*h ≤ ‖y-G b‖ →
      |positionCellGauss b h (fun x => Coulomb.coulombKernel (y-G x))-
        positionCellIntegral b h (fun x => Coulomb.coulombKernel (y-G x))| ≤
        (24*C*D^4)*(32/‖y-G b‖^5+cellHits E b h)*h^7 := by
  obtain ⟨C,hC,hbound⟩ := transportedCoulomb_hybrid_fourth_bound
  refine ⟨C,hC,fun G hG E hE hfix D hD hGD L hL hLip y b h hh hfar => ?_⟩
  have hC0 : 0 ≤ C := (by norm_num : (0:ℝ) ≤ 1).trans hC
  have hd : 0 < ‖y-G b‖ := lt_of_lt_of_le (by positivity) hfar
  have hf (x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 1) (v : ℝ) (hv : v ∈ Set.Icc (-1:ℝ) 1)
      (z : ℝ) (hz : z ∈ Set.Icc (-1:ℝ) 1) :
      ContDiffAt ℝ 4 (fun a => Coulomb.coulombKernel (y-G a)) (cubePoint b (h/2) x v z) := by
    have hc := cubePoint_mem_positionCube b hh.le hx hv hz
    have hn := (transported_far_cube_distances hh G hL hLip hfar hc).1
    have hne : y-G (cubePoint b (h/2) x v z) ≠ 0 :=
      norm_pos_iff.mp (lt_of_lt_of_le (by positivity : (0:ℝ) < (L:ℝ)*h) hn.le)
    exact ContDiffAt.comp (g := Coulomb.coulombKernel) (f := fun a : Position => y-G a)
      _ ((coulombKernel_contDiffAt hne).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4)) (contDiffAt_const.sub hG.contDiffAt)
  apply positionCellGauss_error_local _ b hh.le
    (mul_nonneg (by positivity) (add_nonneg (by positivity) (cellHits_nonneg E b h))) hf
  intro x hx v hv z hz
  let a := cubePoint b (h/2) x v z
  have hc : a ∈ positionCube b h := cubePoint_mem_positionCube b hh.le hx hv hz
  have ha := transported_far_cube_distances hh G hL hLip hfar hc
  have hapos : 0 < ‖y-G a‖ := lt_of_lt_of_le (by positivity : (0:ℝ) < (L:ℝ)*h) ha.1.le
  have hp : 1/‖y-G a‖^5 ≤ 32/‖y-G b‖^5 := by
    have he := one_div_le_one_div_of_le (pow_pos (by positivity : 0 < ‖y-G b‖/2) 5)
      (pow_le_pow_left₀ (by positivity : 0 ≤ ‖y-G b‖/2) ha.2.1 5)
    apply he.trans_eq
    field_simp
    norm_num
  apply (hbound G hG E hE hfix D hD hGD y a (norm_pos_iff.mp hapos)).trans
  exact mul_le_mul_of_nonneg_left (add_le_add hp (cellHits_indicator_le E b h hc)) (by positivity)

theorem transportedCoulomb_far_grid_hybrid_error :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (G : Position → Position), ContDiff ℝ 4 G →
      ∀ (E : Set Position), IsClosed E → (∀ x, x ∉ E → G x = x) →
      ∀ (D : ℝ), 1 ≤ D →
      (∀ x, ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ‖iteratedFDeriv ℝ k G x‖ ≤ D^k) →
      ∀ (L : ℝ≥0), 0 < L → LipschitzWith L G →
      ∀ {ι : Type} [Fintype ι] (index : ι → Fin 3 → ℤ)
        (y : Position) (h : ℝ), 0 < h →
      (∀ i, 4*(L:ℝ)*h ≤ ‖y-G (gaussCellCenter h (index i))‖) →
      |(∑ i, positionCellGauss (gaussCellCenter h (index i)) h
        (fun x => Coulomb.coulombKernel (y-G x)))-
        (∑ i, positionCellIntegral (gaussCellCenter h (index i)) h
          (fun x => Coulomb.coulombKernel (y-G x)))| ≤
        24*C*D^4*h^4*(32*(∑ i, h^3/‖y-G (gaussCellCenter h (index i))‖^5)+
          ∑ i, cellHits E (gaussCellCenter h (index i)) h*h^3) := by
  obtain ⟨C,hC,hbound⟩ := transportedCoulomb_far_cell_hybrid_error
  refine ⟨C,hC,?_⟩
  intro G hG E hE hfix D hD hGD L hL hLip ι _ index y h hh hfar
  have he := weighted_cubature_error h 1
    (fun i => positionCellGauss (gaussCellCenter h (index i)) h
      (fun x => Coulomb.coulombKernel (y-G x)))
    (fun i => positionCellIntegral (gaussCellCenter h (index i)) h
      (fun x => Coulomb.coulombKernel (y-G x)))
    (fun i => 24*C*D^4*(32/‖y-G (gaussCellCenter h (index i))‖^5+
      cellHits E (gaussCellCenter h (index i)) h))
    zero_le_one (fun i => hbound G hG E hE hfix D hD hGD L hL hLip y _ h hh (hfar i))
  simp only [one_mul] at he
  apply he.trans_eq
  have hs : (∑ i, (24*C*D^4*(32/‖y-G (gaussCellCenter h (index i))‖^5+
      cellHits E (gaussCellCenter h (index i)) h))*h^3) =
      (24*C*D^4)*(32*(∑ i, h^3/‖y-G (gaussCellCenter h (index i))‖^5)+
        ∑ i, cellHits E (gaussCellCenter h (index i)) h*h^3) := by
    calc
      _ = ∑ i, (24*C*D^4)*(32*(h^3/‖y-G (gaussCellCenter h (index i))‖^5)+
          cellHits E (gaussCellCenter h (index i)) h*h^3) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [← Finset.mul_sum,Finset.sum_add_distrib,← Finset.mul_sum]
  rw [hs]
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedFarGrid
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The far part of the actual manufactured nuclear quadrature. Its error
has no factor depending on the horizontal area of the enclosing slab. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical NNReal
namespace ContinuumCoulomb

theorem manufactured_moser_far_grid_error (hpublished : PublishedC4FlowInput) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (rho H S freq scale : ℝ) (m : ℕ) (u : Fin m → PlanarPosition),
      0 < rho → 0 ≤ H → 1 ≤ S →
      (∀ x, |manufacturedCharge (manufacturedWellField freq scale S u) x| ≤ rho/2) →
      tsupport (manufacturedWellField freq scale S u) ⊆ slabDomain H S →
      ∀ (G : Position → ℝ → Position),
      IsUnitTimeFlow (moserVelocity rho (manufacturedWellField freq scale S u)) G →
      Function.Bijective (fun x => G x 1) →
      (∀ x, x ∉ tsupport (manufacturedWellField freq scale S u) → G x 1 = x) →
      ∀ (D : ℝ), 1 ≤ D →
      (∀ x, ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ‖iteratedFDeriv ℝ k (fun x => G x 1) x‖ ≤ D^k) →
      ∀ (L : ℝ≥0), 0 < L → LipschitzWith L (fun x => G x 1) →
      ∀ {ι : Type} [Fintype ι] (index : ι → Fin 3 → ℤ), Function.Injective index →
      ∀ (y : Position) (h : ℝ), 0 < h → h ≤ 1 →
      (∀ i, positionCube (gaussCellCenter h (index i)) h ⊆ slabDomain H S) →
      (∀ i, 4*(L:ℝ)*h ≤ ‖y-G (gaussCellCenter h (index i)) 1‖) →
      |(∑ i, positionCellGauss (gaussCellCenter h (index i)) h
        (fun x => Coulomb.coulombKernel (y-G x 1)))-
        (∑ i, positionCellIntegral (gaussCellCenter h (index i)) h
          (fun x => Coulomb.coulombKernel (y-G x 1)))| ≤
        24*C*D^4*(3072*Real.pi*h^2/(L:ℝ)^2+216*m*S*h^4) := by
  obtain ⟨C,hC,hbound⟩ := transportedCoulomb_far_grid_hybrid_error
  refine ⟨C,hC,?_⟩
  intro rho H S freq scale m u hrho hH hS hcharge hsupp G hflow hbij hfix D hD hGD L hL hLip
    ι _ index hindex y h hh hh1 hsub hfar
  let V := manufacturedWellField freq scale S u
  have hV : ContDiff ℝ 6 V := (manufacturedWellField_C7 freq scale S u).of_le (by norm_num)
  have hGreg : ContDiff ℝ 4 (fun x => G x 1) :=
    (moser_flow_C4 hpublished hrho V hV hcharge G hflow).1 1 ⟨by norm_num,le_rfl⟩
  have he := hbound (fun x => G x 1) hGreg (tsupport V) (isClosed_tsupport V) hfix
    D hD hGD L hL hLip index y h hh hfar
  have ht := moser_inverseFifth_grid_sum_bound hpublished hrho hH (by linarith) V hV hcharge hsupp
    G hflow hbij hfix hL hLip index hindex hh hsub y hfar
  have hc := manufactured_cellHits_volume_bound index hindex hh hh1 hS freq scale u
  have hs : 32*(∑ i, h^3/‖y-G (gaussCellCenter h (index i)) 1‖^5)+
      (∑ i, cellHits (tsupport V) (gaussCellCenter h (index i)) h*h^3) ≤
      3072*Real.pi/((L:ℝ)*h)^2+216*m*S := by
    have hi := add_le_add (mul_le_mul_of_nonneg_left ht (by norm_num : (0:ℝ) ≤ 32)) hc
    convert hi using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hC0 : 0 ≤ C := (by norm_num : (0:ℝ) ≤ 1).trans hC
  apply he.trans
  apply (mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 24*C*D^4*h^4)).trans_eq
  have hLn : (L:ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hL)
  field_simp [hh.ne',hLn]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedGridError
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise nuclear replacement on any finite grid: the smooth error is
quadratic in the mesh, and the only singular remainder is an explicit sum of
near-node kernels, suitable for the proved weak-H1 estimate. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical NNReal
namespace ContinuumCoulomb

theorem gaussLatticePoint_mem_cube (h : ℝ) (hh : 0 ≤ h)
    (k : Fin 3 → ℤ) (v : Fin 3 → Fin 2) :
    gaussLatticePoint h (k,v) ∈ positionCube (gaussCellCenter h k) h := by
  rw [← cubePoint_gaussLatticePoint]
  have hb (i : Fin 3) : gaussNode (v i) ∈ Set.Icc (-1:ℝ) 1 := by
    have hg := gaussNode_bounds (v i)
    have ha := gaussAbscissa_bounds
    constructor <;> linarith
  exact cubePoint_mem_positionCube _ hh (hb 0) (hb 1) (hb 2)

theorem near_cell_gauss_truncated {h : ℝ} (hh : 0 < h)
    (G : Position → Position) {L : ℝ≥0} (hL : 0 < L) (hG : LipschitzWith L G)
    (y : Position) (k : Fin 3 → ℤ)
    (hnear : ‖y-G (gaussCellCenter h k)‖ ≤ 4*(L:ℝ)*h) :
    positionCellGauss (gaussCellCenter h k) h (fun x => Coulomb.coulombKernel (y-G x)) =
      (h^3/8)*∑ v : Fin 3 → Fin 2,
        Coulomb.truncatedCoulomb (6*(L:ℝ)*h) (y-G (gaussLatticePoint h (k,v))) := by
  rw [gaussCell_quadrature_lattice]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  exact transported_near_kernel_eq hh G hL hG hnear (gaussLatticePoint_mem_cube h hh.le k v)

theorem manufactured_moser_grid_error (hpublished : PublishedC4FlowInput) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (rho H S freq scale : ℝ) (m : ℕ) (u : Fin m → PlanarPosition),
      0 < rho → 0 ≤ H → 1 ≤ S →
      (∀ x, |manufacturedCharge (manufacturedWellField freq scale S u) x| ≤ rho/2) →
      tsupport (manufacturedWellField freq scale S u) ⊆ slabDomain H S →
      ∀ (G : Position → ℝ → Position),
      IsUnitTimeFlow (moserVelocity rho (manufacturedWellField freq scale S u)) G →
      Function.Bijective (fun x => G x 1) →
      (∀ x, x ∉ tsupport (manufacturedWellField freq scale S u) → G x 1 = x) →
      ∀ (D : ℝ), 1 ≤ D →
      (∀ x, ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ‖iteratedFDeriv ℝ k (fun x => G x 1) x‖ ≤ D^k) →
      ∀ (L : ℝ≥0), 0 < L → LipschitzWith L (fun x => G x 1) →
      ∀ {ι : Type} [Fintype ι] (index : ι → Fin 3 → ℤ), Function.Injective index →
      ∀ (y : Position) (h : ℝ), 0 < h → h ≤ 1 →
      (∀ i, positionCube (gaussCellCenter h (index i)) h ⊆ slabDomain H S) →
      |(∑ i, positionCellGauss (gaussCellCenter h (index i)) h
        (fun x => Coulomb.coulombKernel (y-G x 1)))-
        (∑ i, positionCellIntegral (gaussCellCenter h (index i)) h
          (fun x => Coulomb.coulombKernel (y-G x 1)))| ≤
        24*C*D^4*(3072*Real.pi*h^2/(L:ℝ)^2+216*m*S*h^4)+108*Real.pi*(L:ℝ)^2*h^2+
        (h^3/8)*∑ i, ∑ v : Fin 3 → Fin 2,
          Coulomb.truncatedCoulomb (6*(L:ℝ)*h) (y-G (gaussLatticePoint h (index i,v)) 1) := by
  obtain ⟨C,hC,hfar⟩ := manufactured_moser_far_grid_error hpublished
  refine ⟨C,hC,?_⟩
  intro rho H S freq scale m u hrho hH hS hcharge hsupp G hflow hbij hfix D hD hGD L hL hLip
    ι _ index hindex y h hh hh1 hsub
  let V := manufacturedWellField freq scale S u
  let p : ι → Prop := fun i => 4*(L:ℝ)*h ≤ ‖y-G (gaussCellCenter h (index i)) 1‖
  let Q : ι → ℝ := fun i => positionCellGauss (gaussCellCenter h (index i)) h
    (fun x => Coulomb.coulombKernel (y-G x 1))
  let I : ι → ℝ := fun i => positionCellIntegral (gaussCellCenter h (index i)) h
    (fun x => Coulomb.coulombKernel (y-G x 1))
  let T : ι → ℝ := fun i => ∑ v : Fin 3 → Fin 2,
    Coulomb.truncatedCoulomb (6*(L:ℝ)*h) (y-G (gaussLatticePoint h (index i,v)) 1)
  have hfi : Function.Injective (fun i : {i // p i} => index i.val) :=
    fun i j hij => Subtype.ext (hindex hij)
  have hni : Function.Injective (fun i : {i // ¬p i} => index i.val) :=
    fun i j hij => Subtype.ext (hindex hij)
  have hn (i : {i // ¬p i}) : ‖y-G (gaussCellCenter h (index i.val)) 1‖ ≤ 4*(L:ℝ)*h :=
    (lt_of_not_ge i.property).le
  have hf := hfar rho H S freq scale m u hrho hH hS hcharge hsupp G hflow hbij hfix D hD hGD
    L hL hLip (fun i : {i // p i} => index i.val) hfi y h hh hh1
    (fun i => hsub i.val) (fun i => i.property)
  have hV : ContDiff ℝ 6 V := (manufacturedWellField_C7 freq scale S u).of_le (by norm_num)
  have hnear := moser_near_grid_integral_bound hpublished hrho hH (by linarith) V hV hcharge hsupp
    G hflow hbij hfix hL hLip (fun i : {i // ¬p i} => index i.val) hni hh
    (fun i => hsub i.val) y hn
  have hQn : (∑ i : {i // ¬p i}, Q i.val) ≤ (h^3/8)*∑ i, T i := by
    calc
      _ = (h^3/8)*∑ i : {i // ¬p i}, T i.val := by
        simp only [Q,T,near_cell_gauss_truncated hh (fun x => G x 1) hL hLip y _ (hn _),
          Finset.mul_sum]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have he := Fintype.sum_subtype_add_sum_subtype p T
        have hp : 0 ≤ ∑ i : {i // p i}, T i.val :=
          Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
            (fun v _ => Coulomb.truncatedCoulomb_nonneg _ _))
        linarith
  have hIp : 0 ≤ ∑ i : {i // ¬p i}, I i.val := by
    apply Finset.sum_nonneg
    intro i _
    have hi := moser_coulomb_integrableOn hpublished hrho hH (by linarith) V hV hcharge hsupp
      G hflow hbij hfix y
    rw [show I i.val = ∫ x in positionCube (gaussCellCenter h (index i.val)) h,
        Coulomb.coulombKernel (y-G x 1) from
      positionCellIntegral_eq_setIntegral _ hh.le _ (hi.mono_set (hsub i.val))]
    exact setIntegral_nonneg (positionCube_isClosed _ _).measurableSet
      (fun x _ => Coulomb.coulombKernel_nonneg _)
  have hQp : 0 ≤ ∑ i : {i // ¬p i}, Q i.val := by
    apply Finset.sum_nonneg
    intro i _
    rw [show Q i.val = (h^3/8)*T i.val from
      near_cell_gauss_truncated hh (fun x => G x 1) hL hLip y _ (hn i)]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg
      (fun v _ => Coulomb.truncatedCoulomb_nonneg _ _))
  have heQ := Fintype.sum_subtype_add_sum_subtype p Q
  have heI := Fintype.sum_subtype_add_sum_subtype p I
  change |(∑ i, Q i)-(∑ i, I i)| ≤ _
  rw [← heQ,← heI]
  calc
    _ = |((∑ i : {i // p i}, Q i.val)-(∑ i : {i // p i}, I i.val))+
        ((∑ i : {i // ¬p i}, Q i.val)-(∑ i : {i // ¬p i}, I i.val))| := by congr 1; ring
    _ ≤ |(∑ i : {i // p i}, Q i.val)-(∑ i : {i // p i}, I i.val)|+
        |(∑ i : {i // ¬p i}, Q i.val)-(∑ i : {i // ¬p i}, I i.val)| := abs_add_le _ _
    _ ≤ _ := by
      have hnabs := abs_add_le (∑ i : {i // ¬p i}, Q i.val) (-(∑ i : {i // ¬p i}, I i.val))
      simp only [← sub_eq_add_neg,abs_neg,abs_of_nonneg hQp,abs_of_nonneg hIp] at hnabs
      change |(∑ i : {i // p i}, Q i.val)-(∑ i : {i // p i}, I i.val)| ≤ _ at hf
      change (∑ i : {i // ¬p i}, I i.val) ≤ _ at hnear
      change _ ≤ _ + _ + (h^3/8)*∑ i, T i
      linarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_NuclearGridPotential
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual equal-mass grid potential and its error against the
manufactured continuous potential, at every evaluation point. -/

noncomputable section
open MeasureTheory
open scoped BigOperators NNReal
namespace ContinuumCoulomb

theorem gridNuclearPotential_measurable {ι : Type*} [Fintype ι] (index : ι → Fin 3 → ℤ)
    (G : Position → Position) (rho h : ℝ) : Measurable (gridNuclearPotential index G rho h) := by
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro a _
  exact Coulomb.coulombKernel_measurable.comp (measurable_id.sub measurable_const)

theorem gridNuclearPotential_eq_cells {ι : Type*} [Fintype ι] (index : ι → Fin 3 → ℤ)
    (G : Position → Position) (rho h : ℝ) (y : Position) :
    gridNuclearPotential index G rho h y = -rho*(∑ i,
      positionCellGauss (gaussCellCenter h (index i)) h (fun x => Coulomb.coulombKernel (y-G x))) := by
  simp only [gridNuclearPotential,gridGaussIndex,Fintype.sum_prod_type,
    gaussCell_quadrature_lattice,← Finset.mul_sum]
  ring

theorem manufactured_grid_potential_error (hpublished : PublishedC4FlowInput) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (rho H S freq scale : ℝ) (m : ℕ) (u : Fin m → PlanarPosition),
      0 < rho → 0 ≤ H → 1 ≤ S →
      (∀ x, |manufacturedCharge (manufacturedWellField freq scale S u) x| ≤ rho/2) →
      tsupport (manufacturedWellField freq scale S u) ⊆ slabDomain H S →
      ∀ (G : Position → ℝ → Position),
      IsUnitTimeFlow (moserVelocity rho (manufacturedWellField freq scale S u)) G →
      Function.Bijective (fun x => G x 1) →
      (∀ x, x ∉ tsupport (manufacturedWellField freq scale S u) → G x 1 = x) →
      ∀ (D : ℝ), 1 ≤ D →
      (∀ x, ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ‖iteratedFDeriv ℝ k (fun x => G x 1) x‖ ≤ D^k) →
      ∀ (L : ℝ≥0), 0 < L → LipschitzWith L (fun x => G x 1) →
      ∀ {ι : Type} [Fintype ι] (index : ι → Fin 3 → ℤ), Function.Injective index →
      ∀ (h : ℝ), 0 < h → h ≤ 1 →
      (⋃ i, positionCube (gaussCellCenter h (index i)) h) = slabDomain H S →
      ∀ y : Position,
      |gridNuclearPotential index (fun x => G x 1) rho h y-
        (slabPotential rho H S y+manufacturedWellField freq scale S u y)| ≤
      rho*(24*C*D^4*(3072*Real.pi*h^2/(L:ℝ)^2+216*m*S*h^4)+108*Real.pi*(L:ℝ)^2*h^2)+
        (rho*h^3/8)*∑ a : ι × (Fin 3 → Fin 2),
          Coulomb.truncatedCoulomb (6*(L:ℝ)*h) (y-G (gaussLatticePoint h (gridGaussIndex index a)) 1) := by
  obtain ⟨C,hC,hbound⟩ := manufactured_moser_grid_error hpublished
  refine ⟨C,hC,?_⟩
  intro rho H S freq scale m u hrho hH hS hcharge hsupp G hflow hbij hfix D hD hGD L hL hLip
    ι _ index hindex h hh hh1 hcover y
  have hsub (i : ι) : positionCube (gaussCellCenter h (index i)) h ⊆ slabDomain H S := by
    rw [← hcover]
    exact Set.subset_iUnion_of_subset i (fun _ hx => hx)
  have he := hbound rho H S freq scale m u hrho hH hS hcharge hsupp G hflow hbij hfix D hD hGD
    L hL hLip index hindex y h hh hh1 hsub
  have hp := moser_grid_potential hpublished hrho hH (by linarith) hh
    (manufacturedWellField freq scale S u) ((manufacturedWellField_C7 freq scale S u).of_le (by norm_num))
    (manufacturedWellField_compact freq scale (by linarith) u) hcharge hsupp G hflow hbij hfix index hindex hcover y
  rw [gridNuclearPotential_eq_cells,← hp]
  have ha (a b : ℝ) : |-rho*a-(-rho*b)| = rho*|a-b| := by
    rw [show -rho*a-(-rho*b) = -(rho*(a-b)) by ring,abs_neg,abs_mul,abs_of_pos hrho]
  rw [ha]
  apply (mul_le_mul_of_nonneg_left he hrho.le).trans_eq
  simp only [Fintype.sum_prod_type,gridGaussIndex]
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_AbsoluteNuclearForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute-value form bound for unit-nucleus replacement. It holds
for every spin component of every many-electron weak-H1 state. -/

noncomputable section
open MeasureTheory
open scoped BigOperators NNReal
namespace ContinuumCoulomb

theorem manufactured_grid_absolute_form_error (hpublished : PublishedC4FlowInput)
    (L K : ℝ≥0) (hL : 0 < L) (hK : 0 < K) :
    ∃ C A : ℝ, 1 ≤ C ∧ 1 ≤ A ∧
    ∀ (rho H S freq scale : ℝ) (m : ℕ) (u : Fin m → PlanarPosition),
      0 < rho → 0 ≤ H → 1 ≤ S →
      (∀ x, |manufacturedCharge (manufacturedWellField freq scale S u) x| ≤ rho/2) →
      tsupport (manufacturedWellField freq scale S u) ⊆ slabDomain H S →
      ∀ (G : Position → ℝ → Position),
      IsUnitTimeFlow (moserVelocity rho (manufacturedWellField freq scale S u)) G →
      Function.Bijective (fun x => G x 1) →
      (∀ x, x ∉ tsupport (manufacturedWellField freq scale S u) → G x 1 = x) →
      ∀ (D : ℝ), 1 ≤ D →
      (∀ x, ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ‖iteratedFDeriv ℝ k (fun x => G x 1) x‖ ≤ D^k) →
      LipschitzWith L (fun x => G x 1) → AntilipschitzWith K (fun x => G x 1) →
      ∀ {ι : Type} [Fintype ι] (index : ι → Fin 3 → ℤ), Function.Injective index →
      ∀ (h : ℝ), 0 < h → h ≤ 1 →
      (⋃ i, positionCube (gaussCellCenter h (index i)) h) = slabDomain H S →
      ∀ (n : ℕ) (w : Coulomb.H1Vector n) (s : SpinConfiguration n) (i : Fin n),
      Integrable (fun x => |gridNuclearPotential index (fun x => G x 1) rho h (Coulomb.position x i)-
        (slabPotential rho H S (Coulomb.position x i)+
          manufacturedWellField freq scale S u (Coulomb.position x i))| * ‖w.value s x‖^2) ∧
      (∫ x, |gridNuclearPotential index (fun x => G x 1) rho h (Coulomb.position x i)-
        (slabPotential rho H S (Coulomb.position x i)+
          manufacturedWellField freq scale S u (Coulomb.position x i))| *‖w.value s x‖^2) ≤
      rho*(24*C*D^4*(3072*Real.pi*h^2/(L:ℝ)^2+216*m*S*h^4)+108*Real.pi*(L:ℝ)^2*h^2)*
        (∫ x, ‖w.value s x‖^2)+
      rho*A*h^2*((∫ x, ‖w.value s x‖^2)+∑ k : Fin 3, ∫ x, ‖w.gradient s (i,k) x‖^2) := by
  obtain ⟨C,hC,hpoint⟩ := manufactured_grid_potential_error hpublished
  have hκ : 0 < 6*(L:ℝ) := by positivity
  obtain ⟨A,hA,hnear⟩ := transportedGauss_truncated_form hκ K hK
  refine ⟨C,A,hC,hA,?_⟩
  intro rho H S freq scale m u hrho hH hS hcharge hsupp G hflow hbij hfix D hD hGD hLip hAnti
    ι _ index hindex h hh hh1 hcover n w s i
  let F : Position → ℝ := fun y => gridNuclearPotential index (fun x => G x 1) rho h y-
    (slabPotential rho H S y+manufacturedWellField freq scale S u y)
  let B := rho*(24*C*D^4*(3072*Real.pi*h^2/(L:ℝ)^2+216*m*S*h^4)+108*Real.pi*(L:ℝ)^2*h^2)
  let R : ι × (Fin 3 → Fin 2) → Position := fun a => G (gaussLatticePoint h (gridGaussIndex index a)) 1
  have hF : Measurable F := (gridNuclearPotential_measurable index (fun x => G x 1) rho h).sub
    (((slabPotential_continuous hrho.le hH (by linarith)).add
      (manufacturedWellField_C7 freq scale S u).continuous).measurable)
  have he := weighted_potential_absolute_bound w s i F hF R (6*(L:ℝ)*h) B (rho*h^3/8)
    (hpoint rho H S freq scale m u hrho hH hS hcharge hsupp G hflow hbij hfix
      D hD hGD L hL hLip index hindex h hh hh1 hcover)
  have hn := hnear n w s i h rho hh hh1 hrho.le (gridGaussIndex index)
    (gridGaussIndex_injective index hindex) (fun x => G x 1) hAnti
  exact ⟨he.1, he.2.trans (add_le_add le_rfl hn)⟩

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

theorem manufacturedFieldDerivativeConstant_positive : 0 < manufacturedFieldDerivativeConstant := by
  have hp := planarWellDerivativeConstant_positive
  have hc := (Classical.choose_spec cutoff_derivative_bound_exists).1
  unfold manufacturedFieldDerivativeConstant wellCutoffDerivativeBound
    wellPlanarDerivativeBound wellCutoffDerivativeConstant
  positivity

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedUniformFlow
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The same integer background density and the same flow derivative
constant work for every separated manufactured well family. -/

noncomputable section
namespace ContinuumCoulomb

/-- The background density is selected before the size, sites, field scale,
or slab width. Thus the published flow input has uniform constants. -/
theorem manufactured_uniform_density_and_flow (hpublished : PublishedC4FlowInput) :
    ∃ rho : ℕ, 0 < rho ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (freq scale S : ℝ), 0 < scale → 1 ≤ S →
      ∀ (m : ℕ) (u : Fin m → PlanarPosition),
      (∀ i j, i ≠ j → 3 ≤ ‖u i-u j‖) →
      (∀ i, localizedCounterterm freq u i ≤ scale) →
      (∀ x, |manufacturedCharge (manufacturedWellField freq scale S u) x| ≤ (rho:ℝ)/2) ∧
      (∀ G : Position → ℝ → Position,
        IsUnitTimeFlow (moserVelocity rho (manufacturedWellField freq scale S u)) G →
        ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x,
          ‖iteratedFDeriv ℝ k (fun y => G y t) x‖ ≤ C) := by
  let B := manufacturedFieldDerivativeConstant
  have hB : 0 < B := manufacturedFieldDerivativeConstant_positive
  obtain ⟨rho,hrho⟩ := exists_nat_gt (max (1:ℝ) (6*B/(4*Real.pi)))
  have hrhop : 0 < rho := by
    have h : (1:ℝ) < rho := (le_max_left _ _).trans_lt hrho
    exact_mod_cast (lt_trans zero_lt_one h)
  have hrhopR : (0:ℝ) < rho := by exact_mod_cast hrhop
  obtain ⟨C,hC,hCb⟩ := moserFlow_family_derivative_bound hpublished hrhopR hB.le
  refine ⟨rho,hrhop,C,hC,?_⟩
  intro freq scale S hscale hS m u hsep hcounter
  let V := manufacturedWellField freq scale S u
  have hV : ContDiff ℝ 6 V := (manufacturedWellField_C7 freq scale S u).of_le (by norm_num)
  have hb (k : ℕ) (hk : k ≤ 6) (x : Position) : ‖iteratedFDeriv ℝ k V x‖ ≤ B :=
    manufacturedWellField_derivative_bound freq hscale hS u hsep hcounter hk x
  have hc (x : Position) : |manufacturedCharge V x| ≤ (rho:ℝ)/2 := by
    have h := manufacturedCharge_derivative_bound V hV hB.le hb (k := 0) (by norm_num) x
    simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
    have h' : 6*B/(4*Real.pi) < rho := (le_max_right _ _).trans_lt hrho
    have he : 6*B/(4*Real.pi) = 2*(3*B/(4*Real.pi)) := by ring
    rw [he] at h'
    linarith
  exact ⟨hc, hCb V hV hb hc⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedTransport
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual manufactured fields admit transport maps with common
C4 and inverse Lipschitz constants, chosen before the instance. -/

noncomputable section
open scoped NNReal
namespace ContinuumCoulomb

theorem manufactured_transport_family_with_charge (hpublished : PublishedC4FlowInput) :
    ∃ rho : ℕ, 0 < rho ∧ ∃ L K : ℝ≥0, 0 < L ∧ 0 < K ∧
      ∀ (freq scale S : ℝ), 0 < scale → 1 ≤ S →
      ∀ (m : ℕ) (u : Fin m → PlanarPosition),
      (∀ i j, i ≠ j → 3 ≤ ‖u i-u j‖) →
      (∀ i, localizedCounterterm freq u i ≤ scale) →
      (∀ x, |manufacturedCharge (manufacturedWellField freq scale S u) x| ≤ (rho:ℝ)/2) ∧
      ∃ G : Position → ℝ → Position,
        IsUnitTimeFlow (moserVelocity rho (manufacturedWellField freq scale S u)) G ∧
        Function.Bijective (fun x => G x 1) ∧
        LipschitzWith L (fun x => G x 1) ∧ AntilipschitzWith K (fun x => G x 1) ∧
        (∀ x, x ∉ tsupport (manufacturedWellField freq scale S u) → G x 1 = x) ∧
        ContDiff ℝ 4 (fun x => G x 1) ∧
        (∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ x,
          ‖iteratedFDeriv ℝ k (fun y => G y 1) x‖ ≤ L) := by
  obtain ⟨rho,hrho,D,hD,hfamily⟩ := manufactured_uniform_density_and_flow hpublished
  have hrhop : (0:ℝ) < rho := by exact_mod_cast hrho
  obtain ⟨K,hK,hKb⟩ := moserFlow_family_inverse_bound hrhop
    manufacturedFieldDerivativeConstant_positive.le
  refine ⟨rho,hrho,⟨D,hD.le⟩,K,by exact_mod_cast hD,hK,?_⟩
  intro freq scale S hscale hS m u hsep hcounter
  let V := manufacturedWellField freq scale S u
  have hV : ContDiff ℝ 6 V := (manufacturedWellField_C7 freq scale S u).of_le (by norm_num)
  obtain ⟨hc,hderiv⟩ := hfamily freq scale S hscale hS m u hsep hcounter
  refine ⟨hc,?_⟩
  obtain ⟨G,C,Cinv,D',hD',hflow,hbij,hLip,hAnti,hfix,hreg,hderiv'⟩ :=
    moser_C4_bilipschitz_flow_exists hpublished hrhop V hV
      (manufacturedWellField_compact freq scale (lt_of_lt_of_le zero_lt_one hS) u) hc
  have h1 : (1:ℝ) ∈ Set.Icc 0 1 := ⟨by norm_num,le_rfl⟩
  have hDb (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 4) (x : Position) :
      ‖iteratedFDeriv ℝ k (fun y => G y 1) x‖ ≤ D := hderiv G hflow k hk hk' 1 h1 x
  have hLipD : LipschitzWith (⟨D,hD.le⟩ : ℝ≥0) (fun x => G x 1) :=
    lipschitzWith_of_nnnorm_fderiv_le (hreg.differentiable (by norm_num)) (fun x => by
      have h := hDb 1 (by norm_num) (by norm_num) x
      rw [norm_iteratedFDeriv_one] at h
      exact_mod_cast h)
  have hAntiK := hKb V hV
    (fun k hk x => manufacturedWellField_derivative_bound freq hscale hS u hsep hcounter hk x)
    hc G hflow
  exact ⟨G,hflow,hbij,hLipD,hAntiK,hfix,hreg,hDb⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_UniformAbsoluteNuclearForm
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One fixed integer background density and one fixed constant suffice
for the absolute nuclear replacement form estimate over the whole family. -/

noncomputable section
open MeasureTheory
open scoped BigOperators NNReal
namespace ContinuumCoulomb

theorem manufactured_uniform_nuclear_absolute_form_oai (hpublished : PublishedC4FlowInput) :
    ∃ rho : ℕ, 0 < rho ∧ ∃ L K : ℝ≥0, 0 < L ∧ 0 < K ∧ ∃ B : ℝ, 1 ≤ B ∧
    ∀ (freq scale S : ℝ), 0 < scale → 1 ≤ S →
      ∀ (m : ℕ) (u : Fin m → PlanarPosition),
      (∀ i j, i ≠ j → 3 ≤ ‖u i-u j‖) →
      (∀ i, localizedCounterterm freq u i ≤ scale) →
      ∃ G : Position → ℝ → Position,
        IsUnitTimeFlow (moserVelocity rho (manufacturedWellField freq scale S u)) G ∧
        Function.Bijective (fun x => G x 1) ∧
        LipschitzWith L (fun x => G x 1) ∧ AntilipschitzWith K (fun x => G x 1) ∧
        (∀ x, x ∉ tsupport (manufacturedWellField freq scale S u) → G x 1 = x) ∧
        (∀ x, |manufacturedCharge (manufacturedWellField freq scale S u) x| ≤ (rho:ℝ)/2) ∧
        ContDiff ℝ 4 (fun x => G x 1) ∧
        (∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ k (fun y => G y 1) x‖ ≤ L) ∧
      ∀ (H : ℝ), 0 ≤ H → tsupport (manufacturedWellField freq scale S u) ⊆ slabDomain H S →
      ∀ {ι : Type} [Fintype ι] (index : ι → Fin 3 → ℤ), Function.Injective index →
      ∀ (h : ℝ), 0 < h → h ≤ 1 → (m:ℝ)*S*h^2 ≤ 1 →
      (⋃ i, positionCube (gaussCellCenter h (index i)) h) = slabDomain H S →
      ∀ (n : ℕ) (w : Coulomb.H1Vector n) (s : SpinConfiguration n) (i : Fin n),
      Integrable (fun x => |gridNuclearPotential index (fun x => G x 1) rho h (Coulomb.position x i)-
        (slabPotential rho H S (Coulomb.position x i)+
          manufacturedWellField freq scale S u (Coulomb.position x i))| * ‖w.value s x‖^2) ∧
      (∫ x, |gridNuclearPotential index (fun x => G x 1) rho h (Coulomb.position x i)-
        (slabPotential rho H S (Coulomb.position x i)+
          manufacturedWellField freq scale S u (Coulomb.position x i))| *‖w.value s x‖^2) ≤
      B*h^2*((∫ x, ‖w.value s x‖^2)+∑ k : Fin 3, ∫ x, ‖w.gradient s (i,k) x‖^2) := by
  obtain ⟨rho,hrho,L,K,hL,hK,hfamily⟩ := manufactured_transport_family_with_charge hpublished
  obtain ⟨C,A,hC,hA,hform⟩ := manufactured_grid_absolute_form_error hpublished L K hL hK
  let D : ℝ := max 1 (L:ℝ)
  let E : ℝ := (rho:ℝ)*(24*C*D^4*(3072*Real.pi/(L:ℝ)^2+216)+108*Real.pi*(L:ℝ)^2)
  let B : ℝ := max 1 (E+(rho:ℝ)*A)
  have hD : 1 ≤ D := le_max_left _ _
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hrhoR : (0:ℝ) < rho := by exact_mod_cast hrho
  refine ⟨rho,hrho,L,K,hL,hK,B,le_max_left _ _,?_⟩
  intro freq scale S hscale hS m u hsep hcounter
  obtain ⟨hcharge,G,hflow,hbij,hLip,hAnti,hfix,hreg,hjets⟩ :=
    hfamily freq scale S hscale hS m u hsep hcounter
  refine ⟨G,hflow,hbij,hLip,hAnti,hfix,hcharge,hreg,hjets,?_⟩
  intro H hH hsupp ι _ index hindex h hh hh1 hmesh hcover n w s i
  have hGD (x : Position) (k : ℕ) (hk : 1 ≤ k) (hk4 : k ≤ 4) :
      ‖iteratedFDeriv ℝ k (fun x => G x 1) x‖ ≤ D^k := by
    apply (hjets k hk hk4 x).trans
    exact (le_max_right 1 (L:ℝ)).trans (by simpa only [pow_one] using pow_le_pow_right₀ hD hk)
  have he := hform rho H S freq scale m u hrhoR hH hS hcharge hsupp G hflow hbij hfix D hD hGD
    hLip hAnti index hindex h hh hh1 hcover n w s i
  have hmass : 0 ≤ ∫ x, ‖w.value s x‖^2 := integral_nonneg (fun _ => sq_nonneg _)
  have hgrad : 0 ≤ ∑ k : Fin 3, ∫ x, ‖w.gradient s (i,k) x‖^2 :=
    Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
  have hsize : (m:ℝ)*S*h^4 ≤ h^2 := by
    calc
      _ = h^2*((m:ℝ)*S*h^2) := by ring
      _ ≤ h^2*1 := mul_le_mul_of_nonneg_left hmesh (sq_nonneg h)
      _ = _ := mul_one _
  have hb : (rho:ℝ)*(24*C*D^4*(3072*Real.pi*h^2/(L:ℝ)^2+216*m*S*h^4)+
      108*Real.pi*(L:ℝ)^2*h^2) ≤ E*h^2 := by
    have hs := mul_le_mul_of_nonneg_left hsize (by norm_num : (0:ℝ) ≤ 216)
    have ht := mul_le_mul_of_nonneg_left
      (add_le_add_left hs (3072*Real.pi*h^2/(L:ℝ)^2)) (by positivity : 0 ≤ 24*C*D^4)
    have ht' := mul_le_mul_of_nonneg_left
      (add_le_add_right ht (108*Real.pi*(L:ℝ)^2*h^2)) hrhoR.le
    dsimp only [E]
    first | (convert ht' using 1 <;> ring) | exact (le_of_eq (by ring)).trans (ht'.trans (le_of_eq (by ring)))
  refine ⟨he.1, he.2.trans ?_⟩
  calc
    _ ≤ E*h^2*(∫ x, ‖w.value s x‖^2)+(rho:ℝ)*A*h^2*
        ((∫ x, ‖w.value s x‖^2)+∑ k : Fin 3, ∫ x, ‖w.gradient s (i,k) x‖^2) :=
      add_le_add (mul_le_mul_of_nonneg_right hb hmass) le_rfl
    _ ≤ (E+(rho:ℝ)*A)*h^2*
        ((∫ x, ‖w.value s x‖^2)+∑ k : Fin 3, ∫ x, ‖w.gradient s (i,k) x‖^2) := by
      nlinarith [mul_nonneg (mul_nonneg hE (sq_nonneg h)) hgrad]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (show E+(rho:ℝ)*A ≤ B from le_max_right _ _) (sq_nonneg h))
      (add_nonneg hmass hgrad)

end ContinuumCoulomb

end

end OAI
end

theorem solution : type_of% @OAI.ContinuumCoulomb.manufactured_uniform_nuclear_absolute_form_oai := @OAI.ContinuumCoulomb.manufactured_uniform_nuclear_absolute_form_oai
