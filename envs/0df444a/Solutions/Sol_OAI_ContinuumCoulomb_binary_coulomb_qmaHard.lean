-- Prove2me | solution 1 for OAI.ContinuumCoulomb.binary_coulomb_qmaHard
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:20:17.123735+00:00
-- url     : https://prove2.me/submissions/02ee578d-1436-4561-b501-df80cf9d20a6

import Mathlib
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Hom.PowersetCard
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.UpperLower.Basic
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Moments.Variance
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_OAIQ092A008
import Definitions.Def_OAIQ092A009
import Theorems.Thm_OAI_ContinuumCoulomb_binary_coulomb_qmaHard_of_two_inputs
import Theorems.Thm_OAI_ContinuumCoulomb_publishedCMPHardness

section
-- module Solutions.OAIQ092_CC.BiholderTransport_Calculus_ImplicitNeighborhood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

lemma endomorphism_isInvertible_iff_isUnit (L : Y →L[ℝ] Y) : L.IsInvertible ↔ IsUnit L := by
  constructor
  · rintro ⟨e,rfl⟩
    exact ContinuousLinearMap.isUnit_iff_bijective.mpr e.bijective
  · intro h
    have hb := ContinuousLinearMap.isUnit_iff_bijective.mp h
    exact ⟨ContinuousLinearEquiv.ofBijective L (LinearMap.ker_eq_bot.mpr hb.1)
      (LinearMap.range_eq_top.mpr hb.2),rfl⟩

lemma isOpen_invertible_endomorphism : IsOpen {L : Y →L[ℝ] Y | L.IsInvertible} := by
  simpa only [endomorphism_isInvertible_iff_isUnit] using
    (Units.isOpen : IsOpen {L : Y →L[ℝ] Y | IsUnit L})

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.BiholderTransport_Calculus_PathCalculus
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
universe u w
variable {K : Type w} {E F : Type u} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

attribute [local instance] OAI.WeakMTWTransport.pathCalculusNormedAddCommGroupContinuousMap
lemma hasFDerivAt_path_comp (f : C(E,F)) (f' : C(E,E →L[ℝ] F))
    (hder : ∀ x, HasFDerivAt f (f' x) x) (u : C(K,E)) :
    HasFDerivAt (fun v : C(K,E) => f.comp v) (pathLinearApply (f'.comp u)) u := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero,Asymptotics.isLittleO_iff]
  intro ε hε
  have hc : IsCompact (range u) := isCompact_range u.continuous
  have huni := hc.uniformContinuousAt_of_continuousAt f'
    (fun _ _ => f'.continuous.continuousAt)
    (r := {z : (E →L[ℝ] F) × (E →L[ℝ] F) | dist z.1 z.2 < ε})
    (Metric.mem_uniformity_dist.mpr ⟨ε,hε,fun {_ _} h => h⟩)
  obtain ⟨δ,hδ,hclose⟩ := Metric.mem_uniformity_dist.mp huni
  filter_upwards [Metric.ball_mem_nhds (0:C(K,E)) hδ] with v hv
  have hvnorm : ‖v‖ < δ := by simpa using hv
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg v))).mpr
  intro t
  have hbound : ∀ z ∈ Metric.ball (u t) δ, ‖f' z - f' (u t)‖ ≤ ε := by
    intro z hz
    have hh := hclose (by simpa only [Metric.mem_ball,dist_comm] using hz) (mem_range_self t)
    change dist (f' (u t)) (f' z) < ε at hh
    exact le_of_lt (by simpa only [dist_eq_norm, norm_sub_rev] using hh)
  have hb : u t + v t ∈ Metric.ball (u t) δ := by
    rw [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left]
    exact (v.norm_coe_le_norm t).trans_lt hvnorm
  have hm := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z (_ : z ∈ Metric.ball (u t) δ) => (hder z).hasFDerivWithinAt)
    hbound (convex_ball (u t) δ) (Metric.mem_ball_self hδ) hb
  have heq : ((f.comp (u+v) - f.comp u - pathLinearApply (f'.comp u) v) t) =
      f (u t + v t) - f (u t) - f' (u t) ((u t + v t) - u t) := by
    simp only [ContinuousMap.sub_apply,ContinuousMap.comp_apply,ContinuousMap.add_apply,
      pathLinearApply_apply,add_sub_cancel_left]
  rw [heq]
  exact hm.trans (by simpa only [add_sub_cancel_left] using
    mul_le_mul_of_nonneg_left (v.norm_coe_le_norm t) hε.le)

attribute [local instance] OAI.WeakMTWTransport.pathCalculusNormedAddCommGroupContinuousLinearMap
attribute [local instance] OAI.WeakMTWTransport.pathCalculusNormedSpaceContinuousLinearMap
lemma contDiff_path_comp_nat (m : ℕ) (f : C(E,F)) (hf : ContDiff ℝ m f) :
    ContDiff ℝ m (fun v : C(K,E) => f.comp v) := by
  induction m generalizing F with
  | zero => exact contDiff_zero.mpr f.continuous_postcomp
  | succ m ih =>
    obtain ⟨f',hf',hder⟩ := contDiff_succ_iff_hasFDerivAt.mp hf
    let F' : C(E,E →L[ℝ] F) := ⟨f',hf'.continuous⟩
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨fun v => pathLinearApply (F'.comp v),?_,?_⟩
    · exact (pathLinearApplyL (K := K) (E := E) (F := F)).contDiff.comp
        (ih F' hf')
    · intro u; exact hasFDerivAt_path_comp f F' hder u

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.BiholderTransport_Regularity_UnitTime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma hasDerivAt_unitPathPrimitive [CompleteSpace E] (u : C(UnitTime,E)) (t : ℝ) :
    HasDerivAt (fun s => ∫ r in (0:ℝ)..s, extendUnitPath u r) (extendUnitPath u t) t :=
  intervalIntegral.integral_hasDerivAt_right
    ((extendUnitPath u).continuous.intervalIntegrable 0 t)
    (extendUnitPath u).continuous.stronglyMeasurable.stronglyMeasurableAtFilter
    (extendUnitPath u).continuous.continuousAt

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.BiholderTransport_LocalFlow_ImplicitODE
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma rescaledIntegralCurve_eq (f : C(E,E)) (t : ℝ) (x : E) (u : C(UnitTime,E))
    (hu : u = ContinuousMap.const UnitTime x + t • unitPathIntegral (f.comp u)) (s : UnitTime) :
    rescaledIntegralCurve f t x u s = u s := by
  have h := congrArg (fun v : C(UnitTime,E) => v s) hu
  exact h.symm

lemma hasDerivAt_rescaledIntegralCurve (f : C(E,E)) (t : ℝ) (x : E) (u : C(UnitTime,E))
    (hu : u = ContinuousMap.const UnitTime x + t • unitPathIntegral (f.comp u))
    (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
    HasDerivAt (rescaledIntegralCurve f t x u) (t • f (rescaledIntegralCurve f t x u s)) s := by
  have hd := ((hasDerivAt_unitPathPrimitive (f.comp u) s).const_smul t).const_add x
  have hc := rescaledIntegralCurve_eq f t x u hu ⟨s,hs⟩
  have he : extendUnitPath (f.comp u) s = f (rescaledIntegralCurve f t x u s) := by
    rw [hc]
    exact extendUnitPath_coe (f.comp u) ⟨s,hs⟩
  change HasDerivAt (rescaledIntegralCurve f t x u)
    (t • extendUnitPath (f.comp u) s) s at hd
  rw [he] at hd
  exact hd

omit [CompleteSpace E] in
lemma lipschitzOnWith_const_smul {f : E → E} {K : ℝ≥0} {B : Set E}
    (hf : LipschitzOnWith K f B) (t : ℝ) :
    LipschitzOnWith (‖t‖₊ * K) (fun x => t • f x) B := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [dist_eq_norm,←smul_sub,norm_smul,NNReal.coe_mul,coe_nnnorm,mul_assoc]
  simpa only [dist_eq_norm] using
    mul_le_mul_of_nonneg_left (hf.dist_le_mul x hx y hy) (norm_nonneg t)

lemma rescaled_ode_path_time_scaling (f : C(E,E)) (t : ℝ) (x : E)
    (u v : C(UnitTime,E)) (s : UnitTime) (K : ℝ≥0) (B : Set E)
    (hf : LipschitzOnWith K f B)
    (hu : u = ContinuousMap.const UnitTime x + t • unitPathIntegral (f.comp u))
    (hv : v = ContinuousMap.const UnitTime x + (t * s.val) • unitPathIntegral (f.comp v))
    (huB : ∀ r, u r ∈ B) (hvB : ∀ r, v r ∈ B) :
    u s = v ⟨1,by simp⟩ := by
  let U := rescaledIntegralCurve f t x u
  let V := rescaledIntegralCurve f (t*s.val) x v
  have hsr : ∀ r ∈ Icc (0:ℝ) 1, s.val * r ∈ Icc (0:ℝ) 1 := by
    intro r hr
    exact ⟨mul_nonneg s.property.1 hr.1,
      (mul_le_of_le_one_left hr.1 s.property.2).trans hr.2⟩
  have hU : ∀ r ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun q => U (s.val*q)) ((t*s.val) • f (U (s.val*r))) r := by
    intro r hr
    have h := (hasDerivAt_rescaledIntegralCurve f t x u hu (s.val*r) (hsr r hr)).scomp r
      ((hasDerivAt_id r).const_mul s.val)
    simpa only [mul_one,smul_smul,mul_comm,Function.comp_def,U] using h
  have hV : ∀ r ∈ Icc (0:ℝ) 1, HasDerivAt V ((t*s.val) • f (V r)) r :=
    hasDerivAt_rescaledIntegralCurve f (t*s.val) x v hv
  have hEq : EqOn (fun q => U (s.val*q)) V (Icc (0:ℝ) 1) := by
    apply ODE_solution_unique_of_mem_Icc_right
      (v := fun (_ : ℝ) z => (t*s.val) • f z) (s := fun _ => B) (K := ‖t*s.val‖₊ * K)
    · intro r hr; exact lipschitzOnWith_const_smul hf (t*s.val)
    · exact HasDerivAt.continuousOn hU
    · intro r hr; exact (hU r (Ico_subset_Icc_self hr)).hasDerivWithinAt
    · intro r hr
      dsimp only [U]
      rw [rescaledIntegralCurve_eq f t x u hu ⟨s.val*r,hsr r (Ico_subset_Icc_self hr)⟩]
      exact huB _
    · exact HasDerivAt.continuousOn hV
    · intro r hr; exact (hV r (Ico_subset_Icc_self hr)).hasDerivWithinAt
    · intro r hr
      dsimp only [V]
      rw [rescaledIntegralCurve_eq f (t*s.val) x v hv ⟨r,Ico_subset_Icc_self hr⟩]
      exact hvB _
    · simp only [U,V,mul_zero,rescaledIntegralCurve_zero]
  have h := hEq (by simp : (1:ℝ) ∈ Icc (0:ℝ) 1)
  change U (s.val*1) = V 1 at h
  simpa only [mul_one,U,V,rescaledIntegralCurve_eq f t x u hu s,
    rescaledIntegralCurve_eq f (t*s.val) x v hv ⟨1,by simp⟩] using h

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.BiholderTransport_LocalFlow_SmoothFlowEndpoint
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

namespace WeakMTWTransport

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma ode_family_initial {f : C(E,E)} {U : (ℝ × E) → C(UnitTime,E)} {x : E}
    (h : U (0,x) = ContinuousMap.const UnitTime x +
      (0:ℝ) • unitPathIntegral (f.comp (U (0,x)))) :
    U (0,x) = ContinuousMap.const UnitTime x := by simpa using h

lemma ode_family_endpoint_deriv_ne_zero (f : C(E,E))
    (U : (ℝ × E) → C(UnitTime,E)) (S : Set (ℝ × E)) (hS : IsOpen S)
    (hEq : ∀ z ∈ S, U z = ContinuousMap.const UnitTime z.2 +
      z.1 • unitPathIntegral (f.comp (U z)))
    (K : ℝ≥0) (B : Set E) (hf : LipschitzOnWith K f B)
    (hB : ∀ z ∈ S, ∀ s, U z s ∈ B)
    (t : ℝ) (x : E) (ht : t ≠ 0) (htS : (t,x) ∈ S) (h2tS : (2*t,x) ∈ S) :
    HasDerivAt (fun q => U (q,x) ⟨1,by simp⟩)
      (f (U (t,x) ⟨1,by simp⟩)) t := by
  let a : ℝ := 2*t
  have ha : a ≠ 0 := mul_ne_zero (by norm_num) ht
  have hratio : t/a = 1/2 := by dsimp [a]; field_simp
  have hmem : t/a ∈ Ioo (0:ℝ) 1 := by rw [hratio]; norm_num
  have hnear : ∀ᶠ q in 𝓝 t, (q,x) ∈ S ∧ q/a ∈ Ioo (0:ℝ) 1 :=
    ((continuousAt_id.prodMk continuousAt_const).eventually (hS.mem_nhds htS)).and
      ((continuousAt_id.div_const a).eventually (isOpen_Ioo.mem_nhds hmem))
  let γ := rescaledIntegralCurve f a x (U (a,x))
  have heq : (fun q => U (q,x) ⟨1,by simp⟩) =ᶠ[𝓝 t] (fun q => γ (q/a)) := by
    filter_upwards [hnear] with q hq
    have hqa : a * (q/a) = q := by field_simp
    have hs := rescaled_ode_path_time_scaling f a x (U (a,x)) (U (q,x))
      ⟨q/a,Ioo_subset_Icc_self hq.2⟩ K B hf (hEq (a,x) h2tS)
      (by simpa only [hqa] using hEq (q,x) hq.1)
      (hB (a,x) h2tS) (hB (q,x) hq.1)
    exact hs.symm.trans (rescaledIntegralCurve_eq f a x (U (a,x))
      (hEq (a,x) h2tS) ⟨q/a,Ioo_subset_Icc_self hq.2⟩).symm
  have hd := (hasDerivAt_rescaledIntegralCurve f a x (U (a,x))
    (hEq (a,x) h2tS) (t/a) (Ioo_subset_Icc_self hmem)).scomp t
      ((hasDerivAt_id t).div_const a)
  have hd' : HasDerivAt (fun q => γ (q/a)) (f (γ (t/a))) t := by
    simpa only [one_div,smul_smul,inv_mul_cancel₀ ha,one_smul,Function.comp_def,id_eq,γ] using hd
  have hpoint : U (t,x) ⟨1,by simp⟩ = γ (t/a) := heq.self_of_nhds
  rw [←hpoint] at hd'
  exact hd'.congr_of_eventuallyEq heq

end

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_FlowImplicit
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.WeakMTWTransport.rescaledIntegralCurve_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite C⁴ implicit-function step for the actual four-dimensional
autonomous lift of the three-dimensional time-dependent flow. -/

noncomputable section
open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
namespace ContinuumCoulomb

theorem flow_c4_implicit_neighborhood
    (F : (ℝ × FlowPhase) × FlowPath → FlowPath) (hF : ContDiff ℝ 4 F)
    (a : ℝ × FlowPhase) (b : FlowPath)
    (hi : (fderiv ℝ F (a,b) ∘L inr ℝ (ℝ × FlowPhase) FlowPath).IsInvertible) :
    ∃ U : (ℝ × FlowPhase) → FlowPath, ∃ S : Set (ℝ × FlowPhase),
      IsOpen S ∧ a ∈ S ∧ ContDiffOn ℝ 4 U S ∧ U a = b ∧
        ∀ x ∈ S, F (x,U x) = F (a,b) := by
  let U := hF.contDiffAt.implicitFunction (by norm_num) hi
  have hU : ContDiffAt ℝ 4 U a := hF.contDiffAt.contDiffAt_implicitFunction (by norm_num) hi
  have hb : U a = b := hF.contDiffAt.implicitFunction_apply_self (by norm_num) hi
  have hc : ∀ᶠ x in 𝓝 a, ContDiffAt ℝ 1 U x :=
    (hU.of_le (by norm_num : (1:ℕ∞ω) ≤ 4)).eventually (by first | simp | exact_mod_cast le_top)
  have hid : Continuous (fun p => fderiv ℝ F p ∘L inr ℝ (ℝ × FlowPhase) FlowPath) :=
    (hF.continuous_fderiv (by norm_num)).clm_comp continuous_const
  have hin : ∀ᶠ p in 𝓝 (a,b),
      (fderiv ℝ F p ∘L inr ℝ (ℝ × FlowPhase) FlowPath).IsInvertible :=
    hid.continuousAt (WeakMTWTransport.isOpen_invertible_endomorphism.mem_nhds hi)
  have hgraph : ContinuousAt (fun x => (x,U x)) a := continuousAt_id.prodMk hU.continuousAt
  have hgi : ∀ᶠ x in 𝓝 a,
      (fderiv ℝ F (x,U x) ∘L inr ℝ (ℝ × FlowPhase) FlowPath).IsInvertible :=
    hgraph (by simpa only [hb] using! hin)
  have heq : ∀ᶠ x in 𝓝 a, F (x,U x) = F (a,b) :=
    hF.contDiffAt.eventually_apply_implicitFunction (by norm_num) hi
  obtain ⟨V,hVsub,hV,hbase⟩ := mem_nhds_iff.mp
    (hF.contDiffAt.eventually_apply_eq_iff_implicitFunction (by norm_num) hi)
  have hgin : ∀ᶠ x in 𝓝 a, (x,U x) ∈ V :=
    hgraph (by simpa only [hb] using! hV.mem_nhds hbase)
  obtain ⟨S,hSsub,hS,ha⟩ := mem_nhds_iff.mp (hc.and (hgi.and (heq.and hgin)))
  refine ⟨U,S,hS,ha,?_,hb,fun x hx => (hSsub hx).2.2.1⟩
  intro x hx
  have hh := hSsub hx
  let W := hF.contDiffAt.implicitFunction (by norm_num) hh.2.1
  have hW : ContDiffAt ℝ 4 W x := hF.contDiffAt.contDiffAt_implicitFunction (by norm_num) hh.2.1
  have hwx : W x = U x := hF.contDiffAt.implicitFunction_apply_self (by norm_num) hh.2.1
  have hWgraph : ContinuousAt (fun z => (z,W z)) x := continuousAt_id.prodMk hW.continuousAt
  have hWV : ∀ᶠ z in 𝓝 x, (z,W z) ∈ V :=
    hWgraph (by simpa only [hwx] using hV.mem_nhds hh.2.2.2)
  have hev : U =ᶠ[𝓝 x] W := by
    filter_upwards [hWV,hF.contDiffAt.eventually_apply_implicitFunction (by norm_num) hh.2.1]
      with z hz hz'
    exact (hVsub hz).mp (hz'.trans hh.2.2.1)
  exact (hW.congr_of_eventuallyEq hev).contDiffWithinAt

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_FlowPathFamily
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.WeakMTWTransport.rescaledIntegralCurve_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite C⁴ dependence of the local path-space fixed point. This is the
regularity construction needed before identifying it with the existing flow. -/

noncomputable section
open Set ContinuousLinearMap
open scoped ContDiff
namespace ContinuumCoulomb

theorem flow_c4_rescaled_equation
    (N : FlowPath → FlowPath) (hN : ContDiff ℝ 4 N)
    (c : FlowPhase →L[ℝ] FlowPath) (A : FlowPath →L[ℝ] FlowPath) (a : FlowPhase) :
    ∃ U : (ℝ × FlowPhase) → FlowPath, ∃ S : Set (ℝ × FlowPhase),
      IsOpen S ∧ (0,a) ∈ S ∧ ContDiffOn ℝ 4 U S ∧ U (0,a) = c a ∧
        ∀ z ∈ S, U z = c z.2 + z.1 • A (N (U z)) := by
  let F : (ℝ × FlowPhase) × FlowPath → FlowPath :=
    fun z => z.2-c z.1.2-z.1.1 • A (N z.2)
  let b : FlowPath := c a
  have hF : ContDiff ℝ 4 F :=
    (contDiff_snd.sub (c.contDiff.comp (contDiff_snd.comp contDiff_fst))).sub
      ((contDiff_fst.comp contDiff_fst).smul (A.contDiff.comp (hN.comp contDiff_snd)))
  have hpart : fderiv ℝ F ((0,a),b) ∘L inr ℝ (ℝ × FlowPhase) FlowPath =
      ContinuousLinearMap.id ℝ FlowPath := by
    have hpair : HasFDerivAt (fun p : FlowPath => ((0,a),p))
        (inr ℝ (ℝ × FlowPhase) FlowPath) b :=
      (hasFDerivAt_const ((0:ℝ),a) b).prodMk (hasFDerivAt_id b)
    have hc := (hF.differentiable (by norm_num) ((0,a),b)).hasFDerivAt.comp b hpair
    have hd : HasFDerivAt (fun p : FlowPath => F ((0,a),p))
        (ContinuousLinearMap.id ℝ FlowPath) b := by
      have hi : HasFDerivAt (fun p : FlowPath => p)
          (ContinuousLinearMap.id ℝ FlowPath) b := hasFDerivAt_id b
      change HasFDerivAt (fun p : FlowPath => p-c a-(0:ℝ) • A (N p))
        (ContinuousLinearMap.id ℝ FlowPath) b
      have heq : (fun p : FlowPath => p-c a-(0:ℝ) • A (N p)) =
          (fun p : FlowPath => p-c a) := by
        funext p
        exact (congrArg (fun q : FlowPath => p-c a-q)
          (_root_.zero_smul ℝ (A (N p)))).trans (sub_zero _)
      rw [heq]
      exact hi.sub_const (c a)
    exact hc.unique hd
  have hi : (fderiv ℝ F ((0,a),b) ∘L inr ℝ (ℝ × FlowPhase) FlowPath).IsInvertible := by
    rw [hpart]
    exact ⟨ContinuousLinearEquiv.refl ℝ FlowPath,rfl⟩
  obtain ⟨U,S,hS,ha,hU,hb,hEq⟩ := flow_c4_implicit_neighborhood F hF (0,a) b hi
  refine ⟨U,S,hS,ha,hU,hb,fun z hz => ?_⟩
  have hz' : U z-c z.2-z.1 • A (N (U z)) = 0 := by
    have h := hEq z hz
    change U z-c z.2-z.1 • A (N (U z)) = b-c a-(0:ℝ) • A (N b) at h
    calc
      _ = b-c a-(0:ℝ) • A (N b) := h
      _ = b-c a := (congrArg (fun q : FlowPath => b-c a-q)
        (_root_.zero_smul ℝ (A (N b)))).trans (sub_zero _)
      _ = 0 := sub_self _
  simpa only [add_comm] using eq_add_of_sub_eq (sub_eq_zero.mp hz')

theorem flow_c4_rescaled_family (f : FlowPhase → FlowPhase)
    (hf : ContDiff ℝ 4 f) (a : FlowPhase) :
    ∃ U : (ℝ × FlowPhase) → FlowPath, ∃ S : Set (ℝ × FlowPhase),
      IsOpen S ∧ (0,a) ∈ S ∧ ContDiffOn ℝ 4 U S ∧
      U (0,a) = ContinuousMap.const WeakMTWTransport.UnitTime a ∧
      ∀ z ∈ S, U z = ContinuousMap.const WeakMTWTransport.UnitTime z.2+
        z.1 • WeakMTWTransport.unitPathIntegral
          ((⟨f,hf.continuous⟩ : C(FlowPhase,FlowPhase)).comp (U z)) := by
  let fC : C(FlowPhase,FlowPhase) := ⟨f,hf.continuous⟩
  exact flow_c4_rescaled_equation (fun p => fC.comp p)
    (WeakMTWTransport.contDiff_path_comp_nat 4 fC hf)
    (ContinuousLinearMap.const ℝ WeakMTWTransport.UnitTime) WeakMTWTransport.unitPathIntegral a

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_FlowLocal
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A genuine C⁴ local flow for the four-dimensional autonomous lift. The
path family is identified with its ODE by the proved rescaling uniqueness. -/

noncomputable section
open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
namespace ContinuumCoulomb
open WeakMTWTransport

private theorem flow_endpoint_deriv_zero (f : C(FlowPhase,FlowPhase))
    (hf : ContDiff ℝ 4 f) (U : (ℝ × FlowPhase) → FlowPath) (x : FlowPhase)
    (hU : ContDiffAt ℝ 4 U (0,x))
    (hEq : ∀ᶠ z in 𝓝 ((0:ℝ),x), U z = ContinuousMap.const UnitTime z.2+
      z.1 • unitPathIntegral (f.comp (U z))) :
    HasDerivAt (fun t => U (t,x) ⟨1,by simp⟩) (f x) 0 := by
  let e : UnitTime := ⟨1,by simp⟩
  let W : ℝ → FlowPhase := fun t => unitPathIntegral (f.comp (U (t,x))) e
  have hW : ContDiffAt ℝ 4 W 0 :=
    (ContinuousMap.evalCLM ℝ e).contDiff.contDiffAt.comp 0
      (unitPathIntegral.contDiff.contDiffAt.comp 0
        ((contDiff_path_comp_nat 4 f hf).contDiffAt.comp 0
          (hU.comp 0 (contDiffAt_id.prodMk contDiffAt_const))))
  have hUx : U (0,x) = ContinuousMap.const UnitTime x := ode_family_initial hEq.self_of_nhds
  have hW0 : W 0 = f x := by
    simp [W,unitPathIntegral_apply,hUx,extendUnitPath,ContinuousMap.comp_apply,e]
  have heq : (fun t : ℝ => U (t,x) e) =ᶠ[𝓝 0] (fun t => x+t • W t) := by
    filter_upwards [(continuousAt_id.prodMk continuousAt_const).eventually hEq] with t ht
    exact congrArg (fun u : FlowPath => u e) ht
  have hd := ((hasDerivAt_id (0:ℝ)).smul
    (hW.differentiableAt (by norm_num)).hasDerivAt).const_add x
  change HasDerivAt (fun t => x+t • W t) ((0:ℝ) • deriv W 0+(1:ℝ) • W 0) 0 at hd
  have hd' : HasDerivAt (fun t => x+t • W t) (f x) 0 := by
    simpa only [id_eq,Pi.smul_apply,one_smul,zero_smul,add_zero,zero_add,hW0] using hd
  exact hd'.congr_of_eventuallyEq heq

theorem flow_c4_local (f : FlowPhase → FlowPhase) (hf : ContDiff ℝ 4 f) (a : FlowPhase) :
    ∃ r : ℝ, 0 < r ∧ ∃ Φ : (ℝ × FlowPhase) → FlowPhase,
      ContDiffOn ℝ 4 Φ (Ioo (-r) r ×ˢ Metric.ball a r) ∧
      (∀ x ∈ Metric.ball a r, Φ (0,x) = x) ∧
      ∀ t ∈ Ioo (-r) r, ∀ x ∈ Metric.ball a r,
        HasDerivAt (fun s => Φ (s,x)) (f (Φ (t,x))) t := by
  obtain ⟨U,S,hS,ha,hU,hUa,hEq⟩ := flow_c4_rescaled_family f hf a
  let fC : C(FlowPhase,FlowPhase) := ⟨f,hf.continuous⟩
  obtain ⟨K,B,hBa,hLip⟩ := (hf.contDiffAt.of_le (by norm_num : (1:ℕ∞ω) ≤ 4)).exists_lipschitzOnWith
  obtain ⟨b,hb,hbB⟩ := Metric.mem_nhds_iff.mp hBa
  have hcont : ContinuousAt U (0,a) := (hU.contDiffAt (hS.mem_nhds ha)).continuousAt
  have hn : ∀ᶠ z in 𝓝 ((0:ℝ),a), z ∈ S ∧ dist (U z) (ContinuousMap.const UnitTime a) < b := by
    have h := hcont.eventually (Metric.ball_mem_nhds (U (0,a)) hb)
    rw [hUa] at h
    exact (show ∀ᶠ z in 𝓝 ((0:ℝ),a), z ∈ S from hS.mem_nhds ha).and h
  obtain ⟨ε,hε,hεsub⟩ := Metric.mem_nhds_iff.mp hn
  let R := Metric.ball ((0:ℝ),a) ε
  have hRS : R ⊆ S := fun z hz => (hεsub hz).1
  have hRB : ∀ z ∈ R, ∀ s, U z s ∈ B := by
    intro z hz s
    apply hbB
    exact lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist (f := U z)
      (g := ContinuousMap.const UnitTime a) s) (hεsub hz).2
  let r := ε/3
  have hr : 0 < r := div_pos hε (by norm_num)
  have htr : ∀ t ∈ Ioo (-r) r, ∀ x ∈ Metric.ball a r, (t,x) ∈ R ∧ (2*t,x) ∈ R := by
    intro t ht x hx
    have habs : |t| < r := abs_lt.mpr ht
    have hx' : dist x a < r := hx
    have hre : r < ε := by dsimp [r]; linarith
    have ht2 : |2*t| < ε := by
      rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
      dsimp [r] at habs
      linarith
    constructor
    · change dist (t,x) (0,a) < ε
      rw [Prod.dist_eq,max_lt_iff,Real.dist_eq,sub_zero]
      exact ⟨habs.trans hre,hx'.trans hre⟩
    · change dist (2*t,x) (0,a) < ε
      rw [Prod.dist_eq,max_lt_iff,Real.dist_eq,sub_zero]
      exact ⟨ht2,hx'.trans hre⟩
  let Φ : (ℝ × FlowPhase) → FlowPhase := fun z => U z ⟨1,by simp⟩
  refine ⟨r,hr,Φ,?_,?_,?_⟩
  · have hUSub : ContDiffOn ℝ 4 U (Ioo (-r) r ×ˢ Metric.ball a r) :=
      hU.mono (fun z hz => hRS (htr z.1 hz.1 z.2 hz.2).1)
    exact (ContinuousMap.evalCLM ℝ (⟨1,by simp⟩ : UnitTime)).contDiff.comp_contDiffOn hUSub
  · intro x hx
    have h0 : (0:ℝ) ∈ Ioo (-r) r := ⟨neg_neg_of_pos hr,hr⟩
    have hi := ode_family_initial (hEq (0,x) (hRS (htr 0 h0 x hx).1))
    exact congrArg (fun u : FlowPath => u ⟨1,by simp⟩) hi
  · intro t ht x hx
    by_cases ht0 : t = 0
    · subst t
      have hi : Φ (0,x) = x := congrArg (fun u : FlowPath => u ⟨1,by simp⟩)
        (ode_family_initial (hEq (0,x) (hRS (htr 0 ht x hx).1)))
      rw [hi]
      exact flow_endpoint_deriv_zero fC hf U x
        (hU.contDiffAt (hS.mem_nhds (hRS (htr 0 ht x hx).1)))
        (Filter.eventually_of_mem (hS.mem_nhds (hRS (htr 0 ht x hx).1)) hEq)
    · exact ode_family_endpoint_deriv_ne_zero fC U R Metric.isOpen_ball
        (fun z hz => hEq z (hRS hz)) K B hLip hRB t x ht0
        (htr t ht x hx).1 (htr t ht x hx).2

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_FlowGlobalRegularity
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! C⁴ spatial dependence of complete Lipschitz flows in the four-dimensional
autonomous phase space. Local regularity propagates by uniqueness. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal
namespace ContinuumCoulomb

theorem flow_global_add {f : FlowPhase → FlowPhase} {K : ℝ≥0}
    (hLip : LipschitzWith K f) (G : FlowPhase → ℝ → FlowPhase)
    (h0 : ∀ x, G x 0 = x) (hG : ∀ x t, HasDerivAt (G x) (f (G x t)) t)
    (x : FlowPhase) (s t : ℝ) : G x (s+t) = G (G x s) t := by
  have heq : (fun u => G x (s+u)) = G (G x s) := by
    apply ODE_solution_unique_univ (s := fun _ => univ) (t₀ := 0)
      (fun _ => hLip.lipschitzOnWith)
    · intro u
      refine ⟨?_,mem_univ _⟩
      have hi : HasDerivAt (fun q : ℝ => s+q) 1 u := (hasDerivAt_id u).const_add s
      have hc := (hG x (s+u)).scomp u hi
      rw [one_smul] at hc
      apply hc.congr_of_eventuallyEq
      exact Filter.Eventually.of_forall (fun _ => rfl)
    · intro u
      exact ⟨hG (G x s) u,mem_univ _⟩
    · simp only [add_zero,h0]
  exact congrFun heq t

theorem flow_global_local {f : FlowPhase → FlowPhase} (hf : ContDiff ℝ 4 f)
    {K : ℝ≥0} (hLip : LipschitzWith K f) (G : FlowPhase → ℝ → FlowPhase)
    (h0 : ∀ x, G x 0 = x) (hG : ∀ x t, HasDerivAt (G x) (f (G x t)) t)
    (a : FlowPhase) :
    ∃ r : ℝ, 0 < r ∧
      ContDiffOn ℝ 4 (fun z : ℝ × FlowPhase => G z.2 z.1)
        (Ioo (-r) r ×ˢ Metric.ball a r) := by
  obtain ⟨r,hr,Φ,hΦ,hΦ0,hΦder⟩ := flow_c4_local f hf a
  refine ⟨r,hr,hΦ.congr ?_⟩
  intro z hz
  have heq : EqOn (G z.2) (fun t => Φ (t,z.2)) (Ioo (-r) r) := by
    apply ODE_solution_unique_of_mem_Ioo (s := fun _ => univ)
      (fun _ _ => hLip.lipschitzOnWith) (t₀ := 0)
      (show (0:ℝ) ∈ Ioo (-r) r from ⟨neg_neg_of_pos hr,hr⟩)
    · exact fun t _ => ⟨hG z.2 t,mem_univ _⟩
    · exact fun t ht => ⟨hΦder t ht z.2 hz.2,mem_univ _⟩
    · rw [h0,hΦ0 z.2 hz.2]
  exact heq hz.1

theorem flow_global_spatial_C4 {f : FlowPhase → FlowPhase} (hf : ContDiff ℝ 4 f)
    {K : ℝ≥0} (hLip : LipschitzWith K f) (G : FlowPhase → ℝ → FlowPhase)
    (h0 : ∀ x, G x 0 = x) (hG : ∀ x t, HasDerivAt (G x) (f (G x t)) t)
    (t : ℝ) : ContDiff ℝ 4 (fun x => G x t) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro x
  let P : ℝ → Prop := fun s => ContDiffAt ℝ 4 (fun y => G y s) x
  have hloc : IsLocallyConstant P := by
    apply (IsLocallyConstant.iff_eventually_eq P).mpr
    intro s
    obtain ⟨r,hr,hlocal⟩ := flow_global_local hf hLip G h0 hG (G x s)
    have hnear : ∀ᶠ u in 𝓝 s, |u-s| < r ∧ G x u ∈ Metric.ball (G x s) r := by
      exact ((continuousAt_id.sub continuousAt_const).abs.eventually
        (Iio_mem_nhds (by simpa using hr))).and
        ((hG x s).continuousAt.eventually (Metric.ball_mem_nhds (G x s) hr))
    filter_upwards [hnear] with u hu
    apply propext
    have htime : u-s ∈ Ioo (-r) r := abs_lt.mp hu.1
    have hback : s-u ∈ Ioo (-r) r := by
      constructor <;> linarith [htime.1,htime.2]
    have hreg (v : ℝ) (hv : v ∈ Ioo (-r) r)
        (y : FlowPhase) (hy : y ∈ Metric.ball (G x s) r) :
        ContDiffAt ℝ 4 (fun z => G z v) y := by
      exact (hlocal.contDiffAt
        ((isOpen_Ioo.prod Metric.isOpen_ball).mem_nhds ⟨hv,hy⟩)).comp y
          (contDiffAt_const.prodMk contDiffAt_id)
    constructor
    · intro huP
      have hcomp := (hreg (s-u) hback (G x u) hu.2).comp x huP
      have heq : (fun y => G (G y u) (s-u)) = fun y => G y s := by
        funext y
        rw [←flow_global_add hLip G h0 hG]
        congr 1
        ring
      change ContDiffAt ℝ 4 (fun y => G y s) x
      rw [←heq]
      exact hcomp
    · intro hsP
      have hcomp := (hreg (u-s) htime (G x s) (Metric.mem_ball_self hr)).comp x hsP
      have heq : (fun y => G (G y s) (u-s)) = fun y => G y u := by
        funext y
        rw [←flow_global_add hLip G h0 hG]
        congr 1
        ring
      change ContDiffAt ℝ 4 (fun y => G y u) x
      rw [←heq]
      exact hcomp
  have hP0 : P 0 := by
    change ContDiffAt ℝ 4 (fun y => G y 0) x
    apply (contDiffAt_id : ContDiffAt ℝ 4 (id : FlowPhase → FlowPhase) x).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall h0
  change P t
  rw [hloc.apply_eq_of_preconnectedSpace t 0]
  exact hP0

theorem flow_global_joint_C4 {f : FlowPhase → FlowPhase} (hf : ContDiff ℝ 4 f)
    {K : ℝ≥0} (hLip : LipschitzWith K f) (G : FlowPhase → ℝ → FlowPhase)
    (h0 : ∀ x, G x 0 = x) (hG : ∀ x t, HasDerivAt (G x) (f (G x t)) t) :
    ContDiff ℝ 4 (fun z : ℝ × FlowPhase => G z.2 z.1) := by
  rw [contDiff_iff_contDiffAt]
  rintro ⟨s,x⟩
  obtain ⟨r,hr,hlocal⟩ := flow_global_local hf hLip G h0 hG (G x s)
  have hat : ContDiffAt ℝ 4 (fun z : ℝ × FlowPhase => G z.2 z.1) (0,G x s) :=
    hlocal.contDiffAt ((isOpen_Ioo.prod Metric.isOpen_ball).mem_nhds
      ⟨⟨neg_neg_of_pos hr,hr⟩,Metric.mem_ball_self hr⟩)
  have hmap : ContDiffAt ℝ 4
      (fun z : ℝ × FlowPhase => (z.1-s,G z.2 s)) (s,x) :=
    (contDiffAt_fst.sub contDiffAt_const).prodMk
      ((flow_global_spatial_C4 hf hLip G h0 hG s).contDiffAt.comp (s,x) contDiffAt_snd)
  have hat' : ContDiffAt ℝ 4 (fun z : ℝ × FlowPhase => G z.2 z.1) (s-s,G x s) := by
    rw [sub_self]
    exact hat
  have hc := hat'.comp (s,x) hmap
  have heq : (fun z : ℝ × FlowPhase => G (G z.2 s) (z.1-s)) =
      fun z => G z.2 z.1 := by
    funext z
    rw [←flow_global_add hLip G h0 hG]
    congr 1
    ring
  exact heq ▸ hc

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_FlowGlobalExistence
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete flows of bounded Lipschitz fields, obtained from the existing
Picard theorem on finite intervals and uniqueness on overlaps. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal
namespace ContinuumCoulomb

private theorem flow_interval_coherence {f : FlowPhase → FlowPhase} {K : ℝ≥0}
    (hLip : LipschitzWith K f) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (α β : ℝ → FlowPhase)
    (hα : ∀ t ∈ Icc (-a) a, HasDerivWithinAt α (f (α t)) (Icc (-a) a) t)
    (hβ : ∀ t ∈ Icc (-b) b, HasDerivWithinAt β (f (β t)) (Icc (-b) b) t)
    (h0 : α 0 = β 0) {t : ℝ} (ht : |t| < min a b) : α t = β t := by
  have hm : 0 < min a b := lt_min ha hb
  have heq : EqOn α β (Ioo (-(min a b)) (min a b)) := by
    apply ODE_solution_unique_of_mem_Ioo (s := fun _ => univ)
      (fun _ _ => hLip.lipschitzOnWith)
      (show (0:ℝ) ∈ Ioo (-(min a b)) (min a b) from ⟨neg_neg_of_pos hm,hm⟩)
    · intro u hu
      have hu' : u ∈ Ioo (-a) a :=
        ⟨lt_of_le_of_lt (neg_le_neg (min_le_left a b)) hu.1,
          hu.2.trans_le (min_le_left a b)⟩
      exact ⟨(hα u (Ioo_subset_Icc_self hu')).hasDerivAt
        (Icc_mem_nhds hu'.1 hu'.2),mem_univ _⟩
    · intro u hu
      have hu' : u ∈ Ioo (-b) b :=
        ⟨lt_of_le_of_lt (neg_le_neg (min_le_right a b)) hu.1,
          hu.2.trans_le (min_le_right a b)⟩
      exact ⟨(hβ u (Ioo_subset_Icc_self hu')).hasDerivAt
        (Icc_mem_nhds hu'.1 hu'.2),mem_univ _⟩
    · exact h0
  exact heq (abs_lt.mp ht)

theorem flow_bounded_global_exists {f : FlowPhase → FlowPhase} {K B : ℝ≥0}
    (hLip : LipschitzWith K f) (hB : ∀ x, ‖f x‖ ≤ B) :
    ∃ G : FlowPhase → ℝ → FlowPhase,
      (∀ x, G x 0 = x) ∧ ∀ x t, HasDerivAt (G x) (f (G x t)) t := by
  let Radius := {r : ℝ // 0 < r}
  have hex (x : FlowPhase) (r : Radius) :
      ∃ α : ℝ → FlowPhase, α 0 = x ∧
        ∀ t ∈ Icc (-r.val) r.val,
          HasDerivWithinAt α (f (α t)) (Icc (-r.val) r.val) t := by
    let t₀ : Icc (-r.val) r.val := ⟨0,by constructor <;> linarith [r.property]⟩
    have hp : IsPicardLindelof (fun _ : ℝ => f) t₀ x
        (⟨B*r.val,mul_nonneg B.coe_nonneg r.property.le⟩ : ℝ≥0) 0 B K := {
      lipschitzOnWith := fun _ _ => hLip.lipschitzOnWith
      continuousOn := fun _ _ => continuousOn_const
      norm_le := fun _ _ y _ => hB y
      mul_max_le := by
        change (B:ℝ) * max (r.val-0) (0-(-r.val)) ≤ (B:ℝ)*r.val-0
        simp only [sub_zero,zero_sub,neg_neg,max_self,le_refl] }
    exact hp.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  choose α hα0 hα using hex
  let radius : ℝ → Radius := fun t => ⟨|t|+1,by positivity⟩
  let G : FlowPhase → ℝ → FlowPhase := fun x t => α x (radius t) t
  refine ⟨G,fun x => hα0 x (radius 0),?_⟩
  intro x t
  let r := radius t
  have ht : |t| < r.val := by dsimp [r,radius]; linarith
  have heq : G x =ᶠ[𝓝 t] α x r := by
    filter_upwards [continuous_abs.continuousAt.eventually (Iio_mem_nhds ht)] with u hu
    exact flow_interval_coherence hLip (radius u).property r.property
      (α x (radius u)) (α x r) (hα x (radius u)) (hα x r)
      ((hα0 x (radius u)).trans (hα0 x r).symm)
      (lt_min (by dsimp [radius]; linarith) hu)
  have ht' := abs_lt.mp ht
  have hd := (hα x r t (Ioo_subset_Icc_self ht')).hasDerivAt
    (Icc_mem_nhds ht'.1 ht'.2)
  rw [←heq.self_of_nhds] at hd
  exact hd.congr_of_eventuallyEq heq

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_FlowCompactExtension
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact extensions of the autonomous field along a compact trajectory.
The extension has a complete C⁴ flow by bounded Picard existence. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal
namespace ContinuumCoulomb

theorem flow_c4_compact_extension {f : FlowPhase → FlowPhase} {S K : Set FlowPhase}
    (hS : IsOpen S) (hf : ContDiffOn ℝ 4 f S) (hK : IsCompact K) (hKS : K ⊆ S) :
    ∃ (g : FlowPhase → FlowPhase) (O : Set FlowPhase),
      ContDiff ℝ 4 g ∧ HasCompactSupport g ∧ IsOpen O ∧ K ⊆ O ∧ O ⊆ S ∧ EqOn g f O := by
  obtain ⟨R,_hR,hKR⟩ := hK.isBounded.subset_ball_lt 0 (0 : FlowPhase)
  obtain ⟨V,hV,hKV,hVS⟩ := hK.exists_isOpen_closure_subset
    ((hS.inter Metric.isOpen_ball).mem_nhdsSet.mpr (subset_inter hKS hKR))
  obtain ⟨O,hO,hKO,hOV⟩ := hK.exists_isOpen_closure_subset (hV.mem_nhdsSet.mpr hKV)
  obtain ⟨b,hb',_hb01,hbs,hb1⟩ := exists_contMDiff_support_eq_eq_one_iff
    (I := modelWithCornersSelf ℝ FlowPhase) (n := (4:ℕ∞)) hV isClosed_closure hOV
  have hb : ContDiff ℝ 4 b := contMDiff_iff_contDiff.mp hb'
  have hbS : tsupport b ⊆ S := by
    rw [tsupport,hbs]
    exact hVS.trans inter_subset_left
  have hbc : HasCompactSupport b := by
    apply (isCompact_closedBall (0:FlowPhase) R).of_isClosed_subset isClosed_closure
    change closure (Function.support b) ⊆ Metric.closedBall (0:FlowPhase) R
    rw [hbs]
    exact hVS.trans (inter_subset_right.trans Metric.ball_subset_closedBall)
  let g : FlowPhase → FlowPhase := fun x => b x • f x
  refine ⟨g,O,?_,hbc.smul_right,hO,hKO,?_,?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport b
    · exact hb.contDiffAt.smul (hf.contDiffAt (hS.mem_nhds (hbS hx)))
    · have heq : g =ᶠ[𝓝 x] 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
        change b y • f y = 0
        simp only [hy,Pi.zero_apply,zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq heq
  · exact subset_closure.trans (hOV.trans (subset_closure.trans (hVS.trans inter_subset_left)))
  · intro x hx
    change b x • f x = f x
    rw [(hb1 x).mp (subset_closure hx),one_smul]

theorem flow_compact_global_exists {f : FlowPhase → FlowPhase}
    (hf : ContDiff ℝ 4 f) (hc : HasCompactSupport f) :
    ∃ G : FlowPhase → ℝ → FlowPhase,
      (∀ x, G x 0 = x) ∧ (∀ x t, HasDerivAt (G x) (f (G x t)) t) ∧
      ContDiff ℝ 4 (fun z : ℝ × FlowPhase => G z.2 z.1) := by
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hf (by norm_num)
  obtain ⟨B,hB⟩ := hc.exists_bound_of_continuous hf.continuous
  let B' : ℝ≥0 := ⟨max B 0,le_max_right _ _⟩
  obtain ⟨G,h0,hG⟩ := flow_bounded_global_exists hL
    (B := B') (fun x => (hB x).trans (le_max_left _ _))
  exact ⟨G,h0,hG,flow_global_joint_C4 hf hL G h0 hG⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_FlowIntervalUniqueness
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Closed-interval uniqueness for the lifted field. The local Lipschitz
estimate suffices; no global bound on the field is assumed. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal
namespace ContinuumCoulomb

private theorem flow_box_unique_right {f : FlowPhase → FlowPhase} {K : ℝ≥0}
    {B : Set FlowPhase} (hLip : LipschitzOnWith K f B)
    {a b : ℝ} {α β : ℝ → FlowPhase}
    (hα : ∀ t ∈ Icc a b, HasDerivWithinAt α (f (α t)) (Icc a b) t)
    (hβ : ∀ t ∈ Icc a b, HasDerivWithinAt β (f (β t)) (Icc a b) t)
    (hB : ∀ t ∈ Icc a b, α t ∈ B ∧ β t ∈ B) (h0 : α a = β a) :
    EqOn α β (Icc a b) := by
  have hr (γ : ℝ → FlowPhase)
      (hγ : ∀ t ∈ Icc a b, HasDerivWithinAt γ (f (γ t)) (Icc a b) t)
      (t : ℝ) (ht : t ∈ Ico a b) : HasDerivWithinAt γ (f (γ t)) (Ici t) t := by
    apply (hγ t ⟨ht.1,ht.2.le⟩).mono_of_mem_nhdsWithin
    exact Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1)
  exact ODE_solution_unique_of_mem_Icc_right (s := fun _ => B)
    (fun _ _ => hLip) (HasDerivWithinAt.continuousOn hα) (hr α hα)
    (fun t ht => (hB t ⟨ht.1,ht.2.le⟩).1)
    (HasDerivWithinAt.continuousOn hβ) (hr β hβ)
    (fun t ht => (hB t ⟨ht.1,ht.2.le⟩).2) h0

private theorem flow_box_unique_left {f : FlowPhase → FlowPhase} {K : ℝ≥0}
    {B : Set FlowPhase} (hLip : LipschitzOnWith K f B)
    {a b : ℝ} {α β : ℝ → FlowPhase}
    (hα : ∀ t ∈ Icc a b, HasDerivWithinAt α (f (α t)) (Icc a b) t)
    (hβ : ∀ t ∈ Icc a b, HasDerivWithinAt β (f (β t)) (Icc a b) t)
    (hB : ∀ t ∈ Icc a b, α t ∈ B ∧ β t ∈ B) (h0 : α b = β b) :
    EqOn α β (Icc a b) := by
  have hl (γ : ℝ → FlowPhase)
      (hγ : ∀ t ∈ Icc a b, HasDerivWithinAt γ (f (γ t)) (Icc a b) t)
      (t : ℝ) (ht : t ∈ Ioc a b) : HasDerivWithinAt γ (f (γ t)) (Iic t) t := by
    apply (hγ t ⟨ht.1.le,ht.2⟩).mono_of_mem_nhdsWithin
    exact Filter.mem_of_superset (Icc_mem_nhdsLE ht.1) (Icc_subset_Icc_right ht.2)
  exact ODE_solution_unique_of_mem_Icc_left (s := fun _ => B)
    (fun _ _ => hLip) (HasDerivWithinAt.continuousOn hα) (hl α hα)
    (fun t ht => (hB t ⟨ht.1.le,ht.2⟩).1)
    (HasDerivWithinAt.continuousOn hβ) (hl β hβ)
    (fun t ht => (hB t ⟨ht.1.le,ht.2⟩).2) h0

theorem flow_open_interval_unique {f : FlowPhase → FlowPhase} {S : Set FlowPhase}
    (hS : IsOpen S) (hf : ContDiffOn ℝ 4 f S)
    {a b : ℝ} {α β : ℝ → FlowPhase}
    (hα : ∀ t ∈ Icc a b, HasDerivWithinAt α (f (α t)) (Icc a b) t)
    (hβ : ∀ t ∈ Icc a b, HasDerivWithinAt β (f (β t)) (Icc a b) t)
    (hαS : MapsTo α (Icc a b) S)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b) (heq : α t₀ = β t₀) : EqOn α β (Icc a b) := by
  classical
  let P : Icc a b → Prop := fun t => α t = β t
  have hcα : Continuous (fun t : Icc a b => α t) :=
    continuousOn_iff_continuous_domRestrict.mp (HasDerivWithinAt.continuousOn hα)
  have hcβ : Continuous (fun t : Icc a b => β t) :=
    continuousOn_iff_continuous_domRestrict.mp (HasDerivWithinAt.continuousOn hβ)
  have hpclosed : IsClosed {t : Icc a b | P t} := isClosed_eq hcα hcβ
  have hloc : IsLocallyConstant P := by
    apply (IsLocallyConstant.iff_eventually_eq P).mpr
    intro t
    by_cases ht : P t
    · obtain ⟨L,B,hBt,hLip⟩ :=
        ((hf.contDiffAt (hS.mem_nhds (hαS t.property))).of_le
          (by norm_num : (1:ℕ∞ω) ≤ 4)).exists_lipschitzOnWith
      have hnear : ∀ᶠ u in 𝓝[Icc a b] (t:ℝ), α u ∈ B ∧ β u ∈ B :=
        ((hα t t.property).continuousWithinAt.eventually hBt).and
          ((hβ t t.property).continuousWithinAt.eventually (by
            have ht' : α t = β t := ht
            rw [←ht']
            exact hBt))
      obtain ⟨δ,hδ,hδB⟩ := Metric.mem_nhdsWithin_iff.mp hnear
      have hlocal : ∀ᶠ u in 𝓝[Icc a b] (t:ℝ), α u = β u := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (t:ℝ) hδ),
          self_mem_nhdsWithin] with u hu hui
        have hdist : dist u (t:ℝ) < δ := hu
        by_cases htu : (t:ℝ) ≤ u
        · have hsub : Icc (t:ℝ) u ⊆ Icc a b := Icc_subset_Icc t.property.1 hui.2
          have hB (v : ℝ) (hv : v ∈ Icc (t:ℝ) u) : α v ∈ B ∧ β v ∈ B := by
            apply hδB
            refine ⟨?_,hsub hv⟩
            rw [Metric.mem_ball,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hv.1)]
            rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr htu)] at hdist
            linarith [hv.2]
          exact flow_box_unique_right hLip
            (fun v hv => (hα v (hsub hv)).mono hsub)
            (fun v hv => (hβ v (hsub hv)).mono hsub) hB ht ⟨htu,le_rfl⟩
        · have hut : u ≤ (t:ℝ) := le_of_not_ge htu
          have hsub : Icc u (t:ℝ) ⊆ Icc a b := Icc_subset_Icc hui.1 t.property.2
          have hB (v : ℝ) (hv : v ∈ Icc u (t:ℝ)) : α v ∈ B ∧ β v ∈ B := by
            apply hδB
            refine ⟨?_,hsub hv⟩
            rw [Metric.mem_ball,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hv.2)]
            rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hut)] at hdist
            linarith [hv.1]
          exact flow_box_unique_left hLip
            (fun v hv => (hα v (hsub hv)).mono hsub)
            (fun v hv => (hβ v (hsub hv)).mono hsub) hB ht ⟨le_rfl,hut⟩
      rw [nhdsWithin_eq_map_subtype_coe t.property] at hlocal
      filter_upwards [hlocal] with u hu
      exact propext (iff_of_true hu ht)
    · filter_upwards [hpclosed.isOpen_compl.mem_nhds ht] with u hu
      exact propext (iff_of_false hu ht)
  have : PreconnectedSpace (Icc a b) := Subtype.preconnectedSpace isPreconnected_Icc
  intro t ht
  have hh := hloc.apply_eq_of_preconnectedSpace ⟨t,ht⟩ ⟨t₀,ht₀⟩
  change P ⟨t,ht⟩
  rw [hh]
  exact heq

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_FlowSpatialRegularity
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spatial C⁴ regularity on the entire closed transport interval, derived
from local C⁴ dependence and uniqueness along each compact trajectory. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace ContinuumCoulomb

theorem flow_lifted_local_model {f : FlowPhase → FlowPhase} {S : Set FlowPhase}
    (hS : IsOpen S) (hf : ContDiffOn ℝ 4 f S)
    (A : Position → ℝ → FlowPhase) (h0 : ∀ x, A x 0 = (0,x))
    (hA : ∀ x t, t ∈ Icc (0:ℝ) 1 →
      HasDerivWithinAt (A x) (f (A x t)) (Icc (0:ℝ) 1) t)
    (hAS : ∀ x, MapsTo (A x) (Icc (0:ℝ) 1) S) (x : Position) :
    ∃ H : ℝ × Position → FlowPhase, ContDiff ℝ 4 H ∧
      ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc (0:ℝ) 1, A y t = H (t,y) := by
  let K := A x '' Icc (0:ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn
    (HasDerivWithinAt.continuousOn (hA x))
  have hKS : K ⊆ S := by rintro _ ⟨s,hs,rfl⟩; exact hAS x hs
  obtain ⟨g,O,hg,hgc,hO,hKO,_hOS,hgf⟩ := flow_c4_compact_extension hS hf hK hKS
  obtain ⟨F,hF0,hF,hFC⟩ := flow_compact_global_exists hg hgc
  have hAxO (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : A x s ∈ O := hKO ⟨s,hs,rfl⟩
  have hbase : EqOn (A x) (F (0,x)) (Icc (0:ℝ) 1) := by
    apply flow_open_interval_unique isOpen_univ hg.contDiffOn
      (fun s hs => by simpa only [hgf (hAxO s hs)] using hA x s hs)
      (fun s _ => (hF (0,x) s).hasDerivWithinAt) (fun _ _ => mem_univ _)
      (show (0:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)
    rw [h0,hF0]
  have hnear : ∀ᶠ y in 𝓝 x, ∀ s ∈ Icc (0:ℝ) 1, F (0,y) s ∈ O := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro s hs
    have hc : Continuous (fun z : Position × ℝ => F (0,z.1) z.2) :=
      hFC.continuous.comp (continuous_snd.prodMk (continuous_const.prodMk continuous_fst))
    apply hc.continuousAt.eventually
    apply hO.mem_nhds
    change F (0,x) s ∈ O
    rw [←hbase hs]
    exact hAxO s hs
  refine ⟨fun z => F (0,z.2) z.1,
    hFC.comp (contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd)),?_⟩
  filter_upwards [hnear] with y hy
  apply flow_open_interval_unique hS hf (hA y)
    (fun s hs => by simpa only [hgf (hy s hs)] using
      (hF (0,y) s).hasDerivWithinAt (s := Icc (0:ℝ) 1))
    (hAS y) (show (0:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)
  rw [h0,hF0]

theorem flow_lifted_interval_C4 {f : FlowPhase → FlowPhase} {S : Set FlowPhase}
    (hS : IsOpen S) (hf : ContDiffOn ℝ 4 f S)
    (A : Position → ℝ → FlowPhase) (h0 : ∀ x, A x 0 = (0,x))
    (hA : ∀ x t, t ∈ Icc (0:ℝ) 1 →
      HasDerivWithinAt (A x) (f (A x t)) (Icc (0:ℝ) 1) t)
    (hAS : ∀ x, MapsTo (A x) (Icc (0:ℝ) 1) S)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : ContDiff ℝ 4 (fun x => A x t) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨H,hH,hEq⟩ := flow_lifted_local_model hS hf A h0 hA hAS x
  have hc : ContDiff ℝ 4 (fun y : Position => H (t,y)) :=
    hH.comp (contDiff_const.prodMk contDiff_id)
  exact hc.contDiffAt.congr_of_eventuallyEq (hEq.mono (fun _ hy => hy t ht))

theorem flow_spatial_C4 {U : Set (ℝ × Position)} (hU : IsOpen U)
    (hslab : Icc (0:ℝ) 1 ×ˢ (univ : Set Position) ⊆ U)
    (v : ℝ → Position → Position)
    (hv : ContDiffOn ℝ 4 (fun p : ℝ × Position => v p.1 p.2) U)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow v G)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : ContDiff ℝ 4 (fun x => G x t) := by
  let f : FlowPhase → FlowPhase := fun p => (1,v p.1 p.2)
  let A : Position → ℝ → FlowPhase := fun x s => (s,G x s)
  have hf : ContDiffOn ℝ 4 f U := contDiffOn_const.prodMk hv
  have hA : ∀ x s, s ∈ Icc (0:ℝ) 1 →
      HasDerivWithinAt (A x) (f (A x s)) (Icc (0:ℝ) 1) s := by
    intro x s hs
    exact (hasDerivWithinAt_id s (Icc (0:ℝ) 1)).prodMk (hG.2 x s hs)
  have hc := flow_lifted_interval_C4 hU hf A
    (fun x => by simp only [A,hG.1]) hA (fun x s hs => hslab ⟨hs,mem_univ _⟩) t ht
  exact contDiff_snd.comp hc

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_FlowLocalModel
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smooth local representative of the actual nonautonomous flow, with
agreement uniform over the entire closed time interval. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace ContinuumCoulomb

theorem flow_local_model {U : Set (ℝ × Position)} (hU : IsOpen U)
    (hslab : Icc (0:ℝ) 1 ×ˢ (univ : Set Position) ⊆ U)
    (v : ℝ → Position → Position)
    (hv : ContDiffOn ℝ 4 (fun p : ℝ × Position => v p.1 p.2) U)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow v G) (x : Position) :
    ∃ H : ℝ × Position → Position, ContDiff ℝ 4 H ∧
      ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc (0:ℝ) 1, G y t = H (t,y) := by
  let f : FlowPhase → FlowPhase := fun p => (1,v p.1 p.2)
  let A : Position → ℝ → FlowPhase := fun y s => (s,G y s)
  have hf : ContDiffOn ℝ 4 f U := contDiffOn_const.prodMk hv
  have hA : ∀ y s, s ∈ Icc (0:ℝ) 1 →
      HasDerivWithinAt (A y) (f (A y s)) (Icc (0:ℝ) 1) s := by
    intro y s hs
    exact (hasDerivWithinAt_id s (Icc (0:ℝ) 1)).prodMk (hG.2 y s hs)
  obtain ⟨H,hH,hEq⟩ := flow_lifted_local_model hU hf A
    (fun y => by simp only [A,hG.1]) hA (fun y s hs => hslab ⟨hs,mem_univ _⟩) x
  refine ⟨fun p => (H p).2,contDiff_snd.comp hH,?_⟩
  filter_upwards [hEq] with y hy
  intro t ht
  exact congrArg Prod.snd (hy t ht)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_FlowMixedDerivative
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Interchanging time and a spatial derivative of the local smooth flow
model. This is the first variational equation's calculus step. -/

noncomputable section
open ContinuousLinearMap
open scoped ContDiff
namespace ContinuumCoulomb

theorem flow_spatial_deriv_eq_full (H : ℝ × Position → Position)
    (hH : ContDiff ℝ 4 H) (t : ℝ) (x e : Position) :
    fderiv ℝ (fun y => H (t,y)) x e = fderiv ℝ H (t,x) (0,e) := by
  have hp : HasFDerivAt (fun y : Position => (t,y)) (inr ℝ ℝ Position) x :=
    (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  have hc := ((hH.differentiable (by norm_num)) (t,x)).hasFDerivAt.comp x hp
  change fderiv ℝ (H ∘ (fun y : Position => (t,y))) x e = _
  rw [hc.fderiv]
  rfl

theorem flow_mixed_spatial_derivative (H : ℝ × Position → Position)
    (hH : ContDiff ℝ 4 H) (t : ℝ) (x e : Position) :
    HasDerivAt (fun s => fderiv ℝ (fun y => H (s,y)) x e)
      (fderiv ℝ (fun y => fderiv ℝ H (t,y) (1,0)) x e) t := by
  let p : ℝ × Position := (t,x)
  let v : ℝ × Position := (1,0)
  let w : ℝ × Position := (0,e)
  have hD : ContDiff ℝ 1 (fderiv ℝ H) := hH.fderiv_right (by norm_num)
  have hd := ((hD.differentiable (by norm_num)) p).hasFDerivAt
  have hp : HasDerivAt (fun s : ℝ => (s,x)) v t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  have htime : HasDerivAt (fun s => fderiv ℝ H (s,x) w)
      (fderiv ℝ (fderiv ℝ H) p v w) t := by
    have h := (hd.clm_apply (hasFDerivAt_const w p)).comp_hasDerivAt t hp
    refine h.congr_deriv ?_
    · simp only [add_apply,ContinuousLinearMap.comp_apply,
        zero_apply,map_zero,zero_add,ContinuousLinearMap.flip_apply]
  have hspace : fderiv ℝ (fun y => fderiv ℝ H (t,y) v) x e =
      fderiv ℝ (fderiv ℝ H) p w v := by
    have hi : HasFDerivAt (fun y : Position => (t,y)) (inr ℝ ℝ Position) x :=
      (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
    have h := (hd.clm_apply (hasFDerivAt_const v p)).comp x hi
    change fderiv ℝ ((fun z => fderiv ℝ H z v) ∘
      (fun y : Position => (t,y))) x e = _
    rw [h.fderiv]
    simp only [ContinuousLinearMap.comp_apply,add_apply,
      zero_apply,map_zero,zero_add,ContinuousLinearMap.flip_apply]
    rfl
  have hsym : fderiv ℝ (fderiv ℝ H) p v w = fderiv ℝ (fderiv ℝ H) p w v :=
    hH.contDiffAt.isSymmSndFDerivAt (by norm_num) v w
  change HasDerivAt (fun s => fderiv ℝ (fun y => H (s,y)) x e)
    (fderiv ℝ (fun y => fderiv ℝ H (t,y) v) x e) t
  rw [hspace,←hsym]
  apply htime.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun s => flow_spatial_deriv_eq_full H hH s x e)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_FlowVariational
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first variational equation for a C⁴ local model of the transport
flow, including the endpoints of the closed time interval. -/

noncomputable section
open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
namespace ContinuumCoulomb

theorem flow_model_time_partial (H : ℝ × Position → Position)
    (hH : ContDiff ℝ 4 H) (v : ℝ → Position → Position)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (x : Position)
    (hODE : HasDerivWithinAt (fun s => H (s,x)) (v t (H (t,x))) (Icc (0:ℝ) 1) t) :
    fderiv ℝ H (t,x) (1,0) = v t (H (t,x)) := by
  have hp : HasDerivAt (fun s : ℝ => (s,x)) ((1:ℝ),(0:Position)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  have hd := ((hH.differentiable (by norm_num)) (t,x)).hasFDerivAt.comp_hasDerivAt t hp
  have hd' : HasDerivWithinAt (fun s => H (s,x)) (fderiv ℝ H (t,x) (1,0))
      (Icc (0:ℝ) 1) t := by
    apply hd.hasDerivWithinAt.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun _ => rfl)
    rfl
  have hu := (uniqueDiffOn_Icc (by norm_num : (0:ℝ)<1)).uniqueDiffWithinAt ht
  exact (hd'.derivWithin hu).symm.trans (hODE.derivWithin hu)

theorem flow_model_variational (H : ℝ × Position → Position)
    (hH : ContDiff ℝ 4 H) (v : ℝ → Position → Position) (O : Set Position)
    (hO : IsOpen O) (x : Position) (hx : x ∈ O)
    (hODE : ∀ y ∈ O, ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivWithinAt (fun s => H (s,y)) (v t (H (t,y))) (Icc (0:ℝ) 1) t)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1)
    (hv : DifferentiableAt ℝ (v t) (H (t,x))) (e : Position) :
    HasDerivWithinAt (fun s => fderiv ℝ (fun y => H (s,y)) x e)
      (fderiv ℝ (v t) (H (t,x)) (fderiv ℝ (fun y => H (t,y)) x e))
      (Icc (0:ℝ) 1) t := by
  have heq : (fun y => fderiv ℝ H (t,y) (1,0)) =ᶠ[𝓝 x]
      (fun y => v t (H (t,y))) := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact flow_model_time_partial H hH v t ht y (hODE y hy t ht)
  have hs : DifferentiableAt ℝ (fun y => H (t,y)) x :=
    (hH.comp (contDiff_const.prodMk contDiff_id)).differentiable (by norm_num) x
  have hc := hv.hasFDerivAt.comp x hs.hasFDerivAt
  have hdf : fderiv ℝ (fun y => fderiv ℝ H (t,y) (1,0)) x e =
      fderiv ℝ (v t) (H (t,x)) (fderiv ℝ (fun y => H (t,y)) x e) := by
    rw [heq.fderiv_eq]
    change fderiv ℝ (v t ∘ (fun y => H (t,y))) x e = _
    rw [hc.fderiv]
    rfl
  rw [←hdf]
  exact (flow_mixed_spatial_derivative H hH t x e).hasDerivWithinAt

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_FlowJacobianVariation
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual closed-interval flow satisfies its first variational equation.
The proof transfers the equation from a smooth local representative. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace ContinuumCoulomb

theorem flow_spatial_variational {U : Set (ℝ × Position)} (hU : IsOpen U)
    (hslab : Icc (0:ℝ) 1 ×ˢ (univ : Set Position) ⊆ U)
    (v : ℝ → Position → Position)
    (hv : ContDiffOn ℝ 4 (fun p : ℝ × Position => v p.1 p.2) U)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow v G)
    (x e : Position) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivWithinAt (fun s => fderiv ℝ (fun y => G y s) x e)
      (fderiv ℝ (v t) (G x t) (fderiv ℝ (fun y => G y t) x e))
      (Icc (0:ℝ) 1) t := by
  obtain ⟨H,hH,hEq⟩ := flow_local_model hU hslab v hv G hG x
  obtain ⟨O,hOsub,hO,hx⟩ := mem_nhds_iff.mp hEq
  have hODE (y : Position) (hy : y ∈ O) (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      HasDerivWithinAt (fun r => H (r,y)) (v s (H (s,y))) (Icc (0:ℝ) 1) s := by
    have hd := hG.2 y s hs
    rw [hOsub hy s hs] at hd
    exact hd.congr_of_mem (fun r hr => (hOsub hy r hr).symm) hs
  have hJ (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      fderiv ℝ (fun y => G y s) x = fderiv ℝ (fun y => H (s,y)) x := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hO.mem_nhds hx] with y hy
    exact hOsub hy s hs
  have hv' : DifferentiableAt ℝ (v t) (H (t,x)) := by
    have hh := (hv.contDiffAt (hU.mem_nhds (hslab ⟨ht,mem_univ (H (t,x))⟩))).comp
      (H (t,x)) (contDiffAt_const.prodMk contDiffAt_id)
    exact hh.differentiableAt (by norm_num)
  have hd := flow_model_variational H hH v O hO x hx hODE t ht hv' e
  rw [←hOsub hx t ht,←hJ t ht] at hd
  exact hd.congr_of_mem (fun s hs => congrArg (fun L => L e) (hJ s hs)) ht

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_FlowFirstBound
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gronwall's bound for the first spatial derivative of the actual flow. -/

noncomputable section
open Set
open scoped ContDiff
namespace ContinuumCoulomb

theorem flow_first_derivative_bound_along {U : Set (ℝ × Position)} (hU : IsOpen U)
    (hslab : Icc (0:ℝ) 1 ×ˢ (univ : Set Position) ⊆ U)
    (v : ℝ → Position → Position)
    (hv : ContDiffOn ℝ 4 (fun p : ℝ × Position => v p.1 p.2) U)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow v G)
    (B : ℝ) (hB : 0 ≤ B) (x : Position)
    (hbound : ∀ t ∈ Icc (0:ℝ) 1, ‖fderiv ℝ (v t) (G x t)‖ ≤ B)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    ‖fderiv ℝ (fun y => G y t) x‖ ≤ Real.exp B := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos B).le
  intro e
  let u : ℝ → Position := fun s => fderiv ℝ (fun y => G y s) x e
  let du : ℝ → Position := fun s => fderiv ℝ (v s) (G x s) (u s)
  have hd (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      HasDerivWithinAt u (du s) (Icc (0:ℝ) 1) s :=
    flow_spatial_variational hU hslab v hv G hG x e s hs
  have hright (s : ℝ) (hs : s ∈ Ico (0:ℝ) 1) :
      HasDerivWithinAt u (du s) (Ici s) s := by
    apply (hd s ⟨hs.1,hs.2.le⟩).mono_of_mem_nhdsWithin
    exact Filter.mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc_left hs.1)
  have hu0 : u 0 = e := by
    have hzero : (fun y => G y 0) = id := funext hG.1
    change fderiv ℝ (fun y => G y 0) x e = e
    rw [hzero,fderiv_id]
    rfl
  have hdu (s : ℝ) (hs : s ∈ Ico (0:ℝ) 1) : ‖du s‖ ≤ B * ‖u s‖ + 0 := by
    exact ((fderiv ℝ (v s) (G x s)).le_opNorm (u s)).trans
      (by simpa only [add_zero] using
        mul_le_mul_of_nonneg_right (hbound s ⟨hs.1,hs.2.le⟩) (norm_nonneg (u s)))
  have h := norm_le_gronwallBound_of_norm_deriv_right_le
    (HasDerivWithinAt.continuousOn hd) hright
    (show ‖u 0‖ ≤ ‖e‖ by rw [hu0]) hdu t ht
  simp only [gronwallBound_ε0,sub_zero] at h
  have he : Real.exp (B*t) ≤ Real.exp B :=
    Real.exp_le_exp.mpr (by nlinarith [ht.2])
  exact h.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left he (norm_nonneg e))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_FlowHigherComposition
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A composition estimate that retains the highest derivative linearly.
This is the quantitative form needed in the higher variational equations. -/

noncomputable section
open ContinuousLinearMap
open scoped ContDiff
namespace ContinuumCoulomb

theorem flow_composition_highest_bound (f g : Position → Position)
    (hf : ContDiff ℝ 4 f) (hg : ContDiff ℝ 4 g)
    (k : ℕ) (hk : k ≤ 3) (x : Position) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hgB : ∀ j, 1 ≤ j → j ≤ k+1 → ‖iteratedFDeriv ℝ j g (f x)‖ ≤ B)
    (hfD : ∀ j, 1 ≤ j → j ≤ k → ‖iteratedFDeriv ℝ j f x‖ ≤ D^j) :
    ‖iteratedFDeriv ℝ (k+1) (g ∘ f) x‖ ≤
      B * ‖iteratedFDeriv ℝ (k+1) f x‖ +
        (k:ℝ) * 2^k * (k.factorial:ℝ) * B * D^(k+1) := by
  have hgf : fderiv ℝ (g ∘ f) =
      (fun y => compL ℝ Position Position Position (fderiv ℝ g (f y)) (fderiv ℝ f y)) := by
    funext y
    exact fderiv_comp y (hg.differentiable (by norm_num) (f y))
      (hf.differentiable (by norm_num) y)
  have hg' : ContDiff ℝ 3 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
  have hf' : ContDiff ℝ 3 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hb := (compL ℝ Position Position Position).norm_iteratedFDeriv_le_of_bilinear_of_le_one
    (hg'.comp (hf.of_le (by norm_num))) hf' x
    (show (k:WithTop ℕ∞) ≤ 3 by exact_mod_cast hk)
    (norm_compL_le ℝ Position Position Position)
  rw [←norm_iteratedFDeriv_fderiv, hgf]
  apply hb.trans
  rw [Finset.sum_range_succ']
  have hzero : (k.choose 0:ℝ) * ‖iteratedFDeriv ℝ 0 (fderiv ℝ g ∘ f) x‖ *
      ‖iteratedFDeriv ℝ (k-0) (fderiv ℝ f) x‖ ≤
      B * ‖iteratedFDeriv ℝ (k+1) f x‖ := by
    simp only [Nat.choose_zero_right,Nat.cast_one,one_mul,norm_iteratedFDeriv_zero,
      Function.comp_apply,Nat.sub_zero,norm_iteratedFDeriv_fderiv]
    exact mul_le_mul_of_nonneg_right (by
      simpa only [norm_iteratedFDeriv_one] using hgB 1 le_rfl (by omega)) (norm_nonneg _)
  have hrest : ∑ i ∈ Finset.range k,
      (k.choose (i+1):ℝ) * ‖iteratedFDeriv ℝ (i+1) (fderiv ℝ g ∘ f) x‖ *
        ‖iteratedFDeriv ℝ (k-(i+1)) (fderiv ℝ f) x‖ ≤
      (k:ℝ) * (2^k * (k.factorial:ℝ) * B * D^(k+1)) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range k, 2^k * (k.factorial:ℝ) * B * D^(k+1) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i+1 ≤ k := Finset.mem_range.mp hi
        have hb' : ‖iteratedFDeriv ℝ (i+1) (fderiv ℝ g ∘ f) x‖ ≤
            ((i+1).factorial:ℝ) * B * D^(i+1) := by
          apply norm_iteratedFDeriv_comp_le hg' (hf.of_le (by norm_num))
            (show (i+1:ℕ) ≤ (3:WithTop ℕ∞) by exact_mod_cast hi'.trans hk) x
          · intro j hj
            rw [norm_iteratedFDeriv_fderiv]
            exact hgB (j+1) (by omega) (by omega)
          · intro j hj hj'
            exact hfD j hj (hj'.trans hi')
        have ha : ‖iteratedFDeriv ℝ (k-(i+1)) (fderiv ℝ f) x‖ ≤ D^(k-(i+1)+1) := by
          rw [norm_iteratedFDeriv_fderiv]
          exact hfD _ (by omega) (by omega)
        have hc : (k.choose (i+1):ℝ) ≤ 2^k := by exact_mod_cast Nat.choose_le_two_pow k (i+1)
        have hfac : ((i+1).factorial:ℝ) ≤ (k.factorial:ℝ) := by
          exact_mod_cast Nat.factorial_le hi'
        calc
          _ ≤ (2^k) * (((i+1).factorial:ℝ) * B * D^(i+1)) * D^(k-(i+1)+1) := by
            exact mul_le_mul (mul_le_mul hc hb' (norm_nonneg _) (by positivity)) ha
              (norm_nonneg _) (by positivity)
          _ ≤ (2^k) * ((k.factorial:ℝ) * B * D^(i+1)) * D^(k-(i+1)+1) := by gcongr
          _ = _ := by
            have he : i+1 + (k-(i+1)+1) = k+1 := by omega
            rw [mul_assoc (2^k),mul_assoc _ (D^(i+1)),←pow_add,he]
            ring
      _ = _ := by simp
  exact (add_le_add hrest hzero).trans_eq (by ring)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_FlowJetGronwall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A coarse positive-coefficient Gronwall bound for inhomogeneous jets. -/

noncomputable section
open Set
namespace ContinuumCoulomb

theorem flow_inhomogeneous_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u du : ℝ → E) (B A : ℝ) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hd : ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt u (du t) (Icc (0:ℝ) 1) t)
    (hzero : ‖u 0‖ = 0)
    (hbound : ∀ t ∈ Icc (0:ℝ) 1, ‖du t‖ ≤ B*‖u t‖+A)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    ‖u t‖ ≤ A * Real.exp (B+1) := by
  have hright (s : ℝ) (hs : s ∈ Ico (0:ℝ) 1) :
      HasDerivWithinAt u (du s) (Ici s) s := by
    apply (hd s ⟨hs.1,hs.2.le⟩).mono_of_mem_nhdsWithin
    exact Filter.mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc_left hs.1)
  have hb (s : ℝ) (hs : s ∈ Ico (0:ℝ) 1) :
      ‖du s‖ ≤ (B+1)*‖u s‖+A :=
    (hbound s ⟨hs.1,hs.2.le⟩).trans (by nlinarith [norm_nonneg (u s)])
  have h := norm_le_gronwallBound_of_norm_deriv_right_le
    (HasDerivWithinAt.continuousOn hd) hright (show ‖u 0‖ ≤ 0 by rw [hzero]) hb t ht
  have hpos : 0 < B+1 := by linarith
  simp only [gronwallBound,hpos.ne',↓reduceIte,zero_mul,zero_add,sub_zero] at h
  have ha : A/(B+1) ≤ A := (div_le_iff₀ hpos).mpr (by nlinarith)
  have hexp : 0 ≤ Real.exp ((B+1)*t)-1 :=
    sub_nonneg.mpr (Real.one_le_exp (mul_nonneg hpos.le ht.1))
  have he : Real.exp ((B+1)*t) ≤ Real.exp (B+1) :=
    Real.exp_le_exp.mpr (by nlinarith [ht.2])
  apply h.trans
  calc
    A/(B+1)*(Real.exp ((B+1)*t)-1) ≤ A*(Real.exp ((B+1)*t)-1) :=
      mul_le_mul_of_nonneg_right ha hexp
    _ ≤ A*Real.exp ((B+1)*t) := mul_le_mul_of_nonneg_left (by linarith) hA
    _ ≤ A*Real.exp (B+1) := mul_le_mul_of_nonneg_left he hA

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_FlowPathJets
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spatial derivatives as continuous paths. Taking derivatives in this
Banach space preserves the integral equation through order four without
requiring a fifth joint derivative of the vector field. -/

noncomputable section
open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
namespace ContinuumCoulomb
open WeakMTWTransport

theorem modelPath_C4 (H : ℝ × Position → Position) (hH : ContDiff ℝ 4 H) :
    ContDiff ℝ 4 (modelPath H hH.continuous) := by
  let T : C(UnitTime, ℝ × Position) :=
    ⟨fun s => (s,0), continuous_subtype_val.prodMk continuous_const⟩
  let L : Position →L[ℝ] C(UnitTime, ℝ × Position) :=
    (ContinuousLinearMap.const ℝ UnitTime).comp (inr ℝ ℝ Position)
  have hA : ContDiff ℝ 4 (fun y => T + L y) := contDiff_const.add L.contDiff
  have hc := (contDiff_path_comp_nat 4 (⟨H,hH.continuous⟩ : C(ℝ × Position,Position)) hH).comp hA
  have heq : ((fun v : C(UnitTime,ℝ × Position) =>
      (⟨H,hH.continuous⟩ : C(ℝ × Position,Position)).comp v) ∘ (fun y => T + L y)) =
      modelPath H hH.continuous := by
    funext y
    apply ContinuousMap.ext
    intro s
    change H ((s.val,(0:Position)) + ((0:ℝ),y)) = H (s,y)
    simp
  rwa [heq] at hc

theorem modelPath_iterated_apply (H : ℝ × Position → Position)
    (hH : ContDiff ℝ 4 H) (n : ℕ) (hn : n ≤ 4) (x : Position)
    (e : Fin n → Position) (t : UnitTime) :
    (iteratedFDeriv ℝ n (modelPath H hH.continuous) x e) t =
      iteratedFDeriv ℝ n (fun y => H (t,y)) x e := by
  have h := (ContinuousMap.evalCLM (R := ℝ) t).iteratedFDeriv_comp_left (x := x)
    (modelPath_C4 H hH).contDiffAt (show (n : WithTop ℕ∞) ≤ 4 by exact_mod_cast hn)
  have heq : (ContinuousMap.evalCLM (R := ℝ) t) ∘ modelPath H hH.continuous =
      (fun y => H (t,y)) := rfl
  rw [heq] at h
  exact (congrArg (fun M => M e) h).symm

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_FlowPathEquation
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The integral equation for the spatial jets of a local C⁴ flow model. -/

noncomputable section
open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
namespace ContinuumCoulomb
open WeakMTWTransport

theorem flow_model_path_equation (H K : ℝ × Position → Position)
    (hH : ContDiff ℝ 4 H) (hK : ContDiff ℝ 4 K)
    (O : Set Position)
    (hODE : ∀ y ∈ O, ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun s => H (s,y)) (K (t,y)) t)
    (y : Position) (hy : y ∈ O) :
    modelPath H hH.continuous y =
      ContinuousMap.const UnitTime (H (0,y)) +
        unitPathIntegral (modelPath K hK.continuous y) := by
  apply ContinuousMap.ext
  intro t
  change H (t,y) = H (0,y) + ∫ s in (0:ℝ)..t.val,
    extendUnitPath (modelPath K hK.continuous y) s
  have hd (s : ℝ) (hs : s ∈ uIcc (0:ℝ) t.val) :
      HasDerivAt (fun s => H (s,y))
        (extendUnitPath (modelPath K hK.continuous y) s) s := by
    rw [uIcc_of_le t.property.1] at hs
    have hs' : s ∈ Icc (0:ℝ) 1 := ⟨hs.1,hs.2.trans t.property.2⟩
    have he : extendUnitPath (modelPath K hK.continuous y) s = K (s,y) :=
      extendUnitPath_coe (modelPath K hK.continuous y) ⟨s,hs'⟩
    rw [he]
    exact hODE y hy s hs'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((extendUnitPath (modelPath K hK.continuous y)).continuous.intervalIntegrable _ _)]
  abel

theorem flow_model_jet_integral (H K : ℝ × Position → Position)
    (hH : ContDiff ℝ 4 H) (hK : ContDiff ℝ 4 K)
    (O : Set Position) (hO : IsOpen O) (x : Position) (hx : x ∈ O)
    (hODE : ∀ y ∈ O, ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun s => H (s,y)) (K (t,y)) t)
    (n : ℕ) (hn : n ≤ 4) (e : Fin n → Position) :
    iteratedFDeriv ℝ n (modelPath H hH.continuous) x e =
      ContinuousMap.const UnitTime (iteratedFDeriv ℝ n (fun y => H (0,y)) x e) +
        unitPathIntegral (iteratedFDeriv ℝ n (modelPath K hK.continuous) x e) := by
  let C : Position →L[ℝ] SpatialPath := ContinuousLinearMap.const ℝ UnitTime
  let A : SpatialPath →L[ℝ] SpatialPath := unitPathIntegral
  have hinit : ContDiff ℝ 4 (fun y => H (0,y)) :=
    hH.comp (contDiff_const.prodMk contDiff_id)
  have hP := modelPath_C4 K hK
  have heq : modelPath H hH.continuous =ᶠ[𝓝 x]
      (fun y => C (H (0,y)) + A (modelPath K hK.continuous y)) := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact flow_model_path_equation H K hH hK O hODE y hy
  have hd := (heq.iteratedFDeriv (𝕜 := ℝ) n).eq_of_nhds
  have hsum : (fun y => C (H (0,y)) + A (modelPath K hK.continuous y)) =
      (C ∘ (fun y => H (0,y))) + (A ∘ modelPath K hK.continuous) := rfl
  rw [hd, hsum, iteratedFDeriv_add_apply
    ((C.contDiff.comp hinit).contDiffAt.of_le (show (n:WithTop ℕ∞) ≤ 4 by exact_mod_cast hn))
    ((A.contDiff.comp hP).contDiffAt.of_le (show (n:WithTop ℕ∞) ≤ 4 by exact_mod_cast hn))]
  have hC := C.iteratedFDeriv_comp_left (x := x) hinit.contDiffAt
    (show (n:WithTop ℕ∞) ≤ 4 by exact_mod_cast hn)
  have hA := A.iteratedFDeriv_comp_left (x := x) hP.contDiffAt
    (show (n:WithTop ℕ∞) ≤ 4 by exact_mod_cast hn)
  change (iteratedFDeriv ℝ n (C ∘ (fun y => H (0,y))) x +
    iteratedFDeriv ℝ n (A ∘ modelPath K hK.continuous) x) e = _
  rw [hC,hA]
  rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_FlowJetCoordinates
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite coordinates for spatial jets in dimension three. -/

noncomputable section
open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
namespace ContinuumCoulomb

theorem spatialJetCoordinates_injective (n : ℕ) :
    Function.Injective (spatialJetCoordinates n) := by
  intro A B h
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear
    (fun _i : Fin n => (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis)
  intro e
  have he := congrFun h e
  change A (fun i => (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis (e i)) =
    B (fun i => (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis (e i))
  simpa only [spatialJetCoordinates,LinearMap.coe_mk,AddHom.coe_mk,
    OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply,NeutralAtom.axis] using he

instance spatialJetFiniteDimensional (n : ℕ) : FiniteDimensional ℝ (SpatialJet n) :=
  FiniteDimensional.of_injective (spatialJetCoordinates n) (spatialJetCoordinates_injective n)

theorem spatialJet_hasDerivWithinAt (n : ℕ) (J : ℝ → SpatialJet n)
    (D : SpatialJet n) (s : Set ℝ) (t : ℝ) (ht : t ∈ s)
    (h : ∀ e : Fin n → Position, HasDerivWithinAt (fun u => J u e) (D e) s t) :
    HasDerivWithinAt J D s t := by
  let L := (spatialJetCoordinates n).toContinuousLinearMap
  have hL : Topology.IsEmbedding L :=
    ((spatialJetCoordinates n).isClosedEmbedding_of_injective
      (LinearMap.ker_eq_bot.mpr (spatialJetCoordinates_injective n))).isEmbedding
  have hd : HasDerivWithinAt (fun u => L (J u)) (L D) s t :=
    hasDerivWithinAt_pi.mpr (fun e => h (fun i => NeutralAtom.axis (e i)))
  have hc : ContinuousWithinAt J s t :=
    hL.isInducing.continuousWithinAt_iff.mpr hd.continuousWithinAt
  have hd' : HasFDerivWithinAt (fun u => L (J u))
      (L.comp ((1:ℝ →L[ℝ] ℝ).smulRight D)) s t := by
    convert hd.hasFDerivWithinAt using 1
    all_goals try with_reducible_and_instances rfl
    ext r
    simp
  simpa using (HasFDerivWithinAt.of_comp_of_isEmbedding
    (t := univ) (by rw [nhdsWithin_univ]; exact hc.tendsto)
    L.hasFDerivAt.hasFDerivWithinAt hL hd' (Eventually.of_forall (fun _ => rfl)) ht).hasDerivWithinAt

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_FlowJetVariation
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The closed-interval variational equation through order four, obtained
by differentiating the path-space integral equation. -/

noncomputable section
open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
namespace ContinuumCoulomb
open WeakMTWTransport

theorem flow_model_jet_derivative (H K : ℝ × Position → Position)
    (hH : ContDiff ℝ 4 H) (hK : ContDiff ℝ 4 K)
    (O : Set Position) (hO : IsOpen O) (x : Position) (hx : x ∈ O)
    (hODE : ∀ y ∈ O, ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun s => H (s,y)) (K (t,y)) t)
    (n : ℕ) (hn : n ≤ 4) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivWithinAt (fun s => iteratedFDeriv ℝ n (fun y => H (s,y)) x)
      (iteratedFDeriv ℝ n (fun y => K (t,y)) x) (Icc (0:ℝ) 1) t := by
  apply spatialJet_hasDerivWithinAt n _ _ _ t ht
  intro e
  let q : SpatialPath := iteratedFDeriv ℝ n (modelPath K hK.continuous) x e
  let c : Position := iteratedFDeriv ℝ n (fun y => H (0,y)) x e
  have heq (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      iteratedFDeriv ℝ n (fun y => H (s,y)) x e =
        c + ∫ r in (0:ℝ)..s, extendUnitPath q r := by
    rw [←modelPath_iterated_apply H hH n hn x e ⟨s,hs⟩]
    have hi := congrArg (fun p : SpatialPath => p ⟨s,hs⟩)
      (flow_model_jet_integral H K hH hK O hO x hx hODE n hn e)
    exact hi
  have hd := (hasDerivAt_unitPathPrimitive q t).const_add c
  have hdval : extendUnitPath q t = iteratedFDeriv ℝ n (fun y => K (t,y)) x e := by
    rw [show extendUnitPath q t = q ⟨t,ht⟩ from extendUnitPath_coe q ⟨t,ht⟩]
    exact modelPath_iterated_apply K hK n hn x e ⟨t,ht⟩
  rw [hdval] at hd
  exact hd.hasDerivWithinAt.congr_of_mem heq ht

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_FlowLocalBound
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform higher-jet bounds for a local representative. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace ContinuumCoulomb

theorem flow_local_higher_bound (H W : ℝ × Position → Position)
    (hH : ContDiff ℝ 4 H) (hW : ContDiff ℝ 4 W)
    (O : Set Position) (hO : IsOpen O) (x : Position) (hx : x ∈ O)
    (hinit : ∀ y ∈ O, H (0,y) = y)
    (hODE : ∀ y ∈ O, ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun s => H (s,y)) (W (t,H (t,y))) t)
    (k : ℕ) (hk0 : 1 ≤ k) (hk : k ≤ 3)
    (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hb : ∀ t ∈ Icc (0:ℝ) 1, ∀ j, 1 ≤ j → j ≤ k+1 →
      ‖iteratedFDeriv ℝ j (fun z => W (t,z)) (H (t,x))‖ ≤ B)
    (hprev : ∀ t ∈ Icc (0:ℝ) 1, ∀ j, 1 ≤ j → j ≤ k →
      ‖iteratedFDeriv ℝ j (fun y => H (t,y)) x‖ ≤ D^j)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    ‖iteratedFDeriv ℝ (k+1) (fun y => H (t,y)) x‖ ≤
      ((k:ℝ)*2^k*(k.factorial:ℝ)*B*D^(k+1)) * Real.exp (B+1) := by
  let K : ℝ × Position → Position := fun p => W (p.1,H p)
  have hK : ContDiff ℝ 4 K := hW.comp (contDiff_fst.prodMk hH)
  let J : ℝ → SpatialJet (k+1) := fun s => iteratedFDeriv ℝ (k+1) (fun y => H (s,y)) x
  let dJ : ℝ → SpatialJet (k+1) := fun s => iteratedFDeriv ℝ (k+1) (fun y => K (s,y)) x
  have hd (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      HasDerivWithinAt J (dJ s) (Icc (0:ℝ) 1) s :=
    flow_model_jet_derivative H K hH hK O hO x hx hODE (k+1) (by omega) s hs
  have hz : ‖J 0‖ = 0 := by
    have heq : (fun y => H (0,y)) =ᶠ[𝓝 x] (id : Position → Position) := by
      filter_upwards [hO.mem_nhds hx] with y hy
      exact hinit y hy
    change ‖iteratedFDeriv ℝ (k+1) (fun y => H (0,y)) x‖ = 0
    rw [(heq.iteratedFDeriv ℝ (k+1)).eq_of_nhds,←norm_iteratedFDeriv_fderiv]
    have hid : fderiv ℝ (id : Position → Position) =
        fun _ => ContinuousLinearMap.id ℝ Position := funext (fun y => fderiv_id (x := y))
    rw [hid]
    obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [hm,iteratedFDeriv_succ_const]
    simp
  have hb' (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      ‖dJ s‖ ≤ B*‖J s‖ + (k:ℝ)*2^k*(k.factorial:ℝ)*B*D^(k+1) := by
    have hf : ContDiff ℝ 4 (fun y => H (s,y)) := hH.comp (contDiff_const.prodMk contDiff_id)
    have hg : ContDiff ℝ 4 (fun y => W (s,y)) := hW.comp (contDiff_const.prodMk contDiff_id)
    exact flow_composition_highest_bound (fun y => H (s,y)) (fun y => W (s,y))
      hf hg k hk x B D hB hD (hb s hs) (hprev s hs)
  exact flow_inhomogeneous_bound J dJ B _ hB (by positivity) hd hz hb' t ht

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_FlowLocalEquation
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal _root_.OAI.ContinuumCoulomb.spatialJetFiniteDimensional
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A global C⁴ representative near one compact family of trajectories.
Its derivatives on the base trajectory are those of the original field. -/

noncomputable section
open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
namespace ContinuumCoulomb

theorem flow_local_equation {U : Set (ℝ × Position)} (hU : IsOpen U)
    (hslab : Icc (0:ℝ) 1 ×ˢ (univ : Set Position) ⊆ U)
    (v : ℝ → Position → Position)
    (hv : ContDiffOn ℝ 4 (fun p : ℝ × Position => v p.1 p.2) U)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow v G) (x : Position) :
    ∃ (H W : ℝ × Position → Position) (O : Set Position),
      ContDiff ℝ 4 H ∧ ContDiff ℝ 4 W ∧ IsOpen O ∧ x ∈ O ∧
      (∀ y ∈ O, ∀ t ∈ Icc (0:ℝ) 1, G y t = H (t,y)) ∧
      (∀ y ∈ O, ∀ t ∈ Icc (0:ℝ) 1,
        HasDerivAt (fun s => H (s,y)) (W (t,H (t,y))) t) ∧
      (∀ t ∈ Icc (0:ℝ) 1,
        W =ᶠ[𝓝 (t,G x t)] (fun p : ℝ × Position => v p.1 p.2)) := by
  obtain ⟨H,hH,hEq⟩ := flow_local_model hU hslab v hv G hG x
  let A : ℝ → FlowPhase := fun t => (t,G x t)
  have hA : ContinuousOn A (Icc (0:ℝ) 1) :=
    continuousOn_id.prodMk (HasDerivWithinAt.continuousOn (hG.2 x))
  let K := A '' Icc (0:ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn hA
  have hKU : K ⊆ U := by rintro _ ⟨t,ht,rfl⟩; exact hslab ⟨ht,mem_univ _⟩
  obtain ⟨g,V,hg,_hgc,hV,hKV,_hVU,hgv⟩ := flow_c4_compact_extension
    (f := fun p => (1,v p.1 p.2)) hU (contDiffOn_const.prodMk hv) hK hKU
  let W : ℝ × Position → Position := fun p => (g p).2
  have hW : ContDiff ℝ 4 W := contDiff_snd.comp hg
  have hWv (p : ℝ × Position) (hp : p ∈ V) : W p = v p.1 p.2 :=
    congrArg Prod.snd (hgv hp)
  have hbase (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : H (t,x) = G x t :=
    (hEq.self_of_nhds t ht).symm
  have hnear : ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc (0:ℝ) 1, (t,H (t,y)) ∈ V := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro t ht
    have hc : Continuous (fun p : Position × ℝ => (p.2,H (p.2,p.1))) :=
      continuous_snd.prodMk (hH.continuous.comp (continuous_snd.prodMk continuous_fst))
    apply hc.continuousAt.eventually
    apply hV.mem_nhds
    change (t,H (t,x)) ∈ V
    rw [hbase t ht]
    exact hKV ⟨t,ht,rfl⟩
  obtain ⟨O,hOsub,hO,hxO⟩ := mem_nhds_iff.mp (hEq.and hnear)
  refine ⟨H,W,O,hH,hW,hO,hxO,fun y hy => (hOsub hy).1,?_,?_⟩
  · intro y hy t ht
    have hwithin := (hG.2 y t ht).congr_of_mem
      (fun s hs => ((hOsub hy).1 s hs).symm) ht
    rw [(hOsub hy).1 t ht,←hWv (t,H (t,y)) ((hOsub hy).2 t ht)] at hwithin
    have hp : HasDerivAt (fun s : ℝ => (s,y)) ((1:ℝ),(0:Position)) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
    have hd := ((hH.differentiable (by norm_num)) (t,y)).hasFDerivAt.comp_hasDerivAt t hp
    have he := flow_model_time_partial H hH (fun s z => W (s,z)) t ht y hwithin
    rw [he] at hd
    exact hd.congr_of_eventuallyEq (Eventually.of_forall (fun _ => rfl))
  · intro t ht
    filter_upwards [hV.mem_nhds (hKV ⟨t,ht,rfl⟩)] with p hp
    exact hWv p hp

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_FlowSliceBound
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal _root_.OAI.ContinuumCoulomb.spatialJetFiniteDimensional
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint derivative bounds restrict to spatial slices with no loss. -/

noncomputable section
open ContinuousLinearMap
open scoped ContDiff
namespace ContinuumCoulomb

theorem flow_slice_derivative_bound (F : ℝ × Position → Position)
    (hF : ContDiff ℝ 4 F) (n : ℕ) (hn : n ≤ 4) (t : ℝ) (x : Position) :
    ‖iteratedFDeriv ℝ n (fun y => F (t,y)) x‖ ≤
      ‖iteratedFDeriv ℝ n F (t,x)‖ := by
  let L : Position →L[ℝ] (ℝ × Position) := inr ℝ ℝ Position
  let A : ℝ × Position → Position := fun z => F ((t,0)+z)
  have hA : ContDiff ℝ 4 A := hF.comp (contDiff_const.add contDiff_id)
  have heq : (fun y => F (t,y)) = A ∘ L := by funext y; simp [A,L]
  rw [heq,L.iteratedFDeriv_comp_right hA x (by exact_mod_cast hn)]
  have hb := (iteratedFDeriv ℝ n A (L x)).norm_compContinuousLinearMap_le (fun _ => L)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hb
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    simp [L]
  have hp : ‖L‖^n ≤ 1 := pow_le_one₀ (norm_nonneg L) hL
  apply (hb.trans (mul_le_of_le_one_right (norm_nonneg _) hp)).trans_eq
  have hd := iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := F) n (t,0) (L x)
  change ‖iteratedFDeriv ℝ n (fun z => F ((t,0)+z)) (L x)‖ = _
  rw [hd]
  simp [L]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_FlowActualBound
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer the quantitative jet estimate to the actual closed-interval flow. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace ContinuumCoulomb

theorem flow_actual_higher_bound {U : Set (ℝ × Position)} (hU : IsOpen U)
    (hslab : Icc (0:ℝ) 1 ×ˢ (univ : Set Position) ⊆ U)
    (v : ℝ → Position → Position)
    (hv : ContDiffOn ℝ 4 (fun p : ℝ × Position => v p.1 p.2) U)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow v G)
    (k : ℕ) (hk0 : 1 ≤ k) (hk : k ≤ 3)
    (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hb : ∀ j ≤ 4, ∀ t ∈ Icc (0:ℝ) 1, ∀ z,
      ‖iteratedFDeriv ℝ j (fun p : ℝ × Position => v p.1 p.2) (t,z)‖ ≤ B)
    (hprev : ∀ j, 1 ≤ j → j ≤ k → ∀ t ∈ Icc (0:ℝ) 1, ∀ x,
      ‖iteratedFDeriv ℝ j (fun y => G y t) x‖ ≤ D^j)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (x : Position) :
    ‖iteratedFDeriv ℝ (k+1) (fun y => G y t) x‖ ≤
      ((k:ℝ)*2^k*(k.factorial:ℝ)*B*D^(k+1)) * Real.exp (B+1) := by
  obtain ⟨H,W,O,hH,hW,hO,hx,hEq,hODE,hWv⟩ := flow_local_equation hU hslab v hv G hG x
  have hder (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) (j : ℕ) :
      iteratedFDeriv ℝ j (fun y => G y s) x =
        iteratedFDeriv ℝ j (fun y => H (s,y)) x := by
    have heq : (fun y => G y s) =ᶠ[𝓝 x] (fun y => H (s,y)) := by
      filter_upwards [hO.mem_nhds hx] with y hy
      exact hEq y hy s hs
    exact (heq.iteratedFDeriv ℝ j).eq_of_nhds
  rw [hder t ht (k+1)]
  apply flow_local_higher_bound H W hH hW O hO x hx
    (fun y hy => (hEq y hy 0 ⟨le_rfl,zero_le_one⟩).symm.trans (hG.1 y))
    hODE k hk0 hk B D hB hD
  · intro s hs j hj hj'
    apply (flow_slice_derivative_bound W hW j (by omega) s (H (s,x))).trans
    rw [←hEq x hx s hs,(hWv s hs).iteratedFDeriv ℝ j |>.eq_of_nhds]
    exact hb j (by omega) s hs (G x s)
  · intro s hs j hj hj'
    rw [←hder s hs j]
    exact hprev j hj hj' s hs x
  · exact ht

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_FlowActualFirstBound
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal _root_.OAI.ContinuumCoulomb.spatialJetFiniteDimensional
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first variational estimate from the joint norm hypothesis. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace ContinuumCoulomb

theorem flow_actual_first_bound {U : Set (ℝ × Position)} (hU : IsOpen U)
    (hslab : Icc (0:ℝ) 1 ×ˢ (univ : Set Position) ⊆ U)
    (v : ℝ → Position → Position)
    (hv : ContDiffOn ℝ 4 (fun p : ℝ × Position => v p.1 p.2) U)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow v G)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ t ∈ Icc (0:ℝ) 1, ∀ z,
      ‖iteratedFDeriv ℝ 1 (fun p : ℝ × Position => v p.1 p.2) (t,z)‖ ≤ B)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (x : Position) :
    ‖iteratedFDeriv ℝ 1 (fun y => G y t) x‖ ≤ Real.exp B := by
  rw [norm_iteratedFDeriv_one]
  apply flow_first_derivative_bound_along hU hslab v hv G hG B hB x
  · obtain ⟨_H,W,_O,_hH,hW,_hO,_hx,_hEq,_hODE,hWv⟩ :=
      flow_local_equation hU hslab v hv G hG x
    intro s hs
    have heq : (fun z => W (s,z)) =ᶠ[𝓝 (G x s)] v s :=
      (hWv s hs).comp_tendsto (continuousAt_const.prodMk continuousAt_id)
    have hslice := flow_slice_derivative_bound W hW 1 (by norm_num) s (G x s)
    rw [norm_iteratedFDeriv_one,heq.fderiv_eq] at hslice
    apply hslice.trans
    rw [(hWv s hs).iteratedFDeriv ℝ 1 |>.eq_of_nhds]
    exact hb s hs (G x s)
  · exact ht

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_FlowDeterminant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The three-dimensional Liouville determinant calculation. It remains valid
at singular matrices and at endpoints with a one-sided derivative. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem flow_matrix_det_derivative
    (J : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (A : Matrix (Fin 3) (Fin 3) ℝ)
    (s : Set ℝ) (t : ℝ)
    (hJ : ∀ a b, HasDerivWithinAt (fun u => J u a b) ((A * J t) a b) s t) :
    HasDerivWithinAt (fun u => (J u).det) (A.trace * (J t).det) s t := by
  have hdet := (((((hJ 0 0).mul (hJ 1 1)).mul (hJ 2 2)).sub
      (((hJ 0 0).mul (hJ 1 2)).mul (hJ 2 1))).sub
      (((hJ 0 1).mul (hJ 1 0)).mul (hJ 2 2))).add
      (((hJ 0 1).mul (hJ 1 2)).mul (hJ 2 0))
  have hdet' := (hdet.add (((hJ 0 2).mul (hJ 1 0)).mul (hJ 2 1))).sub
      (((hJ 0 2).mul (hJ 1 1)).mul (hJ 2 0))
  convert hdet' using 1 <;> first | rfl | (funext u; exact Matrix.det_fin_three (J u)) | (
    simp only [Pi.mul_apply,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.det_fin_three]
    ring)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_FlowMatrix
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal _root_.OAI.ContinuumCoulomb.spatialJetFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinates of the actual spatial derivative in the standard orthonormal
basis, preserving its determinant and identifying the divergence with trace. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem flowMatrix_apply (L : Position →L[ℝ] Position) (a b : Fin 3) :
    flowMatrix L a b = L (NeutralAtom.axis b) a := by
  simp only [flowMatrix,LinearMap.toMatrix_apply,OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply,NeutralAtom.axis,ContinuousLinearMap.coe_coe]

theorem flowMatrix_comp (A B : Position →L[ℝ] Position) :
    flowMatrix (A.comp B) = flowMatrix A * flowMatrix B := by
  exact LinearMap.toMatrix_comp (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
    A.toLinearMap B.toLinearMap

theorem flowMatrix_det (L : Position →L[ℝ] Position) :
    (flowMatrix L).det = L.det :=
  LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis L.toLinearMap

theorem flowMatrix_trace (v : Position → Position) (x : Position)
    (hv : DifferentiableAt ℝ v x) :
    (flowMatrix (fderiv ℝ v x)).trace = fieldDivergence v x := by
  simp only [Matrix.trace,Matrix.diag,fieldDivergence]
  apply Finset.sum_congr rfl
  intro a _
  rw [flowMatrix_apply]
  have hd := (flowCoordinate a).hasFDerivAt.comp x hv.hasFDerivAt
  change fderiv ℝ v x (NeutralAtom.axis a) a =
    fderiv ℝ ((flowCoordinate a) ∘ v) x (NeutralAtom.axis a)
  rw [hd.fderiv]
  rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_FlowLiouville
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal _root_.OAI.ContinuumCoulomb.spatialJetFiniteDimensional
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Liouville's equation for the actual spatial Jacobian, on the closed time
interval and without an invertibility assumption. -/

noncomputable section
open Set
open scoped ContDiff
namespace ContinuumCoulomb

theorem flow_liouville {U : Set (ℝ × Position)} (hU : IsOpen U)
    (hslab : Icc (0:ℝ) 1 ×ˢ (univ : Set Position) ⊆ U)
    (v : ℝ → Position → Position)
    (hv : ContDiffOn ℝ 4 (fun p : ℝ × Position => v p.1 p.2) U)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow v G)
    (x : Position) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivWithinAt (fun s => flowJacobian G s x)
      (fieldDivergence (v t) (G x t) * flowJacobian G t x) (Icc (0:ℝ) 1) t := by
  let J : ℝ → Matrix (Fin 3) (Fin 3) ℝ :=
    fun s => flowMatrix (fderiv ℝ (fun y => G y s) x)
  let A : Matrix (Fin 3) (Fin 3) ℝ := flowMatrix (fderiv ℝ (v t) (G x t))
  have hv' : DifferentiableAt ℝ (v t) (G x t) := by
    have hh := (hv.contDiffAt (hU.mem_nhds (hslab ⟨ht,mem_univ (G x t)⟩))).comp
      (G x t) (contDiffAt_const.prodMk contDiffAt_id)
    exact hh.differentiableAt (by norm_num)
  have hJ (a b : Fin 3) :
      HasDerivWithinAt (fun s => J s a b) ((A * J t) a b) (Icc (0:ℝ) 1) t := by
    have hd := (flowCoordinate a).hasFDerivAt.comp_hasDerivWithinAt t
      (flow_spatial_variational hU hslab v hv G hG x (NeutralAtom.axis b) t ht)
    have hvalue : flowCoordinate a
        (fderiv ℝ (v t) (G x t) (fderiv ℝ (fun y => G y t) x (NeutralAtom.axis b))) =
        (A * J t) a b := by
      change _ = (flowMatrix (fderiv ℝ (v t) (G x t)) *
        flowMatrix (fderiv ℝ (fun y => G y t) x)) a b
      rw [←flowMatrix_comp,flowMatrix_apply]
      rfl
    rw [hvalue] at hd
    apply hd.congr_of_mem
    · intro s _
      exact flowMatrix_apply _ a b
    · exact ht
  have hd := flow_matrix_det_derivative J A (Icc (0:ℝ) 1) t hJ
  have hvalue : A.trace * (J t).det =
      fieldDivergence (v t) (G x t) * flowJacobian G t x := by
    rw [show A.trace = fieldDivergence (v t) (G x t) from flowMatrix_trace (v t) (G x t) hv']
    rw [show (J t).det = flowJacobian G t x from flowMatrix_det _]
  rw [hvalue] at hd
  exact hd.congr_of_mem (fun s _ => (flowMatrix_det _).symm) ht

theorem flow_regularity {U : Set (ℝ × Position)} (hU : IsOpen U)
    (hslab : Icc (0:ℝ) 1 ×ˢ (univ : Set Position) ⊆ U)
    (v : ℝ → Position → Position)
    (hv : ContDiffOn ℝ 4 (fun p : ℝ × Position => v p.1 p.2) U)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow v G) :
    (∀ t ∈ Icc (0:ℝ) 1, ContDiff ℝ 4 (fun x => G x t)) ∧
    (∀ x t, t ∈ Icc (0:ℝ) 1 →
      HasDerivWithinAt (fun s => flowJacobian G s x)
        (fieldDivergence (v t) (G x t) * flowJacobian G t x) (Icc (0:ℝ) 1) t) :=
  ⟨flow_spatial_C4 hU hslab v hv G hG,flow_liouville hU hslab v hv G hG⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_FlowUniform
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Discharge the finite C⁴ flow input by the four variational estimates. -/

noncomputable section
open Set
open scoped ContDiff
namespace ContinuumCoulomb

theorem flow_uniform_derivatives (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ UniformFlowDerivativeBound B C 4 := by
  have hind : ∀ k : ℕ, k ≤ 4 → ∃ C : ℝ, 0 < C ∧ UniformFlowDerivativeBound B C k := by
    intro k
    induction k with
    | zero =>
      intro _hk
      refine ⟨1,by norm_num,?_⟩
      intro U hU hs v hv hb G hG r hr hr'
      omega
    | succ k ih =>
      intro hk
      by_cases hk0 : k = 0
      · subst k
        refine ⟨Real.exp B,Real.exp_pos B,?_⟩
        intro U hU hs v hv hb G hG r hr hr' t ht x
        have heq : r = 1 := by omega
        subst r
        exact flow_actual_first_bound hU hs v hv G hG B hB (hb 1 (by norm_num)) t ht x
      · obtain ⟨M,hM,hMb⟩ := ih (by omega)
        let D := M+1
        let A := ((k:ℝ)*2^k*(k.factorial:ℝ)*B*D^(k+1))*Real.exp (B+1)
        have hD : 1 ≤ D := by dsimp [D]; linarith
        have hA : 0 ≤ A := by dsimp [A]; positivity
        refine ⟨M+A+1,by linarith,?_⟩
        intro U hU hs v hv hb G hG r hr hr' t ht x
        by_cases hrk : r ≤ k
        · exact (hMb U hU hs v hv hb G hG r hr hrk t ht x).trans (by linarith)
        · have heq : r = k+1 := by omega
          subst r
          have hprev : ∀ j, 1 ≤ j → j ≤ k → ∀ s ∈ Icc (0:ℝ) 1, ∀ y,
              ‖iteratedFDeriv ℝ j (fun z => G z s) y‖ ≤ D^j := by
            intro j hj hj' s hs' y
            apply (hMb U hU hs v hv hb G hG j hj hj' s hs' y).trans
            exact (show M ≤ D by dsimp [D]; linarith).trans
              (le_self_pow₀ hD (by omega))
          have h := flow_actual_higher_bound hU hs v hv G hG k (by omega) (by omega)
            B D hB (le_trans zero_le_one hD) hb hprev t ht x
          exact h.trans (by change A ≤ M+A+1; linarith)
  exact hind 4 le_rfl

theorem publishedC4FlowInput : PublishedC4FlowInput where
  regularity := fun _U hU hs v hv G hG => flow_regularity hU hs v hv G hG
  uniform := flow_uniform_derivatives

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_OneInputHardness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Continuum Coulomb hardness follows from hardness of the field-free
signed square-lattice Heisenberg energy problem.
-/

noncomputable section
namespace ContinuumCoulomb

theorem binary_coulomb_qmaHard_of_cmp (hcmp : PublishedCMPHardness) :
    QMAHard binaryCoulombCodec.encode binaryCoulombPromise :=
  binary_coulomb_qmaHard_of_two_inputs hcmp publishedC4FlowInput

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_Hardness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
QMA hardness of continuum Coulomb energy with unit nuclear charges
and with binary-encoded positive integer nuclear charges.
-/

noncomputable section
namespace ContinuumCoulomb

theorem binary_coulomb_qmaHard_oai : QMAHard binaryCoulombCodec.encode binaryCoulombPromise :=
  binary_coulomb_qmaHard_of_cmp publishedCMPHardness

end ContinuumCoulomb

end

end OAI
end

theorem solution : type_of% @OAI.ContinuumCoulomb.binary_coulomb_qmaHard_oai := @OAI.ContinuumCoulomb.binary_coulomb_qmaHard_oai
