-- Prove2me | solution 1 for MIPStarRE.LDT.avgOver_uniform_equiv
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:34:20.263878+00:00
-- url     : https://prove2.me/submissions/cdcc32fb-e950-4376-8475-9736e9a7ecf2

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Basic/DistributionAvg.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Basic/Distribution.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Basic/PMFAverages.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Basic/DistributionUniformSums.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/DistributionAvg.lean (solution of MIPStarRE.LDT.avgOver_uniform_equiv);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Invertible.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Subsemigroup.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.GroupWithZero.Invertible
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Opposites
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Nonneg.Basic
import Mathlib.Algebra.Order.Nonneg.Module
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finset.Attach
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Prod.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.Data.Set.Defs
import Mathlib.Data.SetLike.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Nonempty
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Order.Notation
import Mathlib.Order.RelClasses
import Mathlib.Order.SetNotation
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.Star.Real
import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Continuous
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.UniformSpace.Defs
import Mathlib.Topology.UniformSpace.Real
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Theorems.Thm_PMF_map_sum_smul
import Theorems.Thm_PMF_uniformOfFintype_map_equiv

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPStarRE.LDT
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
/-- On a finite ambient type, a summand that vanishes outside a distribution's
explicit support has the same total sum over all ambient values as over that support.

This is a project-local explicit-support adapter around Mathlib's `Finset.sum_subset`:
Mathlib supplies the finite-sum theorem, while this lemma packages the common shape used
when paper expressions sum over a whole question set but the repository stores a smaller
`Distribution.support`.  It is not intended to replace Mathlib probability theory. -/
theorem Distribution.sum_univ_eq_sum_support {α β : Type*} [Fintype α]
    [AddCommMonoid β] (𝒟 : Distribution α) (f : α → β)
    (hf : ∀ a, a ∉ 𝒟.support → f a = 0) :
    (∑ a : α, f a) = ∑ a ∈ 𝒟.support, f a := by
  classical
  simpa using
    (Finset.sum_subset (Finset.subset_univ 𝒟.support)
      (fun a _ ha => hf a ha)).symm
end
end MIPStarRE.LDT

namespace MIPStarRE.LDT.Distribution
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
/-- The associated PMF has zero mass outside the stored support of the project
distribution. -/
theorem toPMF_apply_of_notMem {α : Type*} (𝒟 : Distribution α)
    (h𝒟 : 𝒟.IsProbability) {a : α} (ha : a ∉ 𝒟.support) :
    𝒟.toPMF h𝒟 a = 0 := by
  rw [toPMF_apply, 𝒟.outsideSupport a ha]
  simp
end
end MIPStarRE.LDT.Distribution

namespace MIPStarRE.LDT.Distribution
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
/-- The project uniform distribution on a nonempty finite support is Mathlib's
uniform probability mass function on that support. -/
theorem uniformOnFinset_toPMF
    {α : Type*} (s : Finset α) (hs : s.Nonempty) :
    (uniformOnFinset s).toPMF (uniformOnFinset_isProbability s hs) =
      PMF.uniformOfFinset s hs := by
  ext a
  rw [toPMF_apply]
  rw [show (uniformOnFinset s).weight a =
      (PMF.uniformOfFinset s hs a).toReal by
        classical
        by_cases ha : a ∈ s
        · simp [uniformOnFinset_weight, PMF.uniformOfFinset_apply, ha,
            ENNReal.toReal_inv, ENNReal.toReal_natCast]
        · simp [uniformOnFinset_weight, PMF.uniformOfFinset_apply, ha]]
  exact ENNReal.ofReal_toReal ((PMF.uniformOfFinset s hs).apply_ne_top a)
end
end MIPStarRE.LDT.Distribution

namespace MIPStarRE.LDT
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
/-- The project uniform distribution on a nonempty finite type is Mathlib's
uniform probability mass function on that type. -/
theorem uniformDistribution_toPMF
    (α : Type*) [Fintype α] [DecidableEq α] [Nonempty α] :
    (uniformDistribution α).toPMF (uniformDistribution_isProbability α) =
      PMF.uniformOfFintype α := by
  simpa [uniformDistribution, PMF.uniformOfFintype] using
    Distribution.uniformOnFinset_toPMF (Finset.univ : Finset α) Finset.univ_nonempty
end
end MIPStarRE.LDT

namespace PMF
section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
/-- Reindex a finite sum weighted by Mathlib's uniform PMF along an equivalence. -/
theorem uniformOfFintype_sum_equiv_smul {α β M : Type*}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (e : α ≃ β) (f : α → M) :
    ∑ a : α, (PMF.uniformOfFintype α a).toReal • f a =
      ∑ b : β, (PMF.uniformOfFintype β b).toReal • f (e.symm b) := by
  calc
    ∑ a : α, (PMF.uniformOfFintype α a).toReal • f a =
        ∑ b : β, (((PMF.uniformOfFintype α).map e) b).toReal • f (e.symm b) := by
          simpa using
            (map_sum_smul
              (p := PMF.uniformOfFintype α) (e := e)
              (f := fun b : β => f (e.symm b))).symm
    _ = ∑ b : β, (PMF.uniformOfFintype β b).toReal • f (e.symm b) := by
          rw [uniformOfFintype_map_equiv e]
end
end PMF

namespace PMF
section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
/-- Reindex a finite expectation against Mathlib's uniform PMF along an
equivalence. -/
theorem realWeightedSum_uniformOfFintype_equiv {α β M : Type*}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (e : α ≃ β) (f : α → M) :
    realWeightedSum (PMF.uniformOfFintype α) f =
      realWeightedSum (PMF.uniformOfFintype β) (fun b => f (e.symm b)) := by
  simpa [realWeightedSum] using
    uniformOfFintype_sum_equiv_smul (e := e) (f := f)
end
end PMF

namespace MIPStarRE.LDT.Distribution
section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
/-- A module-valued finite weighted sum against a probabilistic project
distribution may be written with the real weights of the associated Mathlib
probability mass function, over the stored support. -/
theorem sum_smul_eq_toPMF_support_sum {α M : Type*}
    [AddCommMonoid M] [Module Error M]
    (𝒟 : Distribution α) (h𝒟 : 𝒟.IsProbability) (f : α → M) :
    ∑ a ∈ 𝒟.support, 𝒟.weight a • f a =
      ∑ a ∈ 𝒟.support, (𝒟.toPMF h𝒟 a).toReal • f a := by
  exact Finset.sum_congr rfl fun a _ => by
    rw [Distribution.toPMF_apply_toReal]
end
end MIPStarRE.LDT.Distribution

namespace MIPStarRE.LDT.Distribution
section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
/-- A module-valued finite weighted sum against a probabilistic project
distribution may be written as a full finite sum with the real weights of the
associated Mathlib probability mass function. -/
theorem sum_smul_eq_toPMF_sum {α M : Type*} [Fintype α]
    [AddCommMonoid M] [Module Error M]
    (𝒟 : Distribution α) (h𝒟 : 𝒟.IsProbability) (f : α → M) :
    ∑ a ∈ 𝒟.support, 𝒟.weight a • f a =
      ∑ a : α, (𝒟.toPMF h𝒟 a).toReal • f a := by
  rw [Distribution.sum_smul_eq_toPMF_support_sum 𝒟 h𝒟 f]
  exact (Distribution.sum_univ_eq_sum_support 𝒟
    (fun a => (𝒟.toPMF h𝒟 a).toReal • f a)
    (by
      intro a ha
      rw [Distribution.toPMF_apply_of_notMem 𝒟 h𝒟 ha]
      simp)).symm
end
end MIPStarRE.LDT.Distribution

namespace MIPStarRE.LDT
section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
/-- Module-valued finite-sum expression for the uniform distribution, stated
without measurable-space assumptions. -/
theorem uniformDistribution_sum_smul_eq_pmf_sum {α M : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [AddCommMonoid M] [Module Error M] (f : α → M) :
    ∑ a ∈ (uniformDistribution α).support, (uniformDistribution α).weight a • f a =
      ∑ a : α, (PMF.uniformOfFintype α a).toReal • f a := by
  rw [Distribution.sum_smul_eq_toPMF_sum
    (uniformDistribution α) (uniformDistribution_isProbability α)]
  rw [uniformDistribution_toPMF]
end
end MIPStarRE.LDT

namespace MIPStarRE.LDT
section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
/-- Reindex a uniform module-valued average along an equivalence. -/
theorem uniformDistribution_sum_smul_equiv {α β M : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    [AddCommMonoid M] [Module Error M]
    (e : α ≃ β) (f : α → M) :
    ∑ a ∈ (uniformDistribution α).support, (uniformDistribution α).weight a • f a =
      ∑ b ∈ (uniformDistribution β).support,
        (uniformDistribution β).weight b • f (e.symm b) := by
  rw [uniformDistribution_sum_smul_eq_pmf_sum (α := α)]
  rw [uniformDistribution_sum_smul_eq_pmf_sum (α := β)]
  simpa [PMF.realWeightedSum] using
    PMF.realWeightedSum_uniformOfFintype_equiv (e := e) (f := f)
end
end MIPStarRE.LDT

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
theorem _root_.solution
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (e : α ≃ β) (f : α → Error) :
    avgOver (uniformDistribution α) f =
      avgOver (uniformDistribution β) (fun b => f (e.symm b)) := by
  simpa [avgOver, smul_eq_mul] using
    (uniformDistribution_sum_smul_equiv (M := Error) (e := e) (f := f))
end MIPStarRE.LDT
