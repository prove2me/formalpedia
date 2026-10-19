-- Prove2me | solution 1 for MIPStarRE.LDT.SelfImprovement.selfImprovement
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T05:51:03.005066+00:00
-- url     : https://prove2.me/submissions/34061188-a299-4433-8c3c-c5bb73ba6118

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/SelfImprovement/Theorems/Results/SelfImprovementTop/Core.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Basic/ParametersBase.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/SelfImprovement/Defs.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/SelfImprovement/Theorems/Statements.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/SelfImprovement/Theorems/Thresholds/Helper.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/SelfImprovement/Theorems/Thresholds/Final.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/SelfImprovement/Theorems/Results/CommonHelpers.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/SelfImprovement/Theorems/Results/HelperCompleteness/Linearized.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/SelfImprovement/MatrixRealization/Canonical/Saturated.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/SelfImprovement/Theorems/Results/SdpMatrixBridge.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/SelfImprovement/Theorems/Results/HelperCompleteness/Bracketed.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/SelfImprovement/Theorems/Results/SelfImprovementTop/Core.lean (solution of MIPStarRE.LDT.SelfImprovement.selfImprovement);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.IsField
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Opposite
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Group.Invertible.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Opposite
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Subsemigroup.Defs
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.GroupWithZero.Invertible
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Module.Torsion.Pi
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Basic
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Notation.Prod
import Mathlib.Algebra.Opposites
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.IsBotOne
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.NatCast
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Nonneg.Basic
import Mathlib.Algebra.Order.Nonneg.Module
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Pi
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Unitary
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.Convex.Cone.Closure
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Spectrum
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Countable.Defs
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finset.Attach
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Embedding
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.FunLike.IsApply
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sort
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Multiset.ZeroCons
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.NNReal.Star
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Prod.Basic
import Mathlib.Data.Quot
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Init
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.Data.SProd
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.CoeSort
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Set.Operations
import Mathlib.Data.Set.Restrict
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.Sigma.Basic
import Mathlib.Data.ULift
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.Separable
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.CharP
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Basic
import Mathlib.Logic.Embedding.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Function.Defs
import Mathlib.Logic.IsEmpty.Basic
import Mathlib.Logic.IsEmpty.Defs
import Mathlib.Logic.Nonempty
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Logic.Unique
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Order.Basic
import Mathlib.Order.BooleanAlgebra.Defs
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Filter.Extr
import Mathlib.Order.Filter.Tendsto
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.MinMax
import Mathlib.Order.Monotone.Defs
import Mathlib.Order.Nat
import Mathlib.Order.Notation
import Mathlib.Order.RelClasses
import Mathlib.Order.SetNotation
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Attr.Register
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.Star.Real
import Mathlib.Topology.Algebra.UniformMulAction
import Mathlib.Topology.Bases
import Mathlib.Topology.Basic
import Mathlib.Topology.Bornology.Basic
import Mathlib.Topology.Closure
import Mathlib.Topology.Constructions
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Continuous
import Mathlib.Topology.ContinuousMap.ContinuousSqrt
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.GDelta
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.Defs
import Mathlib.Topology.UniformSpace.Real
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Statements
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_ConsistencyBridges
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Projectivization
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_ProjectorONB
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_Sigma
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_LowRank
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_QCompleteness
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Rows
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Completion
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_LayerAlgebra
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_ProjectorApprox
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Completion
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Triangles_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_ProjectivizationChain_Basic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_PolynomialAgreement
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Operators
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Families
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Statements
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_SpectralTruncation_ProjectiveNonMeasurement
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_SpectralTruncation_Conversion
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_LocalityPreservingRepair
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Orthonormalization_RestrictSome
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Orthonormalization
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_DataProcessing
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Thresholds_Final
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_InputSdp
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_FiberBounds
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_Linearized
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Fourier
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_TraceForms
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Base
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_CanonicalPrimal
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_Witness
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_Saturated
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteConicDuality
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_StrongDuality_Basic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_StrongDuality_Separation
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_SdpMatrixBridge
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Foundations
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Matrix
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Results
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_Averaging
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_Statements
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_AlgebraicIdentity
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_CollisionExpansion
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransport_PointLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_TransportChain_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransportSum
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_PolynomialSumBounds
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_Bracketed
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_Selection
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_Residual
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_ScalarChain
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep12_Algebra
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep12_Raw
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep12_Selected
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep34AndTransfer_Factored
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep34AndTransfer_Selected
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep34AndTransfer_Variance
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperSSC_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperSSC_PostDeleteA
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUPointConsistency
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_SelfImprovementTop_Completeness
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_AddInUFullStatement
import Theorems.Thm_MIPStarRE_LDT_GlobalVariance_localVarianceDeviation_sum_le_localVarianceOfPointsError
import Theorems.Thm_MIPStarRE_LDT_MakingMeasurementsProjective_orthonormalization
import Theorems.Thm_MIPStarRE_LDT_Preliminaries_completenessTransferProjectiveP
import Theorems.Thm_MIPStarRE_LDT_Preliminaries_completenessTransferSelfConsistentA
import Theorems.Thm_MIPStarRE_LDT_Preliminaries_sddRel_symm
import Theorems.Thm_MIPStarRE_LDT_Preliminaries_selfConsistencyImpliesDataProcessing
import Theorems.Thm_MIPStarRE_LDT_SelfImprovement_MatrixSdpCanonicalOptimalPair_ofFeasibleStrongDualitySaturateSlackBlock
import Theorems.Thm_MIPStarRE_LDT_SelfImprovement_MatrixSdpOptimalWitness_toSdpOptimalPairWithSlackness
import Theorems.Thm_MIPStarRE_LDT_SelfImprovement_addInUFullStatement_of_isGood
import Theorems.Thm_MIPStarRE_LDT_SelfImprovement_d_q_ratio_nonneg
import Theorems.Thm_MIPStarRE_LDT_SelfImprovement_final_fields_of_helper_outputs_of_total_difference
import Theorems.Thm_MIPStarRE_LDT_SelfImprovement_final_fields_point_consistency_total_difference_error_le_selfImprovementError
import Theorems.Thm_MIPStarRE_LDT_SelfImprovement_helperDeleteAClonedQuantity_abs_sub_moveOverVQuantity_le_sqrt_two_delta
import Theorems.Thm_MIPStarRE_LDT_SelfImprovement_helperDeleteAQuantity_abs_sub_clonedQuantity_le_sqrt
import Theorems.Thm_MIPStarRE_LDT_SelfImprovement_helper_completeness_error_le_selfImprovementHelperError
import Theorems.Thm_MIPStarRE_LDT_SelfImprovement_helper_first_move_abs_sub_bracketed_le_two_sqrt_delta
import Theorems.Thm_MIPStarRE_LDT_SelfImprovement_helper_hhat_vs_z_of_cauchy_schwarz_and_complementary_slackness
import Theorems.Thm_MIPStarRE_LDT_SelfImprovement_helper_mass_eq_avg_pointwise_sandwich_sum
import Theorems.Thm_MIPStarRE_LDT_SelfImprovement_helper_pointwise_sandwich_sum_eq_bracketed
import Theorems.Thm_MIPStarRE_LDT_SelfImprovement_helper_second_move_abs_sub_first_moved_le_sqrt_delta
import Theorems.Thm_MIPStarRE_LDT_SelfImprovement_helper_ssc_bounds_of_scalarTransports_pointTransfer
import Theorems.Thm_MIPStarRE_LDT_SelfImprovement_helper_strong_self_consistency_of_helper_conclusion
import Theorems.Thm_MIPStarRE_LDT_SelfImprovement_input_consistency_dual_mass_lower_bound
import Theorems.Thm_MIPStarRE_LDT_SelfImprovement_matrixSdpCanonicalStrongDuality
import Theorems.Thm_MIPStarRE_LDT_SelfImprovement_matrixSdpOptimalWitness_of_canonicalFeasibleSaturatedComplementarySlackness
import Theorems.Thm_MIPStarRE_LDT_SelfImprovement_selfImprovementHelperError_nonneg
import Theorems.Thm_MIPStarRE_LDT_SelfImprovement_selfImprovement_of_error_ge_one
import Theorems.Thm_MIPStarRE_LDT_SelfImprovement_self_improvement_helper_with_slackness_of_sdp_statement_with_slackness
import Theorems.Thm_MIPStarRE_LDT_averageOperatorOverDistribution_nonneg
import Theorems.Thm_MIPStarRE_LDT_avgOver_congr
import Theorems.Thm_MIPStarRE_LDT_bipartiteConsError_nonneg
import Theorems.Thm_MIPStarRE_LDT_delta_nonneg_of_isGood
import Theorems.Thm_MIPStarRE_LDT_eps_nonneg_of_isGood

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPStarRE.LDT.Parameters
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
/-- Positivity of the field-size parameter after casting to the repository's
real-valued error scalar type. -/
theorem q_cast_pos (params : Parameters) : 0 < (params.q : Error) :=
  Nat.cast_pos.mpr params.hq
end
end MIPStarRE.LDT.Parameters

attribute [instance] MIPStarRE.LDT.FieldModel.instField MIPStarRE.LDT.FieldModel.instFintype MIPStarRE.LDT.FieldModel.instDecidableEq

namespace MIPStarRE.LDT.SelfImprovement
section
open MIPStarRE.LDT
open MIPStarRE.Quantum
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The averaged point operator `A_g` is positive semidefinite. -/
theorem averagedPointOperator_nonneg (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι) (g : Polynomial params) :
    0 ≤ averagedPointOperator params strategy g := by
  unfold averagedPointOperator
  exact averageOperatorOverDistribution_nonneg (uniformDistribution (Point params))
    (pointConditionedOutcomeOperatorAtPolynomial params strategy g)
    (fun u => (strategy.pointMeasurement u).toSubMeas.outcome_pos (g u))
end
end MIPStarRE.LDT.SelfImprovement

namespace MIPStarRE.LDT.SelfImprovement
section
open MIPStarRE.LDT
open MIPStarRE.Quantum
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Dual feasibility already implies that the dual operator is positive
semidefinite, since every averaged point operator `A_g` is positive. -/
theorem sdpDualPositive_of_dualFeasible (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (Z : MIPStarRE.Quantum.Op ι)
    (hdual :
      ∀ g : Polynomial params,
        0 ≤ sdpDualSlackOperator params strategy Z g) :
    0 ≤ Z := by
  -- Any polynomial would suffice here; the distinguished one is only a
  -- convenient fixed element of the finite polynomial type.
  let g0 : Polynomial params := sdpDistinguishedPolynomial params
  have hAg_nonneg : 0 ≤ averagedPointOperator params strategy g0 :=
    averagedPointOperator_nonneg params strategy g0
  have hAg_le_Z : averagedPointOperator params strategy g0 ≤ Z :=
    sub_nonneg.mp (by simpa [sdpDualSlackOperator] using hdual g0)
  exact hAg_nonneg.trans hAg_le_Z
end
end MIPStarRE.LDT.SelfImprovement

namespace MIPStarRE.LDT.SelfImprovement.SdpOptimalPair
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The dual operator in an SDP witness is positive semidefinite. -/
theorem dualPositive {params : Parameters} [FieldModel params.q]
    {strategy : SymStrat params ι}
    {T : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (h : SdpOptimalPair params strategy T Z) :
    0 ≤ Z :=
  sdpDualPositive_of_dualFeasible params strategy Z h.dualFeasible
end
end MIPStarRE.LDT.SelfImprovement.SdpOptimalPair

namespace MIPStarRE.LDT.SelfImprovement
section
open MIPStarRE.LDT
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
set_option backward.isDefEq.respectTransparency false
/-- The parameter `m` is at least one, viewed in the error scalar field. -/
theorem one_le_m_cast (params : Parameters) :
    (1 : Error) ≤ (params.m : Error) := by exact_mod_cast params.hm
end
end MIPStarRE.LDT.SelfImprovement

namespace MIPStarRE.LDT.SelfImprovement
section
open MIPStarRE.LDT
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
set_option backward.isDefEq.respectTransparency false
/-- The final self-improvement threshold as the final-stage power sum with
exponent `1/32`.

This records the literal error parameter appearing in the formal statement of
the self-improvement theorem. -/
theorem selfImprovementError_eq_finalStagePowerSum
    (params : Parameters) [FieldModel params.q] (eps delta : Error) :
    selfImprovementError params eps delta =
      3000 * (params.m : Error) * finalStagePowerSum params eps delta (1 / (32 : Error)) := by
  try rfl
end
end MIPStarRE.LDT.SelfImprovement

namespace MIPStarRE.LDT.SelfImprovement
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Internal helper: lift bipartite SSC from `Unit` to any nonempty question type. -/
lemma bipartiteSSCRel_uniform_const
    {Question Outcome : Type*}
    [Fintype Question] [DecidableEq Question] [Nonempty Question]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (A : SubMeas Outcome ι) (δ : Error) :
    BipartiteSSCRel ψ (uniformDistribution Unit) (constSubMeasFamily A) δ →
      BipartiteSSCRel ψ (uniformDistribution Question) (fun _ : Question => A) δ := by
  intro hssc
  rcases hssc with ⟨hssc⟩
  constructor
  simpa [bipartiteSSCError, avgOver, uniformDistribution, constSubMeasFamily] using hssc
end
end MIPStarRE.LDT.SelfImprovement

namespace MIPStarRE.LDT.SelfImprovement
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Internal helper: lift SDD from `Unit` to any nonempty question type. -/
lemma sddRel_uniform_const
    {κ Question Outcome : Type*}
    [Fintype κ] [DecidableEq κ]
    [Fintype Question] [DecidableEq Question] [Nonempty Question]
    [Fintype Outcome]
    (ψ : QuantumState κ)
    (A B : SubMeas Outcome κ) (δ : Error) :
    SDDRel ψ (uniformDistribution Unit) (constSubMeasFamily A) (constSubMeasFamily B) δ →
      SDDRel ψ (uniformDistribution Question) (fun _ : Question => A)
        (fun _ : Question => B) δ := by
  intro hsdd
  rcases hsdd with ⟨hsdd⟩
  constructor
  simpa [sddError, avgOver, uniformDistribution, constSubMeasFamily] using hsdd
end
end MIPStarRE.LDT.SelfImprovement

namespace MIPStarRE.LDT.SelfImprovement
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Helper-stage completeness from the `Hhat`-versus-`Z` comparison and the
dual-mass lower bound.

The paper proves
`subMeasMass ψ Hhat.liftLeft ≥ ⟨ψ, Z ⊗ I, ψ⟩ - 3 √δ` by the two
Cauchy--Schwarz moves in the helper-completeness paragraph.  Once the separate
input-consistency argument gives `1 - ν ≤ ⟨ψ, Z ⊗ I, ψ⟩`, this theorem performs
the scalar assembly and absorbs the loss `3 √δ` into the helper threshold
`ζ̂ = selfImprovementHelperError params eps delta`. -/
theorem helper_completeness_of_dual_mass_lower_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta nu : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hHhat_vs_Z :
      ev strategy.state (leftTensor (ι₂ := ι) Z) - 3 * Real.sqrt delta ≤
        subMeasMass strategy.state Hhat.liftLeft)
    (hdualMass :
      1 - nu ≤ ev strategy.state (leftTensor (ι₂ := ι) Z)) :
    CompletenessAtLeast strategy.state Hhat.liftLeft
      ((1 - nu) - selfImprovementHelperError params eps delta) := by
  refine ⟨?_⟩
  have herr :=
    helper_completeness_error_le_selfImprovementHelperError params eps delta heps hdelta
  linarith
end
end MIPStarRE.LDT.SelfImprovement

namespace MIPStarRE.LDT.SelfImprovement
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Helper-stage completeness from input consistency and the
`Hhat`-versus-`Z` comparison.

This is the checked assembly of the final part of the helper-completeness
paragraph in `thm:self-improvement`.  The only analytic input still external is
the paper's Cauchy--Schwarz comparison
`subMeasMass ψ Hhat.liftLeft ≥ ⟨ψ, Z ⊗ I, ψ⟩ - 3 √δ`; the SDP dual-feasibility
fields of `SelfImprovementHelperConclusion` and the input consistency of `G`
produce the dual-mass lower bound internally. -/
theorem helper_completeness_of_input_consistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : Measurement (Polynomial params) ι)
    (eps delta nu : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hHhat_vs_Z :
      ev strategy.state (leftTensor (ι₂ := ι) Z) - 3 * Real.sqrt delta ≤
        subMeasMass strategy.state Hhat.liftLeft)
    (hcons : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas) nu) :
    CompletenessAtLeast strategy.state Hhat.liftLeft
      ((1 - nu) - selfImprovementHelperError params eps delta) := by
  refine
    helper_completeness_of_dual_mass_lower_bound params strategy eps delta nu
      heps hdelta hHhat_vs_Z ?_
  exact
    input_consistency_dual_mass_lower_bound params strategy G Z nu
      hhelper.sdpWitness.dualPositive hhelper.sdpWitness.dualFeasible hcons
end
end MIPStarRE.LDT.SelfImprovement

namespace MIPStarRE.LDT.SelfImprovement
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
/-- Assemble the canonical block-SDP conclusions as the matrix-level statement
with zero slack block.

For a feasible canonical primal matrix `X`, the hypothesis
`X_none,none = 0` is exactly the saturated form of the paper's final slack
block assertion.  The theorem extracts the polynomial diagonal blocks and
records the resulting complete primal measurement and complementary-slackness
equations. -/
theorem matrixSdpStatementWithSlackness_of_canonicalFeasibleSaturatedComplementarySlackness
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X)
    (Z : MatrixOperator model.space)
    (hdual :
      ∀ g : Polynomial params,
        0 ≤ matrixSdpDualSlackOperator params model Z g)
    (hstrong :
      Complex.re (Matrix.trace
          (matrixSdpCanonicalObjectiveOperator params model * X)) =
        matrixSdpDualObjective model Z)
    (hcanonical :
      X * (matrixSdpCanonicalDualOperator params model Z -
            matrixSdpCanonicalObjectiveOperator params model) =
        0)
    (hSlack : matrixSdpCanonicalDiagonalBlock params model X none = 0) :
    MatrixSdpStatementWithSlackness params model where
  witness :=
    let hopt :=
      matrixSdpOptimalWitness_of_canonicalFeasibleSaturatedComplementarySlackness
        params model X hX Z hdual hstrong hcanonical hSlack
    ⟨hopt.primalMeasurement, Z, by
      simpa [MatrixSdpOptimalWitness.primalMeasurement,
        MIPStarRE.Quantum.Measurement.ofSumEqOne] using hopt⟩
end
end MIPStarRE.LDT.SelfImprovement

namespace MIPStarRE.LDT.SelfImprovement.MatrixSdpCanonicalOptimalPair
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- A saturated canonical optimal pair gives the matrix-level slackness
statement without adding the auxiliary dominance condition. -/
theorem toMatrixSdpStatementWithSlackness
    {params : Parameters}
    [FieldModel params.q]
    {model : MatrixSdpRealization params}
    {X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)}
    {Z : MatrixOperator model.space}
    (h : MatrixSdpCanonicalOptimalPair params model X Z) :
    MatrixSdpStatementWithSlackness params model :=
  matrixSdpStatementWithSlackness_of_canonicalFeasibleSaturatedComplementarySlackness
    params model X h.feasible Z h.dualFeasible h.strongDuality
    h.complementarySlackness h.slackBlock_eq_zero
end
end MIPStarRE.LDT.SelfImprovement.MatrixSdpCanonicalOptimalPair

namespace MIPStarRE.LDT.SelfImprovement.MatrixSdpStatementWithSlackness
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- A matrix strong-duality statement for the point-measurement realization of
a strategy implies the abstract slackness statement. -/
theorem toSdpStatementWithSlackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (h : MatrixSdpStatementWithSlackness params
      (matrixSdpPointRealizationOfStrategy params strategy)) :
    SdpStatementWithSlackness params strategy := by
  obtain ⟨T, Z, hopt⟩ := h.witness
  exact ⟨MatrixMeasurement.toMeasurement T, Z, by
    simpa [MatrixMeasurement.toMeasurement] using hopt.toSdpOptimalPairWithSlackness⟩
end
end MIPStarRE.LDT.SelfImprovement.MatrixSdpStatementWithSlackness

namespace MIPStarRE.LDT.SelfImprovement
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Canonical strong-duality and complementary-slackness construction for the
point-measurement realization of the Section 9 SDP.

Paper origin: `references/ldt-paper/self_improvement.tex` lines 82--190
(`\label{lem:sdp}` and the proof using Slater's condition).  The paper first
rewrites the primal and dual SDPs in canonical block form, invokes strong
duality, and then applies complementary slackness to obtain a saturated
canonical optimal pair.

This is the source-faithful construction for the formalized SDP route.  Its
conclusion is the native canonical block-SDP output: a feasible canonical primal
matrix, a dual-feasible operator with equal objective value, canonical
complementary slackness, and a vanishing slack block.  It does not
assume the auxiliary dominance condition `I ≤ Z`; the saturated slack block is
part of the expected strong-duality output.  The matrix statement
`matrixSdpPointRealization_statementWithSlackness` follows by extracting the
diagonal polynomial blocks.

Tracked by issue #1230 and documented in
`docs/paper-gaps/issue-1230-self-improvement-sdp-usage.tex`. -/
theorem matrixSdpPointRealization_canonicalOptimalPair
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι) :
    ∃ X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params
        (matrixSdpPointRealizationOfStrategy params strategy)),
      ∃ Z : MIPStarRE.Quantum.Op ι,
        MatrixSdpCanonicalOptimalPair params
          (matrixSdpPointRealizationOfStrategy params strategy) X Z := by
  let model := matrixSdpPointRealizationOfStrategy params strategy
  obtain ⟨X, Z, hX, hdual, hstrong⟩ := matrixSdpCanonicalStrongDuality params model
  refine ⟨matrixSdpCanonicalSaturateSlackBlockMatrix params model X, Z, ?_⟩
  exact MatrixSdpCanonicalOptimalPair.ofFeasibleStrongDualitySaturateSlackBlock
    (params := params) (model := model) (X := X) (Z := Z) hX hdual hstrong
end
end MIPStarRE.LDT.SelfImprovement

namespace MIPStarRE.LDT.SelfImprovement
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Matrix-level strong-duality and complementary-slackness statement for the
point-measurement realization of the Section 9 SDP.

Paper origin: `references/ldt-paper/self_improvement.tex` lines 82--190
(`\label{lem:sdp}`), documented by
`docs/paper-gaps/issue-1230-self-improvement-sdp-usage.tex`.

**Source-faithful transport:** This declaration is a proved extraction from the
canonical optimal-pair construction for `lem:sdp`; it is not a conditional
replacement for the SDP strong-duality theorem.

This theorem is a proved transport from the native canonical optimal-pair
construction `matrixSdpPointRealization_canonicalOptimalPair`.  It contains no
additional dominance, bridge, residual, or package hypothesis. -/
theorem matrixSdpPointRealization_statementWithSlackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι) :
    MatrixSdpStatementWithSlackness params
      (matrixSdpPointRealizationOfStrategy params strategy) := by
  rcases matrixSdpPointRealization_canonicalOptimalPair params strategy with
    ⟨X, Z, hpair⟩
  exact hpair.toMatrixSdpStatementWithSlackness
end
end MIPStarRE.LDT.SelfImprovement

namespace MIPStarRE.LDT.SelfImprovement
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Bracketed form of the helper-stage `Hhat ⊗ I` mass identity.

Combines `helper_mass_eq_avg_pointwise_sandwich_sum` with the per-point
bracketing identity `helper_pointwise_sandwich_sum_eq_bracketed`:

  `⟨ψ| Hhat ⊗ I |ψ⟩
    = E_u Σ_a ⟨ψ| (A^u_a · T_{[h(u) = a]} · A^u_a) ⊗ I |ψ⟩`,

where `T_{[h(u) = a]} = Σ_{h : h u = a} T_h`. This is the second equality in the
displayed completeness chain at
`references/ldt-paper/self_improvement.tex`, lines 354--358 (mirrored at
`blueprint/src/chapter/ch07_self_improvement.tex`, lines 103--113), composed
with the bracketing reindexing `eq:bracketize-the-expression`. The conclusion
is exact (not approximate) and depends on no input-consistency, SDP, or
self-consistency hypotheses. -/
theorem helper_mass_eq_avg_pointwise_bracketed_sum
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    subMeasMass strategy.state
        (averagedSandwichedPolynomialSubMeas params strategy T).liftLeft =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ a : Fq params,
          ev strategy.state
            (leftTensor (ι₂ := ι)
              ((strategy.pointMeasurement u).outcome a *
                (∑ h ∈ Finset.univ.filter (fun h : Polynomial params => h u = a),
                  T.outcome h) *
                (strategy.pointMeasurement u).outcome a))) := by
  rw [helper_mass_eq_avg_pointwise_sandwich_sum]
  refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
  intro u
  exact helper_pointwise_sandwich_sum_eq_bracketed params strategy T u
end
end MIPStarRE.LDT.SelfImprovement

namespace MIPStarRE.LDT.SelfImprovement
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The named bracketed helper-completeness quantity is exactly the
helper-stage `Hhat ⊗ I` mass for the averaged sandwiched family.

This is the Lean form of the equality labelled
`eq:bracketize-the-expression`, after composing the fiberwise reindexing with
the preceding expansion of `Hhat` as the average of the pointwise sandwiched
submeasurements. -/
theorem helperBracketedCompletenessQuantity_eq_mass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    helperBracketedCompletenessQuantity params strategy T =
      subMeasMass strategy.state
        (averagedSandwichedPolynomialSubMeas params strategy T).liftLeft := by
  rw [helper_mass_eq_avg_pointwise_bracketed_sum]
  try rfl
end
end MIPStarRE.LDT.SelfImprovement

namespace MIPStarRE.LDT.SelfImprovement
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The paper-shaped `Hhat`-versus-`Z` comparison assembled from the bracketed
expression, the two Cauchy--Schwarz estimates, and complementary slackness.

The first Cauchy--Schwarz hypothesis moves from the bracketed expression
`E_u Σ_a ⟨ψ, (A^u_a T_[h(u)=a] A^u_a) ⊗ I ψ⟩` to
`helperFirstMovedCompletenessQuantity`.  The second removes the remaining
right-register copy of `A^u_a`, giving `helperLinearizedCompletenessQuantity`.
The latter is then identified with the dual mass by the SDP
complementary-slackness equation. -/
theorem helper_hhat_vs_z_of_bracketed_cauchy_schwarz_and_complementary_slackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hmove_left :
      |helperFirstMovedCompletenessQuantity params strategy T.toSubMeas -
        helperBracketedCompletenessQuantity params strategy T.toSubMeas| ≤
        2 * Real.sqrt delta)
    (hremove_right :
      |helperLinearizedCompletenessQuantity params strategy T.toSubMeas -
        helperFirstMovedCompletenessQuantity params strategy T.toSubMeas| ≤
        Real.sqrt delta)
    (hslack :
      ∀ h : Polynomial params,
        T.toSubMeas.outcome h * averagedPointOperator params strategy h =
          T.toSubMeas.outcome h * Z) :
    ev strategy.state (leftTensor (ι₂ := ι) Z) - 3 * Real.sqrt delta ≤
      subMeasMass strategy.state Hhat.liftLeft := by
  have hbracket_mass :
      helperBracketedCompletenessQuantity params strategy T.toSubMeas =
        subMeasMass strategy.state Hhat.liftLeft := by
    rw [hhelper.averagedConstruction]
    exact helperBracketedCompletenessQuantity_eq_mass params strategy T.toSubMeas
  refine
    helper_hhat_vs_z_of_cauchy_schwarz_and_complementary_slackness
      params strategy eps delta hhelper ?_ hremove_right hslack
  simpa [hbracket_mass] using hmove_left
end
end MIPStarRE.LDT.SelfImprovement

namespace MIPStarRE.LDT.SelfImprovement
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Helper-stage completeness from the paper-shaped Cauchy--Schwarz estimates,
complementary slackness, and input consistency.

Compared with `helper_completeness_of_cauchy_schwarz_input_consistency`, this
version names the expression before the first Cauchy--Schwarz move exactly as
it appears in `eq:bracketize-the-expression`; the equality with the
`Hhat`-mass is supplied internally by
`helperBracketedCompletenessQuantity_eq_mass`. -/
theorem helper_completeness_of_bracketed_cauchy_schwarz_input_consistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : Measurement (Polynomial params) ι)
    (eps delta nu : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hmove_left :
      |helperFirstMovedCompletenessQuantity params strategy T.toSubMeas -
        helperBracketedCompletenessQuantity params strategy T.toSubMeas| ≤
        2 * Real.sqrt delta)
    (hremove_right :
      |helperLinearizedCompletenessQuantity params strategy T.toSubMeas -
        helperFirstMovedCompletenessQuantity params strategy T.toSubMeas| ≤
        Real.sqrt delta)
    (hslack :
      ∀ h : Polynomial params,
        T.toSubMeas.outcome h * averagedPointOperator params strategy h =
          T.toSubMeas.outcome h * Z)
    (hcons : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas) nu) :
    CompletenessAtLeast strategy.state Hhat.liftLeft
      ((1 - nu) - selfImprovementHelperError params eps delta) := by
  refine
    helper_completeness_of_input_consistency params strategy G eps delta nu
      heps hdelta hhelper ?_ hcons
  exact
    helper_hhat_vs_z_of_bracketed_cauchy_schwarz_and_complementary_slackness
      params strategy eps delta hhelper hmove_left hremove_right hslack
end
end MIPStarRE.LDT.SelfImprovement

namespace MIPStarRE.LDT.SelfImprovement
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Helper-stage completeness from point self-consistency, complementary
slackness, and input consistency.

This theorem removes the two external Cauchy--Schwarz hypotheses from
`helper_completeness_of_bracketed_cauchy_schwarz_input_consistency`; both are
proved from the single point-measurement self-consistency hypothesis. -/
theorem helper_completeness_of_self_consistency_complementary_slackness_input_consistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : Measurement (Polynomial params) ι)
    (eps delta nu : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hslack :
      ∀ h : Polynomial params,
        T.toSubMeas.outcome h * averagedPointOperator params strategy h =
          T.toSubMeas.outcome h * Z)
    (hcons : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas) nu) :
    CompletenessAtLeast strategy.state Hhat.liftLeft
      ((1 - nu) - selfImprovementHelperError params eps delta) := by
  refine
    helper_completeness_of_bracketed_cauchy_schwarz_input_consistency
      params strategy G eps delta nu heps hdelta hhelper ?_ ?_ hslack hcons
  · exact helper_first_move_abs_sub_bracketed_le_two_sqrt_delta
      params strategy T.toSubMeas delta hssc
  · exact helper_second_move_abs_sub_first_moved_le_sqrt_delta
      params strategy T.toSubMeas delta hssc
end
end MIPStarRE.LDT.SelfImprovement

namespace MIPStarRE.LDT.SelfImprovement
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Extract the orientation of complementary slackness used by the helper
completeness proof from the strengthened helper conclusion. -/
theorem helper_slackness_eq_of_helper_with_slackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper :
      SelfImprovementHelperConclusionWithSlackness params strategy T Hhat Z eps delta)
    (h : Polynomial params) :
    T.toSubMeas.outcome h * averagedPointOperator params strategy h =
      T.toSubMeas.outcome h * Z :=
  (hhelper.complementarySlackness h).symm
end
end MIPStarRE.LDT.SelfImprovement

namespace MIPStarRE.LDT.SelfImprovement
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Helper-stage completeness from point self-consistency, a helper conclusion
carrying SDP complementary slackness, and input consistency.

This theorem removes the standalone `hslack` hypothesis from
`helper_completeness_of_self_consistency_complementary_slackness_input_consistency`;
the slackness equations are read from
`SelfImprovementHelperConclusionWithSlackness`. -/
theorem helper_completeness_of_self_consistency_helper_slackness_input_consistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : Measurement (Polynomial params) ι)
    (eps delta nu : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper :
      SelfImprovementHelperConclusionWithSlackness params strategy T Hhat Z eps delta)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hcons : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas) nu) :
    CompletenessAtLeast strategy.state Hhat.liftLeft
      ((1 - nu) - selfImprovementHelperError params eps delta) :=
  helper_completeness_of_self_consistency_complementary_slackness_input_consistency
    params strategy G eps delta nu heps hdelta hhelper.toHelperConclusion hssc
    (helper_slackness_eq_of_helper_with_slackness params strategy eps delta hhelper)
    hcons
end
end MIPStarRE.LDT.SelfImprovement

namespace MIPStarRE.LDT.SelfImprovement
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Paper-origin statement for `lem:sdp` with complementary slackness.

Paper origin: `references/ldt-paper/self_improvement.tex` lines 62--88 state
`\label{lem:sdp}` for the primal/dual SDP pair and assert optimal witnesses
`{T_g}`, `Z` with `∑ g, T_g = I` and `T_g Z = T_g A_g`.  Lines 168--190 prove
this by Slater strong duality and complementary slackness after passing through
the canonical SDP form.

The proof transports the formalized canonical optimal-pair output for the
Section 9 SDP back to the paper's abstract notation.  That canonical optimal
pair is obtained from the finite-dimensional strong-duality argument and the
slack-block saturation step in the matrix realization. -/
theorem sdp_statement_with_slackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι) :
    SdpStatementWithSlackness params strategy := by
  exact MatrixSdpStatementWithSlackness.toSdpStatementWithSlackness params strategy
    (matrixSdpPointRealization_statementWithSlackness params strategy)
end
end MIPStarRE.LDT.SelfImprovement

namespace MIPStarRE.LDT.SelfImprovement
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Helper lemma driven by the Section 9 SDP statement with complementary
slackness.

This applies the Section 9 statement `sdp_statement_with_slackness`, which
records the strong-duality conclusion with complementary slackness. -/
lemma self_improvement_helper_with_slackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (nu : Error)
    (G : Measurement (Polynomial params) ι) :
    ∃ T : Measurement (Polynomial params) ι,
      ∃ H : SubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
        SelfImprovementHelperConclusionWithSlackness params strategy T H Z eps delta :=
  self_improvement_helper_with_slackness_of_sdp_statement_with_slackness
    params strategy eps delta gamma
    (sdp_statement_with_slackness (ι := ι) params strategy)
    hgood nu G
end
end MIPStarRE.LDT.SelfImprovement

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPStarRE.LDT.SelfImprovement
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem _root_.solution
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : Measurement (Polynomial params) ι)
    (hcons : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas) nu) :
    ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SelfImprovementConclusion params strategy G H Z eps delta gamma nu := by
  have heps : 0 ≤ eps := eps_nonneg_of_isGood params strategy hgood
  have hdelta : 0 ≤ delta := delta_nonneg_of_isGood params strategy hgood
  have hnu_nonneg : 0 ≤ nu := by
    exact le_trans
      (bipartiteConsError_nonneg strategy.state
        (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas))
      hcons.offDiagonalBound
  by_cases heps_le_one : eps ≤ 1
  · by_cases hdelta_le_one : delta ≤ 1
    · by_cases hd_le_q : (params.d : Error) ≤ (params.q : Error)
      · rcases self_improvement_helper_with_slackness params strategy eps delta gamma
            hgood nu G with
          ⟨T, Hhat, Z, hhelperWithSlackness⟩
        let hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta :=
          hhelperWithSlackness.toHelperConclusion
        have hpointSSC :
            BipartiteSSCRel strategy.state (uniformDistribution (Point params))
              (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta := by
          exact ⟨by
            simpa [SymStrat.selfConsistencyFailureProbability] using
              hgood.selfConsistencyTest⟩
        have haddInUFull : AddInUFullStatement params strategy T eps delta :=
          addInUFullStatement_of_isGood (ι := ι) params strategy eps delta gamma hgood T
        have htransfer :
            |addInULeftQuantity params strategy
                (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
                Hhat
                (pointConsistencyAddInUSelection params) -
              addInURightQuantity params strategy
                (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
                T.toSubMeas
                (pointConsistencyAddInUSelection params)| ≤
              addInUError params eps delta := by
          have htransfer :=
            haddInUFull.selectionDependentTransfer
              (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
              (pointConsistencyAddInUSelection params)
          simpa [hhelper.averagedConstruction] using htransfer
        have hhelperCompleteness :
            CompletenessAtLeast strategy.state Hhat.liftLeft
              ((1 - nu) - selfImprovementHelperError params eps delta) :=
          helper_completeness_of_self_consistency_helper_slackness_input_consistency
            params strategy G eps delta nu heps hdelta hhelperWithSlackness hpointSSC hcons
        have hlocal :
            (∑ g : Polynomial params,
              localVarianceDeviationAtPolynomial params strategy strategy.state
                T.toSubMeas g) ≤
              localVarianceOfPointsError params eps delta :=
          localVarianceDeviation_sum_le_localVarianceOfPointsError
            params strategy eps delta gamma hgood T.toSubMeas
        have hclone :
            |helperDeleteAQuantity params strategy T.toSubMeas -
              helperDeleteAClonedQuantity params strategy T.toSubMeas| ≤
                Real.sqrt (selfImprovementVarianceError params eps delta) :=
          helperDeleteAQuantity_abs_sub_clonedQuantity_le_sqrt
            params strategy eps delta T.toSubMeas hlocal
        have hmove :
            |helperDeleteAClonedQuantity params strategy T.toSubMeas -
              helperMoveOverVQuantity params strategy T.toSubMeas| ≤
                Real.sqrt (2 * delta) :=
          helperDeleteAClonedQuantity_abs_sub_moveOverVQuantity_le_sqrt_two_delta
            params strategy delta T.toSubMeas hpointSSC
        have hslack :
            ∀ h : Polynomial params,
              T.toSubMeas.outcome h * averagedPointOperator params strategy h =
                T.toSubMeas.outcome h * Z :=
          fun h =>
            helper_slackness_eq_of_helper_with_slackness
              params strategy eps delta hhelperWithSlackness h
        have hsscBounds :
            HelperStrongSelfConsistencyBounds params strategy T Hhat eps delta :=
          helper_ssc_bounds_of_scalarTransports_pointTransfer
            params strategy eps delta hhelper hpointSSC hlocal hclone hmove
            hslack htransfer
        have hhelperSSC :
            BipartiteSSCRel strategy.state (uniformDistribution Unit)
              (constSubMeasFamily Hhat)
              (selfImprovementHelperError params eps delta) :=
          helper_strong_self_consistency_of_helper_conclusion
            params strategy eps delta heps hdelta hd_le_q hhelper hsscBounds
        rcases MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalization
            strategy.state strategy.permInvState strategy.isNormalized
            Hhat (selfImprovementHelperError params eps delta) hhelperSSC with
          ⟨H, horth⟩
        have hprojectiveUpperGap :
            ev strategy.state (rightTensor (ι₁ := ι) H.toSubMeas.total) -
              ev strategy.state (rightTensor (ι₁ := ι) Hhat.total) ≤
                2 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta) := by
          let Pconst : IdxProjSubMeas Unit (Polynomial params) (ι × ι) :=
            fun _ => ProjSubMeas.liftLeft H
          have hcomp :
              Preliminaries.CompTransferStmt strategy.state
                (uniformDistribution Unit)
                (constSubMeasFamily Hhat.liftLeft)
                Pconst
                (selfImprovementOrthogonalizationError params eps delta) := by
            apply Preliminaries.completenessTransferProjectiveP
              strategy.state (uniformDistribution Unit) strategy.isNormalized
              (uniformDistribution_weight_sum_le_one Unit)
              (constSubMeasFamily Hhat.liftLeft)
              Pconst
              (selfImprovementOrthogonalizationError params eps delta)
            change SDDRel strategy.state (uniformDistribution Unit)
              (constSubMeasFamily Hhat.liftLeft)
              (constSubMeasFamily H.toSubMeas.liftLeft)
              (orthonormalizationError (selfImprovementHelperError params eps delta))
            exact horth
          have hleft :
              ev strategy.state (leftTensor (ι₂ := ι) Hhat.total) ≥
                ev strategy.state (leftTensor (ι₂ := ι) H.toSubMeas.total) -
                  2 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta) := by
            simpa [idxSubMeasMass, avgOver, uniformDistribution, subMeasMass,
              constSubMeasFamily, Pconst, IdxProjSubMeas.toIdxSubMeas,
              ProjSubMeas.liftLeft, SubMeas.liftLeft, mkLeftPlacedSubMeas_total] using
              hcomp.completenessTransfer
          have hleft' :
              ev strategy.state (leftTensor (ι₂ := ι) H.toSubMeas.total) -
                ev strategy.state (leftTensor (ι₂ := ι) Hhat.total) ≤
                  2 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta) := by
            linarith
          rw [strategy.permInvState.swap_ev H.toSubMeas.total,
            strategy.permInvState.swap_ev Hhat.total] at hleft'
          exact hleft'
        have hhelperUpperGap :
            ev strategy.state (rightTensor (ι₁ := ι) Hhat.total) -
              ev strategy.state (rightTensor (ι₁ := ι) H.toSubMeas.total) ≤
                selfImprovementHelperError params eps delta +
                  2 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta) := by
          have horthIdx :
              SDDRel strategy.state (uniformDistribution Unit)
                (IdxSubMeas.liftLeft (constSubMeasFamily Hhat))
                (IdxSubMeas.liftLeft (constSubMeasFamily H.toSubMeas))
                (selfImprovementOrthogonalizationError params eps delta) := by
            change SDDRel strategy.state (uniformDistribution Unit)
              (constSubMeasFamily Hhat.liftLeft)
              (constSubMeasFamily H.toSubMeas.liftLeft)
              (orthonormalizationError (selfImprovementHelperError params eps delta))
            exact horth
          have hcomp :=
            Preliminaries.completenessTransferSelfConsistentA
              strategy.state strategy.permInvState strategy.isNormalized
              (uniformDistribution Unit)
              (uniformDistribution_weight_sum_le_one Unit)
              (constSubMeasFamily Hhat)
              (constSubMeasFamily H.toSubMeas)
              (selfImprovementHelperError params eps delta)
              (selfImprovementOrthogonalizationError params eps delta)
              hhelperSSC horthIdx
          have hleft :
              ev strategy.state (leftTensor (ι₂ := ι) H.toSubMeas.total) ≥
                ev strategy.state (leftTensor (ι₂ := ι) Hhat.total) -
                  selfImprovementHelperError params eps delta -
                    2 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta) := by
            simpa [idxSubMeasMass, avgOver, uniformDistribution, subMeasMass,
              constSubMeasFamily, IdxSubMeas.liftLeft, SubMeas.liftLeft,
              mkLeftPlacedSubMeas_total] using hcomp
          have hleft' :
              ev strategy.state (leftTensor (ι₂ := ι) Hhat.total) -
                ev strategy.state (leftTensor (ι₂ := ι) H.toSubMeas.total) ≤
                  selfImprovementHelperError params eps delta +
                    2 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta) := by
            linarith
          rw [strategy.permInvState.swap_ev Hhat.total,
            strategy.permInvState.swap_ev H.toSubMeas.total] at hleft'
          exact hleft'
        have hhelperError_nonneg :
            0 ≤ selfImprovementHelperError params eps delta :=
          selfImprovementHelperError_nonneg params eps delta
        have hTotalDiff :
            |ev strategy.state (rightTensor (ι₁ := ι) H.toSubMeas.total) -
              ev strategy.state (rightTensor (ι₁ := ι) Hhat.total)| ≤
                selfImprovementHelperError params eps delta +
                  2 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta) := by
          refine abs_le.mpr ?_
          constructor
          · linarith [hhelperUpperGap]
          · linarith [hprojectiveUpperGap, hhelperError_nonneg]
        have hhelperSSCPoint :
            BipartiteSSCRel strategy.state (uniformDistribution (Point params))
              (fun _ : Point params => Hhat)
              (selfImprovementHelperError params eps delta) :=
          bipartiteSSCRel_uniform_const strategy.state Hhat
            (selfImprovementHelperError params eps delta) hhelperSSC
        have horthPoint :
            SDDRel strategy.state (uniformDistribution (Point params))
              (IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas (fun _ : Point params => H)))
              (IdxSubMeas.liftLeft (fun _ : Point params => Hhat))
              (selfImprovementOrthogonalizationError params eps delta) := by
          change SDDRel strategy.state (uniformDistribution (Point params))
            (fun _ : Point params => H.toSubMeas.liftLeft)
            (fun _ : Point params => Hhat.liftLeft)
            (selfImprovementOrthogonalizationError params eps delta)
          exact sddRel_uniform_const strategy.state H.toSubMeas.liftLeft Hhat.liftLeft
            (selfImprovementOrthogonalizationError params eps delta)
            (MIPStarRE.LDT.Preliminaries.sddRel_symm strategy.state
              (uniformDistribution Unit)
              (constSubMeasFamily Hhat.liftLeft)
              (constSubMeasFamily H.toSubMeas.liftLeft)
              (selfImprovementOrthogonalizationError params eps delta) horth)
        have hdataRev :
            SDDRel strategy.state (uniformDistribution (Point params))
              ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
              ((polynomialEvaluationFamily params Hhat).liftLeft)
              (selfImprovementDataProcessingError params eps delta) := by
          rw [selfImprovementDataProcessingError_eq params eps delta]
          change SDDRel strategy.state (uniformDistribution (Point params))
            (IdxSubMeas.liftLeft
              (fun q : Point params => postprocess H.toSubMeas (fun g => g q)))
            (IdxSubMeas.liftLeft
              (fun q : Point params => postprocess Hhat (fun g => g q)))
            (8 * selfImprovementHelperError params eps delta +
              8 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta))
          exact Preliminaries.selfConsistencyImpliesDataProcessing
            strategy.state strategy.permInvState strategy.isNormalized
            (uniformDistribution (Point params))
            (uniformDistribution_weight_sum_le_one (Point params))
            (fun _ : Point params => Hhat)
            (fun _ : Point params => H)
            (selfImprovementHelperError params eps delta)
            (selfImprovementOrthogonalizationError params eps delta)
            (fun u g => g u)
            hhelperSSCPoint horthPoint
        have hdata :
            SDDRel strategy.state (uniformDistribution (Point params))
              ((polynomialEvaluationFamily params Hhat).liftLeft)
              ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
              (selfImprovementDataProcessingError params eps delta) :=
          MIPStarRE.LDT.Preliminaries.sddRel_symm strategy.state
            (uniformDistribution (Point params))
            ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
            ((polynomialEvaluationFamily params Hhat).liftLeft)
            (selfImprovementDataProcessingError params eps delta) hdataRev
        have hfinal : SelfImprovementFinalFields params strategy H Z eps delta nu :=
          final_fields_of_helper_outputs_of_total_difference
            params strategy eps delta nu
            (selfImprovementHelperError params eps delta +
              2 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta))
            heps heps_le_one hdelta hdelta_le_one hd_le_q
            hhelper hhelperCompleteness hhelperSSC hpointSSC hslack htransfer
            horth hdata hTotalDiff
            (by
              have hbase :=
                final_fields_point_consistency_total_difference_error_le_selfImprovementError
                  params eps delta heps heps_le_one hdelta hdelta_le_one hd_le_q
              nlinarith)
        exact ⟨H, Z,
          { completeness := hfinal.completeness
            pointConsistency := hfinal.pointConsistency
            selfCloseness := hfinal.selfCloseness
            positiveSemidefiniteWitness := hhelper.sdpWitness.dualPositive
            dualDominatesAveragedPoint := hhelper.sdpWitness.dualFeasible
            projectiveResidualBound := hfinal.projectiveResidualBound }⟩
      · have hdq_ge_one : 1 ≤ ((params.d : Error) / (params.q : Error)) := by
          exact (one_le_div₀ params.q_cast_pos).2 (le_of_lt (lt_of_not_ge hd_le_q))
        have hdq_pow_ge_one :
            1 ≤ Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (32 : Error)) := by
          have hpow :=
            Real.rpow_le_rpow (show (0 : Error) ≤ 1 by positivity) hdq_ge_one
              (by positivity : 0 ≤ (1 / (32 : Error)))
          simpa using hpow
        have hsum_ge_one :
            1 ≤ finalStagePowerSum params eps delta (1 / (32 : Error)) := by
          unfold finalStagePowerSum
          have heps_pow_nonneg : 0 ≤ Real.rpow eps (1 / (32 : Error)) :=
            Real.rpow_nonneg heps _
          have hdelta_pow_nonneg : 0 ≤ Real.rpow delta (1 / (32 : Error)) :=
            Real.rpow_nonneg hdelta _
          nlinarith
        have herror_ge_one : 1 ≤ selfImprovementError params eps delta := by
          rw [selfImprovementError_eq_finalStagePowerSum]
          nlinarith [one_le_m_cast params, hsum_ge_one]
        exact selfImprovement_of_error_ge_one
          params strategy eps delta gamma nu hgood G herror_ge_one hnu_nonneg
    · have hdelta_ge_one : 1 ≤ delta := le_of_lt (lt_of_not_ge hdelta_le_one)
      have hdelta_pow_ge_one : 1 ≤ Real.rpow delta (1 / (32 : Error)) := by
        have hpow :=
          Real.rpow_le_rpow (show (0 : Error) ≤ 1 by positivity) hdelta_ge_one
            (by positivity : 0 ≤ (1 / (32 : Error)))
        simpa using hpow
      have hsum_ge_one : 1 ≤ finalStagePowerSum params eps delta (1 / (32 : Error)) := by
        unfold finalStagePowerSum
        have heps_pow_nonneg : 0 ≤ Real.rpow eps (1 / (32 : Error)) :=
          Real.rpow_nonneg heps _
        have hdq_pow_nonneg :
            0 ≤ Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (32 : Error)) :=
          Real.rpow_nonneg (d_q_ratio_nonneg params) _
        nlinarith
      have herror_ge_one : 1 ≤ selfImprovementError params eps delta := by
        rw [selfImprovementError_eq_finalStagePowerSum]
        nlinarith [one_le_m_cast params, hsum_ge_one]
      exact selfImprovement_of_error_ge_one
        params strategy eps delta gamma nu hgood G herror_ge_one hnu_nonneg
  · have heps_ge_one : 1 ≤ eps := le_of_lt (lt_of_not_ge heps_le_one)
    have heps_pow_ge_one : 1 ≤ Real.rpow eps (1 / (32 : Error)) := by
      have hpow :=
        Real.rpow_le_rpow (show (0 : Error) ≤ 1 by positivity) heps_ge_one
          (by positivity : 0 ≤ (1 / (32 : Error)))
      simpa using hpow
    have hsum_ge_one : 1 ≤ finalStagePowerSum params eps delta (1 / (32 : Error)) := by
      unfold finalStagePowerSum
      have hdelta_pow_nonneg : 0 ≤ Real.rpow delta (1 / (32 : Error)) :=
        Real.rpow_nonneg hdelta _
      have hdq_pow_nonneg :
          0 ≤ Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (32 : Error)) := by
        exact Real.rpow_nonneg (d_q_ratio_nonneg params) _
      nlinarith
    have herror_ge_one : 1 ≤ selfImprovementError params eps delta := by
      rw [selfImprovementError_eq_finalStagePowerSum]
      nlinarith [one_le_m_cast params, hsum_ge_one]
    exact selfImprovement_of_error_ge_one
      params strategy eps delta gamma nu hgood G herror_ge_one hnu_nonneg
end MIPStarRE.LDT.SelfImprovement
