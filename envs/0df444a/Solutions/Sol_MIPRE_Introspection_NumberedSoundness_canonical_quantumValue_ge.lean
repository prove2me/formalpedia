-- Prove2me | solution 1 for MIPRE.Introspection.NumberedSoundness.canonical_quantumValue_ge
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T11:09:11.349778+00:00
-- url     : https://prove2.me/submissions/fab78c75-5858-4d62-8cb4-b424d317bce3

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Introspection/NumberedSoundness.lean (solution of MIPRE.Introspection.NumberedSoundness.canonical_quantumValue_ge);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Lean.Elab.Tactic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
import Mathlib.Algebra.Algebra.Subalgebra.Basic
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
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.IsField
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Opposite
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Center
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Group.Invertible.Basic
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
import Mathlib.Algebra.GroupWithZero.Commute
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.GroupWithZero.Invertible
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Algebra.Module.Torsion.Pi
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.NoZeroSMulDivisors.Basic
import Mathlib.Algebra.NoZeroSMulDivisors.Defs
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Indicator
import Mathlib.Algebra.Notation.Pi.Basic
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Notation.Prod
import Mathlib.Algebra.Opposites
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
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
import Mathlib.Algebra.Order.Module.PositiveLinearMap
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.NatCast
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
import Mathlib.Algebra.Order.Nonneg.Basic
import Mathlib.Algebra.Order.Nonneg.Module
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Ring.Pi
import Mathlib.Algebra.Ring.Subring.Defs
import Mathlib.Algebra.Ring.Subsemiring.Defs
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.Unitary
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.Convex.Cone.Closure
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.InnerProductSpace.Trace
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
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.Real.Spectrum
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Countable.Defs
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENat.Defs
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finite.Sum
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
import Mathlib.Data.Finset.Lattice.Lemmas
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Embedding
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.FunLike.IsApply
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Rotate
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
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Commute
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Size
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
import Mathlib.Data.Subtype
import Mathlib.Data.ULift
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.Separable
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.CharP
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Basic
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Embedding.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Function.Defs
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.IsEmpty.Basic
import Mathlib.Logic.IsEmpty.Defs
import Mathlib.Logic.Nonempty
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Logic.Pairwise
import Mathlib.Logic.Unique
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.MeasureTheory.OuterMeasure.Defs
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Order.Basic
import Mathlib.Order.BooleanAlgebra.Defs
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Defs
import Mathlib.Order.ConditionallyCompletePartialOrder.Defs
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
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Lattice
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.MinMax
import Mathlib.Order.Monotone.Defs
import Mathlib.Order.Nat
import Mathlib.Order.Notation
import Mathlib.Order.RelClasses
import Mathlib.Order.SetNotation
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Trace.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Attr.Register
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.LinearCombination.Lemmas
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
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
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.Star
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
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
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
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.Defs
import Mathlib.Topology.UniformSpace.Real
import Mathlib.Topology.UnitInterval
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_SAT_Succinct
import Definitions.Def_MIPRE_Foundations_SAT_Decoupled
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_SAT_Pcp
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_Pasting
import Definitions.Def_MIPRE_Foundations_POVMMix
import Definitions.Def_MIPRE_Foundations_POVMMix_B
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_CL_Downsize
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryConstants
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPower
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryTrace
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotient
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNormalize
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDivision
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryLinear
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryElimination
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasisProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixInverse
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDualize
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySquareRoot
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculant
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculantProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculantProg_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGroupAlgebra
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGroupAlgebra_B
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteReducedComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_IdempotentSplit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponents_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponentsProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponentsProg_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFrobenius
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFactors
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGCD
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryFactorization
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCyclotomicSeed
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySubstitution
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNonresidueLoop
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNonresidueCorrectness
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientOrbit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryTraceBits
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitDescent
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientTranslation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCoprimeDegree
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComposedSumPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComposedSumProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOddPrimeProgram
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPrimePowerTrace
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreier
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierTower
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierLoop
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryDegreeArithmetic
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryPrimality
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryPrimePower
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDegreeFactors
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDegreeDecomposition
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPrimePowerDispatch
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryIrreducibleAssembly
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryIrreducibleConstructor
import Definitions.Def_MIPRE_Foundations_LowDegree_Shoup
import Definitions.Def_MIPRE_Foundations_LowDegree_ShoupCoefficients
import Definitions.Def_MIPRE_Foundations_SAT_QuotientField
import Definitions.Def_MIPRE_Foundations_SAT_FieldTrace
import Definitions.Def_MIPRE_Foundations_SAT_FieldTrace_B
import Definitions.Def_MIPRE_Foundations_SAT_FieldCoordinates
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Introspection_SeedSelectorProg
import Definitions.Def_MIPRE_Foundations_SAT_TraceGram
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDual
import Definitions.Def_MIPRE_Foundations_LowDegree_NormalBasis
import Definitions.Def_MIPRE_Foundations_SAT_NormalGram
import Definitions.Def_MIPRE_Foundations_SAT_FrobeniusAction
import Definitions.Def_MIPRE_Foundations_SAT_NormalElement
import Definitions.Def_MIPRE_Foundations_SAT_FrobeniusMatrix
import Definitions.Def_MIPRE_Foundations_SAT_FrobeniusActionProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryFold
import Definitions.Def_MIPRE_Foundations_SAT_NormalElementProg
import Definitions.Def_MIPRE_Foundations_SAT_NormalElementProg_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryInverse
import Definitions.Def_MIPRE_Foundations_Introspection_LineRepresentativeProg
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Introspection_SeededLineProg
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgParse
import Definitions.Def_MIPRE_Foundations_SAT_BasisTransport
import Definitions.Def_MIPRE_Foundations_SAT_EffectiveSelfDual
import Definitions.Def_MIPRE_Foundations_SAT_EffectiveNormalBasis
import Definitions.Def_MIPRE_Foundations_Introspection_BasisProg
import Definitions.Def_MIPRE_Foundations_Introspection_BinaryBlockProg
import Definitions.Def_MIPRE_Foundations_Introspection_BinaryBlockProg_B
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry
import Definitions.Def_MIPRE_Foundations_CL_DetypingQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCall
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgRoute
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Introspection_PauliStageProg
import Definitions.Def_MIPRE_Foundations_Introspection_PauliStageProg_B
import Definitions.Def_MIPRE_Foundations_Cost_SizeProgram
import Definitions.Def_MIPRE_Foundations_SAT_PcpFormat
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Halting_Arith_B
import Definitions.Def_MIPRE_Foundations_Repeat_Prims
import Definitions.Def_MIPRE_Foundations_CL_Repeat
import Definitions.Def_MIPRE_Foundations_Repeat_Bits
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Pipeline_Budget
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgSampler
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCost
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderRoute
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderProg
import Definitions.Def_MIPRE_Foundations_CL_DetypingClock
import Definitions.Def_MIPRE_Foundations_LowDegree_LineRestrict
import Definitions.Def_MIPRE_Background_LIDT_Coefficients
import Definitions.Def_MIPRE_Background_LIDT_Coefficients_B
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Seeds
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Reparam
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Parameters
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Strategy
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Weights
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_MIPRE_Background_LIDT_Bridge_Field
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_MIPRE_Background_LIDT_Bridge_Polynomial
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
import Definitions.Def_MIPRE_Background_LIDT_Bridge_Measurement
import Definitions.Def_MIPRE_Background_LIDT_Bridge_Strategy
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyBiProj_DirectSum
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyBiProj_Measurements
import Definitions.Def_MIPRE_Background_LIDT_Bridge_Value
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_Definitions
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_EnvelopeBounds
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_MainTheorem_SourceScalars
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LinePolynomialEmbedding
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MainInductionStep_Statements
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Defs_Normalization
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_CommutativityPoints_Approximation
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_EvaluatedSliceBounds_PhaseOneThree
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_EvaluatedSliceCommutation_Averages
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_EvaluationSpecialization
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_Pullback
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_PolynomialAgreement
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Averages
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Y
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Normalization
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Bridges_Closeness
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Bridges_QSDD
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_ZeroBounds
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Main_Auxiliary_HEvalTransport
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Main_Auxiliary_ScalarMarginalization
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_CommutativityPoints_SharedHelpers_SharedLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_CommutativityPoints_BridgeTheorems_DropBridges
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_RawSecond
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_PaperChainPhaseFive
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_First
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_ProcessedG_PhaseTwo
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_ProcessedG_MainChain
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Sandwich_Switcheroo
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Sandwich_GHatSandwich
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Sandwich_PastedFamilies
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Statements
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_SwitcherooSetup_Centers
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_SwitcherooSetup_Terms
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_SwitcherooContraction_Split
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_SwitcherooContraction_ScalarTerms
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_SwitcherooCompletion
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_CommutingWithG_Complete
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_GHatFacts
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_Setup_Definitions
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_Setup_StepLemmas_Split
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Base
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Lifting
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Chain
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_FlatChain
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_BackChain
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_TruncatedSums
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_Weights
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_Scalar
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_Core_BernoulliTail
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_Core_FactBundles
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_MoveLemmas_Basic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_AdjacentStages_StageA0M1
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_AdjacentStages_Chain_HalfSandwich
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_AdjacentStages_Chain_FinalMove
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_PaperBounds
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_MatrixChernoff
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_EndpointEquivs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Core_LdGbcon
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_Endpoint
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_PrefixMoved
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_CSSetup
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_BadLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_BadMass
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_HBConsistency
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_HAConsistency
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_DegreeZero
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_OverAllOutcomes_ErrorAndMass
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_OverAllOutcomes_NonglobalDecomposition
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_OverAllOutcomes_Final
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_Final
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_SelfImprovementAssembly_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_InductionParameterBounds_MainError
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_SelfImprovementAssembly_AnswerSlice
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_RestrictedProbabilities_Base
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_RestrictedProbabilities_Axis
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_RestrictedProbabilities_Diagonal
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_RestrictedProbabilities_AnswerValued
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_StageDataConstructors
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_AvgSliceErrors_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_CommutativityPoints_AnswerTheorems
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_InductionParameterBounds_SelfImprovement
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_PastingAssembly_Successor
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_SchwartzZippelStep
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonProjective
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyBiProjRoleAverage_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyBiProjUnsymmetrization
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_MainTheorem_SourceRoleRegister_Completion
import Definitions.Def_MIPRE_Background_LIDT_Bridge_Main
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Reduction
import Definitions.Def_MIPRE_Background_LIDT_BlockPoly
import Definitions.Def_MIPRE_Foundations_StrategyDilation
import Definitions.Def_MIPRE_Foundations_Pipeline_Introspection
import Definitions.Def_MIPRE_Foundations_Halting_PolyBounded
import Definitions.Def_MIPRE_Foundations_Introspection_ClockArithmetic
import Definitions.Def_MIPRE_Foundations_Introspection_ParserBits
import Definitions.Def_MIPRE_Foundations_Introspection_ParserAnswers
import Definitions.Def_MIPRE_Foundations_Introspection_DynamicParserSlice
import Definitions.Def_MIPRE_Foundations_Introspection_DynamicParser
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerParams
import Definitions.Def_MIPRE_Foundations_Introspection_PauliSamplerParams
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable
import Definitions.Def_MIPRE_LCS_Strategy_ObservableToProjector
import Definitions.Def_MIPRE_LCS_NonlocalGame
import Definitions.Def_MIPRE_LCS_Pauli
import Definitions.Def_MIPRE_LCS_MagicSquare_Strategy
import Definitions.Def_MIPRE_LCS_MagicSquare_Game
import Definitions.Def_MIPRE_Background_QLD_Game
import Definitions.Def_MIPRE_Background_QLD_CLPresentation
import Definitions.Def_MIPRE_Background_QLD_CLBinary
import Definitions.Def_MIPRE_Background_QLD_CLExplicitSeed
import Definitions.Def_MIPRE_Background_QLD_PauliStagePrograms
import Definitions.Def_MIPRE_Background_QLD_TypeEncoding
import Definitions.Def_MIPRE_Foundations_Introspection_FieldAnswerParserProg
import Definitions.Def_MIPRE_Background_QLD_PauliAnswerPrograms
import Definitions.Def_MIPRE_Foundations_Introspection_FieldIndicatorProg
import Definitions.Def_MIPRE_Foundations_Introspection_FieldTableProg
import Definitions.Def_MIPRE_Background_QLD_PauliAnswerCoding
import Definitions.Def_MIPRE_Background_QLD_BinaryBlocks
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Foundations_WeylBinary
import Definitions.Def_MIPRE_Background_QLD_PauliFullAnswerPrograms
import Definitions.Def_MIPRE_Foundations_Introspection_Types
import Definitions.Def_MIPRE_Foundations_Introspection_SamplingPrefix
import Definitions.Def_MIPRE_Foundations_Introspection_TwirlDistance
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_CommutatorParseval
import Definitions.Def_MIPRE_Foundations_Introspection_BlockTwirl
import Definitions.Def_MIPRE_Foundations_Introspection_BlockPOVM
import Definitions.Def_MIPRE_Foundations_Introspection_EPR
import Definitions.Def_MIPRE_Foundations_Introspection_BlockRetention
import Definitions.Def_MIPRE_Foundations_Introspection_PauliMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterTransport
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterEPR
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterCoordinates
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryChecks
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPredicate
import Definitions.Def_MIPRE_Foundations_Introspection_Readout
import Definitions.Def_MIPRE_Foundations_Introspection_FinalExtraction
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph
import Definitions.Def_MIPRE_Foundations_Introspection_HonestCore
import Definitions.Def_MIPRE_Foundations_Introspection_SourcePadding
import Definitions.Def_MIPRE_Foundations_Introspection_ConditionalNormalizer
import Definitions.Def_MIPRE_Foundations_Introspection_HonestFirstHide
import Definitions.Def_MIPRE_Foundations_Introspection_HonestAdaptive
import Definitions.Def_MIPRE_Foundations_Introspection_HonestRead
import Definitions.Def_MIPRE_Foundations_Introspection_HonestXCoordinates
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingStep
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHiding
import Definitions.Def_MIPRE_Foundations_Introspection_HonestLabelSupport
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPresentation
import Definitions.Def_MIPRE_Foundations_Introspection_TypedEstimates
import Definitions.Def_MIPRE_Foundations_Introspection_HidingRigidity
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingChecks
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingAcceptance
import Definitions.Def_MIPRE_Foundations_Introspection_HidingMaps
import Definitions.Def_MIPRE_Foundations_Introspection_ConditionalNormalizerIdeal
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixFactor
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPrefixChain
import Definitions.Def_MIPRE_Foundations_Introspection_ReadChainMaps
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveResidual
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryCanonicalProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDualProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDualKernel
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDualDecode
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryQuotientChecks
import Definitions.Def_MIPRE_Foundations_Introspection_PrefixGuard
import Definitions.Def_MIPRE_Foundations_Introspection_HonestMagicSquare
import Definitions.Def_MIPRE_Background_Introspection_HonestPauliObservables
import Definitions.Def_MIPRE_Background_Introspection_HonestPauliMeasurements
import Definitions.Def_MIPRE_Foundations_Introspection_HonestCoreGame
import Definitions.Def_MIPRE_Foundations_Introspection_HonestReading
import Definitions.Def_MIPRE_Foundations_Introspection_HonestParsed
import Definitions.Def_MIPRE_Foundations_Introspection_HonestParsedHiding
import Definitions.Def_MIPRE_Foundations_Introspection_HonestCompleteAux
import Definitions.Def_MIPRE_Foundations_Introspection_HonestPauliRegister
import Definitions.Def_MIPRE_Foundations_Introspection_HonestSampling
import Definitions.Def_MIPRE_Foundations_Introspection_HonestPauliEdges
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Value
import Definitions.Def_MIPRE_Background_Introspection_HonestPauliEdges
import Definitions.Def_MIPRE_Background_Introspection_HonestPauliGame
import Definitions.Def_MIPRE_Background_Introspection_BinaryMeasurements
import Definitions.Def_MIPRE_Background_Introspection_BinaryAnchors
import Definitions.Def_MIPRE_Foundations_Introspection_PauliRestriction
import Definitions.Def_MIPRE_Background_QLD_CLTransport
import Definitions.Def_MIPRE_Background_Introspection_PauliRestriction
import Definitions.Def_MIPRE_Foundations_Swap
import Definitions.Def_MIPRE_Foundations_Introspection_ValueStability
import Definitions.Def_MIPRE_Foundations_Introspection_IsometricStrategy
import Definitions.Def_MIPRE_Foundations_Introspection_PrefixLaw
import Definitions.Def_MIPRE_Foundations_Introspection_PrefixConditioning
import Definitions.Def_MIPRE_Foundations_Introspection_AmbientMixing
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixMixing
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveInitialInvariant
import Definitions.Def_MIPRE_Foundations_Introspection_AnswerRefinement
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveZFactor
import Definitions.Def_MIPRE_Foundations_Introspection_PauliAuxEstimates
import Definitions.Def_MIPRE_Foundations_Introspection_SamplingRegister
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixAdvance
import Definitions.Def_MIPRE_Foundations_Introspection_HidingInductionDilation
import Definitions.Def_MIPRE_Foundations_Introspection_StrategyReplacement
import Definitions.Def_MIPRE_Foundations_Introspection_StrategyReplacementRegister
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveDilationTransport
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixReplacement
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveAnswerRefinement
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveAnswerDecode
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveNextFactor
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveNextInvariant
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveNextStrategy
import Definitions.Def_MIPRE_Foundations_Introspection_HidingInduction
import Definitions.Def_MIPRE_Foundations_Introspection_HidingBaseOperators
import Definitions.Def_MIPRE_Foundations_Introspection_ProductStageZTests
import Definitions.Def_MIPRE_Foundations_Introspection_IntrospectCanonicalization
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveDecodedInvariant
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveInductionInvariant
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixMarginal
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveAnswerMarginal
import Definitions.Def_MIPRE_Foundations_Introspection_ReadRigidity
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveDualMarginal
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveXSplit
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveDualFactor
import Definitions.Def_MIPRE_Foundations_Introspection_ProductStageReadTests
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveXTest
import Definitions.Def_MIPRE_Foundations_Introspection_ErrorBounds
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveStageBudget
import Definitions.Def_MIPRE_Foundations_Introspection_RegisteredExtensionErrors
import Definitions.Def_MIPRE_Foundations_Introspection_HidingNormalizerPrefix
import Definitions.Def_MIPRE_Foundations_Introspection_HidingRigidityOrientation
import Definitions.Def_MIPRE_Foundations_Introspection_HidingRigidityIteration
import Definitions.Def_MIPRE_Foundations_Introspection_HidingRigidityGame
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveInductionStep
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveIterationBudget
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveInductionIteration
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePlayerSwap
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveBobIteration
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveTwoSidedIteration
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePowerBudget
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveTerminalInvariant
import Definitions.Def_MIPRE_Foundations_Introspection_TerminalOptionExtraction
import Definitions.Def_MIPRE_Foundations_Introspection_PrimitiveSoundness
import Definitions.Def_MIPRE_Foundations_Introspection_ExtractedStateSoundness
import Definitions.Def_MIPRE_Foundations_Introspection_ValidPauliSoundness
import Definitions.Def_MIPRE_Background_Introspection_RestrictedSoundness
import Definitions.Def_MIPRE_Background_QLD_CLExplicitTransport
import Definitions.Def_MIPRE_Foundations_GameTransportProjection
import Definitions.Def_MIPRE_Background_Introspection_ExplicitGame
import Definitions.Def_MIPRE_Foundations_Introspection_SourcePaddingValue
import Definitions.Def_MIPRE_Background_Introspection_RestrictedProfileSoundness
import Definitions.Def_MIPRE_Background_Introspection_BinaryExtraction
import Definitions.Def_MIPRE_Background_Introspection_BinarySampled
import Definitions.Def_MIPRE_Background_Introspection_BinaryGame
import Definitions.Def_MIPRE_Foundations_Introspection_TypedQuotientPredicate
import Definitions.Def_MIPRE_Foundations_GameTransportByQuestion
import Definitions.Def_MIPRE_Foundations_Introspection_TypedQuotientGame
import Definitions.Def_MIPRE_Background_Introspection_BinaryQuotientComplete
import Definitions.Def_MIPRE_Foundations_Introspection_SourceReindex
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryQuotientReindex
import Definitions.Def_MIPRE_Foundations_Introspection_PrefixGuardGame
import Definitions.Def_MIPRE_Foundations_Introspection_TypedQuotientReindex
import Definitions.Def_MIPRE_Background_Introspection_NumberedComplete
import Definitions.Def_MIPRE_Foundations_Introspection_PauliErrorParameters
import Definitions.Def_MIPRE_Background_QLD_Win
import Definitions.Def_MIPRE_Background_QLD_Anticomm
import Definitions.Def_MIPRE_Background_QLD_WinMS
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_Positivity
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_PhiNorm
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_IsometryData
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_Assembly
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_FinDim_JointDiag
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_FinDim_Blocks
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_FinDim_Main
import Definitions.Def_MIPRE_Background_QLD_Ortho
import Definitions.Def_MIPRE_Background_QLD_Consistency
import Definitions.Def_MIPRE_Background_QLD_Commutation
import Definitions.Def_MIPRE_Background_QLD_Expanded
import Definitions.Def_MIPRE_Background_QLD_Swap
import Definitions.Def_MIPRE_Background_QLD_Combined
import Definitions.Def_MIPRE_Background_QLD_Lines
import Definitions.Def_MIPRE_Foundations_Blocks
import Definitions.Def_MIPRE_Background_QLD_Padded
import Definitions.Def_MIPRE_Background_QLD_Product
import Definitions.Def_MIPRE_Background_QLD_Combine
import Definitions.Def_MIPRE_Background_QLD_Legalize
import Definitions.Def_MIPRE_Background_QLD_PaddedLines
import Definitions.Def_MIPRE_Background_QLD_PaddedStrategy
import Definitions.Def_MIPRE_Background_QLD_Dummy
import Definitions.Def_MIPRE_Background_QLD_Products
import Definitions.Def_MIPRE_Background_QLD_Linear
import Definitions.Def_MIPRE_Background_QLD_Separate
import Definitions.Def_MIPRE_Background_QLD_Simul
import Definitions.Def_MIPRE_Background_QLD_Complete
import Definitions.Def_MIPRE_Background_QLD_PauliBasis
import Definitions.Def_MIPRE_Background_QLD_Multilinear
import Definitions.Def_MIPRE_Background_QLD_ExactPauli
import Definitions.Def_MIPRE_Background_QLD_SwapUnitary
import Definitions.Def_MIPRE_Background_QLD_MTilde
import Definitions.Def_MIPRE_Background_QLD_Pulling
import Definitions.Def_MIPRE_Background_QLD_SwapMeasure
import Definitions.Def_MIPRE_Background_QLD_PaddedValue
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Registers
import Definitions.Def_MIPRE_Background_QLD_PaddedLIDT
import Definitions.Def_MIPRE_Background_QLD_ChainProbe
import Definitions.Def_MIPRE_Background_QLD_TwoPairs
import Definitions.Def_MIPRE_Background_QLD_Mirror
import Definitions.Def_MIPRE_Background_QLD_MirrorExists
import Definitions.Def_MIPRE_Background_QLD_SwapState
import Definitions.Def_MIPRE_Background_QLD_Chain
import Definitions.Def_MIPRE_Background_QLD_ChainAssembly
import Definitions.Def_MIPRE_Background_QLD_SelfCons
import Definitions.Def_MIPRE_Background_QLD_SwapItemOne
import Definitions.Def_MIPRE_Background_QLD_PhysEmbed
import Definitions.Def_MIPRE_Background_QLD_ErrorShape
import Definitions.Def_MIPRE_Background_QLD_SwapItemTwo
import Definitions.Def_MIPRE_Background_QLD_QLDError
import Definitions.Def_MIPRE_Background_QLD_RegisterForm
import Definitions.Def_MIPRE_Background_Introspection_QLDExtractionAdapter
import Definitions.Def_MIPRE_Background_Introspection_NumberedSoundness
import Theorems.Thm_MIPRE_CL_CLFun_eval_reindex
import Theorems.Thm_MIPRE_CL_CLFun_factorOfPrefix_reindex
import Theorems.Thm_MIPRE_Introspection_AuxiliaryQuotient_check_sound
import Theorems.Thm_MIPRE_Introspection_AuxiliaryQuotient_stageDual_reindex_eq_iff
import Theorems.Thm_MIPRE_Introspection_ExplicitGame_game_D
import Theorems.Thm_MIPRE_Introspection_PauliErrorParameters_qldError_le_profile
import Theorems.Thm_MIPRE_Introspection_PauliRestriction_binaryStrategy_failure_le
import Theorems.Thm_MIPRE_Introspection_RestrictedSoundness_qldExponent_pos
import Theorems.Thm_MIPRE_Introspection_RestrictedSoundness_quantumValue_ge_of_extraction
import Theorems.Thm_MIPRE_Introspection_TypeGraph_edges_nonempty
import Theorems.Thm_MIPRE_Introspection_errorProfile_of_restricted_bound
import Theorems.Thm_MIPRE_QLD_PauliCL_ExplicitSeed_binaryOutputPermutation_presentation
import Theorems.Thm_MIPRE_QLD_PauliCL_pullbackStrategy_value
import Theorems.Thm_MIPRE_TensorProductStrategy_value_le_mergeAnswersByQuestion
import Theorems.Thm_MIPRE_quantumValue_eq_of_equiv

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.CL.CLFun
section
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {ℓ : ℕ}
theorem ExactlyOn.supportedOn {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.ExactlyOn T) :
    P.SupportedOn T := by
  induction P generalizing T with
  | zero => trivial
  | cons S L₁ next ih => exact ⟨hP.1, fun v => ih v (hP.2 v)⟩
end
end MIPRE.CL.CLFun

namespace MIPRE.TensorProductStrategy
section
open Matrix Kronecker
open scoped ComplexOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {G : Game X Y A B}
/-- Accepting more answer tuples raises the value of a strategy. -/
theorem value_copy_le (S : TensorProductStrategy G) (G' : Game X Y A B)
    (hμ : ∀ x y, G'.μ x y = G.μ x y)
    (hD : ∀ x y a b, G.D x y a b = true → G'.D x y a b = true) :
    S.value ≤ (S.copy G').value := by
  unfold value
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
    Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  rw [hμ]
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (G.μ_nonneg x y))
    (S.re_dotProduct_nonneg x y a b)
  cases h : G.D x y a b with
  | false => by_cases h' : G'.D x y a b = true <;> simp [h']
  | true => rw [hD x y a b h]
end
end MIPRE.TensorProductStrategy

namespace MIPRE.TensorProductStrategy
section
open Matrix Kronecker
open scoped ComplexOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {G : Game X Y A B}
/-- Relabeling along equivalences with matching distribution and decision predicate
preserves the value. -/
theorem value_relabel {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
    (S : TensorProductStrategy G) (G' : Game X' Y' A' B') (eX : X' ≃ X) (eY : Y' ≃ Y)
    (eA : A' ≃ A) (eB : B' ≃ B)
    (hμ : ∀ x' y', G'.μ x' y' = G.μ (eX x') (eY y'))
    (hD : ∀ x' y' a' b', G'.D x' y' a' b' = G.D (eX x') (eY y') (eA a') (eB b')) :
    (S.relabel G' eX eY eA eB).value = S.value := by
  unfold value
  show (∑ x', ∑ y', ∑ a', ∑ b', G'.μ x' y' * (if G'.D x' y' a' b' then 1 else 0) *
      (star S.ψ ⬝ᵥ ((S.PA.M (eX x') (eA a') ⊗ₖ S.PB.M (eY y') (eB b')) *ᵥ S.ψ)).re) =
    ∑ x, ∑ y, ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) *
      (star S.ψ ⬝ᵥ ((S.PA.M x a ⊗ₖ S.PB.M y b) *ᵥ S.ψ)).re
  symm
  refine Fintype.sum_equiv eX.symm _ _ fun x => Fintype.sum_equiv eY.symm _ _ fun y =>
    Fintype.sum_equiv eA.symm _ _ fun a => Fintype.sum_equiv eB.symm _ _ fun b => ?_
  rw [hμ, hD, eX.apply_symm_apply, eY.apply_symm_apply, eA.apply_symm_apply,
    eB.apply_symm_apply]
end
end MIPRE.TensorProductStrategy

namespace MIPRE.CL
section
variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {ι ι' : Type*} {κ : Type*} [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]
variable [DecidableEq ι']
theorem map_sdiff' (e : ι ≃ ι') (S T : Finset ι) :
    T.map e.toEmbedding \ S.map e.toEmbedding = (T \ S).map e.toEmbedding := by
  ext i; simp [Finset.mem_map_equiv]
end
end MIPRE.CL

namespace MIPRE.CL.CLFun
section
variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {ι ι' : Type*} {κ : Type*} [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]
variable [DecidableEq ι']
variable {ℓ : ℕ}
theorem SupportedOn.reindex (e : ι ≃ ι') {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.SupportedOn T) :
    (P.reindex e).SupportedOn (T.map e.toEmbedding) := by
  induction P generalizing T with
  | zero => trivial
  | cons S L₁ next ih =>
    obtain ⟨hS, hnext⟩ := hP
    refine ⟨Finset.map_subset_map.mpr hS, fun v => ?_⟩
    rw [map_sdiff']
    exact ih _ (hnext _)
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {ι ι' : Type*} {κ : Type*} [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]
variable [DecidableEq ι']
variable {ℓ : ℕ}
theorem ExactlyOn.reindex (e : ι ≃ ι') {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.ExactlyOn T) :
    (P.reindex e).ExactlyOn (T.map e.toEmbedding) := by
  induction P generalizing T with
  | zero =>
    have hT : T = ∅ := hP
    show T.map e.toEmbedding = ∅
    rw [hT, Finset.map_empty]
  | cons S L₁ next ih =>
    obtain ⟨hS, hnext⟩ := hP
    refine ⟨Finset.map_subset_map.mpr hS, fun v => ?_⟩
    rw [map_sdiff']
    exact ih _ (hnext _)
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {ι ι' : Type*} {κ : Type*} [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]
variable [Fintype ι]
variable [DecidableEq ι'] [Fintype ι']
variable {ℓ : ℕ}
theorem eval_reindex' (e : ι ≃ ι') (P : CLFun F ι ℓ) (y : ι' → F) :
    (P.reindex e).eval y = reindexEquiv e (P.eval ((reindexEquiv e).symm y)) := by
  conv_lhs => rw [← (reindexEquiv e).apply_symm_apply y]
  rw [eval_reindex]
end
end MIPRE.CL.CLFun

namespace MIPRE.Introspection.PauliSamplerParameters
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program SourceCompiler
theorem registerPower_le (c lam n : ℕ) :
    registerPower c lam n ≤ c * canonicalLog lam n + 1 := by
  apply Nat.lt_size.mp
  have h := Nat.size_pos.mpr (show 0 < c * canonicalLog lam n + 1 by omega)
  omega
end
end MIPRE.Introspection.PauliSamplerParameters

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {V A PA H K : Type*} [Fintype V] [Fintype A] [Fintype PA] [DecidableEq PA]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
theorem completePauliPOVM_mats (a₀ a : PA) (M : POVM (ParsedAnswer V A PA) H) :
    ((completePauliPOVM a₀ M).mats a).val =
      ∑ b ∈ univ.filter (fun b => completePauliAnswer a₀ b = a), (M.mats b).val :=
  POVM.map_mats _ _ _
end
end MIPRE.Introspection

namespace MIPRE.QLD.PauliCL
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
theorem canonicalVector_pauli (W : Bas) :
    canonicalVector (F := F) (m := m) (.pauli W) = 0 := by
  funext i
  cases i with
  | point W i => cases W <;> rfl
  | scalar W => cases W <;> rfl
  | seed => rfl
  | direction i => rfl
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [Algebra (ZMod 2) F] [NeZero m] {t d : ℕ}
theorem pullbackStrategy_pauli_A (hm : m ∣ Fintype.card F)
    (b : Module.Basis (Fin t) (ZMod 2) F)
    (S : TensorProductStrategy (binaryGame (d := d) hm b)) (W : Bas) (a : Answer F m d) :
    (pullbackStrategy hm b S).PA.M (.pauli W) a = S.PA.M (.pauli W, 0) a := by
  simp only [pullbackStrategy, ProjectiveMeasurement.reindex_M, Equiv.refl_apply,
    encodeQuestion, Question.ty, canonicalVector_pauli, map_zero]
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [Algebra (ZMod 2) F] [NeZero m] {t d : ℕ}
theorem pullbackStrategy_pauli_B (hm : m ∣ Fintype.card F)
    (b : Module.Basis (Fin t) (ZMod 2) F)
    (S : TensorProductStrategy (binaryGame (d := d) hm b)) (W : Bas) (a : Answer F m d) :
    (pullbackStrategy hm b S).PB.M (.pauli W) a = S.PB.M (.pauli W, 0) a := by
  simp only [pullbackStrategy, ProjectiveMeasurement.reindex_M, Equiv.refl_apply,
    encodeQuestion, Question.ty, canonicalVector_pauli, map_zero]
end
end MIPRE.QLD.PauliCL

namespace MIPRE.Introspection.PauliRestriction
noncomputable section
open Matrix Finset Classical
set_option linter.unusedSectionVars false
variable {F F₀ ι A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Field F₀] [Fintype F₀] [DecidableEq F₀]
  [Fintype ι] [DecidableEq ι] [Fintype A] {m t d ℓ : ℕ} [NeZero m]
variable (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
  (L : Bool → CL.CLFun F₀ ι ℓ) (project : QLD.Answer F m d → ι → F₀)
  (D : (ι → F₀) → (ι → F₀) → A → A → Bool)
  (S : TensorProductStrategy (fullGame hm b L project D))
theorem strategy_failure_le (a₀ b₀ : QLD.Answer F m d) {ε : ℝ} (hS : 1 - S.value ≤ ε) :
    1 - (strategy hm b L project D S a₀ b₀).value ≤
      (TypeGraph.edges QLD.adj (.pauli .X) (.pauli .Z) ℓ).card * ε := by
  rw [strategy, QLD.PauliCL.pullbackStrategy_value]
  exact binaryStrategy_failure_le hm b L project D S a₀ b₀ hS
end
end MIPRE.Introspection.PauliRestriction

namespace MIPRE.Introspection.PauliRestriction
noncomputable section
open Matrix Finset Classical
set_option linter.unusedSectionVars false
variable {F F₀ ι A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Field F₀] [Fintype F₀] [DecidableEq F₀]
  [Fintype ι] [DecidableEq ι] [Fintype A] {m t d ℓ : ℕ} [NeZero m]
variable (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
  (L : Bool → CL.CLFun F₀ ι ℓ) (project : QLD.Answer F m d → ι → F₀)
  (D : (ι → F₀) → (ι → F₀) → A → A → Bool)
  (S : TensorProductStrategy (fullGame hm b L project D))
theorem strategy_pauli_A (a₀ b₀ : QLD.Answer F m d) (W : QLD.Bas) (a : QLD.Answer F m d) :
    (strategy hm b L project D S a₀ b₀).PA.M (.pauli W) a =
      ((completePauliPOVM a₀ (S.PA.toPOVM (QuestionType.pauli (.pauli W),0))).mats a).val := by
  exact QLD.PauliCL.pullbackStrategy_pauli_A hm b
    (binaryStrategy hm b L project D S a₀ b₀) W a
end
end MIPRE.Introspection.PauliRestriction

namespace MIPRE.Introspection.PauliRestriction
noncomputable section
open Matrix Finset Classical
set_option linter.unusedSectionVars false
variable {F F₀ ι A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Field F₀] [Fintype F₀] [DecidableEq F₀]
  [Fintype ι] [DecidableEq ι] [Fintype A] {m t d ℓ : ℕ} [NeZero m]
variable (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
  (L : Bool → CL.CLFun F₀ ι ℓ) (project : QLD.Answer F m d → ι → F₀)
  (D : (ι → F₀) → (ι → F₀) → A → A → Bool)
  (S : TensorProductStrategy (fullGame hm b L project D))
theorem strategy_pauli_B (a₀ b₀ : QLD.Answer F m d) (W : QLD.Bas) (a : QLD.Answer F m d) :
    (strategy hm b L project D S a₀ b₀).PB.M (.pauli W) a =
      ((completePauliPOVM b₀ (S.PB.toPOVM (QuestionType.pauli (.pauli W),0))).mats a).val := by
  exact QLD.PauliCL.pullbackStrategy_pauli_B hm b
    (binaryStrategy hm b L project D S a₀ b₀) W a
end
end MIPRE.Introspection.PauliRestriction

namespace MIPRE.Introspection
noncomputable section
theorem errorProfile_nonneg {a b x ε : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) (hε : 0 ≤ ε) :
    0 ≤ errorProfile a b x ε := by unfold errorProfile; positivity
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
theorem adaptiveBudgetCoefficient_pos (r : ℕ) {edges : ℝ} (hE : 0 ≤ edges) :
    0 < adaptiveBudgetCoefficient r edges := by
  unfold adaptiveBudgetCoefficient
  positivity
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
theorem adaptivePowerCoefficient_one_le (r : ℕ) {edges : ℝ} (hE : 0 ≤ edges) :
    1 ≤ adaptivePowerCoefficient r edges := by
  unfold adaptivePowerCoefficient
  linarith [adaptiveBudgetCoefficient_pos r hE]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
theorem adaptiveSoundnessCoefficient_one_le (r n : ℕ) {edges : ℝ} (hE : 0 ≤ edges) :
    1 ≤ adaptiveSoundnessCoefficient r edges n :=
  (one_le_pow₀ (adaptivePowerCoefficient_one_le r hE)).trans (le_max_left _ _)
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
theorem primitiveBudgetCoefficient_bounds (r : ℕ) {edges : ℝ} (hE : 0 ≤ edges) :
    1 ≤ primitiveBudgetCoefficient r edges ∧
    4 * edges + 2 ≤ primitiveBudgetCoefficient r edges ∧
    TypedEstimates.hidingPauliBudget r edges 1 1 ≤ primitiveBudgetCoefficient r edges ∧
    4 * edges + 2 * TypedEstimates.hidingPauliBudget r edges 1 1 ≤
      primitiveBudgetCoefficient r edges := by
  have hB : 0 ≤ TypedEstimates.hidingPauliBudget r edges 1 1 := by
    unfold TypedEstimates.hidingPauliBudget
    positivity
  unfold primitiveBudgetCoefficient
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
theorem primitiveSoundnessCoefficient_one_le (r : ℕ) {edges : ℝ} (hE : 0 ≤ edges) :
    1 ≤ primitiveSoundnessCoefficient r edges := by
  have hC := adaptiveSoundnessCoefficient_one_le r (2 * r) hE
  have hc := (primitiveBudgetCoefficient_bounds r hE).1
  have hfirst : 1 ≤ (1 + edges) * adaptiveSoundnessCoefficient r edges (2 * r) := by
    nlinarith [mul_nonneg hE (show 0 ≤ adaptiveSoundnessCoefficient r edges (2 * r) by linarith)]
  unfold primitiveSoundnessCoefficient
  nlinarith [mul_nonneg (sub_nonneg.mpr hfirst) (sub_nonneg.mpr hc)]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
theorem extractedSoundnessCoefficient_one_le (r : ℕ) {edges : ℝ} (hE : 0 ≤ edges) :
    1 ≤ extractedSoundnessCoefficient r edges := by
  unfold extractedSoundnessCoefficient
  linarith [primitiveSoundnessCoefficient_one_le r hE]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
theorem validSoundnessCoefficient_one_le (r : ℕ) {edges : ℝ} (he : 0 ≤ edges) :
    1 ≤ validSoundnessCoefficient r edges := by
  have h := extractedSoundnessCoefficient_one_le r he
  unfold validSoundnessCoefficient
  linarith
end
end MIPRE.Introspection

namespace MIPRE.TensorProductStrategy
section
variable {X Y A B X' Y' A' B' : Type*}
  [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
  {G : Game X Y A B} (S : TensorProductStrategy G) (G' : Game X' Y' A' B')
  (eX : X' → X) (eY : Y' → Y) (eA : A' ≃ A) (eB : B' ≃ B)
/-- Question and answer equalities identify the relabeled Alice effect. -/
theorem relabelPAEq (x' : X') (a' : A') (x : X) (a : A)
    (hx : eX x' = x) (ha : eA a' = a) : S.RelabelPAEq G' eX eY eA eB x' a' x a := by
  simp only [RelabelPAEq, relabel_PA_M, hx, ha]
  rfl
end
end MIPRE.TensorProductStrategy

namespace MIPRE.TensorProductStrategy
section
variable {X Y A B X' Y' A' B' : Type*}
  [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
  {G : Game X Y A B} (S : TensorProductStrategy G) (G' : Game X' Y' A' B')
  (eX : X' → X) (eY : Y' → Y) (eA : A' ≃ A) (eB : B' ≃ B)
/-- Question and answer equalities identify the relabeled Bob effect. -/
theorem relabelPBEq (y' : Y') (b' : B') (y : Y) (b : B)
    (hy : eY y' = y) (hb : eB b' = b) : S.RelabelPBEq G' eX eY eA eB y' b' y b := by
  simp only [RelabelPBEq, relabel_PB_M, hy, hb]
  rfl
end
end MIPRE.TensorProductStrategy

namespace MIPRE.Introspection.ExplicitGame
noncomputable section
open Finset Classical
open QLD.PauliCL
open QLD.PauliCL.ExplicitSeed
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000
variable {F F₀ ι A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Field F₀] [Fintype F₀] [DecidableEq F₀]
  [Fintype ι] [DecidableEq ι] [Fintype A] {m t d ℓ : ℕ} [NeZero m]
variable (hm : m ∣ Fintype.card F) (χ : F → Fin m) (π : F ≃ F)
  (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s)
  (b : Module.Basis (Fin t) (ZMod 2) F)
  (L : Bool → CL.CLFun F₀ ι ℓ) (project : QLD.Answer F m d → ι → F₀)
  (D : (ι → F₀) → (ι → F₀) → A → A → Bool)
include hχ in
/-- The raw question equivalence intertwines every sampled typed question. -/
theorem questionEquiv_family (u : QuestionType QLD.Ty ℓ)
    (x : Fin ((3*m+3)*t) → ZMod 2) :
    questionEquiv π b (u,(TypedPresentation.family (ExplicitSeed.binaryPresentation χ b) u).eval x) =
      (u,(TypedPresentation.family (QLD.PauliCL.binaryPresentation hm b) u).eval
        (binarySeedPermutation π b x)) := by
  cases u with
  | inl p =>
    exact congrArg (fun y => (Sum.inl p,y))
      (binaryOutputPermutation_presentation hm χ π hχ b p x)
  | inr u => rcases u with ⟨u,w⟩; simp
end
end MIPRE.Introspection.ExplicitGame

namespace MIPRE.Introspection.ExplicitGame
noncomputable section
open Finset Classical
open QLD.PauliCL
open QLD.PauliCL.ExplicitSeed
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000
variable {F F₀ ι A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Field F₀] [Fintype F₀] [DecidableEq F₀]
  [Fintype ι] [DecidableEq ι] [Fintype A] {m t d ℓ : ℕ} [NeZero m]
variable (hm : m ∣ Fintype.card F) (χ : F → Fin m) (π : F ≃ F)
  (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s)
  (b : Module.Basis (Fin t) (ZMod 2) F)
  (L : Bool → CL.CLFun F₀ ι ℓ) (project : QLD.Answer F m d → ι → F₀)
  (D : (ι → F₀) → (ι → F₀) → A → A → Bool)
include hχ in
/-- Equality of the complete typed law, including every auxiliary and mixed edge. -/
theorem game_mu (q r : Question m t ℓ) :
    (game hm χ π b L project D).μ q r =
      (PauliRestriction.fullGame hm b L project D).μ
        (questionEquiv π b q) (questionEquiv π b r) := by
  apply dist_equiv _ _ _ _
    (Equiv.prodCongr (Equiv.refl _) (binarySeedPermutation π b)) (questionEquiv π b)
  · intro s
    exact questionEquiv_family hm χ π hχ b s.1.val.1 s.2
  · intro s
    exact questionEquiv_family hm χ π hχ b s.1.val.2 s.2
end
end MIPRE.Introspection.ExplicitGame

namespace MIPRE.Introspection.ExplicitGame
noncomputable section
open Finset Classical
open QLD.PauliCL
open QLD.PauliCL.ExplicitSeed
set_option linter.unusedSectionVars false
set_option maxHeartbeats 60000
set_option backward.isDefEq.respectTransparency true
variable {F F₀ ι A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Field F₀] [Fintype F₀] [DecidableEq F₀]
  [Fintype ι] [DecidableEq ι] [Fintype A] {m t d ℓ : ℕ} [NeZero m]
variable (hm : m ∣ Fintype.card F) (χ : F → Fin m) (π : F ≃ F)
  (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s)
  (b : Module.Basis (Fin t) (ZMod 2) F)
  (L : Bool → CL.CLFun F₀ ι ℓ) (project : QLD.Answer F m d → ι → F₀)
  (D : (ι → F₀) → (ι → F₀) → A → A → Bool)
include hχ in
/-- Transport to the legacy game preserves the strategy value. -/
theorem toLegacy_value (S : TensorProductStrategy (game hm χ π b L project D)) :
    (toLegacy hm χ π b L project D S).value = S.value := by
  apply S.value_relabel _ (questionEquiv π b).symm (questionEquiv π b).symm (.refl _) (.refl _)
  · intro q r
    simpa only [Equiv.apply_symm_apply, Equiv.refl_apply] using
      (game_mu hm χ π hχ b L project D ((questionEquiv π b).symm q)
        ((questionEquiv π b).symm r)).symm
  · intro q r a a'
    simpa only [Equiv.apply_symm_apply, Equiv.refl_apply] using
      (game_D hm χ π b L project D ((questionEquiv π b).symm q)
        ((questionEquiv π b).symm r) a a').symm
end
end MIPRE.Introspection.ExplicitGame

namespace MIPRE.Introspection.ExplicitGame
noncomputable section
open Finset Classical
open QLD.PauliCL
open QLD.PauliCL.ExplicitSeed
set_option linter.unusedSectionVars false
set_option maxHeartbeats 60000
set_option backward.isDefEq.respectTransparency true
variable {F F₀ ι A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Field F₀] [Fintype F₀] [DecidableEq F₀]
  [Fintype ι] [DecidableEq ι] [Fintype A] {m t d ℓ : ℕ} [NeZero m]
variable (hm : m ∣ Fintype.card F) (χ : F → Fin m) (π : F ≃ F)
  (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s)
  (b : Module.Basis (Fin t) (ZMod 2) F)
  (L : Bool → CL.CLFun F₀ ι ℓ) (project : QLD.Answer F m d → ι → F₀)
  (D : (ι → F₀) → (ι → F₀) → A → A → Bool)
/-- Legacy transport preserves Alice's distinguished Pauli effects. -/
theorem toLegacy_pauli_A (S : TensorProductStrategy (game hm χ π b L project D))
    (W : QLD.Bas) (a : ParsedAnswer (ι → F₀) A (QLD.Answer F m d)) :
    S.RelabelPAEq (PauliRestriction.fullGame hm b L project D)
      (questionEquiv π b).symm (questionEquiv π b).symm (.refl _) (.refl _)
      (.inl (.pauli W),0) a (.inl (.pauli W),0) a :=
  S.relabelPAEq (PauliRestriction.fullGame hm b L project D)
    (questionEquiv π b).symm (questionEquiv π b).symm (.refl _) (.refl _)
    (.inl (.pauli W),0) a (.inl (.pauli W),0) a
    (questionEquiv_symm_pauli π b W 0) rfl
end
end MIPRE.Introspection.ExplicitGame

namespace MIPRE.Introspection.ExplicitGame
noncomputable section
open Finset Classical
open QLD.PauliCL
open QLD.PauliCL.ExplicitSeed
set_option linter.unusedSectionVars false
set_option maxHeartbeats 60000
set_option backward.isDefEq.respectTransparency true
variable {F F₀ ι A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Field F₀] [Fintype F₀] [DecidableEq F₀]
  [Fintype ι] [DecidableEq ι] [Fintype A] {m t d ℓ : ℕ} [NeZero m]
variable (hm : m ∣ Fintype.card F) (χ : F → Fin m) (π : F ≃ F)
  (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s)
  (b : Module.Basis (Fin t) (ZMod 2) F)
  (L : Bool → CL.CLFun F₀ ι ℓ) (project : QLD.Answer F m d → ι → F₀)
  (D : (ι → F₀) → (ι → F₀) → A → A → Bool)
/-- Legacy transport preserves Bob's distinguished Pauli effects. -/
theorem toLegacy_pauli_B (S : TensorProductStrategy (game hm χ π b L project D))
    (W : QLD.Bas) (a : ParsedAnswer (ι → F₀) A (QLD.Answer F m d)) :
    S.RelabelPBEq (PauliRestriction.fullGame hm b L project D)
      (questionEquiv π b).symm (questionEquiv π b).symm (.refl _) (.refl _)
      (.inl (.pauli W),0) a (.inl (.pauli W),0) a :=
  S.relabelPBEq (PauliRestriction.fullGame hm b L project D)
    (questionEquiv π b).symm (questionEquiv π b).symm (.refl _) (.refl _)
    (.inl (.pauli W),0) a (.inl (.pauli W),0) a
    (questionEquiv_symm_pauli π b W 0) rfl
end
end MIPRE.Introspection.ExplicitGame

namespace MIPRE.Introspection.RestrictedSoundness
noncomputable section
open Matrix Finset Classical BinaryComplete
set_option linter.unusedSectionVars false
theorem edgeCount_one_le (ℓ : ℕ) : 1 ≤ edgeCount ℓ := by
  have h : 1 ≤ (TypeGraph.edges QLD.adj (.pauli .X) (.pauli .Z) ℓ).card :=
    (TypeGraph.edges_nonempty QLD.adj (.pauli .X) (.pauli .Z) ℓ).card_pos
  unfold edgeCount
  exact_mod_cast h
end
end MIPRE.Introspection.RestrictedSoundness

namespace MIPRE.ProjectiveMeasurement
noncomputable section
open Matrix Kronecker Finset Classical
variable {X A A' H : Type*} [Fintype A] [Fintype A'] [DecidableEq A]
  [Fintype H] [DecidableEq H]
/-- Questions whose decoder is the identity have exactly the original effects. -/
theorem mergeByQuestion_M_of_id (P : ProjectiveMeasurement X A (Matrix H H ℂ))
    (r : X → A → A) (x : X) (hr : ∀ a, r x a = a) (a : A) :
    (P.mergeByQuestion r).M x a = P.M x a := by
  simp [mergeByQuestion_M, hr, Finset.sum_filter]
end
end MIPRE.ProjectiveMeasurement

namespace MIPRE.TensorProductStrategy
noncomputable section
open Matrix Kronecker Finset Classical
variable {X Y A B A' B' : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype A'] [Fintype B'] [DecidableEq A] [DecidableEq B]
/-- Identity decoding at an Alice question preserves its effects literally. -/
theorem mergeByQuestionPAEq {G' : Game X Y A B} (S' : TensorProductStrategy G')
    (G : Game X Y A B) (rA : X → A → A) (rB : Y → B → B) (x : X) (a : A)
    (hr : ∀ a, rA x a = a) : S'.MergeByQuestionPAEq G rA rB x a :=
  S'.PA.mergeByQuestion_M_of_id rA x hr a
end
end MIPRE.TensorProductStrategy

namespace MIPRE.TensorProductStrategy
noncomputable section
open Matrix Kronecker Finset Classical
variable {X Y A B A' B' : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype A'] [Fintype B'] [DecidableEq A] [DecidableEq B]
/-- Identity decoding at a Bob question preserves its effects literally. -/
theorem mergeByQuestionPBEq {G' : Game X Y A B} (S' : TensorProductStrategy G')
    (G : Game X Y A B) (rA : X → A → A) (rB : Y → B → B) (y : Y) (b : B)
    (hr : ∀ b, rB y b = b) : S'.MergeByQuestionPBEq G rA rB y b :=
  S'.PB.mergeByQuestion_M_of_id rB y hr b
end
end MIPRE.TensorProductStrategy

namespace MIPRE.Introspection.AuxiliaryQuotient
noncomputable section
open Classical
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency true
variable {PauliType PauliAnswer F κ A : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Fintype κ] [DecidableEq κ] [Fintype A]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
  (E : PauliType → PauliType → Bool) (X Z : PauliType)
  (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F (ι) ℓ)
  (project : PauliAnswer → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
    PauliAnswer → PauliAnswer → Bool)
/-- Deterministic answer decoding does not decrease the winning probability. -/
theorem value_le_decodedStrategy (hL : ∀ w, (L w).SupportedOn Finset.univ)
    (S : TensorProductStrategy (game E X Z P L project D DP)) :
    S.value ≤ (decodedStrategy E X Z P L project D DP S).value := by
  apply S.value_le_mergeAnswersByQuestion
    (TypedEstimates.parsedGame E X Z P L project D DP)
    (fun q => decodeAnswer L q.1) (fun q => decodeAnswer L q.1) (fun _ _ => rfl)
  intro q r a b h
  exact check_sound L X Z project D hL _ q.1 r.1 a b h
end
end MIPRE.Introspection.AuxiliaryQuotient

namespace MIPRE.Introspection.AuxiliaryQuotient
noncomputable section
open Classical
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency true
variable {PauliType PauliAnswer F κ A : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Fintype κ] [DecidableEq κ] [Fintype A]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
  (E : PauliType → PauliType → Bool) (X Z : PauliType)
  (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F (ι) ℓ)
  (project : PauliAnswer → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
    PauliAnswer → PauliAnswer → Bool)
/-- Any failure bound for the quotient strategy also bounds its legacy decoding. -/
theorem decodedStrategy_failure_le (hL : ∀ w, (L w).SupportedOn Finset.univ)
    (S : TensorProductStrategy (game E X Z P L project D DP))
    {ε : ℝ} (hS : 1 - S.value ≤ ε) :
    1 - (decodedStrategy E X Z P L project D DP S).value ≤ ε :=
  (sub_le_sub_left (value_le_decodedStrategy E X Z P L project D DP hL S) 1).trans hS
end
end MIPRE.Introspection.AuxiliaryQuotient

namespace MIPRE.Introspection.AuxiliaryQuotient
noncomputable section
open Classical
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency true
variable {PauliType PauliAnswer F κ A : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Fintype κ] [DecidableEq κ] [Fintype A]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
  (E : PauliType → PauliType → Bool) (X Z : PauliType)
  (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F (ι) ℓ)
  (project : PauliAnswer → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
    PauliAnswer → PauliAnswer → Bool)
/-- Every Alice effect at every Pauli question is unchanged. -/
theorem decodedStrategy_pauli_A (S : TensorProductStrategy (game E X Z P L project D DP))
    (p : PauliType) (x : κ → ZMod 2) (a : ParsedAnswer (ι → F) A PauliAnswer) :
    S.MergeByQuestionPAEq (TypedEstimates.parsedGame E X Z P L project D DP)
      (fun q => decodeAnswer L q.1) (fun q => decodeAnswer L q.1) (.inl p,x) a :=
  S.mergeByQuestionPAEq _ _ _ _ _ (fun _ => rfl)
end
end MIPRE.Introspection.AuxiliaryQuotient

namespace MIPRE.Introspection.AuxiliaryQuotient
noncomputable section
open Classical
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency true
variable {PauliType PauliAnswer F κ A : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Fintype κ] [DecidableEq κ] [Fintype A]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
  (E : PauliType → PauliType → Bool) (X Z : PauliType)
  (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F (ι) ℓ)
  (project : PauliAnswer → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
    PauliAnswer → PauliAnswer → Bool)
/-- Every Bob effect at every Pauli question is unchanged. -/
theorem decodedStrategy_pauli_B (S : TensorProductStrategy (game E X Z P L project D DP))
    (p : PauliType) (x : κ → ZMod 2) (a : ParsedAnswer (ι → F) A PauliAnswer) :
    S.MergeByQuestionPBEq (TypedEstimates.parsedGame E X Z P L project D DP)
      (fun q => decodeAnswer L q.1) (fun q => decodeAnswer L q.1) (.inl p,x) a :=
  S.mergeByQuestionPBEq _ _ _ _ _ (fun _ => rfl)
end
end MIPRE.Introspection.AuxiliaryQuotient

namespace MIPRE.Introspection.SourceReindex
noncomputable section
open Finset CL Classical
set_option linter.unusedSectionVars false
variable {F ι κ A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype A] [DecidableEq A] {ℓ : ℕ}
  (e : ι ≃ κ) (L : Bool → CLFun F ι ℓ)
  (D : (ι → F) → (ι → F) → A → A → Bool)
theorem exactlyOn (hL : ∀ w, (L w).ExactlyOn univ) (w : Bool) :
    (family e L w).ExactlyOn univ := by
  simpa only [family, Finset.map_univ_equiv] using (hL w).reindex e
end
end MIPRE.Introspection.SourceReindex

namespace MIPRE.Introspection.SourceReindex
noncomputable section
open Finset CL Classical
set_option linter.unusedSectionVars false
variable {F ι κ A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype A] [DecidableEq A] {ℓ : ℕ}
  (e : ι ≃ κ) (L : Bool → CLFun F ι ℓ)
  (D : (ι → F) → (ι → F) → A → A → Bool)
theorem game_mu (x y : κ → F) :
    (Honest.sourceGame (family e L) (decider e D)).μ x y =
      (Honest.sourceGame L D).μ ((reindexEquiv e).symm x) ((reindexEquiv e).symm y) := by
  change SampledGame.dist _ _ _ _ = SampledGame.dist _ _ _ _
  unfold SampledGame.dist
  rw [← Fintype.card_congr (reindexEquiv (F := F) e).toEquiv]
  congr 1
  refine Fintype.sum_equiv (reindexEquiv e).symm.toEquiv _ _ fun z => ?_
  simp only [family, CLFun.eval_reindex', Prod.mk.injEq, LinearEquiv.coe_toEquiv]
  simp only [LinearEquiv.eq_symm_apply]
end
end MIPRE.Introspection.SourceReindex

namespace MIPRE.Introspection.SourceReindex
noncomputable section
open Finset CL Classical
set_option linter.unusedSectionVars false
variable {F ι κ A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype A] [DecidableEq A] {ℓ : ℕ}
  (e : ι ≃ κ) (L : Bool → CLFun F ι ℓ)
  (D : (ι → F) → (ι → F) → A → A → Bool)
theorem quantumValue_eq :
    quantumValue (Honest.sourceGame (family e L) (decider e D)) =
      quantumValue (Honest.sourceGame L D) :=
  quantumValue_eq_of_equiv _ _ (reindexEquiv e).symm.toEquiv (reindexEquiv e).symm.toEquiv
    (.refl _) (.refl _) (game_mu e L D) (fun _ _ _ _ => rfl)
end
end MIPRE.Introspection.SourceReindex

namespace MIPRE.Introspection.CLChecks
noncomputable section
open Finset CL
variable {F ι κ : Type*} [Field F] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] {ℓ : ℕ}
theorem map_compl (e : ι ≃ κ) (S : Finset ι) :
    (Sᶜ).map e.toEmbedding = (S.map e.toEmbedding)ᶜ := by
  ext i
  simp only [mem_map_equiv, mem_compl]
end
end MIPRE.Introspection.CLChecks

namespace MIPRE.Introspection.CLChecks
noncomputable section
open Finset CL
variable {F ι κ : Type*} [Field F] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] {ℓ : ℕ}
theorem outputPrefix_reindex (e : ι ≃ κ) (P : CLFun F ι ℓ) (k : ℕ) (y : ι → F) :
    (P.reindex e).outputPrefix k (reindexEquiv e y) =
      reindexEquiv e (P.outputPrefix k y) := by
  induction P generalizing k y with
  | zero => cases k <;> simp [CLFun.outputPrefix]
  | cons S L next ih =>
    cases k with
    | zero => simp
    | succ k =>
      rw [CLFun.reindex_cons, CLFun.outputPrefix_cons, CLFun.outputPrefix_cons,
        ← map_compl, ← reindexEquiv_proj, ← reindexEquiv_proj,
        LinearEquiv.symm_apply_apply, ih, map_add]
end
end MIPRE.Introspection.CLChecks

namespace MIPRE.Introspection.CLChecks
noncomputable section
open Finset CL
variable {F ι κ : Type*} [Field F] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] {ℓ : ℕ}
theorem prefixRegister_reindex (e : ι ≃ κ) (P : CLFun F ι ℓ) (k : ℕ) (y : ι → F) :
    prefixRegister (P.reindex e) k (reindexEquiv e y) =
      (prefixRegister P k y).map e.toEmbedding := by
  induction P generalizing k y with
  | zero => cases k <;> simp [prefixRegister]
  | cons S L next ih =>
    cases k with
    | zero => simp [prefixRegister]
    | succ k =>
      rw [CLFun.reindex_cons]
      simp only [prefixRegister]
      rw [← map_compl, ← reindexEquiv_proj, ← reindexEquiv_proj,
        LinearEquiv.symm_apply_apply, ih, map_union]
end
end MIPRE.Introspection.CLChecks

namespace MIPRE.Introspection.AuxiliaryQuotient
noncomputable section
open Finset CL CLChecks AuxiliaryDual Classical
set_option linter.unusedSectionVars false
variable {F ι κ A PA PT : Type*} [Field F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {ℓ : ℕ}
theorem reindex_eq_iff (e : ι ≃ κ) (x y : ι → F) :
    reindexEquiv e x = reindexEquiv e y ↔ x = y := (reindexEquiv e).injective.eq_iff
end
end MIPRE.Introspection.AuxiliaryQuotient

namespace MIPRE.Introspection.AuxiliaryQuotient
noncomputable section
open Finset CL CLChecks AuxiliaryDual Classical
set_option linter.unusedSectionVars false
variable {F ι κ A PA PT : Type*} [Field F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {ℓ : ℕ}
theorem hidingNext_reindex (e : ι ≃ κ) (P : CLFun F ι ℓ) (k : ℕ)
    (y yp x z zp v : ι → F) :
    hidingNext (P.reindex e) k
      (reindexEquiv e y, reindexEquiv e yp, reindexEquiv e x)
      (reindexEquiv e z, reindexEquiv e zp, reindexEquiv e v) ↔
      hidingNext P k (y, yp, x) (z, zp, v) := by
  simp only [hidingNext, outputPrefix_reindex, prefixRegister_reindex,
    ← CLChecks.map_compl, ← reindexEquiv_proj, reindex_eq_iff,
    stageDual_reindex_eq_iff]
end
end MIPRE.Introspection.AuxiliaryQuotient

namespace MIPRE.Introspection.AuxiliaryQuotient
noncomputable section
open Finset CL CLChecks AuxiliaryDual Classical
set_option linter.unusedSectionVars false
variable {F ι κ A PA PT : Type*} [Field F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {ℓ : ℕ}
theorem hidingPauli_reindex (e : ι ≃ κ) (P : CLFun F ι ℓ)
    (x y yp z : ι → F) :
    hidingPauli (P.reindex e) (reindexEquiv e x)
      (reindexEquiv e y, reindexEquiv e yp, reindexEquiv e z) ↔
      hidingPauli P x (y, yp, z) := by
  unfold hidingPauli
  rw [← map_zero (reindexEquiv (F := F) e), stageDual_reindex_eq_iff,
    CLFun.factorOfPrefix_reindex, ← CLChecks.map_compl, ← reindexEquiv_proj,
    ← reindexEquiv_proj, reindex_eq_iff]
end
end MIPRE.Introspection.AuxiliaryQuotient

namespace MIPRE.Introspection.AuxiliaryQuotient
noncomputable section
open Finset CL CLChecks AuxiliaryDual Classical
set_option linter.unusedSectionVars false
variable {F ι κ A PA PT : Type*} [Field F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {ℓ : ℕ}
theorem hidingRead_reindex (e : ι ≃ κ) (P : CLFun F ι ℓ)
    (y yp x z zp : ι → F) (a : A) :
    CLChecks.hidingRead (P.reindex e)
      (reindexEquiv e y, reindexEquiv e yp, reindexEquiv e x)
      (reindexEquiv e z, reindexEquiv e zp, a) ↔
      CLChecks.hidingRead P (y, yp, x) (z, zp, a) := by
  simp only [CLChecks.hidingRead, outputPrefix_reindex, reindex_eq_iff]
end
end MIPRE.Introspection.AuxiliaryQuotient

namespace MIPRE.Introspection.AuxiliaryQuotient
noncomputable section
open Finset CL CLChecks AuxiliaryDual Classical
set_option linter.unusedSectionVars false
variable {F ι κ A PA PT : Type*} [Field F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {ℓ : ℕ}
variable (e : ι ≃ κ) (L : Bool → CLFun F ι ℓ) (X Z : PT)
  (project : PA → ι → F) (D : (ι → F) → (ι → F) → A → A → Bool)
set_option backward.isDefEq.respectTransparency false in
theorem directed_reindex (t u : QuestionType PT ℓ)
    (a b : ParsedAnswer (ι → F) A PA) :
    directed (fun w => (L w).reindex e) X Z (fun a => reindexEquiv e (project a))
      (fun x y => D ((reindexEquiv e).symm x) ((reindexEquiv e).symm y))
      t u (answerEquiv e a) (answerEquiv e b) = directed L X Z project D t u a b := by
  fun_cases directed L X Z project D t u a b <;>
    simp_all only [directed, answerEquiv, Equiv.coe_fn_mk, CLChecks.sampling,
      CLFun.eval_reindex, CLChecks.reading, hidingRead_reindex, hidingNext_reindex,
      hidingPauli_reindex, reindex_eq_iff, LinearEquiv.symm_apply_apply,
      and_self, ↓reduceIte] <;> try rfl
  case case3 => exact decide_eq_decide.mpr Iff.rfl
  case case5 => exact decide_eq_decide.mpr Iff.rfl
  case case14 =>
    split <;> try rfl
    all_goals cases a <;> cases b <;> simp_all [-Bool.forall_bool]
    all_goals
      rename_i hbad
      exfalso
      apply hbad <;> rfl
end
end MIPRE.Introspection.AuxiliaryQuotient

namespace MIPRE.Introspection.AuxiliaryQuotient
noncomputable section
open Finset CL CLChecks AuxiliaryDual Classical
set_option linter.unusedSectionVars false
variable {F ι κ A PA PT : Type*} [Field F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {ℓ : ℕ}
variable (e : ι ≃ κ) (L : Bool → CLFun F ι ℓ) (X Z : PT)
  (project : PA → ι → F) (D : (ι → F) → (ι → F) → A → A → Bool)
theorem check_reindex (DP : PT → PT → PA → PA → Bool)
    (t u : QuestionType PT ℓ) (a b : ParsedAnswer (ι → F) A PA) :
    check (fun w => (L w).reindex e) X Z (fun a => reindexEquiv e (project a))
      (fun x y => D ((reindexEquiv e).symm x) ((reindexEquiv e).symm y))
      DP t u (answerEquiv e a) (answerEquiv e b) = check L X Z project D DP t u a b := by
  simp only [check, fits_answerEquiv, Equiv.apply_eq_iff_eq, directed_reindex]
  cases t <;> cases u <;> cases a <;> cases b <;> rfl
end
end MIPRE.Introspection.AuxiliaryQuotient

namespace MIPRE.Introspection.AuxiliaryQuotient
noncomputable section
open Finset CL CLChecks Classical
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency true
variable {F ι κ A PA PT Q : Type*} [Field F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {ℓ : ℕ}
variable [Fintype F] [DecidableEq F] [Fintype A] [Fintype PA]
  [Fintype PT] [DecidableEq PT] [Fintype Q] [DecidableEq Q]
  (e : ι ≃ κ) (E : PT → PT → Bool) (X Z : PT)
  (P : PT → CLFun (ZMod 2) Q 3) (L : Bool → CLFun F ι ℓ)
  (project : PA → ι → F) (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PT → PT → (Q → ZMod 2) → (Q → ZMod 2) → PA → PA → Bool)
theorem reindexedGame_D (q r : CL.Detyping.Question (QuestionType PT ℓ) Q)
    (a b : ParsedAnswer (ι → F) A PA) :
    (reindexedGame e E X Z P L project D DP).D q r (answerEquiv e a) (answerEquiv e b) =
      (game E X Z P L project D DP).D q r a b :=
  check_reindex e L X Z project D _ _ _ _ _
end
end MIPRE.Introspection.AuxiliaryQuotient

namespace MIPRE.Introspection.AuxiliaryQuotient
noncomputable section
open Finset CL CLChecks Classical
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency true
variable {F ι κ A PA PT Q : Type*} [Field F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {ℓ : ℕ}
variable [Fintype F] [DecidableEq F] [Fintype A] [Fintype PA]
  [Fintype PT] [DecidableEq PT] [Fintype Q] [DecidableEq Q]
  (e : ι ≃ κ) (E : PT → PT → Bool) (X Z : PT)
  (P : PT → CLFun (ZMod 2) Q 3) (L : Bool → CLFun F ι ℓ)
  (project : PA → ι → F) (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PT → PT → (Q → ZMod 2) → (Q → ZMod 2) → PA → PA → Bool)
theorem reindexedStrategy_value
    (S : TensorProductStrategy (game E X Z P L project D DP)) :
    (reindexedStrategy e E X Z P L project D DP S).value = S.value := by
  apply S.value_relabel _ (Equiv.refl _) (Equiv.refl _) (answerEquiv e).symm (answerEquiv e).symm
    (fun _ _ => rfl)
  intro q r a b
  obtain ⟨a,rfl⟩ := (answerEquiv (F := F) (A := A) (PA := PA) e).surjective a
  obtain ⟨b,rfl⟩ := (answerEquiv (F := F) (A := A) (PA := PA) e).surjective b
  simpa only [Equiv.refl_apply, Equiv.symm_apply_apply] using
    reindexedGame_D e E X Z P L project D DP q r a b
end
end MIPRE.Introspection.AuxiliaryQuotient

namespace MIPRE.Introspection.PauliErrorParameters
noncomputable section
open SourceCompiler PauliSamplerParameters
theorem profileCoefficient_one_le (a c : ℝ) : 1 ≤ profileCoefficient a c := le_max_left _ _
end
end MIPRE.Introspection.PauliErrorParameters

namespace MIPRE.Introspection.PauliErrorParameters
noncomputable section
open SourceCompiler PauliSamplerParameters
/-- The executable field has at least `(λ*n)^c` elements. -/
theorem canonical_field_lower (c lam n : ℕ) (hx : 2 ≤ lam * n) :
    (lam * n) ^ c ≤ 2 ^ fieldBits c lam n := by
  have ht : canonicalLog lam n = lam * n := Nat.max_eq_right hx
  have hs : lam * n ≤ 2 ^ (lam * n - 1).size := by
    have := Nat.lt_size_self (lam * n - 1)
    omega
  unfold fieldBits
  rw [ht]
  calc
    (lam * n) ^ c ≤ (2 ^ (lam * n - 1).size) ^ c := Nat.pow_le_pow_left hs c
    _ = 2 ^ ((lam * n - 1).size * c) := (pow_mul _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by nlinarith)
end
end MIPRE.Introspection.PauliErrorParameters

namespace MIPRE.Introspection.PauliErrorParameters
noncomputable section
open SourceCompiler PauliSamplerParameters
/-- The lower dyadic rounding of `c*λ*n+1` loses at most a factor of two. -/
theorem canonical_register_lower (c lam n : ℕ) (hx : 2 ≤ lam * n) :
    c * (lam * n) ≤ 2 * registerPower c lam n := by
  have ht : canonicalLog lam n = lam * n := Nat.max_eq_right hx
  have hs := Nat.size_pos.mpr (show 0 < c * canonicalLog lam n + 1 by omega)
  have hp := Nat.lt_size_self (c * canonicalLog lam n + 1)
  have he : (c * canonicalLog lam n + 1).size =
      ((c * canonicalLog lam n + 1).size - 1) + 1 := by omega
  rw [he, pow_succ] at hp
  change c * canonicalLog lam n + 1 < registerPower c lam n * 2 at hp
  rw [ht] at hp
  omega
end
end MIPRE.Introspection.PauliErrorParameters

namespace MIPRE.Introspection.PauliErrorParameters
noncomputable section
open SourceCompiler PauliSamplerParameters
/-- The actual `2^(-b*m)` tail is controlled by taking half the power of this
inequality; the exponent is not replaced by `2^(-2*b*m)`. -/
theorem canonical_exponential_lower (c lam n : ℕ) (hx : 2 ≤ lam * n) :
    (lam * n) ^ c ≤ 2 ^ (2 * registerPower c lam n) := by
  calc
    (lam * n) ^ c ≤ (2 ^ (lam * n)) ^ c :=
      Nat.pow_le_pow_left (Nat.lt_two_pow_self.le) c
    _ = 2 ^ ((lam * n) * c) := (pow_mul _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide)
      (by simpa only [Nat.mul_comm] using canonical_register_lower c lam n hx)
end
end MIPRE.Introspection.PauliErrorParameters

namespace MIPRE.Introspection.PauliErrorParameters
noncomputable section
open SourceCompiler PauliSamplerParameters
/-- The canonical point dimension has a fixed linear bound. -/
theorem canonical_register_upper (c lam n : ℕ) (hx : 2 ≤ lam * n) :
    registerPower c lam n ≤ (c + 1) * (lam * n) := by
  have ht : canonicalLog lam n = lam * n := Nat.max_eq_right hx
  have hm := registerPower_le c lam n
  rw [ht] at hm
  nlinarith
end
end MIPRE.Introspection.PauliErrorParameters

namespace MIPRE.Introspection.PauliErrorParameters
noncomputable section
open SourceCompiler PauliSamplerParameters
/-- The QLD profile for the parameters computed by the sampler has the
uniform introspection shape, including both residual terms. -/
theorem canonical_qldError_le_profile {a b : ℝ} (ha : 1 ≤ a)
    (hb0 : 0 < b) (hb1 : b ≤ 1) (c : ℕ) (hc : 2 ≤ c)
    (hcb : 2 * a + 2 ≤ (c : ℝ) * b) (lam n : ℕ) (hx : 2 ≤ lam * n)
    (ε : ℝ) (hε : 0 ≤ ε) :
    qldError a b (registerPower c lam n) (2 ^ fieldBits c lam n : ℕ) ε ≤
      errorProfile (profileCoefficient a c) b (lam * n) ε := by
  apply qldError_le_profile ha hb0 hb1 (by exact_mod_cast (show 1 ≤ c by omega)) hcb
    (by exact_mod_cast (show 1 ≤ lam * n by omega)) (Nat.cast_nonneg _) hε
  · exact_mod_cast canonical_register_upper c lam n hx
  · rw [Real.rpow_natCast]
    exact_mod_cast canonical_field_lower c lam n hx
  · rw [Real.rpow_natCast,
      show (2 : ℝ) * (registerPower c lam n : ℝ) = ((2 * registerPower c lam n : ℕ) : ℝ) by
        push_cast; ring,
      Real.rpow_natCast]
    exact_mod_cast canonical_exponential_lower c lam n hx
end
end MIPRE.Introspection.PauliErrorParameters

namespace MIPRE.Introspection.RestrictedSoundness
noncomputable section
open Matrix Finset Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] {m d : ℕ} [NeZero m]
/-- Scalar completion has no malformed mass when the parsed measurement only
has genuine full-register outcomes. -/
theorem completePauliPOVM_invalid_of_supported
    {V A H : Type*} [Fintype V] [Fintype A] [Fintype H] [DecidableEq H]
    (M : POVM (ParsedAnswer V A (QLD.Answer F m d)) H)
    (hM : ∀ a, (M.mats a).val ≠ 0 → ∃ x, a = .pauli (.pauliAns x))
    (W : QLD.Bas) (a : QLD.Answer F m d)
    (ha : (QLD.Question.pauli W).fmtOk a = false) :
    ((completePauliPOVM (.val 0) M).mats a).val = 0 := by
  rw [completePauliPOVM_mats]
  apply Finset.sum_eq_zero
  intro c hc
  by_contra hn
  obtain ⟨x,rfl⟩ := hM c hn
  have he : QLD.Answer.pauliAns x = a := (Finset.mem_filter.mp hc).2
  rw [← he] at ha
  cases ha
end
end MIPRE.Introspection.RestrictedSoundness

namespace MIPRE.Introspection.RestrictedSoundness
noncomputable section
open Matrix Finset Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] {m d : ℕ} [NeZero m]
theorem qldCoefficient_one_le : 1 ≤ qldCoefficient :=
  exists_fieldExtraction.choose_spec.choose_spec.1
end
end MIPRE.Introspection.RestrictedSoundness

namespace MIPRE.Introspection.RestrictedSoundness
noncomputable section
open Matrix Finset Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] {m d : ℕ} [NeZero m]
theorem qldExponent_lt_one : qldExponent < 1 :=
  exists_fieldExtraction.choose_spec.choose_spec.2.2.1
end
end MIPRE.Introspection.RestrictedSoundness

namespace MIPRE.Introspection.RestrictedSoundness
noncomputable section
open Matrix Finset Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] {m d : ℕ} [NeZero m]
/-- The proved QLD theorem, with its universal constants fixed globally. -/
theorem fieldExtraction_exists (hm : m ∣ Fintype.card F) (hd : 1 ≤ d)
    (R : TensorProductStrategy (QLD.qldGame (d := d) hm))
    (hA : PauliSupported R.PA.toPOVM) (hB : PauliSupported R.PB.toPOVM)
    {ε : ℝ} (hε : 0 ≤ ε) (hfail : 1 - R.value ≤ ε) :
    Nonempty (FieldExtraction hm R
      (QLD.errShape qldCoefficient qldExponent ε m d (Fintype.card F))) :=
  exists_fieldExtraction.choose_spec.choose_spec.2.2.2 hm hd R hA hB hε hfail
end
end MIPRE.Introspection.RestrictedSoundness

namespace MIPRE.Introspection.RestrictedSoundness
noncomputable section
open Matrix Finset Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] {m d : ℕ} [NeZero m]
theorem degreeOne_fieldExtraction_exists (hm : m ∣ Fintype.card F)
    (R : TensorProductStrategy (QLD.qldGame (d := 1) hm))
    (hA : PauliSupported R.PA.toPOVM) (hB : PauliSupported R.PB.toPOVM)
    {ε : ℝ} (hε : 0 ≤ ε) (hfail : 1 - R.value ≤ ε) :
    Nonempty (FieldExtraction hm R
      (PauliErrorParameters.qldError qldCoefficient qldExponent m (Fintype.card F) ε)) := by
  simpa only [QLD.errShape, PauliErrorParameters.qldError, Nat.cast_one, mul_one, neg_mul]
    using fieldExtraction_exists hm le_rfl R hA hB hε hfail
end
end MIPRE.Introspection.RestrictedSoundness

namespace MIPRE.Introspection.NumberedSoundness
noncomputable section
open Matrix Finset CL Classical BinaryComplete RestrictedSoundness
set_option linter.unusedSectionVars false
variable {F A I : Type} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype I] [DecidableEq I] {m t d ℓ : ℕ} [NeZero m]
  (e : I ≃ Coord m t) (L : Bool → CLFun (ZMod 2) I ℓ)
  (D : (I → ZMod 2) → (I → ZMod 2) → A → A → Bool)
  (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
  (χ : F → Fin m) (π : F ≃ F)
theorem coordinateStrategy_failure_le
    (S : TensorProductStrategy (NumberedComplete.game (d := d) e L D hm b χ π))
    {ε : ℝ} (hS : 1 - S.value ≤ ε) :
    1 - (coordinateStrategy e L D hm b χ π S).value ≤ ε := by
  have hv := (AuxiliaryQuotient.reindexedStrategy e QLD.adj (.pauli .X) (.pauli .Z)
    (QLD.PauliCL.ExplicitSeed.binaryPresentation χ b) L
    (NumberedComplete.project e b) D (ExplicitGame.pauliCheck hm π b) S).value_copy_le
      (BinaryComplete.explicitQuotientGame (SourceReindex.family e L)
        (SourceReindex.decider e D) hm b χ π)
      (fun _ _ => by rw [reindexedGame_eq e L D hm b χ π])
      (fun _ _ _ _ h => by rwa [reindexedGame_eq e L D hm b χ π] at h)
  rw [AuxiliaryQuotient.reindexedStrategy_value] at hv
  exact (sub_le_sub_left hv 1).trans hS
end
end MIPRE.Introspection.NumberedSoundness

namespace MIPRE.Introspection.NumberedSoundness
noncomputable section
open Matrix Finset CL Classical BinaryComplete RestrictedSoundness
set_option linter.unusedSectionVars false
variable {F A I : Type} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype I] [DecidableEq I] {m t d ℓ : ℕ} [NeZero m]
  (e : I ≃ Coord m t) (L : Bool → CLFun (ZMod 2) I ℓ)
  (D : (I → ZMod 2) → (I → ZMod 2) → A → A → Bool)
  (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
  (χ : F → Fin m) (π : F ≃ F)
theorem legacyStrategy_failure_le
    (S : TensorProductStrategy (NumberedComplete.game (d := d) e L D hm b χ π))
    (hL : ∀ w, (L w).SupportedOn univ) (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s)
    {ε : ℝ} (hS : 1 - S.value ≤ ε) :
    1 - (legacyStrategy e L D hm b χ π S).value ≤ ε := by
  have hv := ExplicitGame.toLegacy_value hm χ π hχ b (SourceReindex.family e L)
    (BinaryComplete.project b) (SourceReindex.decider e D) (explicitStrategy e L D hm b χ π S)
  apply (congrArg (fun x : ℝ => 1 - x) hv).le.trans
  apply AuxiliaryQuotient.decodedStrategy_failure_le
  · intro w
    simpa only [SourceReindex.family, map_univ_equiv] using (hL w).reindex e
  · exact coordinateStrategy_failure_le e L D hm b χ π S hS
end
end MIPRE.Introspection.NumberedSoundness

namespace MIPRE.Introspection.NumberedSoundness
noncomputable section
open Matrix Finset CL Classical BinaryComplete RestrictedSoundness
set_option linter.unusedSectionVars false
variable {F A I : Type} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype I] [DecidableEq I] {m t d ℓ : ℕ} [NeZero m]
  (e : I ≃ Coord m t) (L : Bool → CLFun (ZMod 2) I ℓ)
  (D : (I → ZMod 2) → (I → ZMod 2) → A → A → Bool)
  (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
  (χ : F → Fin m) (π : F ≃ F)
set_option backward.isDefEq.respectTransparency false in
theorem legacyStrategy_supported_A
    (S : TensorProductStrategy (NumberedComplete.game (d := d) e L D hm b χ π))
    (hS : ParsedPauliSupported S.PA.toPOVM) :
    ParsedPauliSupported (legacyStrategy e L D hm b χ π S).PA.toPOVM := by
  intro W a ha
  change (legacyStrategy e L D hm b χ π S).PA.M (.inl (.pauli W),0) a ≠ 0 at ha
  have he := ExplicitGame.toLegacy_pauli_A hm χ π b (SourceReindex.family e L)
    (BinaryComplete.project b) (SourceReindex.decider e D)
    (explicitStrategy e L D hm b χ π S) W a
  have hd := AuxiliaryQuotient.decodedStrategy_pauli_A QLD.adj (.pauli .X) (.pauli .Z)
    (QLD.PauliCL.ExplicitSeed.binaryPresentation χ b) (SourceReindex.family e L)
    (BinaryComplete.project b) (SourceReindex.decider e D) (ExplicitGame.pauliCheck hm π b)
    (coordinateStrategy e L D hm b χ π S) (.pauli W) 0 a
  have hc : (coordinateStrategy e L D hm b χ π S).PA.M (.inl (.pauli W),0) a ≠ 0 := by
    intro hz
    exact ha (he.trans (hd.trans hz))
  change S.PA.M (.inl (.pauli W),0) ((AuxiliaryQuotient.answerEquiv e).symm a) ≠ 0 at hc
  obtain ⟨x,hx⟩ := hS W _ hc
  refine ⟨x, ?_⟩
  exact (Equiv.symm_apply_eq (e := AuxiliaryQuotient.answerEquiv e)).mp hx
end
end MIPRE.Introspection.NumberedSoundness

namespace MIPRE.Introspection.NumberedSoundness
noncomputable section
open Matrix Finset CL Classical BinaryComplete RestrictedSoundness
set_option linter.unusedSectionVars false
variable {F A I : Type} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype I] [DecidableEq I] {m t d ℓ : ℕ} [NeZero m]
  (e : I ≃ Coord m t) (L : Bool → CLFun (ZMod 2) I ℓ)
  (D : (I → ZMod 2) → (I → ZMod 2) → A → A → Bool)
  (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
  (χ : F → Fin m) (π : F ≃ F)
set_option backward.isDefEq.respectTransparency false in
theorem legacyStrategy_supported_B
    (S : TensorProductStrategy (NumberedComplete.game (d := d) e L D hm b χ π))
    (hS : ParsedPauliSupported S.PB.toPOVM) :
    ParsedPauliSupported (legacyStrategy e L D hm b χ π S).PB.toPOVM := by
  intro W a ha
  change (legacyStrategy e L D hm b χ π S).PB.M (.inl (.pauli W),0) a ≠ 0 at ha
  have he := ExplicitGame.toLegacy_pauli_B hm χ π b (SourceReindex.family e L)
    (BinaryComplete.project b) (SourceReindex.decider e D)
    (explicitStrategy e L D hm b χ π S) W a
  have hd := AuxiliaryQuotient.decodedStrategy_pauli_B QLD.adj (.pauli .X) (.pauli .Z)
    (QLD.PauliCL.ExplicitSeed.binaryPresentation χ b) (SourceReindex.family e L)
    (BinaryComplete.project b) (SourceReindex.decider e D) (ExplicitGame.pauliCheck hm π b)
    (coordinateStrategy e L D hm b χ π S) (.pauli W) 0 a
  have hc : (coordinateStrategy e L D hm b χ π S).PB.M (.inl (.pauli W),0) a ≠ 0 := by
    intro hz
    exact ha (he.trans (hd.trans hz))
  change S.PB.M (.inl (.pauli W),0) ((AuxiliaryQuotient.answerEquiv e).symm a) ≠ 0 at hc
  obtain ⟨x,hx⟩ := hS W _ hc
  refine ⟨x, ?_⟩
  exact (Equiv.symm_apply_eq (e := AuxiliaryQuotient.answerEquiv e)).mp hx
end
end MIPRE.Introspection.NumberedSoundness

namespace MIPRE.Introspection.NumberedSoundness
noncomputable section
open Matrix Finset CL Classical BinaryComplete RestrictedSoundness
set_option linter.unusedSectionVars false
variable {F A I : Type} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype I] [DecidableEq I] {m t d ℓ : ℕ} [NeZero m]
  (e : I ≃ Coord m t) (L : Bool → CLFun (ZMod 2) I ℓ)
  (D : (I → ZMod 2) → (I → ZMod 2) → A → A → Bool)
  (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
  (χ : F → Fin m) (π : F ≃ F)
theorem qldStrategy_supported_A
    (S : TensorProductStrategy (NumberedComplete.game (d := d) e L D hm b χ π))
    (hS : ParsedPauliSupported S.PA.toPOVM) :
    PauliSupported (qldStrategy e L D hm b χ π S).PA.toPOVM := by
  intro W a ha
  change (qldStrategy e L D hm b χ π S).PA.M (.pauli W) a = 0
  rw [PauliRestriction.strategy_pauli_A]
  exact completePauliPOVM_invalid_of_supported _
    (legacyStrategy_supported_A e L D hm b χ π S hS W) W a ha
end
end MIPRE.Introspection.NumberedSoundness

namespace MIPRE.Introspection.NumberedSoundness
noncomputable section
open Matrix Finset CL Classical BinaryComplete RestrictedSoundness
set_option linter.unusedSectionVars false
variable {F A I : Type} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype I] [DecidableEq I] {m t d ℓ : ℕ} [NeZero m]
  (e : I ≃ Coord m t) (L : Bool → CLFun (ZMod 2) I ℓ)
  (D : (I → ZMod 2) → (I → ZMod 2) → A → A → Bool)
  (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
  (χ : F → Fin m) (π : F ≃ F)
theorem qldStrategy_supported_B
    (S : TensorProductStrategy (NumberedComplete.game (d := d) e L D hm b χ π))
    (hS : ParsedPauliSupported S.PB.toPOVM) :
    PauliSupported (qldStrategy e L D hm b χ π S).PB.toPOVM := by
  intro W a ha
  change (qldStrategy e L D hm b χ π S).PB.M (.pauli W) a = 0
  rw [PauliRestriction.strategy_pauli_B]
  exact completePauliPOVM_invalid_of_supported _
    (legacyStrategy_supported_B e L D hm b χ π S hS W) W a ha
end
end MIPRE.Introspection.NumberedSoundness

namespace MIPRE.Introspection.NumberedSoundness
noncomputable section
open Matrix Finset CL Classical BinaryComplete RestrictedSoundness
set_option linter.unusedSectionVars false
variable {F A I : Type} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype I] [DecidableEq I] {m t d ℓ : ℕ} [NeZero m]
  (e : I ≃ Coord m t) (L : Bool → CLFun (ZMod 2) I ℓ)
  (D : (I → ZMod 2) → (I → ZMod 2) → A → A → Bool)
  (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
  (χ : F → Fin m) (π : F ≃ F)
/-- A witness about the actual restricted strategy gives the source bound in
the original finite coordinates, with no coordinate or quotient penalty. -/
theorem quantumValue_ge_of_extraction
    (S : TensorProductStrategy (NumberedComplete.game (d := d) e L D hm b χ π))
    (hb : LowDegree.IsSelfDualBasis b) (hL : ∀ w, (L w).ExactlyOn univ)
    (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s) {ε δ : ℝ}
    (hδ : 0 ≤ δ) (hS : 1 - S.value ≤ ε)
    (w : FieldExtraction hm (qldStrategy e L D hm b χ π S) δ) :
    1 - validSoundnessCoefficient ℓ (edgeCount ℓ) *
      iteratedRoot (6 * ℓ + 2) (max ε δ) ≤ quantumValue (Honest.sourceGame L D) := by
  let wb := w.toBinary b hb
  have hv := RestrictedSoundness.quantumValue_ge_of_extraction hm b
    (SourceReindex.family e L) (SourceReindex.decider e D)
    (legacyStrategy e L D hm b χ π S) (SourceReindex.exactlyOn e L hL)
    wb.ξ wb.ξ_unit wb.VA wb.VB wb.VA_isometry wb.VB_isometry hδ
    (legacyStrategy_failure_le e L D hm b χ π S (fun w => (hL w).supportedOn) hχ hS)
    wb.state_error wb.X_error wb.Z_error
  exact hv.trans_eq (SourceReindex.quantumValue_eq e L D)
end
end MIPRE.Introspection.NumberedSoundness

namespace MIPRE.Introspection.NumberedSoundness
noncomputable section
open Matrix Finset CL Classical BinaryComplete RestrictedSoundness
set_option linter.unusedSectionVars false
variable {F A I : Type} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype I] [DecidableEq I] {m t d ℓ : ℕ} [NeZero m]
  (e : I ≃ Coord m t) (L : Bool → CLFun (ZMod 2) I ℓ)
  (D : (I → ZMod 2) → (I → ZMod 2) → A → A → Bool)
  (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
  (χ : F → Fin m) (π : F ≃ F)
/-- Uniform profile absorption only needs a witness for this restriction,
rather than an extraction hypothesis quantified over arbitrary strategies. -/
theorem quantumValue_ge_of_errorProfile
    (S : TensorProductStrategy (NumberedComplete.game (d := d) e L D hm b χ π))
    (hb : LowDegree.IsSelfDualBasis b) (hL : ∀ w, (L w).ExactlyOn univ)
    (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s)
    {a β x ε : ℝ} (ha : 1 ≤ a) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hx : 1 ≤ x) (hε : 0 ≤ ε) (hS : 1 - S.value ≤ ε)
    (w : FieldExtraction hm (qldStrategy e L D hm b χ π S)
      (errorProfile a β x (edgeCount ℓ * ε))) :
    1 - errorProfile (profileCoefficient ℓ a β) (β * rootExponent (6 * ℓ + 2)) x ε ≤
      quantumValue (Honest.sourceGame L D) := by
  have he0 : 0 ≤ edgeCount ℓ := (by norm_num : (0 : ℝ) ≤ 1).trans (edgeCount_one_le ℓ)
  have hδ := errorProfile_nonneg (a := a) (b := β) (x := x)
    (by linarith) (by linarith) (mul_nonneg he0 hε)
  have hv := quantumValue_ge_of_extraction e L D hm b χ π S hb hL hχ hδ hS w
  exact errorProfile_of_restricted_bound (6 * ℓ + 2)
    (by linarith [validSoundnessCoefficient_one_le ℓ he0]) ha hβ0 hβ1
    (edgeCount_one_le ℓ) hx hε le_rfl (quantumValue_nonneg _) hv
end
end MIPRE.Introspection.NumberedSoundness

namespace MIPRE.Introspection.NumberedSoundness
noncomputable section
open Matrix Finset CL Classical BinaryComplete RestrictedSoundness
set_option linter.unusedSectionVars false
variable {F A I : Type} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype I] [DecidableEq I] {m t d ℓ : ℕ} [NeZero m]
  (e : I ≃ Coord m t) (L : Bool → CLFun (ZMod 2) I ℓ)
  (D : (I → ZMod 2) → (I → ZMod 2) → A → A → Bool)
  (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
  (χ : F → Fin m) (π : F ≃ F)
theorem qldStrategy_failure_le
    (S : TensorProductStrategy (NumberedComplete.game (d := d) e L D hm b χ π))
    (hL : ∀ w, (L w).SupportedOn univ) (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s)
    {ε : ℝ} (hS : 1 - S.value ≤ ε) :
    1 - (qldStrategy e L D hm b χ π S).value ≤ edgeCount ℓ * ε :=
  PauliRestriction.strategy_failure_le hm b (SourceReindex.family e L)
    (BinaryComplete.project b) (SourceReindex.decider e D)
    (legacyStrategy e L D hm b χ π S) (.val 0) (.val 0)
    (legacyStrategy_failure_le e L D hm b χ π S hL hχ hS)
end
end MIPRE.Introspection.NumberedSoundness

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.NumberedSoundness
open Matrix Finset CL Classical BinaryComplete RestrictedSoundness
open SourceCompiler PauliSamplerParameters
set_option linter.unusedSectionVars false
variable {F A I : Type} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype I] [DecidableEq I] {m t d ℓ : ℕ} [NeZero m]
  (e : I ≃ Coord m t) (L : Bool → CLFun (ZMod 2) I ℓ)
  (D : (I → ZMod 2) → (I → ZMod 2) → A → A → Bool)
  (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
  (χ : F → Fin m) (π : F ≃ F)
attribute [local instance] MIPRE.Introspection.NumberedSoundness.canonical_neZero
theorem _root_.solution
    (c lam n : ℕ) (hc : 2 ≤ c)
    (hcb : 2 * qldCoefficient + 2 ≤ (c : ℝ) * qldExponent)
    (hx : 2 ≤ lam * n) (hq : Fintype.card F = 2 ^ fieldBits c lam n)
    (hm : registerPower c lam n ∣ Fintype.card F)
    (b : Module.Basis (Fin (fieldBits c lam n)) (ZMod 2) F)
    (hb : LowDegree.IsSelfDualBasis b)
    (e : I ≃ Coord (registerPower c lam n) (fieldBits c lam n))
    (L : Bool → CLFun (ZMod 2) I ℓ)
    (D : (I → ZMod 2) → (I → ZMod 2) → A → A → Bool)
    (hL : ∀ w, (L w).ExactlyOn univ)
    (χ : F → Fin (registerPower c lam n)) (π : F ≃ F)
    (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s)
    (S : TensorProductStrategy (NumberedComplete.game (d := 1) e L D hm b χ π))
    (hA : ParsedPauliSupported S.PA.toPOVM) (hB : ParsedPauliSupported S.PB.toPOVM)
    {ε : ℝ} (hε : 0 ≤ ε) (hS : 1 - S.value ≤ ε) :
    1 - errorProfile
      (profileCoefficient ℓ (PauliErrorParameters.profileCoefficient qldCoefficient c) qldExponent)
      (qldExponent * rootExponent (6 * ℓ + 2)) (lam * n) ε ≤
      quantumValue (Honest.sourceGame L D) := by
  have hη : 0 ≤ edgeCount ℓ * ε := mul_nonneg
    ((by norm_num : (0 : ℝ) ≤ 1).trans (edgeCount_one_le ℓ)) hε
  obtain ⟨w⟩ := degreeOne_fieldExtraction_exists hm (qldStrategy e L D hm b χ π S)
    (qldStrategy_supported_A e L D hm b χ π S hA)
    (qldStrategy_supported_B e L D hm b χ π S hB) hη
    (qldStrategy_failure_le e L D hm b χ π S (fun w => (hL w).supportedOn) hχ hS)
  apply quantumValue_ge_of_errorProfile e L D hm b χ π S hb hL hχ
    (PauliErrorParameters.profileCoefficient_one_le qldCoefficient c)
    qldExponent_pos qldExponent_lt_one.le
    (by exact_mod_cast (show 1 ≤ lam * n by omega)) hε hS
  refine w.mono ?_
  rw [hq]
  exact PauliErrorParameters.canonical_qldError_le_profile qldCoefficient_one_le
    qldExponent_pos qldExponent_lt_one.le c hc hcb lam n hx (edgeCount ℓ * ε) hη
end MIPRE.Introspection.NumberedSoundness
