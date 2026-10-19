-- Prove2me | solution 1 for MIPStarRE.LDT.SelfImprovement.matrixSdpCanonicalStrongDuality
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T04:04:05.050229+00:00
-- url     : https://prove2.me/submissions/631836ab-a285-4513-94c9-8bb1b3aa3ea2

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/SelfImprovement/MatrixRealization/Canonical/StrongDuality/Separation.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/Quantum/FiniteMatrix/Order.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/Quantum/FiniteMatrix/BlockDiagonal.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/MakingMeasurementsProjective/Defs.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/SelfImprovement/MatrixRealization/Base.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/SelfImprovement/MatrixRealization/CanonicalPrimal.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/SelfImprovement/MatrixRealization/Canonical.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/SelfImprovement/MatrixRealization/Canonical/StrongDuality/Basic.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/SelfImprovement/MatrixRealization/Canonical/StrongDuality/Separation.lean (solution of MIPStarRE.LDT.SelfImprovement.matrixSdpCanonicalStrongDuality);
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
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
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
import Mathlib.Algebra.Group.Action.Defs
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
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.MvPolynomial.Rename
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
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Unitary
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.Convex.Cone.Closure
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
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
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.FunLike.IsApply
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
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
import Mathlib.Data.Rat.Init
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.Separable
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.CharP
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Basic
import Mathlib.Logic.Embedding.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Prod
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
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
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
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.EMetricSpace.Defs
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
import Mathlib.Topology.Separation.Hausdorff
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Operators
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Families
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Fourier
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_TraceForms
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Base
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_CanonicalPrimal
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteConicDuality
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_StrongDuality_Basic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_StrongDuality_Separation
import Theorems.Thm_MIPStarRE_LDT_SelfImprovement_matrixSdpCanonicalBlockDiagonal_nonneg_iff
import Theorems.Thm_MIPStarRE_LDT_SelfImprovement_matrixSdpCanonicalDualObjective_exists_isMinOn
import Theorems.Thm_MIPStarRE_LDT_SelfImprovement_matrixSdpCanonicalDualOperator_trace_feasible
import Theorems.Thm_MIPStarRE_LDT_SelfImprovement_matrixSdpCanonicalFunctionalDualObjective_min_of_matrixDualMin
import Theorems.Thm_MIPStarRE_LDT_SelfImprovement_matrixSdpCanonicalPrimalFeasible_isClosed
import Theorems.Thm_MIPStarRE_LDT_SelfImprovement_matrixSdpCanonicalPrimalImageCone_identity_mem_iff_exists_feasible_objective
import Theorems.Thm_MIPStarRE_LDT_averageOperatorOverDistribution_nonneg
import Theorems.Thm_MIPStarRE_Quantum_conic_primalValue_eq_dualValue_of_fiber_max_dual_min
import Theorems.Thm_MIPStarRE_Quantum_kronecker_nonneg
import Theorems.Thm_MIPStarRE_Quantum_norm_apply_le_trace_re_of_nonneg
import Theorems.Thm_MIPStarRE_Quantum_trace_mul_nonneg_of_nonneg

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPStarRE.Quantum
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.Elementwise
open WithLp
set_option backward.isDefEq.respectTransparency false
variable {d : Type*} [Fintype d]
attribute [local instance] MIPStarRE.Quantum.instDecidableEq_definitions
/-- The elementwise matrix norm of a positive semidefinite finite matrix is
bounded by its real trace. -/
theorem norm_le_trace_re_of_nonneg {A : Op d} (hA : 0 ≤ A) :
    ‖A‖ ≤ Complex.re A.trace := by
  have htrace_nonneg : 0 ≤ Complex.re A.trace :=
    (Complex.nonneg_iff.mp ((Matrix.nonneg_iff_posSemidef.mp hA).trace_nonneg)).1
  exact (Matrix.norm_le_iff htrace_nonneg).mpr
    (norm_apply_le_trace_re_of_nonneg hA)
end
end MIPStarRE.Quantum

namespace Matrix
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.Elementwise
open WithLp
set_option backward.isDefEq.respectTransparency false
/-- A block-diagonal matrix is the sum of its blocks tensored with the
coordinate projections on the block index. -/
theorem blockDiagonal_eq_sum_kronecker_diagonal {o m : Type*}
    [Fintype o] [DecidableEq o] [Finite m] (B : o → Matrix m m ℂ) :
    Matrix.blockDiagonal B =
      ∑ b : o, Matrix.kronecker (B b)
        (Matrix.diagonal fun c : o => if c = b then (1 : ℂ) else 0) := by
  classical
  letI : Fintype m := Fintype.ofFinite m
  ext x y
  rcases x with ⟨i, bx⟩
  rcases y with ⟨j, cy⟩
  rw [Matrix.sum_apply]
  by_cases hxy : bx = cy
  · subst cy
    simp [Matrix.blockDiagonal_apply, Matrix.kronecker, Matrix.kroneckerMap_apply]
  · simp [Matrix.blockDiagonal_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, hxy]
end
end Matrix

namespace Matrix
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.Elementwise
open WithLp
set_option backward.isDefEq.respectTransparency false
/-- A block-diagonal complex matrix is positive semidefinite when all of its
diagonal blocks are positive semidefinite. -/
theorem blockDiagonal_nonneg {o m : Type*}
    [Finite o] [DecidableEq o] [Finite m]
    (B : o → Matrix m m ℂ) (hB : ∀ b, 0 ≤ B b) :
    0 ≤ Matrix.blockDiagonal B := by
  classical
  letI : Fintype o := Fintype.ofFinite o
  letI : Fintype m := Fintype.ofFinite m
  rw [Matrix.blockDiagonal_eq_sum_kronecker_diagonal B]
  exact Finset.sum_nonneg fun b _ =>
    MIPStarRE.Quantum.kronecker_nonneg (hB b) (by
      refine Matrix.nonneg_iff_posSemidef.mpr ?_
      exact Matrix.PosSemidef.diagonal <| by
        intro c
        by_cases hc : c = b <;> simp [hc])
end
end Matrix

attribute [instance] MIPStarRE.LDT.MakingMeasurementsProjective.FiniteHilbertSpace.instFintype

attribute [instance] MIPStarRE.LDT.MakingMeasurementsProjective.FiniteHilbertSpace.instDecidableEq

attribute [instance] MIPStarRE.LDT.MakingMeasurementsProjective.FiniteHilbertSpace.instNonempty

namespace MIPStarRE.LDT.MakingMeasurementsProjective.MatrixOperator
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder
open MIPStarRE.LDT
set_option backward.isDefEq.respectTransparency false
attribute [instance] MIPStarRE.LDT.MakingMeasurementsProjective.FiniteHilbertSpace.instFintype
attribute [instance] MIPStarRE.LDT.MakingMeasurementsProjective.FiniteHilbertSpace.instDecidableEq
attribute [instance] MIPStarRE.LDT.MakingMeasurementsProjective.FiniteHilbertSpace.instNonempty
noncomputable instance locallyConvexSpace
    (H : FiniteHilbertSpace) :
    LocallyConvexSpace ℝ (MatrixOperator H) :=
  NormedSpace.toLocallyConvexSpace
end
end MIPStarRE.LDT.MakingMeasurementsProjective.MatrixOperator

namespace MIPStarRE.LDT.SelfImprovement
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.Quantum
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
universe u
/-- The averaged point operator `A_g` is positive semidefinite. -/
theorem matrixAveragedPointOperator_nonneg (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (g : Polynomial params) :
    0 ≤ matrixAveragedPointOperator params model g := by
  unfold matrixAveragedPointOperator matrixAveragedPointOperatorContribution
  exact averageOperatorOverDistribution_nonneg (uniformDistribution (Point params))
    (fun u => (model.pointMeasurement u).effect (g u))
    (fun u => (model.pointMeasurement u).pos (g u))
end
end MIPStarRE.LDT.SelfImprovement

namespace MIPStarRE.LDT.SelfImprovement
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.Quantum
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
universe u
/-- Dual feasibility already implies that the dual operator is positive
semidefinite, since every averaged point operator `A_g` is positive. -/
theorem matrixSdpDualPositive_of_dualFeasible (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space)
    (hdual :
      ∀ g : Polynomial params,
        0 ≤ matrixSdpDualSlackOperator params model Z g) :
    0 ≤ Z := by
  -- Any polynomial would suffice here; the distinguished one is only a
  -- convenient fixed element of the finite polynomial type.
  let g0 : Polynomial params := sdpDistinguishedPolynomial params
  have hAg_nonneg : 0 ≤ matrixAveragedPointOperator params model g0 :=
    matrixAveragedPointOperator_nonneg params model g0
  have hAg_le_Z : matrixAveragedPointOperator params model g0 ≤ Z :=
    sub_nonneg.mp (by simpa [matrixSdpDualSlackOperator] using hdual g0)
  exact hAg_nonneg.trans hAg_le_Z
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
/-- A canonical block-diagonal operator is positive semidefinite when all of its
diagonal matrix blocks are positive semidefinite. -/
theorem matrixSdpCanonicalBlockDiagonal_nonneg (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (B : MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space)
    (hB : ∀ b, 0 ≤ B b) :
    0 ≤ matrixSdpCanonicalBlockDiagonal params model B := by
  classical
  rw [matrixSdpCanonicalBlockDiagonal_eq_reindex_blockDiagonal]
  refine Matrix.nonneg_iff_posSemidef.mpr ?_
  rw [Matrix.reindex_apply]
  exact (Matrix.posSemidef_submatrix_equiv
    (M := Matrix.blockDiagonal B)
    (Equiv.prodComm model.space.carrier (MatrixSdpCanonicalBlockIndex params)).symm).2
    (Matrix.nonneg_iff_posSemidef.mp (Matrix.blockDiagonal_nonneg B hB))
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
/-- The canonical equality constraint of a block-diagonal matrix is the sum of
its diagonal blocks. -/
theorem matrixSdpCanonicalConstraintOperator_blockDiagonal (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (B : MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space) :
    matrixSdpCanonicalConstraintOperator params model
        (matrixSdpCanonicalBlockDiagonal params model B) =
      ∑ b : MatrixSdpCanonicalBlockIndex params, B b := by
  simp [matrixSdpCanonicalConstraintOperator]
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
/-- The slack block of a matrix submeasurement is positive semidefinite. -/
theorem matrixSdpCanonicalSlackOperator_nonneg (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space) :
    0 ≤ matrixSdpCanonicalSlackOperator params model T := by
  exact sub_nonneg.mpr T.sum_le_one
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
/-- The canonical block matrix associated to a paper primal submeasurement is
positive semidefinite. -/
theorem matrixSdpCanonicalPrimalBlockMatrix_nonneg
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space) :
    0 ≤ matrixSdpCanonicalPrimalBlockMatrix params model T := by
  rw [matrixSdpCanonicalPrimalBlockMatrix]
  refine matrixSdpCanonicalBlockDiagonal_nonneg params model
    (matrixSdpCanonicalPrimalBlockFamily params model T) ?_
  intro b
  cases b with
  | none =>
      exact matrixSdpCanonicalSlackOperator_nonneg params model T
  | some g =>
      exact T.pos g
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
/-- The canonical block matrix associated to a submeasurement satisfies the
canonical equality constraint `∑_g T_g + S = I`. -/
theorem matrixSdpCanonicalConstraintOperator_primalBlockMatrix
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space) :
    matrixSdpCanonicalConstraintOperator params model
        (matrixSdpCanonicalPrimalBlockMatrix params model T) =
      1 := by
  rw [matrixSdpCanonicalPrimalBlockMatrix,
    matrixSdpCanonicalConstraintOperator_blockDiagonal]
  rw [Fintype.sum_option]
  simp [matrixSdpCanonicalSlackOperator]
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
/-- A paper primal submeasurement determines a feasible point of the canonical
block primal SDP by adjoining the slack block `I - ∑_g T_g`. -/
theorem matrixSdpCanonicalPrimalBlockMatrix_feasible
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space) :
    MatrixSdpCanonicalPrimalFeasible params model
      (matrixSdpCanonicalPrimalBlockMatrix params model T) where
  nonnegative := matrixSdpCanonicalPrimalBlockMatrix_nonneg params model T
  constraintEqOne := matrixSdpCanonicalConstraintOperator_primalBlockMatrix params model T
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
/-- The canonical dual slack is the difference between the canonical dual
operator and the canonical objective operator. -/
theorem matrixSdpCanonicalDualOperator_sub_objectiveOperator
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space) :
    matrixSdpCanonicalDualOperator params model Z -
        matrixSdpCanonicalObjectiveOperator params model =
      matrixSdpCanonicalBlockDiagonal params model
        (matrixSdpCanonicalDualSlackBlockFamily params model Z) := by
  rw [matrixSdpCanonicalDualOperator, matrixSdpCanonicalObjectiveOperator,
    ← matrixSdpCanonicalBlockDiagonal_sub]
  congr
  funext b
  cases b with
  | none =>
      simp
  | some g =>
      simp [matrixSdpDualSlackOperator]
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
/-- The canonical dual slack block matrix is positive semidefinite under paper
dual feasibility.

The canonical dual constraint for the block SDP is the positivity of the block
diagonal operator with blocks `Z - A_g` on the polynomial summands and `Z` on
the slack summand.  The polynomial blocks are precisely the paper dual
feasibility inequalities, while the slack block follows from the same
inequalities because the averaged point operators are positive. -/
theorem matrixSdpCanonicalDualSlackBlockDiagonal_nonneg_of_dualFeasible
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space)
    (hdual :
      ∀ g : Polynomial params,
        0 ≤ matrixSdpDualSlackOperator params model Z g) :
    0 ≤ matrixSdpCanonicalBlockDiagonal params model
      (matrixSdpCanonicalDualSlackBlockFamily params model Z) := by
  refine matrixSdpCanonicalBlockDiagonal_nonneg params model
    (matrixSdpCanonicalDualSlackBlockFamily params model Z) ?_
  intro b
  cases b with
  | none =>
      simpa [matrixSdpCanonicalDualSlackBlockFamily] using
        matrixSdpDualPositive_of_dualFeasible params model Z hdual
  | some g =>
      simpa [matrixSdpCanonicalDualSlackBlockFamily] using hdual g
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
/-- Positivity of the canonical dual slack block matrix is equivalent to the
paper dual feasibility inequalities `Z ≥ A_g`. -/
theorem matrixSdpCanonicalDualSlackBlockDiagonal_nonneg_iff_dualFeasible
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space) :
    0 ≤ matrixSdpCanonicalBlockDiagonal params model
        (matrixSdpCanonicalDualSlackBlockFamily params model Z) ↔
      ∀ g : Polynomial params,
        0 ≤ matrixSdpDualSlackOperator params model Z g := by
  constructor
  · intro hcanonical g
    have hblocks :=
      (matrixSdpCanonicalBlockDiagonal_nonneg_iff params model
        (matrixSdpCanonicalDualSlackBlockFamily params model Z)).mp hcanonical
    simpa using hblocks (some g)
  · exact matrixSdpCanonicalDualSlackBlockDiagonal_nonneg_of_dualFeasible params model Z
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
/-- The canonical dual constraint for `Z` is equivalent to the paper dual
constraints `Z ≥ A_g`. -/
theorem matrixSdpCanonicalDualConstraint_nonneg_iff_dualFeasible
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space) :
    0 ≤ matrixSdpCanonicalDualOperator params model Z -
        matrixSdpCanonicalObjectiveOperator params model ↔
      ∀ g : Polynomial params,
        0 ≤ matrixSdpDualSlackOperator params model Z g := by
  rw [matrixSdpCanonicalDualOperator_sub_objectiveOperator]
  exact matrixSdpCanonicalDualSlackBlockDiagonal_nonneg_iff_dualFeasible params model Z
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
/-- Paper dual feasibility implies feasibility of the canonical block dual
constraint. -/
theorem matrixSdpCanonicalDualConstraint_nonneg_of_dualFeasible
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space)
    (hdual :
      ∀ g : Polynomial params,
        0 ≤ matrixSdpDualSlackOperator params model Z g) :
    0 ≤ matrixSdpCanonicalDualOperator params model Z -
        matrixSdpCanonicalObjectiveOperator params model :=
  (matrixSdpCanonicalDualConstraint_nonneg_iff_dualFeasible params model Z).mpr hdual
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
/-- The canonical block matrix associated to the strict primal witness is
feasible for the canonical primal SDP. -/
theorem matrixSdpCanonicalStrictPrimalBlockMatrix_feasible
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    MatrixSdpCanonicalPrimalFeasible params model
      (matrixSdpCanonicalPrimalBlockMatrix params model
        (matrixSdpStrictPrimalSubmeasurement params model)) :=
  matrixSdpCanonicalPrimalBlockMatrix_feasible params model
    (matrixSdpStrictPrimalSubmeasurement params model)
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
/-- The canonical primal-dual gap is the trace pairing with the canonical dual
slack operator.

This is the algebraic identity behind weak duality for the canonical SDP: after
the dual trace pairing is identified with the paper dual objective, subtracting
the canonical objective leaves the trace pairing against `D(Z)-C`. -/
theorem matrixSdpCanonicalDualGap_trace
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X)
    (Z : MatrixOperator model.space) :
    matrixSdpDualObjective model Z -
        Complex.re (Matrix.trace
          (matrixSdpCanonicalObjectiveOperator params model * X)) =
      Complex.re (Matrix.trace
        ((matrixSdpCanonicalDualOperator params model Z -
            matrixSdpCanonicalObjectiveOperator params model) * X)) := by
  rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]
  rw [matrixSdpCanonicalDualOperator_trace_feasible params model X hX Z]
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
/-- Canonical weak duality for the self-improvement SDP.

For a feasible canonical primal matrix \(X\) and a feasible canonical dual
operator \(D(Z)-C\), the primal-dual gap is the trace pairing of two positive
semidefinite operators.  The preceding trace identity and positivity of this
pairing give the usual weak-duality inequality. -/
theorem matrixSdpCanonicalWeakDuality
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X)
    (Z : MatrixOperator model.space)
    (hdual :
      0 ≤ matrixSdpCanonicalDualOperator params model Z -
        matrixSdpCanonicalObjectiveOperator params model) :
    Complex.re (Matrix.trace
        (matrixSdpCanonicalObjectiveOperator params model * X)) ≤
      matrixSdpDualObjective model Z := by
  rw [← sub_nonneg]
  rw [matrixSdpCanonicalDualGap_trace params model X hX Z]
  exact MIPStarRE.Quantum.trace_mul_nonneg_of_nonneg hdual hX.nonnegative
end
end MIPStarRE.LDT.SelfImprovement

namespace MIPStarRE.LDT.SelfImprovement
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open Filter
open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.Elementwise Topology
set_option backward.isDefEq.respectTransparency false
/-- The canonical primal SDP has a feasible point, supplied by the explicit
strict primal submeasurement. -/
theorem matrixSdpCanonicalPrimalFeasible_nonempty
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    ∃ X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model),
      MatrixSdpCanonicalPrimalFeasible params model X :=
  ⟨matrixSdpCanonicalPrimalBlockMatrix params model
      (matrixSdpStrictPrimalSubmeasurement params model),
    matrixSdpCanonicalStrictPrimalBlockMatrix_feasible params model⟩
end
end MIPStarRE.LDT.SelfImprovement

namespace MIPStarRE.LDT.SelfImprovement
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open Filter
open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.Elementwise Topology
set_option backward.isDefEq.respectTransparency false
/-- The canonical equality-constraint operator preserves trace. -/
theorem matrixSdpCanonicalConstraintOperator_trace_eq
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) :
    Matrix.trace (matrixSdpCanonicalConstraintOperator params model X) =
      Matrix.trace X := by
  classical
  unfold Matrix.trace matrixSdpCanonicalConstraintOperator matrixSdpCanonicalDiagonalBlock
  simp only [Matrix.diag_apply, Matrix.sum_apply]
  change (∑ i : model.space.carrier,
      ∑ b : MatrixSdpCanonicalBlockIndex params, X (b, i) (b, i)) =
    ∑ x : MatrixSdpCanonicalBlockIndex params × model.space.carrier, X x x
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
end
end MIPStarRE.LDT.SelfImprovement

namespace MIPStarRE.LDT.SelfImprovement
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open Filter
open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.Elementwise Topology
set_option backward.isDefEq.respectTransparency false
/-- A feasible canonical primal matrix has trace equal to the base Hilbert-space dimension. -/
theorem matrixSdpCanonicalPrimalFeasible_trace_eq
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X) :
    Matrix.trace X = (Fintype.card model.space.carrier : ℂ) := by
  calc
    Matrix.trace X = Matrix.trace (matrixSdpCanonicalConstraintOperator params model X) := by
      exact (matrixSdpCanonicalConstraintOperator_trace_eq params model X).symm
    _ = Matrix.trace (1 : MatrixOperator model.space) := by rw [hX.constraintEqOne]
    _ = (Fintype.card model.space.carrier : ℂ) := by rw [Matrix.trace_one]
end
end MIPStarRE.LDT.SelfImprovement

namespace MIPStarRE.LDT.SelfImprovement
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open Filter
open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.Elementwise Topology
set_option backward.isDefEq.respectTransparency false
/-- Feasible canonical primal matrices have uniformly bounded elementwise norm. -/
theorem matrixSdpCanonicalPrimalFeasible_norm_le
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X) :
    ‖X‖ ≤ (Fintype.card model.space.carrier : ℝ) := by
  have hnorm := MIPStarRE.Quantum.norm_le_trace_re_of_nonneg hX.nonnegative
  rw [matrixSdpCanonicalPrimalFeasible_trace_eq params model X hX] at hnorm
  simpa using hnorm
end
end MIPStarRE.LDT.SelfImprovement

namespace MIPStarRE.LDT.SelfImprovement
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open Filter
open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.Elementwise Topology
set_option backward.isDefEq.respectTransparency false
/-- The feasible set of the canonical primal SDP is bounded in the elementwise matrix norm. -/
theorem matrixSdpCanonicalPrimalFeasible_isBounded
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    Bornology.IsBounded
      {X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) |
        MatrixSdpCanonicalPrimalFeasible params model X} := by
  rw [isBounded_iff_forall_norm_le]
  exact ⟨(Fintype.card model.space.carrier : ℝ), fun X hX =>
    matrixSdpCanonicalPrimalFeasible_norm_le params model X hX⟩
end
end MIPStarRE.LDT.SelfImprovement

namespace MIPStarRE.LDT.SelfImprovement
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open Filter
open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.Elementwise Topology
set_option backward.isDefEq.respectTransparency false
/-- The feasible set of the canonical primal SDP is compact. -/
theorem matrixSdpCanonicalPrimalFeasible_isCompact
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    IsCompact
      {X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) |
        MatrixSdpCanonicalPrimalFeasible params model X} :=
  Metric.isCompact_of_isClosed_isBounded
    (matrixSdpCanonicalPrimalFeasible_isClosed params model)
    (matrixSdpCanonicalPrimalFeasible_isBounded params model)
end
end MIPStarRE.LDT.SelfImprovement

namespace MIPStarRE.LDT.SelfImprovement
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open Filter
open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.Elementwise Topology
set_option backward.isDefEq.respectTransparency false
/-- The canonical primal objective is continuous. -/
theorem continuous_matrixSdpCanonicalPrimalObjective
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    Continuous fun X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) =>
      Complex.re (Matrix.trace (matrixSdpCanonicalObjectiveOperator params model * X)) := by
  have hmul :
      Continuous fun X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) =>
        matrixSdpCanonicalObjectiveOperator params model * X :=
    continuous_const.mul continuous_id
  exact Complex.continuous_re.comp hmul.matrix_trace
end
end MIPStarRE.LDT.SelfImprovement

namespace MIPStarRE.LDT.SelfImprovement
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open Filter
open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.Elementwise Topology
set_option backward.isDefEq.respectTransparency false
/-- An actual positive semidefinite canonical primal matrix maps into the closed
canonical primal image cone. -/
theorem matrixSdpCanonicalPrimalImageCone_mem_of_nonnegative
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : 0 ≤ X) :
    (matrixSdpCanonicalConstraintOperator params model X,
        Complex.re (Matrix.trace (matrixSdpCanonicalObjectiveOperator params model * X))) ∈
      matrixSdpCanonicalPrimalImageCone params model := by
  rw [← matrixSdpCanonicalPrimalConeMap_apply params model X]
  rw [matrixSdpCanonicalPrimalImageCone, ProperCone.mem_map]
  exact subset_closure <| by
    have hXcone :
        X ∈ (MIPStarRE.Quantum.opNonnegativeProperCone
          (matrixSdpCanonicalBlockHilbertSpace params model).carrier).toPointedCone := by
      change 0 ≤ X
      exact hX
    exact (PointedCone.mem_map).2 ⟨X, hXcone, rfl⟩
end
end MIPStarRE.LDT.SelfImprovement

namespace MIPStarRE.LDT.SelfImprovement
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open Filter
open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.Elementwise Topology
set_option backward.isDefEq.respectTransparency false
/-- A feasible canonical primal matrix maps to the image-cone point with
constraint component equal to the identity. -/
theorem matrixSdpCanonicalPrimalImageCone_mem_of_feasible
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X) :
    ((1 : MatrixOperator model.space),
        Complex.re (Matrix.trace (matrixSdpCanonicalObjectiveOperator params model * X))) ∈
      matrixSdpCanonicalPrimalImageCone params model := by
  simpa [hX.constraintEqOne] using
    matrixSdpCanonicalPrimalImageCone_mem_of_nonnegative params model X hX.nonnegative
end
end MIPStarRE.LDT.SelfImprovement

namespace MIPStarRE.LDT.SelfImprovement
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open Filter
open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.Elementwise Topology
set_option backward.isDefEq.respectTransparency false
/-- The canonical primal objective attains a maximum on the feasible set. -/
theorem matrixSdpCanonicalPrimalObjective_exists_isMaxOn
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    ∃ X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model),
      MatrixSdpCanonicalPrimalFeasible params model X ∧
        ∀ Y : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model),
          MatrixSdpCanonicalPrimalFeasible params model Y →
            Complex.re (Matrix.trace (matrixSdpCanonicalObjectiveOperator params model * Y)) ≤
              Complex.re (Matrix.trace (matrixSdpCanonicalObjectiveOperator params model * X)) := by
  obtain ⟨X, hX, hmax⟩ :=
    (matrixSdpCanonicalPrimalFeasible_isCompact params model).exists_isMaxOn
      (Set.nonempty_def.mpr (matrixSdpCanonicalPrimalFeasible_nonempty params model))
      (continuous_matrixSdpCanonicalPrimalObjective params model).continuousOn
  exact ⟨X, hX, fun Y hY => hmax hY⟩
end
end MIPStarRE.LDT.SelfImprovement

namespace MIPStarRE.LDT.SelfImprovement
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open Filter
open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.Elementwise Topology
set_option backward.isDefEq.respectTransparency false
/-- The canonical primal maximizer and dual minimizer exist, and their attained
values satisfy weak duality. This packages the attained optima but is not the
zero-gap strong-duality theorem. -/
theorem matrixSdpCanonicalPrimalDualOptima_exist
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    ∃ X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model),
      ∃ Z : MatrixOperator model.space,
        MatrixSdpCanonicalPrimalFeasible params model X ∧
        (∀ g : Polynomial params,
          0 ≤ matrixSdpDualSlackOperator params model Z g) ∧
        (∀ Y : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model),
          MatrixSdpCanonicalPrimalFeasible params model Y →
            Complex.re (Matrix.trace
              (matrixSdpCanonicalObjectiveOperator params model * Y)) ≤
              Complex.re (Matrix.trace
                (matrixSdpCanonicalObjectiveOperator params model * X))) ∧
        (∀ W : MatrixOperator model.space,
          (∀ g : Polynomial params,
            0 ≤ matrixSdpDualSlackOperator params model W g) →
          matrixSdpDualObjective model Z ≤ matrixSdpDualObjective model W) ∧
        Complex.re (Matrix.trace
          (matrixSdpCanonicalObjectiveOperator params model * X)) ≤
          matrixSdpDualObjective model Z := by
  obtain ⟨X, hX, hXmax⟩ :=
    matrixSdpCanonicalPrimalObjective_exists_isMaxOn params model
  obtain ⟨Z, hZ, hZmin⟩ :=
    matrixSdpCanonicalDualObjective_exists_isMinOn params model
  refine ⟨X, Z, hX, hZ, hXmax, hZmin, ?_⟩
  exact matrixSdpCanonicalWeakDuality params model X hX Z
    (matrixSdpCanonicalDualConstraint_nonneg_of_dualFeasible params model Z hZ)
end
end MIPStarRE.LDT.SelfImprovement

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPStarRE.LDT.SelfImprovement
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open Filter
open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.Elementwise Topology
set_option backward.isDefEq.respectTransparency false
theorem _root_.solution
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    ∃ X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model),
      ∃ Z : MatrixOperator model.space,
        MatrixSdpCanonicalPrimalFeasible params model X ∧
        (∀ g : Polynomial params,
          0 ≤ matrixSdpDualSlackOperator params model Z g) ∧
        Complex.re (Matrix.trace
            (matrixSdpCanonicalObjectiveOperator params model * X)) =
          matrixSdpDualObjective model Z := by
  obtain ⟨X, Z, hX, hZ, hXmax, hZmin, hweak⟩ :=
    matrixSdpCanonicalPrimalDualOptima_exist params model
  let p : ℝ := Complex.re (Matrix.trace
    (matrixSdpCanonicalObjectiveOperator params model * X))
  let d : ℝ := matrixSdpDualObjective model Z
  have hp_eq_d : p = d := by
    refine MIPStarRE.Quantum.conic_primalValue_eq_dualValue_of_fiber_max_dual_min
      (C := matrixSdpCanonicalPrimalImageCone params model)
      (y := (1 : MatrixOperator model.space)) (p := p) (d := d) ?_ ?_ ?_ ?_
    · simpa [p] using matrixSdpCanonicalPrimalImageCone_mem_of_feasible params model X hX
    · intro t hmem
      obtain ⟨Y, hY, hYobj⟩ :=
        (matrixSdpCanonicalPrimalImageCone_identity_mem_iff_exists_feasible_objective
          params model t).mp hmem
      have ht_le : t ≤ p := by
        simpa [p, hYobj] using hXmax Y hY
      exact ht_le
    · intro ψ hψ
      simpa [d] using
        matrixSdpCanonicalFunctionalDualObjective_min_of_matrixDualMin
          params model Z hZmin ψ hψ
    · simpa [p, d] using hweak
  refine ⟨X, Z, hX, hZ, ?_⟩
  simpa [p, d] using hp_eq_d
end MIPStarRE.LDT.SelfImprovement
