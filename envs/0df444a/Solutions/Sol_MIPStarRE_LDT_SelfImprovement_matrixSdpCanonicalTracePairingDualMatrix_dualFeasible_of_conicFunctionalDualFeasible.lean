-- Prove2me | solution 1 for MIPStarRE.LDT.SelfImprovement.matrixSdpCanonicalTracePairingDualMatrix_dualFeasible_of_conicFunctionalDualFeasible
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:59:35.366544+00:00
-- url     : https://prove2.me/submissions/18ab1ac4-3ff1-4b27-9986-9463222706fa

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
Upstream path: MIPStarRE/Quantum/FiniteMatrix/TracePairing.lean
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
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/SelfImprovement/MatrixRealization/Canonical/StrongDuality/Separation.lean (solution of MIPStarRE.LDT.SelfImprovement.matrixSdpCanonicalTracePairingDualMatrix_dualFeasible_of_conicFunctionalDualFeasible);
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
import Theorems.Thm_MIPStarRE_LDT_averageOperatorOverDistribution_nonneg
import Theorems.Thm_MIPStarRE_Quantum_kronecker_nonneg
import Theorems.Thm_MIPStarRE_Quantum_nonneg_of_trace_mul_nonneg_of_isHermitian
import Theorems.Thm_MIPStarRE_Quantum_realTracePairingCLM_selfAdjointPart_apply_of_isHermitian
import Theorems.Thm_MIPStarRE_Quantum_realTracePairingCLM_tracePairingMatrixOfRealCLM

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPStarRE.Quantum
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.Elementwise
open WithLp
set_option backward.isDefEq.respectTransparency false
variable {d : Type*} [Fintype d]
attribute [local instance] MIPStarRE.Quantum.instDecidableEq_definitions_1
/-- The Hermitian representative is Hermitian. -/
theorem hermitianTracePairingMatrixOfRealCLM_isHermitian
    {d : Type*} [Fintype d] [DecidableEq d]
    (ψ : StrongDual ℝ (Op d)) :
    (hermitianTracePairingMatrixOfRealCLM ψ).IsHermitian :=
  (selfAdjointPart ℝ (tracePairingMatrixOfRealCLM ψ)).property
end
end MIPStarRE.Quantum

namespace MIPStarRE.Quantum
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.Elementwise
open WithLp
set_option backward.isDefEq.respectTransparency false
variable {d : Type*} [Fintype d]
attribute [local instance] MIPStarRE.Quantum.instDecidableEq_definitions_1
/-- On Hermitian inputs, the Hermitian representative gives the same functional. -/
theorem hermitianTracePairingMatrixOfRealCLM_apply_of_isHermitian
    {d : Type*} [Fintype d] [DecidableEq d]
    (ψ : StrongDual ℝ (Op d)) {X : Op d} (hX : X.IsHermitian) :
    ψ X = Complex.re (Matrix.trace
      (hermitianTracePairingMatrixOfRealCLM ψ * X)) := by
  calc
    ψ X = realTracePairingCLM (tracePairingMatrixOfRealCLM ψ) X := by
      rw [realTracePairingCLM_tracePairingMatrixOfRealCLM ψ]
    _ = realTracePairingCLM (hermitianTracePairingMatrixOfRealCLM ψ) X := by
      simpa [hermitianTracePairingMatrixOfRealCLM] using
        (realTracePairingCLM_selfAdjointPart_apply_of_isHermitian
          (tracePairingMatrixOfRealCLM ψ) hX).symm
    _ = Complex.re (Matrix.trace (hermitianTracePairingMatrixOfRealCLM ψ * X)) := by
      try rfl
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
/-- The trace of a canonical block matrix is the sum of the traces of its
diagonal blocks. -/
theorem matrixSdpCanonical_trace_eq_sum_diagonalBlock
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) :
    Matrix.trace X =
      ∑ b : MatrixSdpCanonicalBlockIndex params,
        Matrix.trace (matrixSdpCanonicalDiagonalBlock params model X b) := by
  simp only [Matrix.trace, Matrix.diag_apply, matrixSdpCanonicalDiagonalBlock]
  change (∑ x : MatrixSdpCanonicalBlockIndex params × model.space.carrier, X x x) =
    ∑ b : MatrixSdpCanonicalBlockIndex params,
      ∑ i : model.space.carrier, X (b, i) (b, i)
  rw [Fintype.sum_prod_type]
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
/-- The diagonal block of a product with a canonical block-diagonal operator on
the left depends only on the corresponding diagonal block of the right factor. -/
theorem matrixSdpCanonicalDiagonalBlock_blockDiagonal_mul_left (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (B : MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (b : MatrixSdpCanonicalBlockIndex params) :
    matrixSdpCanonicalDiagonalBlock params model
        (matrixSdpCanonicalBlockDiagonal params model B * X) b =
      B b * matrixSdpCanonicalDiagonalBlock params model X b := by
  classical
  ext i j
  unfold matrixSdpCanonicalDiagonalBlock
  simp only [Matrix.mul_apply]
  change (∑ y : MatrixSdpCanonicalBlockIndex params × model.space.carrier,
      matrixSdpCanonicalBlockDiagonal params model B (b, i) y * X y (b, j)) =
    ∑ k : model.space.carrier, B b i k * X (b, k) (b, j)
  rw [Fintype.sum_prod_type]
  simp
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
/-- The trace pairing of a canonical block-diagonal operator with an arbitrary
canonical matrix depends only on the diagonal blocks of the latter.

This is the block calculation used in the converse direction of the canonical
primal SDP identification: when the objective operator is block diagonal, the
off-diagonal blocks of a feasible canonical matrix do not contribute to the
objective value. -/
theorem matrixSdpCanonicalBlockDiagonal_trace_mul_left (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (B : MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) :
    Matrix.trace (matrixSdpCanonicalBlockDiagonal params model B * X) =
      ∑ b : MatrixSdpCanonicalBlockIndex params,
        Matrix.trace (B b * matrixSdpCanonicalDiagonalBlock params model X b) := by
  rw [matrixSdpCanonical_trace_eq_sum_diagonalBlock]
  simp [matrixSdpCanonicalDiagonalBlock_blockDiagonal_mul_left]
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
/-- Feasibility of the canonical block dual constraint recovers the paper dual
inequalities. -/
theorem matrixSdpDualFeasible_of_canonicalDualConstraint_nonneg
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space)
    (hcanonical :
      0 ≤ matrixSdpCanonicalDualOperator params model Z -
        matrixSdpCanonicalObjectiveOperator params model) :
    ∀ g : Polynomial params,
      0 ≤ matrixSdpDualSlackOperator params model Z g :=
  (matrixSdpCanonicalDualConstraint_nonneg_iff_dualFeasible params model Z).mp hcanonical
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
/-- A canonical block-diagonal operator is Hermitian when all diagonal blocks are
Hermitian. -/
theorem matrixSdpCanonicalBlockDiagonal_isHermitian
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (B : MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space)
    (hB : ∀ b, (B b).IsHermitian) :
    (matrixSdpCanonicalBlockDiagonal params model B).IsHermitian := by
  rw [matrixSdpCanonicalBlockDiagonal_eq_reindex_blockDiagonal]
  exact (Matrix.isHermitian_blockDiagonal_iff.mpr hB).reindex
    (Equiv.prodComm model.space.carrier (MatrixSdpCanonicalBlockIndex params))
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
/-- The canonical dual block operator is Hermitian when the paper dual matrix is
Hermitian. -/
theorem matrixSdpCanonicalDualOperator_isHermitian
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space)
    (hZ : Z.IsHermitian) :
    (matrixSdpCanonicalDualOperator params model Z).IsHermitian := by
  rw [matrixSdpCanonicalDualOperator]
  exact matrixSdpCanonicalBlockDiagonal_isHermitian params model
    (matrixSdpCanonicalDualOperatorBlockFamily params model Z) fun _ => hZ
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
/-- The canonical objective block operator is Hermitian. -/
theorem matrixSdpCanonicalObjectiveOperator_isHermitian
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    (matrixSdpCanonicalObjectiveOperator params model).IsHermitian := by
  rw [matrixSdpCanonicalObjectiveOperator]
  refine matrixSdpCanonicalBlockDiagonal_isHermitian params model
    (matrixSdpCanonicalObjectiveBlockFamily params model) ?_
  intro b
  cases b with
  | none => simp [matrixSdpCanonicalObjectiveBlockFamily]
  | some g =>
      exact (Matrix.nonneg_iff_posSemidef.mp
        (matrixAveragedPointOperator_nonneg params model g)).isHermitian
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
/-- The canonical dual slack block operator is Hermitian when the paper dual
matrix is Hermitian. -/
theorem matrixSdpCanonicalDualOperator_sub_objectiveOperator_isHermitian
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space)
    (hZ : Z.IsHermitian) :
    (matrixSdpCanonicalDualOperator params model Z -
      matrixSdpCanonicalObjectiveOperator params model).IsHermitian :=
  (matrixSdpCanonicalDualOperator_isHermitian params model Z hZ).sub
    (matrixSdpCanonicalObjectiveOperator_isHermitian params model)
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
/-- The canonical dual block trace pairing equals the paper dual trace pairing
against the canonical constraint image. -/
theorem matrixSdpCanonicalDualOperator_trace_constraint
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (Z : MatrixOperator model.space) :
    Complex.re (Matrix.trace
        (matrixSdpCanonicalDualOperator params model Z * X)) =
      Complex.re (Matrix.trace
        (Z * matrixSdpCanonicalConstraintOperator params model X)) := by
  congr 1
  rw [matrixSdpCanonicalDualOperator]
  rw [matrixSdpCanonicalBlockDiagonal_trace_mul_left]
  simp only [matrixSdpCanonicalDualOperatorBlockFamily_apply]
  rw [← Matrix.trace_sum]
  rw [← Finset.mul_sum]
  try rfl
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
/-- The canonical equality-constraint image of a positive canonical primal
matrix is positive semidefinite. -/
theorem matrixSdpCanonicalConstraintOperator_nonneg_of_nonnegative
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    {X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)}
    (hX : 0 ≤ X) :
    0 ≤ matrixSdpCanonicalConstraintOperator params model X := by
  unfold matrixSdpCanonicalConstraintOperator
  exact Finset.sum_nonneg fun b _ =>
    matrixSdpCanonicalDiagonalBlock_nonneg params model hX b
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
/-- The canonical equality-constraint image of a positive canonical primal
matrix is Hermitian. -/
theorem matrixSdpCanonicalConstraintOperator_isHermitian_of_nonnegative
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    {X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)}
    (hX : 0 ≤ X) :
    (matrixSdpCanonicalConstraintOperator params model X).IsHermitian :=
  (Matrix.nonneg_iff_posSemidef.mp
    (matrixSdpCanonicalConstraintOperator_nonneg_of_nonnegative params model hX)).isHermitian
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
/-- A trace-pairing separator against every positive semidefinite canonical primal
matrix can be converted into the paper-form dual feasibility inequalities.

This is a separator-conversion lemma for the later zero-gap argument, not the
strong-duality theorem itself. -/
theorem matrixSdpCanonicalDualConstraint_nonneg_of_trace_pairing_nonneg
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space)
    (hHerm :
      (matrixSdpCanonicalDualOperator params model Z -
        matrixSdpCanonicalObjectiveOperator params model).IsHermitian)
    (htrace :
      ∀ X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model),
        0 ≤ X →
          0 ≤ Complex.re (Matrix.trace
            ((matrixSdpCanonicalDualOperator params model Z -
                matrixSdpCanonicalObjectiveOperator params model) * X))) :
    ∀ g : Polynomial params,
      0 ≤ matrixSdpDualSlackOperator params model Z g := by
  have hcanonical :
      0 ≤ matrixSdpCanonicalDualOperator params model Z -
        matrixSdpCanonicalObjectiveOperator params model :=
    MIPStarRE.Quantum.nonneg_of_trace_mul_nonneg_of_isHermitian hHerm htrace
  exact matrixSdpDualFeasible_of_canonicalDualConstraint_nonneg params model Z hcanonical
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
    (model : MatrixSdpRealization params)
    (ψ : StrongDual ℝ (MatrixOperator model.space))
    (hψ : ∀ z ∈ matrixSdpCanonicalPrimalImageCone params model, z.2 ≤ ψ z.1) :
    ∀ g : Polynomial params,
      0 ≤ matrixSdpDualSlackOperator params model
        (MIPStarRE.Quantum.hermitianTracePairingMatrixOfRealCLM ψ) g := by
  let W := MIPStarRE.Quantum.hermitianTracePairingMatrixOfRealCLM ψ
  refine matrixSdpCanonicalDualConstraint_nonneg_of_trace_pairing_nonneg
    params model W ?_ ?_
  · exact matrixSdpCanonicalDualOperator_sub_objectiveOperator_isHermitian
      params model W (MIPStarRE.Quantum.hermitianTracePairingMatrixOfRealCLM_isHermitian ψ)
  · intro X hX
    have hle :
        Complex.re (Matrix.trace
            (matrixSdpCanonicalObjectiveOperator params model * X)) ≤
          Complex.re (Matrix.trace
            (matrixSdpCanonicalDualOperator params model W * X)) := by
      have hmem :=
        matrixSdpCanonicalPrimalImageCone_mem_of_nonnegative params model X hX
      have hfunctional := hψ
        (matrixSdpCanonicalConstraintOperator params model X,
          Complex.re (Matrix.trace
            (matrixSdpCanonicalObjectiveOperator params model * X))) hmem
      have hconstraintHerm :
          (matrixSdpCanonicalConstraintOperator params model X).IsHermitian :=
        matrixSdpCanonicalConstraintOperator_isHermitian_of_nonnegative params model hX
      rw [MIPStarRE.Quantum.hermitianTracePairingMatrixOfRealCLM_apply_of_isHermitian
        ψ hconstraintHerm] at hfunctional
      rwa [← matrixSdpCanonicalDualOperator_trace_constraint params model X W]
        at hfunctional
    rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]
    exact sub_nonneg.mpr hle
end MIPStarRE.LDT.SelfImprovement
