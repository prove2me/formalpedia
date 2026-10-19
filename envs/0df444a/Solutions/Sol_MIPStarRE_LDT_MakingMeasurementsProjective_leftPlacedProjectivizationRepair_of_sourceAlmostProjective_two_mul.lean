-- Prove2me | solution 1 for MIPStarRE.LDT.MakingMeasurementsProjective.leftPlacedProjectivizationRepair_of_sourceAlmostProjective_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T05:07:18.081115+00:00
-- url     : https://prove2.me/submissions/2cc6c7a0-a270-4b03-a77d-2240ae06c1eb

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/MakingMeasurementsProjective/LocalityPreservingRepair.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Preliminaries/DistanceBounds.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Preliminaries/CompletionTransfer.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/RankReduction/Sigma.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayerIdentities/PositiveGram/Sigma.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayerIdentities/ProjectorApprox.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/MakingMeasurementsProjective/SpectralTruncation/Conversion.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/LocalityPreservingRepair.lean (solution of MIPStarRE.LDT.MakingMeasurementsProjective.leftPlacedProjectivizationRepair_of_sourceAlmostProjective_two_mul);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.IsField
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Opposite
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Group.Invertible.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Opposite
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
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Module.Torsion.Pi
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
import Mathlib.Algebra.Opposites
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
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
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
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
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
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Spectrum
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Countable.Defs
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finset.Attach
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Embedding
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.List.Nodup
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Multiset.MapFold
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
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.Data.Set.CoeSort
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Set.Operations
import Mathlib.Data.Set.Restrict
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.Sigma.Basic
import Mathlib.Data.ULift
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Basic
import Mathlib.Logic.Embedding.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Function.Defs
import Mathlib.Logic.IsEmpty.Basic
import Mathlib.Logic.IsEmpty.Defs
import Mathlib.Logic.Nonempty
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Logic.Unique
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Order.Basic
import Mathlib.Order.BooleanAlgebra.Defs
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.MinMax
import Mathlib.Order.Nat
import Mathlib.Order.Notation
import Mathlib.Order.RelClasses
import Mathlib.Order.SetNotation
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.Abel
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
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.Star.Real
import Mathlib.Topology.Bases
import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Continuous
import Mathlib.Topology.ContinuousMap.ContinuousSqrt
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.GDelta
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Separation.Regular
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_SpectralTruncation_ProjectiveNonMeasurement
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_SpectralTruncation_Conversion
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_LocalityPreservingRepair
import Theorems.Thm_MIPStarRE_LDT_MakingMeasurementsProjective_RankReductionWitness_toSigmaRangeQLayer
import Theorems.Thm_MIPStarRE_LDT_MakingMeasurementsProjective_exists_xHat_of_sigmaFinRangeEmbedding_positiveGram
import Theorems.Thm_MIPStarRE_LDT_MakingMeasurementsProjective_pQApprox
import Theorems.Thm_MIPStarRE_LDT_MakingMeasurementsProjective_projectiveLowRankSum_of_roundingWitness
import Theorems.Thm_MIPStarRE_LDT_MakingMeasurementsProjective_projectiveNonMeasurement_of_sourceAlmostProjective_two_mul_full
import Theorems.Thm_MIPStarRE_LDT_MakingMeasurementsProjective_qSDD_leftPlaced_zeroProjSubMeas_le_one
import Theorems.Thm_MIPStarRE_LDT_Preliminaries_sddOpRel_leftPlaced_of_ev_eq
import Theorems.Thm_MIPStarRE_LDT_Preliminaries_stateDependentDistanceOpRel_triangle
import Theorems.Thm_MIPStarRE_LDT_QuantumState_IsNormalized_nonempty
import Theorems.Thm_MIPStarRE_LDT_leftTensor_mul_leftTensor
import Theorems.Thm_MIPStarRE_LDT_leftTensor_sub

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPStarRE.LDT.Preliminaries
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder
open MIPStarRE.LDT
set_option backward.isDefEq.respectTransparency false
/-- Monotonicity of `SDDOpRel` in the error bound. -/
lemma stateDependentDistanceOpRel_mono
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxOpFamily Question Outcome ι) (δ δ' : Error)
    (hle : δ ≤ δ') :
    SDDOpRel ψ 𝒟 A B δ →
    SDDOpRel ψ 𝒟 A B δ' := by
  intro ⟨h⟩
  exact ⟨le_trans h hle⟩
end
end MIPStarRE.LDT.Preliminaries

namespace MIPStarRE.LDT.Preliminaries
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder
open MIPStarRE.LDT
set_option backward.isDefEq.respectTransparency false
/-- Triangle inequality for state-dependent operator distance. -/
lemma sddOpRel_triangle
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B C : IdxOpFamily Question Outcome ι) (δ₁ δ₂ : Error) :
    SDDOpRel ψ 𝒟 A B δ₁ →
    SDDOpRel ψ 𝒟 B C δ₂ →
    SDDOpRel ψ 𝒟 A C (2 * (δ₁ + δ₂)) :=
  stateDependentDistanceOpRel_triangle ψ 𝒟 A B C δ₁ δ₂
end
end MIPStarRE.LDT.Preliminaries

namespace MIPStarRE.LDT.Preliminaries
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder
open MIPStarRE.LDT
set_option backward.isDefEq.respectTransparency false
/-- Monotonicity for `SDDOpRel`. -/
lemma sddOpRel_mono
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxOpFamily Question Outcome ι) (δ δ' : Error) :
    SDDOpRel ψ 𝒟 A B δ → δ ≤ δ' → SDDOpRel ψ 𝒟 A B δ' := by
  intro h hle
  exact stateDependentDistanceOpRel_mono ψ 𝒟 A B δ δ' hle h
end
end MIPStarRE.LDT.Preliminaries

namespace MIPStarRE.LDT.MakingMeasurementsProjective
noncomputable section
open scoped BigOperators MatrixOrder Matrix ComplexOrder
open MIPStarRE.LDT
set_option backward.isDefEq.respectTransparency false
universe uOutcome uι
/-- Assemble the sigma-space `Q/X/Xhat/P` layer from a rank-reduction witness
and the remaining SVD/polar identities for `Xhat`.

The rank-reduction witness supplies the two facts about the family `Q_a` that
enter the matrix decomposition: each `Q_a` is a projection, and
`∑_a Q_a = Q`.  The auxiliary space, the projective measurement `T`, and the
matrix `X` are therefore the canonical finite-enumeration construction attached
to the ranks of the projectors `Q_a`.  As in the paper, the only data still not
constructed here are the coisometry and mixed square-root identities for the
chosen matrix `Xhat`. -/
theorem exists_qxpLayerData_ofRankReductionSigmaRangeAndSvdIdentities
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState ι} {A : Measurement Outcome ι} {ζ : Error}
    {qLayer : QLayerData Outcome ι}
    (hRank : RankReductionWitness ψ A ζ qLayer)
    [Nonempty (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (qLayer.q.outcome a).rank))]
    (xHat : Matrix (sigmaRangeCarrier qLayer.q) ι ℂ)
    (xHat_coisometry : xHat * xHatᴴ =
      (1 : MIPStarRE.Quantum.Op (sigmaRangeCarrier qLayer.q)))
    (xHat_mixed :
      (sigmaFinRangeEmbedding qLayer.q.outcome hRank.projective)ᴴ * xHat =
        CFC.sqrt (QTotal qLayer)) :
    ∃ data : QXPLayerData Outcome ι,
      ∃ hq : data.qLayer = sigmaRangeQLayer qLayer.q,
        hq ▸ data.x =
            (show Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier ι ℂ from
              sigmaFinRangeEmbedding qLayer.q.outcome hRank.projective) ∧
          hq ▸ data.xHat =
            (show Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier ι ℂ from xHat) := by
  classical
  exact
    ⟨QXPLayerData.ofSigmaRangeAndSvdIdentities (q := qLayer.q)
      hRank.projective hRank.sum_eq_total xHat xHat_coisometry xHat_mixed,
      rfl, rfl, rfl⟩
end
end MIPStarRE.LDT.MakingMeasurementsProjective

namespace MIPStarRE.LDT.MakingMeasurementsProjective
noncomputable section
open scoped BigOperators MatrixOrder Matrix ComplexOrder
open MIPStarRE.LDT
set_option backward.isDefEq.respectTransparency false
universe uOutcome uι
/-- Produce the canonical sigma-space QXP layer from the positive-Gram `Xhat`.

This removes the last explicit `Xhat` input from the sigma-space constructor:
the rank-reduction witness supplies the projective `Q` layer and the
rectangular dimension bound, while
`exists_xHat_of_sigmaFinRangeEmbedding_positiveGram` supplies the coisometry
and mixed square-root identities. -/
theorem exists_qxpLayerData_ofRankReductionSigmaRangePositiveGram
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState ι} {A : Measurement Outcome ι} {ζ : Error}
    {qLayer : QLayerData Outcome ι}
    (hRank : RankReductionWitness ψ A ζ qLayer)
    [Nonempty (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (qLayer.q.outcome a).rank))] :
    ∃ xHat : Matrix (sigmaRangeCarrier qLayer.q) ι ℂ,
      xHat * xHatᴴ =
          (1 : MIPStarRE.Quantum.Op (sigmaRangeCarrier qLayer.q)) ∧
        (sigmaFinRangeEmbedding qLayer.q.outcome hRank.projective)ᴴ * xHat =
            CFC.sqrt (QTotal qLayer) ∧
          ∃ data : QXPLayerData Outcome ι,
            ∃ hq : data.qLayer = sigmaRangeQLayer qLayer.q,
              hq ▸ data.x =
                  (show Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier ι ℂ from
                    sigmaFinRangeEmbedding qLayer.q.outcome hRank.projective) ∧
                hq ▸ data.xHat =
                  (show Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier ι ℂ from
                    xHat) := by
  obtain ⟨xHat, hxHat_coisometry, hxHat_mixed⟩ :=
    exists_xHat_of_sigmaFinRangeEmbedding_positiveGram hRank
  obtain ⟨data, hq, hx, hxHat⟩ :=
    exists_qxpLayerData_ofRankReductionSigmaRangeAndSvdIdentities hRank xHat
      hxHat_coisometry hxHat_mixed
  exact ⟨xHat, hxHat_coisometry, hxHat_mixed, data, hq, hx, hxHat⟩
end
end MIPStarRE.LDT.MakingMeasurementsProjective

namespace MIPStarRE.LDT.MakingMeasurementsProjective
noncomputable section
open scoped BigOperators MatrixOrder Matrix ComplexOrder
open MIPStarRE.LDT
set_option backward.isDefEq.respectTransparency false
universe uOutcome uι
/-- Apply `lem:P-Q-approx` to the positive-Gram sigma-space QXP layer.

This is the constructor-facing form of the local `Q -> X -> Xhat -> P` stage.
The rank-reduction witness supplies the sigma-space `X`; the positive-Gram
polar construction supplies `Xhat`; and the theorem concludes the paper's
`P`-versus-`Q` approximation without any external SVD data. -/
lemma pQApprox_ofRankReductionSigmaRangePositiveGram
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error)
    {qLayer : QLayerData Outcome ι}
    (hRank : RankReductionWitness ψ A ζ qLayer)
    [Nonempty (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (qLayer.q.outcome a).rank))]
    (hψ : ψ.IsNormalized)
    (hζ : 0 ≤ ζ) (hζ_small : ζ ≤ 1 / (4 : Error)) :
    ∃ xHat : Matrix (sigmaRangeCarrier qLayer.q) ι ℂ,
      xHat * xHatᴴ =
          (1 : MIPStarRE.Quantum.Op (sigmaRangeCarrier qLayer.q)) ∧
        (sigmaFinRangeEmbedding qLayer.q.outcome hRank.projective)ᴴ * xHat =
            CFC.sqrt (QTotal qLayer) ∧
          ∃ data : QXPLayerData Outcome ι,
            ∃ hq : data.qLayer = sigmaRangeQLayer qLayer.q,
              hq ▸ data.x =
                  (show Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier ι ℂ from
                    sigmaFinRangeEmbedding qLayer.q.outcome hRank.projective) ∧
                hq ▸ data.xHat =
                    (show Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier ι ℂ from
                      xHat) ∧
                  SDDOpRel ψ (uniformDistribution Unit)
                    (constOpFamily data.qLayer.q)
                    (constOpFamily (PFamily data))
                    (30 * zetaQuarterRoot ζ) := by
  obtain ⟨xHat, hxHat_coisometry, hxHat_mixed, data, hq, hx, hxHat⟩ :=
    exists_qxpLayerData_ofRankReductionSigmaRangePositiveGram hRank
  refine ⟨xHat, hxHat_coisometry, hxHat_mixed, data, hq, hx, hxHat, ?_⟩
  exact pQApprox ψ A ζ data hψ hζ hζ_small
    (hq.symm ▸ hRank.toSigmaRangeQLayer)
end
end MIPStarRE.LDT.MakingMeasurementsProjective

namespace MIPStarRE.LDT.MakingMeasurementsProjective.SpectralTruncationStatement
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder
open MIPStarRE.LDT
set_option backward.isDefEq.respectTransparency false
universe uOutcome uι
/-- Paper origin: `references/ldt-paper/orthonormalization.tex:414-531`
(`\label{lem:projective-non-measurement}`; rounding-to-projectors lemma
with `2√ζ` closeness and `(1+2√ζ)·I` total bound).

Convert a spectral-truncation statement back to the rounded-projector
witness consumed by the QXP rank-reduction layer.

**Source:** This is a source-faithful structural conversion of the rounded-family
conclusion of the cited lemma. It does not recover the source almost-projective
estimate, because that estimate is not a field of `SpectralTruncationStatement`;
rank-reduction constructors which need it therefore keep it as a separate
hypothesis. -/
theorem toRoundingToProjectorsWitness {Outcome : Type uOutcome}
    [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState ι} {A : Measurement Outcome ι} {ζ : Error}
    (h : SpectralTruncationStatement ψ A ζ) :
    RoundingToProjectorsWitness ψ A ζ h.roundedFamily where
  projective := h.projective
  closeness := h.closeness
  sum_eq_total := h.sum_eq_total
  total_le := h.total_le
end
end MIPStarRE.LDT.MakingMeasurementsProjective.SpectralTruncationStatement

namespace MIPStarRE.LDT.MakingMeasurementsProjective
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder
open MIPStarRE.LDT
set_option backward.isDefEq.respectTransparency false
universe uOutcome uι
/-- Feed a spectral-truncation statement into the QXP rank-reduction layer.

The statement `SpectralTruncationStatement` remembers the rounded projectors
and their distance from the source measurement.  The rank-reduction witness also
records the source almost-projectivity estimate, so that estimate remains an
explicit hypothesis here.  This is the precise interface needed when the
orthonormalization spectral input is followed by the paper's
`Q -> X -> Xhat -> P` repair layer. -/
lemma projectiveLowRankSum_of_spectralTruncationStatement
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error)
    (hψ : ψ.IsNormalized)
    (hζ : 0 ≤ ζ) (hζ_le : ζ ≤ 1 / 4)
    (hSpectral : SpectralTruncationStatement ψ A ζ)
    (hsource :
      ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ 2 * ζ) :
    ∃ data : QLayerData Outcome ι,
      RankReductionWitness ψ A ζ data :=
  projectiveLowRankSum_of_roundingWitness ψ A ζ hψ hζ hζ_le hSpectral.roundedFamily
    hSpectral.toRoundingToProjectorsWitness hsource
end
end MIPStarRE.LDT.MakingMeasurementsProjective

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder
open MIPStarRE.LDT
set_option backward.isDefEq.respectTransparency false
theorem _root_.solution
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (A : Measurement Outcome ιA) (ζ : Error) (hζ : 0 ≤ ζ)
    (hsource :
      ∑ a, ev ψ
        ((leftLiftedMeasurement (ιB := ιB) A).outcome a -
          (leftLiftedMeasurement (ιB := ιB) A).outcome a *
            (leftLiftedMeasurement (ιB := ιB) A).outcome a) ≤ 2 * ζ) :
    ∃ P : ProjSubMeas Outcome ιA,
      SDDRel ψ (uniformDistribution Unit)
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) A.toSubMeas))
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) P.toSubMeas))
        (orthonormalizationMainLemmaError ζ) := by
  classical
  letI : DecidableEq Outcome := Classical.decEq Outcome
  rcases QuantumState.IsNormalized.nonempty (ι := ιA × ιB) hψ with ⟨⟨i, j⟩⟩
  letI : Nonempty ιA := ⟨i⟩
  letI : Nonempty ιB := ⟨j⟩
  let φ : QuantumState ιA := leftMarginalState ψ
  have hφ : φ.IsNormalized := leftMarginalState_isNormalized hψ
  have hterm : ∀ a : Outcome,
      ev ψ
        ((leftLiftedMeasurement (ιB := ιB) A).outcome a -
          (leftLiftedMeasurement (ιB := ιB) A).outcome a *
            (leftLiftedMeasurement (ιB := ιB) A).outcome a) =
      ev φ (A.outcome a - A.outcome a * A.outcome a) := by
    intro a
    simpa [φ, leftLiftedMeasurement, leftPlacedSubMeas, leftTensor_sub,
      leftTensor_mul_leftTensor] using
      (leftMarginal_ev_eq (ψ := ψ) (X := A.outcome a - A.outcome a * A.outcome a))
  have hsourceLocal :
      ∑ a, ev φ (A.outcome a - A.outcome a * A.outcome a) ≤ 2 * ζ := by
    simpa [hterm] using hsource
  by_cases hζ_small : ζ ≤ 1 / (4 : Error)
  · have hprojective : projectiveNonMeasurement φ A ζ :=
      projectiveNonMeasurement_of_sourceAlmostProjective_two_mul_full
        φ A ζ hφ hsourceLocal
    obtain ⟨R, hR⟩ := hprojective
    have hSpectralLocal : SpectralTruncationStatement φ A ζ :=
      spectralTruncationStatement_of_witness φ A ζ R hR
    obtain ⟨qLayer, hRank⟩ :=
      projectiveLowRankSum_of_spectralTruncationStatement φ A ζ hφ hζ
        hζ_small hSpectralLocal hsourceLocal
    by_cases hsigma : Nonempty (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (qLayer.q.outcome a).rank))
    · letI := hsigma
      obtain ⟨_xHat, _hxHat_coisometry, _hxHat_mixed, data, hq, _hx, _hxHat, hQP⟩ :=
        pQApprox_ofRankReductionSigmaRangePositiveGram φ A ζ hRank hφ hζ hζ_small
      have hAQ :
          SDDOpRel φ (uniformDistribution Unit)
            (constOpFamily (A.toSubMeas : OpFamily Outcome ιA))
            (constOpFamily data.qLayer.q) (roundingToProjectiveError ζ) := by
        simpa [hq] using hRank.toSigmaRangeQLayer.closeness
      have hAP_local :
          SDDOpRel φ (uniformDistribution Unit)
            (constOpFamily (A.toSubMeas : OpFamily Outcome ιA))
            (constOpFamily (PFamily data)) (orthonormalizationMainLemmaError ζ) := by
        exact MIPStarRE.LDT.Preliminaries.sddOpRel_mono φ (uniformDistribution Unit)
          (constOpFamily (A.toSubMeas : OpFamily Outcome ιA))
          (constOpFamily (PFamily data))
          (2 * (roundingToProjectiveError ζ + 30 * zetaQuarterRoot ζ))
          (orthonormalizationMainLemmaError ζ)
          (MIPStarRE.LDT.Preliminaries.sddOpRel_triangle φ (uniformDistribution Unit)
            (constOpFamily (A.toSubMeas : OpFamily Outcome ιA))
            (constOpFamily data.qLayer.q)
            (constOpFamily (PFamily data))
            (roundingToProjectiveError ζ) (30 * zetaQuarterRoot ζ) hAQ hQP)
          (projectivizationRepair_small_error_bound hζ hζ_small)
      have hLifted :
          SDDOpRel ψ (uniformDistribution Unit)
            (fun _ => OpFamily.leftPlacedOpFamily (ιB := ιB) (A.toSubMeas : OpFamily Outcome ιA))
            (fun _ => OpFamily.leftPlacedOpFamily (ιB := ιB) (PFamily data))
            (orthonormalizationMainLemmaError ζ) := by
        refine MIPStarRE.LDT.Preliminaries.sddOpRel_leftPlaced_of_ev_eq
          (ιA := ιA) (ιB := ιB) ψ φ (uniformDistribution Unit)
          (constOpFamily (A.toSubMeas : OpFamily Outcome ιA))
          (constOpFamily (PFamily data))
          (orthonormalizationMainLemmaError ζ) ?_ hAP_local
        intro X
        exact leftMarginal_ev_eq ψ X
      exact ⟨qxpProjSubMeas data,
        sddRel_of_leftPlaced_sddOpRel
          (R := PFamily data) (P := qxpProjSubMeas data)
          (fun a => by
            rw [qxpProjSubMeas_outcome]
            rfl)
          hLifted⟩
    · have hQzero_rank : ∀ a : Outcome, (qLayer.q.outcome a).rank = 0 := by
        intro a
        by_contra hrank
        have hpos : 0 < (qLayer.q.outcome a).rank := Nat.pos_of_ne_zero hrank
        have : Nonempty (FiniteHilbertSpace.sigmaFinCarrier
            (fun a : Outcome => (qLayer.q.outcome a).rank)) := by
          refine ⟨⟨Fintype.equivFin Outcome a, ⟨0, ?_⟩⟩⟩
          simpa [Fintype.equivFin] using hpos
        exact hsigma this
      have hQzero : ∀ a : Outcome, qLayer.q.outcome a = 0 := by
        intro a
        exact matrix_eq_zero_of_rank_eq_zero (qLayer.q.outcome a) (hQzero_rank a)
      have hQ_lifted :
          SDDOpRel ψ (uniformDistribution Unit)
            (fun _ => OpFamily.leftPlacedOpFamily (ιB := ιB) (A.toSubMeas : OpFamily Outcome ιA))
            (fun _ => OpFamily.leftPlacedOpFamily (ιB := ιB) qLayer.q)
            (roundingToProjectiveError ζ) := by
        refine MIPStarRE.LDT.Preliminaries.sddOpRel_leftPlaced_of_ev_eq
          (ιA := ιA) (ιB := ιB) ψ φ (uniformDistribution Unit)
          (constOpFamily (A.toSubMeas : OpFamily Outcome ιA))
          (constOpFamily qLayer.q) (roundingToProjectiveError ζ) ?_ hRank.closeness
        intro X
        exact leftMarginal_ev_eq ψ X
      exact ⟨zeroProjSubMeas (Outcome := Outcome) (ι := ιA),
        ⟨le_trans
          (sddRel_of_leftPlaced_sddOpRel
            (R := qLayer.q) (P := zeroProjSubMeas (Outcome := Outcome) (ι := ιA))
            hQzero hQ_lifted).squaredDistanceBound
          (roundingToProjectiveError_le_orthonormalizationMainLemmaError
            hζ hζ_small)⟩⟩
  · refine ⟨zeroProjSubMeas (Outcome := Outcome) (ι := ιA), ?_⟩
    have hzero :
        qSDD ψ (leftPlacedSubMeas (ιB := ιB) A.toSubMeas)
          (leftPlacedSubMeas (ιB := ιB)
            (zeroProjSubMeas (Outcome := Outcome) (ι := ιA)).toSubMeas) ≤ 1 :=
      qSDD_leftPlaced_zeroProjSubMeas_le_one ψ hψ A.toSubMeas
    have hbound : 1 ≤ orthonormalizationMainLemmaError ζ :=
      one_le_orthonormalizationMainLemmaError_of_quarter_lt (lt_of_not_ge hζ_small)
    constructor
    simpa [sddError, avgOver, uniformDistribution, constSubMeasFamily]
      using (le_trans hzero hbound)
end MIPStarRE.LDT.MakingMeasurementsProjective
