-- Prove2me | solution 1 for OAI.DukePrimeDegree.hasCyclicRayRealizations_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-14T04:50:19.77485+00:00
-- url     : https://prove2.me/submissions/c6de1ca1-73c6-4a0d-9672-7c9e3b297775

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Subring
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Group.Submonoid.Units
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.GroupWithZero.Action.Prod
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.LinearMap.Polynomial
import Mathlib.Algebra.Module.MinimalAxioms
import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Module.Shrink
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.MonoidAlgebra.Lift
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Group.Cyclic
import Mathlib.Algebra.Order.Hom.Units
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Algebra.Order.WithTop.Untop0
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Ring.Pi
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Normed.Algebra.GelfandMazur
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.Normed.Field.ProperSpace
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Finsupp
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finsupp.Fintype
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.WithZero
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.ZMod.Units
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.FieldTheory.Galois.Notation
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.PrimeField
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.FreeGroup.GeneratorEquiv
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.QuotientGroup.Finite
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Torsion
import Mathlib.GroupTheory.Transfer
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.NumberTheory.Cyclotomic.Discriminant
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
import Mathlib.NumberTheory.NumberField.Completion.Ramification
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.NumberField.Units.Regulator
import Mathlib.NumberTheory.Ostrowski
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.ValuativeRel
import Mathlib.NumberTheory.Padics.WithVal
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.RepresentationTheory.Homological.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.RepresentationTheory.Homological.GroupHomology.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.AlgebraTower
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.ClassGroup.ExtendedHom
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.FormalGroup.Basic
import Mathlib.RingTheory.FractionalIdeal.Norm
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.MvPowerSeries.Expand
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.MvPowerSeries.Order
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.MvPowerSeries.Trunc
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Polynomial.ContentIdeal
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Kernel
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Valuation.Archimedean
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.WittVector.Compare
import Mathlib.RingTheory.WittVector.Complete
import Mathlib.RingTheory.WittVector.FrobeniusFractionField
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.FilterBasis
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Topology.Algebra.Group.TopologicalAbelianization
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.LinearTopology
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.Compact
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Compact
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Valued.ValuativeRel
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Homeomorph.TransferInstance
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.UniformSpace.AbsoluteValue
import Mathlib.Topology.WithTopology
import Definitions.Def_OAIQ244Duke110
import Definitions.Def_OAIQ244Duke111
import Theorems.Thm_GlobalClassFieldTheory_Reciprocity_ramifiedInfinitePlaceOverextension_globalNormResidueOfEmbedding_neg_one
import Theorems.Thm_OAI_DukePrimeDegree_idealCharacter_kernelLaw_of_even_modulus

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_RayClass_FullModulus
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RayClass.Modulus.infiniteCongruenceSubgroupFiniteIndex _root_.RayClass.approximationCompletionTopologicalSpace _root_.RayClass.congruenceSubgroupFiniteIndex _root_.RayClass.finiteCongruenceSubgroupFiniteRelIndex _root_.RayClass.ideleCongruenceSubgroupFiniteRelIndex _root_.RayClass.ideleCongruenceSupPrincipalFiniteIndex _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductor_apply _root_.GlobalClassFieldTheory.GlobalClassFields.idealArtinMap_primeToIdealMap _root_.GlobalClassFieldTheory.GlobalClassFields.idealRayProjection_finitePrimeIdele _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNormDefiningModulus_apply _root_.GlobalClassFieldTheory.GlobalClassFields.normQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqNormQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.primeToIdealMap_finitePrimeIdele _root_.GlobalClassFieldTheory.GlobalClassFields.rayClassGroupEquivIdealRayClassGroup_mk_primeTo _root_.GlobalClassFieldTheory.GlobalClassFields.rayClassGroupEquivIdeleQuotient_mk_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.arithmeticIdealArtinGaloisMap_apply _root_.GlobalClassFieldTheory.IdealClassFieldTheory.arithmeticIdealArtinGaloisMap_eq_inv_idealArtinGaloisMap _root_.GlobalClassFieldTheory.IdealClassFieldTheory.arithmeticIdealArtinGaloisMap_ker _root_.GlobalClassFieldTheory.IdealClassFieldTheory.arithmeticIdealClassQuotientEquivGaloisGroup_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealArtinGaloisMap_apply _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealArtinGaloisMap_ker _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealClassQuotientEquivGaloisGroup_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealClassQuotientEquivNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.rayClassToNormQuotient_mk _root_.IdeleGroup.modulusOfFinset_apply _root_.IdeleGroup.modulusOfFinset_support _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.approximationEmbedding_finite _root_.RayClass.approximationEmbedding_infinite _root_.RayClass.idealNormLiftedModulusExponent_eq_zero_of_not_mem _root_.RayClass.idealNormLiftedModulus_apply _root_.RayClass.mem_idealNormLiftedModulus_support_iff _root_.RayClass.mem_primeToModulusIdeals_iff _root_.RayClass.primeToModulusIdealNorm_coe _root_.RayClass.primeToModulusIdeal_coe _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.quotientRaySubgroupEquivIdealRayClassGroup_mk _root_.RayClass.quotientRaySubgroupEquivIdeleRayQuotient_mk _root_.RayClass.rationalFiniteModulus_apply _root_.RayClass.rationalModulus_finitePart_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Ray moduli with selected real places

A ray modulus consists of a finite modulus together with the real places at
which positivity is imposed.  This file defines the corresponding idèle and
idèle-class congruence subgroups without fixing an archimedean convention.
-/

open scoped Classical NumberField
open NumberField IsDedekindDomain

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

namespace RayClass

namespace Modulus

theorem ext {m n : Modulus K}
    (hfinite : m.finitePart = n.finitePart)
    (hinfinite : m.infinitePart = n.infinitePart) :
    m = n := by
  cases m
  cases n
  cases hfinite
  cases hinfinite
  rfl

instance instPartialOrder : PartialOrder (Modulus K) where
  le_refl m := ⟨le_rfl, fun _ hx => hx⟩
  le_trans m n p hmn hnp :=
    ⟨hmn.1.trans hnp.1, fun x hx => hnp.2 (hmn.2 hx)⟩
  le_antisymm m n hmn hnm :=
    ext (le_antisymm hmn.1 hnm.1) (by
      apply Finset.ext
      intro x
      exact ⟨fun hx => hmn.2 hx, fun hx => hnm.2 hx⟩)
noncomputable instance instSemilatticeInf : SemilatticeInf (Modulus K) where
  inf m n :=
    { finitePart := m.finitePart ⊓ n.finitePart
      infinitePart := m.infinitePart ∩ n.infinitePart }
  inf_le_left _ _ :=
    ⟨inf_le_left, fun _ hx => (Finset.mem_inter.mp hx).1⟩
  inf_le_right _ _ :=
    ⟨inf_le_right, fun _ hx => (Finset.mem_inter.mp hx).2⟩
  le_inf _ _ _ hmn hmp :=
    ⟨le_inf hmn.1 hmp.1,
      fun _ hx => Finset.mem_inter.mpr ⟨hmn.2 hx, hmp.2 hx⟩⟩

noncomputable instance instSemilatticeSup : SemilatticeSup (Modulus K) where
  sup m n :=
    { finitePart := m.finitePart ⊔ n.finitePart
      infinitePart := m.infinitePart ∪ n.infinitePart }
  le_sup_left _ _ :=
    ⟨le_sup_left, fun _ hx => Finset.mem_union.mpr (Or.inl hx)⟩
  le_sup_right _ _ :=
    ⟨le_sup_right, fun _ hx => Finset.mem_union.mpr (Or.inr hx)⟩
  sup_le _ _ _ hmp hnp :=
    ⟨sup_le hmp.1 hnp.1, fun _ hx => by
      rcases Finset.mem_union.mp hx with hx | hx
      · exact hmp.2 hx
      · exact hnp.2 hx⟩

@[simp]
theorem eraseRealPlaces_empty (m : Modulus K) :
    m.eraseRealPlaces ∅ = m := by
  apply ext
  · rfl
  · exact Finset.sdiff_empty

@[simp]
theorem eraseRealPlaces_insert
    (m : Modulus K) (s : Finset (RealPlace K)) (v : RealPlace K) :
    m.eraseRealPlaces (insert v s) =
      (m.eraseRealPlaces s).eraseRealPlace v := by
  apply ext
  · rfl
  · exact Finset.sdiff_insert _ _ _

end Modulus

end RayClass
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_RayClass_Topology
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFiniteAbstractConjugate_normal _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFiniteResidueConjugate_normal _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.abelianIntermediateField_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsCyclotomicExtension _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormExponentNeZero _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldAbsoluteFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerExtensionSubgroupNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.cyclotomicUnramifiedGeometricMaxExtensionNormal _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.chosenFinitePlaceCompletionAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The congruence topology on the idele class group

The local higher-unit groups are open,
the ray congruence subgroups are open (and hence closed) of finite index, and
the congruence subgroups are cofinal among the closed finite-index subgroups
of the idele class group.
-/

open scoped Classical NumberField RestrictedProduct WithZero
open NumberField IsDedekindDomain
open Topology

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace RayClass

/-- Finite congruence subgroups are contravariant in the finite modulus. -/
theorem finiteCongruenceSubgroup_antitone
    {m n : FiniteModulus K} (hmn : m ≤ n) :
    finiteCongruenceSubgroup n ≤ finiteCongruenceSubgroup m := by
  intro a ha
  rw [mem_finiteCongruenceSubgroup_iff] at ha ⊢
  intro v
  exact localHigherUnitGroup_antitone v (hmn v) (ha v)

/-- Infinite congruence subgroups are contravariant in the selected real
places of a full modulus. -/
theorem Modulus.infiniteCongruenceSubgroup_antitone
    {m n : Modulus K} (hmn : m ≤ n) :
    n.infiniteCongruenceSubgroup ≤ m.infiniteCongruenceSubgroup := by
  intro a ha
  rw [Modulus.mem_infiniteCongruenceSubgroup_iff] at ha ⊢
  intro v hv
  exact ha v (hmn.2 hv)

/-- Idèle congruence subgroups are contravariant in a full modulus. -/
theorem Modulus.ideleCongruenceSubgroup_antitone
    {m n : Modulus K} (hmn : m ≤ n) :
    n.ideleCongruenceSubgroup ≤ m.ideleCongruenceSubgroup := by
  intro a ha
  rw [Modulus.mem_ideleCongruenceSubgroup_iff] at ha ⊢
  exact ⟨Modulus.infiniteCongruenceSubgroup_antitone hmn ha.1,
    finiteCongruenceSubgroup_antitone hmn.1 ha.2⟩

/-- Ray congruence subgroups are contravariant in a full modulus. -/
theorem Modulus.congruenceSubgroup_antitone
    {m n : Modulus K} (hmn : m ≤ n) :
    n.congruenceSubgroup ≤ m.congruenceSubgroup := by
  unfold Modulus.congruenceSubgroup
  apply Subgroup.map_mono
  exact sup_le
    ((Modulus.ideleCongruenceSubgroup_antitone hmn).trans le_sup_left)
    le_sup_right

end RayClass
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Extension_InfiniteOnePlaceBaseNorm
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsCyclotomicExtension _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormExponentNeZero _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldAbsoluteFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerExtensionSubgroupNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.cyclotomicUnramifiedGeometricMaxExtensionNormal _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitKummerCoordinatePlace_below _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseEquiv_coe _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassField_algebraMap_original _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseEquiv_coe _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassField_algebraMap_original _root_.GlobalClassFieldTheory.GlobalClassFields.idealArtinMap_primeToIdealMap _root_.GlobalClassFieldTheory.GlobalClassFields.idealRayProjection_finitePrimeIdele _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNormQuotientTowerMap_mk _root_.GlobalClassFieldTheory.GlobalClassFields.mem_cyclotomicKummerNormSupportAbove_iff _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_rayPrimeClass _root_.GlobalClassFieldTheory.GlobalClassFields.normQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqNormQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.primeToIdealMap_finitePrimeIdele _root_.GlobalClassFieldTheory.GlobalClassFields.rayClassGroupEquivIdealRayClassGroup_mk_primeTo _root_.GlobalClassFieldTheory.GlobalClassFields.rayClassGroupEquivIdeleQuotient_mk_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassField_algebraMap_original _root_.GlobalClassFieldTheory.IdealClassFieldTheory.arithmeticIdealArtinGaloisMap_apply _root_.GlobalClassFieldTheory.IdealClassFieldTheory.arithmeticIdealArtinGaloisMap_eq_inv_idealArtinGaloisMap _root_.GlobalClassFieldTheory.IdealClassFieldTheory.arithmeticIdealArtinGaloisMap_ker _root_.GlobalClassFieldTheory.IdealClassFieldTheory.arithmeticIdealClassQuotientEquivGaloisGroup_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealArtinGaloisMap_apply _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealArtinGaloisMap_ker _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealClassQuotientEquivGaloisGroup_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealClassQuotientEquivNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.rayClassToNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom_mk _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicRestriction_infiniteGlobalArtinMonoidHom _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldGlobalNormResidueMonoidHom_fixed_apply _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalArtinMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalArtinMonoidHom_finitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalArtinMonoidHom_infinitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueAbelianizationMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueAbelianizationMonoidHom_ker _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueContinuousMulEquiv_apply _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_ker _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalReciprocityContinuousMulEquiv_globalNormResidue _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalReciprocityContinuousMulEquiv_symm_mk _root_.GlobalClassFieldTheory.Reciprocity.cyclotomicZHatNormCompositeContinuous_apply _root_.GlobalClassFieldTheory.Reciprocity.cyclotomicZHatNormCompositeInMulNatRangeContinuous_apply _root_.GlobalClassFieldTheory.Reciprocity.cyclotomicZHatNormComposite_apply _root_.GlobalClassFieldTheory.Reciprocity.finitePlaceBelow_automorphismCyclicFixedPlace _root_.GlobalClassFieldTheory.Reciprocity.finitePlaceGlobalArtinMonoidHom_finitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.finitePlaceSeparableClosureDecompositionRestriction_coe _root_.GlobalClassFieldTheory.Reciprocity.globalArtinMonoidHom_finitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.globalArtinMonoidHom_ideleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.globalArtinMonoidHom_infinitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.globalArtinMonoidHom_relativeIdeleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_relativeIdeleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationContinuousMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationContinuousMulEquiv_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationIdeleMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationIdeleMonoidHom_eq_one_iff _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationIdeleMonoidHom_ker _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationIdeleMonoidHom_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationMonoidHom_eq_one_iff _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationMonoidHom_ker _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueContinuousMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueContinuousMulEquiv_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueMonoidHomOfEmbedding_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueMonoidHom_eq_one_iff _root_.GlobalClassFieldTheory.Reciprocity.globalReciprocityAbelianizationContinuousMulEquiv_apply _root_.GlobalClassFieldTheory.Reciprocity.globalReciprocityContinuousMulEquiv_apply _root_.GlobalClassFieldTheory.Reciprocity.infiniteGlobalArtinMonoidHom_abstractFixedFieldCyclotomic_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceGlobalArtinMonoidHom_finitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.mem_globalArtinFiniteSupport_iff _root_.GlobalClassFieldTheory.Reciprocity.normalizedCyclotomicZHatIdeleClassValueContinuousMul_mk _root_.GlobalClassFieldTheory.Reciprocity.normalizedCyclotomicZHatIdeleClassValueContinuous_mk _root_.GlobalClassFieldTheory.Reciprocity.normalizedCyclotomicZHatIdeleClassValue_range _root_.GlobalClassFieldTheory.Reciprocity.normalizedCyclotomicZHatIdeleValueContinuousMul_apply _root_.GlobalClassFieldTheory.Reciprocity.normalizedCyclotomicZHatIdeleValueContinuous_apply _root_.GlobalClassFieldTheory.Reciprocity.normalizedCyclotomicZHatIdeleValue_principalIdele_eq_zero _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatCompositumRestriction_infiniteGlobalArtinMonoidHom _root_.GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient_finiteNormClass _root_.GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient_ideleClass _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient_finiteNormClass _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient_ideleClass _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePlaceExtensionToSeparableClosure_algebraMap _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionGlobalArtin_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom_ideleClassNorm _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom_mk _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionNormQuotientArtinMonoidHom_mk _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractFixedFieldIdeleClassEquivFixed_coe _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexificationGlobalArtin_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicIdeleClassValuationData_valuationAt_fixed_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatGlobalArtin_rationalIdeleArchimedeanPart _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatGlobalArtin_rationalPositiveArchimedeanIdele _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleClassNormComposite_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleClassValueContinuousMul_mk _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleClassValueContinuous_mk _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleClassValue_range _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleValueContinuousAdd_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleValueReduction_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleValue_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleValue_principalIdele_eq_one _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleValue_rationalIdeleArchimedeanPart _root_.GlobalClassFieldTheory.Reciprocity.rationalFiniteNormQuotientEquivIdeleClassNormQuotient_finiteNormClass _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleArchimedeanPart_finiteComponent _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleArchimedeanPart_infiniteComponent _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleFinitePart_finiteComponent _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleFinitePart_infiniteComponent _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateIdeleClassEquivGaloisFixed_coe _root_.GlobalClassFieldTheory.Reciprocity.rationalPositiveArchimedeanIdele_finiteComponent _root_.GlobalClassFieldTheory.Reciprocity.restrictNormalHom_infiniteGlobalArtinMonoidHom _root_.GlobalClassFieldTheory.Reciprocity.restrictNormalHom_infiniteGlobalArtinMonoidHom_of_numberField _root_.GlobalClassFieldTheory.Reciprocity.restrictNormalHom_rationalCyclotomicZHatGlobalArtin _root_.IdeleClassGroup.normOneNorm_apply _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.extension_finiteComponent _root_.IdeleGroup.extension_principalIdele _root_.IdeleGroup.extension_self _root_.IdeleGroup.fractionalIdeal_finitePrimeIdele _root_.IdeleGroup.idealClass_finitePrimeIdele _root_.IdeleGroup.ideleNormContinuousMonoidHom_apply _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.idealNormExponentMap_apply _root_.RayClass.idealNormLiftedModulusExponent_eq_zero_of_not_mem _root_.RayClass.mem_idealNormLiftedModulus_support_iff _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk _root_.IdeleGroup.idealClass_classRepresentative _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.finitePlaceBelow_finitePlaceEquiv _root_.ideleClassCongr_ideleClassNorm _root_.ideleClassCongr_mk _root_.ideleClassCongr_refl _root_.ideleClassExtension_mk _root_.ideleClassExtension_self _root_.ideleCongr_finiteComponent _root_.ideleCongr_principalIdele _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe _root_.intermediateClassNormQuotientBaseChangeMulEquiv_mk _root_.mem_finitePlaceDecompositionGroup_iff _root_.mem_finitePlacesAbove_iff _root_.ordinaryIdeleClassNormQuotientCongrOfAlgEquiv_mk _root_.ordinaryIdeleClassNorm_relativeIdeleClassBaseChange _root_.relativeIdeleClassBaseChangeMulEquiv_classInclusion _root_.relativeIdeleClassBaseChangeMulEquiv_congrOfAlgEquiv _root_.relativeIdeleClassBaseChangeMulEquiv_mk _root_.relativeIdeleClassCongrOfAlgEquiv_ideleClassNorm _root_.relativeIdeleClassCongr_ideleClassNorm _root_.relativeIdeleCongr_norm _root_.restrictAbsoluteValueExtensionToIntermediate_apply _root_.towerRelativeIdeleViaOrdinaryMulEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Norms of base units supported at one infinite place

For an infinite place `W` of an extension field, a unit of the
completion at the place below `W` can be extended to `W` and inserted
as a one-place idele.  Its ordinary idele norm remains supported at the
place below `W`; the surviving component is the corresponding local
degree power.
-/

open scoped BigOperators NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace IdeleGroup

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

/-- The idele norm of a base-completion unit supported at one
extension infinite place is the corresponding local-degree power
supported at the place below it. -/
theorem norm_infinitePlaceIdele_infinitePlaceBaseUnitExtension
    (W : InfinitePlace L)
    (x :
      ((_root_.infinitePlaceBelow (K := K) W).Completion)ˣ) :
    norm K L
        (infinitePlaceIdele W
          (infinitePlaceBaseUnitExtension
            (K := K) (L := L) W x)) =
      infinitePlaceIdele
        (_root_.infinitePlaceBelow (K := K) W)
        (x ^ infinitePlaceCompletionDegree
          (K := K) (L := L) W) := by
  classical
  let v := _root_.infinitePlaceBelow (K := K) W
  let W₀ :
      {U : InfinitePlace L //
        _root_.infinitePlaceBelow (K := K) U = v} :=
    ⟨W, rfl⟩
  apply Prod.ext
  · apply ContinuousMulEquiv.piUnits.injective
    funext r
    change
      infiniteComponent r
          (norm K L
            (infinitePlaceIdele W
              (infinitePlaceBaseUnitExtension
                (K := K) (L := L) W x))) =
        infiniteComponent r
          (infinitePlaceIdele v
            (x ^ infinitePlaceCompletionDegree
              (K := K) (L := L) W))
    by_cases hr : r = v
    · subst r
      rw [infiniteComponent_norm_eq_prod,
        infinitePlaceIdele_infiniteComponent_same]
      rw [Finset.prod_eq_single W₀]
      · rw [infinitePlaceIdele_infiniteComponent_same]
        let : W.1.LiesOver v.1 := ⟨rfl⟩
        let : Algebra v.Completion W.Completion :=
          (NumberField.LiesOver.completionMap (v := v) (w := W)).toAlgebra
        have hmap :
            algebraMap v.Completion W.Completion =
              NumberField.LiesOver.completionMap (v := v) (w := W) :=
          RingHom.algebraMap_toAlgebra _
        change
          LocalFieldTheory.normUnits v.Completion W.Completion
              (Units.map
                (NumberField.LiesOver.completionMap (v := v) (w := W)).toMonoidHom
                x) =
            x ^ Module.finrank v.Completion W.Completion
        rw [← hmap]
        simpa [
          LocalFieldTheory.IsNonarchimedeanLocalField.mapBaseUnitsToExtensionUnits,
          MonoidHom.id_apply] using
          (LocalFieldTheory.IsNonarchimedeanLocalField.normUnits_algebraMap_base
            (K := v.Completion) (L := W.Completion) x)
      · intro U _ hU
        have hUW : U.1 ≠ W := by
          intro h
          apply hU
          exact Subtype.ext h
        rw [
          infinitePlaceIdele_infiniteComponent_of_ne
            W U.1
            (infinitePlaceBaseUnitExtension
              (K := K) (L := L) W x)
            hUW,
          map_one]
      · simp
    · rw [
        infiniteComponent_norm_eq_prod,
        infinitePlaceIdele_infiniteComponent_of_ne
          v r
          (x ^ infinitePlaceCompletionDegree
            (K := K) (L := L) W)
          hr]
      apply Finset.prod_eq_one
      intro U _
      have hUW : U.1 ≠ W := by
        intro h
        apply hr
        calc
          r = _root_.infinitePlaceBelow (K := K) U.1 :=
            U.2.symm
          _ = v := by rw [h]
      rw [
        infinitePlaceIdele_infiniteComponent_of_ne
          W U.1
          (infinitePlaceBaseUnitExtension
            (K := K) (L := L) W x)
          hUW,
        map_one]
  · apply RestrictedProduct.ext
    intro q
    change
      finiteComponent q
          (norm K L
            (infinitePlaceIdele W
              (infinitePlaceBaseUnitExtension
                (K := K) (L := L) W x))) =
        finiteComponent q
          (infinitePlaceIdele v
            (x ^ infinitePlaceCompletionDegree
              (K := K) (L := L) W))
    rw [finiteComponent_norm_eq_prod,
      infinitePlaceIdele_finiteComponent]
    apply Finset.prod_eq_one
    intro U _
    rw [infinitePlaceIdele_finiteComponent, map_one]

/-- If the chosen infinite place is unramified over the base, the
completed extension has degree one, so the norm of the extended
one-place idele is exactly the original one-place idele. -/
theorem norm_infinitePlaceIdele_infinitePlaceBaseUnitExtension_of_isUnramified
    (W : InfinitePlace L)
    (hW : W.IsUnramified K)
    (x :
      ((_root_.infinitePlaceBelow (K := K) W).Completion)ˣ) :
    norm K L
        (infinitePlaceIdele W
          (infinitePlaceBaseUnitExtension
            (K := K) (L := L) W x)) =
      infinitePlaceIdele
        (_root_.infinitePlaceBelow (K := K) W) x := by
  let v := _root_.infinitePlaceBelow (K := K) W
  let : W.1.LiesOver v.1 := ⟨rfl⟩
  let : Algebra v.Completion W.Completion :=
    (NumberField.LiesOver.completionMap (v := v) (w := W)).toAlgebra
  have hDegree :
      Module.finrank v.Completion W.Completion = 1 :=
    InfinitePlace.IsUnramified.finrank_eq_one
      v hW
  rw [
    norm_infinitePlaceIdele_infinitePlaceBaseUnitExtension,
    show infinitePlaceCompletionDegree
        (K := K) (L := L) W = 1 by
      simpa only [infinitePlaceCompletionDegree, v] using hDegree,
    pow_one]

/-- The degree-one one-place norm equality descends verbatim to the
actual idele class groups. -/
theorem ideleClassNorm_infinitePlaceIdeleClass_infinitePlaceBaseUnitExtension_of_isUnramified
    (W : InfinitePlace L)
    (hW : W.IsUnramified K)
    (x :
      ((_root_.infinitePlaceBelow (K := K) W).Completion)ˣ) :
    _root_.ideleClassNorm K L
        (infinitePlaceIdeleClass W
          (infinitePlaceBaseUnitExtension
            (K := K) (L := L) W x)) =
      infinitePlaceIdeleClass
        (_root_.infinitePlaceBelow (K := K) W) x := by
  change
    _root_.ideleClassNorm K L
        (QuotientGroup.mk'
          (principalSubgroup L)
          (infinitePlaceIdele W
            (infinitePlaceBaseUnitExtension
              (K := K) (L := L) W x))) =
      QuotientGroup.mk'
        (principalSubgroup K)
        (infinitePlaceIdele
          (_root_.infinitePlaceBelow (K := K) W) x)
  rw [
    _root_.ideleClassNorm_mk,
    norm_infinitePlaceIdele_infinitePlaceBaseUnitExtension_of_isUnramified
      (K := K) (L := L) W hW x]

/-- Idele-class form of the one-place norm equality at a real place
upstairs. -/
theorem ideleClassNorm_infinitePlaceIdeleClass_infinitePlaceBaseUnitExtension_of_isReal
    (W : InfinitePlace L)
    (hWReal : W.IsReal)
    (x :
      ((_root_.infinitePlaceBelow (K := K) W).Completion)ˣ) :
    _root_.ideleClassNorm K L
        (infinitePlaceIdeleClass W
          (infinitePlaceBaseUnitExtension
            (K := K) (L := L) W x)) =
      infinitePlaceIdeleClass
        (_root_.infinitePlaceBelow (K := K) W) x := by
  apply
    ideleClassNorm_infinitePlaceIdeleClass_infinitePlaceBaseUnitExtension_of_isUnramified
      (K := K) (L := L) W
  exact InfinitePlace.isUnramified_iff.mpr (Or.inl hWReal)

/-- At a real place upstairs, the idele-class norm of the one-place
negative-one class is the one-place negative-one class below. -/
theorem ideleClassNorm_infinitePlaceIdeleClass_neg_one_of_isReal
    (W : InfinitePlace L)
    (hWReal : W.IsReal) :
    _root_.ideleClassNorm K L
        (infinitePlaceIdeleClass W (-1 : W.Completionˣ)) =
      infinitePlaceIdeleClass
        (_root_.infinitePlaceBelow (K := K) W)
        (-1 :
          ((_root_.infinitePlaceBelow (K := K) W).Completion)ˣ) := by
  rw [← infinitePlaceBaseUnitExtension_neg_one
    (K := K) (L := L) W]
  exact
    ideleClassNorm_infinitePlaceIdeleClass_infinitePlaceBaseUnitExtension_of_isReal
      (K := K) (L := L) W hWReal
      (-1 :
        ((_root_.infinitePlaceBelow (K := K) W).Completion)ˣ)

end IdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_OnePlaceNormKernel
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsCyclotomicExtension _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormExponentNeZero _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldAbsoluteFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.Reciprocity.rationalFiniteGaloisIdeleClassMulDistribMulAction _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The one-place norm kernel

At the source level, the key calculation is that an idele supported at one
finite place is a global relative-idele norm exactly when its local component
is a norm from the corresponding local tensor algebra.  The determinant-norm
comparison then identifies this image with the norm group of any chosen
completion above the place.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain
open IdeleGroup RelativeIdeleGroup

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

omit [NumberField L] [IsGalois K L] in
/-- A relative idele supported at an archimedean place has norm equal
to the one-place idele of its local determinant norm. -/
theorem norm_relativeInfinitePlaceIdele
    (v : InfinitePlace K)
    (z : (v.Completion ⊗[K] L)ˣ) :
    RelativeIdeleGroup.norm K L
        (relativeInfinitePlaceIdele
          (K := K) (L := L) v z) =
      infinitePlaceIdele v
        (infiniteTensorDetNorm
          (K := K) (L := L) v z) := by
  apply Prod.ext
  · apply ContinuousMulEquiv.piUnits.injective
    funext w
    change
      IdeleGroup.infiniteComponent w
          (RelativeIdeleGroup.norm K L
            (relativeInfinitePlaceIdele
              (K := K) (L := L) v z)) =
        IdeleGroup.infiniteComponent w
          (infinitePlaceIdele v
            (infiniteTensorDetNorm
              (K := K) (L := L) v z))
    by_cases hw : w = v
    · subst w
      rw [RelativeIdeleGroup.infiniteComponent_norm,
        relativeInfinitePlaceIdele_infiniteComponent_same,
        infinitePlaceIdele_infiniteComponent_same]
      rfl
    · rw [RelativeIdeleGroup.infiniteComponent_norm,
        relativeInfinitePlaceIdele_infiniteComponent_of_ne
          v w z hw,
        map_one,
        infinitePlaceIdele_infiniteComponent_of_ne
          v w
          (infiniteTensorDetNorm
            (K := K) (L := L) v z) hw]
  · apply RestrictedProduct.ext
    intro w
    change
      IdeleGroup.finiteComponent w
          (RelativeIdeleGroup.norm K L
            (relativeInfinitePlaceIdele
              (K := K) (L := L) v z)) =
        IdeleGroup.finiteComponent w
          (infinitePlaceIdele v
            (infiniteTensorDetNorm
              (K := K) (L := L) v z))
    rw [RelativeIdeleGroup.finiteComponent_norm,
      relativeInfinitePlaceIdele_finiteComponent,
      map_one,
      infinitePlaceIdele_finiteComponent]

omit [NumberField L] [IsGalois K L] in
/-- Exact archimedean one-place intersection before quotienting by
principal ideles:

`N(I_L) ∩ K_vˣ = N((K_v ⊗_K L)ˣ)`.
-/
theorem infinitePlaceIdele_mem_ideleNormSubgroup_iff
    (v : InfinitePlace K)
    (x : v.Completionˣ) :
    infinitePlaceIdele v x ∈
        ideleNormSubgroup (K := K) (L := L) ↔
      x ∈ infiniteTensorNormSubgroup
        (K := K) (L := L) v := by
  constructor
  · rintro ⟨a, ha⟩
    refine
      ⟨RelativeIdeleGroup.infiniteComponent
          (K := K) (L := L) v a, ?_⟩
    have hcomponent :=
      congrArg (IdeleGroup.infiniteComponent v) ha
    rw [RelativeIdeleGroup.infiniteComponent_norm,
      infinitePlaceIdele_infiniteComponent_same] at hcomponent
    exact hcomponent
  · rintro ⟨z, rfl⟩
    exact
      ⟨relativeInfinitePlaceIdele
          (K := K) (L := L) v z,
        norm_relativeInfinitePlaceIdele
          (K := K) (L := L) v z⟩

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_ConductorInfinitePart
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFiniteAbstractConjugate_normal _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFiniteResidueConjugate_normal _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.abelianIntermediateField_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsCyclotomicExtension _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormExponentNeZero _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldAbsoluteFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerExtensionSubgroupNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.cyclotomicUnramifiedGeometricMaxExtensionNormal _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.chosenFinitePlaceCompletionAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseEquiv_coe _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassField_algebraMap_original _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseEquiv_coe _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassField_algebraMap_original _root_.GlobalClassFieldTheory.GlobalClassFields.idealArtinMap_primeToIdealMap _root_.GlobalClassFieldTheory.GlobalClassFields.idealRayProjection_finitePrimeIdele _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNormDefiningModulus_apply _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNormQuotientTowerMap_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_rayPrimeClass _root_.GlobalClassFieldTheory.GlobalClassFields.normQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqNormQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.primeToIdealMap_finitePrimeIdele _root_.GlobalClassFieldTheory.GlobalClassFields.rayClassGroupEquivIdealRayClassGroup_mk_primeTo _root_.GlobalClassFieldTheory.GlobalClassFields.rayClassGroupEquivIdeleQuotient_mk_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassField_algebraMap_original _root_.GlobalClassFieldTheory.IdealClassFieldTheory.arithmeticIdealArtinGaloisMap_apply _root_.GlobalClassFieldTheory.IdealClassFieldTheory.arithmeticIdealArtinGaloisMap_eq_inv_idealArtinGaloisMap _root_.GlobalClassFieldTheory.IdealClassFieldTheory.arithmeticIdealArtinGaloisMap_ker _root_.GlobalClassFieldTheory.IdealClassFieldTheory.arithmeticIdealClassQuotientEquivGaloisGroup_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealArtinGaloisMap_apply _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealArtinGaloisMap_ker _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealClassQuotientEquivGaloisGroup_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealClassQuotientEquivNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.rayClassToNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom_mk _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicRestriction_infiniteGlobalArtinMonoidHom _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldGlobalNormResidueMonoidHom_fixed_apply _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalArtinMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalArtinMonoidHom_finitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalArtinMonoidHom_infinitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueAbelianizationMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueAbelianizationMonoidHom_ker _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueContinuousMulEquiv_apply _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_ker _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalReciprocityContinuousMulEquiv_globalNormResidue _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalReciprocityContinuousMulEquiv_symm_mk _root_.GlobalClassFieldTheory.Reciprocity.cyclotomicZHatNormCompositeContinuous_apply _root_.GlobalClassFieldTheory.Reciprocity.cyclotomicZHatNormCompositeInMulNatRangeContinuous_apply _root_.GlobalClassFieldTheory.Reciprocity.cyclotomicZHatNormComposite_apply _root_.GlobalClassFieldTheory.Reciprocity.finitePlaceGlobalArtinMonoidHom_finitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.globalArtinMonoidHom_finitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.globalArtinMonoidHom_ideleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.globalArtinMonoidHom_infinitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.globalArtinMonoidHom_relativeIdeleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_relativeIdeleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationContinuousMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationContinuousMulEquiv_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationIdeleMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationIdeleMonoidHom_eq_one_iff _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationIdeleMonoidHom_ker _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationIdeleMonoidHom_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationMonoidHom_eq_one_iff _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationMonoidHom_ker _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueContinuousMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueContinuousMulEquiv_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueEquiv_finiteReciprocityHom _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueMonoidHomOfEmbedding_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueMonoidHom_eq_one_iff _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueMonoidHom_ker _root_.GlobalClassFieldTheory.Reciprocity.globalReciprocityAbelianizationContinuousMulEquiv_apply _root_.GlobalClassFieldTheory.Reciprocity.globalReciprocityContinuousMulEquiv_apply _root_.GlobalClassFieldTheory.Reciprocity.infiniteGlobalArtinMonoidHom_abstractFixedFieldCyclotomic_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceGlobalArtinMonoidHom_finitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.mem_globalArtinFiniteSupport_iff _root_.GlobalClassFieldTheory.Reciprocity.normalizedCyclotomicZHatIdeleClassValueContinuousMul_mk _root_.GlobalClassFieldTheory.Reciprocity.normalizedCyclotomicZHatIdeleClassValueContinuous_mk _root_.GlobalClassFieldTheory.Reciprocity.normalizedCyclotomicZHatIdeleClassValue_range _root_.GlobalClassFieldTheory.Reciprocity.normalizedCyclotomicZHatIdeleValueContinuousMul_apply _root_.GlobalClassFieldTheory.Reciprocity.normalizedCyclotomicZHatIdeleValueContinuous_apply _root_.GlobalClassFieldTheory.Reciprocity.normalizedCyclotomicZHatIdeleValue_principalIdele_eq_zero _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatCompositumRestriction_infiniteGlobalArtinMonoidHom _root_.GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient_finiteNormClass _root_.GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient_ideleClass _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient_finiteNormClass _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient_ideleClass _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionGlobalArtin_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom_ideleClassNorm _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom_mk _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionNormQuotientArtinMonoidHom_mk _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractFixedFieldIdeleClassEquivFixed_coe _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexificationGlobalArtin_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicIdeleClassValuationData_valuationAt_fixed_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatGlobalArtin_rationalIdeleArchimedeanPart _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatGlobalArtin_rationalPositiveArchimedeanIdele _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleClassNormComposite_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleClassValueContinuousMul_mk _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleClassValueContinuous_mk _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleClassValue_range _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleValueContinuousAdd_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleValueReduction_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleValue_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleValue_principalIdele_eq_one _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleValue_rationalIdeleArchimedeanPart _root_.GlobalClassFieldTheory.Reciprocity.rationalFiniteNormQuotientEquivIdeleClassNormQuotient_finiteNormClass _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleArchimedeanPart_finiteComponent _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleArchimedeanPart_infiniteComponent _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleFinitePart_finiteComponent _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleFinitePart_infiniteComponent _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateIdeleClassEquivGaloisFixed_coe _root_.GlobalClassFieldTheory.Reciprocity.rationalPositiveArchimedeanIdele_finiteComponent _root_.GlobalClassFieldTheory.Reciprocity.restrictNormalHom_infiniteGlobalArtinMonoidHom _root_.GlobalClassFieldTheory.Reciprocity.restrictNormalHom_infiniteGlobalArtinMonoidHom_of_numberField _root_.GlobalClassFieldTheory.Reciprocity.restrictNormalHom_rationalCyclotomicZHatGlobalArtin _root_.IdeleClassGroup.normOneNorm_apply _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.extension_finiteComponent _root_.IdeleGroup.extension_principalIdele _root_.IdeleGroup.extension_self _root_.IdeleGroup.fractionalIdeal_finitePrimeIdele _root_.IdeleGroup.idealClass_finitePrimeIdele _root_.IdeleGroup.ideleNormContinuousMonoidHom_apply _root_.IdeleGroup.norm_principalIdele _root_.IdeleGroup.norm_relativeIdeleBaseChangeMulEquiv _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.idealNormLiftedModulusExponent_eq_zero_of_not_mem _root_.RayClass.idealNormLiftedModulus_apply _root_.RayClass.mem_idealNormLiftedModulus_support_iff _root_.RayClass.primeToModulusIdealNorm_coe _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.rationalFiniteModulus_apply _root_.RayClass.rationalModulus_finitePart_apply _root_.RayClass.signToNarrow_mk _root_.IdeleGroup.idealClass_classRepresentative _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleClassCongr_ideleClassNorm _root_.ideleClassCongr_mk _root_.ideleClassCongr_refl _root_.ideleClassExtension_mk _root_.ideleClassExtension_self _root_.ideleClassNorm_mk _root_.ideleCongr_finiteComponent _root_.ideleCongr_principalIdele _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe _root_.infinitePlace_mult_smul _root_.intermediateClassNormQuotientBaseChangeMulEquiv_mk _root_.ordinaryIdeleClassNormQuotientCongrOfAlgEquiv_mk _root_.ordinaryIdeleClassNorm_relativeIdeleClassBaseChange _root_.principalLocalNormQuotientMap_apply _root_.relativeFiniteIdeleMulEquiv_apply _root_.relativeFiniteIdeleToFiniteIdele_apply _root_.relativeIdeleBaseChangeMulEquiv_finite _root_.relativeIdeleBaseChangeMulEquiv_infinite _root_.relativeIdeleBaseChangeMulEquiv_principalIdele _root_.relativeIdeleClassBaseChangeMulEquiv_classInclusion _root_.relativeIdeleClassBaseChangeMulEquiv_congrOfAlgEquiv _root_.relativeIdeleClassBaseChangeMulEquiv_mk _root_.relativeIdeleClassCongrOfAlgEquiv_ideleClassNorm _root_.relativeIdeleClassCongr_ideleClassNorm _root_.relativeIdeleCongr_norm _root_.towerRelativeIdeleViaOrdinaryMulEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Removing one real place from a defining modulus

This file gives the one-place archimedean step toward the full conductor.
Removing the positivity condition at a real place preserves the defining
property exactly when the whole one-place idèle-class image is already
contained in the target subgroup.
-/

open scoped NumberField Classical

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

/-- Erasing a selected real place can only decrease a full modulus. -/
theorem eraseRealPlace_le
    (m : RayClass.Modulus K) (v : RayClass.RealPlace K) :
    m.eraseRealPlace v ≤ m :=
  ⟨le_rfl, Finset.erase_subset v m.infinitePart⟩

/-- If a real place is not selected by a modulus, its whole one-place
idèle-class image lies in the corresponding ray congruence subgroup. -/
theorem infinitePlaceIdeleClass_range_le_congruenceSubgroup_of_not_mem
    (m : RayClass.Modulus K) (v : RayClass.RealPlace K)
    (hv : v ∉ m.infinitePart) :
    (IdeleGroup.infinitePlaceIdeleClass v.1).range ≤
      m.congruenceSubgroup := by
  rintro _ ⟨x, rfl⟩
  rw [RayClass.Modulus.congruenceSubgroup]
  refine ⟨IdeleGroup.infinitePlaceIdele v.1 x, ?_, rfl⟩
  apply Subgroup.mem_sup_left
  rw [RayClass.Modulus.mem_ideleCongruenceSubgroup_iff]
  refine ⟨?_, ?_⟩
  · rw [RayClass.Modulus.mem_infiniteCongruenceSubgroup_iff]
    intro w hw
    have hwv : w ≠ v := by
      intro hwv
      subst w
      exact hv hw
    have hwv' : w.1 ≠ v.1 := by
      intro h
      exact hwv (Subtype.ext h)
    change
      IdeleGroup.infiniteComponent w.1
          (IdeleGroup.infinitePlaceIdele v.1 x) ∈
        RayClass.infinitePositiveSubgroup w.1
    rw [IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne
      v.1 w.1 x hwv']
    exact Subgroup.one_mem _
  · rw [RayClass.mem_finiteCongruenceSubgroup_iff]
    intro w
    change
      IdeleGroup.finiteComponent w
          (IdeleGroup.infinitePlaceIdele v.1 x) ∈
        RayClass.localHigherUnitGroup w (m.finitePart w)
    rw [IdeleGroup.infinitePlaceIdele_finiteComponent]
    exact Subgroup.one_mem _

private theorem eraseRealPlace_isDefiningModulus_of_range_le
    (H : Subgroup (IdeleClassGroup K))
    (m : RayClass.Modulus K)
    (hm : IsDefiningModulus H m)
    (v : RayClass.RealPlace K)
    (hvH : (IdeleGroup.infinitePlaceIdeleClass v.1).range ≤ H) :
    IsDefiningModulus H (m.eraseRealPlace v) := by
  let m' : RayClass.Modulus K := m.eraseRealPlace v
  show IsDefiningModulus H m'
  let q : IdeleGroup K →* IdeleClassGroup K :=
    QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
  rw [IsDefiningModulus, RayClass.Modulus.congruenceSubgroup,
    Subgroup.map_le_iff_le_comap]
  apply sup_le
  · intro a ha
    have ha' :=
      (RayClass.Modulus.mem_ideleCongruenceSubgroup_iff m' a).1 ha
    let s : IdeleGroup K :=
      IdeleGroup.infinitePlaceIdele v.1
        (IdeleGroup.infiniteComponent v.1 a)
    let b : IdeleGroup K := a * s⁻¹
    have hsH : q s ∈ H := by
      change
        IdeleGroup.infinitePlaceIdeleClass v.1
            (IdeleGroup.infiniteComponent v.1 a) ∈ H
      apply hvH
      exact ⟨IdeleGroup.infiniteComponent v.1 a, rfl⟩
    have hbCong : b ∈ m.ideleCongruenceSubgroup := by
      rw [RayClass.Modulus.mem_ideleCongruenceSubgroup_iff]
      refine ⟨?_, ?_⟩
      · rw [RayClass.Modulus.mem_infiniteCongruenceSubgroup_iff]
        intro w hw
        by_cases hwv : w = v
        · subst w
          change
            IdeleGroup.infiniteComponent v.1 b ∈
              RayClass.infinitePositiveSubgroup v.1
          dsimp only [b]
          rw [map_mul, map_inv]
          dsimp only [s]
          rw [IdeleGroup.infinitePlaceIdele_infiniteComponent_same,
            mul_inv_cancel]
          exact Subgroup.one_mem _
        · have hw' : w ∈ m'.infinitePart := by
            change w ∈ m.infinitePart.erase v
            exact Finset.mem_erase.mpr ⟨hwv, hw⟩
          have haw :=
            (RayClass.Modulus.mem_infiniteCongruenceSubgroup_iff
              m' a.1).1 ha'.1 w hw'
          have hwv' : w.1 ≠ v.1 := by
            intro h
            exact hwv (Subtype.ext h)
          change
            IdeleGroup.infiniteComponent w.1 b ∈
              RayClass.infinitePositiveSubgroup w.1
          dsimp only [b]
          rw [map_mul, map_inv]
          dsimp only [s]
          rw [IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne
              v.1 w.1 _ hwv',
            inv_one, mul_one]
          exact haw
      · rw [RayClass.mem_finiteCongruenceSubgroup_iff]
        intro w
        have haw :
            a.2 w ∈ RayClass.localHigherUnitGroup w (m.finitePart w) := by
          simpa [m'] using ha'.2 w
        change
          IdeleGroup.finiteComponent w b ∈
            RayClass.localHigherUnitGroup w (m.finitePart w)
        dsimp only [b]
        rw [map_mul, map_inv]
        dsimp only [s]
        rw [IdeleGroup.infinitePlaceIdele_finiteComponent,
          inv_one, mul_one, IdeleGroup.finiteComponent_apply]
        exact haw
    have hbH : q b ∈ H := by
      apply hm
      rw [RayClass.Modulus.congruenceSubgroup]
      exact ⟨b, Subgroup.mem_sup_left hbCong, rfl⟩
    have hab : a = b * s := by
      dsimp [b]
      group
    change q a ∈ H
    rw [hab, map_mul]
    exact H.mul_mem hbH hsH
  · intro a ha
    change q a ∈ H
    have hqa : q a = 1 :=
      (QuotientGroup.eq_one_iff a).2 ha
    rw [hqa]
    exact H.one_mem

/-- Removing the positivity condition at one real place preserves the
defining-modulus property exactly when the whole one-place idèle-class
image is already contained in the target subgroup. -/
theorem eraseRealPlace_isDefiningModulus_iff
    (H : Subgroup (IdeleClassGroup K))
    (m : RayClass.Modulus K)
    (v : RayClass.RealPlace K) :
    IsDefiningModulus H (m.eraseRealPlace v) ↔
      IsDefiningModulus H m ∧
        (IdeleGroup.infinitePlaceIdeleClass v.1).range ≤ H := by
  constructor
  · intro hm'
    refine ⟨?_, ?_⟩
    · exact
        (RayClass.Modulus.congruenceSubgroup_antitone
          (eraseRealPlace_le m v)).trans hm'
    · exact
        (infinitePlaceIdeleClass_range_le_congruenceSubgroup_of_not_mem
          (m.eraseRealPlace v) v (by simp)).trans hm'
  · rintro ⟨hm, hvH⟩
    exact eraseRealPlace_isDefiningModulus_of_range_le H m hm v hvH

/-- Erasing finitely many real places preserves the defining-modulus
property when every corresponding one-place idèle-class image is contained
in the target subgroup. -/
theorem eraseRealPlaces_isDefiningModulus_of_ranges_le
    (H : Subgroup (IdeleClassGroup K))
    (m : RayClass.Modulus K)
    (hm : IsDefiningModulus H m)
    (s : Finset (RayClass.RealPlace K))
    (hs : ∀ v ∈ s,
      (IdeleGroup.infinitePlaceIdeleClass v.1).range ≤ H) :
    IsDefiningModulus H (m.eraseRealPlaces s) := by
  classical
  revert hs
  induction s using Finset.induction_on with
  | empty =>
      intro _hs
      simpa only [RayClass.Modulus.eraseRealPlaces_empty] using hm
  | @insert v s _ ih =>
      intro hs
      rw [RayClass.Modulus.eraseRealPlaces_insert]
      exact
        (eraseRealPlace_isDefiningModulus_iff H
          (m.eraseRealPlaces s) v).2
          ⟨ih (fun w hw => hs w (Finset.mem_insert_of_mem hw)),
            hs v (Finset.mem_insert_self v s)⟩

namespace ConductorialSubgroup

/-- Every defining modulus contains the infinite part of the full conductor. -/
theorem fullConductorInfinitePart_subset_of_isDefiningModulus
    (H : ConductorialSubgroup K) {m : RayClass.Modulus K}
    (hm : IsDefiningModulus H.1 m) :
    H.fullConductorInfinitePart ⊆ m.infinitePart := by
  intro v hv
  have hvNot := (H.mem_fullConductorInfinitePart_iff v).1 hv
  by_contra hvm
  exact hvNot
    ((infinitePlaceIdeleClass_range_le_congruenceSubgroup_of_not_mem
      m v hvm).trans hm)

/-- The full conductor is itself a defining modulus. -/
theorem fullConductor_isDefiningModulus
    (H : ConductorialSubgroup K) :
    IsDefiningModulus H.1 H.fullConductor := by
  obtain ⟨m, hm, hfinite⟩ :=
    H.exists_definingModulus_finitePart_eq_narrowFiniteConductor
  let s : Finset (RayClass.RealPlace K) :=
    m.infinitePart \ H.fullConductorInfinitePart
  have hs : ∀ v ∈ s,
      (IdeleGroup.infinitePlaceIdeleClass v.1).range ≤ H.1 := by
    intro v hv
    have hvNot : v ∉ H.fullConductorInfinitePart :=
      (Finset.mem_sdiff.mp hv).2
    by_contra hvRange
    exact hvNot (H.mem_fullConductorInfinitePart_iff v |>.2 hvRange)
  have hmErase :
      IsDefiningModulus H.1 (m.eraseRealPlaces s) :=
    eraseRealPlaces_isDefiningModulus_of_ranges_le H.1 m hm s hs
  have hsubset : H.fullConductorInfinitePart ⊆ m.infinitePart :=
    H.fullConductorInfinitePart_subset_of_isDefiningModulus hm
  have hmod : m.eraseRealPlaces s = H.fullConductor := by
    apply RayClass.Modulus.ext
    · simpa only [RayClass.Modulus.finitePart_eraseRealPlaces,
        fullConductor] using hfinite
    · simpa only [RayClass.Modulus.infinitePart_eraseRealPlaces,
        fullConductor, s] using
        Finset.sdiff_sdiff_eq_self hsubset
  rw [← hmod]
  exact hmErase

end ConductorialSubgroup

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_InfinitePlaceOverfield
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsCyclotomicExtension _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseModule _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerBaseFieldScalarTower _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_originalBaseTopAlgebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_originalTopScalarTower _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_topAlgebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_topRatScalarTower _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextension_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_numberField _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_ratScalarTower _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.narrowClassGroup_finite _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalOrdinaryNormQuotientAdditiveTypeAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# The complex-conjugation overfield at an infinite place

This module realizes the embedded field `L(i)` inside `ℂ`, constructs its
complex place, and identifies ambient complex conjugation on that field.
-/

open scoped Classical IsMulCommutative
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

section ComplexConjugationOverextension

variable
    {K L : Type}
    [Field K]
    [Field L] [NumberField L] [Algebra K L]

variable
    [NumberField K]
    [FiniteDimensional K L] [IsAbelianGalois K L]

attribute [local instance] GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfieldRationalAlgebra
omit [FiniteDimensional K L] in
private theorem infinitePlaceRatEmbeddedExtensionField_le_factors
    (v : InfinitePlace K) :
    infinitePlaceRatEmbeddedExtensionField
          (K := K) (L := L) v ≤
      infinitePlaceRatComplexificationFactors
          (K := K) (L := L) v := by
  let C :=
    infinitePlaceComplexificationOverfield
      (K := K) (L := L) v
  let φ :=
    (InfinitePlace.embedding
      (chosenInfinitePlaceAbove (L := L) v)).toRatAlgHom
  let A :=
    infinitePlaceEmbeddedExtensionField
      (K := K) (L := L) v
  let B :=
    infinitePlaceBaseFourthRootField
      (K := K) (L := L) v
  intro x hx
  have hx' :
      (x : C).1 ∈ φ.fieldRange :=
    (IntermediateField.mem_restrict
      (show φ.fieldRange ≤ C from le_sup_left) x).mp hx
  obtain ⟨y, hy⟩ := hx'
  change (x : C) ∈ A ⊔ B
  apply (show A ≤ A ⊔ B from le_sup_left)
  change
    (x : C) ∈
      (IsScalarTower.toAlgHom K L C).fieldRange
  refine ⟨y, ?_⟩
  apply Subtype.ext
  calc
    ((IsScalarTower.toAlgHom K L C y : C) : ℂ) =
        InfinitePlace.embedding
          (chosenInfinitePlaceAbove (L := L) v) y := by
      change
        ((infinitePlaceComplexificationOverfieldEmbedding
            (K := K) (L := L) v y : C) : ℂ) = _
      exact
        infinitePlaceComplexificationOverfieldEmbedding_coe
          (K := K) (L := L) v y
    _ = (x : C).1 := hy

omit [FiniteDimensional K L] in
private theorem infinitePlaceRatFourthRootField_le_factors
    (v : InfinitePlace K) :
    infinitePlaceRatFourthRootField
          (K := K) (L := L) v ≤
      infinitePlaceRatComplexificationFactors
          (K := K) (L := L) v := by
  let C :=
    infinitePlaceComplexificationOverfield
      (K := K) (L := L) v
  let A :=
    infinitePlaceEmbeddedExtensionField
      (K := K) (L := L) v
  let B :=
    infinitePlaceBaseFourthRootField
      (K := K) (L := L) v
  intro x hx
  have hx' :
      (x : C).1 ∈ complexFourthRootField :=
    (IntermediateField.mem_restrict
      (show complexFourthRootField ≤ C from le_sup_right) x).mp hx
  let y : complexFourthRootField := ⟨(x : C).1, hx'⟩
  let i : complexFourthRootField →ₐ[ℚ] C :=
    IntermediateField.inclusion
      (show complexFourthRootField ≤ C from le_sup_right)
  have hy :
      y ∈
        Algebra.adjoin ℚ
          {z : complexFourthRootField |
            ∃ n ∈ ({4} : Set ℕ),
              n ≠ 0 ∧ z ^ n = 1} :=
    IsCyclotomicExtension.adjoin_roots y
  have hiy : i y ∈ B := by
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hy
    · intro z hz
      change
        i z ∈
          IntermediateField.adjoin K
            {w : C |
              ∃ n ∈ ({4} : Set ℕ),
                n ≠ 0 ∧ w ^ n = 1}
      apply IntermediateField.subset_adjoin K
      rcases hz with ⟨n, hn, hn0, hz⟩
      exact
        ⟨n, hn, hn0, by
          rw [← map_pow, hz, map_one]⟩
    · intro q
      rw [i.commutes,
        IsScalarTower.algebraMap_apply ℚ K C]
      exact B.algebraMap_mem (algebraMap ℚ K q)
    · intro z w _hz _hw hiz hiw
      exact B.add_mem hiz hiw
    · intro z w _hz _hw hiz hiw
      exact B.mul_mem hiz hiw
  change (x : C) ∈ A ⊔ B
  apply (show B ≤ A ⊔ B from le_sup_right)
  have hiyx : i y = (x : C) := by
    apply Subtype.ext
    rfl
  rw [← hiyx]
  exact hiy

omit [NumberField K] [FiniteDimensional K L] in
private theorem infinitePlaceRatComplexificationFactors_sup
    (v : InfinitePlace K) :
    infinitePlaceRatEmbeddedExtensionField
          (K := K) (L := L) v ⊔
        infinitePlaceRatFourthRootField
          (K := K) (L := L) v =
      ⊤ := by
  apply IntermediateField.lift_injective
    (infinitePlaceComplexificationOverfield
      (K := K) (L := L) v)
  rw [infinitePlaceRatEmbeddedExtensionField,
    infinitePlaceRatFourthRootField,
    IntermediateField.lift_sup,
    IntermediateField.lift_restrict,
    IntermediateField.lift_restrict,
    IntermediateField.lift_top]
  rfl

omit [FiniteDimensional K L] in
/-- The embedded abelian extension and the base-changed fourth-root
factor generate the whole concrete complexification overfield. -/
theorem infinitePlaceComplexificationFactors_sup
    (v : InfinitePlace K) :
    infinitePlaceEmbeddedExtensionField
          (K := K) (L := L) v ⊔
        infinitePlaceBaseFourthRootField
          (K := K) (L := L) v =
      ⊤ := by
  apply
    (IntermediateField.restrictScalars_eq_top_iff
      (K := ℚ)).mp
  change
    infinitePlaceRatComplexificationFactors
        (K := K) (L := L) v =
      ⊤
  apply top_unique
  rw [← infinitePlaceRatComplexificationFactors_sup
    (K := K) (L := L) v]
  exact sup_le
    (infinitePlaceRatEmbeddedExtensionField_le_factors
      (K := K) (L := L) v)
    (infinitePlaceRatFourthRootField_le_factors
      (K := K) (L := L) v)

noncomputable instance
    infinitePlaceComplexificationOverfield_isAbelianGalois_over_base
    (v : InfinitePlace K) :
    IsAbelianGalois K
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) := by
  let C :=
    infinitePlaceComplexificationOverfield
      (K := K) (L := L) v
  let A :=
    infinitePlaceEmbeddedExtensionField
      (K := K) (L := L) v
  let B :=
    infinitePlaceBaseFourthRootField
      (K := K) (L := L) v
  let : FiniteDimensional K A :=
    (IsScalarTower.toAlgHom K L C).equivFieldRange.toLinearEquiv
      |>.finiteDimensional
  let : FiniteDimensional K B :=
    IsCyclotomicExtension.finiteDimensional
      ({4} : Set ℕ) K B
  let :
      IsAbelianGalois K
        (⊤ : IntermediateField K C) := by
    rw [← infinitePlaceComplexificationFactors_sup
      (K := K) (L := L) v]
    exact
      AlgebraicNumberTheory.isAbelianGalois_sup K A B
  exact
    IsAbelianGalois.of_algHom
      (IntermediateField.topEquiv.symm.toAlgHom :
        C →ₐ[K] (⊤ : IntermediateField K C))

end ComplexConjugationOverextension

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_RamifiedOverextension
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerBaseFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_originalBaseTopAlgebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_originalTopScalarTower _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_topAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# The quadratic overextension at a ramified real place

This module constructs the real fixed field of complex conjugation, the
quadratic overextension above it, and the faithful cyclotomic restriction.
-/

open scoped Classical IsMulCommutative
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

attribute [local instance]
  infinitePlaceComplexificationOverfieldRationalAlgebra

section ComplexConjugationOverextension

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

noncomputable instance
    ramifiedInfinitePlaceRealFixedField_isAbelianGalois_over_base
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    IsAbelianGalois K
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified) :=
  IsAbelianGalois.tower_bot K
    (ramifiedInfinitePlaceRealFixedField
      (K := K) (L := L) v hRamified)
    (infinitePlaceComplexificationOverfield
      (K := K) (L := L) v)

attribute [local instance]
  rationalComplexificationCyclotomicField_isAbelianGalois

end ComplexConjugationOverextension

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_InfinitePlaceCompatibility
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsCyclotomicExtension _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormExponentNeZero _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldAbsoluteFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_numberField _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_originalBaseTopAlgebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_originalTopScalarTower _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_topAlgebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_topRatScalarTower _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.cyclotomicUnramifiedGeometricMaxExtensionNormal
attribute [-simp] _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Infinite-place local-global Artin compatibility

This module compares the real fixed place and the original ramified place,
then transports the special overextension computation through global
norm-residue naturality.
-/

open scoped Classical IsMulCommutative
open NumberField
open IdeleGroup

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

section ComplexConjugationOverextension

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

local instance
    infinitePlaceCompatibilityIdeleClassGroupIsMulCommutative_r0379a7_1
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩
omit [NumberField K] [FiniteDimensional K L] in
/-- The fixed-field place is genuinely real: every element of the
fixed field is fixed by ambient complex conjugation. -/
theorem ramifiedInfinitePlaceRealFixedPlace_isReal
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    (ramifiedInfinitePlaceRealFixedPlace
      (K := K) (L := L) v hRamified).IsReal := by
  let E :=
    infinitePlaceComplexificationOverfield
      (K := K) (L := L) v
  let K' :=
    ramifiedInfinitePlaceRealFixedField
      (K := K) (L := L) v hRamified
  let φ : K' →+* ℂ :=
    E.val.toRingHom.comp (algebraMap K' E)
  refine ⟨φ, ?_, ?_⟩
  · rw [ComplexEmbedding.isReal_iff]
    ext x
    have hx :
        ∀ g ∈
            Subgroup.zpowers
              (ramifiedInfinitePlaceOverfieldConjugation
                (K := K) (L := L) v hRamified),
          g (x : E) = (x : E) := by
      exact
        (IntermediateField.mem_fixedField_iff _ _).1
          x.property
    have hxc :=
      hx
        (ramifiedInfinitePlaceOverfieldConjugation
          (K := K) (L := L) v hRamified)
        (Subgroup.mem_zpowers
          (ramifiedInfinitePlaceOverfieldConjugation
            (K := K) (L := L) v hRamified))
    have hxc' :=
      congrArg
        (fun z : E => E.val.toRingHom z)
        hxc
    have hconj :
        E.val.toRingHom
            (ramifiedInfinitePlaceOverfieldConjugation
              (K := K) (L := L) v hRamified (x : E)) =
          star (E.val.toRingHom (x : E)) := by
      exact
        ramifiedInfinitePlaceOverfieldConjugation_apply
          (K := K) (L := L) v hRamified (x : E)
    rw [ComplexEmbedding.conjugate_coe_eq]
    change
      star (E.val.toRingHom (algebraMap K' E x)) =
        E.val.toRingHom (algebraMap K' E x)
    rw [IntermediateField.algebraMap_apply]
    exact hconj.symm.trans hxc'
  · rfl

omit [FiniteDimensional K L] in
/-- Restricting the concrete real fixed-field place to the original
base recovers the prescribed ramified place `v`. -/
theorem infinitePlaceBelow_ramifiedInfinitePlaceRealFixedPlace
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    infinitePlaceBelow (K := K)
        (ramifiedInfinitePlaceRealFixedPlace
          (K := K) (L := L) v hRamified) =
      v := by
  apply InfinitePlace.ext
  intro x
  change
    ‖((algebraMap
          (ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified)
          (infinitePlaceComplexificationOverfield
            (K := K) (L := L) v)
          (algebraMap K
            (ramifiedInfinitePlaceRealFixedField
              (K := K) (L := L) v hRamified) x) :
        infinitePlaceComplexificationOverfield
          (K := K) (L := L) v) : ℂ)‖ =
      v x
  rw [← IsScalarTower.algebraMap_apply K
    (ramifiedInfinitePlaceRealFixedField
      (K := K) (L := L) v hRamified)
    (infinitePlaceComplexificationOverfield
      (K := K) (L := L) v)]
  change
    ‖InfinitePlace.embedding
        (chosenInfinitePlaceAbove (L := L) v)
        (algebraMap K L x)‖ =
      v x
  rw [InfinitePlace.norm_embedding_eq]
  exact
    congrArg
      (fun q : InfinitePlace K => q x)
      (chosenInfinitePlaceAbove_comap (L := L) v)

omit [FiniteDimensional K L] in
/-- Restricting ambient complex conjugation from `L(i)` to `L`
recovers the actual chosen local Artin symbol of negative one at the
original ramified place. -/
theorem ramifiedInfinitePlaceOverextensionRestriction_conjugation
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    ramifiedInfinitePlaceOverextensionRestriction
        (K := K) (L := L) v hRamified
        (ramifiedInfinitePlaceOverextensionConjugation
          (K := K) (L := L) v hRamified) =
      chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := L) v
        (-1 : v.Completionˣ) := by
  apply AlgEquiv.ext
  intro x
  apply
    (algebraMap L
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v)).injective
  change
    algebraMap L
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v)
        ((AlgEquiv.restrictNormalHom L
          ((ramifiedInfinitePlaceOverextensionConjugation
            (K := K) (L := L) v hRamified).restrictScalars K)) x) =
      algebraMap L
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v)
        (chosenInfinitePlaceArtinMonoidHom
          (K := K) (L := L) v
          (-1 : v.Completionˣ) x)
  have hrestrict :
      algebraMap L
          (infinitePlaceComplexificationOverfield
            (K := K) (L := L) v)
          ((AlgEquiv.restrictNormalHom L
            ((ramifiedInfinitePlaceOverextensionConjugation
              (K := K) (L := L) v hRamified).restrictScalars K)) x) =
        (ramifiedInfinitePlaceOverextensionConjugation
          (K := K) (L := L) v hRamified).restrictScalars K
          (algebraMap L
            (infinitePlaceComplexificationOverfield
              (K := K) (L := L) v) x) := by
    exact
      AlgEquiv.restrictNormal_commutes
        ((ramifiedInfinitePlaceOverextensionConjugation
          (K := K) (L := L) v hRamified).restrictScalars K)
        L x
  rw [hrestrict]
  apply Subtype.ext
  change
    star
        (InfinitePlace.embedding
          (chosenInfinitePlaceAbove (L := L) v) x) =
      InfinitePlace.embedding
        (chosenInfinitePlaceAbove (L := L) v)
        (chosenInfinitePlaceArtinMonoidHom
          (K := K) (L := L) v
          (-1 : v.Completionˣ) x)
  exact
    (chosenInfinitePlaceArtinMonoidHom_neg_one_isConj_of_ramified
      (K := K) (L := L) v hRamified).eq x |>.symm

omit [NumberField K] [FiniteDimensional K L] in
/-- The separable-closure embedding of the complexification overfield
restricts to the standard embedding of its original top field. -/
theorem
    infinitePlaceComplexificationOverfieldSeparableClosureEmbedding_restrictDomain
    (v : InfinitePlace K) :
    (infinitePlaceComplexificationOverfieldSeparableClosureEmbedding
      (K := K) (L := L) v).domRestrict L =
        AlgebraicNumberTheory.numberFieldSeparableClosureEmbedding L :=
  Classical.choose_spec
    (IsAlgClosed.surjective_domRestrict_of_isAlgebraic
      (K := ℚ)
      (L := L)
      (E :=
        infinitePlaceComplexificationOverfield
          (K := K) (L := L) v)
      (M := SeparableClosure ℚ)
      (AlgebraicNumberTheory.numberFieldSeparableClosureEmbedding L))

omit [NumberField K] [FiniteDimensional K L] in
/-- The induced lower embedding is the standard number-field embedding. -/
theorem
    infinitePlaceComplexificationLowerSeparableClosureEmbedding_eq_standard
    (v : InfinitePlace K) :
    infinitePlaceComplexificationLowerSeparableClosureEmbedding
        (K := K) (L := L) v =
      AlgebraicNumberTheory.numberFieldSeparableClosureEmbedding L := by
  simpa only [
    infinitePlaceComplexificationLowerSeparableClosureEmbedding,
    AlgHom.domRestrict] using
    infinitePlaceComplexificationOverfieldSeparableClosureEmbedding_restrictDomain
      (K := K) (L := L) v

private theorem ramifiedInfinitePlace_normResidueDiamond_neg_one
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    ramifiedInfinitePlaceRestrictedOverextensionNormResidueNegOneValue
        (K := K) (L := L) v hRamified =
      ramifiedInfinitePlaceNormedOverextensionNormResidueNegOneValue
        (K := K) (L := L) v hRamified := by
  exact
    DFunLike.congr_fun
      (globalNormResidueMonoidHomOfEmbedding_norm_restriction
        (K := K) (L := L)
        (K' :=
          ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified)
        (L' :=
          infinitePlaceComplexificationOverfield
            (K := K) (L := L) v)
        (infinitePlaceComplexificationOverfieldSeparableClosureEmbedding
          (K := K) (L := L) v))
      (ramifiedInfinitePlaceOverextensionNegOneIdeleClass
        (K := K) (L := L) v hRamified)

omit [FiniteDimensional K L] in
private theorem
    ramifiedInfinitePlace_restrictedOverextensionNormResidue_neg_one
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    ramifiedInfinitePlaceRestrictedOverextensionNormResidueNegOneValue
        (K := K) (L := L) v hRamified =
      ramifiedInfinitePlaceLocalArtinNegOneValue
        (K := K) (L := L) v := by
  rw [
    ramifiedInfinitePlaceRestrictedOverextensionNormResidueNegOneValue,
    ramifiedInfinitePlaceOverextensionGlobalNormResidueNegOneValue,
    ramifiedInfinitePlaceOverextensionNegOneIdeleClass,
    ramifiedInfinitePlaceLocalArtinNegOneValue,
    ramifiedInfinitePlaceOverextension_globalNormResidueOfEmbedding_neg_one,
    ramifiedInfinitePlaceOverextensionRestriction_conjugation]

private theorem ramifiedInfinitePlace_normedNormResidue_neg_one
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    ramifiedInfinitePlaceNormedOverextensionNormResidueNegOneValue
        (K := K) (L := L) v hRamified =
      ramifiedInfinitePlaceGlobalNormResidueNegOneValue
        (K := K) (L := L) v := by
  rw [
    ramifiedInfinitePlaceNormedOverextensionNormResidueNegOneValue,
    infinitePlaceComplexificationLowerSeparableClosureEmbedding_eq_standard,
    ← globalNormResidueMonoidHom_eq_ofEmbedding_standard,
    ramifiedInfinitePlaceOverextensionNegOneIdeleClass,
    IdeleGroup.ideleClassNorm_infinitePlaceIdeleClass_neg_one_of_isReal
      (K := K)
      (L :=
        ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified)
      (ramifiedInfinitePlaceRealFixedPlace
        (K := K) (L := L) v hRamified)
      (ramifiedInfinitePlaceRealFixedPlace_isReal
        (K := K) (L := L) v hRamified),
    infinitePlaceBelow_ramifiedInfinitePlaceRealFixedPlace,
    ramifiedInfinitePlaceGlobalNormResidueNegOneValue]

/-- At every ramified real place of a finite abelian extension, the
canonical global norm-residue symbol of the one-place negative-one
idele class is the actual chosen local Artin symbol.

The proof is the concrete complex-conjugation overextension diamond:
the upper equality is the rational fourth-root product formula, the
vertical map on idele classes is the genuine one-place norm, and the
vertical map on Galois groups is actual restriction. -/
@[simp]
theorem
    globalNormResidueMonoidHom_infinitePlaceIdeleClass_neg_one_of_ramified
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    ramifiedInfinitePlaceGlobalNormResidueNegOneValue
        (K := K) (L := L) v =
      ramifiedInfinitePlaceLocalArtinNegOneValue
        (K := K) (L := L) v := by
  exact
    (ramifiedInfinitePlace_normedNormResidue_neg_one
      (K := K) (L := L) v hRamified).symm |>.trans
      ((ramifiedInfinitePlace_normResidueDiamond_neg_one
        (K := K) (L := L) v hRamified).symm.trans
        (ramifiedInfinitePlace_restrictedOverextensionNormResidue_neg_one
          (K := K) (L := L) v hRamified))

end ComplexConjugationOverextension

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_InfiniteLocalGlobalArtinCompatibility
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsCyclotomicExtension _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormExponentNeZero _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldAbsoluteFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldScalarTowerOverOriginal _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.cyclotomicUnramifiedGeometricMaxExtensionNormal
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseEquiv_coe _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassField_algebraMap_original _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseEquiv_coe _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassField_algebraMap_original _root_.GlobalClassFieldTheory.GlobalClassFields.idealArtinMap_primeToIdealMap _root_.GlobalClassFieldTheory.GlobalClassFields.idealRayProjection_finitePrimeIdele _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNormQuotientTowerMap_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_rayPrimeClass _root_.GlobalClassFieldTheory.GlobalClassFields.normQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqNormQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.primeToIdealMap_finitePrimeIdele _root_.GlobalClassFieldTheory.GlobalClassFields.rayClassGroupEquivIdealRayClassGroup_mk_primeTo _root_.GlobalClassFieldTheory.GlobalClassFields.rayClassGroupEquivIdeleQuotient_mk_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassField_algebraMap_original _root_.GlobalClassFieldTheory.IdealClassFieldTheory.arithmeticIdealArtinGaloisMap_apply _root_.GlobalClassFieldTheory.IdealClassFieldTheory.arithmeticIdealArtinGaloisMap_eq_inv_idealArtinGaloisMap _root_.GlobalClassFieldTheory.IdealClassFieldTheory.arithmeticIdealArtinGaloisMap_ker _root_.GlobalClassFieldTheory.IdealClassFieldTheory.arithmeticIdealClassQuotientEquivGaloisGroup_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealArtinGaloisMap_apply _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealArtinGaloisMap_ker _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealClassQuotientEquivGaloisGroup_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealClassQuotientEquivNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.rayClassToNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom_mk _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicRestriction_infiniteGlobalArtinMonoidHom _root_.GlobalClassFieldTheory.Reciprocity.arithmeticChosenInfinitePlaceArtinMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalArtinMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalArtinMonoidHom_finitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalArtinMonoidHom_infinitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueAbelianizationMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueAbelianizationMonoidHom_ker _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueContinuousMulEquiv_apply _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_ker _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalReciprocityContinuousMulEquiv_globalNormResidue _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalReciprocityContinuousMulEquiv_symm_mk _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_relativeIdeleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationContinuousMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationContinuousMulEquiv_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationIdeleMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationIdeleMonoidHom_eq_one_iff _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationIdeleMonoidHom_ker _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationIdeleMonoidHom_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationMonoidHom_eq_one_iff _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationMonoidHom_ker _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueContinuousMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueContinuousMulEquiv_apply _root_.GlobalClassFieldTheory.Reciprocity.globalReciprocityAbelianizationContinuousMulEquiv_apply _root_.GlobalClassFieldTheory.Reciprocity.globalReciprocityContinuousMulEquiv_apply _root_.GlobalClassFieldTheory.Reciprocity.infiniteGlobalArtinMonoidHom_abstractFixedFieldCyclotomic_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.mem_globalArtinFiniteSupport_iff _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.fractionalIdeal_finitePrimeIdele _root_.IdeleGroup.idealClass_finitePrimeIdele _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.signToNarrow_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Archimedean local-global compatibility of Artin homomorphisms

This file compares the actual Artin homomorphism at an infinite place
with the global norm-residue homomorphism on idele classes.  The
one-place norm statements are proved from genuine relative ideles
supported at the chosen archimedean place.
-/

open scoped NumberField
open NumberField
open IdeleGroup RelativeIdeleGroup

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

omit [IsAbelianGalois K L] in
/-- A determinant norm at one infinite place gives an actual global
idele-class norm.  The witness is the relative idele supported at that
place, transported to an ordinary idele of the extension field. -/
theorem infinitePlaceIdeleClass_mem_ideleClassNorm_range_of_mem_infiniteTensorNorm
    (v : InfinitePlace K)
    (x : v.Completionˣ)
    (hx :
      x ∈ infiniteTensorNormSubgroup
        (K := K) (L := L) v) :
    IdeleGroup.infinitePlaceIdeleClass v x ∈
      (_root_.ideleClassNorm K L).range := by
  have hnorm :
      IdeleGroup.infinitePlaceIdele v x ∈
        ideleNormSubgroup (K := K) (L := L) :=
    (infinitePlaceIdele_mem_ideleNormSubgroup_iff
      (K := K) (L := L) v x).2 hx
  obtain ⟨z, hz⟩ := hnorm
  refine
    ⟨QuotientGroup.mk'
        (IdeleGroup.principalSubgroup L)
        (_root_.relativeIdeleBaseChangeMulEquiv
          (K := K) (L := L) z), ?_⟩
  change
    QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K)
        (IdeleGroup.norm K L
          (_root_.relativeIdeleBaseChangeMulEquiv
            (K := K) (L := L) z)) =
      QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K)
        (IdeleGroup.infinitePlaceIdele v x)
  rw [IdeleGroup.norm_relativeIdeleBaseChangeMulEquiv, hz]

/-- An infinite-place element killed by the actual local Artin
homomorphism is killed by the global norm-residue homomorphism after
insertion as a one-place idele class. -/
theorem globalNormResidueMonoidHom_infinitePlaceIdeleClass_eq_one_of_localArtin_eq_one
    (v : InfinitePlace K)
    (x : v.Completionˣ)
    (hx :
      chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := L) v x = 1) :
    globalNormResidueMonoidHom K L
        (IdeleGroup.infinitePlaceIdeleClass v x) = 1 := by
  rw [globalNormResidueMonoidHom_eq_one_iff]
  exact
    infinitePlaceIdeleClass_mem_ideleClassNorm_range_of_mem_infiniteTensorNorm
      (K := K) (L := L) v x
      ((chosenInfinitePlaceArtinMonoidHom_eq_one_iff_infiniteTensorNorm
        (K := K) (L := L) v x).1 hx)

/-- A positive element at a real infinite place gives an actual
idele-class norm. -/
theorem infinitePlaceIdeleClass_mem_ideleClassNorm_range_of_real_pos
    (v : InfinitePlace K)
    (hvReal : v.IsReal)
    (x : v.Completionˣ)
    (hx :
      0 <
        InfinitePlace.Completion.ringEquivRealOfIsReal
          hvReal (x : v.Completion)) :
    IdeleGroup.infinitePlaceIdeleClass v x ∈
      (_root_.ideleClassNorm K L).range := by
  apply
    infinitePlaceIdeleClass_mem_ideleClassNorm_range_of_mem_infiniteTensorNorm
      (K := K) (L := L) v x
  exact
    (chosenInfinitePlaceArtinMonoidHom_eq_one_iff_infiniteTensorNorm
      (K := K) (L := L) v x).1
      (chosenInfinitePlaceArtinMonoidHom_eq_one_of_real_pos
        (K := K) (L := L) v hvReal x hx)

/-- The global norm-residue symbol of a positive real one-place idele
class is trivial. -/
theorem globalNormResidueMonoidHom_infinitePlaceIdeleClass_eq_one_of_real_pos
    (v : InfinitePlace K)
    (hvReal : v.IsReal)
    (x : v.Completionˣ)
    (hx :
      0 <
        InfinitePlace.Completion.ringEquivRealOfIsReal
          hvReal (x : v.Completion)) :
    globalNormResidueMonoidHom K L
        (IdeleGroup.infinitePlaceIdeleClass v x) = 1 := by
  rw [globalNormResidueMonoidHom_eq_one_iff]
  exact
    infinitePlaceIdeleClass_mem_ideleClassNorm_range_of_real_pos
      (K := K) (L := L) v hvReal x hx

/-- At an actually unramified infinite place, both the restricted
global norm-residue map and the chosen local Artin map are trivial,
hence the local-global compatibility square commutes. -/
theorem globalNormResidueMonoidHom_comp_infinitePlaceIdeleClass_of_unramified
    (v : InfinitePlace K)
    (hUnramified :
      (chosenInfinitePlaceAbove (L := L) v).IsUnramified K) :
    (globalNormResidueMonoidHom K L).comp
        (IdeleGroup.infinitePlaceIdeleClass v) =
      chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := L) v := by
  apply MonoidHom.ext
  intro x
  have hlocal :
      chosenInfinitePlaceArtinMonoidHom
          (K := K) (L := L) v x = 1 := by
    unfold chosenInfinitePlaceArtinMonoidHom
    unfold infinitePlaceArtinMonoidHomOfPlace
    rw [dite_eq_left hUnramified]
    rfl
  have hglobal :
      globalNormResidueMonoidHom K L
          (IdeleGroup.infinitePlaceIdeleClass v x) = 1 :=
    globalNormResidueMonoidHom_infinitePlaceIdeleClass_eq_one_of_localArtin_eq_one
      (K := K) (L := L) v x hlocal
  rw [MonoidHom.comp_apply, hglobal, hlocal]

/-- At a complex base place the chosen place upstairs is automatically
unramified, so the archimedean local-global compatibility square is
trivial. -/
theorem globalNormResidueMonoidHom_comp_infinitePlaceIdeleClass_of_isComplex
    (v : InfinitePlace K)
    (hvComplex : v.IsComplex) :
    (globalNormResidueMonoidHom K L).comp
        (IdeleGroup.infinitePlaceIdeleClass v) =
      chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := L) v := by
  apply
    globalNormResidueMonoidHom_comp_infinitePlaceIdeleClass_of_unramified
      (K := K) (L := L) v
  apply InfinitePlace.isUnramified_iff.mpr
  apply Or.inr
  rw [chosenInfinitePlaceAbove_comap (L := L) v]
  exact hvComplex

omit [NumberField K] in
/-- Every unit at a real completion is positive either as given or
after multiplication by negative one. -/
private theorem realCompletionUnit_pos_or_neg_one_mul_pos
    (v : InfinitePlace K)
    (hvReal : v.IsReal)
    (x : v.Completionˣ) :
    0 <
        InfinitePlace.Completion.ringEquivRealOfIsReal
          hvReal (x : v.Completion) ∨
      0 <
        InfinitePlace.Completion.ringEquivRealOfIsReal
          hvReal
          (((-1 : v.Completionˣ) * x : v.Completionˣ) :
            v.Completion) := by
  let e :
      v.Completion ≃+* ℝ :=
    InfinitePlace.Completion.ringEquivRealOfIsReal hvReal
  have hne :
      e (x : v.Completion) ≠ 0 :=
    (map_ne_zero e).2 (Units.ne_zero x)
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · right
    change 0 < e ((-1 : v.Completion) * (x : v.Completion))
    rw [map_mul, map_neg, map_one]
    simpa only [neg_one_mul] using neg_pos.mpr hneg
  · exact Or.inl hpos

/-- At a real place, the full archimedean local-global Artin square is
equivalent to its single value at negative one.  Positivity kills both
maps, so this isolates the unique ramified real source calculation. -/
theorem globalNormResidueMonoidHom_comp_infinitePlaceIdeleClass_eq_iff_neg_one
    (v : InfinitePlace K)
    (hvReal : v.IsReal) :
    (globalNormResidueMonoidHom K L).comp
          (IdeleGroup.infinitePlaceIdeleClass v) =
        chosenInfinitePlaceArtinMonoidHom
          (K := K) (L := L) v ↔
      globalNormResidueMonoidHom K L
          (IdeleGroup.infinitePlaceIdeleClass v
            (-1 : v.Completionˣ)) =
        chosenInfinitePlaceArtinMonoidHom
          (K := K) (L := L) v
          (-1 : v.Completionˣ) := by
  constructor
  · intro h
    exact DFunLike.congr_fun h (-1 : v.Completionˣ)
  · intro hneg
    apply MonoidHom.ext
    intro x
    rcases
        realCompletionUnit_pos_or_neg_one_mul_pos
          (K := K) v hvReal x with hx | hx
    · rw [MonoidHom.comp_apply,
        globalNormResidueMonoidHom_infinitePlaceIdeleClass_eq_one_of_real_pos
          (K := K) (L := L) v hvReal x hx,
        chosenInfinitePlaceArtinMonoidHom_eq_one_of_real_pos
          (K := K) (L := L) v hvReal x hx]
    · have hglobal :
          globalNormResidueMonoidHom K L
              (IdeleGroup.infinitePlaceIdeleClass v
                ((-1 : v.Completionˣ) * x)) = 1 :=
        globalNormResidueMonoidHom_infinitePlaceIdeleClass_eq_one_of_real_pos
          (K := K) (L := L) v hvReal
          ((-1 : v.Completionˣ) * x) hx
      have hlocal :
          chosenInfinitePlaceArtinMonoidHom
              (K := K) (L := L) v
              ((-1 : v.Completionˣ) * x) = 1 :=
        chosenInfinitePlaceArtinMonoidHom_eq_one_of_real_pos
          (K := K) (L := L) v hvReal
          ((-1 : v.Completionˣ) * x) hx
      change
        ((globalNormResidueMonoidHom K L).comp
          (IdeleGroup.infinitePlaceIdeleClass v))
            ((-1 : v.Completionˣ) * x) = 1 at hglobal
      rw [map_mul] at hglobal hlocal
      have hglobalX :
          globalNormResidueMonoidHom K L
              (IdeleGroup.infinitePlaceIdeleClass v x) =
            (globalNormResidueMonoidHom K L
              (IdeleGroup.infinitePlaceIdeleClass v
                (-1 : v.Completionˣ)))⁻¹ :=
        eq_inv_of_mul_eq_one_right hglobal
      have hlocalX :
          chosenInfinitePlaceArtinMonoidHom
              (K := K) (L := L) v x =
            (chosenInfinitePlaceArtinMonoidHom
              (K := K) (L := L) v
              (-1 : v.Completionˣ))⁻¹ :=
        eq_inv_of_mul_eq_one_right hlocal
      rw [MonoidHom.comp_apply, hglobalX, hlocalX, hneg]

/-- For an arbitrary infinite place, the local-global Artin square is
reduced canonically to the negative-one calculation in the real case;
the complex case is already trivial. -/
theorem
    globalNormResidueMonoidHom_comp_infinitePlaceIdeleClass_eq_iff_real_neg_one
    (v : InfinitePlace K) :
    (globalNormResidueMonoidHom K L).comp
          (IdeleGroup.infinitePlaceIdeleClass v) =
        chosenInfinitePlaceArtinMonoidHom
          (K := K) (L := L) v ↔
      ∀ _hvReal : v.IsReal,
        globalNormResidueMonoidHom K L
            (IdeleGroup.infinitePlaceIdeleClass v
              (-1 : v.Completionˣ)) =
          chosenInfinitePlaceArtinMonoidHom
            (K := K) (L := L) v
            (-1 : v.Completionˣ) := by
  constructor
  · intro h _hvReal
    exact DFunLike.congr_fun h (-1 : v.Completionˣ)
  · intro h
    rcases v.isReal_or_isComplex with hvReal | hvComplex
    · exact
        (globalNormResidueMonoidHom_comp_infinitePlaceIdeleClass_eq_iff_neg_one
          (K := K) (L := L) v hvReal).2
          (h hvReal)
    · exact
        globalNormResidueMonoidHom_comp_infinitePlaceIdeleClass_of_isComplex
          (K := K) (L := L) v hvComplex

/-- The global norm-residue homomorphism restricted to a single
archimedean component is the actual local Artin homomorphism at that
place.

At an unramified archimedean place both maps are trivial.  In the only
remaining case, a ramified real place, positivity reduces the equality
to negative one and the complexification overextension identifies its
global symbol with the genuine local complex conjugation. -/
theorem globalNormResidueMonoidHom_comp_infinitePlaceIdeleClass
    (v : InfinitePlace K) :
    (globalNormResidueMonoidHom K L).comp
          (IdeleGroup.infinitePlaceIdeleClass v) =
      chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := L) v := by
  rw [
    globalNormResidueMonoidHom_comp_infinitePlaceIdeleClass_eq_iff_real_neg_one]
  intro _hvReal
  by_cases hUnramified :
      (chosenInfinitePlaceAbove (L := L) v).IsUnramified K
  · exact
      DFunLike.congr_fun
        (globalNormResidueMonoidHom_comp_infinitePlaceIdeleClass_of_unramified
          (K := K) (L := L) v hUnramified)
        (-1 : v.Completionˣ)
  · exact
      globalNormResidueMonoidHom_infinitePlaceIdeleClass_neg_one_of_ramified
        (K := K) (L := L) v hUnramified

/-- One-place archimedean norm membership is exactly membership in the
local determinant-norm subgroup.  This is the norm-kernel form of
archimedean local-global Artin compatibility. -/
@[simp]
theorem infinitePlaceIdeleClass_mem_ideleClassNorm_range_iff
    (v : InfinitePlace K)
    (x : v.Completionˣ) :
    IdeleGroup.infinitePlaceIdeleClass v x ∈
        (_root_.ideleClassNorm K L).range ↔
      x ∈ infiniteTensorNormSubgroup
        (K := K) (L := L) v := by
  rw [← globalNormResidueMonoidHom_eq_one_iff]
  rw [←
    chosenInfinitePlaceArtinMonoidHom_eq_one_iff_infiniteTensorNorm
      (K := K) (L := L) v x]
  have hcompat :
      globalNormResidueMonoidHom K L
          (IdeleGroup.infinitePlaceIdeleClass v x) =
        chosenInfinitePlaceArtinMonoidHom
          (K := K) (L := L) v x := by
    simpa only [MonoidHom.comp_apply] using
      DFunLike.congr_fun
        (globalNormResidueMonoidHom_comp_infinitePlaceIdeleClass
          (K := K) (L := L) v) x
  rw [hcompat]

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_AbelianConductorExactness
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsCyclotomicExtension _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormExponentNeZero _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldAbsoluteFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldScalarTowerOverOriginal _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.instContinuousSMulPadicLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
attribute [-simp] _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Exact finite ramification loci for abelian norm data

For a finite abelian extension, the modulus constructed from the
actual chosen local norm groups has support exactly the ramified finite
places.  At the archimedean places, the determinant-norm image is the
whole local multiplicative group exactly when the extension is
unramified at infinity.

The finite statement is deliberately about the locally constructed
norm modulus.  Identifying it with the minimal narrow finite conductor also
requires the compatibility between the actual global norm-residue map
and the chosen local Artin map on one-place ideles.
-/

open scoped NumberField Classical NumberField.LiesOver

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open LocalClassFieldTheory LocalFieldTheory
open NumberField IsDedekindDomain

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

omit [FiniteDimensional K L] in
/-- A ramified real-to-complex completion makes the corresponding
archimedean tensor norm subgroup proper. -/
private theorem infiniteTensorNormSubgroup_ne_top_of_isRamified
    (v : InfinitePlace K)
    (w : InfinitePlace L)
    (hw : w.comap (algebraMap K L) = v)
    (hramified : w.IsRamified K) :
    _root_.infiniteTensorNormSubgroup
      (K := K) (L := L) v ≠ ⊤ := by
  let : w.1.LiesOver v.1 :=
    ⟨congrArg (fun q : InfinitePlace K => q.1) hw⟩
  rw [
    _root_.infiniteTensorNormSubgroup_eq_localNormSubgroup
      (K := K) (L := L) v w hw]
  have hvReal : v.IsReal := by
    rw [← hw]
    exact hramified.isReal
  let eRealField :
      v.Completion ≃+* ℝ :=
    InfinitePlace.Completion.ringEquivRealOfIsReal
      hvReal
  let eRealUnits :
      v.Completionˣ ≃* ℝˣ :=
    Units.mapEquiv eRealField.toMulEquiv
  have hwComplex : w.IsComplex :=
    hramified.isComplex
  let eComplexField :
      w.Completion ≃+* ℂ :=
    InfinitePlace.Completion.ringEquivComplexOfIsComplex
      hwComplex
  let eComplexUnits :
      w.Completionˣ ≃* ℂˣ :=
    Units.mapEquiv eComplexField.toMulEquiv
  let :
      NumberField.ComplexEmbedding.LiesOver
        (InfinitePlace.Completion.extensionEmbedding w)
        (InfinitePlace.Completion.extensionEmbedding v) :=
    InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal
      w hvReal
  have hCompletionCompatible :
      RingHom.comp (algebraMap ℝ ℂ) eRealField =
        RingHom.comp eComplexField
          (algebraMap v.Completion w.Completion) := by
    ext x
    change
      (InfinitePlace.Completion.extensionEmbeddingOfIsReal hvReal x : ℂ) =
        InfinitePlace.Completion.extensionEmbedding w
          ((algebraMap v.Completion w.Completion) x)
    rw [InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
    exact
      (InfinitePlace.Completion.liesOver_extensionEmbedding_apply
        w (v := v)).symm
  have hCompletionCompatibleSymm :=
    LocalClassFieldTheory.ringEquiv_compat_symm
      eRealField eComplexField hCompletionCompatible
  have hRealComplexNormTransport :
      (localNormSubgroup ℝ ℂ).map
          eRealUnits.symm.toMonoidHom =
        localNormSubgroup
          v.Completion w.Completion := by
    ext x
    constructor
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      refine ⟨eComplexUnits.symm z, ?_⟩
      exact
        (LocalClassFieldTheory.normUnits_map_ringEquiv
          eRealField.symm eComplexField.symm
          hCompletionCompatibleSymm z).symm
    · rintro ⟨z, rfl⟩
      refine
        ⟨normUnits ℝ ℂ (eComplexUnits z),
          ⟨eComplexUnits z, rfl⟩, ?_⟩
      calc
        eRealUnits.symm
            (normUnits ℝ ℂ (eComplexUnits z)) =
            normUnits v.Completion w.Completion
              (eComplexUnits.symm (eComplexUnits z)) := by
          exact
            LocalClassFieldTheory.normUnits_map_ringEquiv
              eRealField.symm eComplexField.symm
              hCompletionCompatibleSymm
              (eComplexUnits z)
        _ = normUnits v.Completion w.Completion z := by
          rw [eComplexUnits.symm_apply_apply]
  have hNegativeOne :
      (-1 : ℝˣ) ∉ localNormSubgroup ℝ ℂ := by
    rw [
      ← LocalClassFieldTheory.realUnitsSign_ker_eq_complexNormSubgroup,
      LocalClassFieldTheory.mem_realUnitsSign_ker_iff]
    norm_num
  intro htop
  have hx :
      eRealUnits.symm (-1 : ℝˣ) ∈
        localNormSubgroup v.Completion w.Completion := by
    rw [htop]
    exact Subgroup.mem_top _
  rw [← hRealComplexNormTransport] at hx
  obtain ⟨z, hz, hzEq⟩ := hx
  have hzNegativeOne : z = (-1 : ℝˣ) :=
    eRealUnits.symm.injective hzEq
  exact hNegativeOne (hzNegativeOne ▸ hz)

omit [FiniteDimensional K L] in
/-- At a base infinite place, the determinant-norm image is the whole
local multiplicative group exactly when the extension is unramified
above that place. -/
theorem infiniteTensorNormSubgroup_eq_top_iff_isUnramifiedIn
    (v : InfinitePlace K) :
    _root_.infiniteTensorNormSubgroup
          (K := K) (L := L) v = ⊤ ↔
      v.IsUnramifiedIn L := by
  obtain ⟨w, hw⟩ :=
    InfinitePlace.comap_surjective
      (K := L) v
  have hUnramified :
      v.IsUnramifiedIn L ↔ w.IsUnramified K := by
    rw [← hw, InfinitePlace.isUnramifiedIn_comap]
  rw [hUnramified]
  constructor
  · intro htop
    by_contra hramified
    have hRamified : w.IsRamified K :=
      hramified
    exact
      (infiniteTensorNormSubgroup_ne_top_of_isRamified
        (K := K) (L := L) v w hw hRamified)
        htop
  · intro hunramified
    let : w.1.LiesOver v.1 :=
      ⟨congrArg (fun q : InfinitePlace K => q.1) hw⟩
    rw [
      _root_.infiniteTensorNormSubgroup_eq_localNormSubgroup
        (K := K) (L := L) v w hw]
    apply top_unique
    intro x _
    refine
      ⟨Units.map
          (algebraMap
            v.Completion w.Completion).toMonoidHom x, ?_⟩
    apply Units.ext
    change
      Algebra.norm v.Completion
          (algebraMap v.Completion w.Completion
            (x : v.Completion)) =
        (x : v.Completion)
    rw [
      Algebra.norm_algebraMap,
      InfinitePlace.IsUnramified.finrank_eq_one
        v hunramified,
      pow_one]

/-- The infinite part of the full conductor of an idèle-class norm range is
exactly the set of ramified real places. -/
theorem ideleClassNormFullConductor_infinitePart_eq_realRamificationLocus :
    (ideleClassNormConductorialSubgroup
        (K := K) (L := L)).fullConductor.infinitePart =
      (Finset.univ.filter fun v : RayClass.RealPlace K =>
        ¬ v.1.IsUnramifiedIn L) := by
  classical
  ext v
  change
    v ∈ (ideleClassNormConductorialSubgroup
        (K := K) (L := L)).fullConductorInfinitePart ↔
      v ∈ (Finset.univ.filter fun w : RayClass.RealPlace K =>
        ¬ w.1.IsUnramifiedIn L)
  rw [ConductorialSubgroup.mem_fullConductorInfinitePart_iff,
    Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  change
    (¬ (IdeleGroup.infinitePlaceIdeleClass v.1).range ≤
        (_root_.ideleClassNorm K L).range) ↔
      ¬ v.1.IsUnramifiedIn L
  apply not_congr
  calc
    (IdeleGroup.infinitePlaceIdeleClass v.1).range ≤
          (_root_.ideleClassNorm K L).range ↔
        _root_.infiniteTensorNormSubgroup
            (K := K) (L := L) v.1 = ⊤ := by
      constructor
      · intro hRange
        apply top_unique
        intro x _hx
        apply
          (Reciprocity.infinitePlaceIdeleClass_mem_ideleClassNorm_range_iff
            (K := K) (L := L) v.1 x).1
        exact hRange ⟨x, rfl⟩
      · intro hTop
        rintro _ ⟨x, rfl⟩
        apply
          (Reciprocity.infinitePlaceIdeleClass_mem_ideleClassNorm_range_iff
            (K := K) (L := L) v.1 x).2
        rw [hTop]
        exact Subgroup.mem_top x
    _ ↔ v.1.IsUnramifiedIn L :=
      infiniteTensorNormSubgroup_eq_top_iff_isUnramifiedIn
        (K := K) (L := L) v.1

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_ClassFieldKernel
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsCyclotomicExtension _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormExponentNeZero _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldAbsoluteFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldScalarTowerOverOriginal _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The even Artin kernel for totally real extensions

The ordinary finite congruence modulus needed by even Hecke characters is
obtained from the actual class-field conductor, whose infinite part is
empty in a totally real extension.
-/

open scoped NumberField

noncomputable section

namespace DukePrimeDegree

open GlobalClassFieldTheory GlobalClassFieldTheory.GlobalClassFields
  GlobalClassFieldTheory.IdealClassFieldTheory

/-- The norm subgroup of a totally real abelian extension has a defining
modulus with no infinite places. -/
theorem exists_even_artin_modulus
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsAbelianGalois K L] [NumberField.IsTotallyReal L] :
    ∃ m : RayClass.Modulus K, m.infinitePart = ∅ ∧
      m.congruenceSubgroup ≤ (ideleClassNorm K L).range := by
  classical
  let H := ideleClassNormConductorialSubgroup (K := K) (L := L)
  refine ⟨H.fullConductor, ?_, H.fullConductor_isDefiningModulus⟩
  change (ideleClassNormConductorialSubgroup (K := K) (L := L)).fullConductor.infinitePart = ∅
  rw [ideleClassNormFullConductor_infinitePart_eq_realRamificationLocus]
  apply Finset.filter_eq_empty_iff.mpr
  intro v _ hv
  apply hv
  intro w _
  exact (NumberField.IsTotallyReal.isReal w).isUnramified K

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PrimeFactors
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFintype _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.ValuationSubring.charP _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology


namespace PrimeDegreePackets
universe v

lemma ennreal_tsum_fintype_prod {ι : Type u} [Fintype ι]
    (κ : ι → Type v) (f : ∀ i, κ i → ℝ≥0∞) :
    (∑' k : ∀ i, κ i, ∏ i, f i (k i)) = ∏ i, ∑' x : κ i, f i x := by
  classical
  revert κ f
  refine Fintype.induction_empty_option (P := fun ι [Fintype ι] =>
    ∀ (κ : ι → Type v) (f : ∀ i, κ i → ℝ≥0∞),
      (∑' k : ∀ i, κ i, ∏ i, f i (k i)) = ∏ i, ∑' x : κ i, f i x)
    ?_ ?_ ?_ ι
  · intro α β _ e ih κ f
    let : Fintype α := Fintype.ofEquiv β e.symm
    have h := ih (fun i => κ (e i)) (fun i => f (e i))
    rw [← (Equiv.piCongrLeft κ e).tsum_eq]
    convert h using 1
    · apply tsum_congr
      intro k
      exact (Fintype.prod_equiv e _ _ (by intro i; simp)).symm
    · exact (Fintype.prod_equiv e _ _ (by intro i; rfl)).symm
  · intro κ f
    simp
  · intro α _ ih κ f
    rw [← Equiv.piOptionEquivProd.symm.tsum_eq]
    simp only [Fintype.prod_option]
    change (∑' c : κ none × (∀ i, κ (some i)),
      f none c.1 * ∏ i, f (some i) (c.2 i)) = _
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_mul_right, ih]



end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IdealCoefficients
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.nthRootsSubgroupFintype _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFintype _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalOrdinaryNormQuotientAdditiveTypeAddCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.scaledRelativeIntegerLatticeQuotientFinite
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology

open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
namespace PrimeDegreePackets

variable (K : Type*) [Field K] [NumberField K]



lemma idealCoefficient_pos (m : ℕ) (hm : m ≠ 0) :
    idealCoefficient K m = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = m} := by
  simp [idealCoefficient,hm]

lemma idealCoefficient_one : idealCoefficient K 1 = 1 := by
  simp [idealCoefficient, Ideal.absNorm_eq_one_iff]

lemma idealCoefficient_multiplicative : (idealCoefficient K).IsMultiplicative := by
  refine ⟨idealCoefficient_one K, ?_⟩
  intro m n hmn
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  rw [idealCoefficient_pos K _ (mul_ne_zero hm hn), idealCoefficient_pos K _ hm,
    idealCoefficient_pos K _ hn, ← Nat.card_prod]
  exact Nat.card_congr (idealNormProductEquiv K m n hm hn hmn).symm


open Filter Topology Asymptotics

lemma idealCoefficientReal_nonneg (m : ℕ) : 0 ≤ idealCoefficientReal K m := Nat.cast_nonneg _

 
lemma idealCoefficient_summatory_limit :
    Tendsto (fun n : ℕ => (∑k ∈ Icc 1 n, idealCoefficientReal K k) / (n:ℝ))
      atTop (𝓝 (NumberField.dedekindZeta_residue K)) := by
  refine ((NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n => ?_
  simp only [Function.comp_apply, Nat.cast_le]
  congr 1
  simp only [idealCoefficientReal,ArithmeticFunction.coe_mk]
  rw [←Nat.cast_sum]
  congr 1
  rw [←add_left_inj 1, ←Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Icc_succ_left_eq_Ioc _ _]
  have H : (∑k ∈ Ioc 0 n, idealCoefficient K k) =
      ∑k ∈ Ioc 0 n, Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} := by
    apply sum_congr rfl
    intro k hk
    exact idealCoefficient_pos K k (Nat.ne_of_gt (Finset.mem_Ioc.mp hk).1)
  rw [H, show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by
      simp [Ideal.absNorm_eq_zero_iff], sum_Ioc_add_eq_sum_Icc n.zero_le,
    ←card_preimage_eq_sum_card_image_eq (fun k _ => Ideal.finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

lemma idealCoefficient_LSeriesSummable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun m => (idealCoefficientReal K m : ℂ)) s := by
  refine LSeriesSummable_of_sum_norm_bigO_and_nonneg ?_ (idealCoefficientReal_nonneg K) zero_le_one hs
  apply isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
  simpa using idealCoefficient_summatory_limit K


lemma idealCoefficient_LSeries_eq (s : ℂ) :
    LSeries (fun m => (idealCoefficientReal K m : ℂ)) s = NumberField.dedekindZeta K s := by
  apply LSeries_congr _ s
  intro m hm
  simp only [idealCoefficientReal,ArithmeticFunction.coe_mk,idealCoefficient_pos K m hm,
    Complex.ofReal_natCast]


end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PrimeSums
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalOrdinaryNormQuotientAdditiveTypeAddCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.scaledRelativeIntegerLatticeQuotientFinite
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid


namespace PrimeDegreePackets
open scoped ENNReal


variable (K : Type*) [Field K] [NumberField K]

lemma idealsOverPrime_norm_two_le {p : ℕ} {P : Ideal (𝓞 K)}
    (hP : P ∈ idealsOverPrime K p) : 2 ≤ Ideal.absNorm P := by
  have hP0 : Ideal.absNorm P ≠ 0 := by
    exact fun he => (idealsOverPrime_prime K hP).ne_zero (Ideal.absNorm_eq_zero_iff.mp he)
  have hP1 : Ideal.absNorm P ≠ 1 := by
    intro he
    have := Ideal.absNorm_eq_one_iff.mp he
    exact (idealsOverPrime_prime K hP).not_isUnit (by simp [this])
  omega



end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootOverlaps
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldAbsoluteFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.nthRootsSubgroupFintype _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalClassFieldTheory.localDecompositionResidueFintype _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.Padic.padicUnitFiniteFactor_finite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.GlobalClassFieldTheory.GlobalClassFields.narrowClassGroup_finite _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalOrdinaryNormQuotientAdditiveTypeAddCommGroup _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.scaledRelativeIntegerLatticeQuotientFinite
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory

open MeasureTheory

open scoped BigOperators ENNReal
namespace PrimeDegreePackets
universe v

lemma complex_summable_fintype_prod {ι : Type*} [Fintype ι]
    (κ : ι → Type v) (f : ∀ i, κ i → ℂ)
    (hf : ∀ i, Summable (fun a => ‖f i a‖)) :
    Summable (fun k : ∀ i, κ i => ‖∏ i, f i (k i)‖) := by
  classical
  apply tsum_enorm_ne_top_iff_summable_norm.mp
  simp only [enorm_eq_nnnorm, nnnorm_prod, ENNReal.ofNNReal_finsetProd]
  rw [ennreal_tsum_fintype_prod κ (fun i a => (‖f i a‖₊ : ℝ≥0∞))]
  exact ENNReal.prod_ne_top (fun i _ => tsum_enorm_ne_top_iff_summable_norm.mpr (hf i))

lemma complex_tsum_fintype_prod {ι : Type*} [Fintype ι]
    (κ : ι → Type v) (f : ∀ i, κ i → ℂ)
    (hf : ∀ i, Summable (fun a => ‖f i a‖)) :
    (∑' k : ∀ i, κ i, ∏ i, f i (k i)) = ∏ i, ∑' x : κ i, f i x := by
  classical
  revert κ f
  refine Fintype.induction_empty_option (P := fun ι [Fintype ι] =>
    ∀ (κ : ι → Type v) (f : ∀ i, κ i → ℂ),
      (∀ i, Summable (fun a => ‖f i a‖)) →
      (∑' k : ∀ i, κ i, ∏ i, f i (k i)) = ∏ i, ∑' x : κ i, f i x)
    ?_ ?_ ?_ ι
  · intro α β _ e ih κ f hf
    let : Fintype α := Fintype.ofEquiv β e.symm
    have h := ih (fun i => κ (e i)) (fun i => f (e i)) (fun i => hf (e i))
    rw [← (Equiv.piCongrLeft κ e).tsum_eq]
    convert h using 1
    · apply tsum_congr
      intro k
      exact (Fintype.prod_equiv e _ _ (by intro i; simp)).symm
    · exact (Fintype.prod_equiv e _ _ (by intro i; rfl)).symm
  · intro κ f _
    simp
  · intro α _ ih κ f hf
    rw [← Equiv.piOptionEquivProd.symm.tsum_eq]
    simp only [Fintype.prod_option]
    change (∑' c : κ none × (∀ i, κ (some i)),
      f none c.1 * ∏ i, f (some i) (c.2 i)) = _
    rw [←tsum_mul_tsum_of_summable_norm (hf none)
      (complex_summable_fintype_prod _ _ (fun i => hf (some i))), ih _ _ (fun i => hf (some i))]

lemma complex_tsum_multiset_prod {α : Type*} [Fintype α]
    (f : α → ℂ) (hf : ∀ a, ‖f a‖ < 1) :
    Summable (fun m : Multiset α => ‖(m.map f).prod‖) ∧
    (∑' m : Multiset α, (m.map f).prod) = ∏ a, (1-f a)⁻¹ := by
  classical
  let e : (α → ℕ) ≃ Multiset α :=
    Finsupp.equivFunOnFinite.symm.trans Multiset.toFinsupp.symm.toEquiv
  have hm (m : Multiset α) : (m.map f).prod = ∏ a, f a ^ m.count a := by
    rw [Finset.prod_multiset_map_count]
    apply Finset.prod_subset (Finset.subset_univ _)
    intro a _ ha
    rw [Multiset.count_eq_zero.mpr (by simpa using ha),pow_zero]
  have he (k : α → ℕ) (a : α) : (e k).count a = k a := by simp [e]
  have hfS (a : α) : Summable (fun k : ℕ => ‖f a ^ k‖) := by
    simpa only [norm_pow] using summable_geometric_of_norm_lt_one
      (show ‖‖f a‖‖ < 1 by simpa using hf a)
  have hS := complex_summable_fintype_prod (fun _ : α => ℕ) (fun a k => f a ^ k) hfS
  have hT := complex_tsum_fintype_prod (fun _ : α => ℕ) (fun a k => f a ^ k) hfS
  constructor
  · rw [←e.summable_iff]
    simpa only [Function.comp_def,hm,he] using hS
  · rw [←e.tsum_eq]
    simp only [hm,he]
    rw [hT]
    apply Finset.prod_congr rfl
    intro a _
    exact tsum_geometric_of_norm_lt_one (hf a)

end PrimeDegreePackets

open NumberField Finset
namespace PrimeDegreePackets
variable (K : Type*) [Field K] [NumberField K]

lemma zetaSummand_norm_lt_one {s : ℂ} (hs : 1 < s.re) {m : ℕ} (hm : 2 ≤ m) :
    ‖riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs) m‖ < 1 := by
  change ‖(m : ℂ)^(-s)‖ < 1
  rw [←Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_nonneg (Nat.cast_nonneg m)
      (Complex.re_neg_ne_zero_of_one_lt_re hs),Complex.neg_re]
  apply Real.rpow_lt_one_of_one_lt_of_neg
  · exact_mod_cast hm
  · linarith

lemma primary_ideal_complex_series {s : ℂ} (hs : 1 < s.re) {p : ℕ} :
    Summable (fun I : PrimaryIdeal K p =>
      ‖riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs) (Ideal.absNorm I.1)‖) ∧
    (∑' I : PrimaryIdeal K p,
      riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs) (Ideal.absNorm I.1)) =
      ∏ P : idealsOverPrime K p,
        (1-riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs) (Ideal.absNorm P.1))⁻¹ := by
  classical
  let H := riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs)
  have HM (m : Multiset (idealsOverPrime K p)) :
      H (Ideal.absNorm (primaryIdealMultisetEquiv K p m).1) =
        (m.map (fun P => H (Ideal.absNorm P.1))).prod := by
    rw [primaryIdealMultisetEquiv_val]
    induction m using Multiset.induction_on with
    | empty => simp
    | @cons P m ih =>
      simp only [Multiset.map_cons,Multiset.prod_cons,map_mul]
      exact congrArg (fun z => H (Ideal.absNorm P.1)*z) ih
  obtain ⟨hS,hT⟩ := complex_tsum_multiset_prod
    (fun P : idealsOverPrime K p => H (Ideal.absNorm P.1))
    (fun P => zetaSummand_norm_lt_one hs (idealsOverPrime_norm_two_le K P.2))
  constructor
  · rw [←(primaryIdealMultisetEquiv K p).summable_iff]
    change Summable (fun m => ‖H (Ideal.absNorm (primaryIdealMultisetEquiv K p m).1)‖)
    simpa only [HM] using hS
  · rw [←(primaryIdealMultisetEquiv K p).tsum_eq]
    exact (tsum_congr HM).trans hT

lemma norm_fiber_complex_tsum (m : ℕ) (hm : m ≠ 0) (F : ℕ → ℂ) :
    (∑' I : {I : Ideal (𝓞 K) // Ideal.absNorm I = m}, F (Ideal.absNorm I.1)) =
      (idealCoefficient K m : ℂ) * F m := by
  classical
  have : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = m} :=
    (Ideal.finite_setOfPred_absNorm_eq _).to_subtype
  let : Fintype {I : Ideal (𝓞 K) // Ideal.absNorm I = m} := Fintype.ofFinite _
  have he : (fun I : {I : Ideal (𝓞 K) // Ideal.absNorm I = m} => F (Ideal.absNorm I.1)) =
      (fun _ => F m) := funext (fun I => congrArg F I.2)
  rw [he,tsum_fintype,sum_const,idealCoefficient_pos K m hm,Nat.card_eq_fintype_card,
    nsmul_eq_mul,Finset.card_univ]

lemma primary_ideal_tsum_by_norm {p : ℕ} (hp : p.Prime) (H : ℕ → ℂ)
    (HS : Summable (fun I : PrimaryIdeal K p => H (Ideal.absNorm I.1))) :
    (∑' I : PrimaryIdeal K p, H (Ideal.absNorm I.1)) =
      ∑' e : ℕ, (idealCoefficient K (p^e) : ℂ) * H (p^e) := by
  have HE : Summable (fun I : Σe : ℕ, {I : Ideal (𝓞 K) // Ideal.absNorm I = p^e} =>
      H (Ideal.absNorm I.2.1)) :=
    (primaryIdealNormEquiv K p hp).summable_iff.mpr HS
  calc
    _ = ∑' I : Σe : ℕ, {I : Ideal (𝓞 K) // Ideal.absNorm I = p^e},
          H (Ideal.absNorm I.2.1) :=
      ((primaryIdealNormEquiv K p hp).tsum_eq (fun I => H (Ideal.absNorm I.1))).symm
    _ = ∑' e : ℕ, ∑' I : {I : Ideal (𝓞 K) // Ideal.absNorm I = p^e},
          H (Ideal.absNorm I.1) := HE.tsum_sigma
    _ = _ := tsum_congr (fun e => norm_fiber_complex_tsum K _ (pow_ne_zero _ hp.ne_zero) H)

lemma ideal_local_complex_euler {s : ℂ} (hs : 1 < s.re) {p : ℕ} (hp : p.Prime) :
    (∑' e : ℕ, (idealCoefficient K (p^e) : ℂ) *
      riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs) (p^e)) =
        ∏ P : idealsOverPrime K p,
          (1-riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs) (Ideal.absNorm P.1))⁻¹ := by
  have HD := primary_ideal_complex_series K hs (p := p)
  exact (primary_ideal_tsum_by_norm K hp _ HD.1.of_norm).symm.trans HD.2

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma primePower_succ_injective : Function.Injective
    (fun a : Nat.Primes × ℕ => (a.1 : ℕ) ^ (a.2+1)) := by
  rintro ⟨p,k⟩ ⟨q,l⟩ h
  obtain ⟨hp,hk⟩ := p.property.pow_inj q.property h
  exact Prod.ext (Subtype.ext hp) hk

 

theorem complex_multiplicative_tsum_ne_zero
    (f : ℕ → ℂ) (hzero : f 0 = 0) (hone : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → f (m*n) = f m * f n)
    (hs : Summable (fun m => ‖f m‖))
    (hlocal : ∀ p : Nat.Primes, (∑' k : ℕ, f ((p:ℕ)^k)) ≠ 0) :
    (∑' m : ℕ, f m) ≠ 0 := by
  let E (p : Nat.Primes) : ℂ := ∑' k : ℕ, f ((p:ℕ)^k)
  have hpS (p : Nat.Primes) : Summable (fun k : ℕ => f ((p:ℕ)^k)) :=
    hs.of_norm.comp_injective (Nat.pow_right_injective p.property.two_le)
  have hspp : Summable (fun a : Nat.Primes × ℕ => f ((a.1:ℕ)^(a.2+1))) :=
    hs.of_norm.comp_injective primePower_succ_injective
  have he (p : Nat.Primes) : E p = 1 + ∑' k : ℕ, f ((p:ℕ)^(k+1)) := by
    change (∑' k : ℕ, f ((p:ℕ)^k)) = _
    rw [(hpS p).tsum_eq_zero_add]
    simp only [pow_zero,hone]
  have hdev : Summable (fun p : Nat.Primes => 1-E p) := by
    have H := hspp.prod.neg
    exact H.congr (fun p => by dsimp; rw [he]; ring)
  have hl : Summable (fun p : Nat.Primes => Complex.log (E p)) := by
    simpa only [sub_sub_cancel] using hdev.clog_one_sub
  have hP := hl.hasSum.cexp
  have hexp (p : Nat.Primes) : Complex.exp (Complex.log (E p)) = E p :=
    Complex.exp_log (hlocal p)
  simp only [Function.comp_def,hexp] at hP
  have hE : HasProd E (∑' m : ℕ, f m) :=
    EulerProduct.eulerProduct_hasProd hone hmul hs hzero
  rw [hE.unique hP]
  exact Complex.exp_ne_zero _

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma dedekindZeta_ne_zero_of_one_lt_re (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 < s.re) : NumberField.dedekindZeta K s ≠ 0 := by
  classical
  let H := riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs)
  let f (m : ℕ) : ℂ := (idealCoefficient K m : ℂ) * H m
  have hf (m : ℕ) : f m = LSeries.term (fun k => (idealCoefficientReal K k : ℂ)) s m := by
    by_cases hm : m = 0
    · subst m
      simp [f]
    · simp only [f,H,riemannZetaSummandHom,MonoidWithZeroHom.coe_mk,ZeroHom.coe_mk,
        LSeries.term_of_ne_zero hm,idealCoefficientReal,ArithmeticFunction.coe_mk,
        Complex.ofReal_natCast,Complex.cpow_neg,div_eq_mul_inv]
  have hS : Summable (fun m => ‖f m‖) := by
    simpa only [hf] using (idealCoefficient_LSeriesSummable K hs).norm
  have h0 : f 0 = 0 := by simp [f]
  have h1 : f 1 = 1 := by simp [f,idealCoefficient_one]
  have hm {m n : ℕ} (h : m.Coprime n) : f (m*n) = f m * f n := by
    simp only [f,(idealCoefficient_multiplicative K).map_mul_of_coprime h,
      Nat.cast_mul,map_mul]
    ring
  have hE (p : Nat.Primes) : (∑' k : ℕ, f ((p:ℕ)^k)) ≠ 0 := by
    change (∑' k : ℕ, (idealCoefficient K ((p:ℕ)^k) : ℂ) * H ((p:ℕ)^k)) ≠ 0
    rw [ideal_local_complex_euler K hs p.property]
    apply Finset.prod_ne_zero_iff.mpr
    intro P _
    apply inv_ne_zero
    intro he
    have hn := zetaSummand_norm_lt_one hs (idealsOverPrime_norm_two_le K P.2)
    rw [←sub_eq_zero.mp he,norm_one] at hn
    exact (lt_irrefl _ hn)
  have HN := complex_multiplicative_tsum_ne_zero f h0 h1 (fun h => hm h) hS hE
  have he : (∑' m : ℕ, f m) = NumberField.dedekindZeta K s := by
    calc
      _ = LSeries (fun k => (idealCoefficientReal K k : ℂ)) s := tsum_congr hf
      _ = _ := idealCoefficient_LSeries_eq K s
  rwa [he] at HN

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RayFrobenius
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAbstractExtension.ramificationQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.representedQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.residueQuotientFinite _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientRepresentedQuotientFinite _root_.ClassFormation.DegreeData.FiniteResidueAbstractExtension.instFiniteQuotientSubtypeMemSubgroupFieldBaseExtensionSubgroupField _root_.ClassFormation.DegreeData.FiniteTower.baseQuotientFinite _root_.ClassFormation.DegreeData.FiniteTower.topQuotientFinite _root_.ClassFormation.DegreeData.FiniteTower.totalQuotientFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.baseAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.fieldAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.baseRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.fieldRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.relativeRepresentedQuotientFinite _root_.ClassFormation.FiniteAbstractField.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionFinite _root_.ClassFormation.FiniteAbstractFieldExtension.instFiniteQuotientSubtypeMemSubgroupFieldBaseExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerBaseSubgroupAbsoluteQuotientFinite _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerExtensionQuotientFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite_of_isSeparable _root_.LocalClassFieldTheory.finiteGaloisExtensionQuotientOfEmbedding_finite _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.finiteUnramifiedNormQuotient _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSubquotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientMaximalIdealPowFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModHigherPrincipalUnitGroupFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.Padic.padicUnitFiniteFactor_finite _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.narrowClassGroup_finite _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalOrdinaryNormQuotientAdditiveTypeAddCommGroup _root_.LocalClassFieldTheory.finiteGaloisAbstractExtensionOfEmbedding_bundle_finite _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup _root_.scaledRelativeIntegerLatticeQuotientFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Module Filter
open scoped NumberField nonZeroDivisors BigOperators Classical
namespace PrimeDegreePackets
namespace GaloisIdealCharacter

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]


lemma primeFrobenius_spec (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    IsArithFrobAt (𝓞 F) (primeFrobenius F E P) (primeAbove F E P).val := by
  let Q := primeAbove F E P
  let : Q.val.IsPrime := Q.property.1
  let : Q.val.IsMaximal := Q.property.1.isMaximal (primeAbove_ne_bot F E P)
  exact IsArithFrobAt.arithFrobAt (𝓞 F) (E ≃ₐ[F] E) Q.val

variable (χ : (E ≃ₐ[F] E) →* ℂˣ)

lemma idealHom_prime (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    idealHom F E χ (integralIdealFractionalUnit P.asIdeal P.ne_bot) =
      χ (primeFrobenius F E P) := by
  change (∏ᶠ Q : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
    χ (primeFrobenius F E Q) ^ FractionalIdeal.count F Q
      (P.asIdeal : FractionalIdeal (𝓞 F)⁰ F)) = _
  rw [finprod_eq_single _ P]
  · rw [FractionalIdeal.count_self, zpow_one]
  · intro Q hQP
    rw [FractionalIdeal.count_maximal, ite_eq_right hQP.symm, zpow_zero]

lemma idealHom_finiteOrder : ∃ e : ℕ, 0 < e ∧ ∀ I, idealHom F E χ I ^ e = 1 := by
  refine ⟨Nat.card (E ≃ₐ[F] E), Nat.card_pos, ?_⟩
  intro I
  change (∏ᶠ P : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
    χ (primeFrobenius F E P) ^ FractionalIdeal.count F P I.val) ^ _ = 1
  rw [finprod_pow (finite_factor_support F E χ I)]
  have hpow (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
      (χ (primeFrobenius F E P) ^ FractionalIdeal.count F P I.val) ^
        Nat.card (E ≃ₐ[F] E) = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← map_pow,
      pow_card_eq_one', map_one, one_zpow]
  simp only [hpow, finprod_one]



end GaloisIdealCharacter
end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_FrobeniusConductor
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalOrdinaryNormQuotientAdditiveTypeAddCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.scaledRelativeIntegerLatticeQuotientFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Module
open scoped NumberField nonZeroDivisors

namespace PrimeDegreePackets
variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E]

lemma unramified_of_absDiscr_not_mem (F E : Type*)
    [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : Ideal (𝓞 F)) (Q : Ideal (𝓞 E)) [Q.IsPrime]
    (hQ : Q.under (𝓞 F) = P) (hD : ((NumberField.discr E).natAbs : 𝓞 F) ∉ P) :
    Algebra.IsUnramifiedAt (𝓞 F) Q := by
  have hDE : ((NumberField.discr E).natAbs : 𝓞 E) ∉ Q := by
    intro h
    apply hD
    rw [← hQ]
    change algebraMap (𝓞 F) (𝓞 E) _ ∈ Q
    simpa only [map_natCast] using h
  have hnot : ¬ Q ∣ differentIdeal ℤ (𝓞 E) := by
    intro h
    apply hDE
    apply (Ideal.dvd_iff_le.mp h)
    rw [← NumberField.absNorm_differentIdeal E (𝓞 E)]
    exact Ideal.absNorm_mem _
  have : Algebra.IsUnramifiedAt ℤ Q := not_dvd_differentIdeal_iff.mp hnot
  exact Algebra.IsUnramifiedAt.of_restrictScalars ℤ Q

lemma principal_count_ne_zero_iff_mem (a : 𝓞 F) (ha : a ≠ 0)
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    FractionalIdeal.count F P (Ideal.span {a}) ≠ 0 ↔ a ∈ P.asIdeal := by
  have hI : Ideal.span {a} ≠ (0 : Ideal (𝓞 F)) := by
    simpa only [Ideal.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot] using ha
  rw [FractionalIdeal.count_coe F P hI, Int.natCast_ne_zero,
    Associates.count_ne_zero_iff_dvd hI P.irreducible, Ideal.dvd_iff_le,
    Ideal.span_singleton_le_iff_mem]

end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_SplitEuler
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldAbsoluteFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.nthRootsSubgroupFintype _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFintype _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalOrdinaryNormQuotientAdditiveTypeAddCommGroup _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.scaledRelativeIntegerLatticeQuotientFinite
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Module NumberField Filter Topology
open scoped NumberField nonZeroDivisors Classical BigOperators
namespace PrimeDegreePackets

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E]



lemma primeIdealTowerEquiv_val (p : ℕ) (hp : p ≠ 0)
    (PQ : Σ P : idealsOverPrime F p, Ideal.primesOver P.val (𝓞 E)) :
    (primeIdealTowerEquiv F E p hp PQ).val = PQ.2.val := rfl



lemma primeIdealEulerFactor_eq_pow {p : ℕ} (hp : p ≠ 0) (n : ℕ) (s : ℂ)
    (hc : ∀ P : idealsOverPrime F p, Nat.card (Ideal.primesOver P.val (𝓞 E)) = n)
    (hn : ∀ P : idealsOverPrime F p, ∀ Q : Ideal.primesOver P.val (𝓞 E),
      Ideal.absNorm Q.val = Ideal.absNorm P.val) :
    primeIdealEulerFactor E p s = primeIdealEulerFactor F p s ^ n := by
  let (P : idealsOverPrime F p) : Fintype (Ideal.primesOver P.val (𝓞 E)) :=
    by
      let : P.val.IsPrime := ((mem_idealsOverPrime_iff F hp _).mp P.property).1
      exact (Algebra.QuasiFinite.finite_primesOver P.val).fintype
  unfold primeIdealEulerFactor
  rw [← (primeIdealTowerEquiv F E p hp).prod_comp]
  simp only [primeIdealTowerEquiv_val, Fintype.prod_sigma, hn]
  simp only [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hc]
  exact Finset.prod_pow _ _ _

lemma dedekindZeta_hasProd (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => primeIdealEulerFactor K p s) (NumberField.dedekindZeta K s) := by
  let H := riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs)
  let f (m : ℕ) : ℂ := (idealCoefficient K m : ℂ) * H m
  have hf (m : ℕ) : f m = LSeries.term (fun k => (idealCoefficientReal K k : ℂ)) s m := by
    by_cases hm : m = 0
    · subst m
      simp [f]
    · simp only [f,H,riemannZetaSummandHom,MonoidWithZeroHom.coe_mk,ZeroHom.coe_mk,
        LSeries.term_of_ne_zero hm,idealCoefficientReal,ArithmeticFunction.coe_mk,
        Complex.ofReal_natCast,Complex.cpow_neg,div_eq_mul_inv]
  have hS : Summable (fun m => ‖f m‖) := by
    simpa only [hf] using (idealCoefficient_LSeriesSummable K hs).norm
  have h0 : f 0 = 0 := by simp [f]
  have h1 : f 1 = 1 := by simp [f,idealCoefficient_one]
  have hm {m n : ℕ} (h : m.Coprime n) : f (m*n) = f m * f n := by
    simp only [f,(idealCoefficient_multiplicative K).map_mul_of_coprime h,
      Nat.cast_mul,map_mul]
    ring
  have HE := EulerProduct.eulerProduct_hasProd h1 (fun h => hm h) hS h0
  have he : (∑' m : ℕ, f m) = NumberField.dedekindZeta K s := by
    calc
      _ = LSeries (fun k => (idealCoefficientReal K k : ℂ)) s := tsum_congr hf
      _ = _ := idealCoefficient_LSeries_eq K s
  rw [he] at HE
  exact HE.congr_fun (fun p => (ideal_local_complex_euler K hs p.property).symm)

lemma primeEuler_denominator_ne_zero_at_one (K : Type*) [Field K] [NumberField K]
    {p : ℕ} (P : idealsOverPrime K p) :
    1 - (Ideal.absNorm P.val : ℂ) ^ (-(1 : ℂ)) ≠ 0 := by
  rw [Complex.cpow_neg_one]
  apply sub_ne_zero.mpr
  intro h
  have he : (Ideal.absNorm P.val : ℂ) = 1 := inv_eq_one.mp h.symm
  have hn : Ideal.absNorm P.val = 1 := by exact_mod_cast he
  have := idealsOverPrime_norm_two_le K P.property
  omega

lemma primeIdealEulerFactor_ne_zero_at_one (K : Type*) [Field K] [NumberField K]
    (p : ℕ) : primeIdealEulerFactor K p 1 ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro P _
  exact inv_ne_zero (primeEuler_denominator_ne_zero_at_one K P)

lemma primeIdealEulerFactor_continuousAt_one (K : Type*) [Field K] [NumberField K]
    (p : ℕ) : ContinuousAt (primeIdealEulerFactor K p) 1 := by
  apply tendsto_finsetProd
  intro P _
  exact (continuousAt_const.sub
    (continuousAt_id.neg.const_cpow (Or.inr (by norm_num)))).inv₀
      (primeEuler_denominator_ne_zero_at_one K P)

lemma primeIdealEulerFactor_ne_zero (K : Type*) [Field K] [NumberField K]
    (p : ℕ) {s : ℂ} (hs : 1 < s.re) : primeIdealEulerFactor K p s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro P _
  apply inv_ne_zero
  intro he
  have hn := zetaSummand_norm_lt_one hs (idealsOverPrime_norm_two_le K P.property)
  change ‖(Ideal.absNorm P.val : ℂ)^(-s)‖ < 1 at hn
  rw [← sub_eq_zero.mp he, norm_one] at hn
  exact (lt_irrefl _ hn)

omit [Algebra F E]

lemma dedekindZeta_ratio_eq_finite_product (n : ℕ) (S : Finset Nat.Primes)
    (hloc : ∀ p : Nat.Primes, p ∉ S → ∀ s : ℂ, 1 < s.re →
      primeIdealEulerFactor E p s = primeIdealEulerFactor F p s ^ n)
    {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta E s / NumberField.dedekindZeta F s ^ n =
      ∏ p ∈ S, primeIdealEulerFactor E p s / primeIdealEulerFactor F p s ^ n := by
  have HP := (dedekindZeta_hasProd E hs).div₀ ((dedekindZeta_hasProd F hs).pow n)
    (pow_ne_zero n (dedekindZeta_ne_zero_of_one_lt_re F hs))
  rw [← HP.tprod_eq]
  apply tprod_eq_prod
  intro p hp
  rw [hloc p hp s hs, div_self (pow_ne_zero n (primeIdealEulerFactor_ne_zero F p hs))]

 

lemma dedekindZeta_ratio_tendsto_zero {n : ℕ} (hn : 2 ≤ n) :
    Tendsto (fun s : ℝ => NumberField.dedekindZeta E s /
      NumberField.dedekindZeta F s ^ n) (𝓝[>] 1) (𝓝 (0 : ℂ)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hE := NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT E
  have hF := NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT F
  have hR : (NumberField.dedekindZeta_residue F : ℂ) ≠ 0 := by
    exact_mod_cast NumberField.dedekindZeta_residue_ne_zero F
  have hz : Tendsto (fun s : ℝ => (s : ℂ) - 1) (𝓝[>] 1) (𝓝 (0 : ℂ)) := by
    have hc : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 1) (𝓝 (1 : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa using hc.sub_const 1
  have HT := (hE.div (hF.pow (2 + k)) (pow_ne_zero (2+k) hR)).mul (hz.pow (1+k))
  have HT0 : Tendsto (fun s : ℝ =>
      (((s : ℂ) - 1) * NumberField.dedekindZeta E s /
        (((s : ℂ) - 1) * NumberField.dedekindZeta F s) ^ (2+k)) *
      ((s : ℂ) - 1) ^ (1+k)) (𝓝[>] 1) (𝓝 (0 : ℂ)) := by
    simpa only [Pi.div_apply, zero_pow (by omega : 1+k ≠ 0), mul_zero] using HT
  apply HT0.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : 1 < (s : ℂ).re := hs
  have hd : (s : ℂ) - 1 ≠ 0 := by
    intro he
    have he' := congrArg Complex.re (sub_eq_zero.mp he)
    norm_num at he'
    exact (show 1 < s from hs).ne' he'
  have hBF := dedekindZeta_ne_zero_of_one_lt_re F hs'
  simp only [pow_add, pow_one, mul_pow]
  field_simp

 

theorem degree_eq_one_of_localEulerFactor_eq_pow (n : ℕ) (hn : 0 < n)
    (S : Finset Nat.Primes)
    (hloc : ∀ p : Nat.Primes, p ∉ S → ∀ s : ℂ, 1 < s.re →
      primeIdealEulerFactor E p s = primeIdealEulerFactor F p s ^ n) : n = 1 := by
  by_contra hne
  have htwo : 2 ≤ n := by omega
  let C (s : ℂ) := ∏ p ∈ S,
    primeIdealEulerFactor E p s / primeIdealEulerFactor F p s ^ n
  have hC : ContinuousAt C 1 := by
    apply tendsto_finsetProd
    intro p hp
    exact (primeIdealEulerFactor_continuousAt_one E p).div
      ((primeIdealEulerFactor_continuousAt_one F p).pow n)
      (pow_ne_zero n (primeIdealEulerFactor_ne_zero_at_one F p))
  have hCne : C 1 ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact div_ne_zero (primeIdealEulerFactor_ne_zero_at_one E p)
      (pow_ne_zero n (primeIdealEulerFactor_ne_zero_at_one F p))
  have H1 : Tendsto (fun s : ℝ => C s) (𝓝[>] 1) (𝓝 (C 1)) :=
    hC.tendsto.comp
      (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have HR : Tendsto (fun s : ℝ => NumberField.dedekindZeta E s /
      NumberField.dedekindZeta F s ^ n) (𝓝[>] 1) (𝓝 (C 1)) := by
    apply H1.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (dedekindZeta_ratio_eq_finite_product F E n S hloc (s := s) hs).symm
  exact hCne (tendsto_nhds_unique HR (dedekindZeta_ratio_tendsto_zero F E htwo))

end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_FrobeniusSplitting
attribute [-instance] _root_.AlgebraicNumberTheory.numberFieldInRationalSeparableClosure_numberField _root_.ClassFormation.DegreeData.FiniteAbstractExtension.ramificationQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.representedQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.residueQuotientFinite _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientRepresentedQuotientFinite _root_.ClassFormation.DegreeData.FiniteResidueAbstractExtension.instFiniteQuotientSubtypeMemSubgroupFieldBaseExtensionSubgroupField _root_.ClassFormation.DegreeData.FiniteTower.baseQuotientFinite _root_.ClassFormation.DegreeData.FiniteTower.topQuotientFinite _root_.ClassFormation.DegreeData.FiniteTower.totalQuotientFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.baseAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.fieldAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.baseRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.fieldRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.relativeRepresentedQuotientFinite _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFiniteAbstractConjugate_normal _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFiniteResidueConjugate_normal _root_.ClassFormation.FiniteAbstractField.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionFinite _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteAbstractFieldExtension.instFiniteQuotientSubtypeMemSubgroupFieldBaseExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.abelianIntermediateField_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldAbsoluteFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_numberField _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteLayerInCompositum_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteLayerInCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatIntersection_numberField _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerBaseFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerBaseField_numberField _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerBaseSubgroupAbsoluteQuotientFinite _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerExtensionQuotientFinite _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerExtensionSubgroupNormal _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_originalBaseTopAlgebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_originalTopScalarTower _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_topAlgebra _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerInCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldNumberField _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.HilbertRamification.Dedekind.basePrime_isPrime _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicLevel_numberField _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite_of_isSeparable _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionQuotientOfEmbedding_finite _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_finiteDimensional _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_isGalois _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.finiteUnramifiedNormQuotient _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSubquotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientMaximalIdealPowFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModHigherPrincipalUnitGroupFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.Padic.padicUnitFiniteFactor_finite _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedStandardChangedCompositum_changedFieldAlgebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedMaximalIdeal.instIsMaximal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.Modulus.congruenceSubgroup_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.narrowClassGroup_finite _root_.GlobalClassFieldTheory.Reciprocity.cyclotomicUnramifiedGeometricMaxExtensionNormal _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalOrdinaryNormQuotientAdditiveTypeAddCommGroup _root_.LocalClassFieldTheory.finiteGaloisAbstractExtensionOfEmbedding_bundle_finite _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.finiteNormalClosure_numberField _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.scaledRelativeIntegerLatticeQuotientFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Module
open scoped NumberField nonZeroDivisors Classical BigOperators
namespace PrimeDegreePackets.GaloisIdealCharacter
attribute [local instance] Ideal.Quotient.field
variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E]

lemma inertiaDeg_eq_one_of_one_isArithFrobAt
    (P : Ideal (𝓞 F)) (Q : Ideal (𝓞 E))
    [P.IsMaximal] [Q.IsMaximal] [Q.LiesOver P]
    (h : (1 : (𝓞 E) →ₐ[𝓞 F] (𝓞 E)).IsArithFrobAt Q) :
    Q.inertiaDeg (𝓞 F) = 1 := by
  let : Fintype ((𝓞 F) ⧸ P) := Fintype.ofFinite _
  let : Fintype ((𝓞 E) ⧸ Q) := Fintype.ofFinite _
  rw [Ideal.inertiaDeg_eq_of_isMaximal P Q]
  have he : FiniteField.frobeniusAlgHom ((𝓞 F) ⧸ P) ((𝓞 E) ⧸ Q) = 1 := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hx := h.mk_apply x
    simpa only [AlgHom.one_apply, ← Q.over_def P, Nat.card_eq_fintype_card,
      FiniteField.coe_frobeniusAlgHom] using hx.symm
  rw [← FiniteField.orderOf_frobeniusAlgHom ((𝓞 F) ⧸ P) ((𝓞 E) ⧸ Q), he, orderOf_one]

variable [FiniteDimensional F E] [IsGalois F E]

lemma norm_eq_of_inertiaDeg_eq_one
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (Q₀ : Ideal (𝓞 E)) [Q₀.IsPrime] [Q₀.LiesOver P.asIdeal]
    (hf : Q₀.inertiaDeg (𝓞 F) = 1)
    (Q : Ideal (𝓞 E)) [Q.IsPrime] [Q.LiesOver P.asIdeal] :
    Ideal.absNorm Q = Ideal.absNorm P.asIdeal := by
  let : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance
    (Ideal.ne_bot_of_liesOver_of_ne_bot P.ne_bot Q)
  rw [← Ideal.absNorm_pow_inertiaDeg P.asIdeal Q,
    ← Ideal.inertiaDeg_eq_of_isGaloisGroup P.asIdeal Q₀ Q (E ≃ₐ[F] E), hf, pow_one]

lemma card_primesOver_of_unramified_of_inertia_one
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (Q₀ : Ideal (𝓞 E)) [Q₀.IsPrime] [Q₀.LiesOver P.asIdeal]
    [Algebra.IsUnramifiedAt (𝓞 F) Q₀]
    (hf : Q₀.inertiaDeg (𝓞 F) = 1) :
    Nat.card (Ideal.primesOver P.asIdeal (𝓞 E)) = finrank F E := by
  have HC := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    P.asIdeal (𝓞 E) (E ≃ₐ[F] E)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx P.asIdeal Q₀ (E ≃ₐ[F] E),
    Ideal.inertiaDegIn_eq_inertiaDeg P.asIdeal Q₀ (E ≃ₐ[F] E),
    Ideal.ramificationIdx_eq_one_of_isUnramifiedAt, hf, one_mul, mul_one,
    IsGalois.card_aut_eq_finrank] at HC
  exact HC

 

lemma one_isArithFrobAt_kernelFixedField
    (χ : (E ≃ₐ[F] E) →* ℂˣ) (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (hχP : χ (primeFrobenius F E P) = 1) :
    (1 : (𝓞 (IntermediateField.fixedField χ.ker)) →ₐ[𝓞 F]
      (𝓞 (IntermediateField.fixedField χ.ker))).IsArithFrobAt
        ((primeAbove F E P).val.under (𝓞 (IntermediateField.fixedField χ.ker))) := by
  let L : IntermediateField F E := IntermediateField.fixedField χ.ker
  let Q := (primeAbove F E P).val
  intro x
  have hfix : NumberField.RingOfIntegers.mapAlgHom (primeFrobenius F E P)
      (algebraMap (𝓞 L) (𝓞 E) x) = algebraMap (𝓞 L) (𝓞 E) x := by
    apply NumberField.RingOfIntegers.ext
    change primeFrobenius F E P ((x : L) : E) = ((x : L) : E)
    exact (IntermediateField.mem_fixedField_iff χ.ker _).mp (x : L).property
      (primeFrobenius F E P) hχP
  have hF := primeFrobenius_spec F E P
  change (NumberField.RingOfIntegers.mapAlgHom (primeFrobenius F E P)).IsArithFrobAt Q at hF
  have hx := hF (algebraMap (𝓞 L) (𝓞 E) x)
  rw [hfix] at hx
  change algebraMap (𝓞 L) (𝓞 E)
    (x - x ^ Nat.card ((𝓞 F) ⧸ (Q.under (𝓞 L)).under (𝓞 F))) ∈ Q
  simpa only [map_sub, map_pow, Ideal.under_under] using hx

lemma inertiaDeg_eq_one_kernelFixedField
    (χ : (E ≃ₐ[F] E) →* ℂˣ) (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (hχP : χ (primeFrobenius F E P) = 1)
    (R : Ideal (𝓞 (IntermediateField.fixedField χ.ker)))
    [R.IsPrime] [R.LiesOver P.asIdeal] :
    R.inertiaDeg (𝓞 F) = 1 := by
  let L : IntermediateField F E := IntermediateField.fixedField χ.ker
  let Q := (primeAbove F E P).val
  let : Q.IsPrime := (primeAbove F E P).property.1
  let : Q.LiesOver P.asIdeal := (primeAbove F E P).property.2
  let Q₀ := Q.under (𝓞 L)
  let : Q₀.IsPrime := inferInstance
  let : Q₀.LiesOver P.asIdeal := by
    constructor
    rw [Ideal.under_under, Q.over_def P.asIdeal]
  let : Q₀.IsMaximal := Ideal.IsPrime.isMaximal inferInstance
    (Ideal.ne_bot_of_liesOver_of_ne_bot P.ne_bot Q₀)
  have hf := inertiaDeg_eq_one_of_one_isArithFrobAt F L P.asIdeal Q₀
    (one_isArithFrobAt_kernelFixedField F E χ P hχP)
  rw [← Ideal.inertiaDeg_eq_of_isGaloisGroup P.asIdeal Q₀ R (L ≃ₐ[F] L)]
  exact hf

end PrimeDegreePackets.GaloisIdealCharacter

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_FrobeniusNonprincipal
attribute [-instance] _root_.AlgebraicNumberTheory.numberFieldInRationalSeparableClosure_numberField _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFiniteAbstractConjugate_normal _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFiniteResidueConjugate_normal _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.abelianIntermediateField_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldAbsoluteFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseModule _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_numberField _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteLayerInCompositum_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteLayerInCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatIntersection_numberField _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerBaseField_numberField _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerExtensionSubgroupNormal _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_originalBaseTopAlgebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_topAlgebra _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldNumberField _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicLevel_numberField _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_finiteDimensional _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_isGalois _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedStandardChangedCompositum_changedFieldAlgebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.Modulus.congruenceSubgroup_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.ValuationTheory.ValuationSubring.charP _root_.GlobalClassFieldTheory.Reciprocity.cyclotomicUnramifiedGeometricMaxExtensionNormal _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalOrdinaryNormQuotientAdditiveTypeAddCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.finiteNormalClosure_numberField _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Module
open scoped NumberField nonZeroDivisors Classical
namespace PrimeDegreePackets.Unfinished

theorem actual_frobenius_nonprincipal
    (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
    [NumberField.IsTotallyReal F] [NumberField.IsTotallyReal E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    [IsCyclic (E ≃ₐ[F] E)]
    (χ : (E ≃ₐ[F] E) →* ℂˣ) (hχ : χ ≠ 1) (N : ℕ) (hN : 0 < N) :
    ∃ P : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      IsCoprime P.asIdeal (ThetaConstruction.rationalModulusIdeal (𝓞 F) N) ∧
      χ (GaloisIdealCharacter.primeFrobenius F E P) ≠ 1 := by
  classical
  by_contra h
  push Not at h
  let L : IntermediateField F E := IntermediateField.fixedField χ.ker
  have hL : IsGalois F L := inferInstance
  have hχL : L ≠ ⊥ := by
    intro he
    have hk := IntermediateField.fixingSubgroup_fixedField χ.ker
    change L.fixingSubgroup = χ.ker at hk
    rw [he, IntermediateField.fixingSubgroup_bot] at hk
    apply hχ
    apply DFunLike.ext
    intro σ
    have hm : σ ∈ χ.ker := hk ▸ Subgroup.mem_top σ
    exact hm
  let D := (NumberField.discr L).natAbs
  have hD : D ≠ 0 := Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero L)
  let S : Finset Nat.Primes := (N * D).primeFactors.subtype Nat.Prime
  have hloc (p : Nat.Primes) (hp : p ∉ S) (s : ℂ) (_hs : 1 < s.re) :
      primeIdealEulerFactor L p s = primeIdealEulerFactor F p s ^ finrank F L := by
    have hpd : ¬ p.val ∣ N * D := by
      intro hd
      apply hp
      exact (Finset.mem_subtype (a := (⟨p.val, p.property⟩ : Subtype Nat.Prime))).mpr
        (Nat.mem_primeFactors.mpr ⟨p.property, hd, mul_ne_zero (ne_of_gt hN) hD⟩)
    have hpN : p.val.Coprime N := p.property.coprime_iff_not_dvd.mpr
      (fun hd => hpd (dvd_mul_of_dvd_left hd D))
    have hpD : p.val.Coprime D := p.property.coprime_iff_not_dvd.mpr
      (fun hd => hpd (dvd_mul_of_dvd_right hd N))
    have hsplit (P : idealsOverPrime F p) :
        Nat.card (Ideal.primesOver P.val (𝓞 L)) = finrank F L ∧
        ∀ Q : Ideal.primesOver P.val (𝓞 L), Ideal.absNorm Q.val = Ideal.absNorm P.val := by
      have hP := (mem_idealsOverPrime_iff F p.property.ne_zero P.val).mp P.property
      let : P.val.IsPrime := hP.1
      have hP0 : P.val ≠ ⊥ := by
        intro he
        rw [he, Ideal.mem_bot] at hP
        exact p.property.ne_zero (Nat.cast_eq_zero.mp hP.2)
      let PP : IsDedekindDomain.HeightOneSpectrum (𝓞 F) := ⟨P.val, hP.1, hP0⟩
      have hcop : IsCoprime PP.asIdeal (ThetaConstruction.rationalModulusIdeal (𝓞 F) N) := by
        apply Ideal.isCoprime_iff_codisjoint.mpr
        apply Codisjoint.mono ((Ideal.span_singleton_le_iff_mem _).mpr hP.2) le_rfl
        exact ((Ideal.isCoprime_span_singleton_iff _ _).mpr hpN.cast).codisjoint
      have hχP := h PP hcop
      let Q := GaloisIdealCharacter.primeAbove F L PP
      let : Q.val.IsPrime := Q.property.1
      let : Q.val.LiesOver PP.asIdeal := Q.property.2
      have hf := GaloisIdealCharacter.inertiaDeg_eq_one_kernelFixedField F E χ PP hχP Q.val
      let : Algebra.IsUnramifiedAt (𝓞 F) Q.val :=
        unramified_of_absDiscr_not_mem F L PP.asIdeal Q.val (Q.val.over_def PP.asIdeal).symm
          (Ideal.IsPrime.notMem_of_isCoprime_of_mem hpD.cast hP.2)
      refine ⟨GaloisIdealCharacter.card_primesOver_of_unramified_of_inertia_one F L PP Q.val hf, ?_⟩
      intro R
      let : R.val.IsPrime := R.property.1
      let : R.val.LiesOver PP.asIdeal := R.property.2
      exact GaloisIdealCharacter.norm_eq_of_inertiaDeg_eq_one F L PP Q.val hf R.val
    exact primeIdealEulerFactor_eq_pow F L p.property.ne_zero (finrank F L) s
      (fun P => (hsplit P).1) (fun P => (hsplit P).2)
  have hdegree := degree_eq_one_of_localEulerFactor_eq_pow F L (finrank F L)
    Module.finrank_pos S hloc
  exact hχL (IntermediateField.finrank_eq_one_iff.mp hdegree)

end PrimeDegreePackets.Unfinished

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_HeckeFactors
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The principal cyclic Hecke factor

The principal factor in a cyclic Artin factorization is the actual
Dedekind zeta function with the finitely many Euler factors at the chosen
modulus removed. A nonprincipal factor is the proved entire continuation
of its realized even ray character.
-/

noncomputable section

open Filter Set Module
open scoped NumberField nonZeroDivisors BigOperators Classical

namespace DukePrimeDegree

open PrimeDegreePackets PrimeDegreePackets.GaloisIdealCharacter

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]

/-- The conductor kernel gives one common family of even ray
realizations for all cyclic characters. -/
theorem exists_cyclic_ray_family
    [NumberField.IsTotallyReal F] [NumberField.IsTotallyReal E]
    [IsCyclic (E ≃ₐ[F] E)] (N : ℕ) (hN : 0 < N)
    (hk : ∀ χ : (E ≃ₐ[F] E) →* ℂˣ,
      PrincipalRay.KernelLaw (idealHom F E χ) N) :
    ∃ ψ : ((E ≃ₐ[F] E) →* ℂˣ) → EvenRayCharacter F N,
      (∀ χ, (ψ χ).idealHom = idealHom F E χ) ∧
      ∀ χ, χ ≠ 1 → (ψ χ).IsNonprincipal := by
  let ψ := fun χ : (E ≃ₐ[F] E) →* ℂˣ =>
    PrincipalRay.realize (idealHom F E χ) N hN (hk χ) (idealHom_finiteOrder F E χ)
  refine ⟨ψ, fun _ => rfl, ?_⟩
  intro χ hχ
  obtain ⟨P, hc, hP⟩ := Unfinished.actual_frobenius_nonprincipal F E χ hχ N hN
  refine ⟨P.asIdeal, P.ne_bot, hc, ?_⟩
  change idealHom F E χ (integralIdealFractionalUnit P.asIdeal P.ne_bot) ≠ 1
  rwa [idealHom_prime]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_ConductorModulus
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_originalTopScalarTower _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.padicCompletedUnramifiedFieldValued _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.ValuationTheory.ValuationSubring.charP _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalOrdinaryNormQuotientAdditiveTypeAddCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseValued _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.scaledRelativeIntegerLatticeQuotientFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# An integer modulus for finitely many local congruences

The product of norms of conductor primes, raised to their conductor
exponents, gives a rational integer imposing every required local
higher-unit congruence. No quantitative conductor bound is needed.
-/

noncomputable section
open scoped NumberField BigOperators Classical

namespace DukePrimeDegree

open PrimeDegreePackets

variable {K : Type*} [Field K] [NumberField K]

theorem integral_mem_completed_maximal
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {a : 𝓞 K} (ha : a ∈ v.asIdeal) :
    algebraMap (𝓞 K) (v.adicCompletionIntegers K) a ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
  apply (Valuation.mem_maximalIdeal_iff (v.adicCompletion K) Valued.v).mpr
  change Valued.v ((algebraMap (𝓞 K) K a : K) : v.adicCompletion K) < 1
  rw [v.valuedAdicCompletion_eq_valuation', v.valuation_of_algebraMap]
  exact (v.intValuation_lt_one_iff_mem a).mpr ha

theorem exists_integer_for_local_congruences
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (c : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℕ)
    {D : ℕ} (hD : 0 < D) :
    ∃ N : ℕ, 0 < N ∧ D ∣ N ∧ ∀ v ∈ S,
      algebraMap (𝓞 K) (v.adicCompletionIntegers K) (N : 𝓞 K) ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ c v := by
  let N := D * ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ c v
  have hnorm (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
      0 < Ideal.absNorm v.asIdeal := by
    apply Nat.pos_of_ne_zero
    intro h
    exact v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  refine ⟨N, Nat.mul_pos hD (Finset.prod_pos (fun v _ => pow_pos (hnorm v) _)),
    dvd_mul_right D _, ?_⟩
  intro v hv
  have hd : Ideal.absNorm v.asIdeal ^ c v ∣ N := by
    exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hv) _
  obtain ⟨k, hk⟩ := hd
  have hm := Ideal.pow_mem_pow
    (integral_mem_completed_maximal v (Ideal.absNorm_mem v.asIdeal)) (c v)
  rw [hk, Nat.cast_mul, map_mul, Nat.cast_pow, map_pow]
  exact Ideal.mul_mem_right _ _ hm

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_SmallHilbertClassFieldMaximalSubextension
attribute [-instance] _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The maximal everywhere-unramified abelian subextension

The selected small Hilbert class field is characterized in actual field
order.  Its rational absolute class-formation norm subgroup is exactly
the intrinsic small-Hilbert subgroup of its fixed-field base.  The
order-reversing finite abelian classification then places every actual
finite abelian extension unramified at all finite and infinite places
inside the selected field.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open ClassFormation KummerTheory
open IdealClassFieldTheory LocalClassFieldTheory NumberField Reciprocity

/-- Fix the canonical quotient structure at the boundary between ordinary
idele classes and additive fixed subgroups. -/
@[instance_reducible]
private noncomputable def smallHilbertMaximalSubextensionIdeleClassCommGroup
    (F : Type) [Field F] [NumberField F] :
    CommGroup (IdeleClassGroup F) :=
  QuotientGroup.Quotient.commGroup (IdeleGroup.principalSubgroup F)

attribute [local instance] smallHilbertMaximalSubextensionIdeleClassCommGroup

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GroupTheory_Transfer_Witt
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.Padic.padicUnitFiniteFactor_finite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.GlobalClassFieldTheory.GlobalClassFields.narrowClassGroup_finite _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Witt's transfer theorem

For a finitely generated group `G` with finite abelianization, the transfer
from `G / G'` to `G' / G''` is trivial.

The proof follows Witt's group-ring argument. This file first
constructs the required right Fox coefficients directly from free words; no
presentation relations are assumed as extra input.
-/

open scoped BigOperators Pointwise

noncomputable section

namespace GroupTheory
namespace Transfer
namespace Witt

open Subgroup

variable {G : Type*} [Group G]

/-- Finite index of the commutator gives finiteness of the
abelianization. -/
noncomputable instance finiteAbelianizationOfFiniteIndex
    [FiniteIndex (commutator G)] :
    Finite (Abelianization G) := by
  let : Fintype (Abelianization G) :=
    (commutator G).fintypeQuotientOfFiniteIndex
  exact Finite.of_fintype _

end Witt
end Transfer
end GroupTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_IdealClassFieldTheory_RationalFiniteNormTransfer_FieldSpine
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldAbsoluteFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteGaloisLayer_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseModule _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_numberField _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerBaseFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerBaseFieldScalarTower _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerBaseField_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerBaseField_numberField _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerBaseSubgroupAbsoluteQuotientFinite _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerExtensionQuotientFinite _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerExtensionSubgroupNormal _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_originalBaseTopAlgebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_originalTopScalarTower _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_topAlgebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_topRatScalarTower _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerTopField_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerInCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Fixed-field instance spine for rational finite-norm transport

This leaf names the finite-dimensional, scalar-tower, number-field, Galois,
and quotient instances reused by the rational finite-norm transport modules.
The public dependent type aliases are compiled once here.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open ClassFormation
open CyclicCohomology

section RationalIdeleExtension

open Reciprocity
open LocalClassFieldTheory

namespace RationalFiniteNormTransferInternal

/-- The canonical absolute algebra structure on a rational relative fixed field. -/
@[reducible] noncomputable def absoluteAlgebra
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup) :
    Algebra ℚ
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK) :=
  inferInstance

end RationalFiniteNormTransferInternal


end RationalIdeleExtension

end IdealClassFieldTheory
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_IdealClassFieldTheory_SmallHilbertTowerRealization
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldScalarTowerOverOriginal _root_.GroupTheory.Transfer.Witt.finiteAbelianizationOfFiniteIndex _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Actual realization of the two-stage small Hilbert tower

The first small Hilbert class field is the actual finite abelian
subextension selected in `HilbertClassFieldRealization`.  Over its actual
fixed field, the closed finite-index small-Hilbert norm subgroup has a
finite Galois norm neighbourhood.  We embed that neighbourhood in the
rational separable closure compatibly with the already chosen first
stage.  Finite abelian classification then selects the second small
Hilbert class field over the literal first-stage subgroup.

The compatibility of the embedding is essential: an unrelated chosen
copy of the middle number field would produce a class field over a
conjugate closed subgroup rather than over the first-stage subgroup
itself.
-/

open scoped Classical NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open AlgebraicNumberTheory
open ClassFormation
open CyclicCohomology
open GlobalClassFields
open KummerTheory
open LocalClassFieldTheory
open RamificationTheory
open Reciprocity

/-- The ordinary idèle-class operations used by the two-stage transport,
fixed at the canonical principal-subgroup quotient. -/
@[instance_reducible]
private noncomputable def smallHilbertTowerIdeleClassCommGroup
    (F : Type) [Field F] [NumberField F] :
    CommGroup (IdeleClassGroup F) :=
  QuotientGroup.Quotient.commGroup (IdeleGroup.principalSubgroup F)

attribute [local instance] smallHilbertTowerIdeleClassCommGroup

end IdealClassFieldTheory
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_ClassFieldModulus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A common even modulus away from ramification

Enlarging the finite conductor to contain the discriminant primes leaves
its infinite part empty and its Artin-kernel property intact. An ordinary
positive integer then imposes all of its local congruences.
-/

noncomputable section
open scoped NumberField Classical

namespace DukePrimeDegree

open GlobalClassFieldTheory GlobalClassFieldTheory.GlobalClassFields
open PrimeDegreePackets PrimeDegreePackets.GaloisIdealCharacter

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [IsAbelianGalois K L]
variable [NumberField.IsTotallyReal L]

theorem exists_even_unramified_artin_modulus :
    ∃ m : RayClass.Modulus K, m.infinitePart = ∅ ∧
      m.congruenceSubgroup ≤ (ideleClassNorm K L).range ∧
      ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), v ∉ m.finitePart.support →
        Algebra.IsUnramifiedAt (𝓞 K) (primeAbove K L v).val := by
  obtain ⟨m, hm, hnorm⟩ := exists_even_artin_modulus K L
  let D : 𝓞 K := (NumberField.discr L).natAbs
  have hD : D ≠ 0 := by
    change ((NumberField.discr L).natAbs : 𝓞 K) ≠ 0
    exact_mod_cast (Int.natAbs_pos.mpr (NumberField.discr_ne_zero L)).ne'
  let I := integralIdealFractionalUnit (Ideal.span {D})
    (by simpa only [ne_eq, Ideal.span_singleton_eq_bot] using hD)
  let b : RayClass.FiniteModulus K :=
    (FractionalIdealGroup.countVector I).mapRange Int.natAbs rfl
  let m' := m.replaceFinitePart (m.finitePart + b)
  have hle : m ≤ m' := by
    constructor
    · exact le_add_of_nonneg_right (by positivity)
    · exact Finset.Subset.refl _
  refine ⟨m', hm, (RayClass.Modulus.congruenceSubgroup_antitone hle).trans hnorm, ?_⟩
  intro v hv
  have hv0 : m'.finitePart v = 0 := Finsupp.notMem_support_iff.mp hv
  have hb : b v = 0 := by
    change m.finitePart v + b v = 0 at hv0
    omega
  have hcount : FractionalIdeal.count K v (Ideal.span {D}) = 0 := by
    have hc : Int.natAbs (FractionalIdeal.count K v (Ideal.span {D})) = 0 := hb
    exact Int.natAbs_eq_zero.mp hc
  have hnot : D ∉ v.asIdeal := by
    exact mt ((principal_count_ne_zero_iff_mem K D hD v).mpr) (by simpa using hcount)
  let : (primeAbove K L v).val.IsPrime := (primeAbove K L v).property.1
  exact unramified_of_absDiscr_not_mem K L v.asIdeal (primeAbove K L v).val
    (primeAbove K L v).property.2.over.symm hnot

theorem exists_integer_even_artin_modulus :
    ∃ (m : RayClass.Modulus K) (N : ℕ), 0 < N ∧
      (NumberField.discr L).natAbs ∣ N ∧ m.infinitePart = ∅ ∧
      m.congruenceSubgroup ≤ (ideleClassNorm K L).range ∧
      (∀ v ∈ m.finitePart.support,
        algebraMap (𝓞 K) (v.adicCompletionIntegers K) (N : 𝓞 K) ∈
          IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ m.finitePart v) ∧
      ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), v ∉ m.finitePart.support →
        Algebra.IsUnramifiedAt (𝓞 K) (primeAbove K L v).val := by
  obtain ⟨m, hm, hnorm, hur⟩ := exists_even_unramified_artin_modulus (K := K) (L := L)
  obtain ⟨N, hN, hdN, hlocal⟩ := exists_integer_for_local_congruences
    m.finitePart.support m.finitePart (Int.natAbs_pos.mpr (NumberField.discr_ne_zero L))
  exact ⟨m, N, hN, hdN, hm, hnorm, hlocal, hur⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_ClassFieldRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Unconditional even ray realization of cyclic ideal characters

The conductor of a totally real cyclic extension has no infinite part.
Arithmetic Artin reciprocity and the common rational congruence modulus
therefore supply the kernel law for every actual Frobenius ideal
character. This gives their realization as even ray characters.
-/

noncomputable section
open scoped NumberField Classical

namespace DukePrimeDegree
open PrimeDegreePackets PrimeDegreePackets.GaloisIdealCharacter

/-- Actual cyclic Frobenius characters of a totally real extension have
one common even ray modulus, with the discriminant primes removed. -/
theorem exists_cyclic_ray_family_unconditional
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] [NumberField.IsTotallyReal K] [NumberField.IsTotallyReal L] :
    ∃ N : ℕ, 0 < N ∧ (NumberField.discr L).natAbs ∣ N ∧
      ∃ ψ : ((L ≃ₐ[K] L) →* ℂˣ) → EvenRayCharacter K N,
        (∀ χ, (ψ χ).idealHom = idealHom K L χ) ∧
        ∀ χ, χ ≠ 1 → (ψ χ).IsNonprincipal := by
  let : CommGroup (L ≃ₐ[K] L) := IsCyclic.commGroup
  let : IsAbelianGalois K L := { is_comm.comm := mul_comm }
  obtain ⟨m, N, hN, hdN, hm, hnorm, hlocal, hur⟩ :=
    exists_integer_even_artin_modulus (K := K) (L := L)
  obtain ⟨ψ, hid, hψ⟩ := exists_cyclic_ray_family K L N hN
    (idealCharacter_kernelLaw_of_even_modulus m hm hnorm hur N hlocal)
  exact ⟨N, hN, hdN, ψ, hid, hψ⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_StarkUnconditional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Unconditional odd-degree exceptional-zero exclusion

Artin reciprocity supplies even ray characters for each cyclic fixed
field in the normal-closure argument.
The resulting zero exclusion is transported to arbitrary universes.
-/

noncomputable section
open scoped NumberField Classical

namespace DukePrimeDegree

universe u

lemma hasCyclicRayRealizations_unconditional_oai
    (E : Type) [Field E] [NumberField E] [IsGalois ℚ E]
    [NumberField.IsTotallyReal E] : HasCyclicRayRealizations E := by
  intro C hC
  let : IsCyclic C := hC
  let : IsCyclic (E ≃ₐ[IntermediateField.fixedField C] E) :=
    (IntermediateField.subgroupEquivAlgEquiv C).isCyclic.mp hC
  let : NumberField.IsTotallyReal (IntermediateField.fixedField C) :=
    NumberField.IsTotallyReal.of_algebra _ E
  exact exists_cyclic_ray_family_unconditional (IntermediateField.fixedField C) E

end DukePrimeDegree

end

end OAI
end

theorem solution : type_of% @OAI.DukePrimeDegree.hasCyclicRayRealizations_unconditional_oai := @OAI.DukePrimeDegree.hasCyclicRayRealizations_unconditional_oai
