-- Prove2me | solution 1 for GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextension_globalNormResidueOfEmbedding_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-14T04:11:02.780624+00:00
-- url     : https://prove2.me/submissions/c97437b2-9573-4039-bbe4-6469bf302fed

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.BigOperators.Finprod
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
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.LinearMap.Polynomial
import Mathlib.Algebra.Module.MinimalAxioms
import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Module.Shrink
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Module.ZMod
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
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Trace
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.Ideal.Quotient.Operations
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
import Definitions.Def_OAIQ244Duke109
import Theorems.Thm_GlobalClassFieldTheory_Reciprocity_globalNormResidueMonoidHom_ramifiedInfinitePlaceOverextension_infinitePlaceIdeleClass

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_OverextensionArtin
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Artin reciprocity on the ramified infinite-place overextension

This module proves principal-idele triviality, descends the chosen Artin
product to the norm quotient, and identifies it with global reciprocity.
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

section

attribute [-instance]
  ramifiedInfinitePlaceRealFixedField_ratScalarTower

local instance
    ramifiedInfinitePlaceOverextensionIdeleClassGroupIsMulCommutative_ra4258f_1
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩
omit [NumberField K] [FiniteDimensional K L] in
/-- Any two nonidentity automorphisms of the quadratic overextension agree. -/
theorem
    ramifiedInfinitePlaceOverextension_galois_eq_of_ne_one
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K)
    {σ τ :
      Gal(
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v) /
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified))}
    (hσ : σ ≠ 1)
    (hτ : τ ≠ 1) :
    σ = τ := by
  rcases
      ramifiedInfinitePlaceOverextension_eq_one_or_conjugation
        (K := K) (L := L) v hRamified σ with hσ1 | hσc
  · exact (hσ hσ1).elim
  rcases
      ramifiedInfinitePlaceOverextension_eq_one_or_conjugation
        (K := K) (L := L) v hRamified τ with hτ1 | hτc
  · exact (hτ hτ1).elim
  exact hσc.trans hτc.symm

end

end ComplexConjugationOverextension

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_InfinitePlaceCompatibility
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsCyclotomicExtension _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormExponentNeZero _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_numberField _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
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
    infinitePlaceCompatibilityIdeleClassGroupIsMulCommutative
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

omit [NumberField K] [FiniteDimensional K L] in
/-- The chosen place of the special overextension above its concrete
fixed-field place is ramified. -/
theorem
    ramifiedInfinitePlaceOverextension_chosenPlace_isRamified
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    (chosenInfinitePlaceAbove
      (L :=
        infinitePlaceComplexificationOverfield
          (K := K) (L := L) v)
      (ramifiedInfinitePlaceRealFixedPlace
        (K := K) (L := L) v hRamified)).IsRamified
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified) := by
  rw [InfinitePlace.isRamified_iff,
    chosenInfinitePlaceAbove_comap
      (L :=
        infinitePlaceComplexificationOverfield
          (K := K) (L := L) v)
      (ramifiedInfinitePlaceRealFixedPlace
        (K := K) (L := L) v hRamified)]
  exact
    ⟨IsTotallyComplex.isComplex _,
      ramifiedInfinitePlaceRealFixedPlace_isReal
        (K := K) (L := L) v hRamified⟩

omit [NumberField K] [FiniteDimensional K L] in
/-- At the concrete real fixed-field place, the local Artin symbol of
negative one is the distinguished ambient complex conjugation. -/
theorem
    ramifiedInfinitePlaceOverextension_localArtin_neg_one
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    chosenInfinitePlaceArtinMonoidHom
        (K :=
          ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified)
        (L :=
          infinitePlaceComplexificationOverfield
            (K := K) (L := L) v)
        (ramifiedInfinitePlaceRealFixedPlace
          (K := K) (L := L) v hRamified)
        (-1 :
          (ramifiedInfinitePlaceRealFixedPlace
            (K := K) (L := L) v hRamified).Completionˣ) =
      ramifiedInfinitePlaceOverextensionConjugation
        (K := K) (L := L) v hRamified := by
  apply
    ramifiedInfinitePlaceOverextension_galois_eq_of_ne_one
      (K := K) (L := L) v hRamified
  · have hConj :=
      chosenInfinitePlaceArtinMonoidHom_neg_one_isConj_of_ramified
        (K :=
          ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified)
        (L :=
          infinitePlaceComplexificationOverfield
            (K := K) (L := L) v)
        (ramifiedInfinitePlaceRealFixedPlace
          (K := K) (L := L) v hRamified)
        (ramifiedInfinitePlaceOverextension_chosenPlace_isRamified
          (K := K) (L := L) v hRamified)
    exact
      (ComplexEmbedding.isConj_ne_one_iff hConj).2
        (InfinitePlace.isComplex_iff.mp
          (IsTotallyComplex.isComplex
            (chosenInfinitePlaceAbove
              (L :=
                infinitePlaceComplexificationOverfield
                  (K := K) (L := L) v)
              (ramifiedInfinitePlaceRealFixedPlace
                (K := K) (L := L) v hRamified))))
  · intro hc
    apply
      ramifiedInfinitePlaceOverextensionCyclotomicRestriction_conjugation_ne_one
        (K := K) (L := L) v hRamified
    rw [hc, map_one]

omit [NumberField K] [FiniteDimensional K L] in
/-- The canonical global norm-residue value of the concrete
fixed-field one-place negative-one class is ambient complex
conjugation. -/
theorem
    ramifiedInfinitePlaceOverextension_globalNormResidue_neg_one
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    globalNormResidueMonoidHom
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified)
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v)
        (IdeleGroup.infinitePlaceIdeleClass
          (ramifiedInfinitePlaceRealFixedPlace
            (K := K) (L := L) v hRamified)
          (-1 :
            (ramifiedInfinitePlaceRealFixedPlace
              (K := K) (L := L) v hRamified).Completionˣ)) =
      ramifiedInfinitePlaceOverextensionConjugation
        (K := K) (L := L) v hRamified := by
  rw [
    globalNormResidueMonoidHom_ramifiedInfinitePlaceOverextension_infinitePlaceIdeleClass,
    ramifiedInfinitePlaceOverextension_localArtin_neg_one]

omit [NumberField K] [FiniteDimensional K L] in
/-- The explicitly embedded norm-residue map for the quadratic
overextension has the genuine idele-class norm range as its kernel. -/
theorem
    ramifiedInfinitePlaceOverextension_globalNormResidueOfEmbedding_eq_one_iff
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K)
    (j :
      infinitePlaceComplexificationOverfield
          (K := K) (L := L) v →ₐ[ℚ]
        SeparableClosure ℚ)
    (c :
      IdeleClassGroup
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified)) :
    globalNormResidueMonoidHomOfEmbedding
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified)
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v)
        j c =
      1 ↔
    c ∈
      (_root_.ideleClassNorm
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified)
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v)).range := by
  let e :
      (IdeleClassGroup
          (ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified) ⧸
        (_root_.ideleClassNorm
          (ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified)
          (infinitePlaceComplexificationOverfield
            (K := K) (L := L) v)).range) ≃*
        Gal(
          (infinitePlaceComplexificationOverfield
            (K := K) (L := L) v) /
          (ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified)) :=
    AddEquiv.toMultiplicative
      (globalNormResidueEquivOfEmbedding
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified)
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v)
        j)
  change
    e (QuotientGroup.mk'
          (_root_.ideleClassNorm
            (ramifiedInfinitePlaceRealFixedField
              (K := K) (L := L) v hRamified)
            (infinitePlaceComplexificationOverfield
              (K := K) (L := L) v)).range c) =
        1 ↔
      c ∈
        (_root_.ideleClassNorm
          (ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified)
          (infinitePlaceComplexificationOverfield
            (K := K) (L := L) v)).range
  constructor
  · intro h
    have hq :
        QuotientGroup.mk'
            (_root_.ideleClassNorm
              (ramifiedInfinitePlaceRealFixedField
                (K := K) (L := L) v hRamified)
              (infinitePlaceComplexificationOverfield
                (K := K) (L := L) v)).range c =
          1 := by
      apply e.injective
      exact h.trans (map_one e).symm
    exact (QuotientGroup.eq_one_iff c).1 hq
  · intro hc
    have hq :
        QuotientGroup.mk'
            (_root_.ideleClassNorm
              (ramifiedInfinitePlaceRealFixedField
                (K := K) (L := L) v hRamified)
              (infinitePlaceComplexificationOverfield
                (K := K) (L := L) v)).range c =
          1 :=
      (QuotientGroup.eq_one_iff c).2 hc
    calc
      e (QuotientGroup.mk'
          (_root_.ideleClassNorm
            (ramifiedInfinitePlaceRealFixedField
              (K := K) (L := L) v hRamified)
            (infinitePlaceComplexificationOverfield
              (K := K) (L := L) v)).range c) = e 1 :=
        congrArg e hq
      _ = 1 := map_one e

omit [NumberField K] [FiniteDimensional K L] in
/-- For every rational-separable-closure embedding, the norm-residue
value of the concrete upper negative-one one-place class is ambient
complex conjugation.  The point is independent of the embedding
because the upper Galois group is the actual two-element group and all
these maps have the same genuine norm kernel. -/
theorem
    ramifiedInfinitePlaceOverextension_globalNormResidueOfEmbedding_neg_one_oai
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K)
    (j :
      infinitePlaceComplexificationOverfield
          (K := K) (L := L) v →ₐ[ℚ]
        SeparableClosure ℚ) :
    globalNormResidueMonoidHomOfEmbedding
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified)
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v)
        j
        (IdeleGroup.infinitePlaceIdeleClass
          (ramifiedInfinitePlaceRealFixedPlace
            (K := K) (L := L) v hRamified)
          (-1 :
            (ramifiedInfinitePlaceRealFixedPlace
              (K := K) (L := L) v hRamified).Completionˣ)) =
      ramifiedInfinitePlaceOverextensionConjugation
        (K := K) (L := L) v hRamified := by
  rcases
      ramifiedInfinitePlaceOverextension_eq_one_or_conjugation
        (K := K) (L := L) v hRamified
        (globalNormResidueMonoidHomOfEmbedding
          (ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified)
          (infinitePlaceComplexificationOverfield
            (K := K) (L := L) v)
          j
          (IdeleGroup.infinitePlaceIdeleClass
            (ramifiedInfinitePlaceRealFixedPlace
              (K := K) (L := L) v hRamified)
            (-1 :
              (ramifiedInfinitePlaceRealFixedPlace
                (K := K) (L := L) v hRamified).Completionˣ))) with
    htrivial | hconjugation
  · exfalso
    have hnorm :
        IdeleGroup.infinitePlaceIdeleClass
            (ramifiedInfinitePlaceRealFixedPlace
              (K := K) (L := L) v hRamified)
            (-1 :
              (ramifiedInfinitePlaceRealFixedPlace
                (K := K) (L := L) v hRamified).Completionˣ) ∈
          (_root_.ideleClassNorm
            (ramifiedInfinitePlaceRealFixedField
              (K := K) (L := L) v hRamified)
            (infinitePlaceComplexificationOverfield
              (K := K) (L := L) v)).range :=
      (ramifiedInfinitePlaceOverextension_globalNormResidueOfEmbedding_eq_one_iff
        (K := K) (L := L) v hRamified j _).mp htrivial
    have hstandard :
        globalNormResidueMonoidHom
            (ramifiedInfinitePlaceRealFixedField
              (K := K) (L := L) v hRamified)
            (infinitePlaceComplexificationOverfield
              (K := K) (L := L) v)
            (IdeleGroup.infinitePlaceIdeleClass
              (ramifiedInfinitePlaceRealFixedPlace
                (K := K) (L := L) v hRamified)
              (-1 :
                (ramifiedInfinitePlaceRealFixedPlace
                  (K := K) (L := L) v hRamified).Completionˣ)) =
          1 :=
      (globalNormResidueMonoidHom_eq_one_iff
        (K :=
          ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified)
        (L :=
          infinitePlaceComplexificationOverfield
            (K := K) (L := L) v)
        _).2 hnorm
    rw [
      ramifiedInfinitePlaceOverextension_globalNormResidue_neg_one]
      at hstandard
    apply
      ramifiedInfinitePlaceOverextensionCyclotomicRestriction_conjugation_ne_one
        (K := K) (L := L) v hRamified
    rw [hstandard, map_one]
  · exact hconjugation

end ComplexConjugationOverextension

end Reciprocity
end GlobalClassFieldTheory
end
end

theorem solution : type_of% @GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextension_globalNormResidueOfEmbedding_neg_one_oai := @GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextension_globalNormResidueOfEmbedding_neg_one_oai
