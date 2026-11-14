-- Prove2me | solution 1 for GlobalClassFieldTheory.Reciprocity.chosenFinitePlaceLocalArtin_eq_arithmeticFrobenius_inv_of_unramified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-14T01:35:41.311924+00:00
-- url     : https://prove2.me/submissions/3ebd0b32-1c29-4638-83fc-14f3efc93938

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Subring
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Submonoid.Units
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.LinearMap.Polynomial
import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Module.Shrink
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Order.Hom.Units
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Algebra.Order.WithTop.Untop0
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Lifts
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
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Finite
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Transfer
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.NumberField.Units.Regulator
import Mathlib.NumberTheory.Ostrowski
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Ramification
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
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.FractionalIdeal.Norm
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Polynomial.ContentIdeal
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Topology.Algebra.Group.TopologicalAbelianization
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Compact
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.Algebra.Valued.ValuativeRel
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.UniformSpace.AbsoluteValue
import Definitions.Def_OAIQ244Duke087

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_Construction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.padicCompletedUnramifiedFieldValued _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceBaseValued _root_.chosenFinitePlaceCompletionAlgebra
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.valuationModDegreeMulHom_apply _root_.LocalClassFieldTheory.valuationModDegree_apply _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Construction of finite-place Artin homomorphisms

This module constructs the local Artin map for a chosen extension of a finite place and transports it through the actual decomposition group into the global Galois group.
-/

open scoped Classical IsMulCommutative NNReal NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [hKLfinite : FiniteDimensional K L] [IsAbelianGalois K L]

/-- The local Artin input of a chosen order-one prime element has the
inverse-standard normalized local valuation. -/
theorem finitePlaceLocalArtinInput_chosenLocalOrderSection_valuationMap
    (v : HeightOneSpectrum (𝓞 K)) :
    let C := (NumberField.HeightOneSpectrum.adicAbv K v).Completion
    letI : ValuativeRel C := finitePlaceLocalArtinCompletionValuativeRel v
    letI : IsNonarchimedeanLocalField C :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    IsNonarchimedeanLocalField.valuationMap C
      (Additive.ofMul
        (finitePlaceLocalArtinInput v
          (FiniteIdeleGroup.chosenLocalOrderSection v 1))) = -1 := by
  let C := (NumberField.HeightOneSpectrum.adicAbv K v).Completion
  let a : (v.adicCompletion K)ˣ :=
    FiniteIdeleGroup.chosenLocalOrderSection v 1
  let x : Cˣ := finitePlaceLocalArtinInput v a
  let : IsUltrametricDist C :=
    finitePlaceArtinCompletionIsUltrametricDist
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v)
  let : ValuativeRel C := finitePlaceLocalArtinCompletionValuativeRel v
  let : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let f := finitePlaceCompletionRingHom v
  have hfx : f (x : C) = (a : v.adicCompletion K) := by
    exact congrArg Units.val
      ((finitePlaceCompletionUnitsContinuousMulEquiv v).apply_symm_apply a)
  have hva : Valued.v (a : v.adicCompletion K) =
      WithZero.exp (-1 : ℤ) := by
    change Valued.v (Classical.choose
      (HeightOneSpectrum.valuedAdicCompletion_surjective K v
        (WithZero.exp (-1 : ℤ)))) = _
    exact Classical.choose_spec
      (HeightOneSpectrum.valuedAdicCompletion_surjective K v
        (WithZero.exp (-1 : ℤ)))
  have horder (y z : C) :
      ValuativeRel.valuation C y ≤ ValuativeRel.valuation C z ↔
        ‖y‖ ≤ ‖z‖ := by
    change ValuativeRel.ValueGroupWithZero.mk y 1 ≤
      ValuativeRel.ValueGroupWithZero.mk z 1 ↔ _
    rw [ValuativeRel.ValueGroupWithZero.mk_le_mk]
    simp only [Submonoid.coe_one, mul_one]
    change NormedField.valuation y ≤ NormedField.valuation z ↔ _
    simp only [NormedField.valuation_apply, ← NNReal.coe_le_coe, coe_nnnorm]
  have hlt (y z : C) :
      ValuativeRel.valuation C y < ValuativeRel.valuation C z ↔
        ‖y‖ < ‖z‖ := by
    rw [lt_iff_le_not_ge, lt_iff_le_not_ge]
    exact and_congr (horder y z) (not_congr (horder z y))
  have hIntegerBound (η : WithZero (Multiplicative ℤ)) (hη : η < 1) :
      η ≤ WithZero.exp (-1 : ℤ) := by
    cases η using WithZero.recZeroCoe with
    | zero => exact bot_le
    | coe d =>
        change (d : WithZero (Multiplicative ℤ)) ≤
          ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ))
        rw [WithZero.coe_le_coe]
        rw [← Multiplicative.toAdd_le]
        change Multiplicative.toAdd d ≤ (-1 : ℤ)
        have hd : Multiplicative.toAdd d < 0 := by
          have hd' : d < (1 : Multiplicative ℤ) := by
            simpa using hη
          exact Multiplicative.toAdd_lt.mp hd'
        omega
  have hNormInput : ‖(x : C)‖ = ‖(a : v.adicCompletion K)‖ := by
    rw [← hfx]
    exact ((finitePlaceCompletionRingHom_isometry v).norm_map_of_map_zero
      (map_zero f) (x : C)).symm
  have hMax : ∀ δ : ValuativeRel.ValueGroupWithZero C,
      δ < 1 → δ ≤ ValuativeRel.valuation C (x : C) := by
    intro δ hδ
    obtain ⟨y, rfl⟩ := ValuativeRel.valuation_surjective δ
    have hyNorm : ‖y‖ < 1 := by
      simpa only [norm_one] using (hlt y 1).mp (by simpa using hδ)
    have hyConcrete : ‖f y‖ < 1 := by
      rw [(finitePlaceCompletionRingHom_isometry v).norm_map_of_map_zero
        (map_zero f) y]
      exact hyNorm
    let q : ℝ≥0 := v.asIdeal.absNorm
    have hq : 1 < q := HeightOneSpectrum.one_lt_absNorm_nnreal v
    have hyVal : Valued.v (f y) <
        (1 : WithZero (Multiplicative ℤ)) := by
      apply (WithZeroMulInt.toNNReal_lt_one_iff hq).mp
      exact NNReal.coe_lt_coe.mp (by
        simpa only [FinitePlace.norm_def, NNReal.coe_one] using hyConcrete)
    have hyLe := hIntegerBound (Valued.v (f y)) hyVal
    have hyNormLe : ‖f y‖ ≤ ‖(a : v.adicCompletion K)‖ := by
      rw [FinitePlace.norm_def, FinitePlace.norm_def, hva]
      exact NNReal.coe_le_coe.mpr
        ((WithZeroMulInt.toNNReal_strictMono hq).monotone hyLe)
    apply (horder y (x : C)).mpr
    rw [hNormInput]
    rw [← (finitePlaceCompletionRingHom_isometry v).norm_map_of_map_zero
      (map_zero f) y]
    exact hyNormLe
  let φ := _root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt C
  have hφlt : φ (ValuativeRel.valuation C (x : C)) < 1 := by
    have hval : WithZero.exp (-1 : ℤ) <
        (1 : WithZero (Multiplicative ℤ)) := by
      rw [WithZero.exp_eq_coe_ofAdd, ← WithZero.coe_one,
        WithZero.coe_lt_coe]
      change (Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) < 1
      change (-1 : ℤ) < 0
      omega
    have hnorm : ‖(x : C)‖ < 1 := by
      rw [hNormInput, FinitePlace.norm_def, hva]
      exact_mod_cast
        (WithZeroMulInt.toNNReal_lt_one_iff
          (HeightOneSpectrum.one_lt_absNorm_nnreal v)).mpr hval
    have hv : ValuativeRel.valuation C (x : C) < 1 := by
      exact (hlt (x : C) 1).mpr (by simpa only [norm_one] using hnorm)
    simpa only [map_one] using φ.strictMono hv
  have hφmax : ∀ η : WithZero (Multiplicative ℤ),
      η < 1 → η ≤ φ (ValuativeRel.valuation C (x : C)) := by
    intro η hη
    let δ := φ.symm η
    have hδ : δ < 1 := by
      simpa only [map_one] using φ.symm.strictMono hη
    have h := φ.strictMono.monotone (hMax δ hδ)
    change φ (φ.symm η) ≤ _ at h
    simpa only [φ.apply_symm_apply] using h
  have hφeq : φ (ValuativeRel.valuation C (x : C)) =
      WithZero.exp (-1 : ℤ) := by
    apply le_antisymm
    · exact hIntegerBound _ hφlt
    · apply hφmax
      rw [WithZero.exp_eq_coe_ofAdd, ← WithZero.coe_one,
        WithZero.coe_lt_coe]
      change (Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) < 1
      change (-1 : ℤ) < 0
      omega
  change IsNonarchimedeanLocalField.valuationMap C (Additive.ofMul x) = -1
  rw [IsNonarchimedeanLocalField.valuationMap_apply,
    IsNonarchimedeanLocalField.v_apply]
  change Multiplicative.toAdd
    (WithZero.unzero
      (x := φ (ValuativeRel.valuation C (x : C))) (by simp)) = -1
  rw [WithZero.toAdd_unzero_eq_log, hφeq, WithZero.log_exp]

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_UnramifiedNormalization
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionIsAlgebraic _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.padicCompletedUnramifiedFieldValued _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Unramified normalization of the chosen finite-place Artin map

The chosen order-one input has normalized local valuation `-1` in the
geometric finite-place construction. Its local Artin image is therefore
inverse arithmetic Frobenius in the actual chosen completion.
-/

open scoped Classical NumberField ValuativeRel
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.Valuations LocalFieldTheory

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [hKLfinite : FiniteDimensional K L] [IsAbelianGalois K L]

/-- At an unramified chosen finite place, the chosen geometric local Artin
symbol of the order-one section is inverse arithmetic Frobenius. -/
theorem chosenFinitePlaceLocalArtin_eq_arithmeticFrobenius_inv_of_unramified_oai
    (v : HeightOneSpectrum (𝓞 K))
    (hunram : ChosenFinitePlaceIsUnramified (K := K) (L := L) v) :
    finitePlaceLocalArtinMonoidHom (K := K) (L := L) v
        (chosenFinitePlaceExtension (L := L) v)
        (FiniteIdeleGroup.chosenLocalOrderSection v 1) =
      (chosenFinitePlaceLocalArithmeticFrobenius
        (K := K) (L := L) v hunram)⁻¹ := by
  let w := chosenFinitePlaceExtension (L := L) v
  let C := ChosenFinitePlaceBaseCompletion (K := K) v
  let E := ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v
  let x : (v.adicCompletion K)ˣ :=
    FiniteIdeleGroup.chosenLocalOrderSection v 1
  let : Algebra C E := finitePlaceLocalArtinLocalizedAlgebra v w
  let : FiniteDimensional C E := finitePlaceLocalArtinFiniteDimensional v w
  let : IsAbelianGalois C E :=
    finitePlaceLocalArtinIsAbelianGalois v w hKLfinite
  let : ValuativeRel C := finitePlaceLocalArtinCompletionValuativeRel v
  let : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let : IsIntegralClosure 𝒪[E] 𝒪[C] E :=
    chosenFinitePlaceLocalizedIsIntegralClosure (K := K) (L := L) v
  let : Module.Finite 𝒪[C] 𝒪[E] :=
    chosenFinitePlaceLocalizedIntegerModuleFinite (K := K) (L := L) v
  let : IsNonarchimedeanLocalField.IsUnramifiedValuedExtension C E := hunram
  have hval :
      IsNonarchimedeanLocalField.valuationMap C
        (Additive.ofMul (finitePlaceLocalArtinInput v x)) = -1 :=
    finitePlaceLocalArtinInput_chosenLocalOrderSection_valuationMap v
  have hfrob :=
    LocalClassFieldTheory.abelianLocalArtinMonoidHom_eq_frobenius_zpow
      C E (finitePlaceLocalArtinInput v x)
  have hnorm :
      LocalClassFieldTheory.abelianLocalArtinMonoidHom C E
          (finitePlaceLocalArtinInput v x) =
        (arithmeticFrobeniusOfUnramifiedValuation C E)⁻¹ := by
    simpa only [hval, zpow_neg_one] using hfrob
  calc
    finitePlaceLocalArtinMonoidHom (K := K) (L := L) v w x =
        LocalClassFieldTheory.abelianLocalArtinMonoidHom C E
          (finitePlaceLocalArtinInput v x) := by
      rfl
    _ = (chosenFinitePlaceLocalArithmeticFrobenius
          (K := K) (L := L) v hunram)⁻¹ := by
      exact hnorm

end Reciprocity
end GlobalClassFieldTheory
end
end

theorem solution : type_of% @GlobalClassFieldTheory.Reciprocity.chosenFinitePlaceLocalArtin_eq_arithmeticFrobenius_inv_of_unramified_oai := @GlobalClassFieldTheory.Reciprocity.chosenFinitePlaceLocalArtin_eq_arithmeticFrobenius_inv_of_unramified_oai
